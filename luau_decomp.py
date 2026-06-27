#!/usr/bin/env python3
"""
Roblox Luau v6 Bytecode Decompiler — complete rewrite
Parser matches luau_disasm.py exactly.

Analysis passes (all in one forward scan, no AST):
  - Write-count / use-count pre-scan
  - Constant propagation: single-write, non-call registers are inlined at use sites
  - Chain collapsing: a=x; b=a.Y; c=b.Z  →  c=x.Y.Z  (via propagation)
  - Mutation vs declaration: only emit 'local' on first write per register
  - GETIMPORT: name from K[D-1] (the string constant before the import constant)
  - CAPTURE val: inline parent register expression into child upvalue
  - CAPTURE ref: global up_N naming (counter never resets across protos)
  - elseif chain detection via pre-scan of JUMPXEQK* targets
  - Main proto emitted as bare script body (no function wrapper)
"""
import struct, sys
from typing import Optional, List, Tuple, Dict, Set

# ── Opcode table ───────────────────────────────────────────────────────────────
OPCODES = {
    0:'NOP', 1:'BREAK', 2:'LOADNIL', 3:'LOADB', 4:'LOADN', 5:'LOADK',
    6:'MOVE', 7:'GETGLOBAL', 8:'SETGLOBAL', 9:'GETUPVAL', 10:'SETUPVAL',
    11:'CLOSEUPVALS', 12:'GETIMPORT', 13:'GETTABLE', 14:'SETTABLE',
    15:'GETTABLEKS', 16:'SETTABLEKS', 17:'GETTABLEN', 18:'SETTABLEN',
    19:'NEWCLOSURE', 20:'NAMECALL', 21:'CALL', 22:'RETURN',
    23:'JUMP', 24:'JUMPBACK', 25:'JUMPIF', 26:'JUMPIFNOT',
    27:'JUMPIFEQ', 28:'JUMPIFLE', 29:'JUMPIFLT',
    30:'JUMPIFNOTEQ', 31:'JUMPIFNOTLE', 32:'JUMPIFNOTLT',
    33:'ADD', 34:'SUB', 35:'MUL', 36:'DIV', 37:'MOD', 38:'POW',
    39:'ADDK', 40:'SUBK', 41:'MULK', 42:'DIVK', 43:'MODK', 44:'POWK',
    45:'AND', 46:'OR', 47:'ANDK', 48:'ORK',
    49:'CONCAT', 50:'NOT', 51:'MINUS', 52:'LENGTH',
    53:'NEWTABLE', 54:'DUPTABLE', 55:'SETLIST',
    56:'FORNPREP', 57:'FORNLOOP', 58:'FORGLOOP',
    59:'FORGPREP_INEXT', 60:'FASTCALL3', 61:'FORGPREP_NEXT',
    62:'NATIVECALL', 63:'GETVARARGS', 64:'DUPCLOSURE', 65:'PREPVARARGS',
    66:'LOADKX', 67:'JUMPX', 68:'FASTCALL', 69:'COVERAGE', 70:'CAPTURE',
    71:'SUBRK', 72:'DIVRK', 73:'FASTCALL1', 74:'FASTCALL2', 75:'FASTCALL2K',
    76:'FORGPREP', 77:'JUMPXEQKNIL', 78:'JUMPXEQKB', 79:'JUMPXEQKN', 80:'JUMPXEQKS',
    81:'IDIV', 82:'IDIVK',
}

AUX_OPS = frozenset({
    7, 8, 12, 15, 16, 20, 27, 28, 29, 30, 31, 32,
    53, 55, 58, 60, 66, 68, 74, 75, 77, 78, 79, 80,
})

# ── Binary helpers ─────────────────────────────────────────────────────────────
def read_varint(data: bytes, pos: int) -> Tuple[int, int]:
    r = 0; s = 0
    while True:
        b = data[pos]; pos += 1; r |= (b & 0x7F) << s; s += 7
        if b < 0x80: return r, pos

def read_u32(data: bytes, pos: int) -> Tuple[int, int]:
    return struct.unpack_from('<I', data, pos)[0], pos + 4

# ── Proto ──────────────────────────────────────────────────────────────────────
class Proto:
    __slots__ = [
        'idx', 'maxstack', 'nparams', 'nupvals', 'isvararg', 'flags',
        'typeinfo', 'instrs', 'constants', 'child_protos',
        'linedefined', 'debug_name', 'locvars', 'upval_names',
    ]
    def __init__(self):
        self.idx = 0; self.maxstack = 0; self.nparams = 0; self.nupvals = 0
        self.isvararg = 0; self.flags = 0; self.typeinfo = b''
        self.instrs = []; self.constants = []; self.child_protos = []
        self.linedefined = 0; self.debug_name = None
        self.locvars = []; self.upval_names = []

# ── Parser ─────────────────────────────────────────────────────────────────────
class Parser:
    def __init__(self, data: bytes):
        self.data = data; self.strings: List[str] = []; self.protos: List[Proto] = []
        self.version = 0; self.types_ver = 0; self.proto_count = 0; self.main_id = 0

    def run(self):
        buf = self.data; off = 0
        self.version = buf[off]; off += 1
        if self.version >= 4: self.types_ver = buf[off]; off += 1
        num_strs, off = read_varint(buf, off)
        for _ in range(num_strs):
            slen, off = read_varint(buf, off)
            self.strings.append(buf[off:off+slen].decode('utf-8', 'replace')); off += slen
        _, off = read_varint(buf, off)   # num_userdata
        self.proto_count, off = read_varint(buf, off)
        for pid in range(self.proto_count):
            p = Proto(); p.idx = pid; off = self._read_proto(p, off); self.protos.append(p)
        if off < len(buf): self.main_id, off = read_varint(buf, off)

    def _str(self, idx: int) -> Optional[str]:
        return self.strings[idx - 1] if 1 <= idx <= len(self.strings) else None

    def _read_proto(self, p: Proto, pos: int) -> int:
        buf = self.data
        p.maxstack = buf[pos]; p.nparams = buf[pos+1]; p.nupvals = buf[pos+2]
        p.isvararg = buf[pos+3]; p.flags = buf[pos+4]; pos += 5
        tf, pos = read_varint(buf, pos); p.typeinfo = buf[pos:pos+tf]; pos += tf
        isz, pos = read_varint(buf, pos)
        raw = []; consumed = 0
        while consumed < isz:
            w = struct.unpack_from('<I', buf, pos)[0]; pos += 4; consumed += 1
            aux = None
            if (w & 0xFF) in AUX_OPS and consumed < isz:
                aux = struct.unpack_from('<I', buf, pos)[0]; pos += 4; consumed += 1
            raw.append((w, aux))
        p.instrs = []; ri = 0
        for w, aux in raw:
            op = w & 0xFF; A = (w >> 8) & 0xFF; B = (w >> 16) & 0xFF; C = (w >> 24) & 0xFF
            D = (w >> 16) & 0xFFFF; sD = D - 0x10000 if D & 0x8000 else D
            E = (w >> 8) & 0xFFFFFF; sE = E - 0x1000000 if E & 0x800000 else E
            p.instrs.append((op, A, B, C, D, sD, sE, aux, ri))
            ri += 2 if op in AUX_OPS else 1
        ksz, pos = read_varint(buf, pos)
        for _ in range(ksz):
            ct = buf[pos]; pos += 1
            if ct == 0:   p.constants.append(('nil', None))
            elif ct == 1: p.constants.append(('bool', bool(buf[pos]))); pos += 1
            elif ct == 2: p.constants.append(('number', struct.unpack_from('<d', buf, pos)[0])); pos += 8
            elif ct == 3:
                idx, pos = read_varint(buf, pos); p.constants.append(('string', self._str(idx)))
            elif ct == 4:
                raw_i, pos = read_u32(buf, pos); p.constants.append(('import', raw_i))
            elif ct == 5:
                sl, pos = read_varint(buf, pos); keys = []
                for _ in range(sl): k, pos = read_varint(buf, pos); keys.append(self._str(k))
                p.constants.append(('table', keys))
            elif ct == 6: idx, pos = read_varint(buf, pos); p.constants.append(('closure', idx))
            elif ct == 7:
                xyzw = [struct.unpack_from('<f', buf, pos+i*4)[0] for i in range(4)]; pos += 16
                p.constants.append(('vector', tuple(xyzw)))
            elif ct == 8: p.constants.append(('int', struct.unpack_from('<i', buf, pos)[0])); pos += 4
            else: p.constants.append(('unknown', ct))
        csz, pos = read_varint(buf, pos)
        for _ in range(csz): idx, pos = read_varint(buf, pos); p.child_protos.append(idx)
        p.linedefined, pos = read_varint(buf, pos)
        dn, pos = read_varint(buf, pos); p.debug_name = self._str(dn)
        hl = buf[pos]; pos += 1
        if hl:
            lg = buf[pos]; pos += 1; pos += isz
            ivs = ((isz - 1) >> lg) + 1 if lg < 32 and isz > 0 else 0; pos += ivs * 4
        hd = buf[pos]; pos += 1
        if hd:
            dlsz, pos = read_varint(buf, pos)
            for _ in range(dlsz):
                ni2, pos = read_varint(buf, pos); sp2, pos = read_varint(buf, pos)
                ep, pos = read_varint(buf, pos); reg = buf[pos]; pos += 1
                p.locvars.append((reg, self._str(ni2), sp2, ep))
            dusz, pos = read_varint(buf, pos)
            for _ in range(dusz): ui2, pos = read_varint(buf, pos); p.upval_names.append(self._str(ui2))
        if self.version >= 7:
            sz, pos = read_varint(buf, pos)
            for _ in range(sz): _, pos = read_varint(buf, pos)
        return pos


# ── Constant helpers ───────────────────────────────────────────────────────────
def _fmt(c) -> str:
    kt, v = c
    if kt == 'nil':    return 'nil'
    if kt == 'bool':   return 'true' if v else 'false'
    if kt == 'int':    return str(v)
    if kt == 'number':
        try:
            if v == int(v) and abs(v) < 1e15: return str(int(v))
        except:
            return "0"
        return repr(v)
    if kt == 'string':
        if v is None: return 'nil'
        return '"' + v.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'
    if kt == 'import': return f'<import 0x{v:08X}>'   # raw; resolved via K[D-1]
    if kt == 'vector': return f'Vector3.new({v[0]:.4g}, {v[1]:.4g}, {v[2]:.4g})'
    if kt == 'closure': return f'function{v}'
    if kt == 'table':   return '{' + ', '.join(repr(k) for k in v if k) + '}'
    return 'nil'

def _hint(c) -> str:
    kt = c[0]
    if kt == 'string':         return 'Str'
    if kt in ('number', 'int'): return 'Num'
    if kt == 'bool':           return 'Bool'
    if kt in ('import', 'closure'): return 'Func'
    if kt == 'table':          return 'Table'
    return 'Var'

def _getimport_name(constants: list, D: int) -> str:
    """
    GETIMPORT name rule: the global name is the string constant at K[D-1].
    The import constant at K[D] is metadata; the name always lives in K[D-1].
    Fallback: try K[D] if it is a string, then 'K[D]'.
    """
    if D > 0 and D <= len(constants):
        prev = constants[D - 1]
        if prev[0] == 'string' and prev[1]:
            return prev[1]
    if 0 <= D < len(constants):
        c = constants[D]
        if c[0] == 'string' and c[1]: return c[1]
    return f'K[{D}]'


# ── Emitter ────────────────────────────────────────────────────────────────────
class Emitter:
    def __init__(self):
        self._lines: List[str] = []; self._depth = 0
    def indent(self):  self._depth += 1
    def dedent(self):  self._depth = max(0, self._depth - 1)
    def emit(self, line: str = ''):
        self._lines.append('' if not line else '    ' * self._depth + line)
    def lines(self): return self._lines


# ── Global upvalue state ──────────────────────────────────────────────────────
_up_counter: int = 0

def _next_up() -> str:
    global _up_counter
    _up_counter += 1
    return f'up_{_up_counter}'

# Maps proto_idx -> {upval_slot -> ('val', src_reg) | ('ref', up_name) | ('pass', slot)}
_cap_info: Dict[int, Dict[int, tuple]] = {}

# Maps proto_idx -> {slot -> expr_string} for val captures (populated at runtime)
_cap_val_exprs: Dict[int, Dict[int, str]] = {}

# Maps src_reg_in_main -> up_N name (for ref captures)
# These are declared as `local up_N = nil` at the very top of script output
_ref_upval_names: Dict[int, str] = {}   # src_reg -> up_name

# Table val captures: proto_idx -> {slot -> '_UTable<N>'} name
# When a val capture's source register holds a table (NEWTABLE/DUPTABLE),
# we DON'T inline {} or a variable name — we use a stable _UTableN alias.
_utable_counter: int = 0
_val_table_names: Dict[int, Dict[int, str]] = {}  # proto_idx -> {slot -> '_UTableN'}
_main_table_reg_to_utable: Dict[int, set] = {}    # main src_reg -> set of _UTableN names

def _next_utable() -> str:
    global _utable_counter
    _utable_counter += 1
    return f'_UTable{_utable_counter}' 


def _prepass_captures(main_proto: 'Proto', all_protos: List['Proto']) -> Dict[int, str]:
    """
    Walk the main proto's NEWCLOSURE/DUPCLOSURE + CAPTURE sequences.
    Returns {src_reg: up_name} for all ref captures — these become top-level locals.
    Fills _cap_info for every child proto.
    """
    global _ref_upval_names
    _ref_upval_names = {}
    instrs = main_proto.instrs
    n = len(instrs)
    consts = main_proto.constants

    # We need register expressions at the time of each closure.
    # Since this is a pre-pass (no expressions yet), we track what is "obviously"
    # in each register by a lightweight scan: only GETIMPORT, LOADK, NEWTABLE, CALL results.
    # This gives us the expressions to record for val captures.
    # We'll store them as strings. The real expression comes from the decompile pass,
    # but for the pre-pass we only need the ref/val distinction and the up_N names.
    # Val inlining uses the actual reg_expr from decompile_proto at runtime.

    # Pre-scan: find which registers hold tables (NEWTABLE/DUPTABLE) in main
    table_regs: set = set()
    for instr in instrs:
        if instr[0] in (53, 54):  # NEWTABLE, DUPTABLE
            table_regs.add(instr[1])   # register A

    # One _UTableN per src_reg (shared across all children that capture same table)
    _src_reg_to_utable: Dict[int, str] = {}

    i = 0
    while i < n:
        op, A, B, C, D, sD, sE, aux, ri = instrs[i]
        if op in (19, 64):  # NEWCLOSURE, DUPCLOSURE
            if op == 19:
                child_idx = D
            else:
                child_idx = consts[D][1] if 0 <= D < len(consts) and consts[D][0] == 'closure' else None

            if child_idx is not None:
                caps: Dict[int, tuple] = {}
                slot = 0
                j = i + 1
                while j < n and instrs[j][0] == 70:
                    _, ca, cb, cc, _, _, _, _, _ = instrs[j]
                    if ca == 0:    # val: copy of parent register
                        if cb in table_regs:
                            # Table val capture: one stable _UTableN per src_reg (shared across all children)
                            if cb not in _src_reg_to_utable:
                                _src_reg_to_utable[cb] = _next_utable()
                            ut_name = _src_reg_to_utable[cb]
                            _val_table_names.setdefault(child_idx, {})[slot] = ut_name
                            caps[slot] = ('val_table', cb, ut_name)
                        else:
                            caps[slot] = ('val', cb)   # cb = src register in parent
                    elif ca == 1:  # ref: shared mutable reference
                        if cb not in _ref_upval_names:
                            _ref_upval_names[cb] = _next_up()
                        up_name = _ref_upval_names[cb]
                        caps[slot] = ('ref', up_name)
                    else:          # upval passthrough
                        caps[slot] = ('pass', cb)
                    slot += 1; j += 1

                if child_idx not in _cap_info:
                    _cap_info[child_idx] = caps
        i += 1

    # Build main_table_reg_to_utable: src_reg -> set of _UTableN names
    # (one reg may be captured into multiple child protos with different _UTableN names,
    # but in practice all children that capture the same table get the same _UTableN)
    global _main_table_reg_to_utable
    _main_table_reg_to_utable = {}
    for child_idx, cap_dict in _cap_info.items():
        for slot, info in cap_dict.items():
            if info[0] == 'val_table':
                src_reg = info[1]; ut_name = info[2]
                _main_table_reg_to_utable.setdefault(src_reg, set()).add(ut_name)

    return _ref_upval_names


# ── Parameter reconstruction ───────────────────────────────────────────────────
def _params(proto: Proto) -> List[str]:
    if not proto.nparams: return []
    pm: Dict[int, str] = {}
    for (reg, name, sp, ep) in proto.locvars:
        if sp == 0 and reg < proto.nparams and name:
            pm[reg] = name
    return [pm.get(i, f'arg{i+1}') for i in range(proto.nparams)]


# ── Pre-scan: write counts and use counts ──────────────────────────────────────
WRITE_OPS = frozenset({
    2, 3, 4, 5, 6, 7, 9, 12, 13, 15, 17, 19, 21, 33, 34, 35, 36, 37, 38,
    39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 56,
    63, 64, 66, 71, 72, 81, 82,
})

def _prescan(instrs, nparams: int) -> Tuple[Dict[int,int], Dict[int,int]]:
    """Return (write_count[reg], use_count[reg])."""
    wc: Dict[int,int] = {}
    uc: Dict[int,int] = {}
    def w(r): wc[r] = wc.get(r, 0) + 1
    def u(r): uc[r] = uc.get(r, 0) + 1
    for i in range(nparams): w(i)
    for instr in instrs:
        op, A, B, C, D, sD, sE, aux, ri = instr
        if op in WRITE_OPS:
            # GETTABLEKS self-chain (A==B): not a new variable, just extends expression
            if not (op == 15 and A == B):
                w(A)
        if op == 21:  # CALL also writes A on result
            if C > 1:
                for x in range(A, A + C - 1): w(x)
            # reads
            cnt = B if B > 0 else 2
            for x in range(A, A + cnt): u(x)
        elif op == 6:  u(B)          # MOVE
        elif op == 10: u(A)          # SETUPVAL reads A
        elif op == 8:  u(A)          # SETGLOBAL reads A
        elif op in (13, 14): u(B); u(C)
        elif op == 15:
            if A != B: u(B)  # self-chain: A==B not a separate use
        elif op == 16: u(A); u(B)   # SETTABLEKS: reads A (value) and B (table)
        elif op == 17: u(B)
        elif op == 18: u(A); u(B)
        elif op == 20: u(B)          # NAMECALL reads B
        elif op == 22:               # RETURN
            if B == 0: u(A)
            elif B > 1:
                for x in range(A, A + B - 1): u(x)
        elif op in (25, 26): u(A)
        elif op in (27, 28, 29, 30, 31, 32): u(A); (u(aux) if aux is not None else None)
        elif op in (33,34,35,36,37,38,45,46,49): u(B); u(C)
        elif op in (39,40,41,42,43,44,47,48): u(B)
        elif op in (50, 51, 52): u(B)
        elif op in (55,): u(A)
        elif op in (77, 78, 79, 80): u(A)
        elif op in (71, 72): u(B); u(C)
    return wc, uc


# ── Proto decompiler ───────────────────────────────────────────────────────────
def _fname(proto: Proto) -> str:
    return proto.debug_name or f'function{proto.idx}'


def decompile_proto(proto: Proto, all_protos: List[Proto], is_main: bool = False) -> str:
    fname = _fname(proto)
    out = Emitter()
    param_names = _params(proto)

    if is_main:
        out.emit(f'-- [MAIN] function{proto.idx}')
        if proto.typeinfo: out.emit(f'-- type-annotated (tf_size={len(proto.typeinfo)})')
    else:
        out.emit(f'-- [function{proto.idx}] {fname}')
        if proto.typeinfo: out.emit(f'-- type-annotated (tf_size={len(proto.typeinfo)})')
        params = list(param_names) + (['...'] if proto.isvararg else [])
        out.emit(f'local function {fname}({", ".join(params)})')
        out.indent()

    if not proto.instrs:
        if proto.constants:
            out.emit('-- constants:')
            for i, c in enumerate(proto.constants[:16]): out.emit(f'--   [{i}] {_fmt(c)}')
        if proto.upval_names:
            out.emit(f'-- upvalues: {[n or f"_u{i}" for i,n in enumerate(proto.upval_names)]}')
        if proto.child_protos:
            out.emit(f'-- child protos: {proto.child_protos[:16]}')
        if not is_main: out.dedent(); out.emit('end')
        return '\n'.join(out.lines())

    consts = proto.constants

    # ── Upvalue map ────────────────────────────────────────────────────────────
    # uv_name[slot]   = name for GETUPVAL/SETUPVAL (ref captures use up_N)
    # uv_val_reg[slot] = parent src register for val captures (expression resolved later)
    uv_name: Dict[int, str] = {}
    uv_val_reg: Dict[int, int] = {}   # slot -> parent src_reg (val capture)
    for i, nm in enumerate(proto.upval_names):
        uv_name[i] = nm if nm else f'_u{i}'
    for i in range(proto.nupvals):
        if i not in uv_name: uv_name[i] = f'_u{i}'

    cap = _cap_info.get(proto.idx, {})
    # Load val capture expressions resolved by parent's _process_closure call
    uv_val_exprs: Dict[int, Optional[str]] = _cap_val_exprs.get(proto.idx, {}).copy()
    for slot, info in cap.items():
        kind = info[0]
        if kind == 'val':
            src_reg = info[1]
            uv_val_reg[slot] = src_reg
        elif kind == 'ref':
            up_name = info[1]
            uv_name[slot] = up_name

    # For the MAIN proto: rename ref-capture source registers to their up_N names
    _main_ref_renames: Dict[int, str] = {}
    if is_main:
        _main_ref_renames = _ref_upval_names  # src_reg -> up_N

    def kupval(u: int) -> str:
        """Resolve upvalue slot to an expression string."""
        # Check for val_table capture first: use _UTableN alias
        cap_entry = cap.get(u)
        if cap_entry and cap_entry[0] == 'val_table':
            return cap_entry[2]   # e.g. '_UTable1'
        if u in uv_val_reg:
            # val capture: inline the parent reg's expression
            expr = uv_val_exprs.get(u)
            if expr is not None:
                return expr
        return uv_name.get(u, f'_u{u}')

    # ── Pre-scan ───────────────────────────────────────────────────────────────
    wc, uc = _prescan(proto.instrs, proto.nparams)

    last_read_pc: Dict[int, int] = {}  # populated after instrs is assigned below

    _last_read_scan_pending = True  # sentinel
    for lpc2, ins2 in enumerate(proto.instrs):
        op2,A2,B2,C2,D2,sD2,sE2,aux2,ri2 = ins2
        def _mark_read(r):
            if r >= 0: last_read_pc[r] = lpc2
        if op2 == 6: _mark_read(B2)
        elif op2 in (13,14): _mark_read(B2); _mark_read(C2)
        elif op2 == 15: _mark_read(B2)
        elif op2 == 16: _mark_read(A2); _mark_read(B2)  # value=A, table=B
        elif op2 == 17: _mark_read(B2)
        elif op2 == 18: _mark_read(A2); _mark_read(B2)
        elif op2 == 20: _mark_read(B2)
        elif op2 == 21:
            _mark_read(A2)
            cnt = B2 if B2 > 0 else 2
            for x in range(A2+1, A2+cnt): _mark_read(x)
        elif op2 == 22:
            if B2 == 0: _mark_read(A2)
            elif B2 > 1:
                for x in range(A2, A2+B2-1): _mark_read(x)
        elif op2 in (25,26): _mark_read(A2)
        elif op2 in (27,28,29,30,31,32): _mark_read(A2); (lambda: _mark_read(aux2) if aux2 is not None else None)()
        elif op2 in (33,34,35,36,37,38,45,46,49): _mark_read(B2); _mark_read(C2)
        elif op2 in (39,40,41,42,43,44,47,48): _mark_read(B2)
        elif op2 in (50,51,52): _mark_read(B2)
        elif op2 in (77,78,79,80): _mark_read(A2)
        elif op2 in (71,72): _mark_read(B2); _mark_read(C2)
        elif op2 == 10: _mark_read(A2)
        elif op2 == 8: _mark_read(A2)

    # ── Register state ─────────────────────────────────────────────────────────
    # reg_name:  register -> current Lua name (for mutation / multi-write regs)
    # reg_expr:  register -> current propagatable expression (single-write only)
    # declared:  set of registers that already have 'local x' in scope
    # is_call:   registers set by a CALL (can't be inlined)
    reg_name: Dict[int, str] = {}
    reg_expr: Dict[int, Optional[str]] = {}   # propagatable expr (single-write only)
    reg_raw:  Dict[int, str] = {}             # last raw expression (always updated)
    declared: Set[int] = set()
    is_call:  Set[int] = set()
    always_inline: Set[int] = set()           # registers whose expr always inlines (GETIMPORT)
    name_cnt: Dict[str, int] = {}
    _nc_fn:   Dict[int, str] = {}   # NAMECALL: A -> "obj:method" expression
    _nc_self: Dict[int, int] = {}   # NAMECALL: A -> self_reg (for is_nc detection)

    def fresh(hint: str) -> str:
        name_cnt[hint] = name_cnt.get(hint, 0) + 1
        return f'{hint}{name_cnt[hint]}'

    # Seed params
    for i, pname in enumerate(param_names):
        reg_name[i] = pname; reg_expr[i] = pname; declared.add(i)

    # Seed locvars that start at pc=0 (named locals)
    for (reg, nm, sp, ep) in proto.locvars:
        if nm and sp == 0 and reg not in declared:
            reg_name[reg] = nm; reg_expr[reg] = nm; declared.add(reg)

    # _main_ref_renames: src_reg -> up_N for ref-capture registers in main.
    # We do NOT pre-seed reg_name here because the same register may be used
    # for other purposes before the LOADNIL that initializes the ref-capture.
    # Instead, declare() checks _main_ref_renames at write time.

    def get_expr(r: int) -> str:
        """Best expression for register r.
        Inline if: single-write non-call uc<=1, OR always_inline (GETIMPORT),
        OR this is the LAST read of r (last-use propagation for scratch regs)."""
        expr = reg_expr.get(r)
        if expr is None:
            return reg_name.get(r, f'r{r}')
        # Always-inline: GETIMPORT values (game, script, plugin, workspace) are constants
        if r in always_inline:
            return expr
        # Single-write single-use: propagate
        if (wc.get(r, 0) == 1 and r not in is_call
                and r not in range(proto.nparams) and uc.get(r, 0) <= 1):
            return expr
        # Last-use propagation: if current pc is the last read of this register,
        # inline the expression — but only for "stable" pure expressions.
        # Don't inline mutable tables ({}), call results (is_call), or params.
        if (r not in is_call and r not in range(proto.nparams)
                and last_read_pc.get(r, -1) == pc
                and expr not in ('{}', 'nil', 'true', 'false')
                and not expr.startswith('"')):
            return expr
        # Window propagation: multi-write register but this write has only 1 read
        # before the next write (separate lifetime). Propagate if stable expression.
        # Only for non-call results (call results may have side effects that must run in order).
        if (r not in is_call and r not in range(proto.nparams)
                and expr not in ('{}', 'nil', 'true', 'false')
                and not expr.startswith('"')
                and _can_propagate_window(r, pc)):
            return expr
        return reg_name.get(r, f'r{r}')

    def kreg(r: int) -> str:
        return get_expr(r)

    def _substitute(expr: str) -> str:
        """Replace variable names in expr with their fully-inlined values.
        Used to build deep expressions for val capture snapping."""
        if not expr:
            return expr
        result = expr
        # Try each known register name and replace it if it appears as a word boundary
        import re
        for r2, nm in list(reg_name.items()):
            if nm and nm in result:
                # Get the deepest inline value for this register
                raw2 = reg_raw.get(r2)
                if raw2 and raw2 != nm and nm != raw2:
                    # Replace the variable name with its value
                    # Use word boundary to avoid partial matches
                    result = re.sub(r'(?<![\w.])\b' + re.escape(nm) + r'\b(?![\w(])', raw2, result)
        return result

    def kc(k: int) -> str:
        return _fmt(consts[k]) if 0 <= k < len(consts) else f'K[{k}]'

    def cname(idx: int) -> str:
        return _fname(all_protos[idx]) if 0 <= idx < len(all_protos) else f'function{idx}'

    def meth_str(aux) -> str:
        """Key name from NAMECALL/GETTABLEKS aux (aux & 0x7FFFFF = K index)."""
        if aux is not None:
            ki = aux & 0x7FFFFF
            if 0 <= ki < len(consts) and consts[ki][0] == 'string' and consts[ki][1]:
                return consts[ki][1]
        return f'K[{aux}]'

    def declare(r: int, expr: str, hint: str = 'Var',
                call: bool = False, always_inline_expr: bool = False) -> str:
        """
        Every value-producing instruction always creates a fresh local binding.
        - always_inline_expr: if True (e.g. GETIMPORT), the expression is always
          inlined at use sites regardless of write count (it's a global constant).
        - Propagate silently (no 'local' emit) if single-write and single-use.
        - Tracks reg_raw[r] = raw expression (for val capture snapping).
        """
        wcount = wc.get(r, 0)
        ucount = uc.get(r, 0)
        # Store fully-substituted expression for val capture snapping.
        # Replace any variable names with their current inline values.
        reg_raw[r] = _substitute(expr)

        # Check if this register is a ref-capture source in main (up_N naming)
        if is_main and r in _main_ref_renames and expr == 'nil':
            nm = _main_ref_renames[r]
            reg_name[r] = nm
        elif r in reg_name:
            nm = fresh(hint); reg_name[r] = nm
        else:
            nm = fresh(hint); reg_name[r] = nm

        reg_expr[r] = expr
        if call: is_call.add(r)
        if always_inline_expr: always_inline.add(r)

        # Always-inline registers (GETIMPORT) are never emitted as locals
        if always_inline_expr:
            return nm
        # Propagate silently: don't emit 'local' if the value will be inlined
        if wcount <= 1 and not call and ucount <= 1:
            return nm
        # Last-use: if this is the last read of r, we won't need a named local
        # Only for stable expressions (not tables, not call results, not string literals)
        if (not call and last_read_pc.get(r, -1) >= pc and ucount <= 1
                and expr not in ('{}', 'nil', 'true', 'false')
                and not expr.startswith('"')):
            return nm
        # Window propagation: this write has only 1 read before next write (single-use lifetime)
        # Only for non-call-result writes (call results have observable order of execution).
        if (not call
                and r not in is_call
                and expr not in ('{}', 'nil', 'true', 'false')
                and not expr.startswith('"')
                and _can_propagate_window(r, pc)):
            return nm
        out.emit(f'local {nm} = {expr}')
        return nm

    # ── Jump / control-flow helpers ────────────────────────────────────────────
    instrs = proto.instrs; n = len(instrs)

    # Build last_read_pc now that instrs is assigned
    # (The loop above used proto.instrs directly; last_read_pc is already populated)

    # Build next_write_pc[r] = list of pcs where register r is written, in order
    # Used to detect single-use windows for multi-write registers
    import bisect as _bisect
    _write_pcs: Dict[int, list] = {}
    for _wpc, _wi in enumerate(instrs):
        _wop, _wA, _wB, _wC = _wi[0], _wi[1], _wi[2], _wi[3]
        if _wop in WRITE_OPS and not (_wop == 15 and _wA == _wB):
            _write_pcs.setdefault(_wA, []).append(_wpc)
        if _wop == 21 and _wC > 1:
            for _x in range(_wA, _wA + _wC - 1):
                _write_pcs.setdefault(_x, []).append(_wpc)

    def _reads_in_window(r: int, start_pc: int, end_pc: int) -> int:
        """Count how many times register r is read between start_pc and end_pc (exclusive)."""
        cnt = 0
        for _rpc in range(start_pc + 1, end_pc):
            _ri = instrs[_rpc]
            _rop, _rA, _rB, _rC, _rD = _ri[0], _ri[1], _ri[2], _ri[3], _ri[4]
            aux_r = _ri[7]
            reads_r = False
            if _rop == 6 and _rB == r: reads_r = True
            elif _rop in (13, 14) and (_rB == r or _rC == r): reads_r = True
            elif _rop == 15 and _rB == r and _rB != _rA: reads_r = True
            elif _rop == 16 and (_rA == r or _rB == r): reads_r = True
            elif _rop == 20 and _rB == r: reads_r = True
            elif _rop == 21:
                if _rA == r: reads_r = True
                _cnt2 = _rB if _rB > 0 else 2
                if r in range(_rA + 1, _rA + _cnt2): reads_r = True
            elif _rop == 22 and _rB == 0 and _rA == r: reads_r = True
            elif _rop in (25, 26) and _rA == r: reads_r = True
            if reads_r: cnt += 1
        return cnt

    def _can_propagate_window(r: int, declare_pc: int) -> bool:
        """True if register r has only 1 read between declare_pc and the next write to r."""
        writes = _write_pcs.get(r, [])
        # Find the next write after declare_pc
        idx = _bisect.bisect_right(writes, declare_pc)
        if idx >= len(writes):
            return False  # no next write; handled by normal single-write propagation
        next_write = writes[idx]
        reads = _reads_in_window(r, declare_pc, next_write)
        return reads <= 1

    raw_to_logical: Dict[int, int] = {}
    for lpc, instr in enumerate(instrs): raw_to_logical[instr[8]] = lpc

    ELSEIF_OPS = frozenset({77, 78, 79, 80})

    def jmp(ri: int, sd: int) -> int:
        return raw_to_logical.get(ri + 1 + sd, n)

    elseif_pcs: Set[int] = set()
    for lpc2, instr2 in enumerate(instrs):
        if instr2[0] in ELSEIF_OPS:
            t2 = jmp(instr2[8], instr2[5])
            if 0 <= t2 < n and instrs[t2][0] in ELSEIF_OPS:
                elseif_pcs.add(t2)

    def open_branch(tgt_l: int, cond: str, cur_pc: int):
        if cur_pc in elseif_pcs and out._lines and out._lines[-1].strip() == 'end':
            out._lines.pop()
            out.emit(f'elseif {cond} then')
            out.indent()
            struct_stack.append(('elseif', tgt_l))
        else:
            out.emit(f'if {cond} then')
            out.indent()
            struct_stack.append(('if', tgt_l))

    struct_stack: List[Tuple[str, int]] = []
    skip_next = False

    # Snapshot of register expressions at a given pc (for CAPTURE val analysis).
    # Use reg_name for multi-use registers (they will be emitted as named locals).
    # Use reg_raw (substituted) for single-write/always-inline registers.
    def snap() -> Dict[int, str]:
        result = {}
        for r in set(list(reg_name.keys()) + list(reg_raw.keys())):
            nm = reg_name.get(r)
            raw = reg_raw.get(r)
            wcount = wc.get(r, 0)
            ucount = uc.get(r, 0)
            if r in always_inline:
                # GETIMPORT — use raw (the global name like 'game', 'script')
                if raw: result[r] = raw
            elif wcount <= 1 and not (r in is_call) and ucount <= 1 and raw:
                # Single-write single-use: use substituted raw expression
                result[r] = raw
            elif nm and not nm.startswith('r'):
                # Multi-use: use the variable name (e.g. 'Table1', 'Var5')
                result[r] = nm
        return result

    pc = 0
    while pc < n:
        op, A, B, C, D, sD, sE, aux, raw_idx = instrs[pc]

        # Close structures
        while struct_stack and struct_stack[-1][1] == pc:
            kind, _ = struct_stack.pop()
            if kind in ('if', 'else', 'elseif', 'for_num', 'for_gen', 'while'):
                out.dedent(); out.emit('end')

        if skip_next: skip_next = False; pc += 1; continue

        # ── Instruction handlers ───────────────────────────────────────────────
        if op in (0, 1): pass  # NOP, BREAK

        elif op == 2:   # LOADNIL R[A..A+B]=nil
            for r in range(A, A + B + 1): declare(r, 'nil', 'Var')

        elif op == 3:   # LOADB A=B; if C skip next
            declare(A, 'true' if B else 'false', 'Bool')
            if C: skip_next = True

        elif op == 4:   # LOADN A=sD
            declare(A, str(sD), 'Num')

        elif op == 5:   # LOADK A=K[D]
            if 0 <= D < len(consts):
                declare(A, kc(D), _hint(consts[D]))
            else:
                declare(A, f'K[{D}]', 'Var')

        elif op == 6:   # MOVE A=B — register copy
            src_expr = get_expr(B)
            src_raw  = reg_raw.get(B, src_expr)
            # Propagate silently (no local) when source is:
            # - a function name from NEWCLOSURE/DUPCLOSURE (not a table/nil/call result)
            # - an always_inline import  
            # - a single-write non-call non-table register
            # Propagate silently when source is stable:
            # - always_inline (GETIMPORT globals)
            # - single-write non-table/non-nil/non-string  
            # - call results are ALSO stable for MOVE (the value was computed and fixed)
            is_stable = (B in always_inline or
                         (wc.get(B,0) <= 1 and
                          src_raw not in ('nil', '{}') and
                          not src_raw.startswith('"')))
            if is_stable:
                reg_name[A] = src_expr
                reg_expr[A] = src_expr
                reg_raw[A]  = src_raw
            else:
                declare(A, src_expr, 'Var')

        elif op == 7:   # GETGLOBAL A=global[K[aux]]
            name = meth_str(aux)
            declare(A, name, 'Func')

        elif op == 8:   # SETGLOBAL global[K[aux]]=A
            out.emit(f'{meth_str(aux)} = {kreg(A)}')

        elif op == 9:   # GETUPVAL A=upval[B]
            val = kupval(B)
            declare(A, val, 'Var')

        elif op == 10:  # SETUPVAL upval[B]=A
            out.emit(f'{uv_name.get(B, f"_u{B}")} = {kreg(A)}')

        elif op == 11: pass  # CLOSEUPVALS

        elif op == 12:  # GETIMPORT A=global; name from K[D-1]
            name = _getimport_name(consts, D)
            hint = 'Func'
            # GETIMPORT values (game, script, plugin, workspace) are global constants.
            # Always inline them at use sites — never emit a 'local Func1 = game' line.
            declare(A, name, hint, always_inline_expr=True)

        elif op == 13:  # GETTABLE A=B[C]
            declare(A, f'{kreg(B)}[{kreg(C)}]', 'Var')

        elif op == 14:  # SETTABLE A[B]=C
            out.emit(f'{kreg(A)}[{kreg(B)}] = {kreg(C)}')

        elif op == 15:  # GETTABLEKS A=B[K[aux]]
            obj = kreg(B)
            ki = aux & 0x7FFFFF if aux is not None else 0
            if 0 <= ki < len(consts) and consts[ki][0] == 'string' and consts[ki][1]:
                k = consts[ki][1]
                field = f'{obj}.{k}' if k.isidentifier() else f'{obj}[{_fmt(consts[ki])}]'
            else:
                field = f'{obj}[{kc(ki)}]'
            if A == B:
                # Self-chain: R[A] = R[A].field — extend expression in-place, no new local
                reg_expr[A] = field
                reg_raw[A]  = _substitute(field)
                # Don't change reg_name — keeps the same slot, expression updated
            else:
                declare(A, field, 'Var')

        elif op == 16:  # SETTABLEKS B[K[aux]] = A  (A=value, B=table)
            tbl = kreg(B); val = kreg(A)
            ki = aux & 0x7FFFFF if aux is not None else 0
            if 0 <= ki < len(consts) and consts[ki][0] == 'string' and consts[ki][1]:
                k = consts[ki][1]
                lhs = f'{tbl}.{k}' if k.isidentifier() else f'{tbl}[{_fmt(consts[ki])}]'
            else:
                lhs = f'{tbl}[{kc(ki)}]'
            out.emit(f'{lhs} = {val}')

        elif op == 17:  # GETTABLEN A=B[C+1]
            declare(A, f'{kreg(B)}[{C+1}]', 'Var')

        elif op == 18:  # SETTABLEN A[C+1]=B
            out.emit(f'{kreg(A)}[{C+1}] = {kreg(B)}')

        elif op == 19:  # NEWCLOSURE A=proto[D]
            _process_closure(proto, instrs, pc, snap(), D)
            func_expr = cname(D)
            # Look past CAPTURE instructions to find if next is SETTABLEKS on reg A
            _look = pc + 1
            while _look < n and instrs[_look][0] == 70: _look += 1
            _next_op = instrs[_look][0] if _look < n else -1
            _next_B  = instrs[_look][2] if _look < n else -1  # SETTABLEKS: B=table reg
            _next_A  = instrs[_look][1] if _look < n else -1  # SETTABLEKS: A=value reg
            if _next_op == 16 and _next_A == A:
                # Directly assign into the table — no intermediate local needed
                reg_name[A] = func_expr; reg_expr[A] = func_expr; reg_raw[A] = func_expr
            else:
                reg_raw[A] = func_expr
                declare(A, func_expr, 'Func')
            _emit_ref_captures(out, proto, instrs, pc, reg_expr)

        elif op == 20:  # NAMECALL setup — consumed by CALL
            obj = kreg(B); m = meth_str(aux)
            # Store method call expression for A; mark A+1 as namecall sentinel
            # Use a side-table so we don't clobber pre-seeded names (e.g. up_N)
            _nc_fn[A]   = f'{obj}:{m}'
            _nc_self[A] = A+1    # which register holds the sentinel
            reg_expr[A] = f'{obj}:{m}' 

        elif op == 21:  # CALL
            # Use namecall side-table if available, else get_expr
            fn = _nc_fn.pop(A, None) or get_expr(A)
            is_nc = A in _nc_self
            self_reg = _nc_self.pop(A, None)
            if B == 0:
                start = A+2 if is_nc else A+1; args = [kreg(start)]
            else:
                start = A+2 if is_nc else A+1
                count = B - 2 if is_nc else B - 1
                args = [kreg(start + i) for i in range(max(0, count))]
            call_expr = f'{fn}({", ".join(args)})'
            # Clear the function register's namecall entry; don't touch reg_name[A] if pre-seeded
            reg_expr.pop(A, None)
            if C == 1:
                out.emit(call_expr)
            elif C == 0:
                declare(A, call_expr, 'Var', call=True)
            else:
                nms = []
                for i in range(C - 1):
                    nm = fresh('Var'); reg_name[A+i] = nm; reg_expr[A+i] = nm
                    reg_raw[A+i] = _substitute(call_expr)  # track raw for val capture
                    is_call.add(A+i); nms.append(nm)
                out.emit(f'local {", ".join(nms)} = {call_expr}')

        elif op == 22:  # RETURN
            if B == 1:    out.emit('return')
            elif B == 0:  out.emit(f'return {kreg(A)} --[[, ...]]')
            else:         out.emit(f'return {", ".join(kreg(A+i) for i in range(B-1))}')
            if pc == n - 1:
                while struct_stack:
                    kind, _ = struct_stack.pop()
                    if kind in ('if', 'else', 'elseif', 'for_num', 'for_gen', 'while'):
                        out.dedent(); out.emit('end')

        elif op == 23:  # JUMP
            if sD >= 0:
                tgt_l = jmp(raw_idx, sD)
                if struct_stack and struct_stack[-1][0] in ('if', 'elseif'):
                    kind, close_at = struct_stack.pop(); out.dedent()
                    if tgt_l > close_at:
                        out.emit('else'); out.indent(); struct_stack.append(('else', tgt_l))
                    else:
                        out.emit('end')

        elif op == 24: pass  # JUMPBACK

        elif op == 25:  # JUMPIF (jump if truthy → invert for then-body)
            open_branch(jmp(raw_idx, sD), f'not {kreg(A)}', pc)

        elif op == 26:  # JUMPIFNOT (jump if falsy → keep for then-body)
            open_branch(jmp(raw_idx, sD), kreg(A), pc)

        elif op in (27, 28, 29, 30, 31, 32):  # JUMPCMP (jump when true → invert)
            rhs = kreg(aux) if aux is not None else '?'
            inv = {27:'~=', 28:'>', 29:'>=', 30:'==', 31:'<=', 32:'<'}
            open_branch(jmp(raw_idx, sD), f'{kreg(A)} {inv[op]} {rhs}', pc)

        elif op in (33,34,35,36,37,38):
            sym = {33:'+',34:'-',35:'*',36:'/',37:'%',38:'^'}[op]
            declare(A, f'{kreg(B)} {sym} {kreg(C)}', 'Num')
        elif op in (39,40,41,42,43,44):
            sym = {39:'+',40:'-',41:'*',42:'/',43:'%',44:'^'}[op]
            declare(A, f'{kreg(B)} {sym} {kc(C)}', 'Num')
        elif op == 45: declare(A, f'{kreg(B)} and {kreg(C)}', 'Var')
        elif op == 46: declare(A, f'{kreg(B)} or {kreg(C)}', 'Var')
        elif op == 47: declare(A, f'{kreg(B)} and {kc(C)}', 'Var')
        elif op == 48: declare(A, f'{kreg(B)} or {kc(C)}', 'Var')
        elif op == 49:
            declare(A, ' .. '.join(kreg(B+i) for i in range(C-B+1)), 'Str')
        elif op == 50: declare(A, f'not {kreg(B)}', 'Bool')
        elif op == 51: declare(A, f'-{kreg(B)}', 'Num')
        elif op == 52: declare(A, f'#{kreg(B)}', 'Num')
        elif op == 53:  # NEWTABLE
            nm = declare(A, '{}', 'Table')
            # If this register is captured as val_table into child protos,
            # assign the _UTableN alias so children can reference it
            if is_main and A in _main_table_reg_to_utable:
                for ut_name in sorted(_main_table_reg_to_utable[A]):
                    out.emit(f'{ut_name} = {nm}')
        elif op == 54:  # DUPTABLE A = copy of table template K[D]
            # K[D] is a table shape (key list). Emit as '{}' — SETTABLEKS fills values.
            nm = declare(A, '{}', 'Table')
            if is_main and A in _main_table_reg_to_utable:
                for ut_name in sorted(_main_table_reg_to_utable[A]):
                    out.emit(f'{ut_name} = {nm}')

        elif op == 55:  # SETLIST
            out.emit(f'-- SETLIST {kreg(A)}[{B}..] = {{{", ".join(kreg(A+1+i) for i in range(C))}}}')

        elif op == 56:  # FORNPREP
            nm = fresh('Num'); reg_name[A+3] = nm; reg_expr[A+3] = nm
            out.emit(f'for {nm} = {kreg(A+2)}, {kreg(A)}, {kreg(A+1)} do')
            out.indent(); struct_stack.append(('for_num', pc + 1 + sD))

        elif op in (57, 58): pass  # FORNLOOP, FORGLOOP

        elif op in (59, 61, 76):  # FORGPREP*
            vs = [fresh('Var') for _ in range(max(1, C))]
            for i, v in enumerate(vs):
                reg_name[A+3+i] = v; reg_expr[A+3+i] = v
            out.emit(f'for {", ".join(vs)} in {kreg(A)}, {kreg(A+1)} do')
            out.indent(); struct_stack.append(('for_gen', pc + 1 + sD))

        elif op == 63:  # GETVARARGS
            declare(A, '...', 'Var')

        elif op == 64:  # DUPCLOSURE A=proto[D]  (D=closure_constant_idx, NOT proto_idx)
            dup_proto_idx = consts[D][1] if 0 <= D < len(consts) and consts[D][0] == 'closure' else None
            if dup_proto_idx is not None:
                _process_closure(proto, instrs, pc, snap(), dup_proto_idx)
            # Resolve the actual proto name via constant table
            func_expr = _fname(all_protos[dup_proto_idx]) if dup_proto_idx is not None and dup_proto_idx < len(all_protos) else f'function{D}'
            _look = pc + 1
            while _look < n and instrs[_look][0] == 70: _look += 1
            _next_op = instrs[_look][0] if _look < n else -1
            _next_A  = instrs[_look][1] if _look < n else -1
            if _next_op == 16 and _next_A == A:
                reg_name[A] = func_expr; reg_expr[A] = func_expr; reg_raw[A] = func_expr
            else:
                # Use declare() so wc/uc propagation rules apply (may suppress local)
                reg_raw[A] = func_expr
                declare(A, func_expr, 'Func')
            _emit_ref_captures(out, proto, instrs, pc, reg_expr)

        elif op == 65: pass  # PREPVARARGS

        elif op == 66:  # LOADKX
            declare(A, kc(aux) if aux is not None else '?', 'Var')

        elif op == 67:  # JUMPX
            if sE >= 0 and struct_stack and struct_stack[-1][0] == 'if':
                kind, close_at = struct_stack.pop(); out.dedent()
                tgt = pc + 1 + sE
                if tgt > close_at:
                    out.emit('else'); out.indent(); struct_stack.append(('else', tgt))
                else:
                    out.emit('end')

        elif op in (60, 68, 73, 74, 75): pass  # FASTCALL*
        elif op == 69: pass  # COVERAGE
        elif op == 70: pass  # CAPTURE — handled by _process_closure / _emit_ref_captures

        elif op == 71: declare(A, f'{kc(C)} - {kreg(B)}', 'Num')
        elif op == 72: declare(A, f'{kc(B)} / {kreg(C)}', 'Num')

        elif op in (77, 78, 79, 80):  # JUMPXEQK*
            ki = (aux & 0xFFFFFF) if aux is not None else 0
            negated = bool((aux >> 31) & 1) if aux is not None else False
            kv = kc(ki)
            inv_cond = f'{kreg(A)} ~= {kv}' if not negated else f'{kreg(A)} == {kv}'
            open_branch(jmp(raw_idx, sD), inv_cond, pc)

        elif op == 81: declare(A, f'{kreg(B)} // {kreg(C)}', 'Num')
        elif op == 82: declare(A, f'{kreg(B)} // {kc(C)}', 'Num')

        else:
            out.emit(f'-- {OPCODES.get(op, f"OP_{op}")} A={A} B={B} C={C} D={D}')

        pc += 1

    while struct_stack:
        kind, _ = struct_stack.pop()
        if kind in ('if', 'else', 'elseif', 'for_num', 'for_gen', 'while'):
            out.dedent(); out.emit('end')

    if not is_main: out.dedent(); out.emit('end')
    return '\n'.join(out.lines())


def _process_closure(proto: Proto, instrs, closure_pc: int,
                     reg_snapshot: Dict[int, str], child_idx: int):
    """
    At runtime (during parent decompile), snapshot val capture expressions.
    The pre-pass already built _cap_info with slot->('val',src_reg)|('ref',up_name).
    Here we resolve val captures: look up reg_snapshot[src_reg] to get the expression.
    Store in _cap_val_exprs[child_idx][slot] = expr for child to use.
    """
    if child_idx not in _cap_info:
        return   # no captures recorded in pre-pass
    for slot, info in _cap_info[child_idx].items():
        if info[0] == 'val':
            src_reg = info[1]
            expr = reg_snapshot.get(src_reg)
            if expr is not None:
                _cap_val_exprs.setdefault(child_idx, {})[slot] = expr


def _emit_ref_captures(out: Emitter, proto: Proto, instrs, closure_pc: int,
                       reg_expr: Dict[int, Optional[str]]):
    """
    For CAPTURE ref entries after NEWCLOSURE/DUPCLOSURE:
    emit 'local up_N = <current value>' in the parent scope
    so the up_N name is in scope for later SETUPVAL/GETUPVAL in the child.
    The child reads up_N directly; we just need it declared in the parent.
    Actually: the parent already has the register as a named variable.
    The up_N IS just an alias. We don't need to emit anything extra in the parent —
    the child will use up_N which maps back to whatever the parent register holds.
    (The child's GETUPVAL/SETUPVAL uses up_N; the parent's register already has a name.)
    """
    pass   # No extra emit needed — up_N is resolved in the child's kupval map


# ── Top-level ──────────────────────────────────────────────────────────────────
def decompile_all(protos: List[Proto], main_id: int) -> str:
    global _up_counter, _cap_info, _cap_val_exprs, _ref_upval_names
    global _utable_counter, _val_table_names
    _up_counter = 0; _cap_info = {}; _cap_val_exprs = {}; _ref_upval_names = {}
    _utable_counter = 0; _val_table_names = {}
    global _main_table_reg_to_utable; _main_table_reg_to_utable = {}

    # Step 1: Pre-pass — find all captures in main proto, assign up_N names
    main_proto = next((p for p in protos if p.idx == main_id), None)
    if main_proto:
        _prepass_captures(main_proto, protos)

    # Step 2: Decompile MAIN proto first so _process_closure runs and populates
    #         _cap_val_exprs for all child protos
    main_text = ''
    if main_proto:
        main_text = decompile_proto(main_proto, protos, is_main=True)

    # Step 3: Decompile non-main protos (now _cap_val_exprs is available)
    non_main_sections = []
    for proto in protos:
        if proto.idx == main_id:
            continue
        non_main_sections.append(('-- ' + '=' * 60, decompile_proto(proto, protos, is_main=False)))

    # Step 4: Assemble output
    lines = ['--[[ Roblox Luau v6 Bytecode Decompiler ]]',
             f'--[[ {len(protos)} protos, main=function{main_id} ]]', '']
    named = [p.debug_name for p in protos if p.debug_name]
    if named:
        lines.append('--[[ named functions: ' + ', '.join(named) + ' ]]')
        lines.append('')

    # Collect all _UTableN names from val_table captures (deduplicated, sorted)
    all_utable_names = []
    seen_ut = set()
    for slot_map in _val_table_names.values():
        for ut_name in slot_map.values():
            if ut_name not in seen_ut:
                seen_ut.add(ut_name)
                all_utable_names.append(ut_name)
    all_utable_names.sort(key=lambda x: int(x.replace('_UTable', '')))

    # Emit top-level declarations: ref upvalues + table val upvalues
    has_top_decls = bool(_ref_upval_names) or bool(all_utable_names)
    if has_top_decls:
        lines.append('-- Shared upvalues (captured by reference / val-table)')
        for src_reg, up_name in sorted(_ref_upval_names.items(), key=lambda x: x[1]):
            lines.append(f'local {up_name}')
        for ut_name in all_utable_names:
            lines.append(f'local {ut_name}')  # initialized in main body after NEWTABLE
        lines.append('')

    # Non-main proto function definitions
    for sep, text in non_main_sections:
        lines.append(sep)
        lines.append(text)

    # Main proto body
    lines.append('-- ' + '=' * 60)
    lines.append(main_text)

    return '\n'.join(lines)


# ── Entry point ────────────────────────────────────────────────────────────────
def main():
    import argparse, os
    ap = argparse.ArgumentParser(prog='luau_decompiler',
        description='Roblox Luau v6 bytecode decompiler (.luac -> .lua)')
    ap.add_argument('input'); ap.add_argument('-o', '--output', default=None)
    ap.add_argument('--stdout', action='store_true')
    args = ap.parse_args()
    if not os.path.isfile(args.input):
        sys.stderr.write(f'Error: file not found: {args.input}\n'); sys.exit(1)
    out_path = args.output or (os.path.splitext(os.path.basename(args.input))[0] + '_decompiled.lua')
    data = open(args.input, 'rb').read()
    parser = Parser(data)
    try:
        parser.run()
        sys.stderr.write(f'Parsed {len(parser.protos)}/{parser.proto_count} protos, main=function{parser.main_id}\n')
    except Exception as e:
        import traceback; sys.stderr.write(f'Parser error: {e}\n'); traceback.print_exc(file=sys.stderr)
    result = decompile_all(parser.protos, parser.main_id)
    open(out_path, 'w').write(result)
    sys.stderr.write(f'Output: {out_path}\n')
    if args.stdout: print(result)

if __name__ == '__main__': main()