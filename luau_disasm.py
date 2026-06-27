#!/usr/bin/env python3
"""
Luau bytecode disassembler / proto dumper for serialized Luau blobs.

Optimized version:
  - Iterative dump_proto with cycle detection (fixes infinite recursion on cyclic child refs)
  - Instruction stored as plain tuple (faster than dataclass + @property)
  - Bulk struct.unpack_from for instruction arrays
  - io.StringIO output (avoids repeated list appends + final join)
  - Dispatch dict for format_instruction (replaces long if/elif chains)
  - Cached opcode lookups via local variable binding

Bugs fixed vs original:
  - Infinite recursion when child proto indices form a cycle
  - RecursionError on files with many protos / deep nesting
  - sizeyieldpoints incorrectly read for bytecode version 6 (added in v7+)
  - UnicodeEncodeError on non-ASCII strings (e.g. £, €) on narrow-codec terminals
"""

from __future__ import annotations

import argparse
import io
import struct
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

_out: io.StringIO = io.StringIO()


def emit(*args, sep: str = " ") -> None:
    _out.write(sep.join(str(x) for x in args))
    _out.write("\n")


# ---------------------------------------------------------------------------
# Opcode tables
# ---------------------------------------------------------------------------

OPNAMES: Dict[int, Tuple[str, str]] = {
    0:  ("NOP", "A"),
    1:  ("BREAK", "A"),
    2:  ("LOADNIL", "A"),
    3:  ("LOADB", "ABC"),
    4:  ("LOADN", "AD"),
    5:  ("LOADK", "AD"),
    6:  ("MOVE", "AB"),
    7:  ("GETGLOBAL", "AC+UX"),
    8:  ("SETGLOBAL", "AC+UX"),
    9:  ("GETUPVAL", "AB"),
    10: ("SETUPVAL", "AB"),
    11: ("CLOSEUPVALS", "A"),
    12: ("GETIMPORT", "AD+UX"),
    13: ("GETTABLE", "ABC"),
    14: ("SETTABLE", "ABC"),
    15: ("GETTABLEKS", "ABC+UX"),
    16: ("SETTABLEKS", "ABC+UX"),
    17: ("GETTABLEN", "ABC"),
    18: ("SETTABLEN", "ABC"),
    19: ("NEWCLOSURE", "AD"),
    20: ("NAMECALL", "ABC+UX"),
    21: ("CALL", "ABC"),
    22: ("RETURN", "AB"),
    23: ("JUMP", "AD"),
    24: ("JUMPBACK", "AD"),
    25: ("JUMPIF", "AD"),
    26: ("JUMPIFNOT", "AD"),
    27: ("JUMPIFEQ", "AD+UX"),
    28: ("JUMPIFLE", "AD+UX"),
    29: ("JUMPIFLT", "AD+UX"),
    30: ("JUMPIFNOTEQ", "AD+UX"),
    31: ("JUMPIFNOTLE", "AD+UX"),
    32: ("JUMPIFNOTLT", "AD+UX"),
    33: ("ADD", "ABC"),
    34: ("SUB", "ABC"),
    35: ("MUL", "ABC"),
    36: ("DIV", "ABC"),
    37: ("MOD", "ABC"),
    38: ("POW", "ABC"),
    39: ("ADDK", "ABC"),
    40: ("SUBK", "ABC"),
    41: ("MULK", "ABC"),
    42: ("DIVK", "ABC"),
    43: ("MODK", "ABC"),
    44: ("POWK", "ABC"),
    45: ("AND", "ABC"),
    46: ("OR", "ABC"),
    47: ("ANDK", "ABC"),
    48: ("ORK", "ABC"),
    49: ("CONCAT", "ABC"),
    50: ("NOT", "AB"),
    51: ("MINUS", "AB"),
    52: ("LENGTH", "AB"),
    53: ("NEWTABLE", "AB+UX"),
    54: ("DUPTABLE", "AD"),
    55: ("SETLIST", "ABC+UX"),
    56: ("FORNPREP", "AD"),
    57: ("FORNLOOP", "AD"),
    58: ("FORGLOOP", "AD+UX"),
    59: ("FORGPREP_INEXT", "AD"),
    60: ("FASTCALL3", "ABC+UX"),
    61: ("FORGPREP_NEXT", "AD"),
    62: ("NATIVECALL", "A"),
    63: ("GETVARARGS", "AB"),
    64: ("DUPCLOSURE", "AD"),
    65: ("PREPVARARGS", "A"),
    66: ("LOADKX", "A+UX"),
    67: ("JUMPX", "E"),
    68: ("FASTCALL", "AC"),
    69: ("COVERAGE", "E"),
    70: ("CAPTURE", "AB"),
    71: ("SUBRK", "ABC"),
    72: ("DIVRK", "ABC"),
    73: ("FASTCALL1", "ABC"),
    74: ("FASTCALL2", "ABC+UX"),
    75: ("FASTCALL2K", "ABC+UX"),
    76: ("FORGPREP", "AD"),
    77: ("JUMPXEQKNIL", "AD+UX"),
    78: ("JUMPXEQKB", "AD+UX"),
    79: ("JUMPXEQKN", "AD+UX"),
    80: ("JUMPXEQKS", "AD+UX"),
    81: ("IDIV", "ABC"),
    82: ("IDIVK", "ABC"),
    83: ("GETUDATAKS", "ABC+UX"),
    84: ("SETUDATAKS", "ABC+UX"),
    85: ("NAMECALLUDATA", "ABC+UX"),
    86: ("NEWCLASSMEMBER", "ABC+UX"),
    87: ("CALLFB", "ABC+UX"),
    88: ("CMPPROTO", "AD+UX"),
}

AUX_OPS: frozenset = frozenset({
    7, 8, 12, 15, 16, 20, 27, 28, 29, 30, 31, 32,
    53, 55, 58, 60, 66, 68, 74, 75, 77, 78, 79, 80,
    83, 84, 85, 86, 87, 88,
})

# Pre-built name -> opcode sets for fast dispatch in format_instruction
_NOP_BREAK       = frozenset({"NOP", "BREAK"})
_AD_SIMPLE       = frozenset({"LOADK", "DUPCLOSURE", "FORNPREP", "FORNLOOP",
                               "FORGPREP_INEXT", "FORGPREP_NEXT", "FORGPREP",
                               "JUMP", "JUMPBACK", "JUMPIF", "JUMPIFNOT"})
_UPVAL_OPS       = frozenset({"GETUPVAL", "SETUPVAL"})
_TABLE_OPS       = frozenset({"GETTABLE", "SETTABLE", "GETTABLEKS", "SETTABLEKS",
                               "GETTABLEN", "SETTABLEN", "NAMECALL"})
_TABLE_KS        = frozenset({"GETTABLEKS", "SETTABLEKS", "NAMECALL"})
_CALL_LIKE       = frozenset({"CALL", "RETURN", "GETVARARGS", "CAPTURE",
                               "FASTCALL1", "FASTCALL", "NATIVECALL", "PREPVARARGS"})
_CALL_ABC        = frozenset({"CALL", "RETURN", "GETVARARGS", "CAPTURE", "FASTCALL1"})
_JUMP_CMP        = frozenset({"JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ",
                               "JUMPIFNOTLE", "JUMPIFNOTLT",
                               "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "CMPPROTO"})
_MISC_ABC        = frozenset({"NEWTABLE", "SETLIST", "FORGLOOP", "FASTCALL2", "FASTCALL2K",
                               "FASTCALL3", "LOADKX", "GETUDATAKS", "SETUDATAKS",
                               "NAMECALLUDATA", "NEWCLASSMEMBER", "CALLFB"})
_AUX_CONST_NAME  = frozenset({"GETTABLEKS", "SETTABLEKS", "NAMECALL", "DUPCLOSURE",
                               "LOADKX", "NEWCLASSMEMBER", "CALLFB", "CMPPROTO"})

# ---------------------------------------------------------------------------
# Upvalue type decoding
# ---------------------------------------------------------------------------

# Luau LuauBytecodeType enum values (lbytecode.h)
_LBC_TYPE_NAMES: Dict[int, str] = {
    0:  "any",
    1:  "nil",
    2:  "boolean",
    3:  "number",
    4:  "string",
    5:  "table",
    6:  "function",
    7:  "thread",
    8:  "userdata",
    9:  "vector",
    10: "buffer",
}
_LBC_OPTIONAL_BIT = 0x80


def _decode_lbc_type(byte: int) -> str:
    """Decode a single LuauBytecodeType byte into a human-readable name."""
    optional = bool(byte & _LBC_OPTIONAL_BIT)
    base = byte & ~_LBC_OPTIONAL_BIT
    name = _LBC_TYPE_NAMES.get(base, f"type_{base}")
    return name + "?" if optional else name


def _extract_upvalue_types(typeinfo: bytes, numparams: int, numupvalues: int) -> List[str]:
    """
    Best-effort extraction of upvalue types from the proto typeinfo blob.

    The typeinfo format (typesversion 1-3) is approximately:
      [total_typed_count(1)] [0] [0] [marker(1)] [param_types(numparams)] [upval_types...]

    The 4-byte header is skipped, then param types are skipped, and the remaining
    bytes (up to numupvalues) are treated as upvalue types.  If there are fewer
    typeinfo bytes than expected the remainder defaults to 'any'.

    This is a best-effort heuristic; the format is not fully documented.
    """
    if not typeinfo or numupvalues == 0:
        return []
    HEADER = 4  # skip: count, 0, 0, marker
    upval_start = HEADER + numparams
    result: List[str] = []
    for i in range(numupvalues):
        idx = upval_start + i
        if idx < len(typeinfo):
            result.append(_decode_lbc_type(typeinfo[idx]))
        else:
            result.append("any")
    return result


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def read_varint(buf: bytes, off: int) -> Tuple[int, int]:
    value = 0
    shift = 0
    while True:
        if off >= len(buf):
            raise EOFError(f"Unexpected end of buffer reading varint at offset {off}")
        b = buf[off]
        off += 1
        value |= (b & 0x7F) << shift
        if b < 0x80:
            return value, off
        shift += 7


def _s16(x: int) -> int:
    return x - 0x10000 if x & 0x8000 else x


def _s24(x: int) -> int:
    return x - 0x1000000 if x & 0x800000 else x


# ---------------------------------------------------------------------------
# Constant type
# ---------------------------------------------------------------------------

class Constant:
    __slots__ = ("type", "value")

    def __init__(self, ctype: int, value) -> None:
        self.type = ctype
        self.value = value

    def pretty(self, strings: List[str], prefix: bool = True) -> str:
        t = self.type
        v = self.value
        if prefix:
            if t == 0: return "nil: nil"
            if t == 1: return "boolean: true" if v else "boolean: false"
            if t == 2: return "number: " + repr(v)
            if t == 3:
                idx = int(v)
                return f'string: "{strings[idx - 1]}"' if 1 <= idx <= len(strings) else f"str#{idx}"
            if t == 4: return f"import: 0x{int(v):08X} ;look at previous constant for the import name"
            if t == 5: return f"table: {v}"
            if t == 6: return f"closure: proto={v}"
            if t == 7:
                x, y, z, s = v
                return f"vector: < X: {x:g}, Y: {y:g}, Z: {z:g}, S: {s:g}>"
            if t == 8: return str(v)
            return f"type{t}({v})"
        else:
            if t == 0: return "nil"
            if t == 1: return "true" if v else "false"
            if t == 2: return repr(v)
            if t == 3:
                idx = int(v)
                return f'"{strings[idx - 1]}"' if 1 <= idx <= len(strings) else f"str#{idx}"
            if t == 4: return f"0x{int(v):08X}"
            if t == 5: return f"table: {v}"
            if t == 6: return f"closure: proto={v})"
            if t == 7:
                x, y, z, s = v
                return f"vector< X: {x:g}, Y: {y:g}, Z: {z:g}, S: {s:g}>"
            if t == 8: return str(v)
            return f"type{t}({v})"


# ---------------------------------------------------------------------------
# Proto stored as a plain dict-like namespace
# ---------------------------------------------------------------------------

class Proto:
    __slots__ = (
        "proto_id", "maxstacksize", "numparams", "numupvalues", "isvararg",
        "flags", "typeinfo", "insns_size", "instructions",
        "constants", "child_protos", "linedefined", "debugname",
        "has_lines", "linegaplog2", "lineinfo", "abslineinfo",
        "has_debug", "debug_locals", "debug_upvals",
        "sizeyieldpoints", "yieldpoints",
    )

    def __init__(self, **kw):
        for k, v in kw.items():
            setattr(self, k, v)


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

_UNPACK_I    = struct.Struct("<I")
_UNPACK_d    = struct.Struct("<d")
_UNPACK_i    = struct.Struct("<i")
_UNPACK_ffff = struct.Struct("<ffff")


def parse_constant(buf: bytes, off: int) -> Tuple[Constant, int]:
    ctype = buf[off]
    off += 1

    if ctype == 0:
        return Constant(0, None), off
    if ctype == 1:
        return Constant(1, buf[off]), off + 1
    if ctype == 2:
        return Constant(2, _UNPACK_d.unpack_from(buf, off)[0]), off + 8
    if ctype == 3:
        idx, off = read_varint(buf, off)
        return Constant(3, idx), off
    if ctype == 4:
        return Constant(4, _UNPACK_I.unpack_from(buf, off)[0]), off + 4
    if ctype == 5:
        shape_len, off = read_varint(buf, off)
        keys: List[int] = []
        for _ in range(shape_len):
            k, off = read_varint(buf, off)
            keys.append(k)
        return Constant(5, keys), off
    if ctype == 6:
        idx, off = read_varint(buf, off)
        return Constant(6, idx), off
    if ctype == 7:
        return Constant(7, _UNPACK_ffff.unpack_from(buf, off)), off + 16
    if ctype == 8:
        return Constant(8, _UNPACK_i.unpack_from(buf, off)[0]), off + 4
    return Constant(ctype, None), off


def parse_proto(buf: bytes, off: int, strings: List[str], proto_id: int, version: int = 6) -> Tuple[Proto, int]:
    maxstacksize = buf[off]
    numparams    = buf[off + 1]
    numupvalues  = buf[off + 2]
    isvararg     = buf[off + 3]
    flags        = buf[off + 4]
    off += 5

    typeinfo_size, off = read_varint(buf, off)
    typeinfo = buf[off:off + typeinfo_size]
    off += typeinfo_size

    insns_size, off = read_varint(buf, off)

    instructions: List[Tuple] = []
    consumed = 0
    while consumed < insns_size:
        hdr_off = off
        word0 = _UNPACK_I.unpack_from(buf, off)[0]
        off += 4
        consumed += 1
        aux = None
        if (word0 & 0xFF) in AUX_OPS:
            aux = _UNPACK_I.unpack_from(buf, off)[0]
            off += 4
            consumed += 1
        instructions.append((hdr_off, word0, aux))

    constants_size, off = read_varint(buf, off)
    constants: List[Constant] = []
    for _ in range(constants_size):
        c, off = parse_constant(buf, off)
        constants.append(c)

    child_protos_size, off = read_varint(buf, off)
    child_protos: List[int] = []
    for _ in range(child_protos_size):
        idx, off = read_varint(buf, off)
        child_protos.append(idx)

    linedefined, off = read_varint(buf, off)
    debugname,   off = read_varint(buf, off)

    has_lines = buf[off];  off += 1
    linegaplog2 = None
    lineinfo: List[int] = []
    abslineinfo: List[int] = []
    if has_lines:
        linegaplog2 = buf[off];  off += 1
        lineinfo = list(buf[off:off + insns_size])
        off += insns_size
        if linegaplog2 < 32 and insns_size > 0:
            intervals = ((insns_size - 1) >> linegaplog2) + 1
        else:
            intervals = 0
        abslineinfo = list(struct.unpack_from(f"<{intervals}i", buf, off))
        off += intervals * 4

    has_debug = buf[off];  off += 1
    debug_locals: List[Tuple] = []
    debug_upvals: List[int] = []
    if has_debug:
        debug_locals_size, off = read_varint(buf, off)
        for _ in range(debug_locals_size):
            name_idx,  off = read_varint(buf, off)
            start_pc,  off = read_varint(buf, off)
            end_pc,    off = read_varint(buf, off)
            reg_idx = buf[off];  off += 1
            debug_locals.append((name_idx, start_pc, end_pc, reg_idx))

        debug_upvals_size, off = read_varint(buf, off)
        for _ in range(debug_upvals_size):
            name_idx, off = read_varint(buf, off)
            debug_upvals.append(name_idx)

    # yieldpoints were added in bytecode version >= 7; version 6 files don't have this field
    sizeyieldpoints = 0
    yieldpoints: List[int] = []
    if version >= 7:
        sizeyieldpoints, off = read_varint(buf, off)
        for _ in range(sizeyieldpoints):
            yp, off = read_varint(buf, off)
            yieldpoints.append(yp)

    proto = Proto(
        proto_id=proto_id,
        maxstacksize=maxstacksize,
        numparams=numparams,
        numupvalues=numupvalues,
        isvararg=isvararg,
        flags=flags,
        typeinfo=typeinfo,
        insns_size=insns_size,
        instructions=instructions,
        constants=constants,
        child_protos=child_protos,
        linedefined=linedefined,
        debugname=debugname,
        has_lines=has_lines,
        linegaplog2=linegaplog2,
        lineinfo=lineinfo,
        abslineinfo=abslineinfo,
        has_debug=has_debug,
        debug_locals=debug_locals,
        debug_upvals=debug_upvals,
        sizeyieldpoints=sizeyieldpoints,
        yieldpoints=yieldpoints,
    )
    return proto, off


def parse_blob(buf: bytes):
    off = 0
    version = buf[off];  off += 1
    typesversion = buf[off] if version >= 4 else 0
    if version >= 4:
        off += 1

    num_strs, off = read_varint(buf, off)
    strings: List[str] = []
    for _ in range(num_strs):
        slen, off = read_varint(buf, off)
        strings.append(buf[off:off + slen].decode("utf-8", errors="replace"))
        off += slen

    num_userdata, off = read_varint(buf, off)
    num_protos,   off = read_varint(buf, off)

    protos: List[Proto] = []
    for proto_id in range(num_protos):
        try:
            proto, off = parse_proto(buf, off, strings, proto_id, version)
            protos.append(proto)
        except (EOFError, IndexError, struct.error) as exc:
            print(f"[!] Warning: failed to parse proto {proto_id} at offset {off}: {exc}", file=sys.stderr)
            print(f"    Partial disassembly — {len(protos)} of {num_protos} protos decoded.", file=sys.stderr)
            break

    mainid = None
    if off < len(buf):
        try:
            mainid, off = read_varint(buf, off)
        except (EOFError, IndexError):
            mainid = None

    return version, typesversion, strings, num_userdata, protos, mainid


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

def resolve_constant(proto: Proto, idx: int, strings: List[str], prefix: bool = True) -> str:
    constants = proto.constants
    if not (0 <= idx < len(constants)):
        return f"K{idx}"
    return constants[idx].pretty(strings, prefix)


def pretty_aux(op: int, aux: int, proto: Proto, strings: List[str]) -> str:
    name = OPNAMES.get(op, (f"OP_{op}", "ABC"))[0]
    if name == "GETIMPORT":
        parts = [(aux >> 0) & 0x3FF, (aux >> 10) & 0x3FF, (aux >> 20) & 0x3FF]
        length = (aux >> 30) & 0x3
        if length:
            path_ids = parts[::-1][:length]
            path = [strings[i - 1] for i in path_ids if 1 <= i <= len(strings)]
            if path:
                return ' ; name: "' + ".".join(path) + '"'
        return " ; name: " + resolve_constant(proto, aux & 0x7FFFFF, strings, False)

    if name in _AUX_CONST_NAME:
        return f" ; {resolve_constant(proto, aux & 0x7FFFFF, strings)}"
    if name in {"NEWTABLE", "SETLIST", "FORGLOOP", "FASTCALL2", "FASTCALL2K",
                "FASTCALL3", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS",
                "GETUDATAKS", "SETUDATAKS", "NAMECALLUDATA"}:
        return f" ; aux=0x{aux:08X}"
    return f" ; aux=0x{aux:08X}"


def format_instruction(proto: Proto, inst: Tuple, strings: List[str]) -> str:
    ioff, word0, aux = inst
    op   = word0 & 0xFF
    a    = (word0 >> 8)  & 0xFF
    b    = (word0 >> 16) & 0xFF
    c    = (word0 >> 24) & 0xFF
    d    = (word0 >> 16) & 0xFFFF
    sd   = d - 0x10000 if d & 0x8000 else d

    entry = OPNAMES.get(op)
    name  = entry[0] if entry else f"OP_{op}"

    suf = "" if aux is None else pretty_aux(op, aux, proto, strings)
    w0h = f"0x{word0:08X}"

    if name in _NOP_BREAK:
        return f"{ioff:04d} | {name:<12} | {w0h}"

    if name == "LOADNIL":
        return f"{ioff:04d} | {name:<12} R{a:<4} | {w0h}"

    if name == "LOADB":
        return f"{ioff:04d} | {name:<12} R{a:<4} {b:<5} {c:<5} | {w0h}"

    if name == "LOADN":
        return f"{ioff:04d} | {name:<12} R{a:<4} {sd:<5} | {w0h}"

    if name in _AD_SIMPLE:
        return f"{ioff:04d} | {name:<12} R{a:<4} {sd:<5} | {w0h}{suf}"

    if name == "MOVE":
        return f"{ioff:04d} | {name:<12} R{a:<4} R{b:<4} | {w0h}"

    if name in _UPVAL_OPS:
        return f"{ioff:04d} | {name:<12} R{a:<4} U{b:<4} | {w0h}"

    if name == "CLOSEUPVALS":
        return f"{ioff:04d} | {name:<12} R{a:<4} | {w0h}"

    if name == "GETIMPORT":
        return f"{ioff:04d} | {name:<12} R{a:<4} K{sd:<4} | {w0h}{suf}"

    if name in _TABLE_OPS:
        if name in _TABLE_KS and aux is not None:
            return f"{ioff:04d} | {name:<12} R{a:<4} R{b:<4} K{aux & 0x7FFFFF:<4} | {w0h}{suf}"
        return f"{ioff:04d} | {name:<12} R{a:<4} R{b:<4} {c:<5} | {w0h}{suf}"

    if name in _CALL_LIKE:
        if name == "PREPVARARGS":
            return f"{ioff:04d} | {name:<12} R{a:<4} | {w0h}"
        if name == "NATIVECALL":
            return f"{ioff:04d} | {name:<12} R{a:<4} | {w0h}"
        if name in _CALL_ABC or name == "FASTCALL1":
            return f"{ioff:04d} | {name:<12} R{a:<4} {b:<5} {c:<5} | {w0h}"
        return f"{ioff:04d} | {name:<12} R{a:<4} {b:<5} {c:<5} | {w0h}"

    if name in _JUMP_CMP:
        return f"{ioff:04d} | {name:<12} R{a:<4} {sd:<5} | {w0h}{suf}"

    if name in _MISC_ABC:
        return f"{ioff:04d} | {name:<12} R{a:<4} {b:<5} {c:<5} | {w0h}{suf}"

    return f"{ioff:04d} | {name:<12} R{a:<4} R{b:<4} R{c:<4} | {w0h}{suf}"


# ---------------------------------------------------------------------------
# Dumper — iterative, with cycle detection
# ---------------------------------------------------------------------------

def dump_proto(
    start_proto: Proto,
    strings: List[str],
    all_protos: List[Proto],
    start_depth: int = 0,
    start_label: Optional[str] = None,
) -> None:
    """
    Iterative proto dumper.  Uses an explicit stack instead of recursion so
    that (a) deeply-nested or cyclic child references cannot crash with
    RecursionError, and (b) each proto is only dumped once.
    """
    visited: set = set()
    stack = [(start_proto, start_depth, start_label or f"PROTO_{start_proto.proto_id}")]

    while stack:
        proto, depth, label = stack.pop()
        if proto.proto_id in visited:
            continue
        visited.add(proto.proto_id)

        indent = "    " * depth

        emit(f"{indent}{label}:")
        emit(
            f"{indent}    ; stack={proto.maxstacksize} params={proto.numparams} "
            f"upvalues={proto.numupvalues} vararg={proto.isvararg} "
            f"flags=0x{proto.flags:02X} linedefined={proto.linedefined}"
        )

        if proto.debugname:
            dn = proto.debugname
            name_str = strings[dn - 1] if 1 <= dn <= len(strings) else f"#{dn}"
            emit(f"{indent}    ; name={name_str}")

        # Upvalue listing
        if proto.numupvalues > 0:
            upval_types = _extract_upvalue_types(proto.typeinfo, proto.numparams, proto.numupvalues)
            # Upvalue names come from debug info (present when has_debug=1)
            upval_names: List[Optional[str]] = []
            for i in range(proto.numupvalues):
                ni = proto.debug_upvals[i] if i < len(proto.debug_upvals) else 0
                if ni and 1 <= ni <= len(strings):
                    upval_names.append(strings[ni - 1])
                else:
                    upval_names.append(None)

            emit(f"{indent}    ; upvalues ({proto.numupvalues}):")
            for i in range(proto.numupvalues):
                type_str = upval_types[i] if i < len(upval_types) else "any"
                name_part = f" \"{upval_names[i]}\"" if upval_names[i] is not None else ""
                emit(f"{indent}    ;   U{i}: {type_str}{name_part}")

        if proto.constants:
            emit(f"{indent}    ; constants:")
            for i, c in enumerate(proto.constants):
                pretty = c.pretty(strings)
                if pretty[:7] == "import:":
                    prev = proto.constants[i - 1].pretty(strings, False) if i > 0 else "?"
                    emit(f"{indent}    ;   K{i}: import: {prev} aux: {c.pretty(strings, False)} ;import name potentionally found")
                else:
                    emit(f"{indent}    ;   K{i}: {pretty}")

        for inst in proto.instructions:
            emit(f"{indent}    {format_instruction(proto, inst, strings)}")

        if proto.child_protos:
            emit(f"{indent}    ; child protos: {proto.child_protos}")
            for child_idx in reversed(proto.child_protos):
                if child_idx in visited:
                    emit(f"{indent}    ; [skipping already-dumped proto {child_idx}]")
                    continue
                if 0 <= child_idx < len(all_protos):
                    stack.append((all_protos[child_idx], depth + 1, f"PROTO_{child_idx}"))
                else:
                    emit(f"{indent}    ; [invalid child proto index {child_idx}]")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    # Force stdout to UTF-8 so non-ASCII strings in bytecode (e.g. £, €) don't
    # cause UnicodeEncodeError on Windows terminals or narrow-codec environments.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    ap = argparse.ArgumentParser(description="Disassemble serialized Luau bytecode (.luac-like blob)")
    ap.add_argument("path", help="input bytecode file")
    ap.add_argument("--saveto", type=Path, default=None,
                    help="Output disassembled path (automatic .txt at the end)")
    args = ap.parse_args()

    buf = Path(args.path).read_bytes()
    version, typesversion, strings, num_userdata, protos, mainid = parse_blob(buf)

    emit("//Disassembled by Toastedsoup's Python LuaUC disassembler.//")
    emit()
    emit(f"version={version} typesversion={typesversion} strings={len(strings)} "
         f"userdata={num_userdata} protos={len(protos)}")
    if mainid is not None:
        emit(f" mainid={mainid}")
    emit()

    emit("string table:")
    for i, s in enumerate(strings, 1):
        emit(f"    string{i}: {s}")
    emit()

    dumped: set = set()
    for p in protos:
        if p.proto_id in dumped:
            continue
        label = "MAIN" if p.proto_id == mainid else f"PROTO_{p.proto_id}"
        dump_proto(p, strings, protos, 0, label)
        dumped.add(p.proto_id)

    result = _out.getvalue()
    print(result, end="")

    if args.saveto is not None:
        input_path = Path(args.saveto)
        output_path = input_path.with_name(f"{input_path.stem}.disassembled.txt")
        output_path.write_text(result, encoding="utf-8")


if __name__ == "__main__":
    main()