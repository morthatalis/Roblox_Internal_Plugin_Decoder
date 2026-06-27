#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import dataclasses
import json
import struct
import sys
import subprocess
import time
import os
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


# Optional compression backends
try:
    import zstandard as zstd
except Exception:
    zstd = None

try:
    import lz4.block
except Exception:
    lz4 = None
else:
    import lz4


# add near the top
UNKNOWN_RAW_TYPES = {0x21}
should_decomp = False


def decode_prop_values(type_id: int, count: int, r: Reader) -> Tuple[str, List[Any]]:
    if type_id == 0x01:
        return "string", parse_string_array(r, count)
    if type_id == 0x02:
        return "bool", parse_bool_array(r, count)
    if type_id == 0x03:
        return "int", parse_int32_array(r, count)
    if type_id == 0x12:
        return "token", parse_uint32_array(r, count)
    if type_id == 0x13:
        return "ref", parse_referent_array(r, count)
    if type_id == 0x1B:
        return "int64", parse_int64_array(r, count)
    if type_id == 0x1C:
        return "sharedstring", parse_sharedstring_array(r, count)
    if type_id == 0x1D:
        return "bytecode", parse_bytecode_array(r, count)

    # Newer/undocumented types: preserve the raw payload instead of failing.
    if type_id in UNKNOWN_RAW_TYPES:
        raw = r.read(len(r.data) - r.tell())
        return "raw", [raw] * count

    raise NotImplementedError(f"Unsupported property type ID 0x{type_id:02X}")

# -----------------------------
# Low-level helpers
# -----------------------------

def zigzag_decode32(n: int) -> int:
    return (n >> 1) ^ -(n & 1)


def zigzag_decode64(n: int) -> int:
    return (n >> 1) ^ -(n & 1)


def deinterleave(data: bytes, width: int) -> bytes:
    if len(data) % width != 0:
        raise ValueError(f"Data length {len(data)} not divisible by width {width}")
    n = len(data) // width
    out = bytearray(len(data))
    for i in range(n):
        for b in range(width):
            out[i * width + b] = data[b * n + i]
    return bytes(out)


def escape_xml(text: str) -> str:
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&apos;")
    )


def cdata(text: str) -> str:
    # Safe even if text contains "]]>"
    return "<![CDATA[" + text.replace("]]>", "]]]]><![CDATA[>") + "]]>"


def slugify(text: str) -> str:
    out = []
    for ch in text:
        if ch.isalnum() or ch in ("-", "_", "."):
            out.append(ch)
        else:
            out.append("_")
    s = "".join(out).strip("._")
    return s or "unnamed"


class Reader:
    def __init__(self, data: bytes):
        self.data = data
        self.off = 0

    def tell(self) -> int:
        return self.off

    def seek(self, off: int) -> None:
        self.off = off

    def read(self, n: int) -> bytes:
        if self.off + n > len(self.data):
            raise EOFError(f"Need {n} bytes at 0x{self.off:X}, file ends at 0x{len(self.data):X}")
        b = self.data[self.off : self.off + n]
        self.off += n
        return b

    def u8(self) -> int:
        return self.read(1)[0]

    def u32(self) -> int:
        return struct.unpack_from("<I", self.read(4))[0]

    def i32(self) -> int:
        return struct.unpack_from("<i", self.read(4))[0]

    def i64(self) -> int:
        return struct.unpack_from("<q", self.read(8))[0]

    def f32(self) -> float:
        return struct.unpack_from("<f", self.read(4))[0]

    def f64(self) -> float:
        return struct.unpack_from("<d", self.read(8))[0]

    def rbx_string(self) -> bytes:
        n = self.u32()
        return self.read(n)


# -----------------------------
# Model structures
# -----------------------------

@dataclasses.dataclass
class PropertyValue:
    name: str
    kind: str
    value: Any


@dataclasses.dataclass
class Instance:
    class_id: int
    class_name: str
    referent: int
    is_service: bool = False
    properties: List[PropertyValue] = dataclasses.field(default_factory=list)
    parent: Optional[int] = None
    children: List[int] = dataclasses.field(default_factory=list)


@dataclasses.dataclass
class Model:
    header: Dict[str, Any]
    meta: Dict[str, str]
    shared_strings: List[Tuple[bytes, bytes]]  # (md5/raw 16 bytes, value bytes)
    instances_by_referent: Dict[int, Instance]
    instances_by_class_id: Dict[int, List[Instance]]
    roots: List[int]
    raw_chunks: List[Dict[str, Any]]


# -----------------------------
# Chunk decompression
# -----------------------------

def decompress_chunk(body: bytes, compressed_len: int, uncompressed_len: int) -> bytes:
    if compressed_len == 0:
        return body

    # ZSTD chunks start with 28 b5 2f fd according to the binary format docs.
    # Otherwise, Roblox uses LZ4.
    if body[:4] == b"\x28\xb5\x2f\xfd":
        if zstd is None:
            raise RuntimeError(
                "This file uses ZSTD-compressed chunks. Install it with:\n"
                "  py -m pip install zstandard"
            )
        dctx = zstd.ZstdDecompressor()
        return dctx.decompress(body, max_output_size=uncompressed_len)

    if lz4 is None:
        raise RuntimeError(
            "This file uses LZ4-compressed chunks. Install it with:\n"
            "  py -m pip install lz4"
        )

    # Roblox binary chunks do not use an LZ4 frame; they store a raw block.
    try:
        return lz4.block.decompress(body, uncompressed_size=uncompressed_len)
    except Exception:
        # Some files are more forgiving if the size hint is omitted.
        return lz4.block.decompress(body)


# -----------------------------
# Parsing primitive arrays
# -----------------------------

def parse_string_array(r: Reader, count: int) -> List[str]:
    out = []
    for _ in range(count):
        raw = r.rbx_string()
        out.append(raw.decode("utf-8", errors="replace"))
    return out


def parse_bool_array(r: Reader, count: int) -> List[bool]:
    return [bool(r.u8()) for _ in range(count)]


def parse_int32_array(r: Reader, count: int) -> List[int]:
    raw = deinterleave(r.read(4 * count), 4) if count else b""
    out = []
    for i in range(count):
        u = struct.unpack_from(">I", raw, i * 4)[0]
        out.append(zigzag_decode32(u))
    return out


def parse_uint32_array(r: Reader, count: int) -> List[int]:
    raw = deinterleave(r.read(4 * count), 4) if count else b""
    out = []
    for i in range(count):
        out.append(struct.unpack_from(">I", raw, i * 4)[0])
    return out


def parse_int64_array(r: Reader, count: int) -> List[int]:
    raw = deinterleave(r.read(8 * count), 8) if count else b""
    out = []
    for i in range(count):
        u = struct.unpack_from(">Q", raw, i * 8)[0]
        out.append(zigzag_decode64(u))
    return out


def parse_referent_array(r: Reader, count: int) -> List[Optional[int]]:
    deltas = parse_int32_array(r, count)
    out: List[Optional[int]] = []
    acc = 0
    for d in deltas:
        acc += d
        out.append(None if acc == -1 else acc)
    return out


def parse_bytecode_array(r: Reader, count: int) -> List[bytes]:
    out = []
    for _ in range(count):
        out.append(r.rbx_string())
    return out


def parse_sharedstring_array(r: Reader, count: int) -> List[int]:
    return parse_uint32_array(r, count)


# -----------------------------
# Property value decoding
# -----------------------------

def decode_prop_values(type_id: int, count: int, r: Reader) -> Tuple[str, List[Any]]:
    """
    Returns (kind_name, values).

    Supported kinds:
      string, bool, int, token, ref, int64, sharedstring, bytecode
    """
    if type_id == 0x01:  # String
        return "string", parse_string_array(r, count)

    if type_id == 0x02:  # Bool
        return "bool", parse_bool_array(r, count)

    if type_id == 0x03:  # Int32
        return "int", parse_int32_array(r, count)

    if type_id == 0x12:  # Enum / Token
        return "token", parse_uint32_array(r, count)

    if type_id == 0x13:  # Referent
        return "ref", parse_referent_array(r, count)

    if type_id == 0x1B:  # Int64
        return "int64", parse_int64_array(r, count)

    if type_id == 0x1C:  # SharedString
        return "sharedstring", parse_sharedstring_array(r, count)

    if type_id == 0x1D:  # Bytecode
        return "bytecode", parse_bytecode_array(r, count)

    # This parser intentionally stays "alright" rather than pretending to be exhaustive.
    raise NotImplementedError(f"Unsupported property type ID 0x{type_id:02X}")


# -----------------------------
# Chunk parsing
# -----------------------------

def parse_meta_chunk(payload: bytes) -> Dict[str, str]:
    r = Reader(payload)
    n = r.u32()
    meta = {}
    for _ in range(n):
        key = r.rbx_string().decode("utf-8", errors="replace")
        value = r.rbx_string().decode("utf-8", errors="replace")
        meta[key] = value
    return meta


def parse_sstr_chunk(payload: bytes) -> List[Tuple[bytes, bytes]]:
    r = Reader(payload)
    version = r.u32()
    if version != 0:
        raise ValueError(f"SSTR version {version} is not supported")
    n = r.u32()
    out = []
    for _ in range(n):
        md5 = r.read(16)
        value = r.rbx_string()
        out.append((md5, value))
    return out


def parse_inst_chunk(payload: bytes) -> Tuple[int, str, bool, List[int], List[bool]]:
    r = Reader(payload)
    class_id = r.u32()
    class_name = r.rbx_string().decode("utf-8", errors="replace")
    object_format = r.u8()
    is_service = bool(object_format)
    count = r.u32()
    referents = parse_referent_array(r, count)
    service_markers = parse_bool_array(r, count) if is_service else []
    # Referents in INST chunks are expected to be non-null.
    cleaned_refs = [ref if ref is not None else -1 for ref in referents]
    return class_id, class_name, is_service, cleaned_refs, service_markers


def parse_prnt_chunk(payload: bytes) -> Tuple[List[int], List[Optional[int]]]:
    r = Reader(payload)
    version = r.u8()
    if version != 0:
        raise ValueError(f"PRNT version {version} is not supported")
    count = r.u32()
    children = parse_referent_array(r, count)
    parents = parse_referent_array(r, count)
    cleaned_children = [c if c is not None else -1 for c in children]
    return cleaned_children, parents


def parse_rbxm(path: Path) -> Model:
    data = path.read_bytes()
    r = Reader(data)

    header_magic = r.read(8)
    if header_magic != b"<roblox!":
        raise ValueError("Not a binary Roblox model file")

    signature = r.read(6)
    version = struct.unpack("<H", r.read(2))[0]
    class_count = r.i32()
    instance_count = r.i32()
    reserved = r.read(8)

    header = {
        "magic": header_magic.decode("ascii", errors="replace"),
        "signature": signature.hex(" "),
        "version": version,
        "class_count": class_count,
        "instance_count": instance_count,
        "reserved": reserved.hex(" "),
    }

    meta: Dict[str, str] = {}
    shared_strings: List[Tuple[bytes, bytes]] = []
    instances_by_class_id: Dict[int, List[Instance]] = {}
    instances_by_referent: Dict[int, Instance] = {}
    raw_chunks: List[Dict[str, Any]] = []
    prnt_children: List[int] = []
    prnt_parents: List[Optional[int]] = []

    while r.tell() < len(data):
        if len(data) - r.tell() < 16:
            break

        chunk_name_raw = r.read(4)
        chunk_name = chunk_name_raw.rstrip(b"\x00").decode("ascii", errors="replace")
        compressed_len = r.u32()
        uncompressed_len = r.u32()
        chunk_reserved = r.read(4)

        body = r.read(compressed_len) if compressed_len else r.read(uncompressed_len)
        decoded = decompress_chunk(body, compressed_len, uncompressed_len)

        raw_chunks.append(
            {
                "type": chunk_name,
                "compressed_size": compressed_len,
                "uncompressed_size": uncompressed_len,
                "reserved": chunk_reserved.hex(" "),
            }
        )

        if chunk_name == "META":
            meta.update(parse_meta_chunk(decoded))

        elif chunk_name == "SSTR":
            shared_strings = parse_sstr_chunk(decoded)

        elif chunk_name == "INST":
            class_id, class_name, is_service, referents, _service_markers = parse_inst_chunk(decoded)
            insts: List[Instance] = []
            for ref in referents:
                inst = Instance(
                    class_id=class_id,
                    class_name=class_name,
                    referent=ref,
                    is_service=is_service,
                )
                insts.append(inst)
                instances_by_referent[ref] = inst
            instances_by_class_id[class_id] = insts

        elif chunk_name == "PROP":
            r2 = Reader(decoded)
            class_id = r2.u32()
            prop_name = r2.rbx_string().decode("utf-8", errors="replace")
            type_id = r2.u8()

            if class_id not in instances_by_class_id:
                raise KeyError(f"PROP for unknown class_id {class_id} ({prop_name})")

            insts = instances_by_class_id[class_id]
            try:
                kind, values = decode_prop_values(type_id, len(insts), r2)
            except Exception as e:
                print(
                    f"[SKIP] property={prop_name!r} "
                    f"type=0x{type_id:02X}"
                )
                continue
            if len(values) != len(insts):
                raise ValueError(
                    f"Property {prop_name} for class_id {class_id} decoded {len(values)} values, "
                    f"expected {len(insts)}"
                )

            for inst, value in zip(insts, values):
                inst.properties.append(PropertyValue(prop_name, kind, value))

        elif chunk_name == "PRNT":
            prnt_children, prnt_parents = parse_prnt_chunk(decoded)

        elif chunk_name == "END":
            # Compatibility payload should be </roblox>, but we don't depend on it.
            break

        else:
            # Unknown chunk; keep it in raw_chunks but don't try to interpret it.
            pass

    # Apply parents
    roots: List[int] = []
    if prnt_children and prnt_parents:
        for child_ref, parent_ref in zip(prnt_children, prnt_parents):
            child = instances_by_referent.get(child_ref)
            if child is None:
                continue
            child.parent = parent_ref
            if parent_ref is None or parent_ref == -1:
                roots.append(child_ref)
            else:
                parent = instances_by_referent.get(parent_ref)
                if parent is not None:
                    parent.children.append(child_ref)
                else:
                    roots.append(child_ref)
    else:
        # Fallback if PRNT is missing
        for ref, inst in instances_by_referent.items():
            if inst.parent is None:
                roots.append(ref)

    return Model(
        header=header,
        meta=meta,
        shared_strings=shared_strings,
        instances_by_referent=instances_by_referent,
        instances_by_class_id=instances_by_class_id,
        roots=roots,
        raw_chunks=raw_chunks,
    )


# -----------------------------
# JSON conversion
# -----------------------------

def jsonable(value: Any) -> Any:
    if isinstance(value, bytes):
        return {"__bytes_base64__": base64.b64encode(value).decode("ascii")}
    if isinstance(value, list):
        return [jsonable(v) for v in value]
    if isinstance(value, tuple):
        return [jsonable(v) for v in value]
    if isinstance(value, dict):
        return {k: jsonable(v) for k, v in value.items()}
    return value


def model_to_json(model: Model) -> Dict[str, Any]:
    instances = []
    for ref, inst in sorted(model.instances_by_referent.items(), key=lambda kv: kv[0]):
        instances.append(
            {
                "referent": ref,
                "class_name": inst.class_name,
                "class_id": inst.class_id,
                "is_service": inst.is_service,
                "parent": inst.parent,
                "children": inst.children,
                "properties": [
                    {"name": p.name, "kind": p.kind, "value": jsonable(p.value)}
                    for p in inst.properties
                ],
            }
        )

    return {
        "header": model.header,
        "meta": model.meta,
        "shared_strings": [
            {
                "md5_base64": base64.b64encode(md5).decode("ascii"),
                "value_base64": base64.b64encode(val).decode("ascii"),
            }
            for md5, val in model.shared_strings
        ],
        "roots": model.roots,
        "instances": instances,
        "chunks": model.raw_chunks,
    }


# -----------------------------
# RBXMX XML writing
# -----------------------------

def xml_prop_element(prop: PropertyValue, inst: Instance, source_dir: Optional[Path]) -> str:
    name_attr = f' name="{escape_xml(prop.name)}"'

    # Special handling: Source -> ProtectedString with base64 Lua comment
    if prop.kind == "bytecode":
        blob: bytes = prop.value

        if prop.name == "Source":
            b64 = base64.b64encode(blob).decode("ascii")
            text = b64
            file_name = ""
            if source_dir is not None:
                source_dir.mkdir(parents=True, exist_ok=True)
                file_name = f"{slugify(inst.class_name)}_{slugify(prop.name)}_{inst.referent}.luac"
                (source_dir / file_name).write_bytes(blob)

            resultout = ""
            ms = time.time_ns() // 1_000_000
            name = f"TEMPLUACSTR {str(ms)}.luac"
            output_path = Path.cwd() / name 
            output_path.write_bytes(blob)
            global should_decomp
            if should_decomp == False: #standard
                print("disassembling script, may take long.")
                result = subprocess.run(
                    ["python", "luau_disasm.py", name],
                    capture_output=True,
                    text=True
                )
                resultout = "\n".join(result.stdout.splitlines())
                whitelistedstr = "[!] Warning: failed to parse "
                if result.stderr == "" or len(result.stderr) >= len(whitelistedstr) and result.stderr[:len(whitelistedstr)] == whitelistedstr:
                    if result.stderr != "":
                        resultout = "//Disassembler errored, Though there's still a partial disassembly available//\n" + resultout
                        print("disassembler error (though still partially disassembled): ", result.stderr)
                    #else:
                    os.remove(name)
                else:
                    print("disassembler error: ", result.stderr)
                    resultout = "//The LuaUC disassembler errored.//"
                    os.remove(name)
            
            elif should_decomp == True:
                print("decompiling script, may take long.")
                result = subprocess.run(
                    ["python", "luau_decomp.py", name],
                    capture_output=True,
                    text=True
                )
                hello = ""
                print(result.stderr)
                try:
                    decompname = f"TEMPLUACSTR {str(ms)}_decompiled.lua"
                    with open(decompname, "r") as file:
                        resultout = file.read()
                    os.remove(decompname)
                except Exception as e:
                    hello == e
                if "Traceback (most recent call last):" in result.stderr and not hello == "":
                    print("issue: " + e)
                    resultout = "//Decompiler errored//\n" + resultout
                    
                os.remove(name)
            if should_decomp is True:
                return f'<ProtectedString{name_attr}>{cdata("--[[" + "\nbase64 bytecode: \n" +text +  "\nStored Filename (put --sources [path] to see this): " + file_name + "\n\n]]\n\n" + resultout)}</ProtectedString>'
            else:
                return f'<ProtectedString{name_attr}>{cdata("--[[" + "\nbase64 bytecode: \n" +text +  "\nStored Filename (put --sources [path] to see this): " + file_name + "\n\n" + resultout+"\n]]")}</ProtectedString>'
        # For any other bytecode-ish property, preserve as raw bytes.
        b64 = base64.b64encode(blob).decode("ascii")
        return f'<BinaryString{name_attr}>{b64}</BinaryString>'

    if prop.kind == "string":
        text = prop.value if isinstance(prop.value, str) else prop.value.decode("utf-8", errors="replace")
        return f'<string{name_attr}>{escape_xml(text)}</string>'

    if prop.kind == "bool":
        return f'<bool{name_attr}>{"true" if prop.value else "false"}</bool>'

    if prop.kind == "int":
        return f'<int{name_attr}>{int(prop.value)}</int>'

    if prop.kind == "int64":
        return f'<int64{name_attr}>{int(prop.value)}</int64>'

    if prop.kind == "token":
        # XML spec calls Enum properties "token"
        return f'<token{name_attr}>{int(prop.value)}</token>'

    if prop.kind == "ref":
        if prop.value is None or prop.value == -1:
            return f'<Ref{name_attr}>null</Ref>'
        return f'<Ref{name_attr}>RBX{int(prop.value)}</Ref>'

    if prop.kind == "sharedstring":
        # We don't create a SharedStrings repository for these unless needed; this is a
        # convenient conservative output. If you hit a file that uses SharedString heavily,
        # I can extend this to emit the SharedStrings block too.
        if isinstance(prop.value, int):
            return f'<SharedString{name_attr}>{prop.value}</SharedString>'
        if isinstance(prop.value, bytes):
            return f'<SharedString{name_attr}>{base64.b64encode(prop.value).decode("ascii")}</SharedString>'
        return f'<SharedString{name_attr}>{escape_xml(str(prop.value))}</SharedString>'
    if prop.kind == "raw":
        return (
            f'<BinaryString{name_attr}>'
            f'{base64.b64encode(prop.value).decode("ascii")}'
            f'</BinaryString>'
        )

    # Fallback: preserve as base64 in a BinaryString.
    raw = json.dumps(jsonable(prop.value), ensure_ascii=False).encode("utf-8")
    return f'<BinaryString{name_attr}>{base64.b64encode(raw).decode("ascii")}</BinaryString>'


def serialize_item(inst: Instance, model: Model, indent: int, source_dir: Optional[Path]) -> str:
    pad = "  " * indent
    lines: List[str] = []

    ref_name = f"RBX{inst.referent}"
    lines.append(f'{pad}<Item class="{escape_xml(inst.class_name)}" referent="{escape_xml(ref_name)}">')
    lines.append(f"{pad}  <Properties>")

    for prop in inst.properties:
        lines.append("  " * (indent + 2) + xml_prop_element(prop, inst, source_dir))

    lines.append(f"{pad}  </Properties>")

    for child_ref in inst.children:
        child = model.instances_by_referent.get(child_ref)
        if child is not None:
            lines.append(serialize_item(child, model, indent + 1, source_dir))

    lines.append(f"{pad}</Item>")
    return "\n".join(lines)


def model_to_rbxmx(model: Model, source_dir: Optional[Path] = None) -> str:
    lines: List[str] = []
    lines.append('<?xml version="1.0" encoding="utf-8"?>')
    lines.append('<roblox version="4">')

    for k, v in model.meta.items():
        lines.append(f'  <Meta name="{escape_xml(k)}">{escape_xml(v)}</Meta>')

    # Write root items in PRNT order if we have it; otherwise fall back to class/referent sort.
    root_refs = model.roots[:] if model.roots else sorted(
        [ref for ref, inst in model.instances_by_referent.items() if inst.parent in (None, -1)]
    )

    for ref in root_refs:
        inst = model.instances_by_referent.get(ref)
        if inst is not None:
            lines.append(serialize_item(inst, model, 1, source_dir))

    if model.shared_strings:
        lines.append("  <SharedStrings>")
        for md5_raw, value in model.shared_strings:
            md5_b64 = base64.b64encode(md5_raw).decode("ascii")
            val_b64 = base64.b64encode(value).decode("ascii")
            lines.append(f'    <SharedString md5="{escape_xml(md5_b64)}">{val_b64}</SharedString>')
        lines.append("  </SharedStrings>")

    lines.append("</roblox>")
    return "\n".join(lines)


# -----------------------------
# CLI
# -----------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Parse a Roblox RBXM binary model, rebuild hierarchy, and export RBXMX with Source as base64 comments."
    )
    ap.add_argument("input", type=Path, help="Input .rbxm file")
    ap.add_argument("--out", type=Path, default=None, help="Output .rbxmx file")
    ap.add_argument("--json", dest="json_out", type=Path, default=None, help="Optional JSON sidecar output")
    ap.add_argument("--sources", type=Path, default=None, help="Directory to write raw .luac files extracted from Source properties")
    ap.add_argument("--decomp", action="store_true", help="should add an additional decompiled output, may not be as accurate")
    args = ap.parse_args()

    if args.decomp is not False:
        global should_decomp
        should_decomp = True
    print("Disassembly may error (just cuz of a bad disassembler), don't worry as this wont affect the main script.")
    model = parse_rbxm(args.input)

    out_rbxmx = args.out or args.input.with_suffix(".rbxmx")
    xml = model_to_rbxmx(model, source_dir=args.sources)
    out_rbxmx.write_text(xml, encoding="utf-8")

    if args.json_out is not None:
        args.json_out.write_text(json.dumps(model_to_json(model), indent=2, ensure_ascii=False), encoding="utf-8")
    else:
        default_json = args.input.with_suffix(".json")
        default_json.write_text(json.dumps(model_to_json(model), indent=2, ensure_ascii=False), encoding="utf-8")


    print(f"Wrote: {out_rbxmx}")
    if args.json_out is not None:
        print(f"Wrote: {args.json_out}")
    else:
        print(f"Wrote: {args.input.with_suffix('.json')}")

    if args.sources is not None:
        print(f"Wrote raw Source blobs to: {args.sources}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())