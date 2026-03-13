import sys
from pathlib import Path
BASE_DIR = Path(__file__).resolve().parent
DAFNY_DIR = BASE_DIR / "project-py"
sys.path.insert(0, str(DAFNY_DIR))

import os
import struct
from pathlib import Path

import Huffman
import _dafny as _dafny
sys.setrecursionlimit(300000)

MAGIC = b"HUF1"

def bytes_to_dafny_seq(data: bytes):
    return _dafny.SeqWithoutIsStrInference(list(data))

def dafny_seq_to_bytes(seq_obj) -> bytes:
    return bytes(int(x) for x in list(seq_obj))

def pack_bits(bits) -> tuple[bytes, int]:
    bit_list = [1 if b else 0 for b in list(bits)]
    valid_bit_count = len(bit_list)

    out = bytearray()
    current = 0
    count = 0

    for bit in bit_list:
        current = (current << 1) | bit
        count += 1
        if count == 8:
            out.append(current)
            current = 0
            count = 0

    if count > 0:
        current <<= (8 - count)
        out.append(current)

    return bytes(out), valid_bit_count

def unpack_bits(data: bytes, valid_bit_count: int):
    bits = []
    produced = 0

    for byte in data:
        for shift in range(7, -1, -1):
            if produced >= valid_bit_count:
                break
            bits.append(((byte >> shift) & 1) == 1)
            produced += 1

    return _dafny.SeqWithoutIsStrInference(bits)

def write_compressed_file(
    out_path: str,
    original_len: int,
    freq_list,
    packed_bits: bytes,
    valid_bit_count: int,
):
    freq_items = list(freq_list)

    with open(out_path, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack(">Q", original_len))
        f.write(struct.pack(">Q", valid_bit_count))
        f.write(struct.pack(">I", len(freq_items)))

        for symbol, count in freq_items:
            # symbol is a byte value 0..255
            f.write(struct.pack(">B", int(symbol)))
            f.write(struct.pack(">Q", int(count)))

        f.write(packed_bits)

def read_compressed_file(path: str):
    with open(path, "rb") as f:
        magic = f.read(4)
        if magic != MAGIC:
            raise ValueError("Not a valid .huffbmp file")

        original_len = struct.unpack(">Q", f.read(8))[0]
        valid_bit_count = struct.unpack(">Q", f.read(8))[0]
        freq_count = struct.unpack(">I", f.read(4))[0]

        freq_items = []
        for _ in range(freq_count):
            symbol = struct.unpack(">B", f.read(1))[0]
            count = struct.unpack(">Q", f.read(8))[0]
            freq_items.append((symbol, count))

        packed_bits = f.read()

    freq_list = _dafny.SeqWithoutIsStrInference(freq_items)
    return original_len, valid_bit_count, freq_list, packed_bits

def compress_bmp(input_bmp: str, output_huff: str):
    with open(input_bmp, "rb") as f:
        raw = f.read()

    if not raw.startswith(b"BM"):
        raise ValueError("Input file is not a BMP file")

    msg = bytes_to_dafny_seq(raw)

    freq_list = Huffman.default__.BuildFreqFromMsg(msg)
    t = Huffman.default__.BuildHuffmanFromMsg(msg)
    ok = Huffman.default__.CheckPrefixFree(t)
    bits = Huffman.default__.Encode(t, msg)

    packed_bits, valid_bit_count = pack_bits(bits)

    write_compressed_file(
        output_huff,
        original_len=len(raw),
        freq_list=freq_list,
        packed_bits=packed_bits,
        valid_bit_count=valid_bit_count,
    )

    original_size = len(raw)
    compressed_size = os.path.getsize(output_huff)

    print("\nCompression complete")
    print("Input BMP:", input_bmp)
    print("Compressed file:", output_huff)
    print("Prefix-free (verified by Dafny):", ok)
    print("Original size (bytes):", original_size)
    print("Compressed size (bytes):", compressed_size)
    print("Original size (bits):", original_size * 8)
    print("Compressed Huffman bits:", valid_bit_count)

    if compressed_size < original_size:
        saved = original_size - compressed_size
        print("Saved bytes:", saved)
        print("Compression ratio:", round(compressed_size / original_size, 4))
    else:
        extra = compressed_size - original_size
        print("Compressed file is larger by bytes:", extra)
        print("Ratio:", round(compressed_size / original_size, 4))

    return {
        "freq_list": freq_list,
        "tree": t,
        "valid_bit_count": valid_bit_count,
    }

def decompress_bmp(input_huff: str, output_bmp: str):
    original_len, valid_bit_count, freq_list, packed_bits = read_compressed_file(input_huff)

    t = Huffman.default__.BuildHuffman(freq_list)
    bits = unpack_bits(packed_bits, valid_bit_count)
    decoded = Huffman.default__.DecodeOption(t, bits)

    if not decoded.is_Some:
        raise RuntimeError("Dafny DecodeOption returned None; decompression failed")

    out_seq = decoded.value
    out_bytes = dafny_seq_to_bytes(out_seq)

    if len(out_bytes) != original_len:
        raise RuntimeError(
            f"Decoded length mismatch: expected {original_len}, got {len(out_bytes)}"
        )

    with open(output_bmp, "wb") as f:
        f.write(out_bytes)

    print("\nDecompression complete")
    print("Compressed file:", input_huff)
    print("Recovered BMP:", output_bmp)
    print("Recovered size (bytes):", len(out_bytes))

def compare_files(path1: str, path2: str):
    with open(path1, "rb") as f1, open(path2, "rb") as f2:
        b1 = f1.read()
        b2 = f2.read()

    same = b1 == b2
    print("\nRound-trip byte equality:", same)
    return same

def main():
    bmp_path = "image.bmp"
    if not bmp_path:
        print("Empty path.")
        return

    bmp = Path(bmp_path)
    if not bmp.exists():
        print("File not found.")
        return

    compressed_path = str(bmp.with_suffix(".huffbmp"))
    recovered_path = str(bmp.with_name(bmp.stem + "_recovered.bmp"))

    compress_bmp(str(bmp), compressed_path)
    decompress_bmp(compressed_path, recovered_path)
    compare_files(str(bmp), recovered_path)

if __name__ == "__main__":
    main()