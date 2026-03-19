import sys
from pathlib import Path
BASE_DIR = Path(__file__).resolve().parent
DAFNY_DIR = BASE_DIR / "project-py"
sys.path.insert(0, str(DAFNY_DIR))

import os
import Huffman
import _dafny as _dafny
from graphviz import Digraph
from itertools import count
import subprocess

sys.setrecursionlimit(300000)

TEXT_FILE = "input.txt"

def to_dafny_msg(text):
    return _dafny.SeqWithoutIsStrInference([_dafny.CodePoint(c) for c in text])


def draw_tree_png(t, filename_base="huffman_tree"):
    dot = Digraph("HuffmanTree", format="png")
    dot.attr(rankdir="TB", bgcolor="white")
    dot.attr("node", style="filled", fontname="Helvetica")
    dot.attr("edge", fontname="Helvetica", penwidth="1.5")
    nid = count(0)

    def sym_label(sym_obj):
        if hasattr(sym_obj, 'is_Real'):
            if sym_obj.is_Real:
                return repr(str(sym_obj.s))
            else:
                return "\u2205"
        return repr(str(sym_obj))

    def add_node(tree_obj):
        my_id = f"n{next(nid)}"
        if tree_obj.is_Leaf:
            label = sym_label(tree_obj.sym)
            w = tree_obj.w
            dot.node(
                my_id,
                f"{label}\\nw={w}",
                shape="box",
                fillcolor="lightyellow",
                color="black"
            )
        else:
            w = tree_obj.w
            dot.node(
                my_id,
                f"w={w}",
                shape="ellipse",
                fillcolor="lightblue",
                color="navy"
            )
            left_id = add_node(tree_obj.left)
            right_id = add_node(tree_obj.right)
            dot.edge(my_id, left_id, label="0", color="black", fontcolor="black")
            dot.edge(my_id, right_id, label="1", color="red", fontcolor="red")
        return my_id

    add_node(t)
    outpath = dot.render(filename_base, cleanup=True)
    return outpath


def try_open_file(path):
    try:
        subprocess.run(["xdg-open", path], check=False)
    except Exception:
        pass


def extract_codes(t):
    codes = {}

    def sym_label(sym_obj):
        if hasattr(sym_obj, 'is_Real'):
            if sym_obj.is_Real:
                return str(sym_obj.s)
            else:
                return "<SENTINEL>"
        return str(sym_obj)

    def walk(node, path_bits):
        if node.is_Leaf:
            codes[sym_label(node.sym)] = path_bits[:]
        else:
            walk(node.left, path_bits + [0])
            walk(node.right, path_bits + [1])

    walk(t, [])
    return codes


def printable_symbol(s):
    if s == "\n":
        return "\\n"
    if s == "\t":
        return "\\t"
    if s == "\r":
        return "\\r"
    if s == " ":
        return "' '"
    return repr(s)


def main():
    if not os.path.exists(TEXT_FILE):
        print(f"File not found: {TEXT_FILE}")
        return

    with open(TEXT_FILE, "r", encoding="utf-8") as f:
        text = f.read()

    if not text:
        print("Text file is empty.")
        return

    print(f"\nReading text from: {TEXT_FILE}")
    print(f"Character count: {len(text)}")
    print(f"Distinct symbols: {len(set(text))}")

    # Frequency table for display (computed in Python)
    from collections import Counter
    freq_counter = Counter(text)
    print("\nFrequency table:")
    for ch, cnt in sorted(freq_counter.items(), key=lambda x: -x[1]):
        print(f"  {printable_symbol(ch):>6s} : {cnt}")

    msg = to_dafny_msg(text)

    # Build tree via Safe API
    t = Huffman.default__.SafeBuildHuffmanFromMsg(msg)

    png_path = draw_tree_png(t, "text_huffman_tree")
    print(f"\nTree image saved to: {png_path}")

    codes = extract_codes(t)
    print("\nCode table:")
    for s in sorted(codes.keys()):
        print(f"  {printable_symbol(s):>6s} : {''.join(map(str, codes[s]))}")

    ok = Huffman.default__.CheckPrefixFree(t)
    print("\nPrefix-free (verified by Dafny):", ok)

    # Encode via Safe API
    bits = Huffman.default__.SafeEncode(t, msg)
    bits_py = [1 if b else 0 for b in list(bits)]

    preview_len = 300
    bit_string = ''.join(map(str, bits_py))

    # --- Compression summary ---
    original_bytes = len(text.encode("utf-8"))
    original_bits = original_bytes * 8
    compressed_bits = len(bits_py)
    compressed_bytes_est = (compressed_bits + 7) // 8

    print("\nCompression complete")
    print("Input file:", TEXT_FILE)
    print("Original size (bytes):", original_bytes)
    print("Original size (bits):", original_bits)
    print("Compressed Huffman bits:", compressed_bits)
    print("Approx packed bytes:", compressed_bytes_est)

    if compressed_bytes_est < original_bytes:
        saved = original_bytes - compressed_bytes_est
        print("Saved bytes:", saved)
        print("Compression ratio:", round(compressed_bits / original_bits, 4))
    else:
        extra = compressed_bytes_est - original_bytes
        print("Compressed is larger by bytes:", extra)
        print("Ratio:", round(compressed_bits / original_bits, 4))

    if len(bit_string) <= preview_len:
        print("\nHuffman encoded bits:", bit_string)
    else:
        print(f"\nHuffman encoded bits (first {preview_len}):", bit_string[:preview_len] + "...")

    # --- Decode via Safe API ---
    decoded = Huffman.default__.SafeDecodeOption(t, bits)
    if decoded.is_Some:
        out = ''.join(str(cp) for cp in decoded.value)

        decoded_file = "decoded_output.txt"
        with open(decoded_file, "w", encoding="utf-8") as f:
            f.write(out)

        print("\nDecompression complete")
        print("Decoded text saved to:", decoded_file)
        print("Decoded size (chars):", len(out))
        print("\nPrefix-free (verified by Dafny):", ok)
        print("Round-trip decode correct?:", out == text)
    else:
        print("\nDecode failed on encoded bits (should not happen).")


if __name__ == "__main__":
    main()