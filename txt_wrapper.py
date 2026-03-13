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

    def add_node(tree_obj):
        my_id = f"n{next(nid)}"
        if tree_obj.is_Leaf:
            sym = repr(str(tree_obj.sym))
            w = tree_obj.w
            dot.node(
                my_id,
                f"{sym}\\nw={w}",
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

    def walk(node, path_bits):
        if node.is_Leaf:
            codes[str(node.sym)] = path_bits[:]
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

    if len(set(text)) < 2:
        print("Need at least 2 distinct characters for the current Dafny Huffman implementation.")
        return

    print(f"\nReading text from: {TEXT_FILE}")
    print(f"Character count: {len(text)}")

    msg = to_dafny_msg(text)

    freq_list = Huffman.default__.BuildFreqFromMsg(msg)
    print("\nFrequency table (computed by Dafny):")
    for (k, v) in freq_list:
        print(f"{printable_symbol(str(k))} : {v}")

    t = Huffman.default__.BuildHuffmanFromMsg(msg)

    png_path = draw_tree_png(t, "text_huffman_tree")
    print(f"\nTree image saved to: {png_path}")

    codes = extract_codes(t)
    print("\nCode table:")
    for s in sorted(codes.keys()):
        print(f"{printable_symbol(s)} : {''.join(map(str, codes[s]))}")

    ok = Huffman.default__.CheckPrefixFree(t)
    print("\nPrefix-free (verified by Dafny):", ok)

    bits = Huffman.default__.Encode(t, msg)
    bits_py = [1 if b else 0 for b in list(bits)]

    print("\nHuffman encoded bits length:", len(bits_py))

    preview_len = 300
    bit_string = ''.join(map(str, bits_py))
    if len(bit_string) <= preview_len:
        print("Huffman encoded bits:", bit_string)
    else:
        print("Huffman encoded bits preview:", bit_string[:preview_len] + "...")

    original_bits = len(text.encode("utf-8")) * 8
    original_bytes = len(text.encode("utf-8"))
    compressed_bits = len(bits_py)
    compressed_bytes_est = (compressed_bits + 7) // 8

    print("\nOriginal text size:")
    print("Bytes (UTF-8):", original_bytes)
    print("Bits:", original_bits)

    print("\nCompressed Huffman size:")
    print("Bits:", compressed_bits)
    print("Approx packed bytes:", compressed_bytes_est)

    saved_bits = original_bits - compressed_bits
    saved_bytes = original_bytes - compressed_bytes_est

    print("\nSize difference:")
    print("Bits saved:", saved_bits)
    print("Approx bytes saved:", saved_bytes)
    print("Compression ratio:", round(compressed_bits / original_bits, 4))

    decoded = Huffman.default__.DecodeOption(t, bits)
    if decoded.is_Some:
        out_seq = decoded.value
        out = ''.join(str(cp) for cp in out_seq)
        print("\nRound-trip decode correct?:", out == text)

        decoded_file = "decoded_output.txt"
        with open(decoded_file, "w", encoding="utf-8") as f:
            f.write(out)
        print(f"Decoded text saved to: {decoded_file}")
    else:
        print("\nDecode failed on encoded bits (should not happen).")


if __name__ == "__main__":
    main()