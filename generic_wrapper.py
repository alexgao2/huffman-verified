import sys
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
DAFNY_DIR = BASE_DIR / "project-py"
sys.path.insert(0, str(DAFNY_DIR))

import Huffman
import _dafny as _dafny
from graphviz import Digraph
from itertools import count
import subprocess


def to_dafny_msg(text):
    return _dafny.SeqWithoutIsStrInference([_dafny.CodePoint(c) for c in text])


def to_dafny_bits(py_bits):
    return _dafny.SeqWithoutIsStrInference(py_bits)


def draw_tree_png(t, filename_base="huffman_tree"):
    dot = Digraph("HuffmanTree", format="png")
    dot.attr(rankdir="TB", bgcolor="white")
    dot.attr("node", style="filled", fontname="Helvetica")
    dot.attr("edge", fontname="Helvetica", penwidth="1.5")
    nid = count(0)

    def sym_label(sym_obj):
        """Handle both plain chars and WSym-wrapped chars."""
        if hasattr(sym_obj, 'is_Real'):
            # It's a WSym
            if sym_obj.is_Real:
                return str(sym_obj.s)
            else:
                return "\u2205"  # sentinel symbol shown as empty-set
        return str(sym_obj)

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
    """Extract code table, handling WSym-wrapped symbols."""
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


def flip_middle_bit(bits_py):
    if not bits_py:
        return bits_py[:]
    out = bits_py[:]
    mid = len(out) // 2
    out[mid] = not out[mid]
    return out


def drop_middle_bit(bits_py):
    if not bits_py:
        return bits_py[:]
    mid = len(bits_py) // 2
    return bits_py[:mid] + bits_py[mid + 1:]


def insert_extra_bit_middle(bits_py, value=False):
    mid = len(bits_py) // 2
    return bits_py[:mid] + [value] + bits_py[mid:]


def print_decode_result(label, result):
    print(f"\n{label}:")
    if result.is_Some:
        print("Dafny DecodeWithCRC result: Some(...)")
    else:
        print("Dafny DecodeWithCRC result: None")


def main():
    text = input("\nEnter text: ").strip()
    if not text:
        print("Empty input.")
        return

    msg = to_dafny_msg(text)

    t = Huffman.default__.SafeBuildHuffmanFromMsg(msg)

    png_path = draw_tree_png(t, "huffman_tree")
    print(f"\nTree image saved to: {png_path}")
    try_open_file(png_path)

    codes = extract_codes(t)
    print("\nCode table:")
    for s in sorted(codes.keys()):
        bits_str = ''.join(map(str, codes[s]))
        print(f"  {repr(s):>14s} : {bits_str}")

    ok = Huffman.default__.CheckPrefixFree(t)
    print("\nPrefix-free (verified by Dafny):", ok)

    round_trip_ok = Huffman.default__.SafeCheckRoundTrip(t, msg)
    print("Round-trip correct? (verified by Dafny):", round_trip_ok)

    bits, crc = Huffman.default__.SafeEncodeWithCRC(t, msg)
    bits_py = list(bits)

    print("\nCRC value (computed by Dafny):", crc)
    print("Huffman encoded bits length:", len(bits_py))
    print("Huffman encoded bits:", ''.join('1' if b else '0' for b in bits_py))


    # Decode the encoded bits back and print
    decoded_result = Huffman.default__.SafeDecodeWithCRC(t, bits, crc)
    if decoded_result.is_Some:
        decoded_chars = ''.join(str(c) for c in decoded_result.value)
        print("\nDecoded text from Dafny:", decoded_chars)
    else:
        print("\nDecoded text from Dafny: FAILED")

    print("\n--- Robustness experiment using Dafny CRC verification ---")

    # Flip one bit
    flipped_bits = to_dafny_bits(flip_middle_bit(bits_py))
    flipped_result = Huffman.default__.SafeDecodeWithCRC(t, flipped_bits, crc)
    print_decode_result("After flipping one bit", flipped_result)

    # Drop one bit
    dropped_bits = to_dafny_bits(drop_middle_bit(bits_py))
    dropped_result = Huffman.default__.SafeDecodeWithCRC(t, dropped_bits, crc)
    print_decode_result("After dropping one bit", dropped_result)

    # Insert one extra bit
    inserted_bits = to_dafny_bits(insert_extra_bit_middle(bits_py, value=False))
    inserted_result = Huffman.default__.SafeDecodeWithCRC(t, inserted_bits, crc)
    print_decode_result("After inserting one extra bit", inserted_result)


if __name__ == "__main__":
    main()