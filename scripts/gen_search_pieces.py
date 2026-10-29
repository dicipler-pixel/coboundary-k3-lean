#!/usr/bin/env python3
# SCRIPT: GEN-SEARCH-PIECES-01
"""Regenerate the k = 7 and k = 8 branch-and-bound pieces of CoboundaryK3/Basic.lean.

The exhaustions for k = 7 and k = 8 are split by the gauge on the first vertices into
kernel-checked leaves (36 for k = 7, 216 for k = 8), assembled by `search_split` into nodes and
a root. Those 300-odd theorem blocks are machine-made; this script is the machine.

Usage:
    python3 scripts/gen_search_pieces.py           print the block to stdout
    python3 scripts/gen_search_pieces.py --check   exit 1 unless Basic.lean holds it exactly
    python3 scripts/gen_search_pieces.py --write   replace the block in Basic.lean

Why `--check` proves what it claims. The block sits in Basic.lean between two fixed lines: the
section comment that opens it and the docstring of `witness_k7` that follows it. `--check` cuts
out exactly the text between them and compares it, character for character, with the text this
script generates from the four parameters below (witness, bound `D`, number of vertices, split
depth). Equality shows that the committed pieces are the complete, regular split the parameters
describe: every prefix `[1, a, b]` (k = 7) or `[1, a, b, c]` (k = 8) over the six elements of
Sym(3), each node assembling its six children in `S3list` order, nothing missing, duplicated or
edited by hand. It does not check the proofs themselves; the Lean kernel does that in CI. A
difference in one character, an extra or missing piece, or a moved marker makes it fail.
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASIC = ROOT / "CoboundaryK3" / "Basic.lean"
ELEMS = ["1", "t01", "t12", "t02", "c1", "c2"]  # the order of `S3list`
START = "/-! ### The k = 7 and k = 8 exhaustions, split by the gauge on the first vertices -/\n\n"
END = "\n\n/-- **Theorem 3, k = 7.**"
LEAF_FUEL = 4  # vertices left to assign in every leaf

# (name, witness, D, number of vertices k, number of fixed vertices after vertex 0 in a leaf)
CASES = [("k7", "w7", 12, 7, 2), ("k8", "w8", 27, 8, 3)]


def prefix(idx: tuple[int, ...]) -> str:
    return "[" + ", ".join(["1"] + [ELEMS[i] for i in idx]) + "]"


def suffix(idx: tuple[int, ...]) -> str:
    return "".join(f"_{i}" for i in idx)


def tuples(depth: int) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = [()]
    for _ in range(depth):
        out = [t + (i,) for t in out for i in range(6)]
    return out


def block_for(name: str, w: str, d: int, k: int, depth: int) -> list[str]:
    assert LEAF_FUEL + depth + 1 == k, "the leaves must finish the gauge"
    pieces = []
    for idx in tuples(depth):
        pieces.append(
            f"private theorem {name}_leaf{suffix(idx)} : "
            f"search {w} {d} {LEAF_FUEL} {prefix(idx)} = true := by\n"
            "  decide +kernel")
    for level in range(depth - 1, -1, -1):
        fuel = k - 1 - level
        for idx in tuples(level):
            child = "leaf" if level == depth - 1 else "node"
            children = " ".join(f"{name}_{child}{suffix(idx + (i,))}" for i in range(6))
            label = f"{name}_node{suffix(idx)}" if level > 0 else f"{name}_root"
            pieces.append(
                f"private theorem {label} : search {w} {d} {fuel} {prefix(idx)} = true :=\n"
                f"  search_split {w} {d} {fuel - 1} {prefix(idx)} {children}")
    return pieces


def generate() -> str:
    pieces: list[str] = []
    for case in CASES:
        pieces += block_for(*case)
    return "\n\n".join(pieces)


def current() -> tuple[str, int, int]:
    text = BASIC.read_text()
    if text.count(START) != 1 or text.count(END) != 1:
        raise SystemExit("gen_search_pieces: block markers not found exactly once in Basic.lean")
    a = text.index(START) + len(START)
    b = text.index(END)
    return text, a, b


def main(argv: list[str]) -> int:
    gen = generate()
    if "--check" in argv:
        text, a, b = current()
        if text[a:b] != gen:
            print("gen_search_pieces: Basic.lean differs from the generated pieces; "
                  "run scripts/gen_search_pieces.py --write", file=sys.stderr)
            return 1
        print(f"gen_search_pieces: OK, {gen.count('private theorem')} pieces match")
        return 0
    if "--write" in argv:
        text, a, b = current()
        BASIC.write_text(text[:a] + gen + text[b:])
        return 0
    sys.stdout.write(gen + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
