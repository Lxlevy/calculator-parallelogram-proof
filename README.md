# calculator-parallelogram-proof: Parallelogram traces on a calculator keypad are always multiples of 11

Tap four keys of a calculator keypad that form the corners of a parallelogram, in
the order in which the parallelogram is drawn. The four-digit number that appears
is always a multiple of 11.

Draw `1 → 4 → 8 → 5` and the calculator shows **1485 = 11 × 135** — and `135` is
exactly the quotient the formula below predicts.

This repository contains

* a **proof** that isolates the mechanism and displays the quotient,
* a **Lean 4 formalization** of the statement (core library only, no Mathlib),
* an **independent exhaustive Python check** over the whole keypad,
* a **typeset report** (LaTeX, 7 pages) collecting all of the above.

## The keypad, and what a "parallelogram" is

```
 7 8 9     row 3
 4 5 6     row 2
 1 2 3     row 1
```

Number the rows from the bottom (`1, 2, 3`) and the columns from the left
(`0, 1, 2`). The digit on key `(r, c)` is

```
digit(r, c) = 3r + c − 2
```

so the keypad is an **affine lattice**: one step right adds `1` to the digit and
one step up adds `3`, no matter where you start.

Four corner keys `p₁ p₂ p₃ p₄`, listed in tap order, form a parallelogram exactly
when the diagonals bisect each other:

```
p₁ + p₃ = p₂ + p₄        (coordinate-wise)
```

## Why the number is a multiple of 11

Because `digit` is affine, the *digits* inherit the same relation:

```
d₁ + d₃ = d₂ + d₄        (opposite digits have equal sums)
```

That is precisely the condition under which the alternating digit sum vanishes,
and the alternating digit sum is the classical test for divisibility by 11:

```
N = 1000d₁ + 100d₂ + 10d₃ + d₄ ≡ −(d₁ − d₂ + d₃ − d₄) ≡ 0   (mod 11)
```

since `10 ≡ −1`, `100 ≡ 1`, `1000 ≡ −1`. Substituting `d₄ = d₁ + d₃ − d₂` gives
the explicit identity

```
1000d₁ + 100d₂ + 10d₃ + d₄ = 11 · (91d₁ + 9d₂ + d₃)
```

For `1 → 4 → 8 → 5` the bracket is `91·1 + 9·4 + 8 = 135`, which is what the
calculator displays. Nothing in the argument depends on the side lengths, the
orientation, or which of the eight traversal orders is used.

Written in side lengths instead — one side changes the digit by `a`, the other by
`b`, starting from `s` — the tapped digits are `s, s+a, s+a+b, s+b` and

```
1000s + 100(s+a) + 10(s+a+b) + (s+b) = 11 · (101s + 10a + b)
```

for every choice of `s, a, b ∈ ℤ`.

## Results

| Quantity | Value |
| --- | --- |
| Ordered quadruples of digit keys with `p₁ + p₃ = p₂ + p₄` (degenerate included) | 361 |
| Genuine parallelograms (four distinct corners, non-zero area) | 176 |
| Distinct shapes, i.e. vertex sets | 22 (each with 8 traversal orders) |
| Distinct four-digit numbers produced | 176 |
| Smallest / largest | 1254 = 11 × 114 / 9856 = 11 × 896 |
| Numbers divisible by 11 | **176 of 176 (100%)** |
| For comparison: four-digit multiples of 11 | 819 of 9000 (9.1%) |
| Identity `1000s + 100(s+a) + 10(s+a+b) + (s+b) = 11(101s + 10a + b)` | checked on 132 651 triples `(s, a, b) ∈ [−25, 25]³`, 0 mismatches |

**Sharpness.** The statement is about the nine digit keys `1…9`. The `0` key is
not on the affine lattice (`digit(0,0) = 0`, but `3·0 + 0 − 2 = −2`), and indeed
the 42 four-digit values obtained from parallelograms that use `0` include none
that is divisible by 11 — e.g. `1520 = 11 × 138 + 2`. See section 7 of the report.

## Repository contents

| File | What it is |
| --- | --- |
| [`calculator-parallelogram.pdf`](calculator-parallelogram.pdf) | The full report, 7 pages: claim and figure, the affine-lattice lemmas, two proofs, the worked example, the Lean formalization with its axiom audit, the verification tables, the `0`-key boundary, and an appendix listing all 22 parallelograms with their 8 numbers each. |
| [`calculator-parallelogram.tex`](calculator-parallelogram.tex) | LaTeX source of the report (TikZ figure, no external images). |
| [`Parallelogram.lean`](Parallelogram.lean) | Lean 4 proof, core library only, no Mathlib. |
| [`verify.py`](verify.py) | Independent brute-force enumeration with assertions; prints the tables of section 6 of the report. |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lake project; toolchain pinned to `leanprover/lean4:v4.36.0`, no dependencies. |

## The Lean formalization

`Parallelogram.lean` proves, in namespace `Keypad`:

| Theorem | Statement |
| --- | --- |
| `digit_opposite_sum` | The parallelogram condition on the coordinates implies `d₁ + d₃ = d₂ + d₄` for the digits. This is the only place the affine structure `3r + c` is used. |
| `dvd_eleven_of_opposite_digits` | If `d₁ + d₃ = d₂ + d₄` then `11 ∣ 1000d₁ + 100d₂ + 10d₃ + d₄`, with the explicit witness `91d₁ + 9d₂ + d₃`. |
| `eleven_of_opposite_digits` | The same fact as an identity, `N = 11 · (91d₁ + 9d₂ + d₃)`. |
| `dvd_eleven_of_sides` | The side-length form: `11 ∣ 1000s + 100(s+a) + 10(s+a+b) + (s+b)` for all `s, a, b`. |
| `parallelogram_dvd_eleven` | **Main theorem.** Any four keypad keys with `p₁ + p₃ = p₂ + p₄`, tapped in that order, give a multiple of 11. |
| `parallelogram_identity` | The same theorem displaying the quotient. |
| `each_shape_dvd` | The main theorem applied to an enumerated `Shape` structure. |
| `every_keypad_parallelogram` | Machine check over all 9⁴ ordered quadruples: every parallelogram among the nine digit keys yields a multiple of 11 (`native_decide`). |

The arithmetic cores are proved with `omega`; the exhaustive check uses
`native_decide`. An axiom audit (`#print axioms`) shows the mathematical theorems
depend only on `[propext, Quot.sound]` — no Mathlib, no `sorry`, no extra axioms.
`#eval`s at the end of the file print the counts quoted above.

## Reproducing

Prerequisites: [elan](https://github.com/leanprover/elan) (the toolchain is pinned
by `lean-toolchain`), Python 3 (standard library only), and optionally a LaTeX
installation with TikZ.

```bash
# 1. The Lean proof.  Expected: "Build completed successfully".
export PATH="$HOME/.elan/bin:$PATH"
lake build

# 2. The independent Python enumeration.  Every assertion must hold; the output
#    reproduces the result tables.
python3 verify.py

# 3. The report (optional).  Any LaTeX engine with TikZ works; tectonic is used here.
tectonic -X compile calculator-parallelogram.tex      # or: pdflatex calculator-parallelogram.tex (twice)
```

To inspect the axioms of the main results, run a file that imports the library:

```lean
import Parallelogram
#print axioms Keypad.parallelogram_dvd_eleven
#print axioms Keypad.every_keypad_parallelogram
```

and check it with `lake env lean file.lean`.

