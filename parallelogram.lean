/-
  If you punch a four-digit number by "drawing a parallelogram" on a
  calculator keypad, the result is always a multiple of 11.

  This file proves that in Lean 4 (core library only, no Mathlib).

  ----------------------------------------------------------------------------
  The keypad
  ----------------------------------------------------------------------------

  Number the rows from the bottom (1, 2, 3) and the columns from the left
  (0, 1, 2).  The digit keys carry

        7 8 9      row 3
        4 5 6      row 2
        1 2 3      row 1

  so the digit on key (r, c) is

        digit r c = 3 * r + c - 2.

  This map is *affine* in (r, c): one step right adds 1, one step up adds 3,
  hence moving by a fixed vector in the grid changes the digit by the same
  amount no matter where you start.

  ----------------------------------------------------------------------------
  The parallelogram
  ----------------------------------------------------------------------------

  Four corner keys `p₁ p₂ p₃ p₄`, listed in the order you tap them, form a
  parallelogram exactly when the diagonals bisect each other:

        p₁ + p₃ = p₂ + p₄          (coordinate-wise),

  i.e. the side from p₁ equals the side from p₄, and likewise for the other
  pair.  Since `digit` is affine, the *digits* obey the same relation:

        d₁ + d₃ = d₂ + d₄          (opposite digits have equal sums).

  ----------------------------------------------------------------------------
  Why that forces 11 | d₁d₂d₃d₄
  ----------------------------------------------------------------------------

  Option A (the textbook test).  Since 10 ≡ -1, 100 ≡ 1, 1000 ≡ -1 (mod 11),

        N = 1000 d₁ + 100 d₂ + 10 d₃ + d₄ ≡ -(d₁ - d₂ + d₃ - d₄)   (mod 11),

  and the alternating sum d₁ - d₂ + d₃ - d₄ = (d₁ + d₃) - (d₂ + d₄) is 0 for a
  parallelogram digit string, so N ≡ 0.

  Option B (one algebraic identity, which is what Lean checks below).
  Substituting d₄ = d₁ + d₃ - d₂,

        1000 d₁ + 100 d₂ + 10 d₃ + d₄
      = 1000 d₁ + 100 d₂ + 10 d₃ + d₁ + d₃ - d₂
      = 1001 d₁ + 99 d₂ + 11 d₃
      = 11 * (91 d₁ + 9 d₂ + d₃).

  For the picture in the question, 1 → 4 → 8 → 5, the bracket is
  91·1 + 9·4 + 8 = 135: exactly the "135" the calculator displays.

  Note what the proof does *not* use: which two step vectors were chosen.
  Any side lengths, any orientation, and any of the four cyclic orders (or the
  reverse order) give the same conclusion.
-/

local notation "ℤ" => Int

namespace Keypad

/-! ## The digit carried by a key -/

/-- The digit printed on the key in row `r` (counted from the bottom) and
column `c` (counted from the left), for `1 ≤ r ≤ 3` and `0 ≤ c ≤ 2`. -/
def digit (r c : ℤ) : ℤ := 3 * r + c - 2

/-- The nine digit keys: rows 1..3, columns 0..2. -/
def OnPad (r c : ℤ) : Prop := 1 ≤ r ∧ r ≤ 3 ∧ 0 ≤ c ∧ c ≤ 2

/-- Sanity check: the affine formula really prints the keypad `1 … 9`. -/
example :
    (([(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)] :
        List (ℤ × ℤ)).map fun p => digit p.1 p.2) = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  decide

/-! ## The arithmetic core

Divisibility by 11 only sees the alternating digit sum.  A parallelogram
guarantees `d₁ + d₃ = d₂ + d₄`, i.e. that the alternating sum vanishes. -/

/-- **Master lemma.**  If the four digits of a four-digit number satisfy the
parallelogram relation `d₁ + d₃ = d₂ + d₄`, then the number is a multiple of
11.  The explicit quotient is `91 d₁ + 9 d₂ + d₃`. -/
theorem dvd_eleven_of_opposite_digits (d₁ d₂ d₃ d₄ : ℤ) (h : d₁ + d₃ = d₂ + d₄) :
    (11 : ℤ) ∣ 1000 * d₁ + 100 * d₂ + 10 * d₃ + d₄ := by
  refine ⟨91 * d₁ + 9 * d₂ + d₃, by omega⟩

/-- The same divisibility, written as an identity: the quotient is
`91 d₁ + 9 d₂ + d₃`. -/
theorem eleven_of_opposite_digits (d₁ d₂ d₃ d₄ : ℤ) (h : d₁ + d₃ = d₂ + d₄) :
    1000 * d₁ + 100 * d₂ + 10 * d₃ + d₄ = 11 * (91 * d₁ + 9 * d₂ + d₃) := by
  omega

/-- The same statement in "side length" form: a parallelogram whose sides
change the digit by `a` and by `b` produces the digits `s, s+a, s+a+b, s+b`
and hence the number `11 * (101 s + 10 a + b)`, for *every* choice of
`s`, `a`, `b`. -/
theorem dvd_eleven_of_sides (s a b : ℤ) :
    (11 : ℤ) ∣ 1000 * s + 100 * (s + a) + 10 * (s + a + b) + (s + b) :=
  ⟨101 * s + 10 * a + b, by omega⟩

/-! ## From geometry to arithmetic -/

/-- Parallelogram `p₁ p₂ p₃ p₄` ⇒ opposite digits sum equally.  This is the
only place where the affine structure `3 r + c` of the keypad is used. -/
theorem digit_opposite_sum (r₁ c₁ r₂ c₂ r₃ c₃ r₄ c₄ : ℤ)
    (hrows : r₁ + r₃ = r₂ + r₄) (hcols : c₁ + c₃ = c₂ + c₄) :
    digit r₁ c₁ + digit r₃ c₃ = digit r₂ c₂ + digit r₄ c₄ := by
  simp only [digit]
  omega

/-- **Main theorem.**  Take any four keys `p₁ p₂ p₃ p₄` of the keypad whose
coordinates satisfy the parallelogram condition `p₁ + p₃ = p₂ + p₄`
(diagonals bisect each other), and type their digits in that order: the
four-digit number you get is always a multiple of 11. -/
theorem parallelogram_dvd_eleven (r₁ c₁ r₂ c₂ r₃ c₃ r₄ c₄ : ℤ)
    (hrows : r₁ + r₃ = r₂ + r₄) (hcols : c₁ + c₃ = c₂ + c₄) :
    (11 : ℤ) ∣ 1000 * digit r₁ c₁ + 100 * digit r₂ c₂
               + 10 * digit r₃ c₃ + digit r₄ c₄ :=
  dvd_eleven_of_opposite_digits _ _ _ _
    (digit_opposite_sum _ _ _ _ _ _ _ _ hrows hcols)

/-- The same statement in identity form, displaying the quotient: a
parallelogram trace on the keypad produces
`11 * (91 d₁ + 9 d₂ + d₃)`. -/
theorem parallelogram_identity (r₁ c₁ r₂ c₂ r₃ c₃ r₄ c₄ : ℤ)
    (hrows : r₁ + r₃ = r₂ + r₄) (hcols : c₁ + c₃ = c₂ + c₄) :
    1000 * digit r₁ c₁ + 100 * digit r₂ c₂ + 10 * digit r₃ c₃ + digit r₄ c₄
      = 11 * (91 * digit r₁ c₁ + 9 * digit r₂ c₂ + digit r₃ c₃) := by
  have h := digit_opposite_sum r₁ c₁ r₂ c₂ r₃ c₃ r₄ c₄ hrows hcols
  omega

/-! ## The example in the picture: 1 → 4 → 8 → 5 -/

/-- Keys `1, 4, 8, 5` are `(1,0)`, `(2,0)`, `(3,1)`, `(2,1)`, and those are a
parallelogram: `1 + 3 = 2 + 2` rows and `0 + 1 = 0 + 1` columns. -/
example : (1 + 3 : ℤ) = 2 + 2 ∧ (0 + 1 : ℤ) = 0 + 1 := by decide

/-- Hence `1485` is a multiple of 11, by the main theorem. -/
example : (11 : ℤ) ∣ 1000 * digit 1 0 + 100 * digit 2 0 + 10 * digit 3 1 + digit 2 1 :=
  parallelogram_dvd_eleven 1 0 2 0 3 1 2 1 (by decide) (by decide)

/-- And the quotient is `135`, exactly as the calculator displays. -/
example : 1000 * digit 1 0 + 100 * digit 2 0 + 10 * digit 3 1 + digit 2 1 = 11 * 135 := by
  decide

/-! ## An exhaustive machine check over the whole keypad

The theorems above are the proof.  The computation below is its belt-and-
braces counterpart: enumerate *every* ordered quadruple of digit keys that
closes up as a parallelogram and check the conclusion numerically. -/

/-- The nine digit keys as coordinate pairs. -/
def keyPositions : List (ℤ × ℤ) :=
  [(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)]

/-- A cyclic quadruple of key positions. -/
structure Shape where
  p₁ : ℤ × ℤ
  p₂ : ℤ × ℤ
  p₃ : ℤ × ℤ
  p₄ : ℤ × ℤ

/-- `p₁ p₂ p₃ p₄` closes up as a parallelogram: its diagonals bisect each
other, i.e. opposite corners are symmetric about `(p₁+p₃)/2 = (p₂+p₄)/2`. -/
def Shape.IsPara (s : Shape) : Prop :=
  s.p₁.1 + s.p₃.1 = s.p₂.1 + s.p₄.1 ∧ s.p₁.2 + s.p₃.2 = s.p₂.2 + s.p₄.2

instance (s : Shape) : Decidable s.IsPara := by
  unfold Shape.IsPara
  infer_instance

/-- The four-digit number typed when tapping the keys of `s` in order. -/
def Shape.num (s : Shape) : ℤ :=
  1000 * digit s.p₁.1 s.p₁.2 + 100 * digit s.p₂.1 s.p₂.2
    + 10 * digit s.p₃.1 s.p₃.2 + digit s.p₄.1 s.p₄.2

/-- All 9⁴ ordered quadruples of digit keys. -/
def shapes : List Shape :=
  keyPositions.flatMap fun p₁ =>
  keyPositions.flatMap fun p₂ =>
  keyPositions.flatMap fun p₃ =>
  keyPositions.map fun p₄ => ⟨p₁, p₂, p₃, p₄⟩

/-- **Every** parallelogram on the keypad yields a multiple of 11 — the main
theorem applied to each enumerated shape. -/
theorem each_shape_dvd (s : Shape) (hs : s.IsPara) : (11 : ℤ) ∣ s.num :=
  parallelogram_dvd_eleven s.p₁.1 s.p₁.2 s.p₂.1 s.p₂.2 s.p₃.1 s.p₃.2 s.p₄.1 s.p₄.2
    hs.1 hs.2

/-- Closed computation over the whole pad: every parallelogram among the nine
digit keys, in every cyclic order, gives a number divisible by 11. -/
theorem every_keypad_parallelogram :
    (shapes.filter (fun s => decide s.IsPara)).all
      (fun s => decide (s.num % 11 = 0)) = true := by
  native_decide

/-- A *genuine* parallelogram: four distinct corners enclosing non-zero area.
(The divisibility theorem does not need this, but the counts below are more
honest with it.) -/
def Shape.nondeg (s : Shape) : Bool :=
  decide (s.p₁ ≠ s.p₂ ∧ s.p₂ ≠ s.p₃ ∧ s.p₃ ≠ s.p₄ ∧ s.p₄ ≠ s.p₁ ∧
    (s.p₂.1 - s.p₁.1) * (s.p₄.2 - s.p₁.2) - (s.p₂.2 - s.p₁.2) * (s.p₄.1 - s.p₁.1) ≠ 0)

/- Informational: how many ordered quadruples of keys close up as a
parallelogram (`p₁ + p₃ = p₂ + p₄`), degenerate ones included? -/
#eval (shapes.filter (fun s => decide s.IsPara)).length

/- Informational: how many of those are genuine parallelograms? -/
#eval (shapes.filter (fun s => decide s.IsPara && s.nondeg)).length

/- Informational: the smallest distinct four-digit numbers produced. -/
#eval ((((shapes.filter (fun s => decide s.IsPara && s.nondeg)).map Shape.num).mergeSort
    (fun a b => decide (a ≤ b))).eraseDups).take 24

/- Informational: how many distinct four-digit numbers in total? -/
#eval ((((shapes.filter (fun s => decide s.IsPara && s.nondeg)).map Shape.num).mergeSort
    (fun a b => decide (a ≤ b))).eraseDups).length

end Keypad
