#!/usr/bin/env python3
"""Independent brute-force companion to Parallelogram.lean.

Keypad layout (row counted from the bottom, column from the left):

        7 8 9      r = 3
        4 5 6      r = 2
        1 2 3      r = 1

so the digit on key (r, c) is  digit(r, c) = 3r + c - 2.

A cyclic quadruple of keys A B C D is a parallelogram iff its diagonals bisect
each other:  A + C = B + D.  Given A, B, C the fourth corner is forced,
D = A + C - B, and the tapped digits are simply the digits of A, B, C, D in
that order.
"""

from itertools import product

DIGIT_KEYS = {(r, c): 3 * r + c - 2 for r in (1, 2, 3) for c in (0, 1, 2)}


def cross(p1, p2, p4):
    """Twice the signed area of triangle p1 p2 p4 (zero iff collinear)."""
    return (p2[0] - p1[0]) * (p4[1] - p1[1]) - (p2[1] - p1[1]) * (p4[0] - p1[0])


def quadruples(keys):
    """All (A, B, C, D) with A, B, C, D in `keys` and A + C = B + D."""
    out = []
    for a, b, c in product(keys, repeat=3):
        d = (a[0] + c[0] - b[0], a[1] + c[1] - b[1])
        if d in keys:
            out.append((a, b, c, d))
    return out


def genuine(quads):
    """Keep only real parallelograms: four distinct corners, non-zero area."""
    return [q for q in quads
            if len(set(q)) == 4 and cross(q[0], q[1], q[3]) != 0]


def digits_of(quad, keys):
    return tuple(keys[p] for p in quad)


def value_of(digits):
    return 1000 * digits[0] + 100 * digits[1] + 10 * digits[2] + digits[3]


def rule(title):
    print()
    print(title)
    print("-" * len(title))


def main():
    print("keypad (rows from the bottom):")
    for r in (3, 2, 1):
        print("   " + " ".join(str(DIGIT_KEYS[(r, c)]) for c in (0, 1, 2)))

    allq = quadruples(DIGIT_KEYS)
    good = genuine(allq)

    rule("1. every parallelogram on the nine digit keys")
    numbers = {}
    for q in good:
        d = digits_of(q, DIGIT_KEYS)
        n = value_of(d)
        q11, rem = divmod(n, 11)
        assert rem == 0, (d, n)
        assert q11 == 91 * d[0] + 9 * d[1] + d[2], (d, q11)   # Lean's witness
        numbers.setdefault(d, (n, q11, q))
    vertex_sets = {frozenset(q) for q in good}
    print(f"ordered quadruples with A + C = B + D   : {len(allq)}")
    print(f"  of which genuine parallelograms      : {len(good)}")
    print(f"  distinct vertex sets (shapes)        : {len(vertex_sets)} "
          f"({len(good) // len(vertex_sets)} traversal orders per shape)")
    print(f"distinct four-digit numbers produced   : {len(numbers)}")
    print(f"all of them divisible by 11            : "
          f"{all(n % 11 == 0 for n, _, _ in numbers.values())}")
    print(f"quotient is always 91*d1 + 9*d2 + d3    : yes (checked above)")
    print()
    print("  smallest numbers, then the largest:")
    ordered = sorted(numbers.values())
    for n, q11, _ in ordered[:6] + ordered[-3:]:
        print(f"    {n:<6} = 11 x {q11}")
    print(f"    ... {len(ordered) - 9} more ..." if len(ordered) > 9 else "")

    rule("2. the picture from the question: 1 -> 4 -> 8 -> 5")
    pic = ((1, 0), (2, 0), (3, 1), (2, 1))
    assert pic[0][0] + pic[2][0] == pic[1][0] + pic[3][0] == 4
    assert pic[0][1] + pic[2][1] == pic[1][1] + pic[3][1] == 1
    d = digits_of(pic, DIGIT_KEYS)
    n = value_of(d)
    print(f"digits {d} -> {n} = 11 x {n // 11},  and 91*{d[0]} + 9*{d[1]} + {d[2]}"
          f" = {91 * d[0] + 9 * d[1] + d[2]}")
    assert n == 1485 and n // 11 == 135

    rule("3. one side step by a, the other by b: the general identity")
    bad = 0
    for s, a, b in product(range(-25, 26), repeat=3):
        if 1000 * s + 100 * (s + a) + 10 * (s + a + b) + (s + b) != 11 * (101 * s + 10 * a + b):
            bad += 1
    print(f"(s, a, b) in [-25, 25]^3 : {51 ** 3} triples, mismatches: {bad}")
    print("1000s + 100(s+a) + 10(s+a+b) + (s+b) = 11(101s + 10a + b)")
    assert bad == 0

    rule("4. how special is the parallelogram condition?")
    total = sum(1 for n in range(1000, 10000) if n % 11 == 0)
    print(f"four-digit numbers divisible by 11          : {total} of 9000 "
          f"({100 * total / 9000:.1f}%)")
    print(f"four-digit strings from genuine parallelograms: {len(numbers)}, "
          f"100.0% divisible by 11")

    rule("5. boundary: the key 0 is not part of the statement")
    keys0 = dict(DIGIT_KEYS)
    keys0[(0, 0)] = 0
    zero = []
    for q in genuine(quadruples(keys0)):
        if (0, 0) in q:
            d = digits_of(q, keys0)
            n = value_of(d)
            zero.append((d, n, n % 11))
    four = [z for z in zero if z[0][0] != 0]
    print(f"parallelograms using the 0 key: {len(zero)} "
          f"({len(four)} of them give a four-digit value)")
    for d, n, rem in four[:4]:
        print(f"    taps {d} -> {n} = 11 x {n // 11} + {rem}   (NOT divisible)")
    print(f"    ... {len(four) - 4} more like these ..." if len(four) > 4 else "")
    print(f"divisible by 11 among all of them: "
          f"{sum(1 for _, _, rem in zero if rem == 0)}")
    print("Reason: the 0 key carries digit 0, but 3*0 + 0 - 2 = -2, so the affine")
    print("structure the proof relies on breaks there.  Hence the statement is")
    print("about the nine digit keys 1..9 (four-digit numbers), and it is sharp.")


if __name__ == "__main__":
    main()
