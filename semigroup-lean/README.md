# Matrix dimension of ⟨5,7,16,18⟩

This project proves in Lean that the matrix dimension is exactly **3**.
It includes the construction, its correctness for every natural exponent,
and an independent proof excluding dimensions 0, 1, and 2.

The semigroup is defined by its generators, rather than by a finite list:

```lean
def InSemigroup (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, n = 5 * a + 7 * b + 16 * c + 18 * d
```

Matrices are Mathlib matrices over `ℚ`. An integral matrix belongs to the
image of the entrywise cast from matrices over `ℤ`. A matrix realizes the
semigroup if its nth power is integral exactly when n belongs to the semigroup,
for every `n : ℕ`. The matrix dimension is the least realizable dimension.

The final statements are:

```lean
theorem hasMatricialDimension_three : HasMatricialDimension 3
theorem matricial_dimension_eq_three : matricialDimension = 3
```

## Construction and upper bound

The witness is

```lean
def witness : QMatrix 3 :=
  !![0, 0, -357276958458978899;
    1 / 34522712143931, 0, -833361690 / 1771561;
    0, 214358881, -11]
```

`PowerCertificates.lean` supplies exact rational matrices for powers 0 through
18. Lean proves each successive multiplication and hence that these are the
actual matrix powers. The arithmetic uses `norm_num`, which produces proofs
checked by Lean's kernel. The certificates are data, not assumed equalities.

Lean verifies that powers 5, 7, and 14 through 18 are integral, and that powers
9, 11, and 13 are not integral. Multiplicative closure proves integrality for
all exponents at least 14 by induction, stepping by 5. The other gaps are
excluded by adding known integral exponents to reach 9, 11, or 13. In parallel,
Lean proves that the generated semigroup is exactly
`{0, 5, 7, 10, 12} ∪ {n | 14 ≤ n}`. Thus `witness_realizes` applies to every
natural exponent; it is not just a bounded computation.

## Lower bound

For every rational 2×2 matrix M, Lean proves that integral fifth and seventh
powers force the thirteenth power to be integral. First, integrality of the
fifth power forces both the determinant d and trace t to be integers. The
determinant follows from integrality of d⁵. The trace follows from the monic
polynomial

`X⁵ − 5dX³ + 5d²X − trace(M⁵)`.

Cayley–Hamilton and an explicit recurrence then prove

`M¹³ = P(t,d) M⁵ + Q(t,d) M⁷ + R(t,d) I`,

where

```text
P(t,d) = d⁴ − 18d³t² + 7d²t⁴ + 6dt⁶ − 2t⁸
Q(t,d) = t⁴(−8d + 3t²)
R(t,d) = 4d⁶t + 2d⁵t³.
```

These are integer coefficients. Since 5 and 7 belong to the requested
semigroup but 13 does not, a 2×2 realization is impossible. Dimensions 0 and
1 are also excluded directly. No published lower-bound theorem is assumed.

## Reproduce verification

Install Lean through elan, then run these commands in the extracted project:

```sh
lake update
lake exe cache get
lake build SemigroupDimension
lake env lean SemigroupDimensionVerified.lean
```

The project pins Lean **4.19.0** and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The lockfile also pins dependencies.

`SemigroupDimensionVerified.lean` contains the entire proof in one file and
imports only Mathlib. The modular version is under `SemigroupDimension/`, with
the final theorem in `SemigroupDimension.lean`.

Both verification commands were executed successfully. Their actual output
is retained in `verification.log`. The four axiom audits list only:

```text
[propext, Classical.choice, Quot.sound]
```

There are no admitted proofs, additional axioms, or uses of `native_decide`.
The official Lean executable was used. This execution environment required a
small external path-discovery compatibility shim to map `/proc/<own pid>/exe`
to `/proc/self/exe`; it changes neither Lean's code nor its kernel. That shim
is not required in an ordinary Lean installation.

`source-sha256.txt` records the exact source and configuration bytes checked.
