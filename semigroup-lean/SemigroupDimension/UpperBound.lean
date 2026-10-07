import SemigroupDimension.PowerCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace SemigroupDimension

theorem tail_inSemigroup (n : ℕ) (hn : 14 ≤ n) : InSemigroup n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 19
    · interval_cases n
      · exact ⟨0, 2, 0, 0, rfl⟩
      · exact ⟨3, 0, 0, 0, rfl⟩
      · exact ⟨0, 0, 1, 0, rfl⟩
      · exact ⟨2, 1, 0, 0, rfl⟩
      · exact ⟨0, 0, 0, 1, rfl⟩
    · have hlt : n - 5 < n := by omega
      have htail : 14 ≤ n - 5 := by omega
      have heq : n = (n - 5) + 5 := by omega
      rw [heq]
      exact inSemigroup_add (ih (n - 5) hlt htail) inSemigroup_five

theorem inSemigroup_iff (n : ℕ) :
    InSemigroup n ↔ n = 0 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 12 ∨ 14 ≤ n := by
  constructor
  · rintro ⟨a, b, c, d, h⟩
    by_cases hn : 14 ≤ n
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))
    · have hc : c = 0 := by omega
      have hd : d = 0 := by omega
      have ha : a ≤ 2 := by omega
      have hb : b ≤ 1 := by omega
      subst c d
      interval_cases a <;> interval_cases b <;> omega
  · rintro (rfl | rfl | rfl | rfl | rfl | h)
    · exact inSemigroup_zero
    · exact inSemigroup_five
    · exact inSemigroup_seven
    · exact ⟨2, 0, 0, 0, rfl⟩
    · exact ⟨1, 1, 0, 0, rfl⟩
    · exact tail_inSemigroup n h

theorem not_inSemigroup_thirteen : ¬ InSemigroup 13 := by
  rw [inSemigroup_iff]
  omega

theorem integral_pow_ten : IntegralMatrix (witness ^ 10) := by
  simpa only [← pow_add] using integralMatrix_mul integral_pow_5 integral_pow_5

theorem integral_pow_twelve : IntegralMatrix (witness ^ 12) := by
  simpa only [← pow_add] using integralMatrix_mul integral_pow_5 integral_pow_7

theorem tail_integral (n : ℕ) (hn : 14 ≤ n) : IntegralMatrix (witness ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 19
    · interval_cases n
      · exact integral_pow_14
      · exact integral_pow_15
      · exact integral_pow_16
      · exact integral_pow_17
      · exact integral_pow_18
    · have hlt : n - 5 < n := by omega
      have htail : 14 ≤ n - 5 := by omega
      rw [show n = (n - 5) + 5 by omega, pow_add]
      exact integralMatrix_mul (ih (n - 5) hlt htail) integral_pow_5

theorem nonintegral_small_gaps (n : ℕ)
    (hg : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨
      n = 9 ∨ n = 11 ∨ n = 13) : ¬ IntegralMatrix (witness ^ n) := by
  rintro h
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply nonintegral_pow_11
    simpa only [← pow_add] using integralMatrix_mul h integral_pow_ten
  · apply nonintegral_pow_9
    simpa only [← pow_add] using integralMatrix_mul h integral_pow_7
  · apply nonintegral_pow_13
    simpa only [← pow_add] using integralMatrix_mul h integral_pow_ten
  · apply nonintegral_pow_9
    simpa only [← pow_add] using integralMatrix_mul h integral_pow_5
  · apply nonintegral_pow_11
    simpa only [← pow_add] using integralMatrix_mul h integral_pow_5
  · apply nonintegral_pow_13
    simpa only [← pow_add] using integralMatrix_mul h integral_pow_5
  · exact nonintegral_pow_9 h
  · exact nonintegral_pow_11 h
  · exact nonintegral_pow_13 h

/-- The explicit matrix has exactly the requested exponent semigroup,
    for every natural number, without a bound on the exponent. -/
theorem witness_realizes : Realizes witness := by
  intro n
  rw [inSemigroup_iff]
  constructor
  · intro h
    by_contra hbad
    have hg : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨
        n = 9 ∨ n = 11 ∨ n = 13 := by omega
    exact nonintegral_small_gaps n hg h
  · rintro (rfl | rfl | rfl | rfl | rfl | h)
    · simpa using integralMatrix_one 3
    · exact integral_pow_5
    · exact integral_pow_7
    · exact integral_pow_ten
    · exact integral_pow_twelve
    · exact tail_integral n h

theorem dimension_at_most_three : Realizable 3 := ⟨witness, witness_realizes⟩

end SemigroupDimension
