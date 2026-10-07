import SemigroupDimension.UpperBound

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace SemigroupDimension

theorem integralMatrix_entry_integer {n : ℕ} {M : QMatrix n}
    (hM : IntegralMatrix M) (i j : Fin n) : ∃ z : ℤ, (z : ℚ) = M i j :=
  ⟨(M i j).num, Rat.coe_int_num_of_den_eq_one ((integralMatrix_iff_den M).mp hM i j)⟩

theorem rational_integer_of_fifth_power (q : ℚ)
    (h : ∃ z : ℤ, (z : ℚ) = q ^ 5) : ∃ z : ℤ, (z : ℚ) = q := by
  rcases h with ⟨z, hz⟩
  have hp : IsIntegral ℤ (q ^ 5) := by
    rw [← hz]
    exact isIntegral_algebraMap
  have hq : IsIntegral ℤ q := IsIntegral.of_pow (by norm_num) hp
  simpa using (IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) hq)

theorem integralMatrix_trace_integer {n : ℕ} {M : QMatrix n}
    (hM : IntegralMatrix M) : ∃ z : ℤ, (z : ℚ) = Matrix.trace M := by
  rcases hM with ⟨N, rfl⟩
  refine ⟨Matrix.trace N, ?_⟩
  simpa [castMatrix] using AddMonoidHom.map_trace (Int.castRingHom ℚ) N

theorem integralMatrix_det_integer {n : ℕ} {M : QMatrix n}
    (hM : IntegralMatrix M) : ∃ z : ℤ, (z : ℚ) = Matrix.det M := by
  rcases hM with ⟨N, rfl⟩
  refine ⟨Matrix.det N, ?_⟩
  simpa [castMatrix] using (Int.castRingHom ℚ).map_det N

theorem two_by_two_cayley_hamilton (M : QMatrix 2) :
    M ^ 2 = Matrix.trace M • M - Matrix.det M • (1 : QMatrix 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.smul_apply] <;> ring

def lucas (t d : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * lucas t d (n + 1) - d * lucas t d n

theorem matrix_power_lucas (M : QMatrix 2) (n : ℕ) :
    M ^ (n + 1) = lucas (Matrix.trace M) (Matrix.det M) (n + 1) • M -
      (Matrix.det M * lucas (Matrix.trace M) (Matrix.det M) n) • (1 : QMatrix 2) := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    have hm : M * M = Matrix.trace M • M - Matrix.det M • (1 : QMatrix 2) := by
      simpa only [pow_two] using two_by_two_cayley_hamilton M
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hm]
    simp only [smul_sub, smul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, lucas]
    ring

theorem two_by_two_trace_fifth (M : QMatrix 2) :
    Matrix.trace (M ^ 5) = (Matrix.trace M) ^ 5 -
      5 * Matrix.det M * (Matrix.trace M) ^ 3 +
      5 * (Matrix.det M) ^ 2 * Matrix.trace M := by
  rw [show M ^ 5 = _ from matrix_power_lucas M 4]
  simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, lucas]
  ring

/-- The trace and determinant are integers whenever the fifth power is an integer matrix.
    The trace argument uses the monic rational-root theorem. -/
theorem two_by_two_trace_det_integer (M : QMatrix 2)
    (h5 : IntegralMatrix (M ^ 5)) :
    (∃ t : ℤ, (t : ℚ) = Matrix.trace M) ∧
    (∃ d : ℤ, (d : ℚ) = Matrix.det M) := by
  have hd5 := integralMatrix_det_integer h5
  rw [Matrix.det_pow] at hd5
  obtain ⟨d, hd⟩ := rational_integer_of_fifth_power (Matrix.det M) hd5
  obtain ⟨z, hz⟩ := integralMatrix_trace_integer h5
  let f : Polynomial ℤ := Polynomial.X ^ 5 -
    Polynomial.C (5 * d) * Polynomial.X ^ 3 +
    Polynomial.C (5 * d ^ 2) * Polynomial.X - Polynomial.C z
  have hf : f.Monic := by
    dsimp [f]
    monicity!
  have hroot : Polynomial.aeval (Matrix.trace M) f = 0 := by
    simp only [f, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X]
    change Matrix.trace M ^ 5 - 5 * (d : ℚ) * Matrix.trace M ^ 3 +
      5 * (d : ℚ) ^ 2 * Matrix.trace M - (z : ℚ) = 0
    rw [hd]
    rw [two_by_two_trace_fifth] at hz
    exact sub_eq_zero.mpr hz.symm
  have ht : IsIntegral ℤ (Matrix.trace M) := ⟨f, hf, hroot⟩
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) ht
  exact ⟨⟨t, by simpa using ht⟩, ⟨d, hd⟩⟩

def lowerP (t d : ℚ) : ℚ :=
  d ^ 4 - 18 * d ^ 3 * t ^ 2 + 7 * d ^ 2 * t ^ 4 + 6 * d * t ^ 6 - 2 * t ^ 8

def lowerQ (t d : ℚ) : ℚ := t ^ 4 * (-8 * d + 3 * t ^ 2)

def lowerR (t d : ℚ) : ℚ := 4 * d ^ 6 * t + 2 * d ^ 5 * t ^ 3

/-- An exact identity valid for every rational 2×2 matrix. -/
theorem two_by_two_thirteenth_identity (M : QMatrix 2) :
    M ^ 13 = lowerP (Matrix.trace M) (Matrix.det M) • (M ^ 5) +
      lowerQ (Matrix.trace M) (Matrix.det M) • (M ^ 7) +
      lowerR (Matrix.trace M) (Matrix.det M) • (1 : QMatrix 2) := by
  rw [show M ^ 13 = _ from matrix_power_lucas M 12,
    show M ^ 5 = _ from matrix_power_lucas M 4,
    show M ^ 7 = _ from matrix_power_lucas M 6]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [lowerP, lowerQ, lowerR, lucas]
  ring

/-- Integral fifth and seventh powers of a rational 2×2 matrix force its
    thirteenth power to be integral. No published theorem is assumed. -/
theorem two_by_two_thirteenth_integral (M : QMatrix 2)
    (h5 : IntegralMatrix (M ^ 5)) (h7 : IntegralMatrix (M ^ 7)) :
    IntegralMatrix (M ^ 13) := by
  obtain ⟨⟨t, ht⟩, ⟨d, hd⟩⟩ := two_by_two_trace_det_integer M h5
  let P : ℤ := d ^ 4 - 18 * d ^ 3 * t ^ 2 + 7 * d ^ 2 * t ^ 4 +
    6 * d * t ^ 6 - 2 * t ^ 8
  let Q : ℤ := t ^ 4 * (-8 * d + 3 * t ^ 2)
  let R : ℤ := 4 * d ^ 6 * t + 2 * d ^ 5 * t ^ 3
  have hp : lowerP (Matrix.trace M) (Matrix.det M) = (P : ℚ) := by
    rw [← ht, ← hd]
    simp [lowerP, P]
  have hq : lowerQ (Matrix.trace M) (Matrix.det M) = (Q : ℚ) := by
    rw [← ht, ← hd]
    simp [lowerQ, Q]
  have hr : lowerR (Matrix.trace M) (Matrix.det M) = (R : ℚ) := by
    rw [← ht, ← hd]
    simp [lowerR, R]
  rw [two_by_two_thirteenth_identity M, hp, hq, hr]
  exact integralMatrix_add
    (integralMatrix_add (integralMatrix_int_smul P h5) (integralMatrix_int_smul Q h7))
    (integralMatrix_int_smul R (integralMatrix_one 2))

theorem not_realizable_two : ¬ Realizable 2 := by
  rintro ⟨M, hM⟩
  have h5 := (hM 5).mpr inSemigroup_five
  have h7 := (hM 7).mpr inSemigroup_seven
  exact not_inSemigroup_thirteen ((hM 13).mp (two_by_two_thirteenth_integral M h5 h7))

theorem fin_one_power (M : QMatrix 1) (n : ℕ) : (M ^ n) 0 0 = (M 0 0) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, ih]

theorem not_realizable_one : ¬ Realizable 1 := by
  rintro ⟨M, hM⟩
  obtain ⟨z, hz⟩ := integralMatrix_entry_integer ((hM 5).mpr inSemigroup_five) 0 0
  rw [fin_one_power] at hz
  obtain ⟨q, hq⟩ := rational_integer_of_fifth_power (M 0 0) ⟨z, hz⟩
  have hi : IntegralMatrix M := by
    rw [integralMatrix_iff_den]
    intro i j
    fin_cases i
    fin_cases j
    change (M 0 0).den = 1
    rw [← hq]
    exact Rat.den_intCast q
  have h1 : InSemigroup 1 := (hM 1).mp (by simpa using hi)
  rw [inSemigroup_iff] at h1
  omega

theorem not_realizable_zero : ¬ Realizable 0 := by
  rintro ⟨M, hM⟩
  have hi : IntegralMatrix (M ^ 1) := by
    rw [integralMatrix_iff_den]
    intro i
    exact Fin.elim0 i
  have h1 := (hM 1).mp hi
  rw [inSemigroup_iff] at h1
  omega

theorem dimension_at_least_three (k : ℕ) (hk : Realizable k) : 3 ≤ k := by
  by_contra h
  have hlt : k < 3 := by omega
  interval_cases k
  · exact not_realizable_zero hk
  · exact not_realizable_one hk
  · exact not_realizable_two hk

end SemigroupDimension
