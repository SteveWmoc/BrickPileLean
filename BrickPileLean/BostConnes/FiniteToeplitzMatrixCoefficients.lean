import BrickPileLean.BostConnes.FiniteGibbsExpectation

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- A standard Toeplitz monomial acts on a basis vector in the range of its
adjoint index by cancelling that index and applying the left shift. -/
theorem toeplitzMonomial_basisVector_mul
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n q : finitePrimeSemigroup S) :
    toeplitzMonomial hS m n (basisVector S (n * q)) =
      basisVector S (m * q) := by
  unfold toeplitzMonomial
  change shiftOperator hS m
      (shiftAdjoint hS n (basisVector S (n * q))) =
    basisVector S (m * q)
  rw [shiftAdjoint_basisVector_mul, shiftOperator_basisVector]

/-- If the adjoint index does not divide the basis label, the standard
Toeplitz monomial kills that basis vector. -/
theorem toeplitzMonomial_basisVector_eq_zero_of_not_dvd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n k : finitePrimeSemigroup S) (hnk : ¬ n ∣ k) :
    toeplitzMonomial hS m n (basisVector S k) = 0 := by
  unfold toeplitzMonomial
  change shiftOperator hS m
      (shiftAdjoint hS n (basisVector S k)) = 0
  rw [shiftAdjoint_basisVector_eq_zero_of_not_dvd hS n k hnk]
  simp

/-- The coordinate of a canonical basis vector is the expected Kronecker
delta. -/
@[simp] theorem basisVector_apply
    {S : Finset ℕ} (n k : finitePrimeSemigroup S) :
    basisVector S n k = if n = k then 1 else 0 := by
  classical
  simp [basisVector, lp.single_apply, Pi.single_apply]

/-- A matrix coefficient of a standard Toeplitz monomial is nonzero exactly
when the input and output labels are obtained from a common residual factor. -/
theorem toeplitzMonomial_basisVector_apply_ne_zero_iff
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (r s n m : finitePrimeSemigroup S) :
    toeplitzMonomial hS r s (basisVector S n) m ≠ 0 ↔
      ∃ q : finitePrimeSemigroup S, n = s * q ∧ r * q = m := by
  constructor
  · intro h
    by_cases hdvd : s ∣ n
    · rcases hdvd with ⟨q, hq⟩
      have h' := h
      rw [hq, toeplitzMonomial_basisVector_mul hS r s q] at h'
      have hr : r * q = m := by
        simpa using h'
      exact ⟨q, hq, hr⟩
    · have hz :
          toeplitzMonomial hS r s (basisVector S n) m = 0 := by
        rw [toeplitzMonomial_basisVector_eq_zero_of_not_dvd
          hS r s n hdvd]
        rfl
      exact (h hz).elim
  · rintro ⟨q, hq, hr⟩
    rw [hq, toeplitzMonomial_basisVector_mul hS r s q]
    rw [hr]
    simp

/-- A nonzero matrix coefficient forces the adjoint index to divide the
input basis label. -/
theorem toeplitzMonomial_denominator_dvd_of_apply_ne_zero
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (r s n m : finitePrimeSemigroup S)
    (h : toeplitzMonomial hS r s (basisVector S n) m ≠ 0) :
    s ∣ n := by
  rcases (toeplitzMonomial_basisVector_apply_ne_zero_iff
    hS r s n m).1 h with ⟨q, hq, _⟩
  exact ⟨q, hq⟩

/-- Hence a nonzero matrix coefficient can only come from a monomial whose
denominator is no larger than the input label. -/
theorem toeplitzMonomial_denominator_le_of_apply_ne_zero
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (r s n m : finitePrimeSemigroup S)
    (h : toeplitzMonomial hS r s (basisVector S n) m ≠ 0) :
    (s : ℕ) ≤ (n : ℕ) := by
  have hdvd : s ∣ n :=
    toeplitzMonomial_denominator_dvd_of_apply_ne_zero hS r s n m h
  have hdvdNat : (s : ℕ) ∣ (n : ℕ) := by
    rcases hdvd with ⟨q, hq⟩
    refine ⟨(q : ℕ), ?_⟩
    simpa using congrArg (fun x : finitePrimeSemigroup S => (x : ℕ)) hq
  exact Nat.le_of_dvd (finitePrimeSemigroup_coe_pos hS n) hdvdNat

/-- If a nonzero matrix coefficient comes from a monomial with the same
denominator as the input label, then its numerator is forced by the output
label. -/
theorem toeplitzMonomial_numerator_eq_of_same_denominator_apply_ne_zero
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (r s n m : finitePrimeSemigroup S)
    (hden : (s : ℕ) = (n : ℕ))
    (h : toeplitzMonomial hS r s (basisVector S n) m ≠ 0) :
    r = m := by
  have hs : s = n := Subtype.ext hden
  subst s
  rcases (toeplitzMonomial_basisVector_apply_ne_zero_iff
    hS r n n m).1 h with ⟨q, hq, hr⟩
  have hq1 : q = 1 := by
    apply leftMul_injective hS n
    simpa using hq.symm
  subst q
  simpa using hr

end

end BostConnes
end BrickPileLean
