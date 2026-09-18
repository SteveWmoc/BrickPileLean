import BrickPileLean.BostConnes.FiniteToeplitzCore

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The logarithmic frequency attached to the Toeplitz monomial `V_m V_n*`. -/
def toeplitzMonomialFrequency
    {S : Finset ℕ} (m n : finitePrimeSemigroup S) : ℝ :=
  Real.log ((m : ℕ) : ℝ) - Real.log ((n : ℕ) : ℝ)

/-- Complex-time scalar continuation of the real-time monomial phase. -/
def toeplitzMonomialComplexPhase
    {S : Finset ℕ} (z : ℂ) (m n : finitePrimeSemigroup S) : ℂ :=
  Complex.exp (z * Complex.I * (toeplitzMonomialFrequency m n : ℂ))

/-- Complex conjugation reverses the real-time arithmetic phase. -/
@[simp] theorem star_timePhase_eq_neg
    {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) :
    star (timePhase t n) = timePhase (-t) n := by
  unfold timePhase
  change (starRingEnd ℂ) (Complex.exp (↑(t * Real.log ↑↑n) * Complex.I)) =
    Complex.exp (↑(-t * Real.log ↑↑n) * Complex.I)
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The complex-time phase restricts on the real axis to the expected monomial phase. -/
theorem toeplitzMonomialComplexPhase_ofReal
    {S : Finset ℕ} (t : ℝ) (m n : finitePrimeSemigroup S) :
    toeplitzMonomialComplexPhase (t : ℂ) m n =
      timePhase t m * timePhase (-t) n := by
  unfold toeplitzMonomialComplexPhase toeplitzMonomialFrequency timePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At imaginary time `iβ`, the monomial phase becomes a real exponential weight. -/
theorem toeplitzMonomialComplexPhase_mul_I
    {S : Finset ℕ} (β : ℝ) (m n : finitePrimeSemigroup S) :
    toeplitzMonomialComplexPhase ((β : ℂ) * Complex.I) m n =
      Complex.exp (-((β : ℂ) * (toeplitzMonomialFrequency m n : ℂ))) := by
  unfold toeplitzMonomialComplexPhase
  congr 1
  calc
    ((β : ℂ) * Complex.I) * Complex.I *
        (toeplitzMonomialFrequency m n : ℂ) =
      (β : ℂ) * (toeplitzMonomialFrequency m n : ℂ) *
        (Complex.I * Complex.I) := by
          ac_rfl
    _ = -((β : ℂ) * (toeplitzMonomialFrequency m n : ℂ)) := by
          rw [Complex.I_mul_I]
          ring

/-- The real-time evolution scales an adjoint shift by the opposite arithmetic phase. -/
theorem ambientTimeEvolution_shiftAdjoint
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (m : finitePrimeSemigroup S) :
    ambientTimeEvolution S t (shiftAdjoint hS m) =
      timePhase (-t) m • shiftAdjoint hS m := by
  rw [← ambientTimeStarAlgEquiv_apply]
  calc
    ambientTimeStarAlgEquiv S t (shiftAdjoint hS m) =
        ambientTimeStarAlgEquiv S t (star (shiftOperator hS m)) := by
          congr 1
    _ = star (ambientTimeStarAlgEquiv S t (shiftOperator hS m)) := by
          rw [map_star]
    _ = star (timePhase t m • shiftOperator hS m) := by
          rw [ambientTimeStarAlgEquiv_apply, ambientTimeEvolution_shift]
    _ = timePhase (-t) m • shiftAdjoint hS m := by
          simp [shiftAdjoint, ContinuousLinearMap.star_eq_adjoint]

/-- Real-time evolution of a standard Toeplitz monomial. -/
theorem ambientTimeEvolution_toeplitzMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (m n : finitePrimeSemigroup S) :
    ambientTimeEvolution S t (toeplitzMonomial hS m n) =
      (timePhase t m * timePhase (-t) n) • toeplitzMonomial hS m n := by
  rw [← ambientTimeStarAlgEquiv_apply]
  unfold toeplitzMonomial
  rw [map_mul]
  rw [ambientTimeStarAlgEquiv_apply, ambientTimeEvolution_shift]
  rw [ambientTimeStarAlgEquiv_apply, ambientTimeEvolution_shiftAdjoint]
  rw [smul_mul_smul]

/-- The restricted finite time evolution has the same monomial eigenvector formula. -/
theorem finiteTimeEvolution_toeplitzMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (m n : finitePrimeSemigroup S) :
    finiteTimeEvolution hS t (finiteToeplitzMonomial hS m n) =
      (timePhase t m * timePhase (-t) n) •
        finiteToeplitzMonomial hS m n := by
  apply Subtype.ext
  exact ambientTimeEvolution_toeplitzMonomial hS t m n

end

end BostConnes
end BrickPileLean
