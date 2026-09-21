import BrickPileLean.BostConnes.FinitePointNormContinuity
import BrickPileLean.BostConnes.FiniteGibbsState

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct

noncomputable section

/-- A semigroup shift regarded as an element of the finite Toeplitz algebra. -/
def finiteToeplitzShift
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) : finiteToeplitzAlgebra hS :=
  ⟨shiftOperator hS m, shiftOperator_mem_finiteToeplitzAlgebra hS m⟩

/-- An adjoint semigroup shift regarded as an element of the finite Toeplitz algebra. -/
def finiteToeplitzAdjointShift
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) : finiteToeplitzAlgebra hS :=
  ⟨shiftAdjoint hS m, shiftAdjoint_mem_finiteToeplitzAlgebra hS m⟩

@[simp] theorem finiteToeplitzShift_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    ((finiteToeplitzShift hS m : finiteToeplitzAlgebra hS) : FiniteOperator S) =
      shiftOperator hS m :=
  rfl

@[simp] theorem finiteToeplitzAdjointShift_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    ((finiteToeplitzAdjointShift hS m : finiteToeplitzAlgebra hS) : FiniteOperator S) =
      shiftAdjoint hS m :=
  rfl

/-- The reverse product `V_n* V_m`, packaged inside the finite Toeplitz algebra. -/
def finiteReverseToeplitzMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) : finiteToeplitzAlgebra hS :=
  finiteToeplitzAdjointShift hS n * finiteToeplitzShift hS m

@[simp] theorem finiteReverseToeplitzMonomial_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    ((finiteReverseToeplitzMonomial hS m n : finiteToeplitzAlgebra hS) :
      FiniteOperator S) =
        shiftAdjoint hS n * shiftOperator hS m :=
  rfl

/-- The isometry relation `V_m* V_m = 1` in operator-algebra multiplication notation. -/
@[simp] theorem shiftAdjoint_mul_shiftOperator_self
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    shiftAdjoint hS m * shiftOperator hS m = (1 : FiniteOperator S) := by
  apply ContinuousLinearMap.ext
  intro x
  change shiftAdjoint hS m (shiftOperator hS m x) = x
  exact shiftAdjoint_shift_apply hS m x

/-- If `m ≠ n`, the basis-diagonal coefficients of `V_n* V_m` vanish. -/
theorem reverseToeplitzMonomial_diagonal_of_ne
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n)
    (k : finitePrimeSemigroup S) :
    inner ℂ (basisVector S k)
        ((shiftAdjoint hS n * shiftOperator hS m) (basisVector S k)) = 0 := by
  have hdiff : n * k ≠ m * k := by
    intro h
    apply hmn
    exact (rightMul_injective hS k) h.symm
  change inner ℂ (basisVector S k)
      (shiftAdjoint hS n (shiftOperator hS m (basisVector S k))) = 0
  rw [shiftOperator_basisVector]
  calc
    inner ℂ (basisVector S k)
        (shiftAdjoint hS n (basisVector S (m * k))) =
      inner ℂ (shiftOperator hS n (basisVector S k))
        (basisVector S (m * k)) := by
          simpa [shiftAdjoint] using
            (ContinuousLinearMap.adjoint_inner_right
              (shiftOperator hS n) (basisVector S k) (basisVector S (m * k)))
    _ = inner ℂ (basisVector S (n * k)) (basisVector S (m * k)) := by
          rw [shiftOperator_basisVector]
    _ = 0 := by
      unfold basisVector
      rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
      simp [hdiff]

/-- The Gibbs expectation of `V_m* V_m` is one. -/
@[simp] theorem gibbsExpectation_shiftAdjoint_mul_shiftOperator_self
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m : finitePrimeSemigroup S) :
    gibbsExpectation S β (shiftAdjoint hS m * shiftOperator hS m) = 1 := by
  rw [shiftAdjoint_mul_shiftOperator_self, gibbsExpectation_one hS hβ]

/-- Off the diagonal, the Gibbs expectation of `V_n* V_m` vanishes. -/
theorem gibbsExpectation_shiftAdjoint_mul_shiftOperator_of_ne
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (_hβ : 0 < β)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n) :
    gibbsExpectation S β (shiftAdjoint hS n * shiftOperator hS m) = 0 := by
  unfold gibbsExpectation
  calc
    (∑' k : finitePrimeSemigroup S,
      gibbsExpectationTerm S β
        (shiftAdjoint hS n * shiftOperator hS m) k) =
        ∑' _k : finitePrimeSemigroup S, (0 : ℂ) := by
          apply tsum_congr
          intro k
          unfold gibbsExpectationTerm
          rw [reverseToeplitzMonomial_diagonal_of_ne hS hmn k]
          simp
    _ = 0 := by simp

/-- The reverse Toeplitz product has Gibbs expectation `δ_{m,n}`. -/
theorem gibbsExpectation_shiftAdjoint_mul_shiftOperator
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S) :
    gibbsExpectation S β (shiftAdjoint hS n * shiftOperator hS m) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, shiftAdjoint_mul_shiftOperator_self,
      gibbsExpectation_one hS hβ]
  · rw [if_neg hmn,
      gibbsExpectation_shiftAdjoint_mul_shiftOperator_of_ne hS hβ hmn]

/-- The packaged Gibbs state has the same reverse-product formula. -/
theorem finiteGibbsState_reverseToeplitzMonomial
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S) :
    finiteGibbsState hS hβ (finiteReverseToeplitzMonomial hS m n) =
      if m = n then 1 else 0 := by
  change gibbsExpectation S β (shiftAdjoint hS n * shiftOperator hS m) =
    if m = n then 1 else 0
  exact gibbsExpectation_shiftAdjoint_mul_shiftOperator hS hβ m n

/-- The KMS boundary identity on the canonical shift/adjoint generators.

For `a = V_m` and `b = V_n*`, the imaginary-time continuation satisfies
`α_{iβ}(V_m) = m^{-β} V_m`, so the KMS relation reads
`φ(V_m V_n*) = m^{-β} φ(V_n* V_m)`. -/
theorem finiteGibbsState_kms_shift_adjoint
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S) :
    finiteGibbsState hS hβ (finiteToeplitzMonomial hS m n) =
      ((gibbsWeight β m : ℝ) : ℂ) *
        finiteGibbsState hS hβ (finiteReverseToeplitzMonomial hS m n) := by
  rw [finiteGibbsState_toeplitzMonomial,
    finiteGibbsState_reverseToeplitzMonomial]
  by_cases hmn : m = n
  · subst n
    simp
  · simp [hmn]

end

end BostConnes
end BrickPileLean
