import BrickPileLean.BostConnes.FiniteGibbsExpectation
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct ComplexOrder

noncomputable section

/-- The Gibbs expectation is additive at positive inverse temperature. -/
theorem gibbsExpectation_add
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a b : FiniteOperator S) :
    gibbsExpectation S β (a + b) =
      gibbsExpectation S β a + gibbsExpectation S β b := by
  unfold gibbsExpectation
  rw [← Summable.tsum_add (gibbsExpectationTerm_summable hS hβ a)
    (gibbsExpectationTerm_summable hS hβ b)]
  apply tsum_congr
  intro k
  simp [gibbsExpectationTerm, mul_add]

/-- The Gibbs expectation is complex-linear at positive inverse temperature. -/
theorem gibbsExpectation_smul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (c : ℂ) (a : FiniteOperator S) :
    gibbsExpectation S β (c • a) = c • gibbsExpectation S β a := by
  unfold gibbsExpectation
  calc
    (∑' k : finitePrimeSemigroup S,
      gibbsExpectationTerm S β (c • a) k) =
        ∑' k : finitePrimeSemigroup S,
          c * gibbsExpectationTerm S β a k := by
            apply tsum_congr
            intro k
            simp [gibbsExpectationTerm, mul_assoc, mul_left_comm, mul_comm]
    _ = c * (∑' k : finitePrimeSemigroup S,
        gibbsExpectationTerm S β a k) := by
          rw [tsum_mul_left]
    _ = c • (∑' k : finitePrimeSemigroup S,
        gibbsExpectationTerm S β a k) := by
          simp [smul_eq_mul]

/-- The Gibbs expectation as a linear functional on all bounded operators. -/
def gibbsExpectationLinearMap
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    FiniteOperator S →ₗ[ℂ] ℂ where
  toFun := gibbsExpectation S β
  map_add' := gibbsExpectation_add hS hβ
  map_smul' := gibbsExpectation_smul hS hβ

@[simp] theorem gibbsExpectationLinearMap_apply
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : FiniteOperator S) :
    gibbsExpectationLinearMap hS hβ a = gibbsExpectation S β a :=
  rfl

/-- Each Gibbs expectation summand is bounded by its probability weight times the operator norm. -/
theorem norm_gibbsExpectationTerm_le
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : FiniteOperator S) (k : finitePrimeSemigroup S) :
    ‖gibbsExpectationTerm S β a k‖ ≤
      gibbsProbabilityWeight S β k * ‖a‖ := by
  have hinner :
      ‖inner ℂ (basisVector S k) (a (basisVector S k))‖ ≤ ‖a‖ := by
    calc
      ‖inner ℂ (basisVector S k) (a (basisVector S k))‖ ≤
          ‖basisVector S k‖ * ‖a (basisVector S k)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖basisVector S k‖ * (‖a‖ * ‖basisVector S k‖) := by
        gcongr
        exact a.le_opNorm (basisVector S k)
      _ = ‖a‖ := by simp
  calc
    ‖gibbsExpectationTerm S β a k‖ =
        gibbsProbabilityWeight S β k *
          ‖inner ℂ (basisVector S k) (a (basisVector S k))‖ := by
      simp [gibbsExpectationTerm, gibbsProbabilityWeight_nonneg hS hβ]
    _ ≤ gibbsProbabilityWeight S β k * ‖a‖ :=
      mul_le_mul_of_nonneg_left hinner
        (gibbsProbabilityWeight_nonneg hS hβ k)

/-- The normalized Gibbs expectation is contractive. -/
theorem norm_gibbsExpectation_le
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : FiniteOperator S) :
    ‖gibbsExpectation S β a‖ ≤ ‖a‖ := by
  have hs := gibbsExpectationTerm_summable hS hβ a
  have hnorm : Summable (fun k : finitePrimeSemigroup S =>
      ‖gibbsExpectationTerm S β a k‖) := hs.norm
  have hdom : Summable (fun k : finitePrimeSemigroup S =>
      gibbsProbabilityWeight S β k * ‖a‖) :=
    Summable.mul_right ‖a‖ (gibbsProbabilityWeight_summable hS hβ)
  unfold gibbsExpectation
  calc
    ‖∑' k : finitePrimeSemigroup S, gibbsExpectationTerm S β a k‖ ≤
        ∑' k : finitePrimeSemigroup S, ‖gibbsExpectationTerm S β a k‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : finitePrimeSemigroup S,
        gibbsProbabilityWeight S β k * ‖a‖ :=
      hnorm.tsum_le_tsum (norm_gibbsExpectationTerm_le hS hβ a) hdom
    _ = (∑' k : finitePrimeSemigroup S,
        gibbsProbabilityWeight S β k) * ‖a‖ := by
      rw [tsum_mul_right]
    _ = ‖a‖ := by
      rw [tsum_gibbsProbabilityWeight hS hβ, one_mul]

/-- The Gibbs expectation sends the identity operator to one. -/
@[simp] theorem gibbsExpectation_one
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    gibbsExpectation S β (1 : FiniteOperator S) = 1 := by
  unfold gibbsExpectation
  calc
    (∑' k : finitePrimeSemigroup S,
      gibbsExpectationTerm S β (1 : FiniteOperator S) k) =
        ∑' k : finitePrimeSemigroup S,
          ((gibbsProbabilityWeight S β k : ℝ) : ℂ) := by
            apply tsum_congr
            intro k
            simp [gibbsExpectationTerm]
    _ = (((∑' k : finitePrimeSemigroup S,
          gibbsProbabilityWeight S β k) : ℝ) : ℂ) := by
            exact (Complex.ofReal_tsum _).symm
    _ = 1 := by
      rw [tsum_gibbsProbabilityWeight hS hβ]
      norm_num

/-- The Gibbs expectation is positive on positive bounded operators. -/
theorem gibbsExpectation_nonneg
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {a : FiniteOperator S} (ha : 0 ≤ a) :
    0 ≤ gibbsExpectation S β a := by
  unfold gibbsExpectation
  apply tsum_nonneg
  intro k
  unfold gibbsExpectationTerm
  apply mul_nonneg
  · exact Complex.zero_le_real.mpr (gibbsProbabilityWeight_nonneg hS hβ k)
  · exact ((ContinuousLinearMap.nonneg_iff_isPositive a).mp ha).inner_nonneg_right
      (basisVector S k)

/-- The Gibbs expectation as a positive linear functional on all bounded operators. -/
def gibbsExpectationPositiveLinearMap
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    FiniteOperator S →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (gibbsExpectationLinearMap hS hβ)
    (fun _ ha => gibbsExpectation_nonneg hS hβ ha)

@[simp] theorem gibbsExpectationPositiveLinearMap_apply
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : FiniteOperator S) :
    gibbsExpectationPositiveLinearMap hS hβ a = gibbsExpectation S β a :=
  rfl

/-- The Gibbs state on the finite Toeplitz algebra, as a positive linear functional. -/
def finiteGibbsState
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    finiteToeplitzAlgebra hS →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun a => gibbsExpectation S β (a : FiniteOperator S)
      map_add' := fun a b => gibbsExpectation_add hS hβ a b
      map_smul' := fun c a => gibbsExpectation_smul hS hβ c a }
    (fun a ha => by
      apply gibbsExpectation_nonneg hS hβ
      exact ha)

@[simp] theorem finiteGibbsState_apply
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : finiteToeplitzAlgebra hS) :
    finiteGibbsState hS hβ a = gibbsExpectation S β (a : FiniteOperator S) :=
  rfl

/-- The Gibbs state is normalized. -/
@[simp] theorem finiteGibbsState_one
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    finiteGibbsState hS hβ 1 = 1 := by
  exact gibbsExpectation_one hS hβ

/-- The Gibbs state as an explicitly bounded continuous linear functional. -/
def finiteGibbsStateCLM
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    finiteToeplitzAlgebra hS →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => gibbsExpectation S β (a : FiniteOperator S)
      map_add' := fun a b => gibbsExpectation_add hS hβ a b
      map_smul' := fun c a => gibbsExpectation_smul hS hβ c a }
    1
    (fun a => by
      simpa using norm_gibbsExpectation_le hS hβ (a : FiniteOperator S))

@[simp] theorem finiteGibbsStateCLM_apply
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : finiteToeplitzAlgebra hS) :
    finiteGibbsStateCLM hS hβ a = finiteGibbsState hS hβ a :=
  rfl

/-- The Gibbs state has operator norm one. -/
theorem norm_finiteGibbsStateCLM
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    ‖finiteGibbsStateCLM hS hβ‖ = 1 := by
  apply le_antisymm
  · apply (finiteGibbsStateCLM hS hβ).opNorm_le_bound zero_le_one
    intro a
    simpa using norm_gibbsExpectation_le hS hβ (a : FiniteOperator S)
  · let oneA : finiteToeplitzAlgebra hS :=
      ⟨(1 : FiniteOperator S), one_mem (finiteToeplitzAlgebra hS)⟩
    have h := (finiteGibbsStateCLM hS hβ).le_opNorm oneA
    have honeA : finiteGibbsStateCLM hS hβ oneA = 1 := by
      change gibbsExpectation S β (1 : FiniteOperator S) = 1
      exact gibbsExpectation_one hS hβ
    have hnormA : ‖oneA‖ = 1 := by
      change ‖(1 : FiniteOperator S)‖ = 1
      exact norm_one
    rw [honeA, norm_one, hnormA, mul_one] at h
    exact h

/-- The packaged state retains the Toeplitz-monomial expectation formula. -/
theorem finiteGibbsState_toeplitzMonomial
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S) :
    finiteGibbsState hS hβ (finiteToeplitzMonomial hS m n) =
      if m = n then ((gibbsWeight β m : ℝ) : ℂ) else 0 := by
  exact gibbsExpectation_toeplitzMonomial hS hβ m n

end

end BostConnes
end BrickPileLean
