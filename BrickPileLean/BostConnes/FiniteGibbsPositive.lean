import BrickPileLean.BostConnes.FiniteGibbsSemigroup
import Mathlib.Analysis.InnerProductSpace.Positive

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct ENNReal

noncomputable section

/-- At positive inverse temperature every Gibbs multiplier is at most one. -/
theorem gibbsWeight_le_one {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) (n : finitePrimeSemigroup S) :
    gibbsWeight β n ≤ 1 := by
  rw [gibbsWeight_eq_exp_neg_energy hS]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (finiteEnergy_nonneg hS n))

/-- The real diagonal multiplier makes the bounded Gibbs operator symmetric. -/
theorem gibbsOperator_symmetric {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    (gibbsOperator S β).IsSymmetric := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [gibbsOperator_apply_coordinate hS hβ, gibbsOperator_apply_coordinate hS hβ]
  change inner ℂ ((gibbsWeight β n : ℂ) • x n) (y n) =
    inner ℂ (x n) ((gibbsWeight β n : ℂ) • y n)
  rw [inner_smul_left, inner_smul_right]
  simp

/-- The real Gibbs quadratic form is the convergent sum of weighted
coordinate squared norms, for every Hilbert-space vector. -/
theorem hasSum_gibbsOperator_quadratic {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) (x : FiniteHilbertSpace S) :
    HasSum (fun n : finitePrimeSemigroup S => gibbsWeight β n * ‖x n‖ ^ 2)
      (inner ℂ x (gibbsOperator S β x)).re := by
  have h := RCLike.hasSum_re ℂ (lp.hasSum_inner (𝕜 := ℂ) x (gibbsOperator S β x))
  change HasSum (fun n => (inner ℂ (x n) (gibbsOperator S β x n)).re)
    (inner ℂ x (gibbsOperator S β x)).re at h
  have hcoord (n : finitePrimeSemigroup S) :
      (inner ℂ (x n) (gibbsOperator S β x n)).re = gibbsWeight β n * ‖x n‖ ^ 2 := by
    rw [gibbsOperator_apply_coordinate hS hβ]
    change (inner ℂ (x n) ((gibbsWeight β n : ℂ) • x n)).re = _
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    change (Complex.ofReal (gibbsWeight β n) * Complex.ofReal ‖x n‖ ^ 2).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  simpa only [hcoord] using h

/-- The Gibbs operator is positive in the Hilbert-space operator sense. -/
theorem gibbsOperator_isPositive {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    (gibbsOperator S β).IsPositive := by
  refine ⟨gibbsOperator_symmetric hS hβ, ?_⟩
  intro x
  change 0 ≤ (inner ℂ (gibbsOperator S β x) x).re
  rw [gibbsOperator_symmetric hS hβ x x]
  rw [← (hasSum_gibbsOperator_quadratic hS hβ x).tsum_eq]
  exact tsum_nonneg (fun n => mul_nonneg (gibbsWeight_nonneg β n) (sq_nonneg _))

/-- Positivity of the bounded Gibbs operator includes self-adjointness. -/
theorem gibbsOperator_isSelfAdjoint {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    IsSelfAdjoint (gibbsOperator S β) :=
  (gibbsOperator_isPositive hS hβ).isSelfAdjoint

/-- Gibbs damping never increases the norm of a vector. -/
theorem norm_gibbsOperator_apply_le {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) (x : FiniteHilbertSpace S) :
    ‖gibbsOperator S β x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [gibbsOperator_apply_coordinate hS hβ, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (gibbsWeight_nonneg β n)]
  exact mul_le_of_le_one_left (norm_nonneg _) (gibbsWeight_le_one hS hβ n)

/-- The Gibbs operator is contractive in operator norm. -/
theorem norm_gibbsOperator_le_one {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    ‖gibbsOperator S β‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_gibbsOperator_apply_le hS hβ x

/-- The vacuum has Gibbs eigenvalue one, so the contraction bound is sharp. -/
theorem norm_gibbsOperator_eq_one {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    ‖gibbsOperator S β‖ = 1 := by
  apply le_antisymm (norm_gibbsOperator_le_one hS hβ)
  have h := (gibbsOperator S β).le_opNorm (basisVector S 1)
  rw [gibbsOperator_basisVector hS hβ] at h
  have hv : gibbsWeight β (1 : finitePrimeSemigroup S) = 1 := by simp [gibbsWeight]
  simpa only [hv, Complex.ofReal_one, one_smul, norm_basisVector, mul_one] using h

end

end BostConnes
end BrickPileLean
