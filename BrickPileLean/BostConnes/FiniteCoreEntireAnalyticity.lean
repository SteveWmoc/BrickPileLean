import BrickPileLean.BostConnes.FiniteCoreComplexTime
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The scalar complex-time phase of a standard Toeplitz monomial is entire. -/
theorem toeplitzMonomialComplexPhase_analyticOnNhd
    {S : Finset ℕ} (m n : finitePrimeSemigroup S) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => toeplitzMonomialComplexPhase z m n) Set.univ := by
  unfold toeplitzMonomialComplexPhase
  exact
    ((analyticOnNhd_id.mul analyticOnNhd_const).mul
      analyticOnNhd_const).cexp

/-- A standard finite Toeplitz monomial multiplied by its complex-time phase
is an entire algebra-valued function of complex time. -/
theorem finiteToeplitzComplexTimeFamilyA_analyticOnNhd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (i : finiteToeplitzMonomialIndex S) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => finiteToeplitzComplexTimeFamilyA hS z i) Set.univ := by
  unfold finiteToeplitzComplexTimeFamilyA
  exact
    (toeplitzMonomialComplexPhase_analyticOnNhd i.1 i.2).smul
      analyticOnNhd_const

@[simp] theorem finiteToeplitzExpansionComplexTimeA_zero
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ) :
    finiteToeplitzExpansionComplexTimeA hS z
      (0 : finiteToeplitzMonomialIndex S →₀ ℂ) = 0 := by
  simp [finiteToeplitzExpansionComplexTimeA]

@[simp] theorem finiteToeplitzExpansionComplexTimeA_add
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ)
    (c d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzExpansionComplexTimeA hS z (c + d) =
      finiteToeplitzExpansionComplexTimeA hS z c +
        finiteToeplitzExpansionComplexTimeA hS z d := by
  classical
  unfold finiteToeplitzExpansionComplexTimeA
  set_option synthInstance.maxHeartbeats 100000 in
    exact Finsupp.sum_add_index (by simp) (by simp [add_smul])

@[simp] theorem finiteToeplitzExpansionComplexTimeA_single
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ)
    (i : finiteToeplitzMonomialIndex S) (a : ℂ) :
    finiteToeplitzExpansionComplexTimeA hS z (Finsupp.single i a) =
      a • finiteToeplitzComplexTimeFamilyA hS z i := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [finiteToeplitzExpansionComplexTimeA]

/-- The complex-time continuation of every finite monomial expansion is
entire as a function with values in the completed finite Toeplitz algebra. -/
theorem finiteToeplitzExpansionComplexTimeA_analyticOnNhd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => finiteToeplitzExpansionComplexTimeA hS z c) Set.univ := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simpa only [finiteToeplitzExpansionComplexTimeA_zero] using
        (analyticOnNhd_const :
          AnalyticOnNhd ℂ
            (fun _ : ℂ => (0 : finiteToeplitzAlgebra hS)) Set.univ)
  | single_add i a c hi ha ih =>
      have hsingle :
          AnalyticOnNhd ℂ
            (fun z : ℂ =>
              a • finiteToeplitzComplexTimeFamilyA hS z i) Set.univ := by
        exact analyticOnNhd_const.smul
          (finiteToeplitzComplexTimeFamilyA_analyticOnNhd hS i)
      have hfun :
          (fun z : ℂ =>
            finiteToeplitzExpansionComplexTimeA hS z (Finsupp.single i a + c)) =
            (fun z : ℂ => a • finiteToeplitzComplexTimeFamilyA hS z i) +
              (fun z : ℂ => finiteToeplitzExpansionComplexTimeA hS z c) := by
        funext z
        simp only [finiteToeplitzExpansionComplexTimeA_add,
          finiteToeplitzExpansionComplexTimeA_single, Pi.add_apply]
      rw [hfun]
      exact hsingle.add ih

/-- The intrinsic complex-time continuation of every algebraic-core element
is entire. This is the Banach-valued analyticity statement used in the
finite-prime KMS argument. -/
theorem finiteToeplitzCoreComplexTimeA_analyticOnNhd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => finiteToeplitzCoreComplexTimeA hS z x) Set.univ := by
  unfold finiteToeplitzCoreComplexTimeA
  exact finiteToeplitzExpansionComplexTimeA_analyticOnNhd hS
    (finiteToeplitzCoreExpansion hS x)

end

end BostConnes
end BrickPileLean
