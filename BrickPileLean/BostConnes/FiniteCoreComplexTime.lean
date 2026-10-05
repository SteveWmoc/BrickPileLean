import BrickPileLean.BostConnes.FiniteAnalyticKMSBoundary
import BrickPileLean.BostConnes.FiniteToeplitzLinearIndependence

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The finite monomial expansion of a core element is unique even when
expressed in the completed finite Toeplitz algebra. -/
theorem finiteToeplitzCoreExpansion_uniqueA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ)
    (hc : finiteToeplitzExpansionEvalA hS c =
      finiteToeplitzCoreToAlgebra hS x) :
    c = finiteToeplitzCoreExpansion hS x := by
  apply finiteToeplitzExpansionEvalA_injective hS
  calc
    finiteToeplitzExpansionEvalA hS c =
        finiteToeplitzCoreToAlgebra hS x := hc
    _ = finiteToeplitzExpansionEvalA hS
        (finiteToeplitzCoreExpansion hS x) :=
      (finiteToeplitzCoreExpansion_evalA hS x).symm

/-- Intrinsic complex-time continuation of an algebraic-core element,
obtained from its unique finite monomial expansion. -/
def finiteToeplitzCoreComplexTimeA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ)
    (x : finiteToeplitzCore hS) : finiteToeplitzAlgebra hS :=
  finiteToeplitzExpansionComplexTimeA hS z
    (finiteToeplitzCoreExpansion hS x)

/-- Any finite monomial expansion representing a core element gives the same
complex-time continuation. -/
theorem finiteToeplitzExpansionComplexTimeA_eq_core
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ)
    (x : finiteToeplitzCore hS)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ)
    (hc : finiteToeplitzExpansionEvalA hS c =
      finiteToeplitzCoreToAlgebra hS x) :
    finiteToeplitzExpansionComplexTimeA hS z c =
      finiteToeplitzCoreComplexTimeA hS z x := by
  have huniq : c = finiteToeplitzCoreExpansion hS x :=
    finiteToeplitzCoreExpansion_uniqueA hS x c hc
  rw [huniq]
  rfl

/-- On real time, the intrinsic core continuation agrees with the original
finite Toeplitz time evolution. -/
theorem finiteToeplitzCoreComplexTimeA_ofReal
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (t : ℝ) (x : finiteToeplitzCore hS) :
    finiteToeplitzCoreComplexTimeA hS (t : ℂ) x =
      finiteTimeEvolution hS t (finiteToeplitzCoreToAlgebra hS x) := by
  unfold finiteToeplitzCoreComplexTimeA
  rw [finiteToeplitzExpansionComplexTimeA_ofReal]
  rw [finiteToeplitzCoreExpansion_evalA]

/-- At imaginary time iβ, the intrinsic complex-time continuation is
exactly the KMS boundary transform. -/
theorem finiteToeplitzCoreComplexTimeA_mul_I
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (β : ℝ) (x : finiteToeplitzCore hS) :
    finiteToeplitzCoreComplexTimeA hS ((β : ℂ) * Complex.I) x =
      finiteToeplitzCoreKMSBoundaryA hS β x := by
  unfold finiteToeplitzCoreComplexTimeA
  unfold finiteToeplitzCoreKMSBoundaryA
  rw [finiteToeplitzExpansionComplexTimeA_mul_I]

/-- Core-level KMS identity written directly in terms of the intrinsic
complex-time continuation at imaginary time. -/
theorem finiteGibbsState_kms_core_complexTime
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y : finiteToeplitzCore hS) :
    finiteGibbsState hS hβ
        (finiteToeplitzCoreToAlgebra hS x *
          finiteToeplitzCoreToAlgebra hS y) =
      finiteGibbsState hS hβ
        (finiteToeplitzCoreToAlgebra hS y *
          finiteToeplitzCoreComplexTimeA hS
            ((β : ℂ) * Complex.I) x) := by
  rw [finiteToeplitzCoreComplexTimeA_mul_I]
  exact finiteGibbsState_kms_core_boundary hS hβ x y

end

end BostConnes
end BrickPileLean
