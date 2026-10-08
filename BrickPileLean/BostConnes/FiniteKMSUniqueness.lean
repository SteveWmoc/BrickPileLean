import BrickPileLean.BostConnes.FiniteKMSUniquenessRigidity

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- Every normalized bounded core-KMS functional has the same value as the
finite Gibbs functional on a standard Toeplitz monomial. -/
theorem IsFiniteToeplitzCoreKMS.monomial_eq_finiteGibbsStateCLM
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    (m n : finitePrimeSemigroup S) :
    φ (finiteToeplitzMonomial hS m n) =
      finiteGibbsStateCLM hS hβ (finiteToeplitzMonomial hS m n) := by
  by_cases hmn : m = n
  · subst n
    rw [hφ.diagonal hS m]
    change ((gibbsWeight β m : ℝ) : ℂ) =
      gibbsExpectation S β (toeplitzMonomial hS m m)
    exact (gibbsExpectation_toeplitzMonomial_self hS hβ m).symm
  · rw [hφ.offDiagonal hS hβ hmn]
    change 0 = gibbsExpectation S β (toeplitzMonomial hS m n)
    exact (gibbsExpectation_toeplitzMonomial_of_ne hS hβ hmn).symm

/-- Equality with the finite Gibbs functional extends from standard monomials
to every finite monomial expansion. -/
theorem IsFiniteToeplitzCoreKMS.expansion_eq_finiteGibbsStateCLM
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    φ (finiteToeplitzExpansionEvalA hS c) =
      finiteGibbsStateCLM hS hβ (finiteToeplitzExpansionEvalA hS c) := by
  classical
  unfold finiteToeplitzExpansionEvalA
  simp only [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  rcases i with ⟨m, n⟩
  unfold finiteToeplitzMonomialFamilyA
  rw [map_smul, map_smul]
  exact congrArg (fun z : ℂ => (c (m, n)) • z)
    (hφ.monomial_eq_finiteGibbsStateCLM hS hβ m n)

/-- Equality with the finite Gibbs functional holds on the whole algebraic
Toeplitz core. -/
theorem IsFiniteToeplitzCoreKMS.core_eq_finiteGibbsStateCLM
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    (x : finiteToeplitzCore hS) :
    φ (finiteToeplitzCoreToAlgebra hS x) =
      finiteGibbsStateCLM hS hβ
        (finiteToeplitzCoreToAlgebra hS x) := by
  rw [← finiteToeplitzCoreExpansion_evalA hS x]
  exact hφ.expansion_eq_finiteGibbsStateCLM hS hβ
    (finiteToeplitzCoreExpansion hS x)

/-- The canonical inclusion of the algebraic Toeplitz core into its completed
finite Toeplitz algebra has dense range. -/
theorem finiteToeplitzCoreToAlgebra_denseRange
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    DenseRange (finiteToeplitzCoreToAlgebra hS) := by
  change DenseRange
    (Set.inclusion
      (StarSubalgebra.le_topologicalClosure (finiteToeplitzCore hS)))
  rw [denseRange_inclusion_iff]
  intro x hx
  exact hx

/-- The finite Gibbs functional is the unique normalized bounded functional
satisfying the KMS boundary identity on the algebraic Toeplitz core. -/
theorem IsFiniteToeplitzCoreKMS.eq_finiteGibbsStateCLM
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ) :
    φ = finiteGibbsStateCLM hS hβ := by
  apply ContinuousLinearMap.coeFn_injective
  exact (finiteToeplitzCoreToAlgebra_denseRange hS).equalizer
    φ.continuous
    (finiteGibbsStateCLM hS hβ).continuous
    (by
      funext x
      exact hφ.core_eq_finiteGibbsStateCLM hS hβ x)

/-- Any two normalized bounded core-KMS functionals at the same positive
inverse temperature are equal. -/
theorem IsFiniteToeplitzCoreKMS.unique
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {φ ψ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    (hψ : IsFiniteToeplitzCoreKMS hS β ψ) :
    φ = ψ := by
  rw [hφ.eq_finiteGibbsStateCLM hS hβ,
    hψ.eq_finiteGibbsStateCLM hS hβ]

end

end BostConnes
end BrickPileLean
