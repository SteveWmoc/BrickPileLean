import BrickPileLean.BostConnes.FiniteCoreKMSBoundary
import BrickPileLean.BostConnes.FiniteAnalyticMonomial

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The ratio of two Gibbs weights is the real exponential of the negative
inverse temperature times the logarithmic monomial frequency. -/
theorem gibbsWeight_div_eq_exp_neg_frequency
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (β : ℝ) (m n : finitePrimeSemigroup S) :
    gibbsWeight β m / gibbsWeight β n =
      Real.exp (-β * toeplitzMonomialFrequency m n) := by
  have hm : 0 < (((m : ℕ) : ℝ)) := by
    exact_mod_cast finitePrimeSemigroup_coe_pos hS m
  have hn : 0 < (((n : ℕ) : ℝ)) := by
    exact_mod_cast finitePrimeSemigroup_coe_pos hS n
  unfold gibbsWeight toeplitzMonomialFrequency
  rw [Real.rpow_def_of_pos hm, Real.rpow_def_of_pos hn]
  rw [← Real.exp_sub]
  congr 1
  ring

/-- The KMS boundary weight on a standard monomial is exactly its
complex-time phase at imaginary time `iβ`. -/
theorem finiteToeplitzMonomialKMSWeight_eq_complexPhase
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (β : ℝ) (m n : finitePrimeSemigroup S) :
    finiteToeplitzMonomialKMSWeight β (m, n) =
      toeplitzMonomialComplexPhase ((β : ℂ) * Complex.I) m n := by
  rw [toeplitzMonomialComplexPhase_mul_I]
  unfold finiteToeplitzMonomialKMSWeight
  rw [← Complex.ofReal_div]
  rw [gibbsWeight_div_eq_exp_neg_frequency hS β m n]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- A standard monomial multiplied by its complex-time phase. -/
def finiteToeplitzComplexTimeFamilyA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ)
    (i : finiteToeplitzMonomialIndex S) : finiteToeplitzAlgebra hS :=
  toeplitzMonomialComplexPhase z i.1 i.2 •
    finiteToeplitzMonomialFamilyA hS i

/-- Complex-time continuation of a finitely supported monomial expansion,
defined term by term. -/
def finiteToeplitzExpansionComplexTimeA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (z : ℂ)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzAlgebra hS :=
  c.sum fun i a => a • finiteToeplitzComplexTimeFamilyA hS z i

/-- At imaginary time `iβ`, the finite complex-time transform is exactly
the KMS boundary transform from the preceding development. -/
theorem finiteToeplitzExpansionComplexTimeA_mul_I
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (β : ℝ) (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzExpansionComplexTimeA hS ((β : ℂ) * Complex.I) c =
      finiteToeplitzExpansionKMSBoundaryA hS β c := by
  classical
  unfold finiteToeplitzExpansionComplexTimeA
  unfold finiteToeplitzExpansionKMSBoundaryA
  apply Finsupp.sum_congr
  intro i hi
  rcases i with ⟨m, n⟩
  unfold finiteToeplitzComplexTimeFamilyA
  unfold finiteToeplitzKMSBoundaryFamilyA
  rw [← finiteToeplitzMonomialKMSWeight_eq_complexPhase hS β m n]

/-- On the real axis, the finite complex-time transform agrees with the
already-defined real-time automorphism. -/
theorem finiteToeplitzExpansionComplexTimeA_ofReal
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (t : ℝ) (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzExpansionComplexTimeA hS (t : ℂ) c =
      finiteTimeEvolution hS t (finiteToeplitzExpansionEvalA hS c) := by
  classical
  unfold finiteToeplitzExpansionComplexTimeA
  unfold finiteToeplitzExpansionEvalA
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  rcases i with ⟨m, n⟩
  unfold finiteToeplitzComplexTimeFamilyA
  unfold finiteToeplitzMonomialFamilyA
  rw [map_smul]
  rw [finiteTimeEvolution_toeplitzMonomial]
  rw [toeplitzMonomialComplexPhase_ofReal]

end

end BostConnes
end BrickPileLean
