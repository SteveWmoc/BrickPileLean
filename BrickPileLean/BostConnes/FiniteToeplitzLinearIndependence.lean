import BrickPileLean.BostConnes.FiniteCoreExpansion
import BrickPileLean.BostConnes.FiniteToeplitzMatrixCoefficients

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The standard Toeplitz monomials `V_m V_n*` are linearly independent.
The proof is triangular in the denominator: evaluating at the matrix coefficient
`e_n ↦ e_m` sees only terms whose denominator divides `n`; equal
denominators then force the numerator to be `m`. -/
theorem finiteToeplitzMonomialFamily_linearIndependent
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    LinearIndependent ℂ (finiteToeplitzMonomialFamily hS) := by
  classical
  rw [linearIndependent_iff']
  intro s g hrel
  have hzero :
      ∀ N : ℕ, ∀ i : finiteToeplitzMonomialIndex S,
        i ∈ s → (i.2 : ℕ) = N → g i = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro i hi hden
        rcases i with ⟨m, n⟩
        have hmatrix :
            (∑ j ∈ s,
              (g j •
                finiteToeplitzMonomialFamily hS j
                  (basisVector S n)) m) = 0 := by
          have h :=
            congrArg
              (fun T : FiniteOperator S => T (basisVector S n) m)
              hrel
          simpa [Finset.sum_apply, finiteToeplitzMonomialFamily] using h
        have hdiag :
            finiteToeplitzMonomialFamily hS (m, n)
                (basisVector S n) m = 1 := by
          change toeplitzMonomial hS m n (basisVector S n) m = 1
          have h :=
            congrArg
              (fun x : FiniteHilbertSpace S => x m)
              (toeplitzMonomial_basisVector_mul hS m n 1)
          simpa using h
        have hoff :
            ∀ j ∈ s, j ≠ (m, n) →
              (g j •
                finiteToeplitzMonomialFamily hS j
                  (basisVector S n)) m = 0 := by
          intro j hj hji
          rcases j with ⟨r, t⟩
          by_cases hlt : (t : ℕ) < (n : ℕ)
          · have hltN : (t : ℕ) < N := by
              rw [← hden]
              exact hlt
            have hgt : g (r, t) = 0 :=
              ih (t : ℕ) hltN (r, t) hj rfl
            simp [hgt]
          · have hnt : (n : ℕ) ≤ (t : ℕ) :=
              Nat.le_of_not_gt hlt
            by_cases heq : (t : ℕ) = (n : ℕ)
            · have ht : t = n := Subtype.ext heq
              have hrne : r ≠ m := by
                intro hr
                apply hji
                exact Prod.ext hr ht
              have hz :
                  finiteToeplitzMonomialFamily hS (r, t)
                      (basisVector S n) m = 0 := by
                change toeplitzMonomial hS r t
                    (basisVector S n) m = 0
                by_contra hnz
                have hr :=
                  toeplitzMonomial_numerator_eq_of_same_denominator_apply_ne_zero
                    hS r t n m heq hnz
                exact hrne hr
              simp [Pi.smul_apply, hz]
            · have hgt : (n : ℕ) < (t : ℕ) :=
                lt_of_le_of_ne hnt (Ne.symm heq)
              have hz :
                  finiteToeplitzMonomialFamily hS (r, t)
                      (basisVector S n) m = 0 := by
                change toeplitzMonomial hS r t
                    (basisVector S n) m = 0
                by_contra hnz
                have hle :=
                  toeplitzMonomial_denominator_le_of_apply_ne_zero
                    hS r t n m hnz
                exact (not_le_of_gt hgt) hle
              simp [Pi.smul_apply, hz]
        have hcollapse :
            (∑ j ∈ s,
              (g j •
                finiteToeplitzMonomialFamily hS j
                  (basisVector S n)) m) = g (m, n) := by
          rw [Finset.sum_eq_single (m, n)]
          · simp [Pi.smul_apply, hdiag]
          · exact hoff
          · simp [hi]
        rw [hcollapse] at hmatrix
        exact hmatrix
  intro i hi
  exact hzero (i.2 : ℕ) i hi rfl

/-- Evaluating a finite monomial expansion is injective. -/
theorem finiteToeplitzExpansionEval_injective
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    Function.Injective (finiteToeplitzExpansionEval hS) := by
  intro c d hcd
  have hli := finiteToeplitzMonomialFamily_linearIndependent hS
  apply hli.finsuppLinearCombination_injective
  simpa [finiteToeplitzExpansionEval,
    Finsupp.linearCombination_apply] using hcd

/-- Two finite monomial expansions represent the same ambient operator iff
their coefficient families are equal. -/
theorem finiteToeplitzExpansionEval_eq_iff
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (c d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzExpansionEval hS c =
        finiteToeplitzExpansionEval hS d ↔
      c = d := by
  constructor
  · intro h
    exact finiteToeplitzExpansionEval_injective hS h
  · intro h
    exact congrArg (finiteToeplitzExpansionEval hS) h

/-- The algebra-valued finite expansion map is also injective. -/
theorem finiteToeplitzExpansionEvalA_injective
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    Function.Injective (finiteToeplitzExpansionEvalA hS) := by
  intro c d hcd
  apply finiteToeplitzExpansionEval_injective hS
  have hcoe := congrArg
    (fun x : finiteToeplitzAlgebra hS => (x : FiniteOperator S)) hcd
  simpa [finiteToeplitzExpansionEvalA_coe] using hcoe

/-- The chosen finite expansion of a core element is the unique finite
monomial expansion representing it. -/
theorem finiteToeplitzCoreExpansion_unique
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ)
    (hc : finiteToeplitzExpansionEval hS c =
      (x : FiniteOperator S)) :
    c = finiteToeplitzCoreExpansion hS x := by
  apply finiteToeplitzExpansionEval_injective hS
  calc
    finiteToeplitzExpansionEval hS c = (x : FiniteOperator S) := hc
    _ = finiteToeplitzExpansionEval hS
        (finiteToeplitzCoreExpansion hS x) :=
      (finiteToeplitzCoreExpansion_eval hS x).symm

end

end BostConnes
end BrickPileLean
