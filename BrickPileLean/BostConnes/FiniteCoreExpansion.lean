import BrickPileLean.BostConnes.FiniteToeplitzMonomialSpan
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- Index type for the standard Toeplitz monomials `V_m V_n*`. -/
abbrev finiteToeplitzMonomialIndex (S : Finset ℕ) :=
  finitePrimeSemigroup S × finitePrimeSemigroup S

/-- The ambient family of standard Toeplitz monomials. -/
def finiteToeplitzMonomialFamily
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (i : finiteToeplitzMonomialIndex S) : FiniteOperator S :=
  toeplitzMonomial hS i.1 i.2

/-- The previously defined monomial set is exactly the range of the indexed
monomial family. -/
theorem finiteToeplitzMonomialSet_eq_range
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    finiteToeplitzMonomialSet hS =
      Set.range (finiteToeplitzMonomialFamily hS) := by
  ext x
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨(m, n), rfl⟩
  · rintro ⟨⟨m, n⟩, rfl⟩
    exact ⟨m, n, rfl⟩

/-- Evaluation of a finitely supported coefficient family as a finite linear
combination of standard Toeplitz monomials. -/
def finiteToeplitzExpansionEval
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) : FiniteOperator S :=
  c.sum fun i a => a • finiteToeplitzMonomialFamily hS i

/-- Every element of the algebraic Toeplitz core has a finite expansion in
standard monomials. -/
theorem finiteToeplitzCore_exists_finsupp_expansion
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) :
    ∃ c : finiteToeplitzMonomialIndex S →₀ ℂ,
      finiteToeplitzExpansionEval hS c = (x : FiniteOperator S) := by
  have hxspan :
      (x : FiniteOperator S) ∈ finiteToeplitzMonomialSpan hS :=
    finiteToeplitzCore_le_monomialSpan hS x.property
  rw [finiteToeplitzMonomialSpan,
    finiteToeplitzMonomialSet_eq_range hS] at hxspan
  rcases (Finsupp.mem_span_range_iff_exists_finsupp.mp hxspan) with ⟨c, hc⟩
  exact ⟨c, hc⟩

/-- A choice of finite monomial expansion for each algebraic-core element. -/
def finiteToeplitzCoreExpansion
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) :
    finiteToeplitzMonomialIndex S →₀ ℂ :=
  Classical.choose (finiteToeplitzCore_exists_finsupp_expansion hS x)

/-- Evaluating the chosen finite expansion recovers the original core
element in the ambient operator algebra. -/
theorem finiteToeplitzCoreExpansion_eval
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) :
    finiteToeplitzExpansionEval hS (finiteToeplitzCoreExpansion hS x) =
      (x : FiniteOperator S) := by
  exact Classical.choose_spec
    (finiteToeplitzCore_exists_finsupp_expansion hS x)

/-- The canonical inclusion of the algebraic core into the completed finite
Toeplitz algebra. -/
def finiteToeplitzCoreToAlgebra
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) : finiteToeplitzAlgebra hS := by
  refine ⟨(x : FiniteOperator S), ?_⟩
  have hx :
      (x : FiniteOperator S) ∈
        (finiteToeplitzCore hS).topologicalClosure :=
    StarSubalgebra.le_topologicalClosure (finiteToeplitzCore hS) x.property
  simpa using hx

@[simp] theorem finiteToeplitzCoreToAlgebra_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) :
    ((finiteToeplitzCoreToAlgebra hS x : finiteToeplitzAlgebra hS) :
      FiniteOperator S) = (x : FiniteOperator S) :=
  rfl

/-- The standard monomial family, now regarded inside the completed finite
Toeplitz algebra. -/
def finiteToeplitzMonomialFamilyA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (i : finiteToeplitzMonomialIndex S) : finiteToeplitzAlgebra hS :=
  finiteToeplitzMonomial hS i.1 i.2

/-- Evaluation of a finite monomial expansion inside the completed finite
Toeplitz algebra. -/
def finiteToeplitzExpansionEvalA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzAlgebra hS :=
  c.sum fun i a => a • finiteToeplitzMonomialFamilyA hS i

/-- Coercing an algebra-valued finite expansion to bounded operators gives
the ambient expansion. -/
theorem finiteToeplitzExpansionEvalA_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    ((finiteToeplitzExpansionEvalA hS c : finiteToeplitzAlgebra hS) :
      FiniteOperator S) =
      finiteToeplitzExpansionEval hS c := by
  classical
  rw [finiteToeplitzExpansionEvalA, finiteToeplitzExpansionEval]
  induction c using Finsupp.induction with
  | zero =>
      simp
  | @add_one i a c hi ha ih =>
      simp [hi, ih, finiteToeplitzMonomialFamilyA,
        finiteToeplitzMonomialFamily]

/-- The chosen finite expansion also recovers the core element after
inclusion into the completed finite Toeplitz algebra. -/
theorem finiteToeplitzCoreExpansion_evalA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : finiteToeplitzCore hS) :
    finiteToeplitzExpansionEvalA hS (finiteToeplitzCoreExpansion hS x) =
      finiteToeplitzCoreToAlgebra hS x := by
  apply Subtype.ext
  rw [finiteToeplitzExpansionEvalA_coe,
    finiteToeplitzCoreExpansion_eval]

end

end BostConnes
end BrickPileLean
