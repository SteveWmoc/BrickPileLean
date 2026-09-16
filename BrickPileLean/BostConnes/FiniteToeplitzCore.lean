import BrickPileLean.BostConnes.FiniteGibbsExpectation

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The algebraic finite Toeplitz core, before taking norm closure. -/
def finiteToeplitzCore
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    StarSubalgebra ℂ (FiniteOperator S) :=
  StarAlgebra.adjoin ℂ (primeShiftSet hS)

/-- The finite Toeplitz algebra is exactly the topological closure of its algebraic core. -/
@[simp] theorem finiteToeplitzCore_topologicalClosure
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (finiteToeplitzCore hS).topologicalClosure = finiteToeplitzAlgebra hS :=
  rfl

/-- Each prime shift belongs already to the algebraic core. -/
theorem primeShift_mem_finiteToeplitzCore
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (p : S) :
    shiftOperator hS (primeSemigroupElement S p) ∈ finiteToeplitzCore hS := by
  exact StarAlgebra.subset_adjoin ℂ (primeShiftSet hS) ⟨p, rfl⟩

/-- Every semigroup shift belongs already to the algebraic core. -/
theorem shiftOperator_mem_finiteToeplitzCore
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    shiftOperator hS m ∈ finiteToeplitzCore hS := by
  let k := (exponentVectorEquivFinitePrimeSemigroup S hS).symm m
  have hm : m = ∏ p : S, (primeSemigroupElement S p) ^ k p := by
    simpa [k] using finitePrimeSemigroup_eq_prod_primePowers hS m
  rw [hm]
  have hprod : ∀ t : Finset S,
      shiftOperator hS (t.prod fun p => (primeSemigroupElement S p) ^ k p) ∈
        finiteToeplitzCore hS := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty]
        rw [shiftOperator_one]
        exact one_mem _
    | @insert p t hp ih =>
        rw [Finset.prod_insert hp, shiftOperator_mul, shiftOperator_pow]
        exact mul_mem (pow_mem (primeShift_mem_finiteToeplitzCore hS p) _) ih
  simpa using hprod Finset.univ

/-- Every adjoint semigroup shift belongs already to the algebraic core. -/
theorem shiftAdjoint_mem_finiteToeplitzCore
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    shiftAdjoint hS m ∈ finiteToeplitzCore hS := by
  have hm := star_mem (shiftOperator_mem_finiteToeplitzCore hS m)
  simpa [shiftAdjoint, ContinuousLinearMap.star_eq_adjoint] using hm

/-- Every standard Toeplitz monomial `V_m V_n*` lies in the algebraic core. -/
theorem toeplitzMonomial_mem_finiteToeplitzCore
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    toeplitzMonomial hS m n ∈ finiteToeplitzCore hS := by
  exact mul_mem (shiftOperator_mem_finiteToeplitzCore hS m)
    (shiftAdjoint_mem_finiteToeplitzCore hS n)

/-- A standard Toeplitz monomial, regarded as an element of the algebraic core. -/
def finiteToeplitzCoreMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) : finiteToeplitzCore hS :=
  ⟨toeplitzMonomial hS m n, toeplitzMonomial_mem_finiteToeplitzCore hS m n⟩

@[simp] theorem finiteToeplitzCoreMonomial_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    ((finiteToeplitzCoreMonomial hS m n : finiteToeplitzCore hS) : FiniteOperator S) =
      toeplitzMonomial hS m n :=
  rfl

end

end BostConnes
end BrickPileLean
