import BrickPileLean.BostConnes.FiniteKMSMonomials

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The set of standard Toeplitz monomials `V_m V_n*`. -/
def finiteToeplitzMonomialSet
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    Set (FiniteOperator S) :=
  {a | ∃ m n : finitePrimeSemigroup S, a = toeplitzMonomial hS m n}

/-- The complex linear span of the standard Toeplitz monomials. -/
def finiteToeplitzMonomialSpan
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    Submodule ℂ (FiniteOperator S) :=
  Submodule.span ℂ (finiteToeplitzMonomialSet hS)

/-- Every standard Toeplitz monomial belongs to its linear span. -/
theorem toeplitzMonomial_mem_finiteToeplitzMonomialSpan
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    toeplitzMonomial hS m n ∈ finiteToeplitzMonomialSpan hS := by
  apply Submodule.subset_span
  exact ⟨m, n, rfl⟩

/-- The adjoint shift at the identity is the identity operator. -/
@[simp] theorem shiftAdjoint_one
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    shiftAdjoint hS (1 : finitePrimeSemigroup S) = (1 : FiniteOperator S) := by
  unfold shiftAdjoint
  rw [shiftOperator_one]
  exact ContinuousLinearMap.adjoint_one

/-- The identity is the standard monomial `V_1 V_1*`. -/
@[simp] theorem toeplitzMonomial_one_one
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    toeplitzMonomial hS (1 : finitePrimeSemigroup S) 1 =
      (1 : FiniteOperator S) := by
  unfold toeplitzMonomial
  rw [shiftOperator_one, shiftAdjoint_one]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Taking adjoints swaps the two indices of a standard monomial. -/
@[simp] theorem star_toeplitzMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    star (toeplitzMonomial hS m n) = toeplitzMonomial hS n m := by
  unfold toeplitzMonomial
  rw [star_mul]
  simp [shiftAdjoint, ContinuousLinearMap.star_eq_adjoint]

/-- The linear span of standard monomials is closed under multiplication. -/
theorem finiteToeplitzMonomialSpan_mul_mem
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {x y : FiniteOperator S}
    (hx : x ∈ finiteToeplitzMonomialSpan hS)
    (hy : y ∈ finiteToeplitzMonomialSpan hS) :
    x * y ∈ finiteToeplitzMonomialSpan hS := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨m, n, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨r, s, rfl⟩
          rw [toeplitzMonomial_mul_normalForm hS m n r s]
          exact toeplitzMonomial_mem_finiteToeplitzMonomialSpan hS _ _
      | zero =>
          simp
      | add y z _ _ hy hz =>
          have hadd :=
            (finiteToeplitzMonomialSpan hS).add_mem hy hz
          simpa [mul_add] using hadd
      | smul c y _ hy =>
          have hmem :
              c • (toeplitzMonomial hS m n * y) ∈
                finiteToeplitzMonomialSpan hS :=
            (finiteToeplitzMonomialSpan hS).smul_mem c hy
          simpa [mul_smul_comm] using hmem
  | zero =>
      simp
  | add x z _ _ hx hz =>
      have hadd :=
        (finiteToeplitzMonomialSpan hS).add_mem hx hz
      simpa [add_mul] using hadd
  | smul c x _ hx =>
      have hmem :
          c • (x * y) ∈ finiteToeplitzMonomialSpan hS :=
        (finiteToeplitzMonomialSpan hS).smul_mem c hx
      simpa [smul_mul_assoc] using hmem

/-- The linear span of standard monomials is closed under adjoints. -/
theorem finiteToeplitzMonomialSpan_star_mem
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {x : FiniteOperator S}
    (hx : x ∈ finiteToeplitzMonomialSpan hS) :
    star x ∈ finiteToeplitzMonomialSpan hS := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨m, n, rfl⟩
      rw [star_toeplitzMonomial]
      exact toeplitzMonomial_mem_finiteToeplitzMonomialSpan hS n m
  | zero =>
      simp
  | add x y _ _ hx hy =>
      have hadd :=
        (finiteToeplitzMonomialSpan hS).add_mem hx hy
      simpa using hadd
  | smul c x _ hx =>
      have hmem :
          star c • star x ∈ finiteToeplitzMonomialSpan hS :=
        (finiteToeplitzMonomialSpan hS).smul_mem (star c) hx
      simpa using hmem

/-- The identity operator belongs to the monomial span. -/
theorem one_mem_finiteToeplitzMonomialSpan
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (1 : FiniteOperator S) ∈ finiteToeplitzMonomialSpan hS := by
  rw [← toeplitzMonomial_one_one hS]
  exact toeplitzMonomial_mem_finiteToeplitzMonomialSpan hS 1 1

/-- Every element of the algebraic Toeplitz core lies in the linear span of
standard monomials. -/
theorem finiteToeplitzCore_le_monomialSpan
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (finiteToeplitzCore hS).toSubalgebra.toSubmodule ≤
      finiteToeplitzMonomialSpan hS := by
  intro x hx
  change x ∈ StarAlgebra.adjoin ℂ (primeShiftSet hS) at hx
  induction hx using StarAlgebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨p, rfl⟩
      change shiftOperator hS (primeSemigroupElement S p) ∈
        finiteToeplitzMonomialSpan hS
      have hmono :
          shiftOperator hS (primeSemigroupElement S p) =
            toeplitzMonomial hS (primeSemigroupElement S p) 1 := by
        unfold toeplitzMonomial
        rw [shiftAdjoint_one]
        simp
      rw [hmono]
      exact toeplitzMonomial_mem_finiteToeplitzMonomialSpan hS _ _
  | algebraMap c =>
      have h1 := one_mem_finiteToeplitzMonomialSpan hS
      have hc :
          c • (1 : FiniteOperator S) ∈ finiteToeplitzMonomialSpan hS :=
        (finiteToeplitzMonomialSpan hS).smul_mem c h1
      simpa [Algebra.smul_def] using hc
  | add x y _ _ hx hy =>
      exact add_mem hx hy
  | mul x y _ _ hx hy =>
      exact finiteToeplitzMonomialSpan_mul_mem hS hx hy
  | star x _ hx =>
      exact finiteToeplitzMonomialSpan_star_mem hS hx

/-- The linear span of standard monomials lies in the algebraic Toeplitz
core. -/
theorem finiteToeplitzMonomialSpan_le_core
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    finiteToeplitzMonomialSpan hS ≤
      (finiteToeplitzCore hS).toSubalgebra.toSubmodule := by
  rw [finiteToeplitzMonomialSpan, Submodule.span_le]
  intro x hx
  rcases hx with ⟨m, n, rfl⟩
  exact toeplitzMonomial_mem_finiteToeplitzCore hS m n

/-- The algebraic finite Toeplitz core is exactly the complex linear span of
the standard monomials. -/
theorem finiteToeplitzCore_toSubmodule_eq_monomialSpan
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (finiteToeplitzCore hS).toSubalgebra.toSubmodule =
      finiteToeplitzMonomialSpan hS := by
  apply le_antisymm
  · exact finiteToeplitzCore_le_monomialSpan hS
  · exact finiteToeplitzMonomialSpan_le_core hS

/-- Membership in the algebraic core is equivalent to membership in the
linear span of standard monomials. -/
theorem mem_finiteToeplitzCore_iff_mem_monomialSpan
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (x : FiniteOperator S) :
    x ∈ finiteToeplitzCore hS ↔ x ∈ finiteToeplitzMonomialSpan hS := by
  change x ∈ (finiteToeplitzCore hS).toSubalgebra.toSubmodule ↔ _
  rw [finiteToeplitzCore_toSubmodule_eq_monomialSpan hS]

end

end BostConnes
end BrickPileLean
