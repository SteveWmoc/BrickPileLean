import BrickPileLean.BostConnes.FiniteCoreExpansion

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- Imaginary-time KMS weight attached to the standard monomial `V_m V_n*`. -/
def finiteToeplitzMonomialKMSWeight
    {S : Finset ℕ} (β : ℝ) (i : finiteToeplitzMonomialIndex S) : ℂ :=
  (((gibbsWeight β i.1 : ℝ) : ℂ) /
    ((gibbsWeight β i.2 : ℝ) : ℂ))

/-- The standard monomial family after multiplication by its KMS boundary
weight. -/
def finiteToeplitzKMSBoundaryFamilyA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (i : finiteToeplitzMonomialIndex S) : finiteToeplitzAlgebra hS :=
  finiteToeplitzMonomialKMSWeight β i •
    finiteToeplitzMonomialFamilyA hS i

/-- Evaluate a finitely supported monomial expansion after applying the
termwise KMS boundary weight. -/
def finiteToeplitzExpansionKMSBoundaryA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (c : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzAlgebra hS :=
  c.sum fun i a => a • finiteToeplitzKMSBoundaryFamilyA hS β i

@[simp] theorem finiteToeplitzExpansionEvalA_zero
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    finiteToeplitzExpansionEvalA hS
      (0 : finiteToeplitzMonomialIndex S →₀ ℂ) = 0 := by
  simp [finiteToeplitzExpansionEvalA]

@[simp] theorem finiteToeplitzExpansionEvalA_add
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (c d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzExpansionEvalA hS (c + d) =
      finiteToeplitzExpansionEvalA hS c +
        finiteToeplitzExpansionEvalA hS d := by
  classical
  simp [finiteToeplitzExpansionEvalA, Finsupp.sum_add_index]

@[simp] theorem finiteToeplitzExpansionEvalA_single
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (i : finiteToeplitzMonomialIndex S) (a : ℂ) :
    finiteToeplitzExpansionEvalA hS (Finsupp.single i a) =
      a • finiteToeplitzMonomialFamilyA hS i := by
  classical
  simp [finiteToeplitzExpansionEvalA]

@[simp] theorem finiteToeplitzExpansionKMSBoundaryA_zero
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ) :
    finiteToeplitzExpansionKMSBoundaryA hS β
      (0 : finiteToeplitzMonomialIndex S →₀ ℂ) = 0 := by
  simp [finiteToeplitzExpansionKMSBoundaryA]

@[simp] theorem finiteToeplitzExpansionKMSBoundaryA_add
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (c d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteToeplitzExpansionKMSBoundaryA hS β (c + d) =
      finiteToeplitzExpansionKMSBoundaryA hS β c +
        finiteToeplitzExpansionKMSBoundaryA hS β d := by
  classical
  simp [finiteToeplitzExpansionKMSBoundaryA, Finsupp.sum_add_index]

@[simp] theorem finiteToeplitzExpansionKMSBoundaryA_single
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (i : finiteToeplitzMonomialIndex S) (a : ℂ) :
    finiteToeplitzExpansionKMSBoundaryA hS β (Finsupp.single i a) =
      a • finiteToeplitzKMSBoundaryFamilyA hS β i := by
  classical
  simp [finiteToeplitzExpansionKMSBoundaryA]

/-- Scalar-multiple version of the monomial KMS boundary identity. -/
theorem finiteGibbsState_kms_toeplitzMonomial_smul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n r s : finitePrimeSemigroup S) (a : ℂ) :
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          (a • finiteToeplitzMonomial hS r s)) =
      finiteGibbsState hS hβ
        ((a • finiteToeplitzMonomial hS r s) *
          (finiteToeplitzMonomialKMSWeight β (m, n) •
            finiteToeplitzMonomial hS m n)) := by
  have h :=
    finiteGibbsState_kms_toeplitzMonomials hS hβ m n r s
  calc
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          (a • finiteToeplitzMonomial hS r s)) =
      a * finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          finiteToeplitzMonomial hS r s) := by
            rw [mul_smul_comm, map_smul]
            rfl
    _ = a *
        (finiteToeplitzMonomialKMSWeight β (m, n) *
          finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS r s *
              finiteToeplitzMonomial hS m n)) := by
          rw [h]
          rfl
    _ = (a * finiteToeplitzMonomialKMSWeight β (m, n)) *
        finiteGibbsState hS hβ
          (finiteToeplitzMonomial hS r s *
            finiteToeplitzMonomial hS m n) := by
          ring
    _ = finiteGibbsState hS hβ
        ((a • finiteToeplitzMonomial hS r s) *
          (finiteToeplitzMonomialKMSWeight β (m, n) •
            finiteToeplitzMonomial hS m n)) := by
          rw [smul_mul_smul, map_smul]
          simp [smul_eq_mul]

/-- KMS boundary identity for one standard monomial against an arbitrary
finite monomial expansion. -/
theorem finiteGibbsState_kms_toeplitzMonomial_expansion
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S)
    (d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          finiteToeplitzExpansionEvalA hS d) =
      finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          (finiteToeplitzMonomialKMSWeight β (m, n) •
            finiteToeplitzMonomial hS m n)) := by
  classical
  induction d using Finsupp.induction with
  | zero =>
      simp
  | single_add i a d hi ha ih =>
      rcases i with ⟨r, s⟩
      rw [finiteToeplitzExpansionEvalA_add,
        finiteToeplitzExpansionEvalA_single]
      rw [mul_add, add_mul, map_add, map_add]
      congr 1
      exact finiteGibbsState_kms_toeplitzMonomial_smul
        hS hβ m n r s a

/-- Scalar-multiple version of the monomial-versus-expansion KMS identity. -/
theorem finiteGibbsState_kms_smul_toeplitzMonomial_expansion
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S) (a : ℂ)
    (d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteGibbsState hS hβ
        ((a • finiteToeplitzMonomial hS m n) *
          finiteToeplitzExpansionEvalA hS d) =
      finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          (a •
            (finiteToeplitzMonomialKMSWeight β (m, n) •
              finiteToeplitzMonomial hS m n))) := by
  have h :=
    finiteGibbsState_kms_toeplitzMonomial_expansion
      hS hβ m n d
  calc
    finiteGibbsState hS hβ
        ((a • finiteToeplitzMonomial hS m n) *
          finiteToeplitzExpansionEvalA hS d) =
      a * finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          finiteToeplitzExpansionEvalA hS d) := by
            rw [smul_mul_assoc, map_smul]
            rfl
    _ = a * finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          (finiteToeplitzMonomialKMSWeight β (m, n) •
            finiteToeplitzMonomial hS m n)) := by
          rw [h]
    _ = finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          (a •
            (finiteToeplitzMonomialKMSWeight β (m, n) •
              finiteToeplitzMonomial hS m n))) := by
          rw [mul_smul_comm, map_smul]
          rfl

/-- KMS boundary identity for two arbitrary finite monomial expansions. -/
theorem finiteGibbsState_kms_expansions
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (c d : finiteToeplitzMonomialIndex S →₀ ℂ) :
    finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS c *
          finiteToeplitzExpansionEvalA hS d) =
      finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          finiteToeplitzExpansionKMSBoundaryA hS β c) := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simp
  | single_add i a c hi ha ih =>
      rcases i with ⟨m, n⟩
      rw [finiteToeplitzExpansionEvalA_add,
        finiteToeplitzExpansionEvalA_single,
        finiteToeplitzExpansionKMSBoundaryA_add,
        finiteToeplitzExpansionKMSBoundaryA_single]
      rw [add_mul, mul_add, map_add, map_add]
      congr 1
      exact finiteGibbsState_kms_smul_toeplitzMonomial_expansion
        hS hβ m n a d

/-- The chosen KMS boundary representative of an algebraic-core element,
obtained by weighting a chosen finite monomial expansion termwise. -/
def finiteToeplitzCoreKMSBoundaryA
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (x : finiteToeplitzCore hS) : finiteToeplitzAlgebra hS :=
  finiteToeplitzExpansionKMSBoundaryA hS β
    (finiteToeplitzCoreExpansion hS x)

/-- Core-level KMS boundary identity, expressed using the chosen finite
monomial expansion of the first core element. -/
theorem finiteGibbsState_kms_core_boundary
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y : finiteToeplitzCore hS) :
    finiteGibbsState hS hβ
        (finiteToeplitzCoreToAlgebra hS x *
          finiteToeplitzCoreToAlgebra hS y) =
      finiteGibbsState hS hβ
        (finiteToeplitzCoreToAlgebra hS y *
          finiteToeplitzCoreKMSBoundaryA hS β x) := by
  rw [← finiteToeplitzCoreExpansion_evalA hS x,
    ← finiteToeplitzCoreExpansion_evalA hS y]
  exact finiteGibbsState_kms_expansions hS hβ
    (finiteToeplitzCoreExpansion hS x)
    (finiteToeplitzCoreExpansion hS y)

end

end BostConnes
end BrickPileLean
