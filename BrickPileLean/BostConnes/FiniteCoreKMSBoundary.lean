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
  unfold finiteToeplitzExpansionEvalA
  set_option synthInstance.maxHeartbeats 100000 in
    exact Finsupp.sum_add_index (by simp) (by simp [add_smul])

@[simp] theorem finiteToeplitzExpansionEvalA_single
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (i : finiteToeplitzMonomialIndex S) (a : ℂ) :
    finiteToeplitzExpansionEvalA hS (Finsupp.single i a) =
      a • finiteToeplitzMonomialFamilyA hS i := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
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
  unfold finiteToeplitzExpansionKMSBoundaryA
  set_option synthInstance.maxHeartbeats 100000 in
    exact Finsupp.sum_add_index (by simp) (by simp [add_smul])

@[simp] theorem finiteToeplitzExpansionKMSBoundaryA_single
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (i : finiteToeplitzMonomialIndex S) (a : ℂ) :
    finiteToeplitzExpansionKMSBoundaryA hS β (Finsupp.single i a) =
      a • finiteToeplitzKMSBoundaryFamilyA hS β i := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [finiteToeplitzExpansionKMSBoundaryA]

/-- Pull a scalar through multiplication in the second factor and then
through the Gibbs functional. -/
theorem finiteGibbsState_mul_smul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y : finiteToeplitzAlgebra hS) (a : ℂ) :
    finiteGibbsState hS hβ (x * (a • y)) =
      a * finiteGibbsState hS hβ (x * y) := by
  rw [mul_smul_comm, map_smul]
  rfl

/-- Pull a scalar through multiplication in the first factor and then
through the Gibbs functional. -/
theorem finiteGibbsState_smul_mul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y : finiteToeplitzAlgebra hS) (a : ℂ) :
    finiteGibbsState hS hβ ((a • x) * y) =
      a * finiteGibbsState hS hβ (x * y) := by
  rw [smul_mul_assoc, map_smul]
  rfl

/-- Pull two scalars out of a product before applying the Gibbs functional. -/
theorem finiteGibbsState_smul_mul_smul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y : finiteToeplitzAlgebra hS) (a b : ℂ) :
    finiteGibbsState hS hβ ((a • x) * (b • y)) =
      (a * b) * finiteGibbsState hS hβ (x * y) := by
  rw [smul_mul_smul, map_smul]
  rfl

/-- The Gibbs functional distributes over a sum in the right factor. -/
theorem finiteGibbsState_mul_add
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y z : finiteToeplitzAlgebra hS) :
    finiteGibbsState hS hβ (x * (y + z)) =
      finiteGibbsState hS hβ (x * y) +
        finiteGibbsState hS hβ (x * z) := by
  rw [mul_add, map_add]

/-- The Gibbs functional distributes over a sum in the left factor. -/
theorem finiteGibbsState_add_mul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x y z : finiteToeplitzAlgebra hS) :
    finiteGibbsState hS hβ ((x + y) * z) =
      finiteGibbsState hS hβ (x * z) +
        finiteGibbsState hS hβ (y * z) := by
  rw [add_mul, map_add]

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
    finiteGibbsState_kms_toeplitzMonomials
      (S := S) (β := β) hS hβ m n r s
  calc
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          (a • finiteToeplitzMonomial hS r s)) =
      a * finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          finiteToeplitzMonomial hS r s) :=
      finiteGibbsState_mul_smul
        (S := S) (β := β) hS hβ
        (finiteToeplitzMonomial hS m n)
        (finiteToeplitzMonomial hS r s) a
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
            finiteToeplitzMonomial hS m n)) :=
      (finiteGibbsState_smul_mul_smul
        (S := S) (β := β) hS hβ
        (finiteToeplitzMonomial hS r s)
        (finiteToeplitzMonomial hS m n)
        a (finiteToeplitzMonomialKMSWeight β (m, n))).symm

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
      let M : finiteToeplitzAlgebra hS :=
        finiteToeplitzMonomial hS m n
      let N : finiteToeplitzAlgebra hS :=
        finiteToeplitzMonomial hS r s
      let E : finiteToeplitzAlgebra hS :=
        finiteToeplitzExpansionEvalA hS d
      let W : ℂ := finiteToeplitzMonomialKMSWeight β (m, n)
      have hEval :
          finiteToeplitzExpansionEvalA hS (Finsupp.single (r, s) a + d) =
            a • N + E := by
        rw [finiteToeplitzExpansionEvalA_add,
          finiteToeplitzExpansionEvalA_single]
        rfl
      have hsingle :
          finiteGibbsState hS hβ (M * (a • N)) =
            finiteGibbsState hS hβ ((a • N) * (W • M)) := by
        exact finiteGibbsState_kms_toeplitzMonomial_smul
          (S := S) (β := β) hS hβ m n r s a
      have ih' :
          finiteGibbsState hS hβ (M * E) =
            finiteGibbsState hS hβ (E * (W • M)) := by
        exact ih
      calc
        finiteGibbsState hS hβ
            (M * finiteToeplitzExpansionEvalA hS
              (Finsupp.single (r, s) a + d)) =
            finiteGibbsState hS hβ (M * (a • N + E)) := by
          exact congrArg
            (fun X : finiteToeplitzAlgebra hS =>
              finiteGibbsState hS hβ (M * X)) hEval
        _ =
            finiteGibbsState hS hβ (M * (a • N)) +
              finiteGibbsState hS hβ (M * E) :=
          finiteGibbsState_mul_add
            (S := S) (β := β) hS hβ M (a • N) E
        _ = finiteGibbsState hS hβ ((a • N) * (W • M)) +
              finiteGibbsState hS hβ (E * (W • M)) := by
            exact congrArg₂ (fun u v : ℂ => u + v) hsingle ih'
        _ = finiteGibbsState hS hβ ((a • N + E) * (W • M)) :=
          (finiteGibbsState_add_mul
            (S := S) (β := β) hS hβ (a • N) E (W • M)).symm
        _ = finiteGibbsState hS hβ
            (finiteToeplitzExpansionEvalA hS
              (Finsupp.single (r, s) a + d) * (W • M)) := by
          exact congrArg
            (fun X : finiteToeplitzAlgebra hS =>
              finiteGibbsState hS hβ (X * (W • M))) hEval.symm
        _ = finiteGibbsState hS hβ
            (finiteToeplitzExpansionEvalA hS
              (Finsupp.single (r, s) a + d) *
              (finiteToeplitzMonomialKMSWeight β (m, n) •
                finiteToeplitzMonomial hS m n)) := by
          rfl

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
      (S := S) (β := β) hS hβ m n d
  calc
    finiteGibbsState hS hβ
        ((a • finiteToeplitzMonomial hS m n) *
          finiteToeplitzExpansionEvalA hS d) =
      a * finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n *
          finiteToeplitzExpansionEvalA hS d) :=
      finiteGibbsState_smul_mul
        (S := S) (β := β) hS hβ
        (finiteToeplitzMonomial hS m n)
        (finiteToeplitzExpansionEvalA hS d) a
    _ = a * finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          (finiteToeplitzMonomialKMSWeight β (m, n) •
            finiteToeplitzMonomial hS m n)) := by
          rw [h]
    _ = finiteGibbsState hS hβ
        (finiteToeplitzExpansionEvalA hS d *
          (a •
            (finiteToeplitzMonomialKMSWeight β (m, n) •
              finiteToeplitzMonomial hS m n))) :=
      (finiteGibbsState_mul_smul
        (S := S) (β := β) hS hβ
        (finiteToeplitzExpansionEvalA hS d)
        (finiteToeplitzMonomialKMSWeight β (m, n) •
          finiteToeplitzMonomial hS m n) a).symm

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
      let M : finiteToeplitzAlgebra hS :=
        finiteToeplitzMonomial hS m n
      let E : finiteToeplitzAlgebra hS :=
        finiteToeplitzExpansionEvalA hS c
      let D : finiteToeplitzAlgebra hS :=
        finiteToeplitzExpansionEvalA hS d
      let B : finiteToeplitzAlgebra hS :=
        finiteToeplitzExpansionKMSBoundaryA hS β c
      let W : ℂ := finiteToeplitzMonomialKMSWeight β (m, n)
      have hEval :
          finiteToeplitzExpansionEvalA hS (Finsupp.single (m, n) a + c) =
            a • M + E := by
        rw [finiteToeplitzExpansionEvalA_add,
          finiteToeplitzExpansionEvalA_single]
        rfl
      have hBoundary :
          finiteToeplitzExpansionKMSBoundaryA hS β
              (Finsupp.single (m, n) a + c) =
            a • (W • M) + B := by
        rw [finiteToeplitzExpansionKMSBoundaryA_add,
          finiteToeplitzExpansionKMSBoundaryA_single]
        rfl
      have hsingle :
          finiteGibbsState hS hβ ((a • M) * D) =
            finiteGibbsState hS hβ (D * (a • (W • M))) := by
        exact finiteGibbsState_kms_smul_toeplitzMonomial_expansion
          (S := S) (β := β) hS hβ m n a d
      have ih' :
          finiteGibbsState hS hβ (E * D) =
            finiteGibbsState hS hβ (D * B) := by
        exact ih
      calc
        finiteGibbsState hS hβ
            (finiteToeplitzExpansionEvalA hS
              (Finsupp.single (m, n) a + c) * D) =
            finiteGibbsState hS hβ ((a • M + E) * D) := by
          exact congrArg
            (fun X : finiteToeplitzAlgebra hS =>
              finiteGibbsState hS hβ (X * D)) hEval
        _ =
            finiteGibbsState hS hβ ((a • M) * D) +
              finiteGibbsState hS hβ (E * D) :=
          finiteGibbsState_add_mul
            (S := S) (β := β) hS hβ (a • M) E D
        _ = finiteGibbsState hS hβ (D * (a • (W • M))) +
              finiteGibbsState hS hβ (D * B) := by
            exact congrArg₂ (fun u v : ℂ => u + v) hsingle ih'
        _ = finiteGibbsState hS hβ (D * (a • (W • M) + B)) :=
          (finiteGibbsState_mul_add
            (S := S) (β := β) hS hβ D (a • (W • M)) B).symm
        _ = finiteGibbsState hS hβ
            (D * finiteToeplitzExpansionKMSBoundaryA hS β
              (Finsupp.single (m, n) a + c)) := by
          exact congrArg
            (fun X : finiteToeplitzAlgebra hS =>
              finiteGibbsState hS hβ (D * X)) hBoundary.symm

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
