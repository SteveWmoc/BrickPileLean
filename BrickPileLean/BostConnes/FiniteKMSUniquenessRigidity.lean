import BrickPileLean.BostConnes.FiniteCoreComplexTime

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- A normalized bounded functional satisfying the KMS boundary identity on
the dense algebraic Toeplitz core. -/
def IsFiniteToeplitzCoreKMS
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ)
    (φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ) : Prop :=
  φ 1 = 1 ∧
    ∀ x y : finiteToeplitzCore hS,
      φ (finiteToeplitzCoreToAlgebra hS x *
          finiteToeplitzCoreToAlgebra hS y) =
        φ (finiteToeplitzCoreToAlgebra hS y *
          finiteToeplitzCoreComplexTimeA hS
            ((β : ℂ) * Complex.I) x)

/-- The Gibbs functional already constructed in the finite-prime model
satisfies the normalized core KMS condition. -/
theorem finiteGibbsStateCLM_isFiniteToeplitzCoreKMS
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    IsFiniteToeplitzCoreKMS hS β (finiteGibbsStateCLM hS hβ) := by
  constructor
  · change gibbsExpectation S β (1 : FiniteOperator S) = 1
    exact gibbsExpectation_one hS hβ
  · intro x y
    exact finiteGibbsState_kms_core_complexTime hS hβ x y

/-- Inclusion of a standard core monomial into the completed algebra is the
same standard Toeplitz monomial. -/
@[simp] theorem finiteToeplitzCoreToAlgebra_monomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    finiteToeplitzCoreToAlgebra hS
        (finiteToeplitzCoreMonomial hS m n) =
      finiteToeplitzMonomial hS m n := by
  apply Subtype.ext
  rfl

/-- Matching middle indices also cancel inside the completed finite Toeplitz
algebra. -/
@[simp] theorem finiteToeplitzMonomial_mul_matching
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n s : finitePrimeSemigroup S) :
    finiteToeplitzMonomial hS m n *
        finiteToeplitzMonomial hS n s =
      finiteToeplitzMonomial hS m s := by
  apply Subtype.ext
  exact toeplitzMonomial_mul_matching hS m n s

/-- The completed-algebra monomial indexed by (1,1) is the identity. -/
@[simp] theorem finiteToeplitzMonomial_one_one
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    finiteToeplitzMonomial hS
        (1 : finitePrimeSemigroup S) 1 = 1 := by
  apply Subtype.ext
  exact toeplitzMonomial_one_one hS

/-- Complex-time continuation of a single core monomial is just multiplication
by its scalar complex-time phase. -/
theorem finiteToeplitzCoreComplexTimeA_monomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (z : ℂ) (m n : finitePrimeSemigroup S) :
    finiteToeplitzCoreComplexTimeA hS z
        (finiteToeplitzCoreMonomial hS m n) =
      toeplitzMonomialComplexPhase z m n •
        finiteToeplitzMonomial hS m n := by
  let c : finiteToeplitzMonomialIndex S →₀ ℂ :=
    Finsupp.single (m, n) 1
  have hc :
      finiteToeplitzExpansionEvalA hS c =
        finiteToeplitzCoreToAlgebra hS
          (finiteToeplitzCoreMonomial hS m n) := by
    dsimp [c]
    rw [finiteToeplitzExpansionEvalA_single]
    simp [finiteToeplitzMonomialFamilyA]
  rw [← finiteToeplitzExpansionComplexTimeA_eq_core
    hS z (finiteToeplitzCoreMonomial hS m n) c hc]
  dsimp [c]
  simp [finiteToeplitzExpansionComplexTimeA,
    finiteToeplitzComplexTimeFamilyA,
    finiteToeplitzMonomialFamilyA]

/-- The core KMS condition gives the expected weighted boundary identity on
standard monomials for an arbitrary normalized bounded KMS functional. -/
theorem IsFiniteToeplitzCoreKMS.monomials
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    (m n r s : finitePrimeSemigroup S) :
    φ (finiteToeplitzMonomial hS m n *
        finiteToeplitzMonomial hS r s) =
      φ (finiteToeplitzMonomial hS r s *
        (finiteToeplitzMonomialKMSWeight β (m, n) •
          finiteToeplitzMonomial hS m n)) := by
  have h := hφ.2
    (finiteToeplitzCoreMonomial hS m n)
    (finiteToeplitzCoreMonomial hS r s)
  rw [finiteToeplitzCoreToAlgebra_monomial,
    finiteToeplitzCoreToAlgebra_monomial,
    finiteToeplitzCoreComplexTimeA_monomial] at h
  rw [← finiteToeplitzMonomialKMSWeight_eq_complexPhase hS β m n] at h
  exact h

/-- Distinct semigroup elements have distinct Gibbs weights at positive
inverse temperature. -/
theorem gibbsWeight_ne_of_ne
    {S : Finset ℕ} {β : ℝ}
    (_hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n) :
    gibbsWeight β m ≠ gibbsWeight β n := by
  intro h
  unfold gibbsWeight at h
  have hcast :
      (((m : ℕ) : ℝ)) = (((n : ℕ) : ℝ)) := by
    exact (Real.rpow_left_inj
      (Nat.cast_nonneg (m : ℕ))
      (Nat.cast_nonneg (n : ℕ))
      (neg_ne_zero.mpr hβ.ne')).1 h
  have hnat : (m : ℕ) = (n : ℕ) := by
    exact_mod_cast hcast
  exact hmn (Subtype.ext hnat)

/-- For distinct monomials, the KMS boundary scalar is not one. -/
theorem finiteToeplitzMonomialKMSWeight_ne_one_of_ne
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n) :
    finiteToeplitzMonomialKMSWeight β (m, n) ≠ 1 := by
  intro h
  unfold finiteToeplitzMonomialKMSWeight at h
  have hn : ((gibbsWeight β n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (gibbsWeight_pos hS β n).ne'
  have heqC :
      ((gibbsWeight β m : ℝ) : ℂ) =
        ((gibbsWeight β n : ℝ) : ℂ) :=
    (div_eq_one_iff_eq hn).1 h
  have heqR : gibbsWeight β m = gibbsWeight β n :=
    Complex.ofReal_injective heqC
  exact gibbsWeight_ne_of_ne hS hβ hmn heqR

/-- Any normalized bounded core-KMS functional vanishes on off-diagonal
standard Toeplitz monomials. -/
theorem IsFiniteToeplitzCoreKMS.offDiagonal
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n) :
    φ (finiteToeplitzMonomial hS m n) = 0 := by
  have h := hφ.monomials hS m n 1 1
  simp at h
  let w : ℂ := finiteToeplitzMonomialKMSWeight β (m, n)
  have hw : w ≠ 1 := by
    exact finiteToeplitzMonomialKMSWeight_ne_one_of_ne hS hβ hmn
  have hrel :
      φ (finiteToeplitzMonomial hS m n) =
        w * φ (finiteToeplitzMonomial hS m n) := by
    simpa [w, smul_eq_mul] using h
  have hz :
      (1 - w) * φ (finiteToeplitzMonomial hS m n) = 0 := by
    calc
      (1 - w) * φ (finiteToeplitzMonomial hS m n) =
          φ (finiteToeplitzMonomial hS m n) -
            w * φ (finiteToeplitzMonomial hS m n) := by
              ring
      _ = 0 := sub_eq_zero.mpr hrel
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (Ne.symm hw))

/-- Any normalized bounded core-KMS functional has the forced Gibbs value on
the diagonal range projection V_m V_m*. -/
theorem IsFiniteToeplitzCoreKMS.diagonal
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p)
    {φ : finiteToeplitzAlgebra hS →L[ℂ] ℂ}
    (hφ : IsFiniteToeplitzCoreKMS hS β φ)
    (m : finitePrimeSemigroup S) :
    φ (finiteToeplitzMonomial hS m m) =
      ((gibbsWeight β m : ℝ) : ℂ) := by
  have h := hφ.monomials hS
    m 1 (1 : finitePrimeSemigroup S) m
  have hone : φ 1 = 1 := hφ.1
  simpa [finiteToeplitzMonomialKMSWeight, gibbsWeight, hone,
    smul_eq_mul] using h

end

end BostConnes
end BrickPileLean
