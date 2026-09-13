import BrickPileLean.BostConnes.FiniteToeplitzDynamics
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct

noncomputable section

/-- The real Boltzmann weight `n^{-β}` on the finite prime semigroup. -/
def gibbsWeight {S : Finset ℕ} (β : ℝ) (n : finitePrimeSemigroup S) : ℝ :=
  (n.1 : ℝ) ^ (-β)

lemma gibbsWeight_nonneg {S : Finset ℕ} (β : ℝ) (n : finitePrimeSemigroup S) :
    0 ≤ gibbsWeight β n := by
  exact Real.rpow_nonneg (Nat.cast_nonneg n.1) _

lemma gibbsWeight_pos
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (β : ℝ) (n : finitePrimeSemigroup S) :
    0 < gibbsWeight β n := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast finitePrimeSemigroup_coe_pos hS n

/-- The Gibbs weights are summable at positive inverse temperature. -/
theorem gibbsWeight_summable
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    Summable (gibbsWeight (S := S) β) := by
  exact lambdaWeight_summable hS hβ

/-- The finite partition function is strictly positive at positive inverse temperature. -/
theorem lambdaPartition_pos
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    0 < lambdaPartition S β := by
  unfold lambdaPartition
  exact (lambdaWeight_summable hS hβ).tsum_pos
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n.1) _)
    (1 : finitePrimeSemigroup S)
    (by simp)

/-- The normalized Gibbs probability weight on `Λ_S`. -/
def gibbsProbabilityWeight
    (S : Finset ℕ) (β : ℝ) (n : finitePrimeSemigroup S) : ℝ :=
  gibbsWeight β n / lambdaPartition S β

lemma gibbsProbabilityWeight_nonneg
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (n : finitePrimeSemigroup S) :
    0 ≤ gibbsProbabilityWeight S β n := by
  exact div_nonneg (gibbsWeight_nonneg β n) (lambdaPartition_pos hS hβ).le

/-- The normalized Gibbs weights form a summable probability distribution. -/
theorem gibbsProbabilityWeight_summable
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    Summable (gibbsProbabilityWeight S β) := by
  unfold gibbsProbabilityWeight
  exact (gibbsWeight_summable hS hβ).div_const _

/-- The normalized Gibbs weights have total mass one. -/
theorem tsum_gibbsProbabilityWeight
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    (∑' n : finitePrimeSemigroup S, gibbsProbabilityWeight S β n) = 1 := by
  unfold gibbsProbabilityWeight gibbsWeight lambdaPartition
  rw [tsum_div_const]
  exact div_self (lambdaPartition_pos hS hβ).ne'

/-- The rank-one projection onto the canonical basis vector `e_n`. -/
def basisProjection (S : Finset ℕ) (n : finitePrimeSemigroup S) : FiniteOperator S :=
  InnerProductSpace.rankOne ℂ (basisVector S n) (basisVector S n)

@[simp] theorem norm_basisVector (S : Finset ℕ) (n : finitePrimeSemigroup S) :
    ‖basisVector S n‖ = 1 := by
  simp [basisVector]

@[simp] theorem norm_basisProjection (S : Finset ℕ) (n : finitePrimeSemigroup S) :
    ‖basisProjection S n‖ = 1 := by
  simp [basisProjection]

/-- A basis projection selects exactly its own canonical basis vector. -/
theorem basisProjection_apply_basisVector
    (S : Finset ℕ) (n m : finitePrimeSemigroup S) :
    basisProjection S n (basisVector S m) =
      if n = m then basisVector S m else 0 := by
  classical
  unfold basisProjection basisVector
  rw [InnerProductSpace.rankOne_apply]
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h : n = m
  · subst m
    simp
  · simp [h]

/-- The `n`th rank-one term in the diagonal Gibbs operator. -/
def gibbsOperatorTerm
    {S : Finset ℕ} (β : ℝ) (n : finitePrimeSemigroup S) : FiniteOperator S :=
  ((gibbsWeight β n : ℝ) : ℂ) • basisProjection S n

/-- The rank-one Gibbs expansion is absolutely summable in operator norm. -/
theorem gibbsOperatorTerm_summable
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    Summable (gibbsOperatorTerm (S := S) β) := by
  apply Summable.of_norm
  simpa [gibbsOperatorTerm, norm_smul, Complex.norm_real, abs_of_nonneg,
    gibbsWeight_nonneg] using gibbsWeight_summable hS hβ

/-- The diagonal Gibbs operator `D_β = Σ n^{-β} |e_n⟩⟨e_n|`. -/
def gibbsOperator (S : Finset ℕ) (β : ℝ) : FiniteOperator S :=
  ∑' n : finitePrimeSemigroup S, gibbsOperatorTerm β n

/-- Evaluation of bounded operators at a fixed vector, as a continuous linear map. -/
def operatorEval (S : Finset ℕ) (x : FiniteHilbertSpace S) :
    FiniteOperator S →L[ℂ] FiniteHilbertSpace S :=
  LinearMap.mkContinuous
    { toFun := fun T => T x
      map_add' := by intro T U; simp
      map_smul' := by intro c T; simp }
    ‖x‖
    (fun T => by
      simpa [mul_comm] using T.le_opNorm x)

@[simp] theorem operatorEval_apply
    (S : Finset ℕ) (x : FiniteHilbertSpace S) (T : FiniteOperator S) :
    operatorEval S x T = T x :=
  rfl

/-- The Gibbs operator has the expected diagonal action on the canonical basis. -/
theorem gibbsOperator_basisVector
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m : finitePrimeSemigroup S) :
    gibbsOperator S β (basisVector S m) =
      ((gibbsWeight β m : ℝ) : ℂ) • basisVector S m := by
  have hs := gibbsOperatorTerm_summable hS hβ
  have hmap := (operatorEval S (basisVector S m)).map_tsum hs
  change operatorEval S (basisVector S m) (gibbsOperator S β) = _
  rw [hmap]
  rw [tsum_eq_single m]
  · simp [gibbsOperatorTerm, basisProjection_apply_basisVector]
  · intro n hnm
    simp [gibbsOperatorTerm, basisProjection_apply_basisVector, hnm]

/-- The basis-diagonal sum of `D_β`; this is the trace once trace-class theory is available. -/
def gibbsDiagonalSum (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∑' n : finitePrimeSemigroup S, gibbsWeight β n

@[simp] theorem gibbsDiagonalSum_eq_lambdaPartition (S : Finset ℕ) (β : ℝ) :
    gibbsDiagonalSum S β = lambdaPartition S β :=
  rfl

/-- The diagonal Gibbs normalization is the finite Euler product. -/
theorem gibbsDiagonalSum_eq_finiteEulerProduct
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    gibbsDiagonalSum S β = finiteEulerProduct S β := by
  rw [gibbsDiagonalSum_eq_lambdaPartition]
  exact lambdaPartition_eq_finiteEulerProduct_of_prime hS hβ

end

end BostConnes
end BrickPileLean
