import BrickPileLean.BostConnes.FiniteGibbsWeight

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct

noncomputable section

/-- Gibbs weights are multiplicative on the finite prime semigroup. -/
@[simp] theorem gibbsWeight_mul
    {S : Finset ℕ} (β : ℝ) (m n : finitePrimeSemigroup S) :
    gibbsWeight β (m * n) = gibbsWeight β m * gibbsWeight β n := by
  unfold gibbsWeight
  change (((m.1 * n.1 : ℕ) : ℝ) ^ (-β)) =
    (m.1 : ℝ) ^ (-β) * (n.1 : ℝ) ^ (-β)
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m.1) (Nat.cast_nonneg n.1)]

/-- Left multiplication scales normalized Gibbs weights by the weight of the multiplier. -/
@[simp] theorem gibbsProbabilityWeight_mul_left
    {S : Finset ℕ} (β : ℝ)
    (m n : finitePrimeSemigroup S) :
    gibbsProbabilityWeight S β (m * n) =
      gibbsWeight β m * gibbsProbabilityWeight S β n := by
  unfold gibbsProbabilityWeight
  rw [gibbsWeight_mul]
  ring

/-- Right multiplication by a nonzero semigroup element is injective. -/
theorem rightMul_injective
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (r : finitePrimeSemigroup S) :
    Function.Injective (fun n : finitePrimeSemigroup S => n * r) := by
  intro a b hab
  apply Subtype.ext
  apply Nat.mul_right_cancel (finitePrimeSemigroup_coe_pos hS r)
  exact congrArg (fun x : finitePrimeSemigroup S => (x : ℕ)) hab

/-- Left multiplication identifies `Λ_S` with the elements divisible by `m`. -/
def leftMulEquivMultiples
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    finitePrimeSemigroup S ≃ {k : finitePrimeSemigroup S // m ∣ k} where
  toFun r := ⟨m * r, ⟨r, rfl⟩⟩
  invFun k := Classical.choose k.2
  left_inv r := by
    apply leftMul_injective hS m
    exact (Classical.choose_spec
      (show m ∣ m * r from ⟨r, rfl⟩)).symm
  right_inv k := by
    apply Subtype.ext
    exact (Classical.choose_spec k.2).symm

/-- One term in the Gibbs expectation of a bounded operator. -/
def gibbsExpectationTerm
    (S : Finset ℕ) (β : ℝ) (a : FiniteOperator S)
    (k : finitePrimeSemigroup S) : ℂ :=
  ((gibbsProbabilityWeight S β k : ℝ) : ℂ) *
    inner ℂ (basisVector S k) (a (basisVector S k))

/-- The Gibbs expectation series converges absolutely for positive inverse temperature. -/
theorem gibbsExpectationTerm_summable
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (a : FiniteOperator S) :
    Summable (gibbsExpectationTerm S β a) := by
  have hp := gibbsProbabilityWeight_summable hS hβ
  have hdom : Summable (fun k : finitePrimeSemigroup S =>
      gibbsProbabilityWeight S β k * ‖a‖) :=
    Summable.mul_right ‖a‖ hp
  refine Summable.of_norm_bounded hdom ?_
  intro k
  have hinner :
      ‖inner ℂ (basisVector S k) (a (basisVector S k))‖ ≤ ‖a‖ := by
    calc
      ‖inner ℂ (basisVector S k) (a (basisVector S k))‖ ≤
          ‖basisVector S k‖ * ‖a (basisVector S k)‖ :=
        norm_inner_le_norm _ _
      _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        · simp
        · exact a.le_opNorm (basisVector S k)
      _ = ‖a‖ := by simp
  calc
    ‖gibbsExpectationTerm S β a k‖ =
        gibbsProbabilityWeight S β k *
          ‖inner ℂ (basisVector S k) (a (basisVector S k))‖ := by
      simp [gibbsExpectationTerm, gibbsProbabilityWeight_nonneg hS hβ]
    _ ≤ gibbsProbabilityWeight S β k * ‖a‖ :=
      mul_le_mul_of_nonneg_left hinner
        (gibbsProbabilityWeight_nonneg hS hβ k)

/-- The normalized Gibbs expectation on bounded operators, defined by its basis-diagonal sum. -/
def gibbsExpectation
    (S : Finset ℕ) (β : ℝ) (a : FiniteOperator S) : ℂ :=
  ∑' k : finitePrimeSemigroup S, gibbsExpectationTerm S β a k

/-- The standard Toeplitz monomial `V_m V_n*`. -/
def toeplitzMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) : FiniteOperator S :=
  shiftOperator hS m * shiftAdjoint hS n

/-- Every standard monomial belongs to the finite Toeplitz algebra. -/
def finiteToeplitzMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) : finiteToeplitzAlgebra hS :=
  ⟨toeplitzMonomial hS m n,
    mul_mem (shiftOperator_mem_finiteToeplitzAlgebra hS m)
      (shiftAdjoint_mem_finiteToeplitzAlgebra hS n)⟩

/-- The diagonal matrix coefficient of `V_m V_m*` detects divisibility by `m`. -/
theorem toeplitzMonomial_diagonal_self
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m k : finitePrimeSemigroup S) :
    inner ℂ (basisVector S k)
        (toeplitzMonomial hS m m (basisVector S k)) =
      if m ∣ k then 1 else 0 := by
  classical
  by_cases hmk : m ∣ k
  · rcases hmk with ⟨r, rfl⟩
    simp [toeplitzMonomial, basisVector, lp.inner_single_left,
      lp.single_apply, Pi.single_apply]
  · have hz : shiftAdjoint hS m (basisVector S k) = 0 :=
      shiftAdjoint_basisVector_eq_zero_of_not_dvd hS m k hmk
    simp [toeplitzMonomial, hz, hmk]

/-- Off the diagonal `m = n`, every basis-diagonal coefficient of `V_m V_n*` vanishes. -/
theorem toeplitzMonomial_diagonal_of_ne
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n)
    (k : finitePrimeSemigroup S) :
    inner ℂ (basisVector S k)
        (toeplitzMonomial hS m n (basisVector S k)) = 0 := by
  classical
  by_cases hnk : n ∣ k
  · rcases hnk with ⟨r, rfl⟩
    have hdiff : n * r ≠ m * r := by
      intro h
      apply hmn
      exact (rightMul_injective hS r) h.symm
    simp [toeplitzMonomial, basisVector, lp.inner_single_left,
      lp.single_apply, Pi.single_apply, hdiff]
  · have hz : shiftAdjoint hS n (basisVector S k) = 0 :=
      shiftAdjoint_basisVector_eq_zero_of_not_dvd hS n k hnk
    simp [toeplitzMonomial, hz]

/-- The normalized Gibbs mass of the multiples of `m` is exactly `m^{-β}`. -/
theorem tsum_gibbsProbabilityWeight_dvd
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m : finitePrimeSemigroup S) :
    (∑' k : finitePrimeSemigroup S,
      if m ∣ k then gibbsProbabilityWeight S β k else 0) =
      gibbsWeight β m := by
  let M : Set (finitePrimeSemigroup S) := {k | m ∣ k}
  let e := leftMulEquivMultiples hS m
  calc
    (∑' k : finitePrimeSemigroup S,
      if m ∣ k then gibbsProbabilityWeight S β k else 0) =
        ∑' k : M, gibbsProbabilityWeight S β k.1 := by
          have hsub := tsum_subtype M (gibbsProbabilityWeight S β)
          simpa [M, Set.indicator] using hsub.symm
    _ = ∑' r : finitePrimeSemigroup S,
        gibbsProbabilityWeight S β (m * r) := by
          rw [← e.tsum_eq]
          rfl
    _ = ∑' r : finitePrimeSemigroup S,
        gibbsWeight β m * gibbsProbabilityWeight S β r := by
          apply tsum_congr
          intro r
          rw [gibbsProbabilityWeight_mul_left]
    _ = gibbsWeight β m *
        (∑' r : finitePrimeSemigroup S, gibbsProbabilityWeight S β r) := by
          rw [tsum_mul_left]
    _ = gibbsWeight β m := by
          rw [tsum_gibbsProbabilityWeight hS hβ, mul_one]

/-- The Gibbs expectation of a diagonal Toeplitz monomial is `m^{-β}`. -/
theorem gibbsExpectation_toeplitzMonomial_self
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m : finitePrimeSemigroup S) :
    gibbsExpectation S β (toeplitzMonomial hS m m) =
      ((gibbsWeight β m : ℝ) : ℂ) := by
  unfold gibbsExpectation
  calc
    (∑' k : finitePrimeSemigroup S,
      gibbsExpectationTerm S β (toeplitzMonomial hS m m) k) =
        ∑' k : finitePrimeSemigroup S,
          (((if m ∣ k then gibbsProbabilityWeight S β k else 0 : ℝ)) : ℂ) := by
            apply tsum_congr
            intro k
            unfold gibbsExpectationTerm
            rw [toeplitzMonomial_diagonal_self hS m k]
            by_cases hmk : m ∣ k <;> simp [hmk]
    _ = (((∑' k : finitePrimeSemigroup S,
          if m ∣ k then gibbsProbabilityWeight S β k else 0) : ℝ) : ℂ) := by
            exact (Complex.ofReal_tsum _).symm
    _ = ((gibbsWeight β m : ℝ) : ℂ) := by
          rw [tsum_gibbsProbabilityWeight_dvd hS hβ m]

/-- Off-diagonal Toeplitz monomials have zero Gibbs expectation. -/
theorem gibbsExpectation_toeplitzMonomial_of_ne
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    {m n : finitePrimeSemigroup S} (hmn : m ≠ n) :
    gibbsExpectation S β (toeplitzMonomial hS m n) = 0 := by
  unfold gibbsExpectation
  apply tsum_eq_zero
  intro k
  unfold gibbsExpectationTerm
  rw [toeplitzMonomial_diagonal_of_ne hS hmn k]
  simp

/-- The finite Gibbs expectation has the expected value on every Toeplitz monomial. -/
theorem gibbsExpectation_toeplitzMonomial
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n : finitePrimeSemigroup S) :
    gibbsExpectation S β (toeplitzMonomial hS m n) =
      if m = n then ((gibbsWeight β m : ℝ) : ℂ) else 0 := by
  by_cases hmn : m = n
  · subst n
    simp [hmn, gibbsExpectation_toeplitzMonomial_self hS hβ m]
  · simp [hmn, gibbsExpectation_toeplitzMonomial_of_ne hS hβ hmn]

end

end BostConnes
end BrickPileLean
