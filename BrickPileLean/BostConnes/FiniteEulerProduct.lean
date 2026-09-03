import Mathlib

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- The local ratio `p^{-β}` appearing in the finite Euler factor. -/
def localRatio (p : ℕ) (β : ℝ) : ℝ :=
  (p : ℝ) ^ (-β)

lemma localRatio_nonneg (p : ℕ) (β : ℝ) : 0 ≤ localRatio p β := by
  unfold localRatio
  exact Real.rpow_nonneg (Nat.cast_nonneg p) (-β)

lemma localRatio_lt_one {p : ℕ} {β : ℝ} (hp : 1 < p) (hβ : 0 < β) :
    localRatio p β < 1 := by
  unfold localRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hp
  · linarith

/-- The one-prime partition sum is the corresponding Euler factor. -/
theorem tsum_localRatio_pow {p : ℕ} {β : ℝ} (hp : 1 < p) (hβ : 0 < β) :
    (∑' k : ℕ, (localRatio p β) ^ k) = (1 - localRatio p β)⁻¹ := by
  exact tsum_geometric_of_lt_one (localRatio_nonneg p β) (localRatio_lt_one hp hβ)

/-- Product of the independent one-prime partition sums. -/
def separatedPartition (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ S, ∑' k : ℕ, (localRatio p β) ^ k

/-- The finite Euler product attached to `S`. -/
def finiteEulerProduct (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ S, (1 - localRatio p β)⁻¹

/-- At positive inverse temperature, the separated finite-prime partition sum is exactly
its finite Euler product.  No primality assumption is needed beyond `1 < p`; the prime
specialization below is the form used by the Bost--Connes application. -/
theorem separatedPartition_eq_finiteEulerProduct
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, 1 < p) (hβ : 0 < β) :
    separatedPartition S β = finiteEulerProduct S β := by
  unfold separatedPartition finiteEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  exact tsum_localRatio_pow (hS p hp) hβ

/-- Prime-indexed version of `separatedPartition_eq_finiteEulerProduct`. -/
theorem separatedPartition_eq_finiteEulerProduct_of_prime
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    separatedPartition S β = finiteEulerProduct S β := by
  apply separatedPartition_eq_finiteEulerProduct (hβ := hβ)
  intro p hp
  exact (hS p hp).one_lt

@[simp] theorem finiteEulerProduct_empty (β : ℝ) :
    finiteEulerProduct ∅ β = 1 := by
  simp [finiteEulerProduct]

end

end BostConnes
end BrickPileLean
