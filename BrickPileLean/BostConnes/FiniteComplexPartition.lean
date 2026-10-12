import BrickPileLean.BostConnes.FiniteComplexEulerProduct

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- At real inverse temperature the complex ratio is the real ratio embedded
in `ℂ`. Positivity of `p` ensures the real-power logarithm formula applies. -/
theorem complexLocalRatio_ofReal {p : ℕ} (hp : 0 < p) (β : ℝ) :
    complexLocalRatio p (β : ℂ) = (localRatio p β : ℂ) := by
  unfold complexLocalRatio localRatio
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp), Complex.ofReal_exp]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The complex one-prime partition series is absolutely summable on the
right half-plane. -/
theorem summable_complexLocalRatio_pow {p : ℕ} {s : ℂ}
    (hp : 1 < p) (hs : 0 < s.re) :
    Summable (fun k : ℕ => complexLocalRatio p s ^ k) := by
  exact summable_geometric_of_norm_lt_one (norm_complexLocalRatio_lt_one hp hs)

/-- The complex one-prime partition series equals its reciprocal Euler factor. -/
theorem tsum_complexLocalRatio_pow {p : ℕ} {s : ℂ}
    (hp : 1 < p) (hs : 0 < s.re) :
    (∑' k : ℕ, complexLocalRatio p s ^ k) = (1 - complexLocalRatio p s)⁻¹ := by
  exact tsum_geometric_of_norm_lt_one (norm_complexLocalRatio_lt_one hp hs)

/-- Product of the independent complex one-prime partition series. -/
def separatedComplexPartition (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, ∑' k : ℕ, complexLocalRatio p s ^ k

/-- The separated complex partition function equals the finite Euler product
throughout the right half-plane. -/
theorem separatedComplexPartition_eq_finiteComplexEulerProduct
    {S : Finset ℕ} {s : ℂ} (hS : ∀ p ∈ S, 1 < p) (hs : 0 < s.re) :
    separatedComplexPartition S s = finiteComplexEulerProduct S s := by
  unfold separatedComplexPartition finiteComplexEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  exact tsum_complexLocalRatio_pow (hS p hp) hs

/-- At real inverse temperature the complex finite product agrees with the
existing real Euler product. This identity does not require `β > 0`. -/
theorem finiteComplexEulerProduct_ofReal {S : Finset ℕ}
    (hS : ∀ p ∈ S, 1 < p) (β : ℝ) :
    finiteComplexEulerProduct S (β : ℂ) = (finiteEulerProduct S β : ℂ) := by
  unfold finiteComplexEulerProduct finiteEulerProduct
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  rw [complexLocalRatio_ofReal (lt_trans Nat.zero_lt_one (hS p hp))]

/-- At positive real inverse temperature the complex partition function
recovers the previously defined real separated partition function. -/
theorem separatedComplexPartition_ofReal {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, 1 < p) (hβ : 0 < β) :
    separatedComplexPartition S (β : ℂ) = (separatedPartition S β : ℂ) := by
  rw [separatedComplexPartition_eq_finiteComplexEulerProduct hS
    (by simpa only [Complex.ofReal_re] using hβ)]
  rw [finiteComplexEulerProduct_ofReal hS,
    separatedPartition_eq_finiteEulerProduct hS hβ]

/-- Prime-indexed complex partition identity for the finite Bost--Connes model. -/
theorem separatedComplexPartition_eq_finiteComplexEulerProduct_of_prime
    {S : Finset ℕ} {s : ℂ} (hS : ∀ p ∈ S, Nat.Prime p) (hs : 0 < s.re) :
    separatedComplexPartition S s = finiteComplexEulerProduct S s := by
  exact separatedComplexPartition_eq_finiteComplexEulerProduct
    (fun p hp => (hS p hp).one_lt) hs

end

end BostConnes
end BrickPileLean
