import BrickPileLean.BostConnes.FiniteEulerProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- The complex local ratio `p^{-s}`, written using the real logarithm of `p`.
For the Euler-product application we require `1 < p`. -/
def complexLocalRatio (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

/-- The finite Euler product at complex inverse temperature. Its analytic
domain below is the right half-plane; no infinite-prime limit is asserted. -/
def finiteComplexEulerProduct (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - complexLocalRatio p s)⁻¹

/-- Each local ratio is entire. -/
theorem complexLocalRatio_analyticOnNhd (p : ℕ) :
    AnalyticOnNhd ℂ (complexLocalRatio p) Set.univ := by
  unfold complexLocalRatio
  exact (analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp

/-- The modulus of a local ratio depends only on the real part of `s`. -/
theorem norm_complexLocalRatio (p : ℕ) (s : ℂ) :
    ‖complexLocalRatio p s‖ = Real.exp (-s.re * Real.log (p : ℝ)) := by
  simp [complexLocalRatio, Complex.norm_exp, Complex.mul_re]

/-- On the right half-plane the local geometric ratio has modulus below one. -/
theorem norm_complexLocalRatio_lt_one {p : ℕ} {s : ℂ}
    (hp : 1 < p) (hs : 0 < s.re) : ‖complexLocalRatio p s‖ < 1 := by
  rw [norm_complexLocalRatio, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) hlog

/-- No local denominator vanishes on the right half-plane. -/
theorem one_sub_complexLocalRatio_ne_zero {p : ℕ} {s : ℂ}
    (hp : 1 < p) (hs : 0 < s.re) : 1 - complexLocalRatio p s ≠ 0 := by
  intro h
  have heq : complexLocalRatio p s = 1 := (sub_eq_zero.mp h).symm
  have hnorm := norm_complexLocalRatio_lt_one hp hs
  rw [heq, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

/-- Each reciprocal Euler factor is holomorphic on the right half-plane. -/
theorem complexEulerFactor_analyticOnNhd {p : ℕ} (hp : 1 < p) :
    AnalyticOnNhd ℂ (fun s : ℂ => (1 - complexLocalRatio p s)⁻¹)
      {s : ℂ | 0 < s.re} := by
  have hratio := (complexLocalRatio_analyticOnNhd p).mono
    (Set.subset_univ {s : ℂ | 0 < s.re})
  exact (analyticOnNhd_const.sub hratio).inv
    (fun s hs => one_sub_complexLocalRatio_ne_zero hp hs)

/-- A finite Euler product is holomorphic throughout `Re(s) > 0`.
Only `1 < p` is needed for the factors; primality is a specialization. -/
theorem finiteComplexEulerProduct_analyticOnNhd {S : Finset ℕ}
    (hS : ∀ p ∈ S, 1 < p) :
    AnalyticOnNhd ℂ (finiteComplexEulerProduct S) {s : ℂ | 0 < s.re} := by
  unfold finiteComplexEulerProduct
  exact S.analyticOnNhd_fun_prod
    (fun p hp => complexEulerFactor_analyticOnNhd (hS p hp))

/-- Prime-indexed holomorphy in the form used by the finite Bost--Connes model. -/
theorem finiteComplexEulerProduct_analyticOnNhd_of_prime {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    AnalyticOnNhd ℂ (finiteComplexEulerProduct S) {s : ℂ | 0 < s.re} := by
  exact finiteComplexEulerProduct_analyticOnNhd (fun p hp => (hS p hp).one_lt)

/-- The finite product has no zeros on the right half-plane. -/
theorem finiteComplexEulerProduct_ne_zero {S : Finset ℕ} {s : ℂ}
    (hS : ∀ p ∈ S, 1 < p) (hs : 0 < s.re) :
    finiteComplexEulerProduct S s ≠ 0 := by
  unfold finiteComplexEulerProduct
  exact Finset.prod_ne_zero_iff.mpr
    (fun p hp => inv_ne_zero (one_sub_complexLocalRatio_ne_zero (hS p hp) hs))

@[simp] theorem finiteComplexEulerProduct_empty (s : ℂ) :
    finiteComplexEulerProduct ∅ s = 1 := by
  simp [finiteComplexEulerProduct]

end

end BostConnes
end BrickPileLean
