import BrickPileLean.BostConnes.FiniteKMSGenerators
import BrickPileLean.BostConnes.FiniteToeplitzNormalForm

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The diagonal condition after reducing the middle indices is equivalent to
the original cross-product condition. -/
theorem finitePrimeResidual_cross_iff
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n r s : finitePrimeSemigroup S) :
    m * finitePrimeRightResidual hS n r =
        s * finitePrimeLeftResidual hS n r ↔
      m * r = n * s := by
  let d := finitePrimeCommonFactor hS n r
  let a := finitePrimeLeftResidual hS n r
  let b := finitePrimeRightResidual hS n r
  have hn : d * a = n := by
    exact finitePrimeCommonFactor_mul_leftResidual hS n r
  have hr : d * b = r := by
    exact finitePrimeCommonFactor_mul_rightResidual hS n r
  change m * b = s * a ↔ m * r = n * s
  constructor
  · intro h
    calc
      m * r = m * (d * b) := by rw [hr]
      _ = d * (m * b) := by ac_rfl
      _ = d * (s * a) := by rw [h]
      _ = (d * a) * s := by ac_rfl
      _ = n * s := by rw [hn]
  · intro h
    apply leftMul_injective hS d
    calc
      d * (m * b) = m * (d * b) := by ac_rfl
      _ = m * r := by rw [hr]
      _ = n * s := h
      _ = (d * a) * s := by rw [hn]
      _ = d * (s * a) := by ac_rfl

/-- A coprime cross-product equality has a common residual factor:
if `m b = s a` and `a,b` are coprime, then
`m = c a` and `s = c b` for some `c`. -/
theorem finitePrime_coprime_cross_factorization
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {a b m s : finitePrimeSemigroup S}
    (hab : Nat.Coprime (a : ℕ) (b : ℕ))
    (hcross : m * b = s * a) :
    ∃ c : finitePrimeSemigroup S, m = c * a ∧ s = c * b := by
  have hnat := congrArg
    (fun x : finitePrimeSemigroup S => (x : ℕ)) hcross
  have hadivprod : (a : ℕ) ∣ (b : ℕ) * (m : ℕ) := by
    refine ⟨(s : ℕ), ?_⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnat
  have hadivNat : (a : ℕ) ∣ (m : ℕ) :=
    Nat.Coprime.dvd_of_dvd_mul_left hab hadivprod
  have hadiv : a ∣ m :=
    (finitePrimeSemigroup_dvd_iff_coe_dvd hS a m).2 hadivNat
  rcases hadiv with ⟨c, hc⟩
  have hm : m = c * a := by
    simpa [mul_comm] using hc
  refine ⟨c, hm, ?_⟩
  apply rightMul_injective hS a
  calc
    s * a = m * b := hcross.symm
    _ = (c * a) * b := by rw [hm]
    _ = (c * b) * a := by ac_rfl

/-- Gibbs expectation of a product of two standard monomials.  The product is
diagonal exactly when the original four labels satisfy `m r = n s`. -/
theorem finiteGibbsState_toeplitzMonomial_mul
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n r s : finitePrimeSemigroup S) :
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n * finiteToeplitzMonomial hS r s) =
      if m * r = n * s then
        (((gibbsWeight β
          (m * finitePrimeRightResidual hS n r) : ℝ) : ℂ))
      else 0 := by
  let a := finitePrimeLeftResidual hS n r
  let b := finitePrimeRightResidual hS n r
  change gibbsExpectation S β
      (toeplitzMonomial hS m n * toeplitzMonomial hS r s) =
    if m * r = n * s then ((gibbsWeight β (m * b) : ℝ) : ℂ) else 0
  rw [toeplitzMonomial_mul_normalForm hS m n r s]
  change gibbsExpectation S β (toeplitzMonomial hS (m * b) (s * a)) =
    if m * r = n * s then ((gibbsWeight β (m * b) : ℝ) : ℂ) else 0
  rw [gibbsExpectation_toeplitzMonomial hS hβ]
  by_cases hcross : m * r = n * s
  · have hres : m * b = s * a :=
      (finitePrimeResidual_cross_iff hS m n r s).2 hcross
    simp [hcross, hres]
  · have hres : m * b ≠ s * a := by
      intro h
      exact hcross ((finitePrimeResidual_cross_iff hS m n r s).1 h)
    simp [hcross, hres]

/-- Cross-multiplied KMS identity for two arbitrary standard Toeplitz
monomials.  This form avoids division by a Gibbs weight and is the algebraic
heart of the monomial KMS relation. -/
theorem finiteGibbsState_kms_toeplitzMonomials_cross
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n r s : finitePrimeSemigroup S) :
    (((gibbsWeight β n : ℝ) : ℂ)) *
        finiteGibbsState hS hβ
          (finiteToeplitzMonomial hS m n * finiteToeplitzMonomial hS r s) =
      (((gibbsWeight β m : ℝ) : ℂ)) *
        finiteGibbsState hS hβ
          (finiteToeplitzMonomial hS r s * finiteToeplitzMonomial hS m n) := by
  let d := finitePrimeCommonFactor hS n r
  let a := finitePrimeLeftResidual hS n r
  let b := finitePrimeRightResidual hS n r
  have hn : d * a = n := by
    exact finitePrimeCommonFactor_mul_leftResidual hS n r
  have hr : d * b = r := by
    exact finitePrimeCommonFactor_mul_rightResidual hS n r
  have hab : Nat.Coprime (a : ℕ) (b : ℕ) := by
    exact finitePrimeResiduals_coprime hS n r
  by_cases hcross : m * r = n * s
  · have hres : m * b = s * a :=
      (finitePrimeResidual_cross_iff hS m n r s).2 hcross
    obtain ⟨c, hm, hs⟩ :=
      finitePrime_coprime_cross_factorization hS hab hres
    have hAB :
        finiteToeplitzMonomial hS m n * finiteToeplitzMonomial hS r s =
          finiteToeplitzMonomial hS (m * b) (s * a) := by
      apply Subtype.ext
      change toeplitzMonomial hS m n * toeplitzMonomial hS r s =
        toeplitzMonomial hS (m * b) (s * a)
      rw [← hn, ← hr]
      exact toeplitzMonomial_mul_of_common_factor_coprime hS m d a b s hab
    have hBA :
        finiteToeplitzMonomial hS r s * finiteToeplitzMonomial hS m n =
          finiteToeplitzMonomial hS ((d * b) * a) ((d * a) * b) := by
      apply Subtype.ext
      change toeplitzMonomial hS r s * toeplitzMonomial hS m n =
        toeplitzMonomial hS ((d * b) * a) ((d * a) * b)
      rw [← hr, hs, hm, ← hn]
      exact toeplitzMonomial_mul_of_common_factor_coprime
        hS (d * b) c b a (d * a) hab.symm
    have hdiagBA : (d * b) * a = (d * a) * b := by
      ac_rfl
    have hphiAB :
        finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS m n * finiteToeplitzMonomial hS r s) =
          ((gibbsWeight β (m * b) : ℝ) : ℂ) := by
      rw [hAB, finiteGibbsState_toeplitzMonomial, if_pos hres]
    have hphiBA :
        finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS r s * finiteToeplitzMonomial hS m n) =
          ((gibbsWeight β ((d * b) * a) : ℝ) : ℂ) := by
      rw [hBA, finiteGibbsState_toeplitzMonomial, if_pos hdiagBA]
    rw [hphiAB, hphiBA]
    have hweight :
        gibbsWeight β n * gibbsWeight β (m * b) =
          gibbsWeight β m * gibbsWeight β ((d * b) * a) := by
      rw [← hn, hm]
      simp only [gibbsWeight_mul]
      ring
    exact_mod_cast hweight
  · have hcross' : r * m ≠ s * n := by
      intro h
      apply hcross
      simpa [mul_comm] using h
    have hphiAB :
        finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS m n *
              finiteToeplitzMonomial hS r s) = 0 := by
      have h :=
        finiteGibbsState_toeplitzMonomial_mul hS hβ m n r s
      rw [if_neg hcross] at h
      exact h
    have hphiBA :
        finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS r s *
              finiteToeplitzMonomial hS m n) = 0 := by
      have h :=
        finiteGibbsState_toeplitzMonomial_mul hS hβ r s m n
      rw [if_neg hcross'] at h
      exact h
    rw [hphiAB, hphiBA]
    simp

/-- KMS boundary identity for two arbitrary standard analytic monomials.

The scalar is the imaginary-time eigenvalue of `V_m V_n*`, written as the
ratio `m^{-β}/n^{-β}` of Gibbs weights. -/
theorem finiteGibbsState_kms_toeplitzMonomials
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (m n r s : finitePrimeSemigroup S) :
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n * finiteToeplitzMonomial hS r s) =
      ((((gibbsWeight β m : ℝ) : ℂ) /
          ((gibbsWeight β n : ℝ) : ℂ))) *
        finiteGibbsState hS hβ
          (finiteToeplitzMonomial hS r s * finiteToeplitzMonomial hS m n) := by
  have hcross :=
    finiteGibbsState_kms_toeplitzMonomials_cross hS hβ m n r s
  have hn0 : ((gibbsWeight β n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (gibbsWeight_pos hS β n).ne'
  calc
    finiteGibbsState hS hβ
        (finiteToeplitzMonomial hS m n * finiteToeplitzMonomial hS r s) =
      (((gibbsWeight β n : ℝ) : ℂ))⁻¹ *
        ((((gibbsWeight β n : ℝ) : ℂ)) *
          finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS m n *
              finiteToeplitzMonomial hS r s)) := by
        simp [hn0]
    _ = (((gibbsWeight β n : ℝ) : ℂ))⁻¹ *
        ((((gibbsWeight β m : ℝ) : ℂ)) *
          finiteGibbsState hS hβ
            (finiteToeplitzMonomial hS r s *
              finiteToeplitzMonomial hS m n)) := by
        rw [hcross]
    _ = ((((gibbsWeight β m : ℝ) : ℂ) /
          ((gibbsWeight β n : ℝ) : ℂ))) *
        finiteGibbsState hS hβ
          (finiteToeplitzMonomial hS r s *
            finiteToeplitzMonomial hS m n) := by
        rw [div_eq_mul_inv]
        ring

end

end BostConnes
end BrickPileLean
