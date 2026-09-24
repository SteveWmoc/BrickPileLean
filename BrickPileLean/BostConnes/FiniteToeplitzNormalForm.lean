import BrickPileLean.BostConnes.FiniteToeplitzCoprime

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- The coordinatewise common exponent vector of two elements of the finite
prime semigroup. -/
def finitePrimeCommonExponent
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) : ExponentVector S :=
  fun p => min
    ((exponentVectorEquivFinitePrimeSemigroup S hS).symm n p)
    ((exponentVectorEquivFinitePrimeSemigroup S hS).symm r p)

/-- The residual exponent vector left after removing the common factor from
the first semigroup element. -/
def finitePrimeLeftResidualExponent
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) : ExponentVector S :=
  fun p =>
    (exponentVectorEquivFinitePrimeSemigroup S hS).symm n p -
      finitePrimeCommonExponent hS n r p

/-- The residual exponent vector left after removing the common factor from
the second semigroup element. -/
def finitePrimeRightResidualExponent
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) : ExponentVector S :=
  fun p =>
    (exponentVectorEquivFinitePrimeSemigroup S hS).symm r p -
      finitePrimeCommonExponent hS n r p

/-- The canonical common factor of two elements of `Λ_S`, obtained by taking
the coordinatewise minimum of their prime exponents. -/
def finitePrimeCommonFactor
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) : finitePrimeSemigroup S :=
  exponentVectorEquivFinitePrimeSemigroup S hS
    (finitePrimeCommonExponent hS n r)

/-- The residual factor of the first argument after removing the canonical
common factor. -/
def finitePrimeLeftResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) : finitePrimeSemigroup S :=
  exponentVectorEquivFinitePrimeSemigroup S hS
    (finitePrimeLeftResidualExponent hS n r)

/-- The residual factor of the second argument after removing the canonical
common factor. -/
def finitePrimeRightResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) : finitePrimeSemigroup S :=
  exponentVectorEquivFinitePrimeSemigroup S hS
    (finitePrimeRightResidualExponent hS n r)

/-- Re-encoding the exponent vector of a semigroup element recovers its
underlying natural number. -/
theorem semigroupElement_equiv_symm
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n : finitePrimeSemigroup S) :
    semigroupElement S
        ((exponentVectorEquivFinitePrimeSemigroup S hS).symm n) =
      (n : ℕ) := by
  let e := exponentVectorEquivFinitePrimeSemigroup S hS
  calc
    semigroupElement S (e.symm n) = (e (e.symm n) : ℕ) := by
      symm
      exact exponentVectorEquivFinitePrimeSemigroup_apply S hS (e.symm n)
    _ = (n : ℕ) := by
      exact congrArg (fun x : finitePrimeSemigroup S => (x : ℕ))
        (e.apply_symm_apply n)

@[simp] theorem coe_finitePrimeCommonFactor
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    (finitePrimeCommonFactor hS n r : ℕ) =
      semigroupElement S (finitePrimeCommonExponent hS n r) := by
  exact exponentVectorEquivFinitePrimeSemigroup_apply S hS _

@[simp] theorem coe_finitePrimeLeftResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    (finitePrimeLeftResidual hS n r : ℕ) =
      semigroupElement S (finitePrimeLeftResidualExponent hS n r) := by
  exact exponentVectorEquivFinitePrimeSemigroup_apply S hS _

@[simp] theorem coe_finitePrimeRightResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    (finitePrimeRightResidual hS n r : ℕ) =
      semigroupElement S (finitePrimeRightResidualExponent hS n r) := by
  exact exponentVectorEquivFinitePrimeSemigroup_apply S hS _

/-- The common exponent vector plus the left residual recovers the first
exponent vector. -/
theorem finitePrimeCommonExponent_add_leftResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    finitePrimeCommonExponent hS n r +
        finitePrimeLeftResidualExponent hS n r =
      (exponentVectorEquivFinitePrimeSemigroup S hS).symm n := by
  funext p
  exact Nat.add_sub_of_le (Nat.min_le_left _ _)

/-- The common exponent vector plus the right residual recovers the second
exponent vector. -/
theorem finitePrimeCommonExponent_add_rightResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    finitePrimeCommonExponent hS n r +
        finitePrimeRightResidualExponent hS n r =
      (exponentVectorEquivFinitePrimeSemigroup S hS).symm r := by
  funext p
  exact Nat.add_sub_of_le (Nat.min_le_right _ _)

/-- The canonical common factor times the left residual is the first
semigroup element. -/
theorem finitePrimeCommonFactor_mul_leftResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    finitePrimeCommonFactor hS n r *
        finitePrimeLeftResidual hS n r = n := by
  apply Subtype.ext
  change
    (finitePrimeCommonFactor hS n r : ℕ) *
        (finitePrimeLeftResidual hS n r : ℕ) = (n : ℕ)
  rw [coe_finitePrimeCommonFactor, coe_finitePrimeLeftResidual,
    ← semigroupElement_add, finitePrimeCommonExponent_add_leftResidual,
    semigroupElement_equiv_symm]

/-- The canonical common factor times the right residual is the second
semigroup element. -/
theorem finitePrimeCommonFactor_mul_rightResidual
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    finitePrimeCommonFactor hS n r *
        finitePrimeRightResidual hS n r = r := by
  apply Subtype.ext
  change
    (finitePrimeCommonFactor hS n r : ℕ) *
        (finitePrimeRightResidual hS n r : ℕ) = (r : ℕ)
  rw [coe_finitePrimeCommonFactor, coe_finitePrimeRightResidual,
    ← semigroupElement_add, finitePrimeCommonExponent_add_rightResidual,
    semigroupElement_equiv_symm]

/-- If two exponent vectors never have positive entries at the same prime,
their encoded natural numbers are coprime. -/
theorem semigroupElement_coprime_of_disjoint
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (k l : ExponentVector S)
    (hdis : ∀ p : S, k p = 0 ∨ l p = 0) :
    Nat.Coprime (semigroupElement S k) (semigroupElement S l) := by
  apply Nat.coprime_of_dvd
  intro q hq hqk
  intro hql
  change q ∣ ∏ p : S, p.1 ^ k p at hqk
  change q ∣ ∏ p : S, p.1 ^ l p at hql
  rcases
      (hq.prime.dvd_finsetProd_iff
        (fun p : S => p.1 ^ k p)).1 hqk with
    ⟨p, _, hqkp⟩
  rcases
      (hq.prime.dvd_finsetProd_iff
        (fun p : S => p.1 ^ l p)).1 hql with
    ⟨r, _, hqlr⟩
  have hkp : k p ≠ 0 := by
    intro hzero
    simp [hzero, hq.ne_one] at hqkp
  have hlr : l r ≠ 0 := by
    intro hzero
    simp [hzero, hq.ne_one] at hqlr
  have hqp : q = p.1 := by
    apply (Nat.prime_dvd_prime_iff_eq hq (hS p.1 p.2)).1
    exact (hq.prime.dvd_pow_iff_dvd hkp).1 hqkp
  have hqr : q = r.1 := by
    apply (Nat.prime_dvd_prime_iff_eq hq (hS r.1 r.2)).1
    exact (hq.prime.dvd_pow_iff_dvd hlr).1 hqlr
  have hpr : p = r := Subtype.ext (hqp.symm.trans hqr)
  subst r
  rcases hdis p with hk | hl
  · exact hkp hk
  · exact hlr hl

/-- The two residual exponent vectors have disjoint support. -/
theorem finitePrimeResidualExponent_disjoint
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    ∀ p : S,
      finitePrimeLeftResidualExponent hS n r p = 0 ∨
        finitePrimeRightResidualExponent hS n r p = 0 := by
  intro p
  let e := exponentVectorEquivFinitePrimeSemigroup S hS
  by_cases h : e.symm n p ≤ e.symm r p
  · left
    simp [finitePrimeLeftResidualExponent, finitePrimeCommonExponent, e,
      Nat.min_eq_left h]
  · right
    have h' : e.symm r p ≤ e.symm n p :=
      le_of_lt (lt_of_not_ge h)
    simp [finitePrimeRightResidualExponent, finitePrimeCommonExponent, e,
      Nat.min_eq_right h']

/-- The canonical residual factors are coprime. -/
theorem finitePrimeResiduals_coprime
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    Nat.Coprime
      (finitePrimeLeftResidual hS n r : ℕ)
      (finitePrimeRightResidual hS n r : ℕ) := by
  rw [coe_finitePrimeLeftResidual, coe_finitePrimeRightResidual]
  exact semigroupElement_coprime_of_disjoint hS _ _
    (finitePrimeResidualExponent_disjoint hS n r)

/-- The canonical common factor really is the ordinary natural-number gcd of
the two semigroup elements. -/
theorem coe_finitePrimeCommonFactor_eq_gcd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n r : finitePrimeSemigroup S) :
    (finitePrimeCommonFactor hS n r : ℕ) =
      Nat.gcd (n : ℕ) (r : ℕ) := by
  let d := finitePrimeCommonFactor hS n r
  let a := finitePrimeLeftResidual hS n r
  let b := finitePrimeRightResidual hS n r
  have hn : (n : ℕ) = (d : ℕ) * (a : ℕ) := by
    exact congrArg (fun x : finitePrimeSemigroup S => (x : ℕ))
      (finitePrimeCommonFactor_mul_leftResidual hS n r).symm
  have hr : (r : ℕ) = (d : ℕ) * (b : ℕ) := by
    exact congrArg (fun x : finitePrimeSemigroup S => (x : ℕ))
      (finitePrimeCommonFactor_mul_rightResidual hS n r).symm
  have hab : Nat.Coprime (a : ℕ) (b : ℕ) := by
    exact finitePrimeResiduals_coprime hS n r
  change (d : ℕ) = Nat.gcd (n : ℕ) (r : ℕ)
  calc
    (d : ℕ) = (d : ℕ) * 1 := by simp
    _ = (d : ℕ) * Nat.gcd (a : ℕ) (b : ℕ) := by
      rw [hab.gcd_eq_one]
    _ = Nat.gcd ((d : ℕ) * (a : ℕ)) ((d : ℕ) * (b : ℕ)) := by
      rw [Nat.gcd_mul_left]
    _ = Nat.gcd (n : ℕ) (r : ℕ) := by
      rw [hn, hr]

/-- General standard-monomial product normal form.  The middle indices are
split by their canonical gcd/common factor, leaving coprime residuals. -/
theorem toeplitzMonomial_mul_normalForm
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n r s : finitePrimeSemigroup S) :
    toeplitzMonomial hS m n * toeplitzMonomial hS r s =
      toeplitzMonomial hS
        (m * finitePrimeRightResidual hS n r)
        (s * finitePrimeLeftResidual hS n r) := by
  let d := finitePrimeCommonFactor hS n r
  let a := finitePrimeLeftResidual hS n r
  let b := finitePrimeRightResidual hS n r
  have hn : d * a = n := by
    exact finitePrimeCommonFactor_mul_leftResidual hS n r
  have hr : d * b = r := by
    exact finitePrimeCommonFactor_mul_rightResidual hS n r
  have hab : Nat.Coprime (a : ℕ) (b : ℕ) := by
    exact finitePrimeResiduals_coprime hS n r
  have hprod :
      toeplitzMonomial hS m (d * a) *
          toeplitzMonomial hS (d * b) s =
        toeplitzMonomial hS (m * b) (s * a) := by
    exact toeplitzMonomial_mul_of_common_factor_coprime hS m d a b s hab
  calc
    toeplitzMonomial hS m n * toeplitzMonomial hS r s =
        toeplitzMonomial hS m (d * a) *
          toeplitzMonomial hS (d * b) s := by
            rw [hn, hr]
    _ = toeplitzMonomial hS (m * b) (s * a) := hprod
    _ = toeplitzMonomial hS
        (m * finitePrimeRightResidual hS n r)
        (s * finitePrimeLeftResidual hS n r) := by
          rfl

end

end BostConnes
end BrickPileLean
