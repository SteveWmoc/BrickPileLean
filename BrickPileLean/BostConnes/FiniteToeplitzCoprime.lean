import BrickPileLean.BostConnes.FiniteToeplitzCancellation

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- Divisibility inside the finite prime semigroup is exactly ordinary
divisibility of the underlying natural numbers. -/
theorem finitePrimeSemigroup_dvd_iff_coe_dvd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (a b : finitePrimeSemigroup S) :
    a ∣ b ↔ (a : ℕ) ∣ (b : ℕ) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(c : ℕ), rfl⟩
  · intro hab
    let e := exponentVectorEquivFinitePrimeSemigroup S hS
    let ka : ExponentVector S := e.symm a
    let kb : ExponentVector S := e.symm b
    have haka : semigroupElement S ka = (a : ℕ) := by
      calc
        semigroupElement S ka =
            (exponentVectorEquivFinitePrimeSemigroup S hS ka : ℕ) := by
              symm
              exact exponentVectorEquivFinitePrimeSemigroup_apply S hS ka
        _ = (a : ℕ) := by
              exact congrArg
                (fun n : finitePrimeSemigroup S => (n : ℕ))
                (e.apply_symm_apply a)
    have hkb : semigroupElement S kb = (b : ℕ) := by
      calc
        semigroupElement S kb =
            (exponentVectorEquivFinitePrimeSemigroup S hS kb : ℕ) := by
              symm
              exact exponentVectorEquivFinitePrimeSemigroup_apply S hS kb
        _ = (b : ℕ) := by
              exact congrArg
                (fun n : finitePrimeSemigroup S => (n : ℕ))
                (e.apply_symm_apply b)
    have ha0 : (a : ℕ) ≠ 0 :=
      (finitePrimeSemigroup_coe_pos hS a).ne'
    have hb0 : (b : ℕ) ≠ 0 :=
      (finitePrimeSemigroup_coe_pos hS b).ne'
    have hfac :
        (a : ℕ).factorization ≤ (b : ℕ).factorization :=
      (Nat.factorization_le_iff_dvd ha0 hb0).2 hab
    have hle : ∀ p : S, ka p ≤ kb p := by
      intro p
      rw [← semigroupElement_factorization hS ka p,
        ← semigroupElement_factorization hS kb p, haka, hkb]
      exact hfac p.1
    let kc : ExponentVector S := fun p => kb p - ka p
    have hsum : ka + kc = kb := by
      funext p
      simpa [kc] using Nat.add_sub_of_le (hle p)
    let c : finitePrimeSemigroup S := e kc
    have hc : (c : ℕ) = semigroupElement S kc := by
      exact exponentVectorEquivFinitePrimeSemigroup_apply S hS kc
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change (b : ℕ) = (a : ℕ) * (c : ℕ)
    rw [← haka, hc, ← semigroupElement_add, hsum, hkb]

/-- A scalar single basis vector is the corresponding scalar multiple of the
canonical basis vector. -/
theorem lp_single_eq_smul_basisVector
    {S : Finset ℕ} (n : finitePrimeSemigroup S) (z : ℂ) :
    lp.single 2 n z = z • basisVector S n := by
  ext k
  simp [basisVector, lp.single_apply, Pi.single_apply]

/-- Coprime multiplicative shifts commute past adjoint shifts on canonical
basis vectors. -/
theorem shiftAdjoint_shiftOperator_basisVector_of_coprime
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {a b : finitePrimeSemigroup S}
    (hab : Nat.Coprime (a : ℕ) (b : ℕ))
    (k : finitePrimeSemigroup S) :
    shiftAdjoint hS a
        (shiftOperator hS b (basisVector S k)) =
      shiftOperator hS b
        (shiftAdjoint hS a (basisVector S k)) := by
  by_cases hak : a ∣ k
  · rcases hak with ⟨q, rfl⟩
    calc
      shiftAdjoint hS a
          (shiftOperator hS b (basisVector S (a * q))) =
        basisVector S (b * q) := by
          rw [shiftOperator_basisVector]
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            (shiftAdjoint_basisVector_mul hS a (b * q))
      _ = shiftOperator hS b
          (shiftAdjoint hS a (basisVector S (a * q))) := by
            rw [shiftAdjoint_basisVector_mul, shiftOperator_basisVector]
  · have hnot : ¬ a ∣ b * k := by
      intro habk
      have hnat :
          (a : ℕ) ∣ ((b * k : finitePrimeSemigroup S) : ℕ) :=
        (finitePrimeSemigroup_dvd_iff_coe_dvd hS a (b * k)).1 habk
      have hnat' : (a : ℕ) ∣ (b : ℕ) * (k : ℕ) := by
        simpa using hnat
      have haknat : (a : ℕ) ∣ (k : ℕ) :=
        Nat.Coprime.dvd_of_dvd_mul_left hab hnat'
      exact hak ((finitePrimeSemigroup_dvd_iff_coe_dvd hS a k).2 haknat)
    calc
      shiftAdjoint hS a
          (shiftOperator hS b (basisVector S k)) = 0 := by
            rw [shiftOperator_basisVector,
              shiftAdjoint_basisVector_eq_zero_of_not_dvd hS a (b * k) hnot]
      _ = shiftOperator hS b
          (shiftAdjoint hS a (basisVector S k)) := by
            rw [shiftAdjoint_basisVector_eq_zero_of_not_dvd hS a k hak]
            simp

/-- If the semigroup labels are coprime as natural numbers, the adjoint shift
and the forward shift commute. -/
theorem shiftAdjoint_mul_shiftOperator_of_coprime
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {a b : finitePrimeSemigroup S}
    (hab : Nat.Coprime (a : ℕ) (b : ℕ)) :
    shiftAdjoint hS a * shiftOperator hS b =
      shiftOperator hS b * shiftAdjoint hS a := by
  change (shiftAdjoint hS a).comp (shiftOperator hS b) =
    (shiftOperator hS b).comp (shiftAdjoint hS a)
  refine lp.ext_continuousLinearMap
    (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun k => ?_
  apply ContinuousLinearMap.ext
  intro z
  change shiftAdjoint hS a
      (shiftOperator hS b (lp.single 2 k z)) =
    shiftOperator hS b
      (shiftAdjoint hS a (lp.single 2 k z))
  rw [lp_single_eq_smul_basisVector]
  simp only [map_smul]
  rw [shiftAdjoint_shiftOperator_basisVector_of_coprime hS hab k]

/-- Coprime middle indices give the standard Toeplitz product reduction:
`(V_m V_a*) (V_b V_s*) = V_{mb} V_{sa}*`. -/
theorem toeplitzMonomial_mul_of_coprime_middle
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m a b s : finitePrimeSemigroup S)
    (hab : Nat.Coprime (a : ℕ) (b : ℕ)) :
    toeplitzMonomial hS m a * toeplitzMonomial hS b s =
      toeplitzMonomial hS (m * b) (s * a) := by
  unfold toeplitzMonomial
  calc
    (shiftOperator hS m * shiftAdjoint hS a) *
        (shiftOperator hS b * shiftAdjoint hS s) =
      shiftOperator hS m *
        (shiftAdjoint hS a * shiftOperator hS b) *
        shiftAdjoint hS s := by
          simp only [mul_assoc]
    _ = shiftOperator hS m *
        (shiftOperator hS b * shiftAdjoint hS a) *
        shiftAdjoint hS s := by
          rw [shiftAdjoint_mul_shiftOperator_of_coprime hS hab]
    _ = (shiftOperator hS m * shiftOperator hS b) *
        (shiftAdjoint hS a * shiftAdjoint hS s) := by
          simp only [mul_assoc]
    _ = shiftOperator hS (m * b) *
        shiftAdjoint hS (s * a) := by
          rw [shiftOperator_mul, shiftAdjoint_mul]

/-- After cancelling a common middle factor, coprime residuals give the full
product reduction. -/
theorem toeplitzMonomial_mul_of_common_factor_coprime
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m d a b s : finitePrimeSemigroup S)
    (hab : Nat.Coprime (a : ℕ) (b : ℕ)) :
    toeplitzMonomial hS m (d * a) *
        toeplitzMonomial hS (d * b) s =
      toeplitzMonomial hS (m * b) (s * a) := by
  unfold toeplitzMonomial
  calc
    (shiftOperator hS m * shiftAdjoint hS (d * a)) *
        (shiftOperator hS (d * b) * shiftAdjoint hS s) =
      shiftOperator hS m *
        (shiftAdjoint hS (d * a) * shiftOperator hS (d * b)) *
        shiftAdjoint hS s := by
          simp only [mul_assoc]
    _ = shiftOperator hS m *
        (shiftAdjoint hS a * shiftOperator hS b) *
        shiftAdjoint hS s := by
          rw [shiftAdjoint_mul_shiftOperator_cancel_common]
    _ = shiftOperator hS m *
        (shiftOperator hS b * shiftAdjoint hS a) *
        shiftAdjoint hS s := by
          rw [shiftAdjoint_mul_shiftOperator_of_coprime hS hab]
    _ = (shiftOperator hS m * shiftOperator hS b) *
        (shiftAdjoint hS a * shiftAdjoint hS s) := by
          simp only [mul_assoc]
    _ = shiftOperator hS (m * b) *
        shiftAdjoint hS (s * a) := by
          rw [shiftOperator_mul, shiftAdjoint_mul]

end

end BostConnes
end BrickPileLean
