import BrickPileLean.BostConnes.FiniteEulerProduct

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- Exponent vectors for a finite set of primes. -/
abbrev ExponentVector (S : Finset ℕ) := S → ℕ

/-- The Boltzmann weight of an exponent vector. -/
def exponentWeight (S : Finset ℕ) (β : ℝ) (k : ExponentVector S) : ℝ :=
  ∏ p : S, (localRatio p.1 β) ^ k p

/-- The partition sum over all exponent vectors. -/
def exponentPartition (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∑' k : ExponentVector S, exponentWeight S β k

private def finWeight {n : ℕ} (r : Fin n → ℝ) (k : Fin n → ℕ) : ℝ :=
  ∏ i, (r i) ^ k i

private theorem finWeight_nonneg {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (k : Fin n → ℕ) : 0 ≤ finWeight r k := by
  exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr i) _

/-- Finite-dimensional Fubini for products of nonnegative geometric sequences. -/
private theorem finWeight_summable_and_tsum :
    ∀ n : ℕ, ∀ r : Fin n → ℝ,
      (∀ i, 0 ≤ r i) → (∀ i, r i < 1) →
      Summable (finWeight r) ∧
        (∑' k : Fin n → ℕ, finWeight r k) = ∏ i, ∑' m : ℕ, (r i) ^ m := by
  intro n
  induction n with
  | zero =>
      intro r hr0 hr1
      constructor
      · exact (hasSum_unique (finWeight r)).summable
      · simp [finWeight]
  | succ n ih =>
      intro r hr0 hr1
      let rTail : Fin n → ℝ := fun i ↦ r i.succ
      have hhead : Summable (fun m : ℕ ↦ (r 0) ^ m) :=
        summable_geometric_of_lt_one (hr0 0) (hr1 0)
      have htail := ih rTail (fun i ↦ hr0 i.succ) (fun i ↦ hr1 i.succ)
      have hpair : Summable (fun z : ℕ × (Fin n → ℕ) ↦
          (r 0) ^ z.1 * finWeight rTail z.2) := by
        exact hhead.mul_of_nonneg htail.1
          (fun m ↦ pow_nonneg (hr0 0) m)
          (fun k ↦ finWeight_nonneg rTail (fun i ↦ hr0 i.succ) k)
      let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv fun _ ↦ ℕ
      have hweight (z : ℕ × (Fin n → ℕ)) :
          finWeight r (e z) = (r 0) ^ z.1 * finWeight rTail z.2 := by
        simp [finWeight, rTail, e, Fin.prod_univ_succ]
      have hsummable : Summable (finWeight r) := by
        rw [← e.summable_iff]
        simpa [Function.comp_def, hweight] using hpair
      constructor
      · exact hsummable
      · calc
          (∑' k : Fin (n + 1) → ℕ, finWeight r k)
              = ∑' z : ℕ × (Fin n → ℕ), (r 0) ^ z.1 * finWeight rTail z.2 := by
                  rw [← e.tsum_eq]
                  exact tsum_congr hweight
          _ = (∑' m : ℕ, (r 0) ^ m) * (∑' k : Fin n → ℕ, finWeight rTail k) := by
                have hhNorm : Summable (fun m : ℕ ↦ ‖(r 0) ^ m‖) := by
                  simpa [Real.norm_eq_abs, abs_of_nonneg (hr0 0)] using hhead
                have htNorm : Summable (fun k : Fin n → ℕ ↦ ‖finWeight rTail k‖) := by
                  simpa [Real.norm_eq_abs, abs_of_nonneg (finWeight_nonneg rTail
                    (fun i ↦ hr0 i.succ) _)] using htail.1
                exact (tsum_mul_tsum_of_summable_norm hhNorm htNorm).symm
          _ = (∑' m : ℕ, (r 0) ^ m) * ∏ i : Fin n, ∑' m : ℕ, (r i.succ) ^ m := by
                rw [htail.2]
          _ = ∏ i : Fin (n + 1), ∑' m : ℕ, (r i) ^ m := by
                rw [Fin.prod_univ_succ]

/-- The exponent-vector sum is the product of its independent one-prime sums. -/
theorem exponentPartition_eq_separatedPartition
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, 1 < p) (hβ : 0 < β) :
    exponentPartition S β = separatedPartition S β := by
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let r : Fin (Fintype.card S) → ℝ := fun i ↦ localRatio (e.symm i).1 β
  have hr0 : ∀ i, 0 ≤ r i := fun i ↦ localRatio_nonneg _ _
  have hr1 : ∀ i, r i < 1 := by
    intro i
    apply localRatio_lt_one (hβ := hβ)
    exact hS (e.symm i).1 (e.symm i).2
  have hfin := (finWeight_summable_and_tsum (Fintype.card S) r hr0 hr1).2
  let E : (S → ℕ) ≃ (Fin (Fintype.card S) → ℕ) :=
    Equiv.piCongrLeft' (fun _ : S ↦ ℕ) e
  have hweight (k : S → ℕ) :
      exponentWeight S β k = finWeight r (E k) := by
    unfold exponentWeight finWeight
    rw [← e.prod_comp]
    simp [r, E]
  calc
    exponentPartition S β
        = ∑' j : Fin (Fintype.card S) → ℕ, finWeight r j := by
            unfold exponentPartition
            rw [← E.tsum_eq]
            exact tsum_congr hweight
    _ = ∏ i : Fin (Fintype.card S), ∑' m : ℕ, (r i) ^ m := hfin
    _ = ∏ p : S, ∑' m : ℕ, (localRatio p.1 β) ^ m := by
          rw [← e.prod_comp]
          simp [r]
    _ = separatedPartition S β := by
          unfold separatedPartition
          exact Finset.prod_coe_sort

/-- Prime-indexed exponent-vector partition sum equals the finite Euler product. -/
theorem exponentPartition_eq_finiteEulerProduct_of_prime
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    exponentPartition S β = finiteEulerProduct S β := by
  rw [exponentPartition_eq_separatedPartition
    (fun p hp ↦ (hS p hp).one_lt) hβ,
    separatedPartition_eq_finiteEulerProduct_of_prime hS hβ]

@[simp] theorem exponentPartition_empty (β : ℝ) :
    exponentPartition ∅ β = 1 := by
  simp [exponentPartition, exponentWeight]

end

end BostConnes
end BrickPileLean
