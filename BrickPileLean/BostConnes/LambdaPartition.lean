import BrickPileLean.BostConnes.FinitePrimeSemigroup

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- The literal partition sum over the finite prime semigroup `Λ_S`. -/
def lambdaPartition (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∑' n : finitePrimeSemigroup S, (n.1 : ℝ) ^ (-β)

/-- The exponent-vector Boltzmann weight is exactly the corresponding integer weight. -/
theorem exponentWeight_eq_semigroupElement_rpow
    {S : Finset ℕ} (k : ExponentVector S) (β : ℝ) :
    exponentWeight S β k = (semigroupElement S k : ℝ) ^ (-β) := by
  unfold exponentWeight semigroupElement localRatio
  rw [Nat.cast_prod]
  simp_rw [Nat.cast_pow]
  calc
    (∏ p : S, ((p.1 : ℝ) ^ (-β)) ^ k p)
        = ∏ p : S, ((p.1 : ℝ) ^ k p) ^ (-β) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p.1)]
            rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p.1)]
            congr 1
            ring
    _ = (∏ p : S, (p.1 : ℝ) ^ k p) ^ (-β) := by
          simpa using
            (Real.finsetProd_rpow (Finset.univ : Finset S)
              (fun p : S ↦ (p.1 : ℝ) ^ k p)
              (fun p _ ↦ pow_nonneg (Nat.cast_nonneg p.1) _)
              (-β))

/-- For a finite set of primes, the exponent-vector partition is the literal sum over `Λ_S`. -/
theorem exponentPartition_eq_lambdaPartition
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ) :
    exponentPartition S β = lambdaPartition S β := by
  let e := exponentVectorEquivFinitePrimeSemigroup S hS
  unfold exponentPartition lambdaPartition
  rw [← e.tsum_eq]
  apply tsum_congr
  intro k
  rw [exponentWeight_eq_semigroupElement_rpow]
  rfl

/-- The finite Bost--Connes partition function, literally indexed by `Λ_S`, is its Euler product. -/
theorem lambdaPartition_eq_finiteEulerProduct_of_prime
    {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    lambdaPartition S β = finiteEulerProduct S β := by
  rw [← exponentPartition_eq_lambdaPartition hS β]
  exact exponentPartition_eq_finiteEulerProduct_of_prime hS hβ

@[simp] theorem lambdaPartition_empty (β : ℝ) :
    lambdaPartition ∅ β = 1 := by
  have hprime : ∀ p ∈ (∅ : Finset ℕ), Nat.Prime p := by simp
  rw [← exponentPartition_eq_lambdaPartition hprime β]
  exact exponentPartition_empty β

end

end BostConnes
end BrickPileLean
