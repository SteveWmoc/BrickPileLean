import BrickPileLean.BostConnes.FiniteGibbsPositive
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace BrickPileLean
namespace BostConnes

open Filter
open scoped BigOperators Topology

noncomputable section

/-- A canonical basis projection factors through the one-dimensional scalar
space, hence is compact. -/
theorem basisProjection_isCompactOperator (S : Finset ℕ)
    (n : finitePrimeSemigroup S) : IsCompactOperator (basisProjection S n) := by
  unfold basisProjection
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ (basisVector S n))).comp_clm
      (innerSL ℂ (basisVector S n))

/-- Every rank-one Gibbs summand is compact, independently of summability. -/
theorem gibbsOperatorTerm_isCompactOperator {S : Finset ℕ} (β : ℝ)
    (n : finitePrimeSemigroup S) : IsCompactOperator (gibbsOperatorTerm β n) := by
  exact (basisProjection_isCompactOperator S n).smul (gibbsWeight β n : ℂ)

/-- The operator-norm size of each rank-one summand is exactly its Gibbs weight. -/
theorem norm_gibbsOperatorTerm {S : Finset ℕ} (β : ℝ)
    (n : finitePrimeSemigroup S) : ‖gibbsOperatorTerm β n‖ = gibbsWeight β n := by
  simp [gibbsOperatorTerm, norm_smul, gibbsWeight_nonneg]

/-- The absolute operator-norm sum of the rank-one expansion is the partition
function. This statement does not yet assert trace-norm convergence. -/
theorem tsum_norm_gibbsOperatorTerm (S : Finset ℕ) (β : ℝ) :
    (∑' n : finitePrimeSemigroup S, ‖gibbsOperatorTerm β n‖) = lambdaPartition S β := by
  simp only [norm_gibbsOperatorTerm]
  rfl

/-- Finite rank-one truncations of the Gibbs operator. -/
def gibbsOperatorPartialSum (S : Finset ℕ) (β : ℝ)
    (F : Finset (finitePrimeSemigroup S)) : FiniteOperator S :=
  ∑ n ∈ F, gibbsOperatorTerm β n

/-- Every finite truncation is a compact operator. -/
theorem gibbsOperatorPartialSum_isCompactOperator (S : Finset ℕ) (β : ℝ)
    (F : Finset (finitePrimeSemigroup S)) :
    IsCompactOperator (gibbsOperatorPartialSum S β F) := by
  exact (compactOperator (RingHom.id ℂ) (FiniteHilbertSpace S) (FiniteHilbertSpace S)).sum_mem
    (fun n _ => gibbsOperatorTerm_isCompactOperator β n)

/-- At positive inverse temperature, finite rank-one truncations converge to
`D_β` in operator norm, not merely pointwise on vectors. -/
theorem tendsto_gibbsOperatorPartialSum {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    Tendsto (gibbsOperatorPartialSum S β) atTop (𝓝 (gibbsOperator S β)) :=
  (gibbsOperatorTerm_summable hS hβ).hasSum

/-- The Gibbs operator is compact, as an operator-norm limit of its finite
rank-one truncations. -/
theorem gibbsOperator_isCompactOperator {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    IsCompactOperator (gibbsOperator S β) := by
  exact isCompactOperator_of_tendsto (tendsto_gibbsOperatorPartialSum hS hβ)
    (Eventually.of_forall (gibbsOperatorPartialSum_isCompactOperator S β))

end

end BostConnes
end BrickPileLean
