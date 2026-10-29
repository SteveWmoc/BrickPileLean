import BrickPileLean.BostConnes.FiniteHamiltonianSelfAdjoint
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators Topology

noncomputable section

/-- A basis vector paired with its Hamiltonian image. The finite span of
these pairs is the graph of the Hamiltonian on finite basis sums. -/
def hamiltonianGraphBasis (S : Finset ℕ) (n : finitePrimeSemigroup S) :
    FiniteHilbertSpace S × FiniteHilbertSpace S :=
  (basisVector S n, (finiteEnergy n : ℂ) • basisVector S n)

/-- Every finite basis graph pair belongs to the natural Hamiltonian graph. -/
theorem hamiltonianGraphBasis_span_le (S : Finset ℕ) :
    Submodule.span ℂ (Set.range (hamiltonianGraphBasis S)) ≤
      (finiteHamiltonianPMap S).graph := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  change (basisVector S n, (finiteEnergy n : ℂ) • basisVector S n) ∈ _
  rw [← finiteHamiltonian_basisVector S n]
  exact (finiteHamiltonianPMap S).mem_graph (hamiltonianBasisVector S n)

/-- The same finite basis truncations approximate a domain vector and its
Hamiltonian image simultaneously, i.e. in the graph topology. -/
theorem hasSum_hamiltonianGraphBasis (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    HasSum (fun n : finitePrimeSemigroup S => x.1 n • hamiltonianGraphBasis S n)
      (x.1, finiteHamiltonian S x) := by
  have hfun :
      (fun n : finitePrimeSemigroup S => x.1 n • hamiltonianGraphBasis S n) =
      (fun n => (x.1 n • basisVector S n,
        finiteHamiltonian S x n • basisVector S n)) := by
    funext n
    apply Prod.ext
    · rfl
    · change x.1 n • ((finiteEnergy n : ℂ) • basisVector S n) =
        ((finiteEnergy n : ℂ) * x.1 n) • basisVector S n
      rw [smul_smul, mul_comm]
  rw [hfun]
  exact (hasSum_basisVector S x.1).prodMk
    (hasSum_basisVector S (finiteHamiltonian S x))

/-- Finite basis sums are an operator core: closing their graph recovers
exactly the full natural Hamiltonian graph, not merely its ambient domain. -/
theorem hamiltonianGraphBasis_span_topologicalClosure (S : Finset ℕ) :
    (Submodule.span ℂ (Set.range (hamiltonianGraphBasis S))).topologicalClosure =
      (finiteHamiltonianPMap S).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (hamiltonianGraphBasis_span_le S)
      (finiteHamiltonianPMap_isClosed S)
  · intro z hz
    obtain ⟨x, rfl⟩ := ((finiteHamiltonianPMap S).mem_graph_iff').1 hz
    refine mem_closure_of_tendsto (hasSum_hamiltonianGraphBasis S x)
      (Filter.Eventually.of_forall ?_)
    intro F
    change (∑ n ∈ F, x.1 n • hamiltonianGraphBasis S n) ∈
      Submodule.span ℂ (Set.range (hamiltonianGraphBasis S))
    exact Submodule.sum_mem _ (fun n _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩))

end

end BostConnes
end BrickPileLean
