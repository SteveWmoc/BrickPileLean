import BrickPileLean.BostConnes.FiniteHamiltonianSymmetry
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators LinearPMap

noncomputable section

/-- The logarithmic Hamiltonian packaged as a partially defined linear
operator, retaining exactly its natural domain. -/
def finiteHamiltonianPMap (S : Finset ℕ) :
    FiniteHilbertSpace S →ₗ.[ℂ] FiniteHilbertSpace S where
  domain := finiteHamiltonianDomain S
  toFun := finiteHamiltonian S

/-- The Hamiltonian is its own formal adjoint on the natural domain. -/
theorem finiteHamiltonianPMap_isFormalAdjoint (S : Finset ℕ) :
    (finiteHamiltonianPMap S).IsFormalAdjoint (finiteHamiltonianPMap S) :=
  finiteHamiltonian_symmetric S

/-- Symmetry and density give inclusion in the Hilbert-space adjoint. -/
theorem finiteHamiltonianPMap_le_adjoint (S : Finset ℕ) :
    finiteHamiltonianPMap S ≤ (finiteHamiltonianPMap S).adjoint := by
  exact LinearPMap.IsFormalAdjoint.le_adjoint
    (finiteHamiltonianDomain_dense S) (finiteHamiltonianPMap_isFormalAdjoint S)

/-- Testing the adjoint identity on each canonical basis vector forces the
adjoint to have the same logarithmic coordinate multiplier. -/
theorem finiteHamiltonian_adjoint_apply_coordinate (S : Finset ℕ)
    (y : (finiteHamiltonianPMap S).adjoint.domain) (n : finitePrimeSemigroup S) :
    (finiteHamiltonianPMap S).adjoint y n = (finiteEnergy n : ℂ) * y.1 n := by
  have hformal : (finiteHamiltonianPMap S).IsFormalAdjoint
      (finiteHamiltonianPMap S).adjoint :=
    (LinearPMap.adjoint_isFormalAdjoint
      (T := finiteHamiltonianPMap S) (finiteHamiltonianDomain_dense S)).symm
  have h := hformal (hamiltonianBasisVector S n) y
  change inner ℂ (finiteHamiltonian S (hamiltonianBasisVector S n)) y.1 =
    inner ℂ (basisVector S n) ((finiteHamiltonianPMap S).adjoint y) at h
  rw [finiteHamiltonian_basisVector, inner_smul_left] at h
  simpa [basisVector, lp.inner_single_left] using h.symm

/-- Every vector in the adjoint domain belongs to the natural Hamiltonian
domain because its energy-weighted coordinates form the adjoint output in ℓ². -/
theorem finiteHamiltonian_adjoint_domain_le (S : Finset ℕ) :
    (finiteHamiltonianPMap S).adjoint.domain ≤ finiteHamiltonianDomain S := by
  intro y hy
  change Memℓp (finiteHamiltonianCoefficients S y) 2
  have hcoords : finiteHamiltonianCoefficients S y =
      ⇑((finiteHamiltonianPMap S).adjoint ⟨y, hy⟩) := by
    funext n
    exact (finiteHamiltonian_adjoint_apply_coordinate S ⟨y, hy⟩ n).symm
  rw [hcoords]
  exact lp.memℓp _

/-- The adjoint domain is exactly the natural logarithmic Hamiltonian domain. -/
theorem finiteHamiltonian_adjoint_domain (S : Finset ℕ) :
    (finiteHamiltonianPMap S).adjoint.domain = finiteHamiltonianDomain S := by
  exact le_antisymm (finiteHamiltonian_adjoint_domain_le S)
    (finiteHamiltonianPMap_le_adjoint S).1

/-- Explicit square-summability characterization of the adjoint domain. -/
theorem mem_finiteHamiltonian_adjoint_domain_iff (S : Finset ℕ)
    (y : FiniteHilbertSpace S) :
    y ∈ (finiteHamiltonianPMap S).adjoint.domain ↔
      Summable (fun n : finitePrimeSemigroup S => (finiteEnergy n) ^ 2 * ‖y n‖ ^ 2) := by
  rw [finiteHamiltonian_adjoint_domain]
  exact mem_finiteHamiltonianDomain_iff S y

/-- Equality with the Hilbert-space adjoint as partially defined operators:
both the domains and the actions agree. -/
theorem finiteHamiltonianPMap_adjoint_eq (S : Finset ℕ) :
    (finiteHamiltonianPMap S).adjoint = finiteHamiltonianPMap S := by
  exact (LinearPMap.eq_of_le_of_domain_eq (finiteHamiltonianPMap_le_adjoint S)
    (finiteHamiltonian_adjoint_domain S).symm).symm

/-- The logarithmic Hamiltonian is self-adjoint in mathlib's unbounded
(partially defined) operator API. No primality assumption is needed. -/
theorem finiteHamiltonianPMap_isSelfAdjoint (S : Finset ℕ) :
    IsSelfAdjoint (finiteHamiltonianPMap S) := by
  exact LinearPMap.isSelfAdjoint_def.mpr (finiteHamiltonianPMap_adjoint_eq S)

/-- The graph of the logarithmic Hamiltonian is closed. This does not assert
that its domain is closed in the ambient Hilbert norm. -/
theorem finiteHamiltonianPMap_isClosed (S : Finset ℕ) :
    (finiteHamiltonianPMap S).IsClosed :=
  (finiteHamiltonianPMap_isSelfAdjoint S).isClosed

end

end BostConnes
end BrickPileLean
