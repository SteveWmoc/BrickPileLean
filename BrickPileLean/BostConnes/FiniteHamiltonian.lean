import BrickPileLean.BostConnes.FiniteEnergy

namespace BrickPileLean
namespace BostConnes

open scoped ENNReal

noncomputable section

/-- Coordinate multiplication by the arithmetic energy, before imposing the
square-summability condition on the output. -/
def finiteHamiltonianCoefficients (S : Finset ℕ) :
    FiniteHilbertSpace S →ₗ[ℂ] (finitePrimeSemigroup S → ℂ) where
  toFun x n := (finiteEnergy n : ℂ) * x n
  map_add' x y := by
    funext n
    change (finiteEnergy n : ℂ) * (x n + y n) = _
    exact mul_add _ _ _
  map_smul' c x := by
    funext n
    change (finiteEnergy n : ℂ) * (c * x n) = c * ((finiteEnergy n : ℂ) * x n)
    ring

/-- The natural domain of the logarithmic Hamiltonian: vectors whose
energy-weighted coordinates still lie in `ℓ²`. It is a complex submodule,
with no claim that it is closed in the Hilbert norm. -/
def finiteHamiltonianDomain (S : Finset ℕ) : Submodule ℂ (FiniteHilbertSpace S) :=
  (lpSubmodule ℂ (fun _ : finitePrimeSemigroup S => ℂ) 2).comap
    (finiteHamiltonianCoefficients S)

/-- Membership in the Hamiltonian domain is square summability of the
energy-weighted coordinates. -/
theorem mem_finiteHamiltonianDomain_iff (S : Finset ℕ) (x : FiniteHilbertSpace S) :
    x ∈ finiteHamiltonianDomain S ↔
      Summable (fun n : finitePrimeSemigroup S => (finiteEnergy n) ^ 2 * ‖x n‖ ^ 2) := by
  change Memℓp (fun n => (finiteEnergy n : ℂ) * x n) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

/-- The logarithmic Hamiltonian, as a linear map from its natural domain
into the ambient Hilbert space. No boundedness is asserted. -/
def finiteHamiltonian (S : Finset ℕ) :
    finiteHamiltonianDomain S →ₗ[ℂ] FiniteHilbertSpace S where
  toFun x := ⟨finiteHamiltonianCoefficients S x.1, x.2⟩
  map_add' x y := by
    apply lp.ext
    exact (finiteHamiltonianCoefficients S).map_add x.1 y.1
  map_smul' c x := by
    apply lp.ext
    exact (finiteHamiltonianCoefficients S).map_smul c x.1

/-- The Hamiltonian acts by multiplication by `log n` in each coordinate. -/
@[simp] theorem finiteHamiltonian_apply (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (n : finitePrimeSemigroup S) :
    finiteHamiltonian S x n = (finiteEnergy n : ℂ) * x.1 n := rfl

/-- Energy multiplication sends a canonical basis vector to its scalar
multiple as a coordinate function. -/
theorem finiteHamiltonianCoefficients_basisVector (S : Finset ℕ)
    (n : finitePrimeSemigroup S) :
    finiteHamiltonianCoefficients S (basisVector S n) =
      ⇑((finiteEnergy n : ℂ) • basisVector S n) := by
  classical
  funext k
  change (finiteEnergy k : ℂ) * basisVector S n k =
    (finiteEnergy n : ℂ) * basisVector S n k
  by_cases h : k = n
  · subst k
    rfl
  · simp [basisVector, lp.single_apply, h]

/-- Every canonical basis vector lies in the natural Hamiltonian domain. -/
theorem basisVector_mem_finiteHamiltonianDomain (S : Finset ℕ)
    (n : finitePrimeSemigroup S) : basisVector S n ∈ finiteHamiltonianDomain S := by
  change Memℓp (finiteHamiltonianCoefficients S (basisVector S n)) 2
  rw [finiteHamiltonianCoefficients_basisVector]
  exact lp.memℓp _

/-- A canonical basis vector equipped with its Hamiltonian-domain proof. -/
def hamiltonianBasisVector (S : Finset ℕ) (n : finitePrimeSemigroup S) :
    finiteHamiltonianDomain S :=
  ⟨basisVector S n, basisVector_mem_finiteHamiltonianDomain S n⟩

/-- Canonical basis vectors are eigenvectors with eigenvalues `log n`. -/
theorem finiteHamiltonian_basisVector (S : Finset ℕ) (n : finitePrimeSemigroup S) :
    finiteHamiltonian S (hamiltonianBasisVector S n) =
      (finiteEnergy n : ℂ) • basisVector S n := by
  apply lp.ext
  exact finiteHamiltonianCoefficients_basisVector S n

/-- The vacuum basis vector has Hamiltonian eigenvalue zero. -/
@[simp] theorem finiteHamiltonian_vacuum (S : Finset ℕ) :
    finiteHamiltonian S (hamiltonianBasisVector S 1) = 0 := by
  rw [finiteHamiltonian_basisVector, finiteEnergy_one]
  simp

end

end BostConnes
end BrickPileLean
