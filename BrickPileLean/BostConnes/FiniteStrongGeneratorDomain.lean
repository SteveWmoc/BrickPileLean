import BrickPileLean.BostConnes.FiniteStrongGenerator

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- A strong orbit derivative determines every coordinate of its velocity. -/
theorem timeOperator_derivative_coordinate_zero (S : Finset ℕ)
    (x v : FiniteHilbertSpace S)
    (h : HasDerivAt (fun t : ℝ => timeOperator S t x) v 0)
    (n : finitePrimeSemigroup S) :
    v n = Complex.I * ((finiteEnergy n : ℂ) * x n) := by
  let ev := (lp.evalCLM ℂ (fun _ : finitePrimeSemigroup S => ℂ) 2 n).restrictScalars ℝ
  have hev : HasDerivAt (fun t : ℝ => timeOperator S t x n) (v n) 0 :=
    ev.hasFDerivAt.comp_hasDerivAt 0 h
  have hphase := (hasDerivAt_timePhase n 0).mul_const (x n)
  have hfun : (fun t : ℝ => timeOperator S t x n) =
      (fun t : ℝ => timePhase t n * x n) := by
    funext t
    exact timeOperator_apply_coordinate S t x n
  rw [hfun] at hev
  have heq := hev.unique hphase
  simpa only [timePhase_zero, one_mul, mul_assoc, mul_comm, mul_left_comm] using heq

/-- Strong differentiability forces the energy-weighted coordinates into
`ℓ²`, so the natural Hamiltonian domain is also necessary. -/
theorem mem_finiteHamiltonianDomain_of_hasDerivAt (S : Finset ℕ)
    (x v : FiniteHilbertSpace S)
    (h : HasDerivAt (fun t : ℝ => timeOperator S t x) v 0) :
    x ∈ finiteHamiltonianDomain S := by
  have heq : (fun n => (finiteEnergy n : ℂ) * x n) =
      ⇑((-Complex.I) • v) := by
    funext n
    change (finiteEnergy n : ℂ) * x n = (-Complex.I) * v n
    rw [timeOperator_derivative_coordinate_zero S x v h n]
    simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  change Memℓp (fun n => (finiteEnergy n : ℂ) * x n) 2
  rw [heq]
  exact lp.memℓp _

/-- The domain of the strong infinitesimal generator is exactly the natural
logarithmic Hamiltonian domain. -/
theorem differentiableAt_timeOperator_zero_iff (S : Finset ℕ)
    (x : FiniteHilbertSpace S) :
    DifferentiableAt ℝ (fun t : ℝ => timeOperator S t x) 0 ↔
      x ∈ finiteHamiltonianDomain S := by
  constructor
  · intro h
    exact mem_finiteHamiltonianDomain_of_hasDerivAt S x _ h.hasDerivAt
  · intro hx
    exact (hasDerivAt_timeOperator_zero S ⟨x, hx⟩).differentiableAt

/-- Exact graph characterization: a strong velocity at zero is precisely
`i H x`, with `x` in the natural Hamiltonian domain. -/
theorem hasDerivAt_timeOperator_zero_iff (S : Finset ℕ)
    (x v : FiniteHilbertSpace S) :
    HasDerivAt (fun t : ℝ => timeOperator S t x) v 0 ↔
      ∃ hx : x ∈ finiteHamiltonianDomain S,
        v = Complex.I • finiteHamiltonian S ⟨x, hx⟩ := by
  constructor
  · intro h
    have hx := mem_finiteHamiltonianDomain_of_hasDerivAt S x v h
    exact ⟨hx, h.unique (hasDerivAt_timeOperator_zero S ⟨x, hx⟩)⟩
  · rintro ⟨hx, rfl⟩
    exact hasDerivAt_timeOperator_zero S ⟨x, hx⟩

/-- An orbit is differentiable at all real times exactly when its initial
vector belongs to the Hamiltonian domain. -/
theorem differentiable_timeOperator_iff (S : Finset ℕ)
    (x : FiniteHilbertSpace S) :
    Differentiable ℝ (fun t : ℝ => timeOperator S t x) ↔
      x ∈ finiteHamiltonianDomain S := by
  constructor
  · intro h
    exact (differentiableAt_timeOperator_zero_iff S x).1 (h 0)
  · intro hx t
    exact (hasDerivAt_timeOperator_apply S ⟨x, hx⟩ t).differentiableAt

end

end BostConnes
end BrickPileLean
