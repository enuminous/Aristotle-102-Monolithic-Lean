module

public import Mathlib

/-!
# Algebraic laws of the field, quantum, cognitive-PDE and recursion clusters

Field equations are treated *pointwise*: derivatives at a spacetime point are represented
by their numerical values (gradient components, Hessian components, Laplacian, …), so the
statements below are exact algebraic identities between the corpus equations.
-/

@[expose] public section

open scoped InnerProductSpace

namespace EFMW

/-! ### ME-003 ⇒ ME-004: flat d'Alembertian -/

/-- Minkowski inverse metric in coordinates `(t, x, y, z)` with signature `(+ − − −)`. -/
noncomputable def minkInv (c : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun μ ν => if μ = ν then (if μ = 0 then 1 / c ^ 2 else -1) else 0

/-- ME-003 (`□φ = g^{μν} ∇_μ∇_νφ`) in flat spacetime is ME-004:
`□φ = (1/c²) ∂²φ/∂t² − ∇²φ`, where `H` is the Hessian of `φ` at the point. -/
theorem dAlembert_flat (c : ℝ) (H : Fin 4 → Fin 4 → ℝ) :
    ∑ μ, ∑ ν, minkInv c μ ν * H μ ν = (1 / c ^ 2) * H 0 0 - (H 1 1 + H 2 2 + H 3 3) := by
  simp [minkInv, Fin.sum_univ_four]
  ring

/-! ### ME-002 + ME-004 ⇒ ME-005, and the role of `α` -/

/-- ME-005, left-hand side, from the values `φtt = ∂²φ/∂t²` and `lap = ∇²φ`. -/
noncomputable def me005LHS (c α φtt lap : ℝ) : ℝ :=
  (1 / c ^ 2) * φtt - lap - (α ^ 2 / c ^ 2) * φtt

/-- ME-005 law: the expanded scalar equation is `((1 − α²)/c²) ∂²φ/∂t² − ∇²φ = (4π/c²)(E + Pc)`.
Hence it is a wave equation with effective speed `c/√(1 − α²)` only when `α² < 1`; for
`α² = 1` the time derivative drops out and ME-002 degenerates to the Poisson equation
`−∇²φ = (4π/c²)(E + Pc)` (no propagation at all). -/
theorem me005_reduction (c α φtt lap E P : ℝ) :
    me005LHS c α φtt lap = ((1 - α ^ 2) / c ^ 2) * φtt - lap ∧
    (α ^ 2 = 1 →
      (me005LHS c α φtt lap = (4 * Real.pi / c ^ 2) * (E + P * c) ↔
        -lap = (4 * Real.pi / c ^ 2) * (E + P * c))) := by
  have h : me005LHS c α φtt lap = ((1 - α ^ 2) / c ^ 2) * φtt - lap := by
    unfold me005LHS; ring
  refine ⟨h, fun hα => ?_⟩
  rw [h, hα]; simp

/-! ### ME-006, ME-007, ME-008, ME-015: informational tensor vs. scalar stress tensor -/

variable {ι : Type*}

/-- ME-015: scalar stress tensor `T^φ_{μν} = ∇_μφ∇_νφ − g_{μν}[(1/2)(∇φ)² + V(φ)]`, where
`dφ` are the gradient components and `gradSq = ∇_αφ∇^αφ`. -/
noncomputable def scalarStress (g : ι → ι → ℝ) (dφ : ι → ℝ) (gradSq V : ℝ) : ι → ι → ℝ :=
  fun μ ν => dφ μ * dφ ν - g μ ν * ((1 / 2) * gradSq + V)

/-- ME-006: Wright informational tensor
`I_{μν} = ∇_μφ∇_νφ − (1/2)g_{μν}(∇φ)² − g_{μν}V(φ) + R_{μν}`. -/
noncomputable def infoTensor (g : ι → ι → ℝ) (dφ : ι → ℝ) (gradSq V : ℝ) (R : ι → ι → ℝ) : ι → ι → ℝ :=
  fun μ ν => dφ μ * dφ ν - (1 / 2) * g μ ν * gradSq - g μ ν * V + R μ ν

/-- Law ME-006 = ME-015 + R: the informational tensor is exactly the standard scalar
stress-energy tensor plus the Ricci-type term `R_{μν}`. -/
theorem infoTensor_eq_stress_add (g : ι → ι → ℝ) (dφ : ι → ℝ) (gradSq V : ℝ)
    (R : ι → ι → ℝ) :
    infoTensor g dφ gradSq V R = fun μ ν => scalarStress g dφ gradSq V μ ν + R μ ν := by
  funext μ ν; simp only [infoTensor, scalarStress]; ring

/-- Law ME-007 ⇔ ME-008: `G + Λg = 8πG(T + κI)` is the same equation as its expansion
`G + Λg = 8πG T + 8πGκ[∇φ∇φ − (1/2)g(∇φ)² − gV + R]`, componentwise. -/
theorem einstein_expanded (Gμν g T R : ι → ι → ℝ) (dφ : ι → ℝ) (gradSq V Λ Gn κ : ℝ)
    (μ ν : ι) :
    (Gμν μ ν + Λ * g μ ν = 8 * Real.pi * Gn * (T μ ν + κ * infoTensor g dφ gradSq V R μ ν)) ↔
    (Gμν μ ν + Λ * g μ ν = 8 * Real.pi * Gn * T μ ν + 8 * Real.pi * Gn * κ *
      (dφ μ * dφ ν - (1 / 2) * g μ ν * gradSq - g μ ν * V + R μ ν)) := by
  simp only [infoTensor]; constructor <;> intro h <;> linarith

/-! ### ME-016 ⇒ ME-017 -/

/-- ME-017 from ME-016: for `ψ = ρ e^{iθ}` with real amplitude `ρ`, `|ψ|² = ρ²`. -/
theorem polar_density (ρ θ : ℝ) : ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 = ρ ^ 2 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]
  simp [sq_abs]

/-! ### ME-036 / ME-037: the coupled S–O equations -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- ME-036 right-hand side at a point: values `S`, `lapS = ΔS`, gradients `gS`, `gO`. -/
noncomputable def puddleRHS (α β Pr S0 lam V13 S lapS : ℝ) (gS gO : F) : ℝ :=
  lapS + α * ⟪gS, gO⟫_ℝ + β * ⟪gO, gS⟫_ℝ - (S - S ^ 3) - Pr * (S - S0) + lam * V13

/-- ME-036/037 law: (i) the two cross-coupling constants enter only through `α + β`
(because the dot product is symmetric), and (ii) the O-equation ME-037 is the S-equation
ME-036 with the roles of `S` and `O` exchanged. -/
theorem puddle_laws (α β Pr S0 O0 lam V13 S lapS O lapO : ℝ) (gS gO : F) :
    puddleRHS α β Pr S0 lam V13 S lapS gS gO =
      lapS + (α + β) * ⟪gS, gO⟫_ℝ - (S - S ^ 3) - Pr * (S - S0) + lam * V13 ∧
    puddleRHS α β Pr O0 lam V13 O lapO gO gS =
      lapO + α * ⟪gO, gS⟫_ℝ + β * ⟪gS, gO⟫_ℝ - (O - O ^ 3) - Pr * (O - O0) + lam * V13 := by
  refine ⟨?_, rfl⟩
  unfold puddleRHS
  rw [real_inner_comm gO gS]; ring

/-! ### Recursion laws -/

/-- ME-065 law: in any monoid of transformations, observer–observed closure
`O_{n+1} = O_n ∘ S_n`, `S_{n+1} = S_n ∘ O_{n+1}` forces `S_{n+1} = S_n ∘ O_n ∘ S_n`. -/
theorem closure_law {M : Type*} [Monoid M] (O S : ℕ → M)
    (hO : ∀ n, O (n + 1) = O n * S n) (hS : ∀ n, S (n + 1) = S n * O (n + 1)) (n : ℕ) :
    S (n + 1) = S n * O n * S n := by
  rw [hS, hO, mul_assoc]

/-- ME-073/074 law: if time reversal `T` is an involution and conjugates the forward
step `U` to its inverse (`T⁻¹ U T = U⁻¹`), then `T ∘ U` is itself an involution. -/
theorem chronologos_involution {G : Type*} [Group G] (T U : G) (hT : T * T = 1)
    (hU : T⁻¹ * U * T = U⁻¹) : (T * U) * (T * U) = 1 := by
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hT
  rw [hTinv] at hU
  calc (T * U) * (T * U) = (T * U * T) * U := by group
    _ = 1 := by rw [hU]; group

/-- ME-094 / ME-101 law: with constant coherence `C`, the linear recursions
`E_{n+1} = E_n + ΔE·C` and `I_{t+1} = I_t + λC` have closed form `E_n = E_0 + n·ΔE·C`;
in particular they grow without bound whenever `ΔE·C > 0` (no saturation). -/
theorem linear_accumulation (E : ℕ → ℝ) (dE C : ℝ) (h : ∀ n, E (n + 1) = E n + dE * C)
    (n : ℕ) : E n = E 0 + n * (dE * C) := by
  induction n with
  | zero => simp
  | succ k ih => rw [h, ih]; push_cast; ring

end EFMW
