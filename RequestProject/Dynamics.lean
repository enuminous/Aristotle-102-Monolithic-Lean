module

public import Mathlib

/-!
# Relaxation laws (ME-078, ME-079, ME-082) and emergent time (ME-075, ME-076)
-/

@[expose] public section

open Real Filter Topology

namespace EFMW

/-- Uniqueness law for the relaxation equation ME-082, `dη/dt = (η_eq − η)/τ`:
every solution is `η(t) = η_eq + (η(0) − η_eq) e^(−t/τ)`. -/
theorem relaxation_unique {τ ηeq : ℝ} (hτ : τ ≠ 0) (η : ℝ → ℝ)
    (hη : ∀ t, HasDerivAt η ((ηeq - η t) / τ) t) (t : ℝ) :
    η t = ηeq + (η 0 - ηeq) * exp (-t / τ) := by
  set g : ℝ → ℝ := fun s => (η s - ηeq) * exp (s / τ)
  have hg : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h1 := ((hη s).sub_const ηeq).mul (((hasDerivAt_id s).div_const τ).exp)
    refine h1.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
    (fun s => (hg s).deriv) t 0
  simp only [g, zero_div, exp_zero, mul_one] at hconst
  have he : exp (t / τ) * exp (-t / τ) = 1 := by
    rw [← exp_add]; ring_nf; simp
  have : η t - ηeq = (η 0 - ηeq) * exp (-t / τ) := by
    rw [← hconst]; linear_combination -(η t - ηeq) * he
  linarith

/-- Existence half: the exponential relaxation profile solves ME-082. -/
theorem relaxation_solves {τ : ℝ} (hτ : τ ≠ 0) (ηeq η0 t : ℝ) :
    HasDerivAt (fun s => ηeq + (η0 - ηeq) * exp (-s / τ))
      ((ηeq - (ηeq + (η0 - ηeq) * exp (-t / τ))) / τ) t := by
  have h := ((((hasDerivAt_id t).neg).div_const τ).exp.const_mul (η0 - ηeq)).const_add ηeq
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, id]
  field_simp
  ring

/-- ME-078: thixotropic viscosity law `η(t) = η₀(1 − e^(−t/τ))`. -/
noncomputable def thixoViscosity (η0 τ t : ℝ) : ℝ := η0 * (1 - exp (-t / τ))

/-- ME-078 derived from ME-082: the thixotropic law solves the relaxation equation
with `η_eq = η₀`, starts from `η(0) = 0`, and is the *only* such solution. -/
theorem thixo_eq_relaxation {τ : ℝ} (hτ : τ ≠ 0) (η0 : ℝ) :
    (∀ t, HasDerivAt (thixoViscosity η0 τ) ((η0 - thixoViscosity η0 τ t) / τ) t) ∧
    thixoViscosity η0 τ 0 = 0 ∧
    (∀ η : ℝ → ℝ, (∀ t, HasDerivAt η ((η0 - η t) / τ) t) → η 0 = 0 →
      η = thixoViscosity η0 τ) := by
  refine ⟨fun t => ?_, by simp [thixoViscosity], fun η hη h0 => ?_⟩
  · have := relaxation_solves hτ η0 0 t
    have e : thixoViscosity η0 τ = fun s => η0 + (0 - η0) * exp (-s / τ) := by
      funext s; simp [thixoViscosity]; ring
    rw [e]; convert this using 2
  · funext t
    rw [relaxation_unique hτ η hη t, h0, thixoViscosity]; ring

/-- ME-078 long-time law: for `τ > 0`, `η(t) → η₀` as `t → ∞`. -/
theorem thixo_tendsto {τ : ℝ} (hτ : 0 < τ) (η0 : ℝ) :
    Tendsto (thixoViscosity η0 τ) atTop (𝓝 η0) := by
  have h : Tendsto (fun t : ℝ => exp (-t / τ)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -t / τ) atTop atBot := by
      simpa [neg_div] using (tendsto_neg_atTop_atBot.atBot_div_const hτ)
    exact tendsto_exp_atBot.comp this
  have := (h.const_sub 1).const_mul η0
  simpa [thixoViscosity] using this

/-- ME-079: neutron-decay density `ρ(t) = ρ₀ e^(−t/τₙ)`. -/
noncomputable def decayDensity (ρ0 τn t : ℝ) : ℝ := ρ0 * exp (-t / τn)

/-- ME-079 law: the density is the unique solution of `dρ/dt = −ρ/τₙ` with `ρ(0) = ρ₀`. -/
theorem decay_ode {τn : ℝ} (hτ : τn ≠ 0) (ρ0 : ℝ) :
    (∀ t, HasDerivAt (decayDensity ρ0 τn) (-decayDensity ρ0 τn t / τn) t) ∧
    (∀ ρ : ℝ → ℝ, (∀ t, HasDerivAt ρ (-ρ t / τn) t) → ρ 0 = ρ0 → ρ = decayDensity ρ0 τn) := by
  refine ⟨fun t => ?_, fun ρ hρ h0 => ?_⟩
  · have := relaxation_solves hτ 0 ρ0 t
    have e : decayDensity ρ0 τn = fun s => 0 + (ρ0 - 0) * exp (-s / τn) := by
      funext s; simp [decayDensity]
    rw [e]; convert this using 2; ring
  · funext t
    have := relaxation_unique (ηeq := 0) hτ ρ (fun s => by simpa using hρ s) t
    rw [this, h0, decayDensity]; ring

/-- ME-079 half-life law: `ρ(τₙ ln 2) = ρ₀ / 2`. -/
theorem decay_half_life {τn : ℝ} (hτ : τn ≠ 0) (ρ0 : ℝ) :
    decayDensity ρ0 τn (τn * log 2) = ρ0 / 2 := by
  have : -(τn * log 2) / τn = -log 2 := by field_simp
  rw [decayDensity, this, exp_neg, exp_log (by norm_num)]
  ring

/-- ME-076: accumulated recursive phase `Θ(t) = ∫₀ᵗ ω_rec`. -/
noncomputable def recursivePhase (ω : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, ω s

/-- ME-075 derived from ME-076: for continuous `ω_rec`, `dΘ/dt = ω_rec(t)`, i.e. `dt = dΘ/ω_rec`
wherever `ω_rec ≠ 0`; if `ω_rec > 0` everywhere, `Θ` is strictly increasing, so the emergent
phase is a legitimate clock (a strictly monotone reparametrisation of `t`). -/
theorem emergent_time {ω : ℝ → ℝ} (hω : Continuous ω) :
    (∀ t, HasDerivAt (recursivePhase ω) (ω t) t) ∧
    ((∀ t, 0 < ω t) → StrictMono (recursivePhase ω)) := by
  have hd : ∀ t, HasDerivAt (recursivePhase ω) (ω t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hω.intervalIntegrable _ _)
      (hω.stronglyMeasurableAtFilter _ _) hω.continuousAt
  refine ⟨hd, fun hpos => ?_⟩
  exact strictMono_of_hasDerivAt_pos hd hpos

end EFMW
