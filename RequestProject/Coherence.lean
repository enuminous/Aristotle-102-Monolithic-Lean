module

public import Mathlib

/-!
# Laws of the coherence order parameter (ME-024, ME-025) and the Red Queen law (ME-062, ME-063)
-/

@[expose] public section

namespace EFMW

/-- ME-025: the coherence potential `U(Φ) = (a/4)Φ⁴ − (b/2)Φ²`. -/
noncomputable def U (a b Φ : ℝ) : ℝ := (a / 4) * Φ ^ 4 - (b / 2) * Φ ^ 2

/-- `U` is even: coherent states `±Φ` are energetically equivalent. -/
theorem U_even (a b Φ : ℝ) : U a b (-Φ) = U a b Φ := by
  unfold U; ring

/-- The force law: `U'(Φ) = aΦ³ − bΦ`, so the deterministic, uncoupled part of
ME-024 (`τ Φ̇ = bΦ − aΦ³`) is exactly the gradient flow `τ Φ̇ = −U'(Φ)`. -/
theorem U_hasDerivAt (a b Φ : ℝ) : HasDerivAt (U a b) (a * Φ ^ 3 - b * Φ) Φ := by
  have := (((hasDerivAt_pow 4 Φ).const_mul (a / 4)).sub ((hasDerivAt_pow 2 Φ).const_mul (b / 2)))
  exact this.congr_deriv (by push_cast; ring)

/-- Critical points (equilibria of the uncoupled ME-024): for `a, b > 0` they are exactly
`Φ = 0` and `Φ = ±√(b/a)`. -/
theorem U_critical_iff {a b : ℝ} (ha : 0 < a) (Φ : ℝ) :
    a * Φ ^ 3 - b * Φ = 0 ↔ Φ = 0 ∨ Φ ^ 2 = b / a := by
  constructor
  · intro h
    have : Φ * (a * Φ ^ 2 - b) = 0 := by linarith [h]
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl h1
    · right; field_simp; linarith
  · rintro (h | h)
    · simp [h]
    · have : a * Φ ^ 2 = b := by field_simp at h; linarith
      have : a * Φ ^ 3 = b * Φ := by rw [← this]; ring
      linarith

/-- Double-well law: for `a > 0` the potential is bounded below by `−b²/(4a)`,
with equality exactly on the coherent states `Φ² = b/a`. -/
theorem U_ge_min {a : ℝ} (ha : 0 < a) (b Φ : ℝ) :
    -(b ^ 2) / (4 * a) ≤ U a b Φ ∧ (U a b Φ = -(b ^ 2) / (4 * a) ↔ Φ ^ 2 = b / a) := by
  have key : U a b Φ - (-(b ^ 2) / (4 * a)) = (a / 4) * (Φ ^ 2 - b / a) ^ 2 := by
    unfold U; field_simp; ring
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (a / 4) * (Φ ^ 2 - b / a) ^ 2 := by positivity
    linarith
  · constructor
    · intro h
      have : (a / 4) * (Φ ^ 2 - b / a) ^ 2 = 0 := by linarith
      have h4 : (a / 4) ≠ 0 := by positivity
      have := (mul_eq_zero.1 this).resolve_left h4
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · intro h
      have : (a / 4) * (Φ ^ 2 - b / a) ^ 2 = 0 := by rw [h]; ring
      linarith

/-- Lyapunov law for ME-024 (uncoupled, noise-free part): along any solution of
`τ Φ̇ = bΦ − aΦ³` with `τ > 0`, the coherence potential satisfies
`d/dt U(Φ(t)) = −(U'(Φ))²/τ ≤ 0`, hence `U(Φ(t))` never increases. -/
theorem U_lyapunov {a b τ : ℝ} (hτ : 0 < τ) (Φ : ℝ → ℝ)
    (hΦ : ∀ t, HasDerivAt Φ ((b * Φ t - a * Φ t ^ 3) / τ) t) :
    (∀ t, HasDerivAt (fun s => U a b (Φ s)) (-(a * Φ t ^ 3 - b * Φ t) ^ 2 / τ) t) ∧
      Antitone (fun s => U a b (Φ s)) := by
  have hd : ∀ t, HasDerivAt (fun s => U a b (Φ s)) (-(a * Φ t ^ 3 - b * Φ t) ^ 2 / τ) t := by
    intro t
    have := (U_hasDerivAt a b (Φ t)).comp t (hΦ t)
    convert this using 1
    field_simp
    ring
  refine ⟨hd, ?_⟩
  apply antitone_of_deriv_nonpos
  · intro t; exact (hd t).differentiableAt
  · intro t
    rw [(hd t).deriv]
    have : 0 ≤ (a * Φ t ^ 3 - b * Φ t) ^ 2 / τ := by positivity
    rw [neg_div]
    linarith

/-- ME-062: right-hand side of the Red Queen equation
`dC/dt = αC(1 − C/K) − βD + γ dD/dt`. -/
noncomputable def redQueenRHS (α K β γ C D Ddot : ℝ) : ℝ :=
  α * C * (1 - C / K) - β * D + γ * Ddot

/-- ME-063 derived from ME-062: `dC/dt = 0` iff `αC(1 − C/K) = βD − γḊ`. -/
theorem redQueen_equilibrium (α K β γ C D Ddot : ℝ) :
    redQueenRHS α K β γ C D Ddot = 0 ↔ α * C * (1 - C / K) = β * D - γ * Ddot := by
  unfold redQueenRHS; constructor <;> intro h <;> linarith

/-- New law from ME-063 (maximum sustainable disorder load): for `α, K > 0` an
equilibrium coherence exists iff the net disorder load satisfies `βD − γḊ ≤ αK/4`.
Above this threshold coherence must decline (no Red Queen equilibrium). -/
theorem redQueen_equilibrium_exists_iff {α K : ℝ} (hα : 0 < α) (hK : 0 < K) (β γ D Ddot : ℝ) :
    (∃ C, redQueenRHS α K β γ C D Ddot = 0) ↔ β * D - γ * Ddot ≤ α * K / 4 := by
  simp only [redQueen_equilibrium]
  constructor
  · rintro ⟨C, hC⟩
    have : α * C * (1 - C / K) = α * K / 4 - (α / K) * (C - K / 2) ^ 2 := by
      field_simp; ring
    have : 0 ≤ (α / K) * (C - K / 2) ^ 2 := by positivity
    linarith
  · intro h
    set s := β * D - γ * Ddot
    have hnn : 0 ≤ K ^ 2 / 4 - s * K / α := by
      have : s * K / α ≤ (α * K / 4) * K / α := by gcongr
      have e : (α * K / 4) * K / α = K ^ 2 / 4 := by field_simp
      linarith
    refine ⟨K / 2 + Real.sqrt (K ^ 2 / 4 - s * K / α), ?_⟩
    have hsq := Real.sq_sqrt hnn
    set r := Real.sqrt (K ^ 2 / 4 - s * K / α)
    have : α * (K / 2 + r) * (1 - (K / 2 + r) / K) = α * K / 4 - (α / K) * r ^ 2 := by
      field_simp; ring
    rw [this, hsq]
    field_simp
    ring

end EFMW
