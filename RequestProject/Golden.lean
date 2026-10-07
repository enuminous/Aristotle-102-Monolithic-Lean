module

public import Mathlib

/-!
# Golden-ratio laws behind the Scalar-φ constructs (ME-041 … ME-046, ME-085 … ME-088)

All statements use the corpus definition `φ = (1 + √5)/2` (ME-041).
-/

@[expose] public section

namespace EFMW

/-- ME-041: the golden ratio `φ = (1 + √5)/2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_eq_goldenRatio : phi = Real.goldenRatio := rfl

lemma phi_pos : 0 < phi := Real.goldenRatio_pos

/-- Defining law of ME-041: `φ² = φ + 1`. -/
theorem phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq

/-- `φ − 1 = 1/φ`: the residual weight of ME-046 is the reciprocal of `φ`. -/
theorem phi_sub_one : phi - 1 = phi⁻¹ := by
  have h := phi_pos
  have h2 := phi_sq
  field_simp
  nlinarith

/-- Fibonacci law: `φ^(n+1) = F(n+1)·φ + F(n)` for every `n`. -/
theorem phi_pow_succ (n : ℕ) :
    phi ^ (n + 1) = (Nat.fib (n + 1) : ℝ) * phi + Nat.fib n := by
  rw [phi_eq_goldenRatio, ← Real.goldenRatio_mul_fib_succ_add_fib]
  ring

/-- ME-042: `Φ₂₃ = φ²³ = 28657 φ + 17711` (Fibonacci numbers `F₂₃`, `F₂₂`). -/
theorem scalar23_closed_form : phi ^ 23 = 28657 * phi + 17711 := by
  have := phi_pow_succ 22
  norm_num [Nat.fib_add_two] at this
  simpa using this

/-- ME-043: `Φ₄₆ = φ⁴⁶ = (φ²³)² = 1836311903 φ + 1134903170`. -/
theorem scalar46_closed_form :
    phi ^ 46 = (phi ^ 23) ^ 2 ∧ phi ^ 46 = 1836311903 * phi + 1134903170 := by
  refine ⟨by rw [← pow_mul], ?_⟩
  have := phi_pow_succ 45
  norm_num [Nat.fib_add_two] at this
  simpa using this

/-- ME-044: `V₁₃ = φ¹³ = 233 φ + 144`. -/
theorem veto13_closed_form : phi ^ 13 = 233 * phi + 144 := by
  have := phi_pow_succ 12
  norm_num [Nat.fib_add_two] at this
  simpa using this

/-- ME-046: the φ-tiled coherence operator `C_φ[X] = A(φX) + (φ − 1)(X − A(φX))`,
for an arbitrary averaging operator `A` on a real vector space. -/
noncomputable def phiTiled {E : Type*} [AddCommGroup E] [Module ℝ E] (A : E → E) (X : E) : E :=
  A (phi • X) + (phi - 1) • (X - A (phi • X))

/-- ME-046 law: `C_φ` is the convex combination `C_φ[X] = φ⁻¹ • X + φ⁻² • A(φX)`,
with weights `φ⁻¹ + φ⁻² = 1`. -/
theorem phiTiled_convex {E : Type*} [AddCommGroup E] [Module ℝ E] (A : E → E) (X : E) :
    phiTiled A X = phi⁻¹ • X + (phi⁻¹) ^ 2 • A (phi • X) ∧ phi⁻¹ + (phi⁻¹) ^ 2 = 1 := by
  have h1 : phi - 1 = phi⁻¹ := phi_sub_one
  have h2 : phi⁻¹ + (phi⁻¹) ^ 2 = 1 := by
    have hp := phi_pos
    have := phi_sq
    field_simp
    nlinarith
  refine ⟨?_, h2⟩
  have h3 : (1 : ℝ) - phi⁻¹ = (phi⁻¹) ^ 2 := by linarith
  unfold phiTiled
  rw [h1, smul_sub, ← h3, sub_smul, one_smul]
  abel

/-- ME-085: the Scalar-23 operator `S₂₃(X) = φ²³ X` as a linear map. -/
noncomputable def S23 {E : Type*} [AddCommGroup E] [Module ℝ E] : E →ₗ[ℝ] E :=
  (phi ^ 23) • LinearMap.id

/-- ME-085 law: `S₂₃` is invertible, with inverse `X ↦ φ⁻²³ X`. -/
theorem S23_inverse {E : Type*} [AddCommGroup E] [Module ℝ E] (X : E) :
    (phi ^ 23)⁻¹ • S23 X = X ∧ S23 ((phi ^ 23)⁻¹ • X) = X := by
  have h : phi ^ 23 ≠ 0 := pow_ne_zero _ phi_pos.ne'
  simp [S23, smul_smul, h]

/-- ME-086/088 law (a no-go): since `S₂₃` is linear, the "rebirth" of the null state
is null, `S₂₃(0) = 0`, and `S₂₃ X = 0` only for `X = 0`. A null state cannot be
turned into a non-zero coherent state by Scalar-23 scaling. -/
theorem S23_null {E : Type*} [AddCommGroup E] [Module ℝ E] (X : E) :
    S23 (0 : E) = 0 ∧ (S23 X = 0 ↔ X = 0) := by
  have h : phi ^ 23 ≠ 0 := pow_ne_zero _ phi_pos.ne'
  simp [S23, h]

end EFMW
