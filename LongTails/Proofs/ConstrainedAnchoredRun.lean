import LongTails.Proofs.ConstrainedAnchoredStep
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ConstrainedMonotone

open GeneralizedMonotone (Hyp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def iter (F P : E → E) (L0 L1 : ℝ) (a : E) (s : E × E × ℝ) : E × E × ℝ :=
  (P (targetPoint a s.1 (F (halfPoint a s.1 (F s.1) s.2.1 s.2.2
      (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2))) s.2.2
      (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2)),
    (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2)⁻¹ •
      (targetPoint a s.1 (F (halfPoint a s.1 (F s.1) s.2.1 s.2.2
        (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2))) s.2.2
        (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2) -
      P (targetPoint a s.1 (F (halfPoint a s.1 (F s.1) s.2.1 s.2.2
        (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2))) s.2.2
        (stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2))),
    s.2.2 + stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2)

noncomputable def run (F P : E → E) (L0 L1 : ℝ) (a : E) : ℕ → E × E × ℝ
  | 0 => (a, 0, 0)
  | k + 1 => iter F P L0 L1 a (run F P L0 L1 a k)

omit [InnerProductSpace ℝ E] in
lemma stepSize_spec {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (a x g ξ : E) {S : ℝ}
    (hS : 0 ≤ S) (hx : S = 0 → x = a) :
    0 < stepSize L0 L1 a x g ξ S ∧
    stepSize L0 L1 a x g ξ S * (L0 + L1 * mval a x g ξ S) ≤ 1 / 4 ∧
    ‖x - a‖ ≤ (S + stepSize L0 L1 a x g ξ S) * (mval a x g ξ S - ‖g‖ - ‖g + ξ‖) ∧
    (S ≠ 0 → stepSize L0 L1 a x g ξ S ≤ S / 3) := by
  have hm : 0 ≤ mval a x g ξ S := by unfold mval; positivity
  have hden : 0 < 4 * (L0 + L1 * mval a x g ξ S) := by positivity
  have hnat : 1 / (4 * (L0 + L1 * mval a x g ξ S)) * (L0 + L1 * mval a x g ξ S) = 1 / 4 := by
    field_simp
  have hsub : mval a x g ξ S - ‖g‖ - ‖g + ξ‖ = ‖x - a‖ / S := by unfold mval; ring
  by_cases h0 : S = 0
  · have hxa : x = a := hx h0
    have hγ : stepSize L0 L1 a x g ξ S = 1 / (4 * (L0 + L1 * mval a x g ξ S)) := by
      rw [stepSize, ite_eq_left h0]
    rw [hγ, hsub]
    refine ⟨by positivity, hnat.le, ?_, fun h => absurd h0 h⟩
    subst hxa
    simp
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm h0)
    have hγ : stepSize L0 L1 a x g ξ S =
        min (S / 3) (1 / (4 * (L0 + L1 * mval a x g ξ S))) := by
      rw [stepSize, ite_eq_right h0]
    have hpos : 0 < stepSize L0 L1 a x g ξ S := by
      rw [hγ]
      exact lt_min (by positivity) (by positivity)
    refine ⟨hpos, ?_, ?_, fun _ => by rw [hγ]; exact min_le_left _ _⟩
    · have hle : stepSize L0 L1 a x g ξ S ≤ 1 / (4 * (L0 + L1 * mval a x g ξ S)) := by
        rw [hγ]
        exact min_le_right _ _
      calc stepSize L0 L1 a x g ξ S * (L0 + L1 * mval a x g ξ S)
          ≤ 1 / (4 * (L0 + L1 * mval a x g ξ S)) * (L0 + L1 * mval a x g ξ S) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 1 / 4 := hnat
    · rw [hsub]
      have hD := norm_nonneg (x - a)
      have : ‖x - a‖ = S * (‖x - a‖ / S) := by field_simp
      have h2 : 0 ≤ stepSize L0 L1 a x g ξ S * (‖x - a‖ / S) := by positivity
      nlinarith

structure Ctx (F P : E → E) (X : Set E) (L0 L1 : ℝ) (a xs : E) (R G : ℝ) : Prop where
  hyp : Hyp F L0 L1
  proj : Proj X P
  convex : Convex ℝ X
  anchor : a ∈ X
  sol : xs ∈ X
  vi : ∀ v ∈ X, 0 ≤ ⟪F xs, v - xs⟫
  dist0 : ‖a - xs‖ ≤ R
  grad : ‖F xs‖ ≤ G
  R_pos : 0 < R

structure Inv (F : E → E) (X : Set E) (a xs : E) (R : ℝ) (s : E × E × ℝ) : Prop where
  S_nonneg : 0 ≤ s.2.2
  start : s.2.2 = 0 → s.1 = a
  mem : s.1 ∈ X
  normal : Normal X s.1 s.2.1
  pot : potential a s.1 (F s.1 + s.2.1) s.2.2 ≤ 0
  dist : ‖s.1 - xs‖ ≤ 3 * R

section run

variable {F P : E → E} {X : Set E} {L0 L1 : ℝ} {a xs : E} {R G : ℝ}

lemma residual_pair (c : Ctx F P X L0 L1 a xs R G) {x ξ : E} (hx : x ∈ X)
    (hξ : Normal X x ξ) : 0 ≤ ⟪F x + ξ, x - xs⟫ := by
  have h1 := c.hyp.mono x xs
  have h2 := c.vi x hx
  have h3 := hξ xs c.sol
  have e1 : ⟪F x + ξ, x - xs⟫ = ⟪F x, x - xs⟫ + ⟪ξ, x - xs⟫ := inner_add_left _ _ _
  have e2 : ⟪F x - F xs, x - xs⟫ = ⟪F x, x - xs⟫ - ⟪F xs, x - xs⟫ := inner_sub_left _ _ _
  have e3 : ⟪ξ, xs - x⟫ = -⟪ξ, x - xs⟫ := by rw [← inner_neg_right, neg_sub]
  linarith

lemma potential_lower (c : Ctx F P X L0 L1 a xs R G) {x ξ : E} {S : ℝ} (hS : 0 ≤ S)
    (hx : x ∈ X) (hξ : Normal X x ξ) : -(R ^ 2 / 2) ≤ potential a x (F x + ξ) S := by
  have hpair := residual_pair c hx hξ
  have hsplit : ⟪F x + ξ, x - a⟫ = ⟪F x + ξ, x - xs⟫ + ⟪F x + ξ, xs - a⟫ := by
    rw [← inner_add_right]
    congr 1
    abel
  have hcs := real_inner_le_norm (F x + ξ) (a - xs)
  have hneg : ⟪F x + ξ, xs - a⟫ = -⟪F x + ξ, a - xs⟫ := by
    rw [← inner_neg_right, neg_sub]
  have hp := norm_nonneg (F x + ξ)
  have h1 : ‖F x + ξ‖ * ‖a - xs‖ ≤ ‖F x + ξ‖ * R := mul_le_mul_of_nonneg_left c.dist0 hp
  unfold potential
  rw [hsplit, hneg]
  nlinarith [sq_nonneg (S * ‖F x + ξ‖ - R), mul_nonneg hS hpair]

lemma residual_bound (c : Ctx F P X L0 L1 a xs R G) {s : E × E × ℝ} (hI : Inv F X a xs R s) :
    s.2.2 * ‖F s.1 + s.2.1‖ ≤ 2 * R := by
  have hpot := hI.pot
  have hpair := residual_pair c hI.mem hI.normal
  have hS := hI.S_nonneg
  unfold potential at hpot
  have hsplit : ⟪F s.1 + s.2.1, s.1 - a⟫ =
      ⟪F s.1 + s.2.1, s.1 - xs⟫ - ⟪F s.1 + s.2.1, a - xs⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hcs := real_inner_le_norm (F s.1 + s.2.1) (a - xs)
  have hp := norm_nonneg (F s.1 + s.2.1)
  have h1 : ‖F s.1 + s.2.1‖ * ‖a - xs‖ ≤ ‖F s.1 + s.2.1‖ * R :=
    mul_le_mul_of_nonneg_left c.dist0 hp
  rw [hsplit] at hpot
  have h2 : s.2.2 ^ 2 / 2 * ‖F s.1 + s.2.1‖ ^ 2 ≤ s.2.2 * (‖F s.1 + s.2.1‖ * R) := by
    nlinarith [mul_nonneg hS hpair]
  by_contra hcon
  push Not at hcon
  have h3 : 0 < s.2.2 * ‖F s.1 + s.2.1‖ - 2 * R := by linarith
  have h4 : 0 ≤ s.2.2 * ‖F s.1 + s.2.1‖ := by positivity
  nlinarith [mul_pos h3 (by linarith [c.R_pos] : 0 < s.2.2 * ‖F s.1 + s.2.1‖)]

lemma inv_step (c : Ctx F P X L0 L1 a xs R G) {s : E × E × ℝ} (hI : Inv F X a xs R s) :
    Inv F X a xs R (iter F P L0 L1 a s) := by
  obtain ⟨x, ξ, S⟩ := s
  obtain ⟨hS, hstart, hx, hξ, hpot, hdist⟩ := hI
  obtain ⟨hγ, hstep, hD, -⟩ :=
    stepSize_spec c.hyp.L0_pos c.hyp.L1_nonneg a x (F x) ξ hS hstart
  set γ := stepSize L0 L1 a x (F x) ξ S with hγdef
  set m := mval a x (F x) ξ S with hm
  have hΓ : 0 < S + γ := by linarith
  have hpstep := potential_step (P := P) c.hyp c.proj c.convex c.anchor hx hξ hS hγ hD hstep
  have hdstep := distance_step (P := P) (ξ := ξ) c.hyp c.proj c.convex c.anchor hx hS hγ hD hstep
    c.sol c.vi
  set z := halfPoint a x (F x) ξ S γ with hzdef
  set w := targetPoint a x (F z) S γ with hwdef
  set W := ‖(F z + γ⁻¹ • (w - P w)) - (S / (S + γ)) • (F x + ξ)‖ with hWdef
  have hPw : P w ∈ X := c.proj.mem w
  have hnorm : Normal X (P w) (γ⁻¹ • (w - P w)) := c.proj.normal w hγ
  have hlow := potential_lower c (S := S + γ) hΓ.le hPw hnorm
  have hpotplus : potential a (P w) (F (P w) + γ⁻¹ • (w - P w)) (S + γ) ≤ 0 := by
    have : 0 ≤ 3 / 8 * (S + γ) ^ 2 * W ^ 2 := by positivity
    linarith
  have hW : (S + γ) * W ≤ 7 / 6 * R := by
    have hsq : ((S + γ) * W) ^ 2 ≤ (7 / 6 * R) ^ 2 := by
      have : 3 / 8 * (S + γ) ^ 2 * W ^ 2 ≤ R ^ 2 / 2 := by linarith
      nlinarith [sq_nonneg R]
    exact (sq_le_sq₀ (by positivity) (by linarith [c.R_pos])).mp hsq
  have hγW : γ * W ≤ γ / (S + γ) * (7 / 6 * R) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hΓ]
    nlinarith [hW]
  refine ⟨hΓ.le, fun h0 => absurd h0 hΓ.ne', hPw, hnorm, hpotplus, ?_⟩
  show ‖P w - xs‖ ≤ 3 * R
  have hb0 : 0 < γ / (S + γ) := by positivity
  have hb1 : γ / (S + γ) ≤ 1 := (div_le_one hΓ).mpr (by linarith)
  have hbt : S / (S + γ) = 1 - γ / (S + γ) := by field_simp; ring
  have hR := c.R_pos
  have hRsq : ‖a - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) c.dist0 2
  have hDsq : ‖x - xs‖ ^ 2 ≤ (3 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  set D := ‖P w - xs‖ with hDdef
  have hD0 : 0 ≤ D := norm_nonneg _
  set β := γ / (S + γ) with hβ
  rw [hbt] at hdstep
  have hmain : D ^ 2 ≤ β * R ^ 2 + (1 - β) * (3 * R) ^ 2 + β * (7 / 6 * R) * D := by
    have h1 : γ * W * D ≤ β * (7 / 6 * R) * D := mul_le_mul_of_nonneg_right hγW hD0
    have h2 : (1 - β) * ‖x - xs‖ ^ 2 ≤ (1 - β) * (3 * R) ^ 2 :=
      mul_le_mul_of_nonneg_left hDsq (by linarith)
    have h3 : β * ‖a - xs‖ ^ 2 ≤ β * R ^ 2 := mul_le_mul_of_nonneg_left hRsq hb0.le
    have : γ * W * D = γ * W * ‖P w - xs‖ := rfl
    nlinarith
  by_contra hcon
  push Not at hcon
  have hk1 : 0 < D - 3 * R := by linarith
  have hk2 : 0 < D + 3 * R - 7 / 6 * β * R := by nlinarith
  have hk3 := mul_pos hk1 hk2
  nlinarith [mul_pos hb0 (mul_pos hR hR)]

lemma run_inv (c : Ctx F P X L0 L1 a xs R G) (k : ℕ) : Inv F X a xs R (run F P L0 L1 a k) := by
  induction k with
  | zero =>
    refine ⟨le_refl _, fun _ => rfl, c.anchor, ?_, by simp [run, potential], ?_⟩
    · intro w _
      simp [run]
    · simp only [run]
      linarith [c.dist0, c.R_pos]
  | succ k ih => exact inv_step c ih

end run

end OracleTemplate.ConstrainedMonotone
