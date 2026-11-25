import LongTails.Proofs.RhoSmoothPhaseOne

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothPhaseTwo

open LongTails.Setups.RhoSmoothRadiusConvex LongTails.Algorithms.RhoSmoothThreePhase
open LongTails.Proofs.RhoSmoothLocal LongTails.Proofs.RhoSmoothParams
open LongTails.Proofs.RhoSmoothPhaseOne

lemma lyap_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y w A B u y' : E) (fy fy' fs Γ γ α c : ℝ) (hΓ : 0 < Γ) (hα0 : 0 ≤ α)
    (hα : α ^ 2 = γ * Γ) (hc : γ ≤ 2 * c)
    (hy' : (1 + α) • y' = y + α • w - γ • A)
    (hconv : fy' + ⟪B, u - y'⟫ ≤ fs)
    (hcoc : fy' + ⟪B, y - y'⟫ + c * ‖A - B‖ ^ 2 ≤ fy) :
    (1 + α) * (fy' - fs + Γ / (1 + α) / 2 * ‖(w - (α / Γ) • B) - u‖ ^ 2) ≤
      fy - fs + Γ / 2 * ‖w - u‖ ^ 2 := by
  have hpos : 0 < 1 + α := by linarith
  have e1 : ‖(w - (α / Γ) • B) - u‖ ^ 2 =
      ‖w - u‖ ^ 2 - 2 * (α / Γ) * ⟪w - u, B⟫ + (α / Γ) ^ 2 * ‖B‖ ^ 2 := by
    rw [show (w - (α / Γ) • B) - u = (w - u) - (α / Γ) • B by abel, norm_sub_sq_real,
      real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have e2 : α • (w - u) = (y' - y) + α • (y' - u) + γ • A := by
    linear_combination (norm := module) -hy'
  have e3 : α * ⟪w - u, B⟫ = ⟪y' - y, B⟫ + α * ⟪y' - u, B⟫ + γ * ⟪A, B⟫ := by
    have := congrArg (fun z => ⟪z, B⟫) e2
    simp only [inner_add_left, real_inner_smul_left] at this
    linarith
  have hc1 : ⟪B, u - y'⟫ = -⟪y' - u, B⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  have hc2 : ⟪B, y - y'⟫ = -⟪y' - y, B⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  have hAB : ‖A - B‖ ^ 2 = ‖A‖ ^ 2 - 2 * ⟪A, B⟫ + ‖B‖ ^ 2 := norm_sub_sq_real A B
  rw [hc1] at hconv
  rw [hc2, hAB] at hcoc
  have h3 : α * (fy' - fs) ≤ α * ⟪y' - u, B⟫ := mul_le_mul_of_nonneg_left (by linarith) hα0
  have hcoef : (1 + α) * (Γ / (1 + α) / 2) = Γ / 2 := by field_simp
  have hsq : Γ / 2 * (α / Γ) ^ 2 = γ / 2 := by
    rw [div_pow, hα]; field_simp
  have hlin : Γ / 2 * (2 * (α / Γ) * ⟪w - u, B⟫) = α * ⟪w - u, B⟫ := by
    field_simp
  rw [e1]
  have expand : (1 + α) * (fy' - fs + Γ / (1 + α) / 2 *
      (‖w - u‖ ^ 2 - 2 * (α / Γ) * ⟪w - u, B⟫ + (α / Γ) ^ 2 * ‖B‖ ^ 2)) =
      (1 + α) * (fy' - fs) + Γ / 2 * ‖w - u‖ ^ 2 - α * ⟪w - u, B⟫ + γ / 2 * ‖B‖ ^ 2 := by
    have : (1 + α) * (fy' - fs + Γ / (1 + α) / 2 *
        (‖w - u‖ ^ 2 - 2 * (α / Γ) * ⟪w - u, B⟫ + (α / Γ) ^ 2 * ‖B‖ ^ 2)) =
        (1 + α) * (fy' - fs) + ((1 + α) * (Γ / (1 + α) / 2)) *
          (‖w - u‖ ^ 2 - 2 * (α / Γ) * ⟪w - u, B⟫ + (α / Γ) ^ 2 * ‖B‖ ^ 2) := by ring
    rw [this, hcoef]
    have : Γ / 2 * (‖w - u‖ ^ 2 - 2 * (α / Γ) * ⟪w - u, B⟫ + (α / Γ) ^ 2 * ‖B‖ ^ 2) =
        Γ / 2 * ‖w - u‖ ^ 2 - Γ / 2 * (2 * (α / Γ) * ⟪w - u, B⟫) +
          Γ / 2 * (α / Γ) ^ 2 * ‖B‖ ^ 2 := by ring
    rw [this, hlin, hsq]
    ring
  rw [expand, e3]
  have hkey : -c * ‖A‖ ^ 2 + (2 * c - γ) * ⟪A, B⟫ + (γ / 2 - c) * ‖B‖ ^ 2 ≤ 0 := by
    have h1 : 0 ≤ ‖A - B‖ ^ 2 := sq_nonneg _
    rw [hAB] at h1
    have h2 : 0 ≤ (c - γ / 2) * (‖A‖ ^ 2 - 2 * ⟪A, B⟫ + ‖B‖ ^ 2) :=
      mul_nonneg (by linarith) h1
    have hγ : 0 ≤ γ := by
      have := sq_nonneg α
      rw [hα] at this
      exact nonneg_of_mul_nonneg_left this hΓ
    nlinarith [sq_nonneg ‖A‖]
  nlinarith

noncomputable def lyap (p : Params) (f : p.E → ℝ) (g : p.E → p.E) (u : p.E) (s : State p.E) : ℝ :=
  match s with
  | .accel y w Γ b => f y - f u + nextWeight p Γ b / 2 * ‖nextDual p w (g y) Γ b - u‖ ^ 2
  | _ => 0

noncomputable def weightOf (p : Params) (s : State p.E) : ℝ :=
  match s with
  | .accel _ _ Γ b => nextWeight p Γ b
  | _ => 0

lemma trans_accel (p : Params) (g : p.E → p.E) (y w : p.E) (Γ : ℝ) (b : Bool) :
    trans p g (.accel y w Γ b) =
      .accel (accelPoint p y (nextDual p w (g y) Γ b) (g y) (nextWeight p Γ b))
        (nextDual p w (g y) Γ b) (nextWeight p Γ b) true := rfl

lemma accel_iter_form (p : Params) (g : p.E → p.E) (x : p.E) :
    ∀ m, ∃ y w Γ b, (trans p g)^[m] (.accel x x (initialWeight p) false) = .accel y w Γ b := by
  intro m
  induction m with
  | zero => exact ⟨x, x, initialWeight p, false, rfl⟩
  | succ m ih =>
      obtain ⟨y, w, Γ, b, h⟩ := ih
      refine ⟨accelPoint p y (nextDual p w (g y) Γ b) (g y) (nextWeight p Γ b),
        nextDual p w (g y) Γ b, nextWeight p Γ b, true, ?_⟩
      rw [Function.iterate_succ_apply', h, trans_accel]

structure Inv (p : Params) (f : p.E → ℝ) (g : p.E → p.E) (u : p.E) (y w : p.E) (Γ : ℝ)
    (b : Bool) : Prop where
  lyap_le : lyap p f g u (.accel y w Γ b) ≤ nextWeight p Γ b * p.R ^ 2
  weight_pos : 0 < nextWeight p Γ b
  weight_le : nextWeight p Γ b ≤ initialWeight p
  dist_le : ‖y - u‖ ≤ 3 * p.R

section
variable (p : Params) (hp : spec.valid p) {f : p.E → ℝ} {g : p.E → p.E}
  (H : Hyp f g p.L0 p.L1 p.ρ) {u : p.E} (hu : IsMinOn f Set.univ u)
include hp H hu

lemma small_gradient (y : p.E) (hy : f y - f u ≤ threshold p ^ 2 / (8192 * p.L0)) :
    ‖g y‖ ≤ threshold p / 8 := by
  have hG := threshold_pos p hp
  have hL := L0_pos p hp
  by_contra hcon
  rw [not_le] at hcon
  have hlow := gap_lower H hu y
  rw [← curvature_eq] at hlow
  have hmono := sq_curv_mono p hp (s := threshold p / 8) (t := ‖g y‖) (by positivity) hcon.le
  have hc : curvature p (2 * (threshold p / 8)) ≤ 2 * p.L0 :=
    curvature_le_of_le p hp (by positivity) (by linarith)
  have hK := curvature_pos p hp (show (0 : ℝ) ≤ 2 * ‖g y‖ by positivity)
  have h1 : 3 * (threshold p / 8) ^ 2 / (16 * (2 * p.L0)) ≤
      3 * ‖g y‖ ^ 2 / (16 * curvature p (2 * ‖g y‖)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : threshold p ^ 2 / (8192 * p.L0) < 3 * (threshold p / 8) ^ 2 / (16 * (2 * p.L0)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (pow_pos hG 2) hL]
  linarith

lemma gradient_square (y : p.E) (hy : ‖g y‖ ≤ threshold p / 4) :
    ‖g y‖ ^ 2 ≤ 32 * p.L0 / 3 * (f y - f u) := by
  have hG := threshold_pos p hp
  have hL := L0_pos p hp
  have h0 := gradient_zero H hu
  have hco := cocoercive H y u (b := threshold p / 4) (by positivity) hy
    (by rw [h0, norm_zero]; positivity)
  rw [h0, sub_zero, inner_zero_left, add_zero, ← curvature_eq] at hco
  have hc : curvature p (2 * (threshold p / 4)) ≤ 2 * p.L0 :=
    curvature_le_of_le p hp (by positivity) (by linarith)
  have hcp := curvature_pos p hp (show (0 : ℝ) ≤ 2 * (threshold p / 4) by positivity)
  have h1 : 3 / (32 * p.L0) * ‖g y‖ ^ 2 ≤ 3 / (16 * curvature p (2 * (threshold p / 4))) *
      ‖g y‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  have h2 : 3 / (32 * p.L0) * ‖g y‖ ^ 2 ≤ f y - f u := by linarith
  have e : 32 * p.L0 / 3 * (3 / (32 * p.L0) * ‖g y‖ ^ 2) = ‖g y‖ ^ 2 := by field_simp
  nlinarith

set_option maxHeartbeats 1000000 in
lemma inv_step (y w : p.E) (Γ : ℝ) (b : Bool) (hI : Inv p f g u y w Γ b) (y' : p.E)
    (hy' : y' = accelPoint p y (nextDual p w (g y) Γ b) (g y) (nextWeight p Γ b)) :
    Inv p f g u y' (nextDual p w (g y) Γ b) (nextWeight p Γ b) true ∧
      (1 + momentum p (nextWeight p Γ b)) *
        lyap p f g u (.accel y' (nextDual p w (g y) Γ b) (nextWeight p Γ b) true) ≤
        lyap p f g u (.accel y w Γ b) := by
  have hG := threshold_pos p hp
  have hL := L0_pos p hp
  have hR := R_pos p hp
  set G := threshold p
  set wt := nextDual p w (g y) Γ b
  set Γt := nextWeight p Γ b
  set α := momentum p Γt
  set γ := stepSize p
  have hΓ := hI.weight_pos
  have hγ : 0 < γ := stepSize_pos p hp
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hα2 : α ^ 2 = γ * Γt := Real.sq_sqrt (by positivity)
  have hα1 : α ≤ 1 := momentum_le_one p hp hI.weight_le
  have hmin : f u ≤ f y := hu (Set.mem_univ y)
  have hlyap : lyap p f g u (.accel y w Γ b) = f y - f u + Γt / 2 * ‖wt - u‖ ^ 2 := rfl
  have hV := hI.lyap_le
  rw [hlyap] at hV
  have hΓR : Γt * p.R ^ 2 ≤ G ^ 2 / (8192 * p.L0) :=
    (mul_le_mul_of_nonneg_right hI.weight_le (sq_nonneg _)).trans (initialWeight_le_gap p hp)
  have hgap : f y - f u ≤ Γt * p.R ^ 2 := by
    have : 0 ≤ Γt / 2 * ‖wt - u‖ ^ 2 := by positivity
    linarith
  have hgy : ‖g y‖ ≤ G / 8 := small_gradient p hp H hu y (hgap.trans hΓR)
  have hw : ‖wt - u‖ ^ 2 ≤ 2 * p.R ^ 2 := by
    have h1 : Γt / 2 * ‖wt - u‖ ^ 2 ≤ Γt * p.R ^ 2 := by linarith
    have : Γt * ‖wt - u‖ ^ 2 ≤ Γt * (2 * p.R ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hΓ
  have hwn : ‖wt - u‖ ≤ 3 / 2 * p.R := by
    have : ‖wt - u‖ ^ 2 ≤ (3 / 2 * p.R) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  have hgsq := gradient_square p hp H hu y (by linarith)
  have hγg : γ * ‖g y‖ ≤ 6 / 5 * α * p.R := by
    have h1 : (γ * ‖g y‖) ^ 2 ≤ (6 / 5 * α * p.R) ^ 2 := by
      have hγdef : γ = 1 / (8 * p.L0) := rfl
      have e : (6 / 5 * α * p.R) ^ 2 = 36 / 25 * (γ * Γt) * p.R ^ 2 := by rw [← hα2]; ring
      rw [e, mul_pow]
      have h2 : γ ^ 2 * ‖g y‖ ^ 2 ≤ γ ^ 2 * (32 * p.L0 / 3 * (Γt * p.R ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact hgsq.trans (mul_le_mul_of_nonneg_left hgap (by positivity))
      have h3 : γ ^ 2 * (32 * p.L0 / 3 * (Γt * p.R ^ 2)) ≤ 36 / 25 * (γ * Γt) * p.R ^ 2 := by
        rw [hγdef]
        have : 0 ≤ Γt * p.R ^ 2 := by positivity
        field_simp
        nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hαR : α * p.R ≤ G / (256 * p.L0) := by
    have h1 : (α * p.R) ^ 2 ≤ (G / (256 * p.L0)) ^ 2 := by
      rw [mul_pow, hα2]
      have hγdef : γ = 1 / (8 * p.L0) := rfl
      have : γ * Γt * p.R ^ 2 = γ * (Γt * p.R ^ 2) := by ring
      rw [this]
      have h2 : γ * (Γt * p.R ^ 2) ≤ γ * (G ^ 2 / (8192 * p.L0)) :=
        mul_le_mul_of_nonneg_left hΓR hγ.le
      have e : γ * (G ^ 2 / (8192 * p.L0)) = (G / (256 * p.L0)) ^ 2 := by
        rw [hγdef]; field_simp; ring
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hy'def : (1 + α) • y' = y + α • wt - γ • g y := by
    rw [hy']
    unfold accelPoint
    rw [smul_smul, mul_one_div_cancel (by linarith), one_smul]
  have hdisp_eq : (1 + α) • (y' - y) = α • (wt - y) - γ • g y := by
    linear_combination (norm := module) hy'def
  have hscale : ‖y' - y‖ ≤ ‖α • (wt - y) - γ • g y‖ := by
    rw [← hdisp_eq, norm_smul, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (y' - y)]
  have hdisp : ‖y' - y‖ ≤ G / (32 * p.L0) := by
    refine hscale.trans ?_
    have h1 : ‖α • (wt - y) - γ • g y‖ ≤ α * ‖wt - y‖ + γ * ‖g y‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hα0, Real.norm_of_nonneg hγ.le]
    have h2 : ‖wt - y‖ ≤ ‖wt - u‖ + ‖y - u‖ := by
      have := norm_sub_le (wt - u) (y - u)
      simpa using this
    have h3 : α * ‖wt - y‖ ≤ α * (3 / 2 * p.R + 3 * p.R) :=
      mul_le_mul_of_nonneg_left (h2.trans (by linarith [hI.dist_le])) hα0
    have e : G / (32 * p.L0) = 8 * (G / (256 * p.L0)) := by field_simp; ring
    rw [e]
    nlinarith
  have hgy' : ‖g y'‖ ≤ G / 4 := by
    have hv : 2 * curv p.L0 p.L1 p.ρ (2 * (G / 8)) * ‖y' - y‖ ≤ G / 8 := by
      rw [← curvature_eq]
      have hc : curvature p (2 * (G / 8)) ≤ 2 * p.L0 :=
        curvature_le_of_le p hp (by positivity) (by linarith)
      have hcp := curvature_pos p hp (show (0 : ℝ) ≤ 2 * (G / 8) by positivity)
      have : 2 * curvature p (2 * (G / 8)) * ‖y' - y‖ ≤ 2 * (2 * p.L0) * (G / (32 * p.L0)) := by
        apply mul_le_mul (by linarith) hdisp (norm_nonneg _) (by positivity)
      have e : 2 * (2 * p.L0) * (G / (32 * p.L0)) = G / 8 := by field_simp; ring
      linarith
    have h := segment_norm H y (y' - y) (a := G / 8) (by positivity) hgy hv
      (t := 1) ⟨zero_le_one, le_rfl⟩
    rw [one_smul, add_sub_cancel] at h
    linarith
  have hcoc := cocoercive H y y' (b := G / 4) (by positivity) (by linarith) hgy'
  rw [← curvature_eq] at hcoc
  have hcG : curvature p (2 * (G / 4)) ≤ 2 * p.L0 :=
    curvature_le_of_le p hp (by positivity) (by linarith)
  have hcp := curvature_pos p hp (show (0 : ℝ) ≤ 2 * (G / 4) by positivity)
  have hcγ : γ ≤ 2 * (3 / (16 * curvature p (2 * (G / 4)))) := by
    have hγdef : γ = 1 / (8 * p.L0) := rfl
    rw [hγdef, div_le_iff₀ (by positivity)]
    rw [show 2 * (3 / (16 * curvature p (2 * (G / 4)))) * (8 * p.L0) =
      48 * p.L0 / (16 * curvature p (2 * (G / 4))) by ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hconv := convex_lower H y' u
  have hstep := lyap_step y wt (g y) (g y') u y' (f y) (f y') (f u) Γt γ α
    (3 / (16 * curvature p (2 * (G / 4)))) hΓ hα0 hα2 hcγ hy'def (by linarith)
    (by linarith)
  have hlyap' : lyap p f g u (.accel y' wt Γt true) =
      f y' - f u + Γt / (1 + α) / 2 * ‖(wt - (α / Γt) • g y') - u‖ ^ 2 := rfl
  have hstep' : (1 + α) * lyap p f g u (.accel y' wt Γt true) ≤ lyap p f g u (.accel y w Γ b) := by
    rw [hlyap', hlyap]; exact hstep
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hstep'⟩
  · have hnw : nextWeight p Γt true = Γt / (1 + α) := rfl
    rw [hnw]
    have : lyap p f g u (.accel y' wt Γt true) ≤ lyap p f g u (.accel y w Γ b) / (1 + α) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    calc lyap p f g u (.accel y' wt Γt true) ≤ lyap p f g u (.accel y w Γ b) / (1 + α) := this
      _ ≤ Γt * p.R ^ 2 / (1 + α) := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          rw [hlyap]; exact hV
      _ = Γt / (1 + α) * p.R ^ 2 := by ring
  · show 0 < Γt / (1 + α)
    positivity
  · show Γt / (1 + α) ≤ initialWeight p
    have : Γt / (1 + α) ≤ Γt := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    exact this.trans hI.weight_le
  · have heq : (1 + α) • (y' - u) = (y - u) + α • (wt - u) - γ • g y := by
      linear_combination (norm := module) hy'def
    have hnorm : (1 + α) * ‖y' - u‖ = ‖(y - u) + α • (wt - u) - γ • g y‖ := by
      rw [← heq, norm_smul, Real.norm_of_nonneg (by linarith)]
    have h1 : ‖(y - u) + α • (wt - u) - γ • g y‖ ≤ ‖y - u‖ + α * ‖wt - u‖ + γ * ‖g y‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul (γ) (g y), Real.norm_of_nonneg hγ.le]
      have := norm_add_le (y - u) (α • (wt - u))
      rw [norm_smul, Real.norm_of_nonneg hα0] at this
      linarith
    have h2 : ‖y - u‖ + α * ‖wt - u‖ + γ * ‖g y‖ ≤ (1 + α) * (3 * p.R) := by
      have h5 := hI.dist_le
      have h3 : α * ‖wt - u‖ ≤ 3 / 2 * (α * p.R) := by
        have := mul_le_mul_of_nonneg_left hwn hα0
        linarith
      have h6 : 0 ≤ α * p.R := mul_nonneg hα0 hR.le
      have e : (1 + α) * (3 * p.R) = 3 * p.R + 3 * (α * p.R) := by ring
      have e2 : 6 / 5 * α * p.R = 6 / 5 * (α * p.R) := by ring
      rw [e2] at hγg
      linarith
    have h4 : (1 + α) * ‖y' - u‖ ≤ (1 + α) * (3 * p.R) := by rw [hnorm]; linarith
    exact le_of_mul_le_mul_left h4 (by linarith)

end

end LongTails.Proofs.RhoSmoothPhaseTwo
