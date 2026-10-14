import LongTails.Proofs.AnchoredExtragradientStep
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def run (F : E → E) (L0 L1 : ℝ) (a : E) : ℕ → E × ℝ
  | 0 => (a, 0)
  | k + 1 =>
      (full F a (run F L0 L1 a k).1 (run F L0 L1 a k).2
          (stepSize L0 L1 a (run F L0 L1 a k).1 (F (run F L0 L1 a k).1) (run F L0 L1 a k).2),
        (run F L0 L1 a k).2 +
          stepSize L0 L1 a (run F L0 L1 a k).1 (F (run F L0 L1 a k).1) (run F L0 L1 a k).2)

omit [InnerProductSpace ℝ E] in
lemma stepSize_spec {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (a x g : E) {S : ℝ}
    (hS : 0 ≤ S) (hx : S = 0 → x = a) :
    0 < stepSize L0 L1 a x g S ∧
    stepSize L0 L1 a x g S * (L0 + L1 * (‖g‖ + ‖x - a‖ / S)) ≤ 1 / 4 ∧
    ‖x - a‖ ≤ (S + stepSize L0 L1 a x g S) * (‖g‖ + ‖x - a‖ / S - ‖g‖) ∧
    (S ≠ 0 → stepSize L0 L1 a x g S ≤ S / 3) := by
  have hm : 0 ≤ ‖g‖ + ‖x - a‖ / S := by positivity
  have hden : 0 < 4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S)) := by positivity
  have hnat : 1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S))) *
      (L0 + L1 * (‖g‖ + ‖x - a‖ / S)) = 1 / 4 := by
    field_simp
  by_cases h0 : S = 0
  · have hxa : x = a := hx h0
    have hγ : stepSize L0 L1 a x g S = 1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S))) := by
      rw [stepSize, ite_eq_left h0]
    rw [hγ]
    refine ⟨by positivity, hnat.le, ?_, fun h => absurd h0 h⟩
    subst hxa
    simp
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm h0)
    have hγ : stepSize L0 L1 a x g S =
        min (S / 3) (1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S)))) := by
      rw [stepSize, ite_eq_right h0]
    have hpos : 0 < stepSize L0 L1 a x g S := by
      rw [hγ]
      exact lt_min (by positivity) (by positivity)
    refine ⟨hpos, ?_, ?_, fun _ => by rw [hγ]; exact min_le_left _ _⟩
    · have hle : stepSize L0 L1 a x g S ≤ 1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S))) := by
        rw [hγ]
        exact min_le_right _ _
      calc stepSize L0 L1 a x g S * (L0 + L1 * (‖g‖ + ‖x - a‖ / S))
          ≤ 1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S))) * (L0 + L1 * (‖g‖ + ‖x - a‖ / S)) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 1 / 4 := hnat
    · have hD := norm_nonneg (x - a)
      have : ‖x - a‖ = S * (‖x - a‖ / S) := by field_simp
      have h2 : 0 ≤ stepSize L0 L1 a x g S * (‖x - a‖ / S) := by positivity
      nlinarith

lemma quad_aux {b t : ℝ} (hbt : b + t = 1) (hb0 : 0 ≤ b) (hb4 : b ≤ 1 / 4) :
    0 ≤ t ^ 2 - 2 * (t / 3 + b) ^ 2 ∧ 0 ≤ b * t - 2 * b ^ 2 / 9 := by
  have ht : t = 1 - b := by linarith
  subst ht
  constructor
  · nlinarith [sq_nonneg b]
  · nlinarith [mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ 1 - 11 / 9 * b)]

lemma quad_main {b t : ℝ} (D v : ℝ) (hbt : b + t = 1) (hb0 : 0 ≤ b) (hb4 : b ≤ 1 / 4) :
    (b * D / 3 + (t / 3 + b) * v) ^ 2 ≤ b * t * D ^ 2 + t ^ 2 * v ^ 2 := by
  obtain ⟨h1, h2⟩ := quad_aux hbt hb0 hb4
  nlinarith [sq_nonneg (b * D / 3 - (t / 3 + b) * v), mul_nonneg h2 (sq_nonneg D),
    mul_nonneg h1 (sq_nonneg v)]

structure Inv (F : E → E) (a xs : E) (R : ℝ) (s : E × ℝ) : Prop where
  S_nonneg : 0 ≤ s.2
  start : s.2 = 0 → s.1 = a
  pot : potential F a s.1 s.2 ≤ 0
  dist : ‖s.1 - xs‖ ^ 2 ≤ 5 / 4 * R ^ 2

lemma first_step_bound {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) :
    1 / (4 * (L0 + L1 * ‖F a‖)) * ‖F a‖ ≤ R / 2 := by
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have hρ := norm_nonneg (F a)
  have hd := norm_nonneg (a - xs)
  have hden : 0 < 4 * (L0 + L1 * ‖F a‖) := by positivity
  have key : ‖F a‖ ≤ 2 * R * (L0 + L1 * ‖F a‖) := by
    by_cases hc : L1 * ‖a - xs‖ ≤ 1 / 2
    · have hloc := h.local a xs (by linarith)
      rw [hroot, sub_zero] at hloc
      have h1 : (L0 + L1 * ‖F a‖) * ‖a - xs‖ ≤ (L0 + L1 * ‖F a‖) * R :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      nlinarith [mul_nonneg hρ (sub_nonneg.mpr hc)]
    · push Not at hc
      have h1 : L1 * ‖a - xs‖ ≤ L1 * R := mul_le_mul_of_nonneg_left hR hL1
      have h2 : 0 ≤ R := hd.trans hR
      nlinarith [mul_nonneg hρ (by linarith : (0 : ℝ) ≤ L1 * R - 1 / 2), mul_pos hL0 hL0,
        mul_nonneg h2 hL0.le]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
  nlinarith

lemma inv_step {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) {x : E} {S : ℝ} (hI : Inv F a xs R (x, S)) :
    Inv F a xs R (full F a x S (stepSize L0 L1 a x (F x) S),
      S + stepSize L0 L1 a x (F x) S) := by
  obtain ⟨hS, hstart, hpot, hdist⟩ := hI
  dsimp only at hS hstart hpot hdist
  obtain ⟨hγ, hstep, hD, hcap⟩ := stepSize_spec h.L0_pos h.L1_nonneg a x (F x) hS hstart
  set γ := stepSize L0 L1 a x (F x) S with hγdef
  set m := ‖F x‖ + ‖x - a‖ / S with hm
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hΓ : 0 < S + γ := by linarith
  refine ⟨hΓ.le, fun h0 => absurd h0 hΓ.ne', (potential_step h hS hγ hD hstep).trans hpot, ?_⟩
  dsimp only
  have hds := distance_step h (a := a) (x := x) hS hγ hroot
  obtain ⟨hpm, hh1, -, hh3, -⟩ := half_bounds h hS hγ hD hstep
  have hRsq : ‖a - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  by_cases h0 : S = 0
  · have hxa : x = a := hstart h0
    subst hxa
    have hm0 : m = ‖F x‖ := by rw [hm, h0]; simp
    have hγv : γ = 1 / (4 * (L0 + L1 * ‖F x‖)) := by
      rw [hγdef, stepSize, ite_eq_left h0, h0]
      simp
    have hfirst := first_step_bound h hroot hR
    rw [← hγv] at hfirst
    have hhalf : half F x x S γ = x := by
      rw [half, h0]
      simp
    rw [hhalf, h0] at hds
    simp only [zero_add, zero_div, zero_smul, sub_zero, mul_zero, sub_self, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hds
    rw [div_self hγ.ne', one_mul] at hds
    have hsq : (γ * ‖F x‖) ^ 2 ≤ (R / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfirst 2
    rw [h0]
    nlinarith
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm h0)
    have hcap' := hcap h0
    set b := γ / (S + γ) with hb
    set t := S / (S + γ) with ht
    have hbt : b + t = 1 := by rw [hb, ht]; field_simp; ring
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have hb4 : b ≤ 1 / 4 := by
      rw [hb, div_le_iff₀ hΓ]
      linarith
    set W := ‖F (half F a x S γ) - t • F x‖ with hW
    set D := ‖x - a‖ with hDdef
    set v := γ * ‖F x‖ with hv
    have hv0 : 0 ≤ v := by rw [hv]; positivity
    have hD0 : 0 ≤ D := norm_nonneg _
    have hW0 : 0 ≤ W := norm_nonneg _
    have hWle : W ≤ ‖F (half F a x S γ) - F x‖ + b * ‖F x‖ := by
      have he : F (half F a x S γ) - t • F x = (F (half F a x S γ) - F x) + b • F x := by
        have : t = 1 - b := by linarith
        rw [this]
        module
      rw [hW, he]
      calc ‖(F (half F a x S γ) - F x) + b • F x‖
          ≤ ‖F (half F a x S γ) - F x‖ + ‖b • F x‖ := norm_add_le _ _
        _ = ‖F (half F a x S γ) - F x‖ + b * ‖F x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0]
    have hX : γ * W ≤ b * D / 3 + (t / 3 + b) * v := by
      have := mul_le_mul_of_nonneg_left hWle hγ.le
      rw [hv]
      nlinarith
    have hsq : (γ * W) ^ 2 ≤ (b * D / 3 + (t / 3 + b) * v) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hX 2
    have hquad := quad_main D v hbt hb0 hb4
    have hv2 : γ ^ 2 * t ^ 2 * ‖F x‖ ^ 2 = t ^ 2 * v ^ 2 := by rw [hv]; ring
    have hW2 : γ ^ 2 * W ^ 2 = (γ * W) ^ 2 := by ring
    rw [hv2, hW2] at hds
    have ht0 : 0 ≤ t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hRsq hb0, mul_le_mul_of_nonneg_left hdist ht0]

lemma run_inv {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) (k : ℕ) : Inv F a xs R (run F L0 L1 a k) := by
  induction k with
  | zero =>
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
    refine ⟨le_refl _, fun _ => rfl, by simp [run, potential], ?_⟩
    have := pow_le_pow_left₀ (norm_nonneg (a - xs)) hR 2
    simp only [run]
    nlinarith [sq_nonneg R]
  | succ k ih => exact inv_step h hroot hR ih

lemma run_pos {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) (k : ℕ) : 0 < (run F L0 L1 a (k + 1)).2 := by
  have hI := run_inv h hroot hR k
  have hγ := (stepSize_spec h.L0_pos h.L1_nonneg a (run F L0 L1 a k).1
    (F (run F L0 L1 a k).1) hI.S_nonneg hI.start).1
  have := hI.S_nonneg
  simp only [run]
  linarith

lemma residual_bound {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) {x : E} {S : ℝ} (hS : 0 < S)
    (hI : Inv F a xs R (x, S)) : S * ‖F x‖ ≤ 2 * R := by
  have hpot := hI.pot
  dsimp only [potential] at hpot
  have hmono := h.mono x xs
  rw [hroot, sub_zero] at hmono
  have hsplit : ⟪F x, x - a⟫ = ⟪F x, x - xs⟫ - ⟪F x, a - xs⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hcs := real_inner_le_norm (F x) (a - xs)
  have hp := norm_nonneg (F x)
  have h1 : ‖F x‖ * ‖a - xs‖ ≤ ‖F x‖ * R := mul_le_mul_of_nonneg_left hR hp
  rw [hsplit] at hpot
  have h2 : S ^ 2 / 2 * ‖F x‖ ^ 2 ≤ S * (‖F x‖ * R) := by nlinarith
  by_contra hcon
  push Not at hcon
  have h3 : 0 < S * ‖F x‖ - 2 * R := by linarith
  have h4 : 0 ≤ S * ‖F x‖ := by positivity
  nlinarith [mul_pos h3 (by nlinarith [(norm_nonneg (a - xs)).trans hR] : 0 < S * ‖F x‖)]

noncomputable def growth (L0 L1 R S : ℝ) : ℝ :=
  4 * L0 * S + (20 * L1 * R + 3) * Real.log S

lemma growth_step {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) {x : E} {S : ℝ} (hS : 0 < S)
    (hI : Inv F a xs R (x, S)) :
    growth L0 L1 R S + 3 / 4 ≤ growth L0 L1 R (S + stepSize L0 L1 a x (F x) S) := by
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hres := residual_bound h hroot hR hS hI
  have hdist := hI.dist
  dsimp only at hdist
  have hxs : ‖x - xs‖ ≤ 9 / 8 * R := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (x - xs)]
  have hD : ‖x - a‖ ≤ 17 / 8 * R := by
    have he : x - a = (x - xs) - (a - xs) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  set m := ‖F x‖ + ‖x - a‖ / S with hm
  have hSm : S * m ≤ 5 * R := by
    have : S * m = S * ‖F x‖ + ‖x - a‖ := by rw [hm]; field_simp
    linarith
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hnat : 1 / (4 * (L0 + L1 * m)) * (4 * (L0 + L1 * m)) = 1 := by
    have : 0 < L0 + L1 * m := by positivity
    field_simp
  have hγ : stepSize L0 L1 a x (F x) S = min (S / 3) (1 / (4 * (L0 + L1 * m))) := by
    rw [stepSize, ite_eq_right hS.ne']
  set γ := stepSize L0 L1 a x (F x) S with hγdef
  have hγpos : 0 < γ := by
    rw [hγ]
    exact lt_min (by positivity) (by positivity)
  have hγle : γ ≤ S / 3 := by rw [hγ]; exact min_le_left _ _
  have hc0 : 0 < γ / S := by positivity
  have hlog : γ / (S + γ) ≤ Real.log (S + γ) - Real.log S := by
    rw [← Real.log_div (by linarith : S + γ ≠ 0) hS.ne']
    have h1 := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < (S + γ) / S)
    have h2 : 1 - ((S + γ) / S)⁻¹ = γ / (S + γ) := by
      rw [inv_div]
      field_simp
      ring
    linarith
  have hfrac : 3 / 4 * (γ / S) ≤ γ / (S + γ) := by
    rw [show 3 / 4 * (γ / S) = 3 / 4 * γ / S by ring, div_le_div_iff₀ hS (by linarith)]
    nlinarith [mul_nonneg hγpos.le (by linarith : (0 : ℝ) ≤ S / 4 - 3 / 4 * γ)]
  have hcoef : 0 ≤ 20 * L1 * R + 3 := by positivity
  have hkey : 1 ≤ 4 * L0 * γ + 20 * L1 * R * (γ / S) + 3 * (γ / S) := by
    have hmS : m * γ ≤ 5 * R * (γ / S) := by
      have h1 : m ≤ 5 * R / S := by
        rw [le_div_iff₀ hS]
        linarith
      calc m * γ ≤ 5 * R / S * γ := mul_le_mul_of_nonneg_right h1 hγpos.le
        _ = 5 * R * (γ / S) := by ring
    have hLm := mul_le_mul_of_nonneg_left hmS (by positivity : (0 : ℝ) ≤ 4 * L1)
    rcases min_choice (S / 3) (1 / (4 * (L0 + L1 * m))) with hmin | hmin
    · have hγS : γ / S = 1 / 3 := by
        rw [hγ, hmin]
        field_simp
      have : 0 ≤ 4 * L0 * γ := by positivity
      have : 0 ≤ 20 * L1 * R * (γ / S) := by positivity
      linarith
    · have hγv : γ * (4 * (L0 + L1 * m)) = 1 := by
        rw [hγ, hmin]
        exact hnat
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hfrac.trans hlog) hcoef
  unfold growth
  nlinarith

lemma growth_run {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) (n : ℕ) :
    growth L0 L1 R (run F L0 L1 a 1).2 + 3 / 4 * n ≤
      growth L0 L1 R (run F L0 L1 a (n + 1)).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : growth L0 L1 R (run F L0 L1 a (n + 1)).2 + 3 / 4 ≤
        growth L0 L1 R (run F L0 L1 a (n + 1 + 1)).2 :=
      growth_step h hroot hR (run_pos h hroot hR n) (run_inv h hroot hR (n + 1))
    push_cast
    linarith

lemma run_first {F : E → E} (L0 L1 : ℝ) (a : E) :
    (run F L0 L1 a 1).2 = 1 / (4 * (L0 + L1 * ‖F a‖)) := by
  simp [run, stepSize]

theorem run_accuracy {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a xs : E} {R G ε : ℝ}
    (hroot : F xs = 0) (hR : ‖a - xs‖ ≤ R) (hG : ‖F a‖ ≤ G) (hε : 0 < ε) (n : ℕ)
    (hn : 4 / 3 * (8 * L0 * R / ε +
      (20 * L1 * R + 3) * Real.log (1 + 8 * (L0 + L1 * G) * R / ε)) ≤ n) :
    ‖F (run F L0 L1 a (n + 1)).1‖ ≤ ε := by
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hρ := norm_nonneg (F a)
  have hSpos := run_pos h hroot hR n
  have hI := run_inv h hroot hR (n + 1)
  have hres : (run F L0 L1 a (n + 1)).2 * ‖F (run F L0 L1 a (n + 1)).1‖ ≤ 2 * R :=
    residual_bound h hroot hR hSpos hI
  set S := (run F L0 L1 a (n + 1)).2 with hSdef
  by_cases hbig : 2 * R / ε ≤ S
  · rw [div_le_iff₀ hε] at hbig
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hSpos]
  · push Not at hbig
    exfalso
    have hRpos : 0 < R := by
      by_contra hcon
      have : R = 0 := le_antisymm (not_lt.mp hcon) hR0
      rw [this] at hbig
      simp at hbig
      linarith
    have hgr := growth_run h hroot hR n
    rw [run_first] at hgr
    set S1 := 1 / (4 * (L0 + L1 * ‖F a‖)) with hS1
    have hS1pos : 0 < S1 := by rw [hS1]; positivity
    have hlogS : Real.log S < Real.log (2 * R / ε) := Real.log_lt_log hSpos hbig
    have hcoef : 0 < 20 * L1 * R + 3 := by positivity
    have harg : 2 * R / ε / S1 ≤ 1 + 8 * (L0 + L1 * G) * R / ε := by
      have : 2 * R / ε / S1 = 8 * (L0 + L1 * ‖F a‖) * R / ε := by
        rw [hS1]
        field_simp
        ring
      rw [this]
      have h1 : 8 * (L0 + L1 * ‖F a‖) * R / ε ≤ 8 * (L0 + L1 * G) * R / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        have := mul_le_mul_of_nonneg_left hG hL1
        nlinarith
      linarith
    have hlog2 : Real.log (2 * R / ε) - Real.log S1 ≤
        Real.log (1 + 8 * (L0 + L1 * G) * R / ε) := by
      rw [← Real.log_div (by positivity) hS1pos.ne']
      exact Real.log_le_log (by positivity) harg
    have hSlt : 4 * L0 * S < 4 * L0 * (2 * R / ε) := by
      apply mul_lt_mul_of_pos_left hbig
      positivity
    have h8 : 4 * L0 * (2 * R / ε) = 8 * L0 * R / ε := by ring
    have hS1n : 0 ≤ 4 * L0 * S1 := by positivity
    unfold growth at hgr
    have hm1 := mul_lt_mul_of_pos_left hlogS hcoef
    have hm2 := mul_le_mul_of_nonneg_left hlog2 hcoef.le
    nlinarith

end OracleTemplate.GeneralizedMonotone
