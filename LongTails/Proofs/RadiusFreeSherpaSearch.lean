import LongTails.Proofs.RadiusFreeSherpaStep

set_option linter.unusedSectionVars false

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def seg (c : Core E) (t : ℝ) : E := c.v + t • (c.x - c.v)

noncomputable def slope (g : E → E) (c : Core E) (t : ℝ) : ℝ := ⟪g (seg c t), c.x - c.v⟫

omit [CompleteSpace E] in
lemma probePoint_eq (c : Core E) (tm tp : ℝ) : probePoint c tm tp = seg c ((tm + tp) / 2) := rfl

omit [CompleteSpace E] in
lemma seg_zero (c : Core E) : seg c 0 = c.v := by simp [seg]

omit [CompleteSpace E] in
lemma seg_one (c : Core E) : seg c 1 = c.x := by simp [seg]

omit [CompleteSpace E] in
lemma seg_sub (c : Core E) (s t : ℝ) : seg c t - seg c s = (t - s) • (c.x - c.v) := by
  simp only [seg, sub_smul]; abel

lemma gradient_monotone {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (a b : E) : 0 ≤ ⟪g a - g b, a - b⟫ := by
  have h1 := OracleTemplate.Gradient.convex_support H.convex H.grad a b
  have h2 := OracleTemplate.Gradient.convex_support H.convex H.grad b a
  rw [inner_sub_left]
  have : ⟪g a, b - a⟫ = -⟪g a, a - b⟫ := by rw [← inner_neg_right]; congr 1; abel
  linarith

lemma slope_mono {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (c : Core E) {s t : ℝ} (hst : s ≤ t) : slope g c s ≤ slope g c t := by
  have h := gradient_monotone H (seg c t) (seg c s)
  rw [seg_sub, real_inner_smul_right, inner_sub_left] at h
  unfold slope
  rcases eq_or_lt_of_le hst with h' | h'
  · rw [h']
  · have : 0 < t - s := by linarith
    nlinarith

lemma seg_f_le {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (c : Core E) {t : ℝ} (ht : t ≤ 1) (hs : 0 ≤ slope g c t) : f (seg c t) ≤ f c.x := by
  have h := OracleTemplate.Gradient.convex_support H.convex H.grad (seg c t) c.x
  have he : c.x - seg c t = (1 - t) • (c.x - c.v) := by
    simp only [seg, sub_smul, one_smul]; abel
  rw [he, real_inner_smul_right] at h
  unfold slope at hs
  nlinarith

omit [CompleteSpace E] in
lemma seg_inner_v (g : E → E) (c : Core E) (t : ℝ) :
    ⟪g (seg c t), seg c t - c.v⟫ = t * slope g c t := by
  have he : seg c t - c.v = t • (c.x - c.v) := by simp [seg]
  rw [he, real_inner_smul_right]; rfl

structure PInv (f : E → ℝ) (g : E → E) (L0 L1 : ℝ) (u : E) (c : Core E) (tm tp : ℝ) : Prop where
  tm_nonneg : 0 ≤ tm
  lt : tm < tp
  tp_le : tp ≤ 1
  neg : slope g c tm < 0
  fail : ¬ (tp * slope g c tp ≤ ‖g (seg c tp)‖ ^ 2 / (16 * localCurvature L0 L1 ‖g (seg c tp)‖))

omit [CompleteSpace E] in
lemma PInv.slope_pos {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} {c : Core E} {tm tp : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (h : PInv f g L0 L1 u c tm tp) : 0 < slope g c tp := by
  by_contra hcon
  push Not at hcon
  apply h.fail
  have hL := localCurvature_pos hL0 hL1.le (norm_nonneg (g (seg c tp)))
  have : tp * slope g c tp ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [h.tm_nonneg, h.lt]) hcon
  have : 0 ≤ ‖g (seg c tp)‖ ^ 2 / (16 * localCurvature L0 L1 ‖g (seg c tp)‖) := by positivity
  linarith

omit [CompleteSpace E] in
lemma PInv.d_pos {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} {c : Core E} {tm tp : ℝ}
    (h : PInv f g L0 L1 u c tm tp) : 0 < ‖c.x - c.v‖ := by
  by_contra hcon
  push Not at hcon
  have hz : c.x - c.v = 0 := norm_le_zero_iff.mp hcon
  have := h.neg
  unfold slope at this
  rw [hz, inner_zero_right] at this
  exact lt_irrefl _ this

lemma probe_width {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) {c : Core E} {tm tp : ℝ} (h : PInv f g L0 L1 u c tm tp)
    (hG : threshold L0 L1 < ‖g (seg c tp)‖) :
    1 / (800 * (L1 * ‖c.x - c.v‖) ^ 2) < tp - tm := by
  have hL0 := H.L0_pos
  set d := c.x - c.v with hd
  have hdpos : 0 < ‖d‖ := h.d_pos
  set δ := tp - tm with hδ
  have hδpos : 0 < δ := by linarith [h.lt]
  have hδ1 : δ ≤ 1 := by linarith [h.tm_nonneg, h.tp_le]
  set G := ‖g (seg c tp)‖ with hGdef
  set L := localCurvature L0 L1 G with hLdef
  have hGpos : 0 < G := lt_of_le_of_lt (by unfold threshold; positivity) hG
  have hL : 0 < L := localCurvature_pos hL0 hL1.le hGpos.le
  have hLG : L < 5 * L1 * G := by
    unfold threshold at hG
    unfold localCurvature at hLdef
    rw [hLdef]
    have : L0 < 4 * L1 * G := by
      rw [div_lt_iff₀ (by positivity)] at hG; linarith
    linarith
  have hslope_pos := h.slope_pos hL0 hL1
  have hfail : G ^ 2 / (16 * L) < slope g c tp := by
    have hf := h.fail
    push Not at hf
    have : tp * slope g c tp ≤ slope g c tp := by
      have := h.tp_le
      nlinarith
    linarith
  by_cases hcase : L1 * (δ * ‖d‖) ≤ 1 / 2
  · have hpair := gradient_pair_bound H hL1 (seg c tm) (seg c tp)
      (by rw [seg_sub, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith)]
          rw [show -(tm - tp) = δ by ring]; exact hcase)
    rw [seg_sub, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith),
      show -(tm - tp) = δ by ring] at hpair
    rw [← hGdef, ← hLdef] at hpair
    have hdiff : slope g c tp - slope g c tm = ⟪g (seg c tp) - g (seg c tm), d⟫ := by
      unfold slope; rw [inner_sub_left]
    have hcs := real_inner_le_norm (g (seg c tp) - g (seg c tm)) d
    have hneg := h.neg
    have hbound : slope g c tp ≤ 2 * L * δ * ‖d‖ ^ 2 := by
      have h1 : slope g c tp ≤ slope g c tp - slope g c tm := by linarith
      have h2 : ⟪g (seg c tp) - g (seg c tm), d⟫ ≤ ‖g (seg c tp) - g (seg c tm)‖ * ‖d‖ := hcs
      have h3 : ‖g (seg c tm) - g (seg c tp)‖ * ‖d‖ ≤ 2 * L * (δ * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hpair (norm_nonneg _)
      calc slope g c tp ≤ slope g c tp - slope g c tm := h1
        _ = ⟪g (seg c tp) - g (seg c tm), d⟫ := hdiff
        _ ≤ ‖g (seg c tp) - g (seg c tm)‖ * ‖d‖ := h2
        _ = ‖g (seg c tm) - g (seg c tp)‖ * ‖d‖ := by rw [norm_sub_rev]
        _ ≤ 2 * L * (δ * ‖d‖) * ‖d‖ := h3
        _ = 2 * L * δ * ‖d‖ ^ 2 := by ring
    have hkey : G ^ 2 / (16 * L) < 2 * L * δ * ‖d‖ ^ 2 := lt_of_lt_of_le hfail hbound
    rw [div_lt_iff₀ (by positivity)] at hkey
    have hL2 : L ^ 2 < 25 * L1 ^ 2 * G ^ 2 := by nlinarith [hL, hLG]
    have hδd : 0 < δ * ‖d‖ ^ 2 := by positivity
    have hmain : G ^ 2 < 800 * L1 ^ 2 * G ^ 2 * δ * ‖d‖ ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_right hL2 hδd]
    rw [div_lt_iff₀ (by positivity)]
    by_contra hcon
    push Not at hcon
    have hG2 : 0 < G ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hcon hG2.le
    nlinarith
  · push Not at hcase
    have hδlow : 1 / (2 * L1 * ‖d‖) < δ := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    have h400 : 1 ≤ 400 * (L1 * ‖d‖) := by
      by_contra hcon
      push Not at hcon
      have : L1 * (δ * ‖d‖) ≤ L1 * ‖d‖ := by
        have := mul_le_mul_of_nonneg_left hδ1 (norm_nonneg d)
        nlinarith [hL1]
      linarith
    calc 1 / (800 * (L1 * ‖d‖) ^ 2) ≤ 1 / (2 * L1 * ‖d‖) := by
          apply div_le_div_of_nonneg_left zero_le_one (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left h400 (mul_pos hL1 hdpos).le]
      _ < δ := hδlow

lemma PInv.width_bound {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) {c : Core E} {tm tp : ℝ} (h : PInv f g L0 L1 u c tm tp)
    (hG : threshold L0 L1 < ‖g (seg c tp)‖) {j : ℕ} (hj : tp - tm = (1 / 2) ^ j)
    {D : ℝ} (hd : ‖c.x - c.v‖ ≤ D) :
    (2 : ℝ) ^ j < 800 * (L1 * D) ^ 2 := by
  have hw := probe_width H hL1 h hG
  rw [hj] at hw
  have hdpos : 0 < ‖c.x - c.v‖ := h.d_pos
  have h2 : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
  rw [h2, div_lt_div_iff₀ (by positivity) (by positivity)] at hw
  have hmono : (L1 * ‖c.x - c.v‖) ^ 2 ≤ (L1 * D) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hd hL1.le
  nlinarith

end OracleTemplate.RadiusFreeSherpa
