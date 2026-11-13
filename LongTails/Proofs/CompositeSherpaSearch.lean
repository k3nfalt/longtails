import LongTails.Proofs.CompositeSherpaStep

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeSherpa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ψ : E → ℝ} {g : E → E} {prox : ℝ → E → E → E} {L0 L1 M : ℝ} {xs : E}

omit [CompleteSpace E] in
lemma seg_zero (c : Core E) : seg c 0 = c.v := by simp [seg]

omit [CompleteSpace E] in
lemma seg_one (c : Core E) : seg c 1 = c.x := by simp [seg]

omit [CompleteSpace E] in
lemma seg_sub (c : Core E) (s t : ℝ) : seg c t - seg c s = (t - s) • (c.x - c.v) := by
  simp only [seg, sub_smul]; abel

omit [CompleteSpace E] in
lemma seg_combo (c : Core E) {s t u : ℝ} (hst : s < t) (htu : t < u) :
    seg c t = ((u - t) / (u - s)) • seg c s + ((t - s) / (u - s)) • seg c u := by
  have hus : u - s ≠ 0 := by linarith
  simp only [seg, smul_add, smul_smul]
  have e1 : (u - t) / (u - s) + (t - s) / (u - s) = 1 := by field_simp; ring
  have e2 : (u - t) / (u - s) * s + (t - s) / (u - s) * u = t := by field_simp; ring
  calc c.v + t • (c.x - c.v)
      = ((u - t) / (u - s) + (t - s) / (u - s)) • c.v +
          ((u - t) / (u - s) * s + (t - s) / (u - s) * u) • (c.x - c.v) := by rw [e1, e2, one_smul]
    _ = _ := by simp only [add_smul]; abel

omit [CompleteSpace E] in
lemma secant_mono_left (hψ : ConvexOn ℝ univ ψ) (c : Core E) {s t u : ℝ} (hst : s < t)
    (htu : t < u) :
    (ψ (seg c u) - ψ (seg c s)) / (u - s) ≤ (ψ (seg c u) - ψ (seg c t)) / (u - t) := by
  have hus : 0 < u - s := by linarith
  have hut : 0 < u - t := by linarith
  have hts : 0 < t - s := by linarith
  have hcomb := hψ.2 (mem_univ (seg c s)) (mem_univ (seg c u))
    (show 0 ≤ (u - t) / (u - s) by positivity) (show 0 ≤ (t - s) / (u - s) by positivity)
    (by field_simp; ring)
  rw [← seg_combo c hst htu] at hcomb
  simp only [smul_eq_mul] at hcomb
  rw [div_le_div_iff₀ hus hut]
  have e : (u - t) / (u - s) * ψ (seg c s) + (t - s) / (u - s) * ψ (seg c u) =
      ((u - t) * ψ (seg c s) + (t - s) * ψ (seg c u)) / (u - s) := by field_simp
  rw [e, le_div_iff₀ hus] at hcomb
  nlinarith

omit [CompleteSpace E] in
lemma secant_mono_right (hψ : ConvexOn ℝ univ ψ) (c : Core E) {s t u : ℝ} (hst : s < t)
    (htu : t < u) :
    (ψ (seg c t) - ψ (seg c s)) / (t - s) ≤ (ψ (seg c u) - ψ (seg c s)) / (u - s) := by
  have hus : 0 < u - s := by linarith
  have hut : 0 < u - t := by linarith
  have hts : 0 < t - s := by linarith
  have hcomb := hψ.2 (mem_univ (seg c s)) (mem_univ (seg c u))
    (show 0 ≤ (u - t) / (u - s) by positivity) (show 0 ≤ (t - s) / (u - s) by positivity)
    (by field_simp; ring)
  rw [← seg_combo c hst htu] at hcomb
  simp only [smul_eq_mul] at hcomb
  rw [div_le_div_iff₀ hts hus]
  have e : (u - t) / (u - s) * ψ (seg c s) + (t - s) / (u - s) * ψ (seg c u) =
      ((u - t) * ψ (seg c s) + (t - s) * ψ (seg c u)) / (u - s) := by field_simp
  rw [e, le_div_iff₀ hus] at hcomb
  nlinarith

lemma test_one (H : Hyp f ψ g prox L0 L1 M xs) (c : Core E) {t : ℝ} {τ : ℝ}
    (h : -τ ≤ (1 - t) * ⟪g (seg c t), c.x - c.v⟫ + ψ c.x - ψ (seg c t)) :
    f (seg c t) + ψ (seg c t) ≤ f c.x + ψ c.x + τ := by
  have hs := Gradient.convex_support H.convex H.grad (seg c t) c.x
  have he : c.x - seg c t = (1 - t) • (c.x - c.v) := by
    simp only [seg, sub_smul, one_smul]; abel
  rw [he, real_inner_smul_right] at hs
  linarith

lemma test_two (H : Hyp f ψ g prox L0 L1 M xs) (c : Core E) {tm t τ : ℝ} (htm : 0 ≤ tm)
    (hlt : tm < t) (_ht1 : t ≤ 1)
    (h : t * (⟪g (seg c t), c.x - c.v⟫ + (ψ (seg c t) - ψ (seg c tm)) / (t - tm)) ≤ τ)
    (w : E) :
    ψ (seg c t) - ψ w + ⟪g (seg c t), seg c t - w⟫ ≤ τ + (‖g (seg c t)‖ + M) * ‖w - c.v‖ := by
  set y := seg c t with hy
  have htpos : 0 < t := by linarith
  set s := (t - tm) / t with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one htpos]; linarith
  have hcomb := H.ψconvex.2 (mem_univ y) (mem_univ w) (show 0 ≤ 1 - s by linarith) hs0.le
    (by ring)
  simp only [smul_eq_mul] at hcomb
  have hpt : (1 - s) • y + s • w = y + s • (c.v - y) + s • (w - c.v) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  have hseg : y + s • (c.v - y) = seg c tm := by
    have e : y + s • (c.v - y) = c.v + (t - s * t) • (c.x - c.v) := by
      simp only [hy, seg]; module
    rw [e]
    have htne : t ≠ 0 := htpos.ne'
    have : t - s * t = tm := by rw [hs]; field_simp; ring
    rw [this]
    rfl
  rw [hpt, hseg] at hcomb
  have hlip := H.ψ_sub_le (seg c tm) (seg c tm + s • (w - c.v))
  rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hlip
  have h1 : ψ y - ψ w ≤ (ψ y - ψ (seg c tm)) / s + M * ‖w - c.v‖ := by
    have h2 : s * (ψ w - ψ y) ≥ ψ (seg c tm) - s * M * ‖w - c.v‖ - ψ y := by nlinarith
    have h3 : s * (ψ y - ψ w) ≤ ψ y - ψ (seg c tm) + s * (M * ‖w - c.v‖) := by nlinarith
    have h4 := div_le_div_of_nonneg_right h3 hs0.le
    rw [mul_div_cancel_left₀ _ hs0.ne', add_div, mul_div_cancel_left₀ _ hs0.ne'] at h4
    exact h4
  have htmne : t - tm ≠ 0 := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have hsecant : (ψ y - ψ (seg c tm)) / s = t * ((ψ y - ψ (seg c tm)) / (t - tm)) := by
    rw [hs]; field_simp
  have hinner : ⟪g y, y - w⟫ = t * ⟪g y, c.x - c.v⟫ + ⟪g y, c.v - w⟫ := by
    rw [← real_inner_smul_right, ← inner_add_right]
    congr 1
    simp only [hy, seg]; abel
  have hcs : ⟪g y, c.v - w⟫ ≤ ‖g y‖ * ‖w - c.v‖ := by
    rw [← norm_neg (w - c.v), neg_sub]; exact real_inner_le_norm _ _
  rw [hinner]
  have h' := h
  rw [mul_add] at h'
  rw [hsecant] at h1
  linarith

lemma test_zero (H : Hyp f ψ g prox L0 L1 M xs) (c : Core E) (w : E) :
    ψ c.v - ψ w + ⟪g c.v, c.v - w⟫ ≤ (‖g c.v‖ + M) * ‖w - c.v‖ := by
  have hlip := H.ψ_sub_le c.v w
  rw [norm_sub_rev] at hlip
  have hcs : ⟪g c.v, c.v - w⟫ ≤ ‖g c.v‖ * ‖w - c.v‖ := by
    rw [← norm_neg (w - c.v), neg_sub]; exact real_inner_le_norm _ _
  nlinarith

structure PInv (f ψ : E → ℝ) (g : E → E) (L0 L1 M : ℝ) (c : Core E) (tm tp : ℝ) : Prop where
  tm_nonneg : 0 ≤ tm
  lt : tm < tp
  tp_le : tp ≤ 1
  gtm : gthr L0 L1 M < ‖g (seg c tm)‖
  fail_left : (1 - tm) * ⟪g (seg c tm), c.x - c.v⟫ + ψ c.x - ψ (seg c tm) <
    -tol L0 L1 M ‖g (seg c tm)‖
  fail_right : tp = 1 ∨ (gthr L0 L1 M < ‖g (seg c tp)‖ ∧
    tol L0 L1 M ‖g (seg c tp)‖ <
      tp * (⟪g (seg c tp), c.x - c.v⟫ + (ψ (seg c tp) - ψ (seg c tm)) / (tp - tm)))

omit [CompleteSpace E] in
lemma PInv.move_left (hψ : ConvexOn ℝ univ ψ) {c : Core E} {tm tp t : ℝ}
    (h : PInv f ψ g L0 L1 M c tm tp) (hlt : tm < t) (htp : t < tp)
    (hg : gthr L0 L1 M < ‖g (seg c t)‖)
    (hfail : (1 - t) * ⟪g (seg c t), c.x - c.v⟫ + ψ c.x - ψ (seg c t) < -tol L0 L1 M ‖g (seg c t)‖) :
    PInv f ψ g L0 L1 M c t tp := by
  refine ⟨by linarith [h.tm_nonneg], htp, h.tp_le, hg, hfail, ?_⟩
  rcases h.fail_right with h1 | ⟨hg', hr⟩
  · left; exact h1
  · right
    refine ⟨hg', lt_of_lt_of_le hr ?_⟩
    have hmono := secant_mono_left hψ c hlt htp
    have htp0 : 0 ≤ tp := by linarith [h.tm_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left hmono htp0]

omit [CompleteSpace E] in
lemma PInv.move_right {c : Core E} {tm tp t : ℝ}
    (h : PInv f ψ g L0 L1 M c tm tp) (hlt : tm < t) (htp : t < tp)
    (hg : gthr L0 L1 M < ‖g (seg c t)‖)
    (hfail : tol L0 L1 M ‖g (seg c t)‖ <
      t * (⟪g (seg c t), c.x - c.v⟫ + (ψ (seg c t) - ψ (seg c tm)) / (t - tm))) :
    PInv f ψ g L0 L1 M c tm t :=
  ⟨h.tm_nonneg, hlt, by linarith [h.tp_le], h.gtm, h.fail_left, Or.inr ⟨hg, hfail⟩⟩

set_option maxHeartbeats 1000000 in
lemma probe_width (H : Hyp f ψ g prox L0 L1 M xs) {c : Core E} {tm tp : ℝ}
    (h : PInv f ψ g L0 L1 M c tm tp) :
    1 / (2304 * (1 + L1 * ‖c.x - c.v‖) ^ 2) < tp - tm := by
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  set d := c.x - c.v with hd
  set w := tp - tm with hw
  have hwpos : 0 < w := by linarith [h.lt]
  have hdn : 0 ≤ ‖d‖ := norm_nonneg _
  obtain ⟨hGs, h45s, h65s, hLGs, hcs, -⟩ := gthr_facts hL0 hL1 hM h.gtm
  set Gs := ‖g (seg c tm)‖ with hGsdef
  set Ls := curv L0 L1 M Gs with hLsdef
  have hLs : 0 < Ls := curv_pos hL0 hL1.le hM hGs.le
  have hτs : tol L0 L1 M Gs = Gs ^ 2 / (200 * Ls) := rfl
  have hden : 0 < 2304 * (1 + L1 * ‖d‖) ^ 2 := by positivity
  rcases h.fail_right with htp1 | ⟨hGp, hfr⟩
  · have hfl := h.fail_left
    have hw1 : w = 1 - tm := by rw [hw, htp1]
    have hcs' : -(Gs * ‖d‖) ≤ ⟪g (seg c tm), d⟫ := by
      have := real_inner_le_norm (g (seg c tm)) (-d)
      rw [inner_neg_right, norm_neg] at this; linarith
    have hlip : -(M * ((1 - tm) * ‖d‖)) ≤ ψ c.x - ψ (seg c tm) := by
      have := H.ψ_sub_le (seg c tm) c.x
      have he : seg c tm - c.x = -((1 - tm) • d) := by
        simp only [seg, hd, sub_smul, one_smul]; abel
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [h.tp_le, h.lt])]
        at this
      linarith
    have h1tm : 0 ≤ 1 - tm := by linarith [h.tp_le, h.lt]
    have hkey : Gs ^ 2 / (200 * Ls) < (1 - tm) * ((Gs + M) * ‖d‖) := by
      rw [← hτs]
      nlinarith [mul_le_mul_of_nonneg_left hcs' h1tm]
    rw [hw1]
    rw [div_lt_iff₀ hden]
    have hGM : (Gs + M) * ‖d‖ ≤ 6 / 5 * Gs * ‖d‖ := by nlinarith
    have hL : 200 * Ls ≤ 480 * (L1 * Gs) := by linarith
    have hpos : 0 < Gs ^ 2 / (200 * Ls) := by positivity
    have h2 : Gs / (480 * L1) ≤ Gs ^ 2 / (200 * Ls) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hL hGs.le, sq_nonneg Gs]
    have h3 : Gs / (480 * L1) < (1 - tm) * (6 / 5 * Gs * ‖d‖) := by
      linarith [mul_le_mul_of_nonneg_left hGM h1tm]
    have h4 : 1 < (1 - tm) * (576 * (L1 * ‖d‖)) := by
      have := mul_lt_mul_of_pos_left h3 (div_pos (by positivity : (0:ℝ) < 480 * L1) hGs)
      rw [show 480 * L1 / Gs * (Gs / (480 * L1)) = 1 by field_simp] at this
      rw [show 480 * L1 / Gs * ((1 - tm) * (6 / 5 * Gs * ‖d‖)) = (1 - tm) * (576 * (L1 * ‖d‖)) by
        field_simp; ring] at this
      exact this
    have hx : 576 * (L1 * ‖d‖) ≤ 2304 * (1 + L1 * ‖d‖) ^ 2 := by
      nlinarith [sq_nonneg (1 - L1 * ‖d‖), mul_nonneg hL1.le hdn]
    calc 1 < (1 - tm) * (576 * (L1 * ‖d‖)) := h4
      _ ≤ (1 - tm) * (2304 * (1 + L1 * ‖d‖) ^ 2) := mul_le_mul_of_nonneg_left hx h1tm
  · have hfl := h.fail_left
    have htp0 : 0 < tp := by linarith [h.tm_nonneg, h.lt]
    have h1tm : 0 < 1 - tm := by linarith [h.tp_le, h.lt]
    obtain ⟨hGp, -, -, -, -, -⟩ := gthr_facts hL0 hL1 hM hGp
    set Gp := ‖g (seg c tp)‖ with hGpdef
    have hτp : 0 < tol L0 L1 M Gp := tol_pos hL0 hL1.le hM hGp
    have hτs : 0 < tol L0 L1 M Gs := tol_pos hL0 hL1.le hM hGs
    set U := ⟪g (seg c tp), d⟫ + (ψ (seg c tp) - ψ (seg c tm)) / w with hU
    set Λ := ⟪g (seg c tm), d⟫ + (ψ c.x - ψ (seg c tm)) / (1 - tm) with hΛ
    have hUpos : tol L0 L1 M Gp < U := by
      have hU0 : 0 < U := by
        by_contra hc0; push Not at hc0
        have : tp * U ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htp0.le hc0
        linarith
      linarith [mul_nonneg (sub_nonneg.mpr h.tp_le) hU0.le]
    have hΛneg : Λ < -tol L0 L1 M Gs := by
      have e : (1 - tm) * Λ = (1 - tm) * ⟪g (seg c tm), d⟫ + ψ c.x - ψ (seg c tm) := by
        rw [hΛ]; field_simp; ring
      have : (1 - tm) * Λ < -tol L0 L1 M Gs := by rw [e]; exact hfl
      by_contra hc0; push Not at hc0
      have : (1 - tm) * (-tol L0 L1 M Gs) ≤ (1 - tm) * Λ :=
        mul_le_mul_of_nonneg_left hc0 h1tm.le
      have h1 : (1 - tm) * (-tol L0 L1 M Gs) ≥ -tol L0 L1 M Gs := by
        linarith [mul_nonneg h.tm_nonneg hτs.le]
      linarith
    have hsec : (ψ (seg c tp) - ψ (seg c tm)) / w ≤ (ψ c.x - ψ (seg c tm)) / (1 - tm) := by
      rcases lt_or_eq_of_le h.tp_le with hlt | heq
      · have := secant_mono_right H.ψconvex c h.lt hlt
        rw [seg_one] at this
        exact this
      · rw [hw, heq, seg_one]
    have hdiff : U - Λ ≤ ‖g (seg c tp) - g (seg c tm)‖ * ‖d‖ := by
      have hcs := real_inner_le_norm (g (seg c tp) - g (seg c tm)) d
      rw [inner_sub_left] at hcs
      linarith
    have hgap : tol L0 L1 M Gs < U - Λ := by linarith
    have hdpos : 0 < ‖d‖ := by
      rcases hdn.eq_or_lt with h0 | hpos
      · exfalso
        rw [← h0, mul_zero] at hdiff
        linarith
      · exact hpos
    have hsegd : ‖seg c tp - seg c tm‖ = w * ‖d‖ := by
      rw [seg_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hwpos]
    rw [div_lt_iff₀ hden]
    by_cases hsmall : L1 * (w * ‖d‖) ≤ 1 / 2
    · have hlip := CompositeGeneralized.ball_lipschitz hL0.le hL1.le H.cont H.smooth
        (x := seg c tm) (u := seg c tp) (v := seg c tm) (r := w * ‖d‖) hsmall
        (by rw [hsegd]) (by simp; positivity)
      rw [hsegd] at hlip
      have hLs' : L0 + L1 * Gs ≤ Ls := by
        rw [hLsdef]; unfold curv; nlinarith [mul_nonneg hL1.le hM]
      have hkey : tol L0 L1 M Gs < 2 * Ls * (w * ‖d‖) * ‖d‖ := by
        have h1 : ‖g (seg c tp) - g (seg c tm)‖ * ‖d‖ ≤ 2 * (L0 + L1 * Gs) * (w * ‖d‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right hlip hdn
        have h2 : 2 * (L0 + L1 * Gs) * (w * ‖d‖) * ‖d‖ ≤ 2 * Ls * (w * ‖d‖) * ‖d‖ := by
          calc 2 * (L0 + L1 * Gs) * (w * ‖d‖) * ‖d‖ = (L0 + L1 * Gs) * (2 * (w * ‖d‖) * ‖d‖) := by
                ring
            _ ≤ Ls * (2 * (w * ‖d‖) * ‖d‖) := mul_le_mul_of_nonneg_right hLs' (by positivity)
            _ = 2 * Ls * (w * ‖d‖) * ‖d‖ := by ring
        linarith
      have hτ : tol L0 L1 M Gs = Gs ^ 2 / (200 * Ls) := rfl
      rw [hτ, div_lt_iff₀ (by positivity)] at hkey
      have hkey' : Gs ^ 2 < 400 * Ls ^ 2 * w * ‖d‖ ^ 2 := by
        calc Gs ^ 2 < 2 * Ls * (w * ‖d‖) * ‖d‖ * (200 * Ls) := hkey
          _ = 400 * Ls ^ 2 * w * ‖d‖ ^ 2 := by ring
      have hLs2 : Ls ^ 2 ≤ (12 / 5 * (L1 * Gs)) ^ 2 := pow_le_pow_left₀ hLs.le hcs 2
      have hw2 : Gs ^ 2 < 400 * (12 / 5 * (L1 * Gs)) ^ 2 * w * ‖d‖ ^ 2 := by
        calc Gs ^ 2 < 400 * Ls ^ 2 * w * ‖d‖ ^ 2 := hkey'
          _ ≤ 400 * (12 / 5 * (L1 * Gs)) ^ 2 * w * ‖d‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hLs2 (by norm_num)) hwpos.le) (sq_nonneg _)
      have hG2 : 0 < Gs ^ 2 := by positivity
      have h5 : 1 < 2304 * (L1 * ‖d‖) ^ 2 * w := by
        have e : 400 * (12 / 5 * (L1 * Gs)) ^ 2 * w * ‖d‖ ^ 2 =
            Gs ^ 2 * (2304 * (L1 * ‖d‖) ^ 2 * w) := by ring
        rw [e] at hw2
        exact (lt_mul_iff_one_lt_right hG2).mp hw2
      have hx : (L1 * ‖d‖) ^ 2 ≤ (1 + L1 * ‖d‖) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith [mul_nonneg hL1.le hdn]) 2
      calc 1 < 2304 * (L1 * ‖d‖) ^ 2 * w := h5
        _ ≤ w * (2304 * (1 + L1 * ‖d‖) ^ 2) := by
          linarith [mul_le_mul_of_nonneg_right hx hwpos.le]
    · push Not at hsmall
      have hx2 : 2 * (L1 * ‖d‖) ≤ (1 + L1 * ‖d‖) ^ 2 := by nlinarith [sq_nonneg (1 - L1 * ‖d‖)]
      linarith [mul_le_mul_of_nonneg_left hx2 hwpos.le, mul_nonneg hL1.le hdn]

end OracleTemplate.CompositeSherpa
