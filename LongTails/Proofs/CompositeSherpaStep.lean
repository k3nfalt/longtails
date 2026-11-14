import LongTails.Proofs.CompositeSherpaBasic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeSherpa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ψ : E → ℝ} {g : E → E} {prox : ℝ → E → E → E} {L0 L1 M : ℝ} {xs : E}

lemma tol_pos {L0 L1 M G : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hG : 0 < G) :
    0 < tol L0 L1 M G := by
  unfold tol; have := curv_pos hL0 hL1 hM hG.le; positivity

set_option maxHeartbeats 1000000 in
lemma accepted_potential (H : Hyp f ψ g prox L0 L1 M xs) {A : ℝ} (hA : 0 ≤ A) {x v y : E}
    (hG : gthr L0 L1 M < ‖g y‖)
    (hfy : f y + ψ y ≤ f x + ψ x + tol L0 L1 M ‖g y‖)
    (hE : ψ y - ψ (prox (cweight L0 L1 M A ‖g y‖) v (g y)) +
      ⟪g y, y - prox (cweight L0 L1 M A ‖g y‖) v (g y)⟫ ≤
      tol L0 L1 M ‖g y‖ + (‖g y‖ + M) * ‖prox (cweight L0 L1 M A ‖g y‖) v (g y) - v‖) :
    (A + cweight L0 L1 M A ‖g y‖) *
        (f (prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y)) +
          ψ (prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y)) - (f xs + ψ xs)) +
        cweight L0 L1 M A ‖g y‖ ^ 2 * ‖g y‖ ^ 2 / 2 +
        ‖prox (cweight L0 L1 M A ‖g y‖) v (g y) - xs‖ ^ 2 / 2 ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖v - xs‖ ^ 2 / 2 := by
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hGf := gthr_facts hL0 hL1 hM hG
  obtain ⟨hGpos, h45, h65, hLG, hc, hL0'⟩ := hGf
  set G := ‖g y‖ with hGdef
  have hcpos : 0 < curv L0 L1 M G := curv_pos hL0 hL1.le hM hGpos.le
  set L := curv L0 L1 M G with hLdef
  set τ := tol L0 L1 M G with hτdef
  have hτ : τ = G ^ 2 / (200 * L) := rfl
  set a := cweight L0 L1 M A G with hadef
  obtain ⟨hapos, haeq⟩ := cweight_eq hL0 hL1 hM hA hGpos (by linarith)
  rw [← hadef] at hapos haeq
  set Φ := phiFun (L0 + L1 * M) L1 (G - M) with hΦdef
  have hLp : 0 < L0 + L1 * M := by have := mul_nonneg hL1.le hM; linarith
  have hΦ0 : 0 ≤ Φ := phiFun_nonneg hLp hL1 (by linarith)
  set lam := 1 / (4 * L) with hlamdef
  have hlam : 0 < lam := by positivity
  set xn := prox lam y (g y) with hxn
  set vn := prox a v (g y) with hvn
  set D := ‖vn - v‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  clear_value D vn xn lam Φ a τ L G
  have hthree := H.prox_three hapos v (g y) xs
  rw [← hvn] at hthree
  have hsh := H.shifted_norm_ge y
  rw [← hGdef] at hsh
  have hhpos : 0 < ‖shiftedGrad g xs y‖ := by linarith
  have hphi := H.phi_inequality y hhpos
  have hmono : Φ ≤ phiFun (L0 + L1 * M) L1 ‖shiftedGrad g xs y‖ := by
    rw [hΦdef]; exact phiFun_mono hLp hL1 (by linarith) hsh
  obtain ⟨hlow, -, -⟩ := H.move_bounds y
  have hdesc := H.step_descent y
  rw [← hGdef, ← hLdef, ← hlamdef, ← hxn] at hlow hdesc
  set δ := ‖xn - y‖ with hδ
  have hδ2 : (lam * (G - M)) ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hlam.le (by linarith)) hlow 2
  have hdes2 : 3 * L * (lam * (G - M)) ^ 2 ≤ 3 * L * δ ^ 2 :=
    mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have hval : 3 * L * (lam * (G - M)) ^ 2 = 3 * (G - M) ^ 2 / (16 * L) := by
    rw [hlamdef]; field_simp; ring
  have h45sq : (4 / 5 * G) ^ 2 ≤ (G - M) ^ 2 := pow_le_pow_left₀ (by positivity) h45 2
  have hdes3 : 3 / 25 * (G ^ 2 / L) ≤ 3 * L * δ ^ 2 := by
    have : 3 / 25 * (G ^ 2 / L) ≤ 3 * (G - M) ^ 2 / (16 * L) := by
      rw [show 3 / 25 * (G ^ 2 / L) = 3 / 25 * G ^ 2 / L by ring,
        div_le_div_iff₀ hcpos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h45sq hcpos.le]
    linarith
  have hyoung : a * (G + M) * D - D ^ 2 / 2 ≤ a ^ 2 * (G + M) ^ 2 / 2 := by
    linarith [sq_nonneg (a * (G + M) - D)]
  have hGM2 : (G + M) ^ 2 ≤ 36 / 25 * G ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ G + M) h65 2
    linarith
  have hyoung2 : a * (G + M) * D - D ^ 2 / 2 ≤ 18 / 25 * (a ^ 2 * G ^ 2) := by
    have := mul_le_mul_of_nonneg_left hGM2 (sq_nonneg a)
    linarith
  have haeq' : a ^ 2 = (A + a) / (12 * L) + a * Φ / (2 * G ^ 2) := by
    rw [hLdef]; exact haeq
  have hroot : a ^ 2 * G ^ 2 = (A + a) * (G ^ 2 / L) / 12 + a * Φ / 2 := by
    rw [haeq']; field_simp
  have hgap_xn : f xn + ψ xn - (f xs + ψ xs) ≤ f y + ψ y - (f xs + ψ xs) - 3 / 25 * (G ^ 2 / L) := by
    linarith
  have hAa : 0 ≤ A + a := by linarith
  have h1 : (A + a) * (f xn + ψ xn - (f xs + ψ xs)) ≤
      (A + a) * (f y + ψ y - (f xs + ψ xs)) - (A + a) * (3 / 25 * (G ^ 2 / L)) := by
    nlinarith [mul_le_mul_of_nonneg_left hgap_xn hAa]
  have h2 : A * (f y + ψ y - (f xs + ψ xs)) ≤ A * (f x + ψ x - (f xs + ψ xs)) + A * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hfy hA]
  have hinner : ⟪g y, vn - xs⟫ = -⟪g y, xs - y⟫ - ⟪g y, y - vn⟫ := by
    rw [← inner_neg_right, ← inner_sub_right]
    congr 1; abel
  rw [hinner] at hthree
  have h3 : ‖vn - xs‖ ^ 2 / 2 ≤ ‖v - xs‖ ^ 2 / 2 - D ^ 2 / 2 +
      a * (f xs + ψ xs - (f y + ψ y)) + a * τ + a * (G + M) * D - a * Φ := by
    have hE' := mul_le_mul_of_nonneg_left hE hapos.le
    have hphi' : a * ⟪g y, xs - y⟫ ≤ a * (f xs - f y - Φ) := by
      apply mul_le_mul_of_nonneg_left _ hapos.le
      linarith
    rw [← hD] at hthree
    linarith [hthree, hE', hphi']
  have hτL : (A + a) * τ = (A + a) * (G ^ 2 / L) / 200 := by rw [hτ]; ring
  have hGL : 0 ≤ (A + a) * (G ^ 2 / L) := by positivity
  have hΦa : 0 ≤ a * Φ := mul_nonneg hapos.le hΦ0
  linarith [h1, h2, h3, hyoung2, hroot, hτL, hGL, hΦa]

structure Inv (f ψ : E → ℝ) (xs : E) (R : ℝ) (c : Core E) (S : ℝ) : Prop where
  A_nonneg : 0 ≤ c.A
  S_nonneg : 0 ≤ S
  potential : c.A * (f c.x + ψ c.x - (f xs + ψ xs)) + S / 2 + ‖c.v - xs‖ ^ 2 / 2 ≤ R ^ 2 / 2
  x_dist : ‖c.x - xs‖ ≤ R

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma Inv.v_dist {R : ℝ} {c : Core E} {S : ℝ} (hR : 0 ≤ R)
    (hmin : IsMinOn (fun x => f x + ψ x) univ xs) (h : Inv f ψ xs R c S) : ‖c.v - xs‖ ≤ R := by
  have hgap : 0 ≤ f c.x + ψ c.x - (f xs + ψ xs) := by
    have := hmin (mem_univ c.x); simp only [mem_ofPred_eq] at this; linarith
  have hp := h.potential
  have hA := mul_nonneg h.A_nonneg hgap
  have hS := h.S_nonneg
  have hsq : ‖c.v - xs‖ ^ 2 ≤ R ^ 2 := by linarith
  by_contra hcon
  push Not at hcon
  have : R ^ 2 < ‖c.v - xs‖ ^ 2 := by nlinarith [norm_nonneg (c.v - xs)]
  linarith

omit [CompleteSpace E] in
lemma Inv.segment_dist {R : ℝ} {c : Core E} {S : ℝ} (hR : 0 ≤ R)
    (hmin : IsMinOn (fun x => f x + ψ x) univ xs) (h : Inv f ψ xs R c S) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ‖seg c t - xs‖ ≤ R := by
  have hv := h.v_dist hR hmin
  have hx := h.x_dist
  have he : seg c t - xs = (1 - t) • (c.v - xs) + t • (c.x - xs) := by
    simp only [seg, sub_smul, one_smul, smul_sub]; abel
  rw [he]
  calc ‖(1 - t) • (c.v - xs) + t • (c.x - xs)‖ ≤ ‖(1 - t) • (c.v - xs)‖ + ‖t • (c.x - xs)‖ :=
        norm_add_le _ _
    _ = (1 - t) * ‖c.v - xs‖ + t * ‖c.x - xs‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    _ ≤ (1 - t) * R + t * R := by gcongr
    _ = R := by ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma Inv.d_le {R : ℝ} {c : Core E} {S : ℝ} (hR : 0 ≤ R)
    (hmin : IsMinOn (fun x => f x + ψ x) univ xs) (h : Inv f ψ xs R c S) :
    ‖c.x - c.v‖ ≤ 2 * R := by
  have h1 := h.x_dist
  have h2 := h.v_dist hR hmin
  calc ‖c.x - c.v‖ = ‖(c.x - xs) - (c.v - xs)‖ := by congr 1; abel
    _ ≤ ‖c.x - xs‖ + ‖c.v - xs‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith

lemma accept_inv (H : Hyp f ψ g prox L0 L1 M xs) {R : ℝ} {c : Core E} {S : ℝ}
    (hI : Inv f ψ xs R c S) {y : E} (hG : gthr L0 L1 M < ‖g y‖) (hyd : ‖y - xs‖ ≤ R)
    (hfy : f y + ψ y ≤ f c.x + ψ c.x + tol L0 L1 M ‖g y‖)
    (hE : ψ y - ψ (prox (cweight L0 L1 M c.A ‖g y‖) c.v (g y)) +
      ⟪g y, y - prox (cweight L0 L1 M c.A ‖g y‖) c.v (g y)⟫ ≤
      tol L0 L1 M ‖g y‖ + (‖g y‖ + M) * ‖prox (cweight L0 L1 M c.A ‖g y‖) c.v (g y) - c.v‖) :
    Inv f ψ xs R (acceptCore L0 L1 M c (g y) (prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y))
      (prox (cweight L0 L1 M c.A ‖g y‖) c.v (g y)))
      (S + cweight L0 L1 M c.A ‖g y‖ ^ 2 * ‖g y‖ ^ 2) := by
  have hA := hI.A_nonneg
  have hpot := accepted_potential H hA (x := c.x) (v := c.v) hG hfy hE
  have hGpos : 0 < ‖g y‖ := (gthr_facts H.hL0 H.hL1 H.hM hG).1
  have hw := (cweight_eq H.hL0 H.hL1 H.hM hA hGpos
    (by linarith [(gthr_facts H.hL0 H.hL1 H.hM hG).2.1])).1
  refine ⟨add_nonneg hA hw.le, add_nonneg hI.S_nonneg (by positivity), ?_, ?_⟩
  · have := hI.potential
    simp only [acceptCore]
    linarith
  · simp only [acceptCore]
    exact (H.step_dist y).trans hyd

end OracleTemplate.CompositeSherpa
