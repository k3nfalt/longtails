import LongTails.Proofs.AbcChainProfiles
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace LongTails.Proofs.NcPlProfiles

open LongTails.Proofs.AbcChainProfiles

noncomputable def gate (u : ℝ) : ℝ := psi (u / 2)

noncomputable def dgate (u : ℝ) : ℝ := dpsi (u / 2) / 2

noncomputable def push (u : ℝ) : ℝ := phi (u - 1) / 3

noncomputable def dpush (u : ℝ) : ℝ := dphi (u - 1) / 3

lemma gate_hasDerivAt (u : ℝ) : HasDerivAt gate (dgate u) u := by
  have h : HasDerivAt (psi ∘ fun x : ℝ => x / 2) (dpsi (u / 2) * (1 / 2)) u :=
    HasDerivAt.comp u (psi_hasDerivAt (u / 2)) ((hasDerivAt_id' u).div_const 2)
  have e : dpsi (u / 2) * (1 / 2) = dgate u := by unfold dgate; ring
  rw [e] at h
  exact h

lemma push_hasDerivAt (u : ℝ) : HasDerivAt push (dpush u) u := by
  have h : HasDerivAt (phi ∘ fun x : ℝ => x - 1) (dphi (u - 1) * 1) u :=
    HasDerivAt.comp u (phi_hasDerivAt (u - 1)) ((hasDerivAt_id' u).sub_const 1)
  have h2 := h.div_const 3
  have e : dphi (u - 1) * 1 / 3 = dpush u := by unfold dpush; ring
  rw [e] at h2
  exact h2

lemma gate_nonneg (u : ℝ) : 0 ≤ gate u := psi_nonneg _

lemma gate_le_one (u : ℝ) : gate u ≤ 1 := psi_le_one _

lemma gate_of_le {u : ℝ} (h : u ≤ 1) : gate u = 0 := psi_of_le (by linarith)

lemma dgate_of_le {u : ℝ} (h : u ≤ 1) : dgate u = 0 := by
  rw [dgate, dpsi_of_le (by linarith), zero_div]

lemma gate_of_ge {u : ℝ} (h : 2 ≤ u) : gate u = 1 := psi_of_ge (by linarith)

lemma dgate_of_ge {u : ℝ} (h : 2 ≤ u) : dgate u = 0 := by
  rw [dgate, dpsi_of_ge (by linarith), zero_div]

lemma dgate_nonneg (u : ℝ) : 0 ≤ dgate u := div_nonneg (dpsi_nonneg _) (by norm_num)

lemma dgate_le (u : ℝ) : dgate u ≤ 2 := by
  have := dpsi_le (u / 2)
  unfold dgate
  linarith

lemma psi_lt_one {t : ℝ} (h : t < 1) : psi t < 1 := by
  simp only [psi, rr, pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (1 - t)]

lemma lt_two_of_gate_lt_one {u : ℝ} (h : gate u < 1) : u < 2 := by
  by_contra hc
  rw [gate_of_ge (not_lt.mp hc)] at h
  exact lt_irrefl _ h

lemma gate_lt_one {u : ℝ} (h : u < 2) : gate u < 1 := psi_lt_one (by linarith)

lemma dgate_eq_zero_of_gate_eq_one {u : ℝ} (h : gate u = 1) : dgate u = 0 := by
  apply dgate_of_ge
  by_contra hc
  exact (gate_lt_one (not_le.mp hc)).ne h

lemma gate_lipschitz (u v : ℝ) : |gate u - gate v| ≤ 2 * |u - v| := by
  have h := psi_lipschitz (u / 2) (v / 2)
  have e : u / 2 - v / 2 = (u - v) / 2 := by ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  unfold gate
  linarith

lemma dgate_lipschitz (u v : ℝ) : |dgate u - dgate v| ≤ 16 * |u - v| := by
  have h := dpsi_lipschitz (u / 2) (v / 2)
  have e : u / 2 - v / 2 = (u - v) / 2 := by ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have e2 : dgate u - dgate v = (dpsi (u / 2) - dpsi (v / 2)) / 2 := by
    unfold dgate; ring
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

lemma push_nonneg (u : ℝ) : 0 ≤ push u := div_nonneg (phi_nonneg _) (by norm_num)

lemma push_le_one (u : ℝ) : push u ≤ 1 := by
  have := phi_le (u - 1)
  unfold push
  linarith

lemma push_of_le {u : ℝ} (h : u ≤ -1) : push u = 0 := by
  rw [push, phi_of_le_neg_two (by linarith), zero_div]

lemma dpush_of_le {u : ℝ} (h : u ≤ -1) : dpush u = 0 := by
  rw [dpush, dphi_of_le_neg_two (by linarith), zero_div]

lemma push_of_ge {u : ℝ} (h : 3 ≤ u) : push u = 1 := by
  rw [push, phi_of_two_le (by linarith)]
  norm_num

lemma dpush_of_ge {u : ℝ} (h : 3 ≤ u) : dpush u = 0 := by
  rw [dpush, dphi_of_two_le (by linarith), zero_div]

lemma dpush_nonneg (u : ℝ) : 0 ≤ dpush u := div_nonneg (dphi_nonneg _) (by norm_num)

lemma dpush_le (u : ℝ) : dpush u ≤ 1 / 3 := by
  have := dphi_le_one (u - 1)
  unfold dpush
  linarith

lemma dpush_of_mem {u : ℝ} (h0 : 0 ≤ u) (h2 : u ≤ 2) : dpush u = 1 / 3 := by
  rw [dpush, dphi_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)]

lemma dpush_of_neg {u : ℝ} (h1 : -1 ≤ u) (h0 : u ≤ 0) : dpush u = (u + 1) / 3 := by
  simp only [dpush, dphi, pos_of_nonneg (by linarith : 0 ≤ u - 1 + 2),
    pos_of_nonpos (by linarith : u - 1 + 1 ≤ 0), pos_of_nonpos (by linarith : u - 1 - 1 ≤ 0),
    pos_of_nonpos (by linarith : u - 1 - 2 ≤ 0)]
  ring

lemma dpush_of_top {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 3) : dpush u = (3 - u) / 3 := by
  simp only [dpush, dphi, pos_of_nonneg (by linarith : 0 ≤ u - 1 + 2),
    pos_of_nonneg (by linarith : 0 ≤ u - 1 + 1), pos_of_nonneg (by linarith : 0 ≤ u - 1 - 1),
    pos_of_nonpos (by linarith : u - 1 - 2 ≤ 0)]
  ring

lemma push_lipschitz (u v : ℝ) : |push u - push v| ≤ |u - v| / 3 := by
  have h := phi_lipschitz (u - 1) (v - 1)
  have e : u - 1 - (v - 1) = u - v := by ring
  rw [e] at h
  have e2 : push u - push v = (phi (u - 1) - phi (v - 1)) / 3 := by
    unfold push; ring
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

lemma dpush_lipschitz (u v : ℝ) : |dpush u - dpush v| ≤ 4 / 3 * |u - v| := by
  have h := dphi_lipschitz (u - 1) (v - 1)
  have e : u - 1 - (v - 1) = u - v := by ring
  rw [e] at h
  have e2 : dpush u - dpush v = (dphi (u - 1) - dphi (v - 1)) / 3 := by
    unfold dpush; ring
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

lemma push_mono {u v : ℝ} (h : u ≤ v) : push u ≤ push v :=
  monotone_of_hasDerivAt_nonneg push_hasDerivAt (fun x => dpush_nonneg x) h

lemma gate_mono {u v : ℝ} (h : u ≤ v) : gate u ≤ gate v :=
  monotone_of_hasDerivAt_nonneg gate_hasDerivAt (fun x => dgate_nonneg x) h

lemma phi_concave {s t : ℝ} (hs : -1 ≤ s) (ht : -1 ≤ t) :
    phi s - phi t ≤ dphi t * (s - t) := by
  simp only [phi, dphi, rr, pos_of_nonneg (by linarith : 0 ≤ s + 2),
    pos_of_nonneg (by linarith : 0 ≤ s + 1), pos_of_nonneg (by linarith : 0 ≤ t + 2),
    pos_of_nonneg (by linarith : 0 ≤ t + 1)]
  simp only [pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (s - t), sq_nonneg (s - 1), sq_nonneg (s - 2),
    sq_nonneg (t - 1), sq_nonneg (t - 2)]

lemma push_concave {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    push b - push a ≤ dpush a * (b - a) := by
  have h := phi_concave (s := b - 1) (t := a - 1) (by linarith) (by linarith)
  unfold push dpush
  have e : b - 1 - (a - 1) = b - a := by ring
  rw [e] at h
  linarith

section Potential

variable (lam Lam r0 α r : ℝ)

noncomputable def hpot (v : ℝ) : ℝ :=
  α * push (v / r) - lam * v ^ 2 / 2 - Lam / 2 * pos (-v - r0 / 2) ^ 2

noncomputable def dhpot (v : ℝ) : ℝ :=
  α * dpush (v / r) / r - lam * v + Lam * pos (-v - r0 / 2)

variable {lam Lam r0 α r}

lemma hpot_le_amp (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam) (hα : 0 ≤ α) (v : ℝ) :
    hpot lam Lam r0 α r v ≤ α := by
  have h1 := mul_le_mul_of_nonneg_left (push_le_one (v / r)) hα
  have h2 : 0 ≤ lam * v ^ 2 / 2 := by positivity
  have h3 : 0 ≤ Lam / 2 * pos (-v - r0 / 2) ^ 2 := by positivity
  unfold hpot
  linarith

lemma hpot_sub_nonneg (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hr0 : 0 ≤ r0) (hα : 0 ≤ α) (hr : 0 < r)
    {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) :
    hpot lam Lam r0 α r w - hpot lam Lam r0 α r v ≤ dhpot lam Lam r0 α r v ^ 2 / (2 * lam) := by
  have hc := push_concave (a := v / r) (b := w / r) (div_nonneg hv hr.le) (div_nonneg hw hr.le)
  have hc' := mul_le_mul_of_nonneg_left hc hα
  have gv : pos (-v - r0 / 2) = 0 := pos_of_nonpos (by linarith)
  have gw : 0 ≤ Lam / 2 * pos (-w - r0 / 2) ^ 2 := by positivity
  have e : α * (dpush (v / r) * (w / r - v / r)) = α * dpush (v / r) / r * (w - v) := by
    field_simp
  rw [e] at hc'
  set D := dhpot lam Lam r0 α r v with hD
  have hDv : D = α * dpush (v / r) / r - lam * v := by
    rw [hD, dhpot, gv]; ring
  have key : hpot lam Lam r0 α r w - hpot lam Lam r0 α r v ≤ D * (w - v) - lam / 2 * (w - v) ^ 2 := by
    unfold hpot
    rw [gv, hDv]
    nlinarith
  have hq : D * (w - v) - lam / 2 * (w - v) ^ 2 ≤ D ^ 2 / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (D - lam * (w - v))]
  linarith

lemma hpot_le_zero (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam) (hα : 0 ≤ α) (hr : 0 < r)
    {w : ℝ} (hw : w ≤ 0) :
    hpot lam Lam r0 α r w ≤ hpot lam Lam r0 α r 0 + Lam / 2 * pos (-(0 : ℝ) - r0 / 2) ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_left (push_mono (div_le_div_of_nonneg_right hw hr.le)) hα
  have h2 : 0 ≤ lam * w ^ 2 / 2 := by positivity
  have h3 : 0 ≤ Lam / 2 * pos (-w - r0 / 2) ^ 2 := by positivity
  unfold hpot
  nlinarith

lemma hpot_sub_of_nonneg (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hr0 : 0 ≤ r0) (hα : 0 ≤ α) (hr : 0 < r)
    {v : ℝ} (hv : 0 ≤ v) (w : ℝ) :
    hpot lam Lam r0 α r w - hpot lam Lam r0 α r v ≤ dhpot lam Lam r0 α r v ^ 2 / (2 * lam) := by
  rcases le_total 0 w with hw | hw
  · exact hpot_sub_nonneg hlam hLam hr0 hα hr hv hw
  · have h0 := hpot_le_zero (r0 := r0) hlam.le hLam hα hr hw
    have g0 : pos (-(0 : ℝ) - r0 / 2) = 0 := pos_of_nonpos (by linarith)
    rw [g0] at h0
    have h1 := hpot_sub_nonneg hlam hLam hr0 hα hr hv (le_refl (0 : ℝ))
    nlinarith

lemma dhpot_zero (hr0 : 0 ≤ r0) : dhpot lam Lam r0 α r 0 = α / (3 * r) := by
  have g0 : pos (-(0 : ℝ) - r0 / 2) = 0 := pos_of_nonpos (by linarith)
  rw [dhpot, g0, zero_div, dpush_of_mem le_rfl (by norm_num)]
  ring

lemma dhpot_neg_lower (hα : 0 ≤ α) (hr : 0 < r) (hr0 : r0 ≤ r)
    (hαL : α ≤ 3 * Lam * r ^ 2) {v : ℝ} (hv : v < 0) :
    α / (6 * r) ≤ α * dpush (v / r) / r + Lam * pos (-v - r0 / 2) := by
  have hLam : 0 ≤ Lam := by
    by_contra hc
    have : 3 * Lam * r ^ 2 < 0 := by nlinarith [sq_pos_of_pos hr, not_le.mp hc]
    linarith
  have hp : -v - r / 2 ≤ pos (-v - r0 / 2) := by
    have := le_max_left (-v - r0 / 2) 0
    unfold pos
    linarith
  have hp0 := pos_nonneg (-v - r0 / 2)
  have hd0 := dpush_nonneg (v / r)
  have e6 : α / (6 * r) = α * (1 / 6) / r := by field_simp
  rcases le_total (-(r / 2)) v with h1 | h1
  · have hu1 : -1 ≤ v / r := by rw [le_div_iff₀ hr]; linarith
    have hu0 : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.le hr.le
    have hd : 1 / 6 ≤ dpush (v / r) := by
      rw [dpush_of_neg hu1 hu0]
      have : -(1 / 2) ≤ v / r := by rw [le_div_iff₀ hr]; linarith
      linarith
    rw [e6]
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hα) hr.le
    nlinarith [mul_nonneg hLam hp0]
  · rcases le_total (-r) v with h2 | h2
    · have hu1 : -1 ≤ v / r := by rw [le_div_iff₀ hr]; linarith
      have hu0 : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.le hr.le
      rw [dpush_of_neg hu1 hu0]
      have e : α * ((v / r + 1) / 3) / r = α * (v + r) / (3 * r ^ 2) := by field_simp
      rw [e, div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      have hw : 0 ≤ v + r := by linarith
      have hq : 0 ≤ -v - r / 2 := by linarith
      have h3 : Lam * (-v - r / 2) ≤ Lam * pos (-v - r0 / 2) := mul_le_mul_of_nonneg_left hp hLam
      have hr3 : 0 ≤ 18 * r ^ 3 := by positivity
      have k1 := mul_le_mul_of_nonneg_right h3 hr3
      have k2 : α * (-v - r / 2) * (6 * r) ≤ 3 * Lam * r ^ 2 * (-v - r / 2) * (6 * r) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hαL hq
      nlinarith
    · have h3 : Lam * (r / 2) ≤ Lam * pos (-v - r0 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hLam
      have h4 : 0 ≤ α * dpush (v / r) / r := div_nonneg (mul_nonneg hα hd0) hr.le
      have h5 : α / (6 * r) ≤ Lam * (r / 2) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith

lemma hpot_sub_le (hlam : 0 < lam) (hlL : lam ≤ Lam) (hr0 : 0 ≤ r0) (hα : 0 ≤ α) (hr : 0 < r)
    (hr0r : r0 ≤ r) (hαL : α ≤ 3 * Lam * r ^ 2) (v w : ℝ) :
    hpot lam Lam r0 α r w - hpot lam Lam r0 α r v ≤ 5 / (2 * lam) * dhpot lam Lam r0 α r v ^ 2 := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlL
  rcases le_or_gt 0 v with hv | hv
  · have h := hpot_sub_of_nonneg hlam hLam.le hr0 hα hr hv w
    have e : dhpot lam Lam r0 α r v ^ 2 / (2 * lam) ≤ 5 / (2 * lam) * dhpot lam Lam r0 α r v ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [sq_nonneg (dhpot lam Lam r0 α r v)]
    linarith
  · have h0 := hpot_sub_of_nonneg hlam hLam.le hr0 hα hr (le_refl (0 : ℝ)) w
    rw [dhpot_zero hr0] at h0
    have hlow := dhpot_neg_lower hα hr hr0r hαL hv
    obtain ⟨p, hp⟩ : ∃ p, p = pos (-v - r0 / 2) := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, a = α * dpush (v / r) / r + Lam * p := ⟨_, rfl⟩
    rw [← hp, ← ha] at hlow
    have hp0 : 0 ≤ p := by rw [hp]; exact pos_nonneg _
    have ha0 : 0 ≤ α / (6 * r) := by positivity
    have hd : dhpot lam Lam r0 α r v = a + lam * (-v) := by
      rw [ha, hp, dhpot]; ring
    have hLp : Lam * p ≤ a := by
      rw [ha]
      have : 0 ≤ α * dpush (v / r) / r := div_nonneg (mul_nonneg hα (dpush_nonneg _)) hr.le
      linarith
    have hu : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.le hr.le
    have hpl : push 0 - push (v / r) ≤ -(v / r) / 3 := by
      have h := push_lipschitz 0 (v / r)
      rw [zero_sub, abs_neg, abs_of_nonpos hu] at h
      exact (le_abs_self _).trans h
    have g0 : pos (-(0 : ℝ) - r0 / 2) = 0 := pos_of_nonpos (by linarith)
    have h00 : hpot lam Lam r0 α r 0 = α * push 0 := by
      unfold hpot
      rw [g0, zero_div]
      ring
    have hvv : hpot lam Lam r0 α r v = α * push (v / r) - lam * v ^ 2 / 2 - Lam / 2 * p ^ 2 := by
      rw [hp, hpot]
    have hdiff : hpot lam Lam r0 α r 0 - hpot lam Lam r0 α r v ≤
        α * (-v / (3 * r)) + lam * v ^ 2 / 2 + Lam / 2 * p ^ 2 := by
      rw [h00, hvv]
      have e : -(v / r) / 3 = -v / (3 * r) := by field_simp
      rw [e] at hpl
      have := mul_le_mul_of_nonneg_left hpl hα
      linarith
    have hA : α / (3 * r) ≤ 2 * a := by
      have e : α / (3 * r) = 2 * (α / (6 * r)) := by field_simp; ring
      rw [e]; linarith
    have hA0 : 0 ≤ α / (3 * r) := by positivity
    have hb : 0 ≤ lam * (-v) := by nlinarith
    have ha' : 0 ≤ a := le_trans ha0 hlow
    have h1 : (α / (3 * r)) ^ 2 ≤ 4 * a ^ 2 := by
      nlinarith [mul_self_le_mul_self hA0 hA]
    have h2 : α * (-v / (3 * r)) * lam ≤ 2 * a * (lam * (-v)) := by
      have e : α * (-v / (3 * r)) * lam = α / (3 * r) * (lam * (-v)) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hA hb
    have h4 : Lam * p ^ 2 * lam ≤ a ^ 2 := by
      have hLp0 : 0 ≤ Lam * p := mul_nonneg hLam.le hp0
      have h5 := mul_self_le_mul_self hLp0 hLp
      have h6 : lam * (Lam * p ^ 2) ≤ Lam * (Lam * p ^ 2) :=
        mul_le_mul_of_nonneg_right hlL (mul_nonneg hLam.le (sq_nonneg p))
      nlinarith
    have key : (hpot lam Lam r0 α r w - hpot lam Lam r0 α r v) * (2 * lam) ≤
        5 * (a + lam * (-v)) ^ 2 := by
      have k0 : (hpot lam Lam r0 α r w - hpot lam Lam r0 α r 0) * (2 * lam) ≤ (α / (3 * r)) ^ 2 := by
        have := mul_le_mul_of_nonneg_right h0 (by positivity : (0 : ℝ) ≤ 2 * lam)
        rwa [div_mul_cancel₀ _ (by positivity : (2 * lam : ℝ) ≠ 0)] at this
      have k1 : (hpot lam Lam r0 α r 0 - hpot lam Lam r0 α r v) * (2 * lam) ≤
          (α * (-v / (3 * r)) + lam * v ^ 2 / 2 + Lam / 2 * p ^ 2) * (2 * lam) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
      have k2 : (α * (-v / (3 * r)) + lam * v ^ 2 / 2 + Lam / 2 * p ^ 2) * (2 * lam) =
          2 * (α * (-v / (3 * r)) * lam) + (lam * (-v)) ^ 2 + Lam * p ^ 2 * lam := by ring
      nlinarith [mul_nonneg ha' hb, sq_nonneg (lam * (-v))]
    rw [hd]
    have e : 5 / (2 * lam) * (a + lam * (-v)) ^ 2 = 5 * (a + lam * (-v)) ^ 2 / (2 * lam) := by ring
    rw [e, le_div_iff₀ (by positivity)]
    exact key

lemma dhpot_strong_lower (hlam : 0 ≤ lam) (hα : 0 ≤ α) (hr : 0 < r) (hr0r : r0 ≤ r)
    (hαL : α ≤ 3 * Lam * r ^ 2) (hstrong : 24 * lam * r ^ 2 ≤ α) {v : ℝ} (hv : v < 2 * r) :
    α / (6 * r) ≤ dhpot lam Lam r0 α r v := by
  rcases le_or_gt 0 v with h0 | h0
  · have hu0 : 0 ≤ v / r := div_nonneg h0 hr.le
    have hu2 : v / r ≤ 2 := by rw [div_le_iff₀ hr]; linarith
    have hp0 := pos_nonneg (-v - r0 / 2)
    have hLam : 0 ≤ Lam := by
      by_contra hc
      have : 3 * Lam * r ^ 2 < 0 := by nlinarith [sq_pos_of_pos hr, not_le.mp hc]
      linarith
    rw [dhpot, dpush_of_mem hu0 hu2]
    have e : α * (1 / 3) / r = α / (3 * r) := by field_simp
    rw [e]
    have h1 : lam * v ≤ α / (12 * r) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hv.le hlam, mul_nonneg hlam h0]
    have e3 : α / (3 * r) = α / (6 * r) + 2 * (α / (12 * r)) := by field_simp; ring
    have h6 : 0 ≤ α / (12 * r) := by positivity
    nlinarith [mul_nonneg hLam hp0]
  · have h := dhpot_neg_lower hα hr hr0r hαL h0
    have : 0 ≤ -(lam * v) := by nlinarith
    unfold dhpot
    linarith

lemma exists_hpot_max (hlam : 0 < lam) (hlL : lam ≤ Lam) (hr0 : 0 ≤ r0) (hα : 0 ≤ α) (hr : 0 < r)
    (hr0r : r0 ≤ r) (hαL : α ≤ 3 * Lam * r ^ 2) (hstrong : 6 * lam * r ^ 2 ≤ α) :
    ∃ v, 2 * r ≤ v ∧ ∀ w, hpot lam Lam r0 α r w ≤ hpot lam Lam r0 α r v := by
  have hden : 0 < α + 3 * lam * r ^ 2 := by positivity
  obtain ⟨v, hvD⟩ : ∃ v, v * (α + 3 * lam * r ^ 2) = 3 * r * α :=
    ⟨3 * r * α / (α + 3 * lam * r ^ 2), div_mul_cancel₀ _ hden.ne'⟩
  have hlr : 0 < lam * r ^ 2 := by positivity
  have hv2 : 2 * r ≤ v := by
    by_contra hc
    have hlt : v < 2 * r := not_le.mp hc
    have h1 : v * (α + 3 * lam * r ^ 2) < 2 * r * (α + 3 * lam * r ^ 2) :=
      mul_lt_mul_of_pos_right hlt hden
    nlinarith [mul_le_mul_of_nonneg_left hstrong hr.le]
  have hv3 : v ≤ 3 * r := by
    by_contra hc
    have hlt : 3 * r < v := not_le.mp hc
    have h1 : 3 * r * (α + 3 * lam * r ^ 2) < v * (α + 3 * lam * r ^ 2) :=
      mul_lt_mul_of_pos_right hlt hden
    nlinarith [mul_pos hr hlr]
  refine ⟨v, hv2, fun w => ?_⟩
  have hu2 : 2 ≤ v / r := by rw [le_div_iff₀ hr]; linarith
  have hu3 : v / r ≤ 3 := by rw [div_le_iff₀ hr]; linarith
  have hd : dhpot lam Lam r0 α r v = 0 := by
    have g : pos (-v - r0 / 2) = 0 := pos_of_nonpos (by nlinarith)
    have e : α * ((3 - v / r) / 3) / r = α * (3 * r - v) / (3 * r ^ 2) := by
      field_simp
    rw [dhpot, g, dpush_of_top hu2 hu3, e, mul_zero, add_zero, sub_eq_zero,
      div_eq_iff (by positivity)]
    linear_combination -hvD
  have h := hpot_sub_le hlam hlL hr0 hα hr hr0r hαL v w
  rw [hd] at h
  have hz : (5 : ℝ) / (2 * lam) * 0 ^ 2 = 0 := by ring
  rw [hz] at h
  linarith

end Potential

end LongTails.Proofs.NcPlProfiles
