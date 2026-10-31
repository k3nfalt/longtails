import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Topology

open Set Metric Filter
open scoped Topology

namespace LongTails.Proofs.SymmetricGeneralizedSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma local_segment_sup_bound {g : E → E} (hg : Continuous g) (x : E)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y, ‖y - x‖ < δ →
      sSup ((fun z => ‖g z‖) '' segment ℝ x y) ≤ ‖g x‖ + η := by
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hg.norm.continuousAt η hη
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  apply csSup_le (Set.Nonempty.image _ ⟨x, left_mem_segment ℝ x y⟩)
  rintro _ ⟨z, hz, rfl⟩
  have hzball := (convex_ball x δ).segment_subset (mem_ball_self hδ)
    (show y ∈ ball x δ by simpa [dist_eq_norm] using hy) hz
  have hz' := hb hzball
  rw [Real.dist_eq] at hz'
  have h := le_abs_self (‖g z‖ - ‖g x‖)
  linarith

lemma local_gradient_lipschitz_bound {g : E → E} (hg : Continuous g)
    {L0 L1 : ℝ} (hL1 : 0 ≤ L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (x : E) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y, ‖y - x‖ < δ →
      ‖g y - g x‖ ≤ (L0 + L1 * (‖g x‖ + η)) * ‖y - x‖ := by
  obtain ⟨δ, hδ, hb⟩ := local_segment_sup_bound hg x hη
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have h := hgs x y
  rw [norm_sub_rev (g x) (g y), norm_sub_rev x y] at h
  apply h.trans
  gcongr
  exact hb y hy

lemma ray_norm_liminf_slope {g : E → E} (hg : Continuous g)
    {L0 L1 : ℝ} (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (y v : E) (hv : v ≠ 0) (t c : ℝ)
    (hc : (L0 + L1 * ‖g (y + t • v)‖) * ‖v‖ < c) :
    ∃ᶠ z in 𝓝[>] t,
      (z - t)⁻¹ * (‖g (y + z • v)‖ - ‖g (y + t • v)‖) < c := by
  let A := (L0 + L1 * ‖g (y + t • v)‖) * ‖v‖
  let η := (c - A) / (2 * L1 * ‖v‖)
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hη : 0 < η := div_pos (sub_pos.mpr hc) (by positivity)
  obtain ⟨δ, hδ, hb⟩ := local_gradient_lipschitz_bound hg hL1.le hgs (y + t • v) hη
  have hcont : Continuous (fun z : ℝ => ‖(y + z • v) - (y + t • v)‖) := by fun_prop
  have hev : ∀ᶠ z in 𝓝 t, ‖(y + z • v) - (y + t • v)‖ < δ :=
    hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hδ))
  have hev' : ∀ᶠ z in 𝓝[>] t, ‖(y + z • v) - (y + t • v)‖ < δ :=
    hev.filter_mono nhdsWithin_le_nhds
  have hcoef : (L0 + L1 * (‖g (y + t • v)‖ + η)) * ‖v‖ < c := by
    have he : 2 * L1 * ‖v‖ * η = c - A := by
      dsimp [η]
      field_simp
    dsimp [A] at he
    nlinarith
  apply Filter.Eventually.frequently
  filter_upwards [hev', self_mem_nhdsWithin] with z hz hzt
  have hzt' : 0 < z - t := sub_pos.mpr hzt
  have h := hb (y + z • v) hz
  have he : ‖(y + z • v) - (y + t • v)‖ = (z - t) * ‖v‖ := by
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hzt']
  rw [he] at h
  have hn := norm_sub_norm_le (g (y + z • v)) (g (y + t • v))
  have hs := mul_le_mul_of_nonneg_left (hn.trans h) (inv_nonneg.mpr hzt'.le)
  have hid : (z - t)⁻¹ * ((L0 + L1 * (‖g (y + t • v)‖ + η)) * ((z - t) * ‖v‖)) =
      (L0 + L1 * (‖g (y + t • v)‖ + η)) * ‖v‖ := by
    field_simp
  rw [hid] at hs
  exact hs.trans_lt hcoef

lemma gradient_ray_growth {g : E → E} (hg : Continuous g)
    {L0 L1 : ℝ} (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (y v : E) {t : ℝ} (ht : 0 ≤ t) :
    L0 + L1 * ‖g (y + t • v)‖ ≤
      (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖v‖ * t) := by
  by_cases hv : v = 0
  · simp [hv]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hK : L1 * ‖v‖ ≠ 0 := ne_of_gt (mul_pos hL1 hvp)
  have hcont : Continuous (fun z : ℝ => ‖g (y + z • v)‖) :=
    hg.norm.comp (by fun_prop)
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun z => ‖g (y + z • v)‖)
    (f' := fun z => (L0 + L1 * ‖g (y + z • v)‖) * ‖v‖)
    (δ := ‖g y‖) (K := L1 * ‖v‖) (ε := L0 * ‖v‖) (a := 0) (b := t)
    hcont.continuousOn
    (fun z _ c hc => ray_norm_liminf_slope hg hL1 hgs y v hv z c hc)
    (by simp) (by intro z hz; exact le_of_eq (by ring)) t ⟨ht, le_rfl⟩
  rw [sub_zero, gronwallBound_of_K_ne_0 hK] at h
  have hmul := mul_le_mul_of_nonneg_left h hL1.le
  have he : L1 * (L0 * ‖v‖ / (L1 * ‖v‖)) = L0 := by field_simp
  dsimp only at hmul
  rw [mul_add, ← mul_assoc L1 (L0 * ‖v‖ / (L1 * ‖v‖)), he] at hmul
  nlinarith only [hmul]

lemma gradient_growth {g : E → E} (hg : Continuous g)
    {L0 L1 : ℝ} (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (x y : E) :
    L0 + L1 * ‖g x‖ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) := by
  simpa using gradient_ray_growth hg hL1 hgs y (x - y) (t := 1) zero_le_one

lemma gradient_difference_bound {g : E → E} (hg : Continuous g)
    {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (x y : E) :
    ‖g x - g y‖ ≤
      (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) * ‖x - y‖ := by
  have hseg : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hco : IsCompact ((fun z => ‖g z‖) '' segment ℝ x y) :=
    hseg.image hg.norm
  have hne : ((fun z => ‖g z‖) '' segment ℝ x y).Nonempty :=
    Set.Nonempty.image _ ⟨x, left_mem_segment ℝ x y⟩
  obtain ⟨z, hz, he⟩ := hco.sSup_mem hne
  have hzball := (convex_closedBall y ‖x - y‖).segment_subset
    (show x ∈ closedBall y ‖x - y‖ by simp [mem_closedBall, dist_eq_norm])
    (mem_closedBall_self (norm_nonneg (x - y))) hz
  have hzdist : ‖z - y‖ ≤ ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm] using hzball
  have hcurv := (gradient_growth hg hL1 hgs z y).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzdist hL1.le))
      (show 0 ≤ L0 + L1 * ‖g y‖ by positivity))
  dsimp only at he
  rw [he] at hcurv
  exact (hgs x y).trans (mul_le_mul_of_nonneg_right hcurv (norm_nonneg _))

end LongTails.Proofs.SymmetricGeneralizedSmooth
