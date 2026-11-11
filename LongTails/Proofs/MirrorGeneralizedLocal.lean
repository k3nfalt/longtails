import LongTails.Setups.MirrorGeneralizedSmooth
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

open Set

namespace LongTails.Proofs.MirrorGeneralizedLocal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F]

open LongTails.Setups.MirrorGeneralizedSmooth

lemma segment_gradient_bound {g : E → F} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hg : Continuous g) (hs : SegmentSmooth g L0 L1) (x w : E)
    (hr : L1 * ‖w - x‖ ≤ 1 / 2) :
    ‖g w‖ ≤ 2 * (‖g x‖ + L0 * ‖w - x‖) := by
  set r := ‖w - x‖
  have hcont : ContinuousOn (fun t : ℝ => ‖g (x + t • (w - x))‖) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => ‖g (x + t • (w - x))‖).continuousOn
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hcont
  set S := ‖g (x + t0 • (w - x))‖
  have hS : ∀ θ ∈ Icc (0 : ℝ) 1, ‖g (x + θ • (x + t0 • (w - x) - x))‖ ≤ S := by
    intro θ hθ
    have hmem : θ * t0 ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hθ.1 ht0.1, by nlinarith [hθ.1, hθ.2, ht0.1, ht0.2]⟩
    have h := hmax hmem
    simp only [mem_ofPred_eq] at h
    have he : x + θ • (x + t0 • (w - x) - x) = x + (θ * t0) • (w - x) := by
      rw [add_sub_cancel_left, smul_smul]
    rw [he]
    exact h
  have h := hs x (x + t0 • (w - x)) S hS
  have hd : ‖x - (x + t0 • (w - x))‖ ≤ r := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht0.2
  have hS0 : 0 ≤ S := norm_nonneg _
  have hdiff : S ≤ ‖g x‖ + (L0 + L1 * S) * r := by
    have h1 : S ≤ ‖g x‖ + ‖g x - g (x + t0 • (w - x))‖ := by
      have := norm_sub_norm_le (g (x + t0 • (w - x))) (g x)
      rw [norm_sub_rev] at this
      linarith
    have h2 : (L0 + L1 * S) * ‖x - (x + t0 • (w - x))‖ ≤ (L0 + L1 * S) * r :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    linarith
  have hw : ‖g w‖ ≤ S := by
    have h1 := hmax (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    simp only [mem_ofPred_eq, one_smul, add_sub_cancel] at h1
    exact h1
  have hr0 : 0 ≤ r := norm_nonneg _
  nlinarith

lemma ball_lipschitz {g : E → F} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hg : Continuous g) (hs : SegmentSmooth g L0 L1) {x u v : E} {r : ℝ}
    (hr : L1 * r ≤ 1 / 2) (hu : ‖u - x‖ ≤ r) (hv : ‖v - x‖ ≤ r) :
    ‖g u - g v‖ ≤ 2 * (L0 + L1 * ‖g x‖) * ‖u - v‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hu
  have hpt : ∀ θ ∈ Icc (0 : ℝ) 1, ‖g (u + θ • (v - u))‖ ≤ 2 * (‖g x‖ + L0 * r) := by
    intro θ hθ
    have hdist : ‖u + θ • (v - u) - x‖ ≤ r := by
      have he : u + θ • (v - u) - x = (1 - θ) • (u - x) + θ • (v - x) := by module
      rw [he]
      calc ‖(1 - θ) • (u - x) + θ • (v - x)‖ ≤ ‖(1 - θ) • (u - x)‖ + ‖θ • (v - x)‖ :=
            norm_add_le _ _
        _ = (1 - θ) * ‖u - x‖ + θ * ‖v - x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr hθ.2), abs_of_nonneg hθ.1]
        _ ≤ (1 - θ) * r + θ * r := by
            gcongr
            · exact sub_nonneg.mpr hθ.2
            · exact hθ.1
        _ = r := by ring
    have h := segment_gradient_bound hL0 hL1 hg hs x (u + θ • (v - u))
      (le_trans (mul_le_mul_of_nonneg_left hdist hL1) hr)
    have h2 : L0 * ‖u + θ • (v - u) - x‖ ≤ L0 * r := mul_le_mul_of_nonneg_left hdist hL0
    linarith
  have h := hs u v _ hpt
  have hc : L0 + L1 * (2 * (‖g x‖ + L0 * r)) ≤ 2 * (L0 + L1 * ‖g x‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hr hL0]
  exact h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

lemma segment_upper_bound {f : E → ℝ} {g : E → E →L[ℝ] ℝ} {L : ℝ}
    (hg : ∀ x, HasFDerivAt f (g x) x) (x y : E)
    (hlip : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖g (x + t • (y - x)) - g x‖ ≤ L * t * ‖y - x‖) :
    f y ≤ f x + g x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let F' := fun t : ℝ => g (x + t • d) d
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := (hg _).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    simp only [id_eq, one_smul] at h
    exact h
  let B := fun t : ℝ => f x + t * g x d + t ^ 2 * (L / 2 * ‖d‖ ^ 2)
  have hB : ∀ t, HasDerivAt B (g x d + L * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const (g x d) |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖d‖ ^ 2)) using 1
    · funext u
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, F' t ≤ g x d + L * ‖d‖ ^ 2 * t := by
    intro t ht
    have h := ((le_abs_self ((g (x + t • d) - g x) d)).trans ((g (x + t • d) - g x).le_opNorm d)).trans
      (mul_le_mul_of_nonneg_right (hlip t ht) (norm_nonneg d))
    simp only [sub_apply] at h
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

lemma ball_upper {f : E → ℝ} {g : E → E →L[ℝ] ℝ} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hf : ∀ x, HasFDerivAt f (g x) x) (hg : Continuous g) (hs : SegmentSmooth g L0 L1)
    {x u v : E} {r : ℝ} (hr : L1 * r ≤ 1 / 2) (hu : ‖u - x‖ ≤ r) (hv : ‖v - x‖ ≤ r) :
    f v ≤ f u + g u (v - u) + (L0 + L1 * ‖g x‖) * ‖v - u‖ ^ 2 := by
  have h := segment_upper_bound (L := 2 * (L0 + L1 * ‖g x‖)) hf u v (by
    intro t ht
    have hpt : ‖u + t • (v - u) - x‖ ≤ r := by
      have he : u + t • (v - u) - x = (1 - t) • (u - x) + t • (v - x) := by module
      rw [he]
      calc ‖(1 - t) • (u - x) + t • (v - x)‖ ≤ ‖(1 - t) • (u - x)‖ + ‖t • (v - x)‖ :=
            norm_add_le _ _
        _ = (1 - t) * ‖u - x‖ + t * ‖v - x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr ht.2.le), abs_of_nonneg ht.1]
        _ ≤ (1 - t) * r + t * r := by
            gcongr
            · exact sub_nonneg.mpr ht.2.le
            · exact ht.1
        _ = r := by ring
    have h := ball_lipschitz hL0 hL1 hg hs hr hpt hu
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
    linarith)
  linarith

lemma approximate_norming (g : E →L[ℝ] ℝ) (hg : 0 < ‖g‖) :
    ∃ d : E, ‖d‖ ≤ 1 ∧ ‖g‖ / 2 ≤ g d := by
  obtain ⟨d, hd, hgd⟩ := g.exists_lt_apply_of_lt_opNorm (by linarith : ‖g‖ / 2 < ‖g‖)
  rw [Real.norm_eq_abs] at hgd
  by_cases h : 0 ≤ g d
  · rw [abs_of_nonneg h] at hgd
    exact ⟨d, hd.le, hgd.le⟩
  · refine ⟨-d, by simpa using hd.le, ?_⟩
    rw [map_neg]
    rw [abs_of_neg (lt_of_not_ge h)] at hgd
    exact hgd.le

lemma gradient_self_bound {f : E → ℝ} {g : E → E →L[ℝ] ℝ} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasFDerivAt f (g x) x)
    (hg : Continuous g) (hs : SegmentSmooth g L0 L1)
    {xs : E} (hmin : ∀ w, f xs ≤ f w) (x : E) :
    ‖g x‖ ^ 2 ≤ 16 * (L0 + L1 * ‖g x‖) * (f x - f xs) := by
  by_cases hz : ‖g x‖ = 0
  · rw [hz]
    have hgap : 0 ≤ f x - f xs := sub_nonneg.mpr (hmin x)
    simpa using mul_nonneg (show 0 ≤ 16 * (L0 + L1 * 0) by positivity) hgap
  have hG : 0 < ‖g x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  obtain ⟨d, hd, hgd⟩ := approximate_norming (g x) hG
  set M := L0 + L1 * ‖g x‖
  have hM : 0 < M := by dsimp [M]; positivity
  set t := ‖g x‖ / (4 * M)
  have ht : 0 < t := by positivity
  have htM : t * (4 * M) = ‖g x‖ := by dsimp [t]; field_simp
  have hrad : L1 * t ≤ 1 / 2 := by
    have hh : L1 * ‖g x‖ ≤ M := by dsimp [M]; linarith
    nlinarith
  have hdist : ‖(x - t • d) - x‖ ≤ t := by
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_of_le_one_right ht.le hd
  have hu := ball_upper hL0.le hL1 hf hg hs hrad
    (show ‖x - x‖ ≤ t by simpa using ht.le) hdist
  have he : g x ((x - t • d) - x) = -t * g x d := by simp
  rw [he] at hu
  have hsquare : ‖(x - t • d) - x‖ ^ 2 ≤ t ^ 2 := by
    nlinarith [norm_nonneg ((x - t • d) - x)]
  have hlow := hmin (x - t • d)
  have hdec : t * ‖g x‖ / 2 - M * t ^ 2 ≤ f x - f xs := by
    have := mul_le_mul_of_nonneg_left hsquare hM.le
    dsimp [M] at this
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hdec (show 0 ≤ 16 * M by positivity)]

lemma curvature_of_self_bound {L0 L1 G δ : ℝ} (hL0 : 0 ≤ L0)
    (hδ : 0 ≤ δ) (h : G ^ 2 ≤ 16 * (L0 + L1 * G) * δ) :
    L0 + L1 * G ≤ 2 * L0 + 32 * L1 ^ 2 * δ := by
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg L1)
  by_contra hn
  push Not at hn
  have hu : L0 + 32 * L1 ^ 2 * δ < L1 * G := by linarith
  have hb : 0 ≤ L1 ^ 2 * δ := mul_nonneg (sq_nonneg L1) hδ
  have hh' : (L1 * G) ^ 2 ≤ 16 * L0 * (L1 ^ 2 * δ) +
      16 * (L1 * G) * (L1 ^ 2 * δ) := by nlinarith [hh]
  nlinarith [mul_nonneg (show 0 ≤ L1 * G by linarith)
    (show 0 ≤ L1 * G - 32 * L1 ^ 2 * δ by linarith)]

lemma curvature_gap_bound {f : E → ℝ} {g : E → E →L[ℝ] ℝ} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasFDerivAt f (g x) x)
    (hg : Continuous g) (hs : SegmentSmooth g L0 L1)
    {xs : E} (hmin : ∀ w, f xs ≤ f w) (x : E) :
    L0 + L1 * ‖g x‖ ≤ 2 * L0 + 32 * L1 ^ 2 * (f x - f xs) :=
  curvature_of_self_bound hL0.le (sub_nonneg.mpr (hmin x))
    (gradient_self_bound hL0 hL1 hf hg hs hmin x)

end LongTails.Proofs.MirrorGeneralizedLocal
