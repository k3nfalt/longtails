import LongTails.Algorithms.BallAnchoredNewton
import LongTails.Proofs.HessianStableNewton
import LongTails.Proofs.CachedJacobianGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped RealInnerProductSpace
open Set

namespace LongTails.Proofs.BallAnchoredInner

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.HessianStableNewton

noncomputable section

variable {p : Public}

structure Regular (p : Public) (F : p.E → p.E) (S : p.E →L[ℝ] p.E) : Prop where
  M_pos : 0 < p.M
  D_pos : 0 < p.D
  ε_pos : 0 < p.ε
  diff : ∀ x, HasFDerivAt F (fderiv ℝ F x) x
  skew : ∀ v, ⟪S v, v⟫ = 0
  sa : ∀ x u v, ⟪(fderiv ℝ F x - S) u, v⟫ = ⟪u, (fderiv ℝ F x - S) v⟫
  psd : ∀ x v, 0 ≤ ⟪(fderiv ℝ F x - S) v, v⟫
  stab : ∀ x y v, ⟪(fderiv ℝ F y - S) v, v⟫ ≤
    Real.exp (p.M * ‖y - x‖) * ⟪(fderiv ℝ F x - S) v, v⟫

def Hs (F : p.E → p.E) (S : p.E →L[ℝ] p.E) (x : p.E) : p.E →L[ℝ] p.E := fderiv ℝ F x - S

lemma radius_pos (hreg : Regular p F S) : 0 < radius p := by
  unfold radius; have := hreg.M_pos; positivity

lemma M_radius (hreg : Regular p F S) : p.M * radius p = 1 / 8 := by
  unfold radius; have := hreg.M_pos.ne'; field_simp

lemma exp_le_of_dist (hreg : Regular p F S) {x y : p.E} {m : ℝ} (hxy : ‖y - x‖ ≤ m * radius p) :
    Real.exp (p.M * ‖y - x‖) ≤ Real.exp (m / 8) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hxy hreg.M_pos.le
  rw [show p.M * (m * radius p) = m * (p.M * radius p) by ring, M_radius hreg] at h
  linarith

lemma exp_eighth_le : Real.exp (1 / 8) ≤ 2 := by
  have h1 : Real.exp (1 / 8) ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr (by norm_num)
  linarith [exp_quarter_le]

lemma qf_Hs_eq (hreg : Regular p F S) (x v : p.E) :
    qf (Hs F S x) v = ⟪fderiv ℝ F x v, v⟫ := by
  unfold qf Hs
  rw [sub_apply, inner_sub_left, hreg.skew v, sub_zero]

lemma qf_Hs_le (hreg : Regular p F S) (x v : p.E) :
    qf (Hs F S x) v ≤ ‖fderiv ℝ F x‖ * ‖v‖ ^ 2 := by
  rw [qf_Hs_eq hreg]
  calc ⟪fderiv ℝ F x v, v⟫ ≤ ‖fderiv ℝ F x v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ ‖fderiv ℝ F x‖ * ‖v‖ * ‖v‖ := by
      gcongr; exact (fderiv ℝ F x).le_opNorm v
    _ = _ := by ring

lemma Hs_norm_le (hreg : Regular p F S) {c u : p.E} {s : ℝ}
    (hs : Real.exp (p.M * ‖u - c‖) ≤ s) (w : p.E) :
    ‖Hs F S u w‖ ≤ s * ‖fderiv ℝ F c‖ * ‖w‖ := by
  apply norm_apply_le_of_qf (hreg.sa u) (hreg.psd u)
  intro v
  have h1 := hreg.stab c u v
  have h2 := qf_Hs_le hreg c v
  have h3 := hreg.psd c v
  change qf (Hs F S u) v ≤ Real.exp (p.M * ‖u - c‖) * qf (Hs F S c) v at h1
  have h4 : Real.exp (p.M * ‖u - c‖) * qf (Hs F S c) v ≤ s * qf (Hs F S c) v :=
    mul_le_mul_of_nonneg_right hs h3
  calc qf (Hs F S u) v ≤ s * qf (Hs F S c) v := h1.trans h4
    _ ≤ s * (‖fderiv ℝ F c‖ * ‖v‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left h2
      exact (Real.exp_pos _).le.trans hs
    _ = _ := by ring

lemma S_norm_le (hreg : Regular p F S) (c w : p.E) : ‖S w‖ ≤ 2 * ‖fderiv ℝ F c‖ * ‖w‖ := by
  have h1 := Hs_norm_le hreg (c := c) (u := c) (s := 1) (by simp) w
  have e : S w = fderiv ℝ F c w - Hs F S c w := by
    unfold Hs; rw [sub_apply]; abel
  rw [e]
  calc _ ≤ ‖fderiv ℝ F c w‖ + ‖Hs F S c w‖ := norm_sub_le _ _
    _ ≤ ‖fderiv ℝ F c‖ * ‖w‖ + 1 * ‖fderiv ℝ F c‖ * ‖w‖ :=
      add_le_add ((fderiv ℝ F c).le_opNorm w) h1
    _ = _ := by ring

lemma deriv_norm_ball (hreg : Regular p F S) {c u : p.E} (hu : ‖u - c‖ ≤ radius p) :
    ‖fderiv ℝ F u‖ ≤ 4 * ‖fderiv ℝ F c‖ := by
  have hs : Real.exp (p.M * ‖u - c‖) ≤ 2 :=
    (exp_le_of_dist hreg (m := 1) (by linarith)).trans exp_eighth_le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have e : fderiv ℝ F u w = Hs F S u w + S w := by
    unfold Hs; rw [sub_apply]; abel
  rw [e]
  calc _ ≤ ‖Hs F S u w‖ + ‖S w‖ := norm_add_le _ _
    _ ≤ 2 * ‖fderiv ℝ F c‖ * ‖w‖ + 2 * ‖fderiv ℝ F c‖ * ‖w‖ :=
      add_le_add (Hs_norm_le hreg hs w) (S_norm_le hreg c w)
    _ = _ := by ring


lemma line_deriv (hreg : Regular p F S) (x e e' : p.E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ⟪F (x + t • e), e'⟫) ⟪fderiv ℝ F (x + s • e) e, e'⟫ s := by
  have hline : HasDerivAt (fun t : ℝ => x + t • e) e s := by
    simpa using ((hasDerivAt_id s).smul_const e).const_add x
  have hF : HasDerivAt (fun t : ℝ => F (x + t • e)) (fderiv ℝ F (x + s • e) e) s :=
    (hreg.diff _).comp_hasDerivAt s hline
  simpa using hF.inner ℝ (hasDerivAt_const s e')

lemma mvt_inner (hreg : Regular p F S) (x e e' : p.E) :
    ∃ ξ ∈ Ioo (0 : ℝ) 1, ⟪F (x + e) - F x, e'⟫ = ⟪fderiv ℝ F (x + ξ • e) e, e'⟫ := by
  have hc : ContinuousOn (fun t : ℝ => ⟪F (x + t • e), e'⟫) (Icc 0 1) :=
    fun t _ => (line_deriv hreg x e e' t).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => ⟪F (x + t • e), e'⟫)
    (fun s => ⟪fderiv ℝ F (x + s • e) e, e'⟫) (by norm_num : (0 : ℝ) < 1) hc
    (fun t _ => line_deriv hreg x e e' t)
  refine ⟨ξ, hξ, ?_⟩
  rw [h]
  simp [inner_sub_left]

lemma deriv_inner_nonneg (hreg : Regular p F S) (x v : p.E) : 0 ≤ ⟪fderiv ℝ F x v, v⟫ := by
  have := hreg.psd x v
  rw [sub_apply, inner_sub_left, hreg.skew v, sub_zero] at this
  exact this

lemma monotone_F (hreg : Regular p F S) (x y : p.E) : 0 ≤ ⟪F x - F y, x - y⟫ := by
  obtain ⟨ξ, -, h⟩ := mvt_inner hreg y (x - y) (x - y)
  rw [show y + (x - y) = x by abel] at h
  rw [h]
  exact deriv_inner_nonneg hreg _ _

lemma lipschitz_ball (hreg : Regular p F S) {c u v : p.E} (hu : ‖u - c‖ ≤ radius p)
    (hv : ‖v - c‖ ≤ radius p) : ‖F u - F v‖ ≤ 4 * ‖fderiv ℝ F c‖ * ‖u - v‖ := by
  have hs : Convex ℝ (Metric.closedBall c (radius p)) := convex_closedBall c _
  have hd : ∀ x ∈ Metric.closedBall c (radius p),
      HasFDerivWithinAt F (fderiv ℝ F x) (Metric.closedBall c (radius p)) x :=
    fun x _ => (hreg.diff x).hasFDerivWithinAt
  have hb : ∀ x ∈ Metric.closedBall c (radius p), ‖fderiv ℝ F x‖ ≤ 4 * ‖fderiv ℝ F c‖ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    exact deriv_norm_ball hreg hx
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hv)
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hu)

lemma ball_vi_exists (hreg : Regular p F S) {a : ℝ} (ha : 0 < a) (w c : p.E) :
    ∃ u ∈ Metric.closedBall c (radius p), ∀ v ∈ Metric.closedBall c (radius p),
      0 ≤ ⟪a • F u + u - w, v - u⟫ := by
  have hmono : ∀ u ∈ Metric.closedBall c (radius p), ∀ v ∈ Metric.closedBall c (radius p),
      0 ≤ ⟪a • F u - a • F v, u - v⟫ := by
    intro u _ v _
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg ha.le (monotone_F hreg u v)
  have hlip : ∀ u ∈ Metric.closedBall c (radius p), ∀ v ∈ Metric.closedBall c (radius p),
      ‖a • F u - a • F v‖ ≤ (a * (4 * ‖fderiv ℝ F c‖)) * ‖u - v‖ := by
    intro u hu v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hu hv
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_assoc]
    exact mul_le_mul_of_nonneg_left (lipschitz_ball hreg hu hv) ha.le
  obtain ⟨y, hy, hvi⟩ := CachedJacobianGeometry.regularized_vi_exists (F := fun u => a • F u)
    (M := a * (4 * ‖fderiv ℝ F c‖)) (μ := 1) w (isCompact_closedBall c _)
    (convex_closedBall c _) ⟨c, Metric.mem_closedBall_self (radius_pos hreg).le⟩
    (by positivity) one_pos hmono hlip
  refine ⟨y, hy, fun v hv => ?_⟩
  have := hvi v hv
  simpa [one_smul, add_sub_assoc] using this

lemma interior_zero {c u g : p.E} {r : ℝ} (hu : ‖u - c‖ < r)
    (hvi : ∀ v ∈ Metric.closedBall c r, 0 ≤ ⟪g, v - u⟫) : g = 0 := by
  by_contra hg
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  set t := (r - ‖u - c‖) / (‖g‖ + 1) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by positivity)
  have hmem : u - t • g ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖u - t • g - c‖ ≤ ‖u - c‖ + t * ‖g‖ := by
      calc ‖u - t • g - c‖ = ‖(u - c) - t • g‖ := by congr 1; abel
        _ ≤ ‖u - c‖ + ‖t • g‖ := norm_sub_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have h2 : t * ‖g‖ ≤ r - ‖u - c‖ := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have h := hvi _ hmem
  rw [show u - t • g - u = -(t • g) by abel, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at h
  nlinarith [mul_pos ht0 (pow_pos hgn 2)]

lemma affinePoint_spec (hreg : Regular p F S) {a : ℝ} (ha : 0 < a) (c x : p.E) (b : p.E) :
    affinePoint p c (a • fderiv ℝ F x) b ∈ Metric.closedBall c (radius p) ∧
      ∀ v ∈ Metric.closedBall c (radius p),
        0 ≤ ⟪b + (a • fderiv ℝ F x) (affinePoint p c (a • fderiv ℝ F x) b) +
          (1 : ℝ) • affinePoint p c (a • fderiv ℝ F x) b,
          v - affinePoint p c (a • fderiv ℝ F x) b⟫ := by
  classical
  have hB : ∀ u ∈ Metric.closedBall c (radius p), ∀ v ∈ Metric.closedBall c (radius p),
      0 ≤ ⟪(a • fderiv ℝ F x) (u - v), u - v⟫ := by
    intro u _ v _
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg ha.le (deriv_inner_nonneg hreg x _)
  have hex : ∃ y ∈ Metric.closedBall c (radius p), ∀ v ∈ Metric.closedBall c (radius p),
      0 ≤ ⟪b + (a • fderiv ℝ F x) y + (1 : ℝ) • y, v - y⟫ :=
    CachedJacobianGeometry.affine_vi_exists b (isCompact_closedBall c _) (convex_closedBall c _)
      ⟨c, Metric.mem_closedBall_self (radius_pos hreg).le⟩ one_pos hB
  have he : affinePoint p c (a • fderiv ℝ F x) b = Classical.choose hex := by
    simp only [affinePoint, hex, ↓reduceDIte]
  rw [he]
  exact Classical.choose_spec hex


lemma qN_compare (hreg : Regular p F S) {a : ℝ} (ha : 0 ≤ a) {x y : p.E} {s : ℝ}
    (hs : Real.exp (p.M * ‖y - x‖) ≤ s) (v : p.E) :
    qN a (Hs F S y) v ≤ s * qN a (Hs F S x) v := by
  have h1 := hreg.stab x y v
  have hs1 : 1 ≤ s := (Real.one_le_exp (by have := hreg.M_pos; positivity)).trans hs
  have hq := hreg.psd x v
  change qf (Hs F S y) v ≤ Real.exp (p.M * ‖y - x‖) * qf (Hs F S x) v at h1
  unfold qN
  have h2 : qf (Hs F S y) v ≤ s * qf (Hs F S x) v :=
    h1.trans (mul_le_mul_of_nonneg_right hs hq)
  have h3 : ‖v‖ ^ 2 ≤ s * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

def newtonPoint (F : p.E → p.E) (a : ℝ) (w c x : p.E) : p.E :=
  affinePoint p c (a • fderiv ℝ F x) (a • F x - w - (a • fderiv ℝ F x) x)

lemma newton_contract (hreg : Regular p F S) {a : ℝ} (ha : 0 < a) {w c us ut : p.E}
    (hus : us ∈ Metric.closedBall c (radius p))
    (hvi : ∀ v ∈ Metric.closedBall c (radius p), 0 ≤ ⟪a • F us + us - w, v - us⟫)
    (hut : ut ∈ Metric.closedBall c (radius p)) :
    newtonPoint F a w c ut ∈ Metric.closedBall c (radius p) ∧
      qN a (Hs F S c) (newtonPoint F a w c ut - us) ≤ 1 / 4 * qN a (Hs F S c) (ut - us) := by
  obtain ⟨hy, hviy⟩ := affinePoint_spec hreg ha c ut (a • F ut - w - (a • fderiv ℝ F ut) ut)
  set y := newtonPoint F a w c ut with hy_def
  have hy' : y ∈ Metric.closedBall c (radius p) := hy
  refine ⟨hy', ?_⟩
  set e := ut - us with he
  set e' := y - us with he'
  have v1 := hviy us hus
  have v2 := hvi y hy'
  obtain ⟨ξ, hξ, hm⟩ := mvt_inner hreg us e e'
  have hue : us + e = ut := by rw [he]; abel
  rw [hue] at hm
  set q := us + ξ • e with hq
  have hkey : ⟪e + a • ((Hs F S q + S) e), e'⟫ +
      ⟪(e' - e) + a • ((Hs F S ut + S) (e' - e)), e'⟫ ≤ 0 := by
    have e1 : Hs F S q + S = fderiv ℝ F q := by unfold Hs; abel
    have e2 : Hs F S ut + S = fderiv ℝ F ut := by unfold Hs; abel
    rw [e1, e2]
    have hyv : y = us + e' := by rw [he']; abel
    have v1' : 0 ≤ ⟪a • F ut - w - (a • fderiv ℝ F ut) ut + (a • fderiv ℝ F ut) y + y,
        -e'⟫ := by
      have h0 : 0 ≤ ⟪a • F ut - w - (a • fderiv ℝ F ut) ut + (a • fderiv ℝ F ut) y +
          (1 : ℝ) • y, us - y⟫ := v1
      have h1 : us - y = -e' := by rw [he']; abel
      rw [one_smul, h1] at h0
      exact h0
    have v2' : 0 ≤ ⟪a • F us + us - w, e'⟫ := v2
    rw [inner_neg_right] at v1'
    have hX : a • F ut - w - (a • fderiv ℝ F ut) ut + (a • fderiv ℝ F ut) y + y =
        (a • F us + us - w) + a • (F ut - F us) +
          (e + a • (fderiv ℝ F ut) (e' - e) + (e' - e)) := by
      have hJ : (a • fderiv ℝ F ut) y - (a • fderiv ℝ F ut) ut =
          a • (fderiv ℝ F ut) (e' - e) := by
        rw [← map_sub, smul_apply]
        congr 2
        rw [he', he]; abel
      have hy2 : y = us + e' := hyv
      calc a • F ut - w - (a • fderiv ℝ F ut) ut + (a • fderiv ℝ F ut) y + y
          = a • F ut - w + ((a • fderiv ℝ F ut) y - (a • fderiv ℝ F ut) ut) + y := by abel
        _ = a • F ut - w + a • (fderiv ℝ F ut) (e' - e) + (us + e') := by rw [hJ, ← hy2]
        _ = _ := by rw [he]; module
    have expand : ⟪a • F ut - w - (a • fderiv ℝ F ut) ut + (a • fderiv ℝ F ut) y + y, e'⟫ =
        ⟪a • F us + us - w, e'⟫ + a * ⟪F ut - F us, e'⟫ +
          ⟪e + a • (fderiv ℝ F ut) (e' - e) + (e' - e), e'⟫ := by
      rw [hX, inner_add_left, inner_add_left, real_inner_smul_left]
    rw [expand, hm] at v1'
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at v1' v2' ⊢
    linarith
  have dist_q : ‖q - ut‖ ≤ 2 * radius p := by
    have h1 : q - ut = (ξ - 1) • e := by rw [hq, he]; module
    have hus' := hus; have hut' := hut
    rw [Metric.mem_closedBall, dist_eq_norm] at hus' hut'
    have h2 : ‖e‖ ≤ 2 * radius p := by
      calc ‖e‖ = ‖(ut - c) - (us - c)‖ := by rw [he]; congr 1; abel
        _ ≤ ‖ut - c‖ + ‖us - c‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hξ.2])]
    have : -(ξ - 1) ≤ 1 := by linarith [hξ.1]
    nlinarith [norm_nonneg e, hξ.2]
  set sq := Real.exp (p.M * ‖q - ut‖) with hsq
  have hsq_le : sq ≤ Real.exp (1 / 4) := by
    have := exp_le_of_dist hreg (m := 2) dist_q
    rw [show (2 : ℝ) / 8 = 1 / 4 by norm_num] at this
    exact this
  have hsq1 : 1 ≤ sq := Real.one_le_exp (by have := hreg.M_pos; positivity)
  have hb : ∀ v, |qf (Hs F S ut - Hs F S q) v| ≤ (sq - 1) * qf (Hs F S ut) v := by
    intro v
    have h1 : ∀ v, qf (Hs F S q) v ≤ sq * qf (Hs F S ut) v := fun v => hreg.stab ut q v
    have h2 : ∀ v, qf (Hs F S ut) v ≤ sq * qf (Hs F S q) v := by
      intro v
      have := hreg.stab q ut v
      rwa [norm_sub_rev] at this
    have := stab_diff hsq1 h1 h2 (fun v => hreg.psd ut v) v
    rw [qf_sub] at this ⊢
    rwa [abs_sub_comm] at this
  have hsa : ∀ u v, ⟪(Hs F S ut - Hs F S q) u, v⟫ = ⟪u, (Hs F S ut - Hs F S q) v⟫ := by
    intro u v
    have h1 : ⟪(Hs F S ut) u, v⟫ = ⟪u, (Hs F S ut) v⟫ := hreg.sa ut u v
    have h2 : ⟪(Hs F S q) u, v⟫ = ⟪u, (Hs F S q) v⟫ := hreg.sa q u v
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    rw [h1, h2]
  have hcore := newton_core ha.le hreg.skew hsa (fun v => hreg.psd ut v) hb hkey
  have hκ : sq - 1 ≤ 1 / 3 := by linarith [exp_quarter_le]
  have hκ0 : 0 ≤ sq - 1 := by linarith
  have hcu : ‖ut - c‖ ≤ 1 * radius p := by
    have := hut; rw [Metric.mem_closedBall, dist_eq_norm] at this; linarith
  have hcu' : ‖c - ut‖ ≤ 1 * radius p := by rw [norm_sub_rev]; exact hcu
  have hs8 := exp_le_of_dist hreg hcu
  have hs8' := exp_le_of_dist hreg hcu'
  have c1 := qN_compare hreg ha.le (x := ut) (y := c) hs8' e'
  have c2 := qN_compare hreg ha.le (x := c) (y := ut) hs8 e
  have hN0 : 0 ≤ qN a (Hs F S ut) e := by
    unfold qN; have := hreg.psd ut e; positivity
  have hNc0 : 0 ≤ qN a (Hs F S c) e := by
    unfold qN; have := hreg.psd c e; positivity
  have he8 : Real.exp (1 / 8) * Real.exp (1 / 8) = Real.exp (1 / 4) := by
    rw [← Real.exp_add]; norm_num
  have hk2 : (sq - 1) ^ 2 ≤ 1 / 9 := by nlinarith
  have hE8 : 0 ≤ Real.exp (1 / 8) := (Real.exp_pos _).le
  calc qN a (Hs F S c) e' ≤ Real.exp (1 / 8) * qN a (Hs F S ut) e' := c1
    _ ≤ Real.exp (1 / 8) * ((sq - 1) ^ 2 * qN a (Hs F S ut) e) :=
      mul_le_mul_of_nonneg_left hcore hE8
    _ ≤ Real.exp (1 / 8) * ((sq - 1) ^ 2 * (Real.exp (1 / 8) * qN a (Hs F S c) e)) := by
      apply mul_le_mul_of_nonneg_left _ hE8
      exact mul_le_mul_of_nonneg_left c2 (sq_nonneg _)
    _ = Real.exp (1 / 4) * (sq - 1) ^ 2 * qN a (Hs F S c) e := by rw [← he8]; ring
    _ ≤ (4 / 3) * (1 / 9) * qN a (Hs F S c) e := by
      apply mul_le_mul_of_nonneg_right _ hNc0
      exact mul_le_mul exp_quarter_le hk2 (sq_nonneg _) (by norm_num)
    _ ≤ 1 / 4 * qN a (Hs F S c) e := by nlinarith

def iter (F : p.E → p.E) (a : ℝ) (w c : p.E) : ℕ → p.E
  | 0 => c
  | n + 1 => newtonPoint F a w c (iter F a w c n)

lemma iter_spec (hreg : Regular p F S) {a : ℝ} (ha : 0 < a) {w c us : p.E}
    (hus : us ∈ Metric.closedBall c (radius p))
    (hvi : ∀ v ∈ Metric.closedBall c (radius p), 0 ≤ ⟪a • F us + us - w, v - us⟫) :
    ∀ n, iter F a w c n ∈ Metric.closedBall c (radius p) ∧
      qN a (Hs F S c) (iter F a w c n - us) ≤ (1 / 4) ^ n * qN a (Hs F S c) (c - us)
  | 0 => ⟨Metric.mem_closedBall_self (radius_pos hreg).le, by simp [iter]⟩
  | n + 1 => by
    obtain ⟨hn, hq⟩ := iter_spec hreg ha hus hvi n
    obtain ⟨h1, h2⟩ := newton_contract hreg ha hus hvi hn
    refine ⟨h1, ?_⟩
    calc qN a (Hs F S c) (iter F a w c (n + 1) - us) ≤ 1 / 4 * qN a (Hs F S c) (iter F a w c n - us) := h2
      _ ≤ 1 / 4 * ((1 / 4) ^ n * qN a (Hs F S c) (c - us)) := by gcongr
      _ = _ := by ring

lemma initial_qN (hreg : Regular p F S) {a : ℝ} (ha : 0 ≤ a) {c us : p.E}
    (hus : us ∈ Metric.closedBall c (radius p)) :
    qN a (Hs F S c) (c - us) ≤ (1 + a * ‖fderiv ℝ F c‖) * radius p ^ 2 := by
  have hd : ‖c - us‖ ≤ radius p := by
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hus; exact hus
  have h1 := qf_Hs_le hreg c (c - us)
  have h2 : ‖c - us‖ ^ 2 ≤ radius p ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  unfold qN
  have h3 := mul_le_mul_of_nonneg_left h1 ha
  have h4 : a * (‖fderiv ℝ F c‖ * ‖c - us‖ ^ 2) ≤ a * (‖fderiv ℝ F c‖ * radius p ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ ha
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  nlinarith

lemma norm_sq_le_qN (hreg : Regular p F S) {a : ℝ} (ha : 0 ≤ a) (x v : p.E) :
    ‖v‖ ^ 2 ≤ qN a (Hs F S x) v := by
  have h : 0 ≤ qf (Hs F S x) v := hreg.psd x v
  unfold qN; nlinarith [mul_nonneg ha h]


lemma pow_log2_gt (n : ℕ) : n < 2 * 2 ^ Nat.log2 n := by
  rw [Nat.log2_eq_log_two, ← pow_succ']
  exact Nat.lt_pow_succ_log_self (by norm_num) n

lemma newtonCount_pow (k : ℕ) (a Γ : ℝ) (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) :
    32 * ((k : ℝ) + 1) ^ 2 * (1 + 4 * a * Γ) ^ 2 ≤ 2 ^ newtonCount k a Γ := by
  set m := ⌈1 + 4 * a * Γ⌉₊ with hm
  have h1 := pow_log2_gt (k + 1)
  have h2 := pow_log2_gt m
  have hm1 : 1 + 4 * a * Γ ≤ (m : ℝ) := Nat.le_ceil _
  have hx0 : 0 ≤ 1 + 4 * a * Γ := by positivity
  have h1r : ((k : ℝ) + 1) ≤ 2 * 2 ^ Nat.log2 (k + 1) := by exact_mod_cast h1.le
  have h2r : (m : ℝ) ≤ 2 * 2 ^ Nat.log2 m := by exact_mod_cast h2.le
  have e : (2 : ℝ) ^ newtonCount k a Γ =
      2 ^ 9 * ((2 : ℝ) ^ Nat.log2 (k + 1)) ^ 2 * ((2 : ℝ) ^ Nat.log2 m) ^ 2 := by
    unfold newtonCount; rw [← hm]; ring
  rw [e]
  have hk0 : 0 ≤ (k : ℝ) + 1 := by positivity
  have a1 := pow_le_pow_left₀ hk0 h1r 2
  have a2 := pow_le_pow_left₀ hx0 (hm1.trans h2r) 2
  have hp1 : (0 : ℝ) ≤ ((2 : ℝ) ^ Nat.log2 (k + 1)) ^ 2 := by positivity
  have hp2 : (0 : ℝ) ≤ ((2 : ℝ) ^ Nat.log2 m) ^ 2 := by positivity
  nlinarith [mul_le_mul a1 a2 (sq_nonneg _) (by positivity)]

lemma iter_accuracy (hreg : Regular p F S) {a : ℝ} (ha : 0 < a) {w c us : p.E}
    (hus : us ∈ Metric.closedBall c (radius p))
    (hvi : ∀ v ∈ Metric.closedBall c (radius p), 0 ≤ ⟪a • F us + us - w, v - us⟫) (k : ℕ) :
    ‖iter F a w c (newtonCount k a ‖fderiv ℝ F c‖) - us‖ ≤
      tolerance p k / (1 + 4 * a * ‖fderiv ℝ F c‖) := by
  set Γ := ‖fderiv ℝ F c‖ with hΓ
  set n := newtonCount k a Γ
  obtain ⟨-, hq⟩ := iter_spec hreg ha hus hvi n
  have h0 := initial_qN hreg ha.le hus
  have h1 := norm_sq_le_qN hreg ha.le c (iter F a w c n - us)
  have hpow := newtonCount_pow k a Γ ha.le (norm_nonneg _)
  have hr := radius_pos hreg
  have hX : 0 < 1 + 4 * a * Γ := by positivity
  set X := 1 + 4 * a * Γ with hXdef
  have hY : 1 + a * Γ ≤ X := by rw [hXdef]; nlinarith [mul_nonneg ha.le (norm_nonneg (fderiv ℝ F c))]
  have h4 : ((1 : ℝ) / 4) ^ n = 1 / (2 ^ n) ^ 2 := by
    rw [one_div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hsq : ‖iter F a w c n - us‖ ^ 2 ≤ X * radius p ^ 2 / (2 ^ n) ^ 2 := by
    calc _ ≤ (1 / 4) ^ n * qN a (Hs F S c) (c - us) := h1.trans hq
      _ ≤ (1 / 4) ^ n * ((1 + a * Γ) * radius p ^ 2) := by gcongr
      _ ≤ (1 / 4) ^ n * (X * radius p ^ 2) := by gcongr
      _ = X * radius p ^ 2 / (2 ^ n) ^ 2 := by rw [h4]; ring
  have htarget : X * radius p ^ 2 / (2 ^ n) ^ 2 ≤ (tolerance p k / X) ^ 2 := by
    have h2n : (0 : ℝ) < (2 ^ n) ^ 2 := by positivity
    have hp2 := pow_le_pow_left₀ (by positivity) hpow 2
    have hX1 : 1 ≤ X := by rw [hXdef]; nlinarith [mul_nonneg ha.le (norm_nonneg (fderiv ℝ F c))]
    have hX34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
    have hk0 : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by positivity
    have hA0 : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 * X ^ 3 := by positivity
    have key : 144 * ((k : ℝ) + 1) ^ 4 * X ^ 3 ≤ (2 ^ n) ^ 2 := by
      calc 144 * ((k : ℝ) + 1) ^ 4 * X ^ 3 ≤ (32 * ((k : ℝ) + 1) ^ 2 * X ^ 2) ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left hX34 hk0]
        _ ≤ _ := hp2
    have e : (tolerance p k / X) ^ 2 = radius p ^ 2 / (144 * ((k : ℝ) + 1) ^ 4 * X ^ 2) := by
      unfold tolerance
      rw [div_pow, div_pow, div_div]
      congr 1
      ring
    rw [e, div_le_div_iff₀ h2n (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ radius p ^ 2)]
  have hfin := hsq.trans htarget
  have hnn : 0 ≤ tolerance p k / X := by unfold tolerance; positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn (by norm_num)).mp hfin

lemma certificate_bound (hreg : Regular p F S) {a : ℝ} (ha : 0 < a) {w c us x : p.E}
    (hus : ‖us - c‖ ≤ radius p) (hx : ‖x - c‖ ≤ radius p) (hzero : a • F us + us - w = 0) :
    ‖a • F x + x - w‖ ≤ (1 + 4 * a * ‖fderiv ℝ F c‖) * ‖x - us‖ := by
  have e : a • F x + x - w = a • (F x - F us) + (x - us) := by
    have h : a • F x + x - w = a • (F x - F us) + (x - us) + (a • F us + us - w) := by module
    rw [h, hzero, add_zero]
  rw [e]
  calc _ ≤ ‖a • (F x - F us)‖ + ‖x - us‖ := norm_add_le _ _
    _ = a * ‖F x - F us‖ + ‖x - us‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    _ ≤ a * (4 * ‖fderiv ℝ F c‖ * ‖x - us‖) + ‖x - us‖ := by
      gcongr; exact lipschitz_ball hreg hx hus
    _ = _ := by ring

end

end LongTails.Proofs.BallAnchoredInner
