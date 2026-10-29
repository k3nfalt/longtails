import LongTails.Setups.CohypomonotoneNewton
import LongTails.Proofs.RiverValleyCalculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp

open scoped RealInnerProductSpace
open Filter Topology

namespace LongTails.Proofs.CohypomonotoneNewtonGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma expansive_derivative {T : E → E} {D : E →L[ℝ] E} {x : E}
    (hT : HasFDerivAt T D x)
    (hexp : ∀ y, ‖y - x‖ ≤ ‖T y - T x‖) (v : E) : ‖v‖ ≤ ‖D v‖ := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ => T (x + t • v)) (D v) 0 := by
    have hx : HasFDerivAt T D ((fun t : ℝ => x + t • v) 0) := by simpa using hT
    exact hx.comp_hasDerivAt (0 : ℝ) hline
  have hl := hd.tendsto_slope_zero_right.norm
  refine ge_of_tendsto hl ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [zero_add, zero_smul, add_zero]
  have hb := hexp (x + t • v)
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le] at hb
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  have hp := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht.le)
  simpa [← mul_assoc, ht.ne'] using hp

lemma shifted_norm_lower {u v : E} {ρ γ : ℝ} (hγ : 2 * ρ ≤ γ) (hγ0 : 0 ≤ γ)
    (h : -ρ * ‖v‖ ^ 2 ≤ ⟪v, u⟫) : ‖u‖ ≤ ‖u + γ • v‖ := by
  have hsq : ‖u‖ ^ 2 ≤ ‖u + γ • v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0,
      real_inner_smul_right, real_inner_comm]
    nlinarith [mul_le_mul_of_nonneg_left h hγ0,
      mul_nonneg hγ0 (mul_nonneg (sub_nonneg.mpr hγ) (sq_nonneg ‖v‖))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

lemma shifted_expansive {F : E → E} {ρ γ : ℝ} (hγ : 2 * ρ ≤ γ) (hγ0 : 0 ≤ γ)
    (h : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) (x y : E) :
    ‖x - y‖ ≤ ‖(x + γ • F x) - (y + γ • F y)‖ := by
  have he : (x + γ • F x) - (y + γ • F y) = (x - y) + γ • (F x - F y) := by
    rw [smul_sub]
    abel
  rw [he]
  exact shifted_norm_lower hγ hγ0 (h x y)

lemma shifted_cocoercive {F : E → E} {ρ γ : ℝ}
    (h : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) (x y : E) :
    (γ - ρ) * ‖F x - F y‖ ^ 2 ≤
      ⟪F x - F y, (x + γ • F x) - (y + γ • F y)⟫ := by
  have he : (x + γ • F x) - (y + γ • F y) = (x - y) + γ • (F x - F y) := by
    rw [smul_sub]
    abel
  rw [he, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  linarith [h x y]

lemma damped_newton_residual {T : E → E} {D : E → E →L[ℝ] E} {M t : ℝ}
    (hT : ∀ x, HasFDerivAt T (D x) x) (hM : 0 ≤ M)
    (hD : ∀ x y, ‖D x - D y‖ ≤ M * ‖x - y‖)
    (x w v : E) (hv : D x v = -(T x - w)) (hvn : ‖v‖ ≤ ‖T x - w‖)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hsmall : M * t * ‖T x - w‖ ≤ 1 / 2) :
    ‖T (x + t • v) - w‖ ≤ (1 - t / 2) * ‖T x - w‖ := by
  have hrem := OracleTemplate.RiverValley.taylor_lip hT hM hD x (t • v)
  have he : T (x + t • v) - w =
      (1 - t) • (T x - w) + (T (x + t • v) - T x - D x (t • v)) := by
    rw [map_smul, hv, smul_neg, sub_smul, one_smul]
    abel
  have hmain : ‖T (x + t • v) - w‖ ≤
      (1 - t) * ‖T x - w‖ + M * t ^ 2 * ‖v‖ ^ 2 := by
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
    have hr := hrem
    rw [norm_smul, Real.norm_of_nonneg ht, mul_pow] at hr
    nlinarith only [hr]
  have hs : ‖v‖ ^ 2 ≤ ‖T x - w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvn 2
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hM (sq_nonneg t))
  have hb := mul_le_mul_of_nonneg_right hsmall (mul_nonneg ht (norm_nonneg (T x - w)))
  nlinarith only [hmain, hm, hb]

lemma initial_newton_residual {T : E → E} {D : E → E →L[ℝ] E} {M R : ℝ}
    (hT : ∀ x, HasFDerivAt T (D x) x) (hM : 0 ≤ M)
    (hD : ∀ x y, ‖D x - D y‖ ≤ M * ‖x - y‖)
    (x root v : E) (hroot : T root = root) (hR : ‖x - root‖ ≤ R)
    (hlower : ∀ u, ‖u‖ ≤ ‖D x u‖) (hv : D x v = -(T x - x)) :
    ‖T (x + v) - x‖ ≤ M * (2 * R + M * R ^ 2) ^ 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hrem := OracleTemplate.RiverValley.taylor_lip hT hM hD x (root - x)
  rw [add_sub_cancel, hroot, norm_sub_rev root x] at hrem
  have hs := pow_le_pow_left₀ (norm_nonneg (x - root)) hR 2
  have hrem' : ‖root - T x - D x (root - x)‖ ≤ M * R ^ 2 :=
    hrem.trans (mul_le_mul_of_nonneg_left hs hM)
  have he : D x (v + (x - root)) =
      (x - root) + (root - T x - D x (root - x)) := by
    simp only [map_add, map_sub, hv]
    abel
  have hb : ‖v + (x - root)‖ ≤ R + M * R ^ 2 := by
    calc
      ‖v + (x - root)‖ ≤ ‖D x (v + (x - root))‖ := hlower _
      _ = ‖(x - root) + (root - T x - D x (root - x))‖ := by rw [he]
      _ ≤ ‖x - root‖ + ‖root - T x - D x (root - x)‖ := norm_add_le _ _
      _ ≤ R + M * R ^ 2 := add_le_add hR hrem'
  have hvn : ‖v‖ ≤ 2 * R + M * R ^ 2 := by
    have ht := norm_sub_le (v + (x - root)) (x - root)
    rw [add_sub_cancel_right] at ht
    linarith
  have hr := OracleTemplate.RiverValley.taylor_lip hT hM hD x v
  have her : T (x + v) - T x - D x v = T (x + v) - x := by rw [hv]; abel
  rw [her] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg v) hvn 2) hM)

lemma affine_model_displacement {G : E → E} {J : E → E →L[ℝ] E}
    {m n v w c : E} {a H : ℝ} (ha : 0 ≤ a)
    (hmono : ∀ z, 0 ≤ ⟪J n z, z⟫)
    (hrem : ‖G m - G n - J n (m - n)‖ ≤ H * ‖m - n‖ ^ 2)
    (hJ : ‖J m - J n‖ ≤ H * ‖m - n‖)
    (hv : v + a • (G m + J m (v - m)) = c)
    (hw : w + a • (G n + J n (w - n)) = c) :
    ‖w - v‖ ≤ a * H * ‖m - n‖ * (‖v - m‖ + ‖m - n‖) := by
  have hid : (G m + J m (v - m)) - (G n + J n (v - n)) =
      (G m - G n - J n (m - n)) + (J m - J n) (v - m) := by
    simp only [map_sub, sub_apply]
    abel
  have hb : ‖(G m + J m (v - m)) - (G n + J n (v - n))‖ ≤
      H * ‖m - n‖ * (‖v - m‖ + ‖m - n‖) := by
    rw [hid]
    have hop := (J m - J n).le_opNorm (v - m)
    have hp := mul_le_mul_of_nonneg_right hJ (norm_nonneg (v - m))
    have ht := norm_add_le (G m - G n - J n (m - n)) ((J m - J n) (v - m))
    nlinarith only [hop, hp, ht, hrem]
  have he : (w - v) + a • J n (w - v) =
      a • ((G m + J m (v - m)) - (G n + J n (v - n))) := by
    have hh : w + a • (G n + J n (w - n)) = v + a • (G m + J m (v - m)) :=
      hw.trans hv.symm
    simp only [map_sub, smul_add, smul_sub] at hh ⊢
    linear_combination (norm := module) hh
  have hlow := shifted_norm_lower (ρ := 0) (γ := a) (by simpa using ha) ha
    (u := w - v) (v := J n (w - v)) (by simpa using hmono (w - v))
  rw [he, norm_smul, Real.norm_of_nonneg ha] at hlow
  have hp := mul_le_mul_of_nonneg_left hb ha
  nlinarith only [hlow, hp]

lemma initial_trust_region_residual {T : E → E} {D : E → E →L[ℝ] E} {M R : ℝ}
    (hT : ∀ x, HasFDerivAt T (D x) x) (hM : 0 ≤ M)
    (hD : ∀ x y, ‖D x - D y‖ ≤ M * ‖x - y‖)
    (x root v : E) (hroot : T root = root) (hR : ‖root - x‖ ≤ R)
    (hv : ‖v‖ ≤ R)
    (hmin : ∀ d, ‖d‖ ≤ R → ‖T x - x + D x v‖ ≤ ‖T x - x + D x d‖) :
    ‖T (x + v) - x‖ ≤ R + 2 * M * R ^ 2 := by
  have hrem := OracleTemplate.RiverValley.taylor_lip hT hM hD x (root - x)
  rw [add_sub_cancel, hroot] at hrem
  have hs := pow_le_pow_left₀ (norm_nonneg (root - x)) hR 2
  have hrem' : ‖root - T x - D x (root - x)‖ ≤ M * R ^ 2 :=
    hrem.trans (mul_le_mul_of_nonneg_left hs hM)
  have he : T x - x + D x (root - x) =
      (root - x) - (root - T x - D x (root - x)) := by abel
  have hb : ‖T x - x + D x v‖ ≤ R + M * R ^ 2 := by
    calc
      ‖T x - x + D x v‖ ≤ ‖T x - x + D x (root - x)‖ := hmin _ hR
      _ = ‖(root - x) - (root - T x - D x (root - x))‖ := by rw [he]
      _ ≤ ‖root - x‖ + ‖root - T x - D x (root - x)‖ := norm_sub_le _ _
      _ ≤ R + M * R ^ 2 := add_le_add hR hrem'
  have hr := OracleTemplate.RiverValley.taylor_lip hT hM hD x v
  have hsv := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hsv hM)
  have he' : T (x + v) - x = (T x - x + D x v) + (T (x + v) - T x - D x v) := by
    abel
  rw [he']
  have ht := norm_add_le (T x - x + D x v) (T (x + v) - T x - D x v)
  linarith

omit [InnerProductSpace ℝ E] in
lemma displacement_comparison (m n w z : E) :
    ‖w - n‖ ≤ ‖z - m‖ + ‖z - w‖ + ‖n - m‖ := by
  have h1 := norm_sub_le (w - z) (n - z)
  have h2 := norm_sub_le (n - m) (z - m)
  have he1 : (w - z) - (n - z) = w - n := by abel
  have he2 : (n - m) - (z - m) = n - z := by abel
  rw [he1, norm_sub_rev w z] at h1
  rw [he2] at h2
  linarith

lemma inexact_affine_residual {G : E → E} {J : E →L[ℝ] E}
    {a L H e : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L) (he : 0 ≤ e)
    (c m n w z : E)
    (hmodel : w + a • (G n + J (w - n)) = c)
    (hrem : ‖G w - G n - J (w - n)‖ ≤ H * ‖w - n‖ ^ 2)
    (hlip : ‖G z - G w‖ ≤ L * ‖z - w‖)
    (hmerit : a * H * ‖w - n‖ ≤ 1 / 32)
    (hcenter : ‖n - m‖ ≤ e / 64)
    (hendpoint : (1 + a * L) * ‖z - w‖ ≤ e / 64) :
    ‖z + a • G z - c‖ ≤ ‖z - m‖ / 4 + e := by
  have hid : z + a • G z - c = (z - w) + a • (G z - G w) +
      a • (G w - G n - J (w - n)) := by
    rw [← hmodel, smul_sub, smul_sub]
    module
  have hmain : ‖z + a • G z - c‖ ≤
      (1 + a * L) * ‖z - w‖ + a * H * ‖w - n‖ ^ 2 := by
    rw [hid]
    have ht := (norm_add_le ((z - w) + a • (G z - G w))
      (a • (G w - G n - J (w - n)))).trans
      (add_le_add (norm_add_le (z - w) (a • (G z - G w))) le_rfl)
    simp only [norm_smul, Real.norm_of_nonneg ha] at ht
    have hp := mul_le_mul_of_nonneg_left hrem ha
    have hq := mul_le_mul_of_nonneg_left hlip ha
    nlinarith only [ht, hp, hq]
  have hmd := mul_le_mul_of_nonneg_right hmerit (norm_nonneg (w - n))
  have hdelta : ‖z - w‖ ≤ e / 64 := by
    have hp := mul_nonneg (mul_nonneg ha hL) (norm_nonneg (z - w))
    nlinarith only [hendpoint, hp]
  have hd := displacement_comparison m n w z
  nlinarith [norm_nonneg (z - m)]

omit [InnerProductSpace ℝ E] in
lemma inexact_large_step {a H : ℝ} (haH : 0 ≤ a * H) (m n w z : E)
    (hmerit : 1 / 64 ≤ a * H * ‖w - n‖)
    (hcenter : a * H * ‖n - m‖ ≤ 1 / 4096)
    (hendpoint : a * H * ‖z - w‖ ≤ 1 / 4096) :
    1 / 128 ≤ a * H * ‖z - m‖ := by
  have hh := mul_le_mul_of_nonneg_left (displacement_comparison m n w z) haH
  nlinarith only [hh, hmerit, hcenter, hendpoint]

omit [InnerProductSpace ℝ E] in
lemma merit_perturbation {b κ : ℝ} (hb : 0 ≤ b) (hκ : 0 ≤ κ) (m n v w : E)
    (hpert : ‖w - v‖ ≤ b * ‖n - m‖ * (‖v - m‖ + ‖n - m‖))
    (hsmall : b * ‖n - m‖ ≤ κ) :
    |b * ‖w - n‖ - b * ‖v - m‖| ≤ κ * (b * ‖v - m‖) + κ + κ ^ 2 := by
  have hdiff : |‖w - n‖ - ‖v - m‖| ≤ ‖w - v‖ + ‖n - m‖ := by
    have he : (w - n) - (v - m) = (w - v) - (n - m) := by abel
    exact (abs_norm_sub_norm_le (w - n) (v - m)).trans
      (by rw [he]; exact norm_sub_le _ _)
  have h1 := mul_le_mul_of_nonneg_left hdiff hb
  have h2 := mul_le_mul_of_nonneg_left hpert hb
  have h3 := mul_le_mul hsmall (add_le_add (le_refl (b * ‖v - m‖)) hsmall)
    (add_nonneg (mul_nonneg hb (norm_nonneg _)) (mul_nonneg hb (norm_nonneg _))) hκ
  rw [← mul_sub, abs_mul, abs_of_nonneg hb]
  nlinarith only [h1, h2, h3, hsmall]

lemma affine_resolvent_stability {P Q : E → E} (J : E →L[ℝ] E)
    {a b : ℝ} (ha : 0 ≤ a) (hmono : ∀ u, 0 ≤ ⟪J u, u⟫)
    (w v c d : E) (hP : P w - P v = J (w - v))
    (hw : w + a • P w = c) (hv : v + b • Q v = d) :
    ‖w - v‖ ≤ ‖c - d‖ + |a - b| * ‖Q v‖ + a * ‖Q v - P v‖ := by
  have hid : (w - v) + a • J (w - v) =
      (c - d) + (b - a) • Q v + a • (Q v - P v) := by
    rw [← hP, ← hw, ← hv, sub_smul, smul_sub]
    module
  have hl := shifted_norm_lower (ρ := 0) (γ := a) (by simpa using ha) ha
    (u := w - v) (v := J (w - v)) (by simpa using hmono (w - v))
  rw [hid] at hl
  have ht := (norm_add_le ((c - d) + (b - a) • Q v) (a • (Q v - P v))).trans
    (add_le_add (norm_add_le (c - d) ((b - a) • Q v)) le_rfl)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_sub_comm b a] at ht
  exact hl.trans ht

lemma terminal_residual_estimate {G : E → E} (J : E →L[ℝ] E)
    {a H L : ℝ} (ha : 0 ≤ a) (m n w z c : E)
    (hw : w + a • (G n + J (w - n)) = c)
    (hrem : ‖G w - G n - J (w - n)‖ ≤ H * ‖w - n‖ ^ 2)
    (hlip : ‖G z - G w‖ ≤ L * ‖z - w‖) :
    a * ‖G z‖ ≤ ‖c - m‖ + ‖n - m‖ + ‖w - n‖ +
      a * H * ‖w - n‖ ^ 2 + a * L * ‖z - w‖ := by
  have hid : a • G z = (c - w) + a • (G w - G n - J (w - n)) +
      a • (G z - G w) := by rw [← hw]; module
  have hn := norm_add_le ((c - w) + a • (G w - G n - J (w - n)))
    (a • (G z - G w))
  have hn' := norm_add_le (c - w) (a • (G w - G n - J (w - n)))
  have hc : ‖c - w‖ ≤ ‖c - m‖ + ‖n - m‖ + ‖w - n‖ := by
    have he : c - w = ((c - m) - (n - m)) - (w - n) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hr := mul_le_mul_of_nonneg_left hrem ha
  have hl := mul_le_mul_of_nonneg_left hlip ha
  rw [← hid] at hn
  simp only [norm_smul, Real.norm_of_nonneg ha] at hn hn'
  nlinarith only [hn, hn', hc, hr, hl]

lemma terminal_scalar_bound {a H R s eta delta g : ℝ} (ha : 0 < a) (hH : 0 < H)
    (hR : 0 ≤ R) (hs : 0 ≤ s) (hmerit : a * H * s ≤ 1 / 32)
    (heta : eta ≤ R / 64) (hdelta : delta ≤ R / 64)
    (hg : a * g ≤ 4 * R + eta + s + a * H * s ^ 2 + delta) :
    g ≤ 5 * R / a + 5 / (64 * H * a ^ 2) := by
  have hprod := mul_le_mul_of_nonneg_right hmerit hs
  have hsb : s ≤ 1 / (32 * a * H) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * a * H)).mpr
    nlinarith only [hmerit]
  have he : a * (5 * R / a + 5 / (64 * H * a ^ 2)) =
      5 * R + 5 / (64 * H * a) := by field_simp
  apply (mul_le_mul_iff_right₀ ha).mp
  rw [he]
  have hf : 33 / 32 * (1 / (32 * a * H)) ≤ 5 / (64 * H * a) := by
    field_simp
    norm_num
  nlinarith only [hg, heta, hdelta, hprod, hsb, hf, hR]

lemma affine_models_difference {G : E → E} {J : E → E →L[ℝ] E}
    {L H : ℝ} (m n v : E)
    (hG : ‖G n - G m‖ ≤ L * ‖n - m‖) (hJ : ‖J m‖ ≤ L)
    (hJL : ‖J n - J m‖ ≤ H * ‖n - m‖) :
    ‖(G n + J n (v - n)) - (G m + J m (v - m))‖ ≤
      (2 * L + H * ‖v - n‖) * ‖n - m‖ := by
  have he : (G n + J n (v - n)) - (G m + J m (v - m)) =
      (G n - G m) + J m (m - n) + (J n - J m) (v - n) := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  have ht := (norm_add_le ((G n - G m) + J m (m - n)) ((J n - J m) (v - n))).trans
    (add_le_add (norm_add_le (G n - G m) (J m (m - n))) le_rfl)
  have h1 := (J m).le_opNorm (m - n)
  have h2 := mul_le_mul_of_nonneg_right hJ (norm_nonneg (m - n))
  have h3 := (J n - J m).le_opNorm (v - n)
  have h4 := mul_le_mul_of_nonneg_right hJL (norm_nonneg (v - n))
  rw [norm_sub_rev m n] at h1 h2
  nlinarith only [ht, hG, h1, h2, h3, h4]

lemma affine_path_lipschitz {G : E → E} {J : E → E →L[ℝ] E}
    {a b amax L H Kc Km B D : ℝ} (ha : 0 ≤ a) (hamax : a ≤ amax)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hKm : 0 ≤ Km) (hD : 0 ≤ D)
    (m n w v c d : E) (hmono : ∀ u, 0 ≤ ⟪J m u, u⟫)
    (hw : w + a • (G m + J m (w - m)) = c)
    (hv : v + b • (G n + J n (v - n)) = d)
    (hG : ‖G n - G m‖ ≤ L * ‖n - m‖)
    (hJm : ‖J m‖ ≤ L) (hJn : ‖J n‖ ≤ L)
    (hJL : ‖J n - J m‖ ≤ H * ‖n - m‖)
    (hGn : ‖G n‖ ≤ B) (hvn : ‖v - n‖ ≤ D)
    (hc : ‖c - d‖ ≤ Kc * |a - b|) (hm : ‖n - m‖ ≤ Km * |a - b|) :
    ‖w - v‖ ≤ (Kc + B + L * D + amax * (2 * L + H * D) * Km) * |a - b| := by
  have hh := affine_resolvent_stability (P := fun x => G m + J m (x - m))
    (Q := fun x => G n + J n (x - n)) (J m) ha hmono w v c d
    (by simp only [map_sub]; abel) hw hv
  have hq : ‖G n + J n (v - n)‖ ≤ B + L * D := by
    have ht := norm_add_le (G n) (J n (v - n))
    have hop := (J n).le_opNorm (v - n)
    have hp := mul_le_mul hJn hvn (norm_nonneg _) hL
    linarith
  have hp := affine_models_difference m n v hG hJm hJL
  have hdiff : ‖(G n + J n (v - n)) - (G m + J m (v - m))‖ ≤
      (2 * L + H * D) * Km * |a - b| := by
    have h1 := mul_le_mul_of_nonneg_left hvn hH
    have h2 := mul_le_mul (add_le_add le_rfl h1) hm (norm_nonneg _)
      (by positivity : 0 ≤ 2 * L + H * D)
    nlinarith only [hp, h2]
  have hq' := mul_le_mul_of_nonneg_left hq (abs_nonneg (a - b))
  have hdiff' := mul_le_mul_of_nonneg_left hdiff ha
  have hmax := mul_le_mul_of_nonneg_right hamax
    (by positivity : 0 ≤ (2 * L + H * D) * Km * |a - b|)
  nlinarith only [hh, hc, hq', hdiff', hmax]

omit [InnerProductSpace ℝ E] in
lemma merit_path_lipschitz {a b amax H D Kv Km : ℝ}
    (ha : 0 ≤ a) (hamax : a ≤ amax) (hH : 0 ≤ H) (hKv : 0 ≤ Kv) (hKm : 0 ≤ Km)
    (w v m n : E) (hvn : ‖v - n‖ ≤ D)
    (hwv : ‖w - v‖ ≤ Kv * |a - b|) (hmn : ‖m - n‖ ≤ Km * |a - b|) :
    |a * H * ‖w - m‖ - b * H * ‖v - n‖| ≤
      H * (D + amax * (Kv + Km)) * |a - b| := by
  have hdiff : |‖w - m‖ - ‖v - n‖| ≤ (Kv + Km) * |a - b| := by
    have he : (w - m) - (v - n) = (w - v) - (m - n) := by abel
    have hh := abs_norm_sub_norm_le (w - m) (v - n)
    rw [he] at hh
    have ht := norm_sub_le (w - v) (m - n)
    nlinarith only [hh, ht, hwv, hmn]
  have he : a * H * ‖w - m‖ - b * H * ‖v - n‖ =
      H * (a * (‖w - m‖ - ‖v - n‖) + (a - b) * ‖v - n‖) := by ring
  rw [he, abs_mul, abs_of_nonneg hH]
  have ht := abs_add_le (a * (‖w - m‖ - ‖v - n‖)) ((a - b) * ‖v - n‖)
  rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg (norm_nonneg _)] at ht
  have hp := mul_le_mul_of_nonneg_left hdiff ha
  have hq := mul_le_mul_of_nonneg_left hvn (abs_nonneg (a - b))
  have hm := mul_le_mul_of_nonneg_right hamax
    (by positivity : 0 ≤ (Kv + Km) * |a - b|)
  have hb : |a * (‖w - m‖ - ‖v - n‖) + (a - b) * ‖v - n‖| ≤
      (D + amax * (Kv + Km)) * |a - b| := by nlinarith only [ht, hp, hq, hm]
  have hh := mul_le_mul_of_nonneg_left hb hH
  nlinarith only [hh]

lemma merit_low_exact {phi approx : ℝ}
    (herr : |approx - phi| ≤ phi / 4096 + 1 / 4096 + 1 / 4096 ^ 2)
    (hlow : approx < 1 / 64) : phi < 1 / 60 := by
  have hh := (abs_le.mp herr).1
  linarith

lemma merit_high_exact {phi approx : ℝ}
    (herr : |approx - phi| ≤ phi / 4096 + 1 / 4096 + 1 / 4096 ^ 2)
    (hhigh : 1 / 32 < approx) : 1 / 33 < phi := by
  have hh := (abs_le.mp herr).2
  linarith

lemma merit_safe_floor {phi approx : ℝ}
    (herr : |approx - phi| ≤ phi / 4096 + 1 / 4096 + 1 / 4096 ^ 2)
    (hphi : phi ≤ 10 / 128 ^ 2) : approx < 1 / 64 := by
  have hh := (abs_le.mp herr).2
  linarith

lemma merit_bracket_width {phiLow phiHigh approxLow approxHigh L lo hi : ℝ}
    (hlow : approxLow < 1 / 64) (hhigh : 1 / 32 < approxHigh)
    (herrLow : |approxLow - phiLow| ≤ phiLow / 4096 + 1 / 4096 + 1 / 4096 ^ 2)
    (herrHigh : |approxHigh - phiHigh| ≤ phiHigh / 4096 + 1 / 4096 + 1 / 4096 ^ 2)
    (hlip : |phiHigh - phiLow| ≤ L * (hi - lo)) :
    1 / 100 < L * (hi - lo) := by
  have h1 := merit_low_exact herrLow hlow
  have h2 := merit_high_exact herrHigh hhigh
  have h3 := (abs_le.mp hlip).2
  linarith

lemma fraction_difference_bound {A a b : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a / (A + a) - b / (A + b)| ≤ |a - b| / A := by
  have hAa : 0 < A + a := by positivity
  have hAb : 0 < A + b := by positivity
  have hid : a / (A + a) - b / (A + b) = (A / ((A + a) * (A + b))) * (a - b) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ A / ((A + a) * (A + b)))]
  have hcoef : A / ((A + a) * (A + b)) ≤ 1 / A := by
    apply (div_le_div_iff₀ (mul_pos hAa hAb) hA).mpr
    nlinarith [mul_nonneg ha hb, mul_nonneg hA.le ha, mul_nonneg hA.le hb]
  have hh := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (a - b))
  convert hh using 1; ring

lemma approximate_merit_error {G : E → E} {J : E → E →L[ℝ] E} {a H : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hG : ∀ x, HasFDerivAt G (J x) x)
    (hJL : ∀ x y, ‖J x - J y‖ ≤ H * ‖x - y‖)
    (m n v w c : E) (hmono : ∀ u, 0 ≤ ⟪J n u, u⟫)
    (hv : v + a • (G m + J m (v - m)) = c)
    (hw : w + a • (G n + J n (w - n)) = c)
    (hcenter : a * H * ‖n - m‖ ≤ 1 / 4096) :
    |a * H * ‖w - n‖ - a * H * ‖v - m‖| ≤
      (a * H * ‖v - m‖) / 4096 + 1 / 4096 + 1 / 4096 ^ 2 := by
  have hrem := OracleTemplate.RiverValley.taylor_lip hG hH hJL n (m - n)
  rw [add_sub_cancel] at hrem
  have hpert := affine_model_displacement ha hmono hrem (hJL m n) hv hw
  rw [norm_sub_rev m n] at hpert
  have hh := merit_perturbation (mul_nonneg ha hH) (by norm_num : (0 : ℝ) ≤ 1 / 4096)
    m n v w hpert hcenter
  convert hh using 1; ring

end LongTails.Proofs.CohypomonotoneNewtonGeometry
