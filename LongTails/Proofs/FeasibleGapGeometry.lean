import LongTails.Proofs.FrankWolfeDescent
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FeasibleGapGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma positive_map_square {H : E →L[ℝ] E} {M : ℝ}
    (hH : H.IsPositive) (hM : 0 < M) (hbound : ‖H‖ ≤ M) (v : E) :
    ‖H v‖ ^ 2 ≤ M * ⟪H v, v⟫ := by
  have hp := hH.inner_nonneg_left (M • v - H v)
  have hs := hH.inner_left_eq_inner_right v (H v)
  have hb : ⟪H (H v), H v⟫ ≤ M * ‖H v‖ ^ 2 := by
    calc
      _ ≤ ‖H (H v)‖ * ‖H v‖ := real_inner_le_norm _ _
      _ ≤ (M * ‖H v‖) * ‖H v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
      _ = _ := by ring
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq] at hp
  have he : ⟪H (H v), v⟫ = ‖H v‖ ^ 2 := by
    rw [real_inner_comm, ← hs, real_inner_self_eq_norm_sq]
  simp only [conj_trivial, he] at hp
  nlinarith

lemma positive_map_reflection {H : E →L[ℝ] E} {M : ℝ}
    (hH : H.IsPositive) (hM : 0 < M) (hbound : ‖H‖ ≤ M) (v : E) :
    ‖v - (2 / M) • H v‖ ≤ ‖v‖ := by
  have hh := positive_map_square hH hM hbound v
  have hi : ⟪v, H v⟫ = ⟪H v, v⟫ := real_inner_comm _ _
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, hi]
  have hm : M ≠ 0 := ne_of_gt hM
  field_simp
  nlinarith

lemma hessian_cocoercivity {Q : Set E} (hQ : Convex ℝ Q)
    {g : E → E} {H : E → E →L[ℝ] E} {M : ℝ} (hM : 0 < M)
    (hg : ∀ x ∈ Q, HasFDerivAt g (H x) x)
    (hpos : ∀ x ∈ Q, (H x).IsPositive)
    (hbound : ∀ x ∈ Q, ‖H x‖ ≤ M)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖g y - g x‖ ^ 2 ≤ M * ⟪g y - g x, y - x⟫ := by
  let T : E → E := fun x => x - (2 / M) • g x
  let D : E → E →L[ℝ] E := fun x =>
    ContinuousLinearMap.id ℝ E - (2 / M) • H x
  have hd : ∀ x ∈ Q, HasFDerivWithinAt T (D x) Q x := by
    intro x hx
    exact ((hasFDerivAt_id x).sub ((hg x hx).const_smul (2 / M))).hasFDerivWithinAt
  have hb : ∀ x ∈ Q, ‖D x‖ ≤ 1 := by
    intro x hx
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    simpa [D] using positive_map_reflection (hpos x hx) hM (hbound x hx) v
  have hh := hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hx hy
  have he : T y - T x = (y - x) - (2 / M) • (g y - g x) := by
    dsimp [T]
    module
  rw [he, one_mul] at hh
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right] at hs
  have hi := real_inner_comm (y - x) (g y - g x)
  have hm : M ≠ 0 := ne_of_gt hM
  field_simp at hs
  nlinarith

lemma bounded_increment {u v w : E} {M d a b : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hab : 0 ≤ b - a)
    (hstep : b - a ≤ 1 - b)
    (hc : ‖v - u‖ ^ 2 ≤ M * (b - a) * ⟪v - u, w⟫)
    (hdir : (1 - b) * ⟪v - u, w⟫ ≤ d) :
    ‖v - u‖ ≤ Real.sqrt (M * d) := by
  have hfactor : M * (b - a) * ⟪v - u, w⟫ ≤ M * d := by
    by_cases h : 0 ≤ ⟪v - u, w⟫
    · have h1 := mul_le_mul_of_nonneg_right hstep h
      have h2 := mul_le_mul_of_nonneg_left (h1.trans hdir) hM
      nlinarith only [h2]
    · have hneg : M * (b - a) * ⟪v - u, w⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hM hab) (le_of_not_ge h)
      exact hneg.trans (mul_nonneg hM hd)
  have hs := Real.sq_sqrt (mul_nonneg hM hd)
  have hn := Real.sqrt_nonneg (M * d)
  nlinarith [norm_nonneg (v - u)]

lemma hessian_lipschitz {Q : Set E} (hQ : Convex ℝ Q)
    {g : E → E} {H : E → E →L[ℝ] E} {M : ℝ}
    (hg : ∀ x ∈ Q, HasFDerivAt g (H x) x)
    (hbound : ∀ x ∈ Q, ‖H x‖ ≤ M)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖g y - g x‖ ≤ M * ‖y - x‖ :=
  hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hg x hx).hasFDerivWithinAt) hbound hx hy

lemma hessian_upper_bound [CompleteSpace E]
    {Q : Set E} (hQ : Convex ℝ Q) {f : E → ℝ} {g : E → E}
    {H : E → E →L[ℝ] E} {M : ℝ}
    (hg : ∀ x ∈ Q, HasGradientAt f (g x) x)
    (hder : ∀ x ∈ Q, HasFDerivAt g (H x) x)
    (hbound : ∀ x ∈ Q, ‖H x‖ ≤ M)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤ f x + ⟪g x, y - x⟫ + M / 2 * ‖y - x‖ ^ 2 := by
  apply OracleTemplate.FrankWolfe.smooth_upper_bound_on hQ hg _ hx hy
  intro u hu v hv
  exact hessian_lipschitz hQ hder hbound hv hu

lemma maximum_absorption {m d J H0 H1 t slope : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hJ : J ≤ 2 * d)
    (ht : 0 ≤ t) (hH1 : 0 ≤ H1)
    (hslope : slope ≤ d / 4) (ht0 : t * H0 ≤ d / 4)
    (ht1 : t * H1 ≤ 1 / 8)
    (hmax : m ≤ d + slope + t * (H0 + H1 * (m + J))) :
    m ≤ 2 * d := by
  have h1 := mul_le_mul_of_nonneg_left hJ (mul_nonneg ht hH1)
  have h2 := mul_le_mul_of_nonneg_right ht1 hm
  have h3 := mul_le_mul_of_nonneg_right ht1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd)
  nlinarith

lemma compact_gap_bound [CompleteSpace E]
    {C : Set E} (hc : IsCompact C) (hC : Convex ℝ C)
    {f j : E → ℝ} {g : E → E} {H : E → E →L[ℝ] E}
    (hf : ∀ y ∈ C, HasGradientAt f (g y) y)
    (hder : ∀ y ∈ C, HasFDerivAt g (H y) y)
    {H0 H1 d G r : ℝ} (h0 : 0 ≤ H0) (h1 : 0 ≤ H1)
    (hd : 0 ≤ d) (hG : 0 ≤ G) (hr : 0 ≤ r)
    (hcurv : ∀ y ∈ C, ‖H y‖ ≤ H0 + H1 * (f y + j y))
    (hfn : ∀ y ∈ C, 0 ≤ f y) (hj : ∀ y ∈ C, j y ≤ 2 * d)
    {x : E} (hx : x ∈ C) (hstart : f x ≤ d) (hgrad : ‖g x‖ ≤ G)
    (hdist : ∀ y ∈ C, ‖y - x‖ ≤ r)
    (hGr : G * r ≤ d / 4) (hr0 : r ^ 2 / 2 * H0 ≤ d / 4)
    (hr1 : r ^ 2 / 2 * H1 ≤ 1 / 8) :
    ∀ y ∈ C, f y ≤ 2 * d := by
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn ⟨x, hx⟩ (HasGradientAt.continuousOn hf)
  let M := H0 + H1 * (f z + 2 * d)
  have hMn : 0 ≤ M := by dsimp [M]; positivity [hfn z hz]
  have hb : ∀ y ∈ C, ‖H y‖ ≤ M := by
    intro y hy
    apply (hcurv y hy).trans
    dsimp [M]
    gcongr
    · exact hmax hy
    · exact hj y hy
  have hu := hessian_upper_bound hC hf hder hb hx hz
  have hinner : ⟪g x, z - x⟫ ≤ G * r :=
    (real_inner_le_norm _ _).trans (mul_le_mul hgrad (hdist z hz) (norm_nonneg _) hG)
  have hsquare : ‖z - x‖ ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hr).mpr (hdist z hz)
  have hquad := mul_le_mul_of_nonneg_left hsquare (div_nonneg hMn (by norm_num : (0 : ℝ) ≤ 2))
  have hscalar : f z ≤ d + G * r + (r ^ 2 / 2) * (H0 + H1 * (f z + 2 * d)) := by
    dsimp [M] at hu hquad
    nlinarith only [hu, hinner, hquad, hstart]
  have hzbound := maximum_absorption hd (hfn z hz) (le_refl (2 * d))
    (by positivity : 0 ≤ r ^ 2 / 2) h1 hGr hr0 hr1 hscalar
  exact fun y hy => (hmax hy).trans hzbound

lemma gradient_path_increment [CompleteSpace E]
    {Q : Set E} {f : E → ℝ} {g : E → E} {H : E → E →L[ℝ] E}
    (hf : ConvexOn ℝ Q f) (hg : ∀ x ∈ Q, HasGradientAt f (g x) x)
    {M d : ℝ} (hM : 0 < M) (hd : 0 ≤ d)
    (hder : ∀ x ∈ Q, HasFDerivAt g (H x) x)
    (hpos : ∀ x ∈ Q, (H x).IsPositive)
    (hbound : ∀ x ∈ Q, ‖H x‖ ≤ M)
    {s x : E} (hs : s ∈ Q) (hx : x ∈ Q) (hgs : g s = 0)
    (hgap : f x - f s ≤ d)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hstep : b - a ≤ 1 - b) :
    ‖g (s + b • (x - s)) - g (s + a • (x - s))‖ ≤ Real.sqrt (M * d) := by
  let w := x - s
  let p := fun t : ℝ => s + t • w
  have hmem : ∀ t, 0 ≤ t → t ≤ 1 → p t ∈ Q := by
    intro t ht ht1
    convert hf.1 hs hx (sub_nonneg.mpr ht1) ht (by ring) using 1
    dsimp [p, w]
    module
  have hma := hmem a ha (hab.trans hb)
  have hmb := hmem b (ha.trans hab) hb
  have hp : p b - p a = (b - a) • w := by dsimp [p]; module
  have hc := hessian_cocoercivity hf.1 hM hder hpos hbound hma hmb
  rw [hp, inner_smul_right] at hc
  have hnon : 0 ≤ ⟪g (p a), w⟫ := by
    by_cases hz : a = 0
    · simp [p, hz, hgs]
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      have hh := hessian_cocoercivity hf.1 hM hder hpos hbound hs hma
      simp only [hgs, sub_zero] at hh
      have hp' : p a - s = a • w := by simp [p]
      rw [hp', inner_smul_right] at hh
      have hn : 0 ≤ M * a * ⟪g (p a), w⟫ := by nlinarith [sq_nonneg ‖g (p a)‖]
      exact nonneg_of_mul_nonneg_right hn (mul_pos hM hapos)
  have hlow := OracleTemplate.FrankWolfe.convex_support_on hf hs hmb (hg s hs)
  simp only [hgs, inner_zero_left] at hlow
  have hu := OracleTemplate.FrankWolfe.convex_support_on hf hmb hx (hg _ hmb)
  have hp' : x - p b = (1 - b) • w := by dsimp [p, w]; module
  rw [hp', inner_smul_right] at hu
  apply bounded_increment hM.le hd (sub_nonneg.mpr hab) hstep
  · nlinarith only [hc]
  · rw [inner_sub_left]
    have hn := mul_nonneg (sub_nonneg.mpr hb) hnon
    nlinarith

omit [InnerProductSpace ℝ E] in
lemma finite_path_bound (g : ℕ → E) (K : ℕ) {B : ℝ}
    (hb : ∀ k < K, ‖g (k + 1) - g k‖ ≤ B) :
    ‖g K - g 0‖ ≤ (K : ℝ) * B := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hprev := ih (fun k hk => hb k (Nat.lt_succ_of_lt hk))
    have hlast := hb K (Nat.lt_succ_self K)
    calc
      ‖g (K + 1) - g 0‖ ≤ ‖g (K + 1) - g K‖ + ‖g K - g 0‖ :=
        by
          convert norm_add_le (g (K + 1) - g K) (g K - g 0) using 1
          congr 1
          module
      _ ≤ B + (K : ℝ) * B := add_le_add hlast hprev
      _ = ((K + 1 : ℕ) : ℝ) * B := by push_cast; ring

lemma dyadic_gradient_bound [CompleteSpace E]
    {Q : Set E} {f : E → ℝ} {g : E → E} {H : E → E →L[ℝ] E}
    (hf : ConvexOn ℝ Q f) (hg : ∀ x ∈ Q, HasGradientAt f (g x) x)
    {M d R : ℝ} (hM : 0 < M) (hd : 0 ≤ d)
    (hder : ∀ x ∈ Q, HasFDerivAt g (H x) x)
    (hpos : ∀ x ∈ Q, (H x).IsPositive)
    (hbound : ∀ x ∈ Q, ‖H x‖ ≤ M)
    {s x : E} (hs : s ∈ Q) (hx : x ∈ Q) (hgs : g s = 0)
    (hgap : f x - f s ≤ d) (hR : ‖x - s‖ ≤ R) (K : ℕ) :
    ‖g x‖ ≤ (K : ℝ) * Real.sqrt (M * d) + M * R * (1 / 2 : ℝ) ^ K := by
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  let p : ℕ → E := fun k => s + (1 - q k) • (x - s)
  have hq0 : ∀ k, 0 ≤ q k := fun k => by dsimp [q]; positivity
  have hq1 : ∀ k, q k ≤ 1 := fun k => by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hstep : ∀ k, q (k + 1) = q k / 2 := by
    intro k
    dsimp [q]
    rw [pow_succ]
    ring
  have hinc : ∀ k < K, ‖g (p (k + 1)) - g (p k)‖ ≤ Real.sqrt (M * d) := by
    intro k _
    apply gradient_path_increment hf hg hM hd hder hpos hbound hs hx hgs hgap
      (sub_nonneg.mpr (hq1 k))
    · rw [hstep]
      linarith [hq0 k]
    · linarith [hq0 (k + 1)]
    · rw [hstep]
      ring_nf
      exact le_rfl
  have hsum := finite_path_bound (fun k => g (p k)) K hinc
  have hp0 : p 0 = s := by simp [p, q]
  rw [hp0, hgs, sub_zero] at hsum
  have hpk : p K ∈ Q := by
    convert hf.1 hs hx (hq0 K) (sub_nonneg.mpr (hq1 K)) (by ring) using 1
    dsimp [p]
    module
  have htail := hessian_lipschitz hf.1 hder hbound hpk hx
  have he : x - p K = q K • (x - s) := by dsimp [p]; module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq0 K)] at htail
  have ht : ‖g x - g (p K)‖ ≤ M * R * q K := by
    calc
      _ ≤ M * (q K * ‖x - s‖) := htail
      _ ≤ M * (q K * R) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hR (hq0 K)) hM.le
      _ = _ := by ring
  calc
    ‖g x‖ ≤ ‖g x - g (p K)‖ + ‖g (p K)‖ := by simpa [add_comm] using (norm_le_insert' (g x) (g (p K)))
    _ ≤ M * R * q K + (K : ℝ) * Real.sqrt (M * d) := add_le_add ht hsum
    _ = _ := by dsimp [q]; ring

lemma initial_smallness {G M d w : ℝ} (hd : 0 < d) (hG : 0 ≤ G) (hw : 0 ≤ w)
    (hGM : M * d ≤ G ^ 2)
    (hstep : 64 * (G * w) ^ 2 ≤ d * (G * w) + d ^ 2) :
    G * w ≤ d / 4 ∧ M * w ^ 2 ≤ d / 16 := by
  have hGw : 0 ≤ G * w := mul_nonneg hG hw
  have hsmall : G * w ≤ d / 4 := by
    by_contra! hh
    have hp := mul_pos (show 0 < G * w - d / 4 by linarith)
      (show 0 < G * w + d / 4 by positivity)
    nlinarith
  refine ⟨hsmall, ?_⟩
  have hs := (sq_le_sq₀ hGw (by positivity : 0 ≤ d / 4)).mpr hsmall
  have hm := mul_le_mul_of_nonneg_right hGM (sq_nonneg w)
  nlinarith

end LongTails.Proofs.FeasibleGapGeometry
