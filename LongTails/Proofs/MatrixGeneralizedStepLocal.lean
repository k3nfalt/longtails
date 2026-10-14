import LongTails.Proofs.MatrixGeneralizedRademacher
import LongTails.Proofs.MatrixGeneralizedSchedule
import LongTails.Proofs.MatrixGeneralizedExpect

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

structure Inst (p : Params) (f : Point p.d → ℝ) (H : Point p.d →L[ℝ] Point p.d)
    (xstar : Point p.d) : Prop where
  valid : Valid p
  geom : Geometry H
  trace : ∑ i, ⟪H (ebasis i), ebasis i⟫ ≤ p.r
  convex : ConvexOn ℝ Set.univ f
  grad : ∀ x, HasGradientAt f (gradient f x) x
  diff : Differentiable ℝ (gradient f)
  hess : HessBound f H p.L0 (Lp p)
  min : IsMinOn f Set.univ xstar
  start : ‖p.x0 - xstar‖ ≤ p.R
  gap : f p.x0 - f xstar ≤ p.Δ

section

variable {p : Params} {f : Point p.d → ℝ} {H : Point p.d →L[ℝ] Point p.d} {xstar : Point p.d}
  (I : Inst p f H xstar)
include I

omit I in
lemma norm_signVec (s : Fin p.d → Bool) : ‖signVec s‖ = Real.sqrt p.d := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_vec_sq]

lemma quad_signVec_le (s : Fin p.d → Bool) : ⟪H (signVec s), signVec s⟫ ≤ p.d := by
  have := I.geom.upper (signVec s)
  rwa [norm_vec_sq] at this

lemma hnorm_le_sqrt_d (c : ℝ) (s : Fin p.d → Bool) : hnorm H (c • signVec s) ≤ |c| * Real.sqrt p.d := by
  rw [hnorm_smul (H := H), ← norm_signVec (p := p) s]
  exact mul_le_mul_of_nonneg_left (hnorm_le_norm I.geom _) (abs_nonneg c)

lemma convex_lower (x v : Point p.d) : f x + ⟪gradient f x, v⟫ ≤ f (x + v) := by
  have h := Gradient.convex_support I.convex I.grad x (x + v)
  rw [add_sub_cancel_left] at h
  linarith

lemma descent (x v : Point p.d) (hv : Lp p * hnorm H v ≤ 1 / 2) :
    f (x + v) ≤ f x + ⟪gradient f x, v⟫ + curv H p.L0 (Lp p) (gradient f x) * hnorm H v ^ 2 :=
  local_descent I.geom I.valid.L0_pos (Lp_pos I.valid).le I.grad I.diff I.hess x v hv

lemma fd_error (y : Point p.d) {M : ℝ} (hM : curv H p.L0 (Lp p) (gradient f y) ≤ M)
    {h : ℝ} (hh : 0 < h) (htr : Lp p * (h * Real.sqrt p.d) ≤ 1 / 2) (s : Fin p.d → Bool) :
    |(f (y + h • signVec s) - f (y - h • signVec s)) / (2 * h) - ⟪gradient f y, signVec s⟫| ≤
      M * h * p.d / 2 := by
  set u := signVec s
  have hcv : 0 ≤ curv H p.L0 (Lp p) (gradient f y) := by
    unfold curv
    have := dnorm_nonneg I.geom (gradient f y)
    have := Lp_pos I.valid
    have := I.valid.L0_pos
    positivity
  have hn1 : hnorm H (h • u) ≤ h * Real.sqrt p.d := by
    have := hnorm_le_sqrt_d I h s; rwa [abs_of_pos hh] at this
  have hn2 : hnorm H ((-h) • u) ≤ h * Real.sqrt p.d := by
    have := hnorm_le_sqrt_d I (-h) s; rwa [abs_neg, abs_of_pos hh] at this
  have hq : hnorm H (h • u) ^ 2 ≤ h ^ 2 * p.d := by
    rw [hnorm_sq I.geom, quad_smul ]
    exact mul_le_mul_of_nonneg_left (quad_signVec_le I s) (sq_nonneg h)
  have hq' : hnorm H ((-h) • u) ^ 2 ≤ h ^ 2 * p.d := by
    rw [hnorm_sq I.geom, quad_smul , neg_sq]
    exact mul_le_mul_of_nonneg_left (quad_signVec_le I s) (sq_nonneg h)
  have hL := Lp_pos I.valid
  have hd1 := descent I y (h • u) (le_trans (mul_le_mul_of_nonneg_left hn1 hL.le) htr)
  have hd2 := descent I y ((-h) • u) (le_trans (mul_le_mul_of_nonneg_left hn2 hL.le) htr)
  have hl1 := convex_lower I y (h • u)
  have hl2 := convex_lower I y ((-h) • u)
  rw [real_inner_smul_right] at hd1 hl1
  rw [real_inner_smul_right] at hd2 hl2
  rw [show y + (-h) • u = y - h • u by rw [neg_smul, ← sub_eq_add_neg]] at hd2 hl2
  have hm1 : curv H p.L0 (Lp p) (gradient f y) * hnorm H (h • u) ^ 2 ≤ M * (h ^ 2 * p.d) :=
    mul_le_mul hM hq (sq_nonneg _) (hcv.trans hM)
  have hm2 : curv H p.L0 (Lp p) (gradient f y) * hnorm H ((-h) • u) ^ 2 ≤ M * (h ^ 2 * p.d) :=
    mul_le_mul hM hq' (sq_nonneg _) (hcv.trans hM)
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    nlinarith

lemma grad_at (y : Point p.d) {F : ℝ} (hF : 0 ≤ F) (hy : f y - f xstar ≤ F) :
    dnorm H (gradient f y) ≤ gradBound p F ∧
      curv H p.L0 (Lp p) (gradient f y) ≤ curvBound p F := by
  have hL := Lp_pos I.valid
  have hL0 := I.valid.L0_pos
  have hsq := dnorm_sq_le I.geom hL0 hL.le I.grad I.diff I.hess I.min y
  have hN := dnorm_nonneg I.geom (gradient f y)
  have hgap : 0 ≤ f y - f xstar := by
    have := I.min (Set.mem_univ y); simp only [Set.mem_ofPred_eq] at this; linarith
  have hsq' : dnorm H (gradient f y) ^ 2 ≤ 4 * (p.L0 + Lp p * dnorm H (gradient f y)) * F := by
    have : 4 * curv H p.L0 (Lp p) (gradient f y) * (f y - f xstar) ≤
        4 * (p.L0 + Lp p * dnorm H (gradient f y)) * F := by
      unfold curv
      have : 0 ≤ 4 * (p.L0 + Lp p * dnorm H (gradient f y)) := by positivity
      exact mul_le_mul_of_nonneg_left hy this
    linarith
  have h1 := dnorm_le_of_sq hF hL0.le hL.le hsq'
  refine ⟨h1, ?_⟩
  unfold curv curvBound
  have := mul_le_mul_of_nonneg_left h1 hL.le
  unfold gradBound at this ⊢
  linarith

lemma extrapolate_eq (k : ℕ) (x z : Point p.d) :
    extrapolate p k x z = x + (weight p (sched p k) / (sched p k + weight p (sched p k))) • (z - x) := by
  have hA := sched_pos I.valid k
  have ha := weight_pos I.valid hA
  unfold extrapolate
  have e : sched p k / (sched p k + weight p (sched p k)) =
      1 - weight p (sched p k) / (sched p k + weight p (sched p k)) := by
    field_simp; ring
  rw [e, sub_smul, one_smul, smul_sub]
  abel

lemma theta_sq_le (k : ℕ) :
    (weight p (sched p k) / (sched p k + weight p (sched p k))) ^ 2 ≤
      1 / (64 * p.d * rp p * curvBound p (gapLevel p (sched p k)) * sched p k) := by
  have hv := I.valid
  have hA := sched_pos hv k
  have ha := weight_pos hv hA
  have hst := stepSize_pos hv hA
  have hd := dR_pos hv
  have hrp := rp_pos hv
  have hMb := curvBound_pos hv (gapLevel_pos hv hA).le
  have hθa : weight p (sched p k) / (sched p k + weight p (sched p k)) ≤
      weight p (sched p k) / sched p k := div_le_div_of_nonneg_left ha.le hA (by linarith)
  have h1 := pow_le_pow_left₀ (by positivity) hθa 2
  have hw := weight_sq_le hv hA
  have h2 : (weight p (sched p k) / sched p k) ^ 2 ≤
      stepSize p (sched p k) / (8 * p.d * sched p k) := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hw (show 0 ≤ 8 * p.d * sched p k by positivity)
    have e : sched p k * stepSize p (sched p k) / (8 * p.d) * (8 * p.d * sched p k) =
        stepSize p (sched p k) * sched p k ^ 2 := by field_simp
    nlinarith
  have h3 : stepSize p (sched p k) / (8 * p.d * sched p k) =
      1 / (64 * p.d * rp p * curvBound p (gapLevel p (sched p k)) * sched p k) := by
    unfold stepSize; field_simp; ring
  linarith

lemma ell_sq_le (k : ℕ) (x z pt : Point p.d)
    (hz : ‖z - xstar‖ ≤ Real.sqrt 8 * p.R)
    (hpt : ‖pt - xstar‖ ≤ Real.sqrt 8 * p.R)
    (he : lagWeight p (sched p k) * hnorm H (x - pt) ^ 2 ≤ 4 * p.R ^ 2) :
    hnorm H (z - x) ^ 2 ≤ 100 * p.d * rp p * p.R ^ 2 := by
  have hv := I.valid
  have hA := sched_pos hv k
  have hγ := lagWeight_pos hv hA
  have hγl := lagWeight_ge hv hA
  have hd := dR_pos hv
  have hd1 := one_le_d hv
  have hrp := rp_pos hv
  have hrp16 := rp_ge16 hv
  have hR := hv.R_pos
  have hℓ0 := hnorm_nonneg' (H := H) (z - x)
  have hℓ : hnorm H (z - x) ≤ ‖z - xstar‖ + ‖pt - xstar‖ + hnorm H (x - pt) := by
    have e : z - x = (z - xstar) + (xstar - pt) + (pt - x) := by abel
    have h1 := hnorm_add I.geom ((z - xstar) + (xstar - pt)) (pt - x)
    have h2 := hnorm_add I.geom (z - xstar) (xstar - pt)
    rw [← e] at h1
    rw [hnorm_sub_comm (H := H) xstar pt] at h2
    rw [hnorm_sub_comm (H := H) pt x] at h1
    linarith [hnorm_le_norm I.geom (z - xstar), hnorm_le_norm I.geom (pt - xstar)]
  have hz2 : ‖z - xstar‖ ^ 2 ≤ 8 * p.R ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hz 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num)] at this
  have hp2 : ‖pt - xstar‖ ^ 2 ≤ 8 * p.R ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hpt 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num)] at this
  have hex : hnorm H (x - pt) ^ 2 ≤ 32 * p.d * rp p * p.R ^ 2 := by
    have h1 : hnorm H (x - pt) ^ 2 ≤ 4 * p.R ^ 2 / lagWeight p (sched p k) := by
      rw [le_div_iff₀ hγ]; linarith
    have h2 : 4 * p.R ^ 2 / lagWeight p (sched p k) ≤ 32 * p.d * rp p * p.R ^ 2 := by
      rw [div_le_iff₀ hγ]
      have := mul_le_mul_of_nonneg_left hγl (show 0 ≤ 32 * p.d * rp p * p.R ^ 2 by positivity)
      have e : 32 * p.d * rp p * p.R ^ 2 * (1 / (8 * p.d * rp p)) = 4 * p.R ^ 2 := by
        field_simp; ring
      linarith
    linarith
  have hsum := pow_le_pow_left₀ hℓ0 hℓ 2
  set a1 := ‖z - xstar‖
  set a2 := ‖pt - xstar‖
  set a3 := hnorm H (x - pt)
  have h3 : (a1 + a2 + a3) ^ 2 ≤ 3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) := by
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (a1 - a3), sq_nonneg (a2 - a3)]
  have hdr : 16 ≤ p.d * rp p := by nlinarith
  have h4 : 3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) ≤ 48 * p.R ^ 2 + 96 * p.d * rp p * p.R ^ 2 := by
    linarith
  have h5 : 48 * p.R ^ 2 ≤ 4 * p.d * rp p * p.R ^ 2 := by
    have : 0 ≤ p.R ^ 2 := sq_nonneg _
    nlinarith
  linarith

omit I in
lemma loc_trust_aux {θ ℓ Mb A R d rp L : ℝ} (hθ0 : 0 ≤ θ) (hℓ0 : 0 ≤ ℓ) (hMb : 0 < Mb)
    (hA : 0 < A) (hd : 0 < d) (hrp : 0 < rp) (hL : 0 < L)
    (hθ2 : θ ^ 2 ≤ 1 / (64 * d * rp * Mb * A)) (hℓ2 : ℓ ^ 2 ≤ 100 * d * rp * R ^ 2)
    (hMA : 32 * L ^ 2 * R ^ 2 ≤ Mb * A) :
    L * (θ * ℓ) ≤ 1 / 2 ∧ Mb * (θ * ℓ) ^ 2 ≤ 2 * R ^ 2 / A := by
  have hprod : θ ^ 2 * ℓ ^ 2 ≤ 100 * R ^ 2 / (64 * Mb * A) := by
    have h1 : θ ^ 2 * ℓ ^ 2 ≤ 1 / (64 * d * rp * Mb * A) * (100 * d * rp * R ^ 2) :=
      mul_le_mul hθ2 hℓ2 (sq_nonneg _) (by positivity)
    have h2 : 1 / (64 * d * rp * Mb * A) * (100 * d * rp * R ^ 2) = 100 * R ^ 2 / (64 * Mb * A) := by
      field_simp
    linarith
  constructor
  · have h1 : (L * (θ * ℓ)) ^ 2 ≤ (1 / 2) ^ 2 := by
      have e : (L * (θ * ℓ)) ^ 2 = L ^ 2 * (θ ^ 2 * ℓ ^ 2) := by ring
      rw [e]
      have h3 : L ^ 2 * (θ ^ 2 * ℓ ^ 2) ≤ L ^ 2 * (100 * R ^ 2 / (64 * Mb * A)) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      have h4 : L ^ 2 * (100 * R ^ 2 / (64 * Mb * A)) ≤ (1 / 2) ^ 2 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  · have h1 : Mb * (θ * ℓ) ^ 2 ≤ Mb * (100 * R ^ 2 / (64 * Mb * A)) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hprod hMb.le
    have h2 : Mb * (100 * R ^ 2 / (64 * Mb * A)) = 100 / 64 * (R ^ 2 / A) := by
      field_simp
    have h3 : 0 ≤ R ^ 2 / A := by positivity
    have h4 : 2 * R ^ 2 / A = 2 * (R ^ 2 / A) := by ring
    linarith

omit I in
lemma loc_term1_aux {θ G Mb A R d rp : ℝ} (hθ0 : 0 ≤ θ) (hG0 : 0 ≤ G) (hMb : 0 < Mb)
    (hA : 0 < A) (hd : 0 < d) (hrp : 0 < rp) (hR : 0 < R) (hdr : 16 ≤ d * rp)
    (hθ2 : θ ^ 2 ≤ 1 / (64 * d * rp * Mb * A)) (hG2 : G ^ 2 ≤ 8 * (8 * R ^ 2 / A) * Mb) :
    θ * (G * (Real.sqrt 8 * R)) ≤ 2 * R ^ 2 / A := by
  have e : (θ * (G * (Real.sqrt 8 * R))) ^ 2 = θ ^ 2 * G ^ 2 * (8 * R ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have h3 : θ ^ 2 * G ^ 2 * (8 * R ^ 2) ≤
      1 / (64 * d * rp * Mb * A) * (8 * (8 * R ^ 2 / A) * Mb) * (8 * R ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hθ2 hG2 (sq_nonneg _) (by positivity)
  have h4 : 1 / (64 * d * rp * Mb * A) * (8 * (8 * R ^ 2 / A) * Mb) * (8 * R ^ 2) =
      8 * R ^ 4 / (d * rp * A ^ 2) := by
    field_simp; ring
  have h5 : 8 * R ^ 4 / (d * rp * A ^ 2) ≤ (2 * R ^ 2 / A) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ R ^ 4 * A ^ 2 := by positivity
    nlinarith
  have h2 : (θ * (G * (Real.sqrt 8 * R))) ^ 2 ≤ (2 * R ^ 2 / A) ^ 2 := by
    rw [e]; linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp h2

lemma locality (k : ℕ) (x z pt : Point p.d)
    (hx : f x - f xstar ≤ 4 * p.R ^ 2 / sched p k)
    (hz : ‖z - xstar‖ ≤ Real.sqrt 8 * p.R)
    (hpt : ‖pt - xstar‖ ≤ Real.sqrt 8 * p.R)
    (he : lagWeight p (sched p k) * hnorm H (x - pt) ^ 2 ≤ 4 * p.R ^ 2) :
    f (extrapolate p k x z) - f xstar ≤ gapLevel p (sched p k) := by
  have hv := I.valid
  set A := sched p k with hAdef
  have hA : 0 < A := sched_pos hv k
  set a := weight p A
  have ha : 0 < a := weight_pos hv hA
  set st := stepSize p A
  have hst : 0 < st := stepSize_pos hv hA
  set Mb := curvBound p (gapLevel p A)
  have hMb : 0 < Mb := curvBound_pos hv (gapLevel_pos hv hA).le
  set Gb := gradBound p (gapLevel p A)
  set γ := lagWeight p A
  have hγ : 0 < γ := lagWeight_pos hv hA
  have hγl := lagWeight_ge hv hA
  set θ := a / (A + a)
  have hθ0 : 0 ≤ θ := by positivity
  have hd := dR_pos hv
  have hrp := rp_pos hv
  have hrp16 := rp_ge16 hv
  have hR := hv.R_pos
  have hL := Lp_pos hv
  have hd1 := one_le_d hv
  have hgapA : gapLevel p A = 8 * p.R ^ 2 / A := rfl
  have hfx0 : 0 ≤ f x - f xstar := by
    have := I.min (Set.mem_univ x); simp only [Set.mem_ofPred_eq] at this; linarith
  have hx8 : f x - f xstar ≤ gapLevel p A := by
    rw [hgapA]; have : 4 * p.R ^ 2 / A ≤ 8 * p.R ^ 2 / A :=
      div_le_div_of_nonneg_right (by nlinarith) hA.le
    linarith
  obtain ⟨hNx, hMx⟩ := grad_at I x (gapLevel_pos hv hA).le hx8
  have hθ2 : θ ^ 2 ≤ 1 / (64 * p.d * rp p * Mb * A) := theta_sq_le I k
  have hMA := curv_mul_A hv hA
  set ℓ := hnorm H (z - x)
  have hℓ0 : 0 ≤ ℓ := hnorm_nonneg' (H := H) _
  have hℓ2 : ℓ ^ 2 ≤ 100 * p.d * rp p * p.R ^ 2 := ell_sq_le I k x z pt hz hpt he
  have hdr : 16 ≤ p.d * rp p := by nlinarith
  obtain ⟨htr, hterm2'⟩ := loc_trust_aux hθ0 hℓ0 hMb hA hd hrp hL hθ2 hℓ2 hMA
  have htrust : Lp p * hnorm H (θ • (z - x)) ≤ 1 / 2 := by
    rw [hnorm_smul (H := H), abs_of_nonneg hθ0]; exact htr
  have hdesc := descent I x (θ • (z - x)) htrust
  rw [← extrapolate_eq I] at hdesc
  rw [real_inner_smul_right, hnorm_smul (H := H), abs_of_nonneg hθ0] at hdesc
  have hin : ⟪gradient f x, z - x⟫ ≤ dnorm H (gradient f x) * (Real.sqrt 8 * p.R) := by
    have h1 := convex_lower I x (xstar - x)
    rw [add_sub_cancel] at h1
    have h2 := inner_le_dnorm I.geom (gradient f x) (z - xstar)
    have h3 : hnorm H (z - xstar) ≤ Real.sqrt 8 * p.R := (hnorm_le_norm I.geom _).trans hz
    have e : z - x = (z - xstar) + (xstar - x) := by abel
    rw [e, inner_add_right]
    have hN0 := dnorm_nonneg I.geom (gradient f x)
    have := mul_le_mul_of_nonneg_left h3 hN0
    linarith
  have hGb0 : 0 ≤ Gb := gradBound_nonneg hv (gapLevel_pos hv hA).le
  have hG2 : Gb ^ 2 ≤ 8 * (8 * p.R ^ 2 / A) * Mb := gradBound_sq_le hv (gapLevel_pos hv hA).le
  have hterm1 : θ * ⟪gradient f x, z - x⟫ ≤ 2 * p.R ^ 2 / A := by
    have h1 : θ * ⟪gradient f x, z - x⟫ ≤ θ * (Gb * (Real.sqrt 8 * p.R)) := by
      apply mul_le_mul_of_nonneg_left _ hθ0
      exact hin.trans (mul_le_mul_of_nonneg_right hNx (by positivity))
    have := loc_term1_aux hθ0 hGb0 hMb hA hd hrp hR hdr hθ2 hG2
    linarith
  have hterm2 : curv H p.L0 (Lp p) (gradient f x) * (θ * ℓ) ^ 2 ≤ 2 * p.R ^ 2 / A := by
    have : curv H p.L0 (Lp p) (gradient f x) * (θ * ℓ) ^ 2 ≤ Mb * (θ * ℓ) ^ 2 :=
      mul_le_mul_of_nonneg_right hMx (sq_nonneg _)
    linarith
  rw [hgapA]
  have e : 8 * p.R ^ 2 / A = 4 * p.R ^ 2 / A + 2 * p.R ^ 2 / A + 2 * p.R ^ 2 / A := by ring
  linarith

omit I in
lemma clip_abs_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : |clip c t| ≤ c := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

omit I in
lemma clip_abs_le_abs {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : |clip c t| ≤ |t| := by
  unfold clip
  rcases le_total t 0 with ht | ht
  · rw [min_eq_right (by linarith), abs_of_nonpos ht, abs_le]
    exact ⟨by linarith [le_max_right (-c) t], max_le (by linarith) (by linarith)⟩
  · have hm : 0 ≤ min c t := le_min hc ht
    rw [max_eq_right (by linarith), abs_of_nonneg ht, abs_of_nonneg hm]
    exact min_le_right _ _

omit I in
lemma clip_lower {c η t th : ℝ} (hc : 2 * η ≤ c) (hη : 0 ≤ η) (he : |th - t| ≤ η) :
    t ^ 2 - η * |t| - (if c - η < |t| then t ^ 2 else 0) ≤ clip c th * t := by
  have hc0 : 0 ≤ c := by linarith
  rw [abs_le] at he
  by_cases hin : |th| ≤ c
  · have hcl : clip c th = th := by
      unfold clip; rw [abs_le] at hin
      rw [min_eq_right hin.2, max_eq_right hin.1]
    rw [hcl]
    have : th * t ≥ t ^ 2 - η * |t| := by
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]; nlinarith
      · rw [abs_of_nonpos ht]; nlinarith
    split_ifs <;> nlinarith [sq_nonneg t]
  · rw [not_le] at hin
    have hbig : c - η < |t| := by
      have : |th| ≤ |t| + η := by
        rcases le_total 0 th with h1 | h1 <;> rcases le_total 0 t with h2 | h2 <;>
          simp only [abs_of_nonneg, abs_of_nonpos, *] <;> linarith
      linarith
    rw [ite_eq_left hbig]
    have hsame : 0 ≤ clip c th * t := by
      unfold clip
      rcases lt_or_gt_of_ne (show th ≠ 0 by intro h0; rw [h0, abs_zero] at hin; linarith) with h1 | h1
      · have : th < -c := by
          rw [abs_of_neg h1] at hin; linarith
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        have : t < 0 := by
          have : |t| > η := by linarith
          rcases le_total 0 t with h2 | h2
          · rw [abs_of_nonneg h2] at this; linarith
          · rw [abs_of_nonpos h2] at this; linarith
        nlinarith
      · have : c < th := by rw [abs_of_pos h1] at hin; linarith
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        have : 0 < t := by
          have : |t| > η := by linarith
          rcases le_total 0 t with h2 | h2
          · rw [abs_of_nonneg h2] at this; linarith
          · rw [abs_of_nonpos h2] at this; linarith
        nlinarith
    have : t ^ 2 - η * |t| - t ^ 2 ≤ 0 := by nlinarith [abs_nonneg t]
    linarith

omit I in
lemma xstep_safe (y : Point p.d) (s : Fin p.d → Bool) (st c : ℝ) :
    f (if f (y - (st * c) • signVec s) ≤ f y then y - (st * c) • signVec s else y) ≤ f y := by
  split_ifs with h
  · exact h
  · exact le_rfl

lemma xstep_descent (y : Point p.d) (s : Fin p.d → Bool) {st c lam Mb : ℝ}
    (hst : 0 ≤ st) (hlam : 0 ≤ lam) (hc : |c| ≤ lam)
    (hM : curv H p.L0 (Lp p) (gradient f y) ≤ Mb)
    (htr : Lp p * (st * lam * Real.sqrt (48 * p.r)) ≤ 1 / 2)
    (hq : ⟪H (signVec s), signVec s⟫ ≤ 48 * p.r) :
    f (if f (y - (st * c) • signVec s) ≤ f y then y - (st * c) • signVec s else y) ≤
      f y - st * c * ⟪gradient f y, signVec s⟫ + Mb * (st ^ 2 * c ^ 2 * ⟪H (signVec s), signVec s⟫) := by
  have hv := I.valid
  have hL := Lp_pos hv
  have hq0 := quad_nonneg I.geom (signVec s)
  have hn : hnorm H (-(st * c) • signVec s) ≤ st * lam * Real.sqrt (48 * p.r) := by
    rw [hnorm_smul (H := H), abs_neg, abs_mul, abs_of_nonneg hst, hnorm]
    have : Real.sqrt ⟪H (signVec s), signVec s⟫ ≤ Real.sqrt (48 * p.r) := Real.sqrt_le_sqrt hq
    have h1 : |c| * Real.sqrt ⟪H (signVec s), signVec s⟫ ≤ lam * Real.sqrt (48 * p.r) :=
      mul_le_mul hc this (Real.sqrt_nonneg _) hlam
    nlinarith [Real.sqrt_nonneg ⟪H (signVec s), signVec s⟫]
  have hd := descent I y (-(st * c) • signVec s) (le_trans (mul_le_mul_of_nonneg_left hn hL.le) htr)
  rw [real_inner_smul_right, hnorm_sq I.geom, quad_smul ,
    show y + -(st * c) • signVec s = y - (st * c) • signVec s by rw [neg_smul, ← sub_eq_add_neg]] at hd
  have hcv : 0 ≤ curv H p.L0 (Lp p) (gradient f y) := by
    unfold curv; have := dnorm_nonneg I.geom (gradient f y); have := hv.L0_pos; positivity
  have hmono : curv H p.L0 (Lp p) (gradient f y) * ((-(st * c)) ^ 2 * ⟪H (signVec s), signVec s⟫) ≤
      Mb * (st ^ 2 * c ^ 2 * ⟪H (signVec s), signVec s⟫) := by
    rw [neg_sq, mul_pow]
    exact mul_le_mul_of_nonneg_right hM (by positivity)
  split_ifs with h
  · linarith
  · rw [not_le] at h; linarith

end

end OracleTemplate.MatrixGeneralizedZO
