import LongTails.Proofs.MatrixGeneralizedStepLocal

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

noncomputable def fdVal (p : Params) (f : Point p.d → ℝ) (k : ℕ) (y : Point p.d)
    (s : Fin p.d → Bool) : ℝ :=
  (f (y + fdStep p k • signVec s) - f (y - fdStep p k • signVec s)) / (2 * fdStep p k)

noncomputable def cand (p : Params) (f : Point p.d → ℝ) (k : ℕ) (y : Point p.d)
    (s : Fin p.d → Bool) : Point p.d :=
  candidate p k y s (f (y + fdStep p k • signVec s)) (f (y - fdStep p k • signVec s))

noncomputable def xnext (p : Params) (f : Point p.d → ℝ) (k : ℕ) (y : Point p.d)
    (s : Fin p.d → Bool) : Point p.d :=
  if f (cand p f k y s) ≤ f y then cand p f k y s else y

noncomputable def etaOf (p : Params) (k : ℕ) : ℝ :=
  curvBound p (gapLevel p (sched p k)) * fdStep p k * p.d / 2

lemma cand_eq (p : Params) (f : Point p.d → ℝ) (k : ℕ) (y : Point p.d) (s : Fin p.d → Bool) :
    cand p f k y s = y - (stepSize p (sched p k) *
      clip (clipLevel p (sched p k)) (fdVal p f k y s)) • signVec s := rfl

noncomputable def znext (p : Params) (f : Point p.d → ℝ) (k : ℕ) (y z : Point p.d)
    (s : Fin p.d → Bool) : Point p.d :=
  nextDual p k z s (f (y + fdStep p k • signVec s)) (f (y - fdStep p k • signVec s))

noncomputable def potential (p : Params) (f : Point p.d → ℝ) (H : Point p.d →L[ℝ] Point p.d)
    (xstar : Point p.d) (k : ℕ) (x z pt : Point p.d) : ℝ :=
  sched p k * (f x - f xstar) + ‖z - xstar‖ ^ 2 / 2 + lagWeight p (sched p k) * hnorm H (x - pt) ^ 2

lemma znext_eq (p : Params) (f : Point p.d → ℝ) (k : ℕ) (y z : Point p.d) (s : Fin p.d → Bool) :
    znext p f k y z s = z - (weight p (sched p k) * fdVal p f k y s) • signVec s := rfl

lemma combine_algebra {A a st G η ℓ2 γ γ' d r Dz : ℝ} (hA : 0 < A) (ha : 0 < a) (hst : 0 < st)
     (hℓ : 0 ≤ ℓ2) (hγ : 0 < γ) (hd : 0 < d) (hr : 0 < r)
    (hγdef : γ = a / (64 * st)) (hγ' : γ' ≤ (1 + a / A) * γ)
    (hcontr : (1 + a / A) * ((A / (A + a)) ^ 2 + a / A / 2) ≤ 1)
    (hw : a ^ 2 ≤ A * st / (8 * d)) (hθr : a / A * (r + 2) ≤ 2) :
    -(A + a) * (st * (G ^ 2 / 4 - 17 / 4 * η ^ 2)) + a * η * Dz + a ^ 2 * d * (G ^ 2 + η ^ 2) +
      γ' * (((A / (A + a)) ^ 2 + a / A / 2) * ℓ2 + 4 / (a / A) * st ^ 2 * (G ^ 2 + η ^ 2) +
        st ^ 2 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r)) ≤
      γ * ℓ2 + (5 * ((A + a) * st) * η ^ 2 + a * η * Dz + a ^ 2 * d * η ^ 2) := by
  set θ := a / A
  have hθ : 0 < θ := by positivity
  have hθr' : θ * r ≤ 2 := by nlinarith
  have hc1 : γ' * ((A / (A + a)) ^ 2 + θ / 2) * ℓ2 ≤ γ * ℓ2 := by
    have h1 : γ' * ((A / (A + a)) ^ 2 + θ / 2) ≤ (1 + θ) * γ * ((A / (A + a)) ^ 2 + θ / 2) :=
      mul_le_mul_of_nonneg_right hγ' (by positivity)
    have h2 : (1 + θ) * γ * ((A / (A + a)) ^ 2 + θ / 2) ≤ γ := by
      have := mul_le_mul_of_nonneg_left hcontr hγ.le
      nlinarith
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hℓ
  have hc2 : γ' * (4 / θ * st ^ 2) ≤ (A + a) * st / 16 := by
    have h1 : γ' * (4 / θ * st ^ 2) ≤ (1 + θ) * γ * (4 / θ * st ^ 2) :=
      mul_le_mul_of_nonneg_right hγ' (by positivity)
    have e : (1 + θ) * γ * (4 / θ * st ^ 2) = (A + a) * st / 16 := by
      rw [hγdef]; simp only [θ]; field_simp; ring
    linarith
  have hc3 : γ' * st ^ 2 ≤ (A + a) * st * θ / 64 := by
    have h1 : γ' * st ^ 2 ≤ (1 + θ) * γ * st ^ 2 := mul_le_mul_of_nonneg_right hγ' (sq_nonneg _)
    have e : (1 + θ) * γ * st ^ 2 = (A + a) * st * θ / 64 := by
      rw [hγdef]; simp only [θ]; field_simp
    linarith
  have hw' : a ^ 2 * d ≤ (A + a) * st / 8 := by
    have := mul_le_mul_of_nonneg_right hw hd.le
    have e : A * st / (8 * d) * d = A * st / 8 := by field_simp
    nlinarith
  have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have hAs : 0 < (A + a) * st := by positivity
  have t1 : γ' * (4 / θ * st ^ 2 * (G ^ 2 + η ^ 2)) ≤ (A + a) * st / 16 * (G ^ 2 + η ^ 2) := by
    rw [show γ' * (4 / θ * st ^ 2 * (G ^ 2 + η ^ 2)) = γ' * (4 / θ * st ^ 2) * (G ^ 2 + η ^ 2) by ring]
    exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  have t2 : γ' * (st ^ 2 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r)) ≤
      (A + a) * st * θ / 64 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r) := by
    rw [show γ' * (st ^ 2 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r)) =
      γ' * st ^ 2 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r) by ring]
    exact mul_le_mul_of_nonneg_right hc3 (by positivity)
  have t3 : (A + a) * st * θ / 64 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r) ≤
      (A + a) * st / 16 * G ^ 2 + (A + a) * st / 16 * η ^ 2 := by
    have e : (A + a) * st * θ / 64 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r) =
        (A + a) * st / 32 * (G ^ 2 * (θ * (r + 2)) + η ^ 2 * (θ * r)) := by ring
    rw [e]
    have h1 : G ^ 2 * (θ * (r + 2)) ≤ G ^ 2 * 2 := mul_le_mul_of_nonneg_left hθr hG2
    have h2 : η ^ 2 * (θ * r) ≤ η ^ 2 * 2 := mul_le_mul_of_nonneg_left hθr' hη2
    have h3 : (A + a) * st / 32 * (G ^ 2 * (θ * (r + 2)) + η ^ 2 * (θ * r)) ≤
        (A + a) * st / 32 * (G ^ 2 * 2 + η ^ 2 * 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have t4 : a ^ 2 * d * G ^ 2 ≤ (A + a) * st / 8 * G ^ 2 := mul_le_mul_of_nonneg_right hw' hG2
  have e1 : γ' * (((A / (A + a)) ^ 2 + θ / 2) * ℓ2 + 4 / θ * st ^ 2 * (G ^ 2 + η ^ 2) +
      st ^ 2 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r)) =
      γ' * ((A / (A + a)) ^ 2 + θ / 2) * ℓ2 + γ' * (4 / θ * st ^ 2 * (G ^ 2 + η ^ 2)) +
        γ' * (st ^ 2 * (2 * G ^ 2 * (r + 2) + 2 * η ^ 2 * r)) := by ring
  rw [e1]
  nlinarith

lemma sq_le_of_abs_sub {a b η : ℝ} (h : |a - b| ≤ η) : a ^ 2 ≤ 2 * b ^ 2 + 2 * η ^ 2 := by
  rw [abs_le] at h
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b)]

lemma xstep_algebra {G η st Mb rp r : ℝ} (hst : 0 < st) (hrp : 0 < rp)
    (hMbst : Mb * st = 1 / (8 * rp)) (hrp2 : r + 2 ≤ rp) :
    st * (G ^ 2 / 4 - 17 / 4 * η ^ 2) ≤
      st * (G ^ 2 - G ^ 2 / 4 - η * G - 3 * G ^ 2 / 16) -
        Mb * (st ^ 2 * (2 * (G ^ 2 * (r + 2)) + 2 * η ^ 2 * r)) := by
  have e : Mb * (st ^ 2 * (2 * (G ^ 2 * (r + 2)) + 2 * η ^ 2 * r)) =
      st * ((2 * (G ^ 2 * (r + 2)) + 2 * η ^ 2 * r) / (8 * rp)) := by
    rw [show Mb * (st ^ 2 * (2 * (G ^ 2 * (r + 2)) + 2 * η ^ 2 * r)) =
      (Mb * st) * st * (2 * (G ^ 2 * (r + 2)) + 2 * η ^ 2 * r) by ring, hMbst]
    field_simp
  rw [e]
  have h1 : (2 * (G ^ 2 * (r + 2)) + 2 * η ^ 2 * r) / (8 * rp) ≤ G ^ 2 / 4 + η ^ 2 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hr' : r ≤ rp := by linarith
    have h3 : G ^ 2 * (r + 2) ≤ G ^ 2 * rp := mul_le_mul_of_nonneg_left hrp2 (sq_nonneg G)
    have h4 : η ^ 2 * r ≤ η ^ 2 * rp := mul_le_mul_of_nonneg_left hr' (sq_nonneg η)
    nlinarith
  have h2 : η * G ≤ G ^ 2 / 16 + 4 * η ^ 2 := by nlinarith [sq_nonneg (G / 4 - 2 * η)]
  have : G ^ 2 / 4 - 17 / 4 * η ^ 2 ≤
      G ^ 2 - G ^ 2 / 4 - η * G - 3 * G ^ 2 / 16 - (G ^ 2 / 4 + η ^ 2 / 4) := by linarith
  have := mul_le_mul_of_nonneg_left this hst.le
  have := mul_le_mul_of_nonneg_left h1 hst.le
  nlinarith

lemma contraction_aux {A a : ℝ} (hA : 0 < A) (ha : 0 < a) (hθ : a / A ≤ 1 / 4) :
    (1 + a / A) * ((A / (A + a)) ^ 2 + a / A / 2) ≤ 1 := by
  set θ := a / A
  have hθ0 : 0 < θ := by positivity
  have hρ : A / (A + a) = 1 / (1 + θ) := by simp only [θ]; field_simp
  rw [hρ]
  rw [show (1 + θ) * ((1 / (1 + θ)) ^ 2 + θ / 2) = 1 / (1 + θ) + θ * (1 + θ) / 2 by
    field_simp]
  rw [div_add_div _ _ (by positivity) (by norm_num), div_le_one (by positivity)]
  have h2 : 0 ≤ θ * (2 - (1 + θ) ^ 2) := mul_nonneg hθ0.le (by nlinarith)
  nlinarith

lemma error_aux {A a st η Dz d R τ W : ℝ} (hAst : 0 ≤ (A + a) * st) (ha : 0 ≤ a) (hd : 1 ≤ d)
    (hη : 0 ≤ η) (hDz : Dz ≤ 3 * R) (hR : 0 < R) (hτ : 0 ≤ τ) (hτR : τ ≤ R)
    (hW : 1 + (A + a) * st + a * Real.sqrt d + a ^ 2 * d ≤ W) (hηW : η ≤ τ / W) :
    5 * ((A + a) * st) * η ^ 2 + a * η * Dz + a ^ 2 * d * η ^ 2 ≤ 9 * (τ * R) := by
  have hW1 : 1 ≤ W := by
    have : 0 ≤ a * Real.sqrt d := mul_nonneg ha (Real.sqrt_nonneg _)
    have : 0 ≤ a ^ 2 * d := by positivity
    linarith
  have hW0 : 0 < W := by linarith
  have hηW' : η * W ≤ τ := by rwa [le_div_iff₀ hW0] at hηW
  have hητ : η ≤ τ := by nlinarith
  have hηR : η ≤ R := hητ.trans hτR
  have hsd : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hd
  have h1 : (A + a) * st * η ≤ τ := by
    have : (A + a) * st ≤ W := by
      have : 0 ≤ a * Real.sqrt d := mul_nonneg ha (Real.sqrt_nonneg _)
      have : 0 ≤ a ^ 2 * d := by positivity
      linarith
    nlinarith
  have h2 : a * η ≤ τ := by
    have : a ≤ W := by
      have : a ≤ a * Real.sqrt d := le_mul_of_one_le_right ha hsd
      have : 0 ≤ a ^ 2 * d := by positivity
      linarith
    nlinarith
  have h3 : a ^ 2 * d * η ≤ τ := by
    have : a ^ 2 * d ≤ W := by
      have : 0 ≤ a * Real.sqrt d := mul_nonneg ha (Real.sqrt_nonneg _)
      linarith
    nlinarith
  have t1 : 5 * ((A + a) * st) * η ^ 2 ≤ 5 * (τ * R) := by
    have : (A + a) * st * η * η ≤ τ * R := mul_le_mul h1 hηR hη hτ
    nlinarith
  have t2 : a * η * Dz ≤ 3 * (τ * R) := by
    have hDz0 : a * η * Dz ≤ a * η * (3 * R) := by
      by_cases hD : 0 ≤ Dz
      · exact mul_le_mul_of_nonneg_left hDz (mul_nonneg ha hη)
      · have : a * η * Dz ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hη) (by linarith)
        have : 0 ≤ a * η * (3 * R) := by positivity
        linarith
    nlinarith
  have t3 : a ^ 2 * d * η ^ 2 ≤ τ * R := by
    have : a ^ 2 * d * η * η ≤ τ * R := mul_le_mul h3 hηR hη hτ
    nlinarith
  linarith

section

variable {p : Params} {f : Point p.d → ℝ} {H : Point p.d →L[ℝ] Point p.d} {xstar : Point p.d}
  (I : Inst p f H xstar)
include I

lemma diag_nonneg (k : Fin p.d) : 0 ≤ ⟪H (ebasis k), ebasis k⟫ := quad_nonneg I.geom _

lemma expect_quad_le : (𝔼 s : Fin p.d → Bool, ⟪H (signVec s), signVec s⟫) ≤ p.r := by
  rw [expect_quad I.geom.symm]; exact I.trace

lemma expect_D2q_le (g : Point p.d) :
    (𝔼 s : Fin p.d → Bool, ⟪g, signVec s⟫ ^ 2 * ⟪H (signVec s), signVec s⟫) ≤
      ‖g‖ ^ 2 * (p.r + 2) := by
  have h := expect_inner_sq_quad I.geom.symm (diag_nonneg I) g
  have h2 : ⟪H g, g⟫ ≤ ‖g‖ ^ 2 := I.geom.upper g
  have h3 := mul_le_mul_of_nonneg_left I.trace (sq_nonneg ‖g‖)
  nlinarith

lemma fd_bound (k : ℕ) (y : Point p.d) (hy : f y - f xstar ≤ gapLevel p (sched p k))
    (s : Fin p.d → Bool) :
    |fdVal p f k y s - ⟪gradient f y, signVec s⟫| ≤ etaOf p k := by
  have hv := I.valid
  have hA := sched_pos hv k
  obtain ⟨_, hM⟩ := grad_at I y (gapLevel_pos hv hA).le hy
  exact fd_error I y hM (fdStep_pos hv k) (fdStep_trust hv k) s

lemma xnext_pointwise (k : ℕ) (y : Point p.d) (hy : f y - f xstar ≤ gapLevel p (sched p k))
    (s : Fin p.d → Bool) :
    f (xnext p f k y s) ≤ f y -
      (if ⟪H (signVec s), signVec s⟫ ≤ 48 * p.r then
        stepSize p (sched p k) * clip (clipLevel p (sched p k)) (fdVal p f k y s) *
            ⟪gradient f y, signVec s⟫ -
          curvBound p (gapLevel p (sched p k)) *
            (stepSize p (sched p k) ^ 2 * clip (clipLevel p (sched p k)) (fdVal p f k y s) ^ 2 *
              ⟪H (signVec s), signVec s⟫)
      else 0) := by
  have hv := I.valid
  have hA := sched_pos hv k
  have hst := stepSize_pos hv hA
  have hL := Lp_pos hv
  have hr := hv.r_pos
  set lam := clipLevel p (sched p k)
  have hlam : 0 ≤ lam := by
    have := clipLevel_ge hv hA
    have := curvBound_pos hv (gapLevel_pos hv hA).le
    have : 0 ≤ 32 * curvBound p (gapLevel p (sched p k)) / Lp p := by positivity
    linarith
  unfold xnext
  rw [cand_eq]
  by_cases hq : ⟪H (signVec s), signVec s⟫ ≤ 48 * p.r
  · rw [ite_eq_left hq]
    obtain ⟨_, hM⟩ := grad_at I y (gapLevel_pos hv hA).le hy
    have htr : Lp p * (stepSize p (sched p k) * lam * Real.sqrt (48 * p.r)) ≤ 1 / 2 := by
      have hs48 : 0 < Real.sqrt (48 * p.r) := Real.sqrt_pos.mpr (by positivity)
      have e : Lp p * (stepSize p (sched p k) * lam * Real.sqrt (48 * p.r)) = 1 / 2 := by
        simp only [lam, clipLevel]; field_simp
      rw [e]
    have := xstep_descent I y s (c := clip lam (fdVal p f k y s)) hst.le hlam
      (clip_abs_le hlam (fdVal p f k y s)) hM htr hq
    linarith
  · rw [ite_eq_right hq]
    have := xstep_safe (p := p) (f := f) y s (stepSize p (sched p k)) (clip lam (fdVal p f k y s))
    linarith

lemma clip_conditions (k : ℕ) (y : Point p.d) (hy : f y - f xstar ≤ gapLevel p (sched p k)) :
    4 * ‖gradient f y‖ + etaOf p k ≤ clipLevel p (sched p k) ∧
      2 * etaOf p k ≤ clipLevel p (sched p k) ∧ 0 ≤ etaOf p k ∧
      0 < clipLevel p (sched p k) - etaOf p k := by
  have hv := I.valid
  have hA := sched_pos hv k
  have hL := Lp_pos hv
  have hMb := curvBound_pos hv (gapLevel_pos hv hA).le
  have hlam := clipLevel_ge hv hA
  obtain ⟨hN, _⟩ := grad_at I y (gapLevel_pos hv hA).le hy
  have hG : ‖gradient f y‖ ≤ dnorm H (gradient f y) := norm_le_dnorm I.geom _
  have hGb : Lp p * gradBound p (gapLevel p (sched p k)) ≤ curvBound p (gapLevel p (sched p k)) :=
    grad_le_curvBound hv
  have hL0M := L0_le_curvBound hv (gapLevel_pos hv hA).le
  have hη := fdStep_eta_L0 hv k
  have hη0 : 0 ≤ etaOf p k := by
    unfold etaOf
    have := fdStep_pos hv k
    have := dR_pos hv
    positivity
  have h1 : ‖gradient f y‖ ≤ curvBound p (gapLevel p (sched p k)) / Lp p := by
    rw [le_div_iff₀ hL]; nlinarith
  have h2 : etaOf p k ≤ 16 * (curvBound p (gapLevel p (sched p k)) / Lp p) := by
    unfold etaOf
    have : 16 * p.L0 / Lp p ≤ 16 * (curvBound p (gapLevel p (sched p k)) / Lp p) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL0M hL.le) (by norm_num)
    linarith
  have h3 : 32 * curvBound p (gapLevel p (sched p k)) / Lp p =
      32 * (curvBound p (gapLevel p (sched p k)) / Lp p) := by ring
  have hpos : 0 < curvBound p (gapLevel p (sched p k)) / Lp p := by positivity
  refine ⟨by linarith, by linarith, hη0, by linarith⟩

lemma xstep_expect (k : ℕ) (y : Point p.d) (hy : f y - f xstar ≤ gapLevel p (sched p k)) :
    (𝔼 s : Fin p.d → Bool, f (xnext p f k y s)) ≤
      f y - stepSize p (sched p k) * (‖gradient f y‖ ^ 2 / 4 - 17 / 4 * etaOf p k ^ 2) := by
  have hv := I.valid
  have hA := sched_pos hv k
  have hst := stepSize_pos hv hA
  have hr := hv.r_pos
  obtain ⟨hc1, hc2, hη0, hc3⟩ := clip_conditions I k y hy
  have hMbst := stepSize_curv hv hA
  set A := sched p k
  set st := stepSize p A
  set lam := clipLevel p A
  set Mb := curvBound p (gapLevel p A)
  set η := etaOf p k
  set g := gradient f y
  set G := ‖g‖
  have hrp := rp_pos hv
  have hrp2 := r_two_le_rp hv
  set D := fun s : Fin p.d → Bool => ⟪g, signVec s⟫
  set Dh := fun s : Fin p.d → Bool => fdVal p f k y s
  set c := fun s : Fin p.d → Bool => clip lam (Dh s)
  set q := fun s : Fin p.d → Bool => ⟪H (signVec s), signVec s⟫
  set Ic := fun s : Fin p.d → Bool => if 48 * p.r < q s then D s ^ 2 else 0
  set T := fun s : Fin p.d → Bool => if lam - η < |D s| then D s ^ 2 else 0
  have hfd : ∀ s, |Dh s - D s| ≤ η := fun s => fd_bound I k y hy s
  have hq0 : ∀ s, 0 ≤ q s := fun s => quad_nonneg I.geom _
  have hB : ∀ s, f (xnext p f k y s) ≤ f y -
      (st * (D s ^ 2 - Ic s - η * |D s| - T s) - Mb * (st ^ 2 * (c s ^ 2 * q s))) := by
    intro s
    have h := xnext_pointwise I k y hy s
    have hcl := clip_lower (c := lam) (η := η) (t := D s) (th := Dh s) hc2 hη0 (hfd s)
    have hT0 : 0 ≤ T s := by simp only [T]; split_ifs <;> positivity
    have hcq : 0 ≤ Mb * (st ^ 2 * (c s ^ 2 * q s)) := by
      have := curvBound_pos hv (gapLevel_pos hv hA).le
      have := hq0 s
      positivity
    by_cases hqs : q s ≤ 48 * p.r
    · rw [ite_eq_left hqs] at h
      have hIc : Ic s = 0 := by simp only [Ic]; rw [ite_eq_right (not_lt.mpr hqs)]
      rw [hIc]
      have e : st * clip lam (fdVal p f k y s) * ⟪g, signVec s⟫ = st * (c s * D s) := by
        simp only [c, Dh, D]; ring
      have e2 : Mb * (st ^ 2 * clip lam (fdVal p f k y s) ^ 2 * ⟪H (signVec s), signVec s⟫) =
          Mb * (st ^ 2 * (c s ^ 2 * q s)) := by simp only [c, Dh, q]; ring
      rw [e, e2] at h
      have : st * (D s ^ 2 - 0 - η * |D s| - T s) ≤ st * (c s * D s) := by
        apply mul_le_mul_of_nonneg_left _ hst.le
        have : clip lam (Dh s) * D s = c s * D s := rfl
        linarith
      linarith
    · rw [ite_eq_right hqs] at h
      have hIc : Ic s = D s ^ 2 := by simp only [Ic]; rw [ite_eq_left (not_le.mp hqs)]
      rw [hIc]
      have : st * (D s ^ 2 - D s ^ 2 - η * |D s| - T s) ≤ 0 := by
        have := abs_nonneg (D s)
        have : D s ^ 2 - D s ^ 2 - η * |D s| - T s ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos hst.le this
      linarith
  have hEB := Finset.expect_le_expect (s := Finset.univ) (fun s _ => hB s)
  have hR : (𝔼 s : Fin p.d → Bool, (f y -
      (st * (D s ^ 2 - Ic s - η * |D s| - T s) - Mb * (st ^ 2 * (c s ^ 2 * q s))))) =
      f y - (st * ((𝔼 s : Fin p.d → Bool, D s ^ 2) - (𝔼 s : Fin p.d → Bool, Ic s) -
        η * (𝔼 s : Fin p.d → Bool, |D s|) - (𝔼 s : Fin p.d → Bool, T s)) -
        Mb * (st ^ 2 * (𝔼 s : Fin p.d → Bool, c s ^ 2 * q s))) := by
    rw [Finset.expect_sub_distrib, Fintype.expect_const, Finset.expect_sub_distrib,
      ← Finset.mul_expect, ← Finset.mul_expect, ← Finset.mul_expect,
      Finset.expect_sub_distrib, Finset.expect_sub_distrib, Finset.expect_sub_distrib,
      ← Finset.mul_expect]
  rw [hR] at hEB
  have hD2 : (𝔼 s : Fin p.d → Bool, D s ^ 2) = G ^ 2 := expect_inner_vec_sq g
  have hD4 : (𝔼 s : Fin p.d → Bool, D s ^ 4) ≤ 3 * (G ^ 2) ^ 2 := expect_inner_vec_four g
  have hEq : (𝔼 s : Fin p.d → Bool, q s) ≤ p.r := expect_quad_le I
  have hInd : (𝔼 s : Fin p.d → Bool, if 48 * p.r < q s then (1 : ℝ) else 0) ≤ 1 / 48 := by
    have h := expect_indicator_le q hq0 (show (0 : ℝ) < 48 * p.r by positivity)
    have : (𝔼 s : Fin p.d → Bool, q s) / (48 * p.r) ≤ 1 / 48 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hIc : (𝔼 s : Fin p.d → Bool, Ic s) ≤ G ^ 2 / 4 := by
    have h := expect_sq_indicator_le D (fun s => 48 * p.r < q s)
    have h1 : Real.sqrt (𝔼 s : Fin p.d → Bool, D s ^ 4) ≤ Real.sqrt 3 * G ^ 2 := by
      calc Real.sqrt (𝔼 s : Fin p.d → Bool, D s ^ 4) ≤ Real.sqrt (3 * (G ^ 2) ^ 2) :=
            Real.sqrt_le_sqrt hD4
        _ = Real.sqrt 3 * G ^ 2 := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (sq_nonneg _)]
    have h2 : Real.sqrt (𝔼 s : Fin p.d → Bool, if 48 * p.r < q s then (1 : ℝ) else 0) ≤
        Real.sqrt (1 / 48) := Real.sqrt_le_sqrt hInd
    have h3 : Real.sqrt 3 * Real.sqrt (1 / 48) = 1 / 4 := by
      rw [← Real.sqrt_mul (by norm_num)]
      rw [show (3 : ℝ) * (1 / 48) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h4 : Real.sqrt (𝔼 s : Fin p.d → Bool, D s ^ 4) *
        Real.sqrt (𝔼 s : Fin p.d → Bool, if 48 * p.r < q s then (1 : ℝ) else 0) ≤
        Real.sqrt 3 * G ^ 2 * Real.sqrt (1 / 48) :=
      mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    have : Real.sqrt 3 * G ^ 2 * Real.sqrt (1 / 48) = G ^ 2 / 4 := by
      rw [mul_comm (Real.sqrt 3), mul_assoc, h3]; ring
    have hIceq : (𝔼 s : Fin p.d → Bool, Ic s) =
        𝔼 s : Fin p.d → Bool, if 48 * p.r < q s then D s ^ 2 else 0 := rfl
    linarith
  have hAbs : (𝔼 s : Fin p.d → Bool, |D s|) ≤ G := by
    have h := expect_abs_le_sqrt D
    rw [hD2, Real.sqrt_sq (norm_nonneg _)] at h
    exact h
  have hT : (𝔼 s : Fin p.d → Bool, T s) ≤ 3 * G ^ 2 / 16 := by
    have h := expect_sq_tail_le D hc3
    have h1 : (𝔼 s : Fin p.d → Bool, D s ^ 4) / (lam - η) ^ 2 ≤ 3 * (G ^ 2) ^ 2 / (lam - η) ^ 2 :=
      div_le_div_of_nonneg_right hD4 (sq_nonneg _)
    have h2 : 3 * (G ^ 2) ^ 2 / (lam - η) ^ 2 ≤ 3 * G ^ 2 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h16 : 16 * G ^ 2 ≤ (lam - η) ^ 2 := by
        have : 4 * G ≤ lam - η := by linarith
        have h0 : 0 ≤ 4 * G := by positivity
        nlinarith
      nlinarith [sq_nonneg G]
    have hTeq : (𝔼 s : Fin p.d → Bool, T s) =
        𝔼 s : Fin p.d → Bool, if lam - η < |D s| then D s ^ 2 else 0 := rfl
    linarith
  have hcq : (𝔼 s : Fin p.d → Bool, c s ^ 2 * q s) ≤ 2 * (G ^ 2 * (p.r + 2)) + 2 * η ^ 2 * p.r := by
    have hpt : ∀ s, c s ^ 2 * q s ≤ 2 * (D s ^ 2 * q s) + 2 * η ^ 2 * q s := by
      intro s
      have hcl : |c s| ≤ |Dh s| := clip_abs_le_abs (by linarith) _
      have h1 : c s ^ 2 ≤ Dh s ^ 2 := by
        rw [← sq_abs (c s), ← sq_abs (Dh s)]
        exact pow_le_pow_left₀ (abs_nonneg _) hcl 2
      have h2 : Dh s ^ 2 ≤ 2 * D s ^ 2 + 2 * η ^ 2 := sq_le_of_abs_sub (hfd s)
      have := hq0 s
      nlinarith
    have h := Finset.expect_le_expect (s := Finset.univ) (fun s _ => hpt s)
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at h
    have h2 := expect_D2q_le I g
    have h3 : 2 * η ^ 2 * (𝔼 s : Fin p.d → Bool, q s) ≤ 2 * η ^ 2 * p.r :=
      mul_le_mul_of_nonneg_left hEq (by positivity)
    have h4 : 2 * (𝔼 s : Fin p.d → Bool, D s ^ 2 * q s) ≤ 2 * (G ^ 2 * (p.r + 2)) := by
      have : (𝔼 s : Fin p.d → Bool, D s ^ 2 * q s) =
          𝔼 s : Fin p.d → Bool, ⟪g, signVec s⟫ ^ 2 * ⟪H (signVec s), signVec s⟫ := rfl
      linarith
    linarith
  have hfin := xstep_algebra (G := G) (η := η) hst hrp hMbst hrp2
  have hE1 : st * (G ^ 2 - G ^ 2 / 4 - η * G - 3 * G ^ 2 / 16) ≤
      st * ((𝔼 s : Fin p.d → Bool, D s ^ 2) - (𝔼 s : Fin p.d → Bool, Ic s) -
        η * (𝔼 s : Fin p.d → Bool, |D s|) - (𝔼 s : Fin p.d → Bool, T s)) := by
    apply mul_le_mul_of_nonneg_left _ hst.le
    rw [hD2]
    have := mul_le_mul_of_nonneg_left hAbs hη0
    linarith
  have hE2 : Mb * (st ^ 2 * (𝔼 s : Fin p.d → Bool, c s ^ 2 * q s)) ≤
      Mb * (st ^ 2 * (2 * (G ^ 2 * (p.r + 2)) + 2 * η ^ 2 * p.r)) := by
    apply mul_le_mul_of_nonneg_left _ (curvBound_pos hv (gapLevel_pos hv hA).le).le
    exact mul_le_mul_of_nonneg_left hcq (sq_nonneg _)
  linarith

lemma zstep_expect (k : ℕ) (y z : Point p.d) (hy : f y - f xstar ≤ gapLevel p (sched p k)) :
    (𝔼 s : Fin p.d → Bool, ‖znext p f k y z s - xstar‖ ^ 2) ≤
      ‖z - xstar‖ ^ 2 - 2 * weight p (sched p k) * ⟪gradient f y, z - xstar⟫ +
        2 * weight p (sched p k) * etaOf p k * ‖z - xstar‖ +
        2 * weight p (sched p k) ^ 2 * p.d * (‖gradient f y‖ ^ 2 + etaOf p k ^ 2) := by
  have hv := I.valid
  have hA := sched_pos hv k
  have ha := weight_pos hv hA
  obtain ⟨_, _, hη0, _⟩ := clip_conditions I k y hy
  set a := weight p (sched p k)
  set η := etaOf p k
  set g := gradient f y
  set w := z - xstar
  have hpt : ∀ s : Fin p.d → Bool, ‖znext p f k y z s - xstar‖ ^ 2 ≤
      ‖w‖ ^ 2 - 2 * a * (⟪g, signVec s⟫ * ⟪w, signVec s⟫) + 2 * a * η * |⟪w, signVec s⟫| +
        a ^ 2 * p.d * (2 * ⟪g, signVec s⟫ ^ 2 + 2 * η ^ 2) := by
    intro s
    have hfd := fd_bound I k y hy s
    have e : znext p f k y z s - xstar = w - (a * fdVal p f k y s) • signVec s := by
      rw [znext_eq]; simp only [w]; abel
    rw [e, norm_sub_sq_real, norm_smul, mul_pow, norm_signVec (p := p) s, Real.sq_sqrt (dR_pos hv).le,
      real_inner_smul_right, Real.norm_eq_abs, sq_abs]
    have h1 : -(a * fdVal p f k y s * ⟪w, signVec s⟫) ≤
        -(a * (⟪g, signVec s⟫ * ⟪w, signVec s⟫)) + a * η * |⟪w, signVec s⟫| := by
      have h2 : |(fdVal p f k y s - ⟪g, signVec s⟫) * ⟪w, signVec s⟫| ≤ η * |⟪w, signVec s⟫| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hfd (abs_nonneg _)
      have h3 := neg_abs_le ((fdVal p f k y s - ⟪g, signVec s⟫) * ⟪w, signVec s⟫)
      have h4 : a * (-(η * |⟪w, signVec s⟫|)) ≤ a * ((fdVal p f k y s - ⟪g, signVec s⟫) * ⟪w, signVec s⟫) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
      nlinarith
    have h5 : fdVal p f k y s ^ 2 ≤ 2 * ⟪g, signVec s⟫ ^ 2 + 2 * η ^ 2 := sq_le_of_abs_sub hfd
    have h6 : (a * fdVal p f k y s) ^ 2 * p.d ≤ a ^ 2 * p.d * (2 * ⟪g, signVec s⟫ ^ 2 + 2 * η ^ 2) := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_left h5 (show 0 ≤ a ^ 2 * p.d by have := dR_pos hv; positivity)
      nlinarith
    nlinarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun s _ => hpt s)
  have hR : (𝔼 s : Fin p.d → Bool, (‖w‖ ^ 2 - 2 * a * (⟪g, signVec s⟫ * ⟪w, signVec s⟫) +
      2 * a * η * |⟪w, signVec s⟫| + a ^ 2 * p.d * (2 * ⟪g, signVec s⟫ ^ 2 + 2 * η ^ 2))) =
      ‖w‖ ^ 2 - 2 * a * (𝔼 s : Fin p.d → Bool, ⟪g, signVec s⟫ * ⟪w, signVec s⟫) +
        2 * a * η * (𝔼 s : Fin p.d → Bool, |⟪w, signVec s⟫|) +
        a ^ 2 * p.d * (2 * (𝔼 s : Fin p.d → Bool, ⟪g, signVec s⟫ ^ 2) + 2 * η ^ 2) := by
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Finset.expect_sub_distrib,
      Fintype.expect_const, ← Finset.mul_expect, ← Finset.mul_expect, ← Finset.mul_expect,
      Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
  rw [hR, expect_inner_vec_mul, expect_inner_vec_sq] at h
  have habs : (𝔼 s : Fin p.d → Bool, |⟪w, signVec s⟫|) ≤ ‖w‖ := by
    have := expect_abs_le_sqrt (fun s : Fin p.d → Bool => ⟪w, signVec s⟫)
    rwa [expect_inner_vec_sq, Real.sqrt_sq (norm_nonneg _)] at this
  have : 2 * a * η * (𝔼 s : Fin p.d → Bool, |⟪w, signVec s⟫|) ≤ 2 * a * η * ‖w‖ :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  nlinarith

omit I in
lemma xnext_eq_acc (k : ℕ) (y : Point p.d) (s : Fin p.d → Bool) :
    xnext p f k y s = y - (stepSize p (sched p k) * clip (clipLevel p (sched p k)) (fdVal p f k y s) *
      (if f (cand p f k y s) ≤ f y then 1 else 0)) • signVec s := by
  unfold xnext
  split_ifs with h
  · rw [mul_one, cand_eq]
  · simp

lemma lag_expect (k : ℕ) (x z pt : Point p.d) (hy : f (extrapolate p k x z) - f xstar ≤
      gapLevel p (sched p k)) :
    (𝔼 s : Fin p.d → Bool, hnorm H (xnext p f k (extrapolate p k x z) s - extrapolate p k pt z) ^ 2) ≤
      ((sched p k / (sched p k + weight p (sched p k))) ^ 2 +
          weight p (sched p k) / sched p k / 2) * hnorm H (x - pt) ^ 2 +
        4 / (weight p (sched p k) / sched p k) * stepSize p (sched p k) ^ 2 *
          (‖gradient f (extrapolate p k x z)‖ ^ 2 + etaOf p k ^ 2) +
        stepSize p (sched p k) ^ 2 * (2 * ‖gradient f (extrapolate p k x z)‖ ^ 2 * (p.r + 2) +
          2 * etaOf p k ^ 2 * p.r) := by
  have hv := I.valid
  have hA := sched_pos hv k
  have ha := weight_pos hv hA
  have hst := stepSize_pos hv hA
  set y := extrapolate p k x z
  obtain ⟨_, hc2, hη0, _⟩ := clip_conditions I k y hy
  set A := sched p k
  set a := weight p A
  set st := stepSize p A
  set lam := clipLevel p A
  set η := etaOf p k
  set g := gradient f y
  set G := ‖g‖
  set e := x - pt
  set ρ := A / (A + a)
  set θ := a / A
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hθ : 0 < θ := by positivity
  have hlam0 : 0 ≤ lam := by linarith
  set κ := fun s : Fin p.d → Bool =>
    st * clip lam (fdVal p f k y s) * (if f (cand p f k y s) ≤ f y then 1 else 0)
  have hdiff : ∀ s, xnext p f k y s - extrapolate p k pt z = ρ • e - κ s • signVec s := by
    intro s
    rw [xnext_eq_acc k y s]
    simp only [y, extrapolate, κ, e, ρ]
    module
  have hpt : ∀ s, hnorm H (xnext p f k y s - extrapolate p k pt z) ^ 2 =
      ρ ^ 2 * hnorm H e ^ 2 - 2 * ρ * (κ s * ⟪H e, signVec s⟫) +
        κ s ^ 2 * ⟪H (signVec s), signVec s⟫ := by
    intro s
    rw [hdiff s, hnorm_sq I.geom, hnorm_sq I.geom, sub_eq_add_neg, ← neg_smul, quad_add I.geom,
      quad_smul , quad_smul , ContinuousLinearMap.map_smul, real_inner_smul_left,
      real_inner_smul_right]
    ring
  have hκ2 : ∀ s, κ s ^ 2 ≤ st ^ 2 * fdVal p f k y s ^ 2 := by
    intro s
    simp only [κ]
    have hcl := clip_abs_le_abs hlam0 (fdVal p f k y s)
    have h1 : clip lam (fdVal p f k y s) ^ 2 ≤ fdVal p f k y s ^ 2 := by
      rw [← sq_abs (clip _ _), ← sq_abs (fdVal p f k y s)]
      exact pow_le_pow_left₀ (abs_nonneg _) hcl 2
    split_ifs
    · rw [mul_one, mul_pow]; exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    · simp; positivity
  have hfd2 : ∀ s, fdVal p f k y s ^ 2 ≤ 2 * ⟪g, signVec s⟫ ^ 2 + 2 * η ^ 2 :=
    fun s => sq_le_of_abs_sub (fd_bound I k y hy s)
  have hE := Finset.expect_le_expect (s := Finset.univ) (fun s _ => le_of_eq (hpt s))
  have hκsq : (𝔼 s : Fin p.d → Bool, κ s ^ 2) ≤ st ^ 2 * (2 * G ^ 2 + 2 * η ^ 2) := by
    have h := Finset.expect_le_expect (s := Finset.univ)
      (fun s _ => (hκ2 s).trans (mul_le_mul_of_nonneg_left (hfd2 s) (sq_nonneg st)))
    rw [← Finset.mul_expect, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const,
      expect_inner_vec_sq] at h
    exact h
  have hcross : -(𝔼 s : Fin p.d → Bool, κ s * ⟪H e, signVec s⟫) ≤
      st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e := by
    have h := expect_mul_le_sqrt (fun s => -κ s) (fun s => ⟪H e, signVec s⟫)
    simp only [neg_mul, neg_sq, Finset.expect_neg_distrib] at h
    rw [expect_inner_vec_sq] at h
    have h1 : Real.sqrt (𝔼 s : Fin p.d → Bool, κ s ^ 2) ≤ st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) := by
      calc Real.sqrt (𝔼 s : Fin p.d → Bool, κ s ^ 2) ≤ Real.sqrt (st ^ 2 * (2 * G ^ 2 + 2 * η ^ 2)) :=
            Real.sqrt_le_sqrt hκsq
        _ = st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hst.le]
    have h2 : Real.sqrt (‖H e‖ ^ 2) ≤ hnorm H e := by
      rw [Real.sqrt_sq (norm_nonneg _)]; exact norm_H_le I.geom e
    calc -(𝔼 s : Fin p.d → Bool, κ s * ⟪H e, signVec s⟫) ≤
          Real.sqrt (𝔼 s : Fin p.d → Bool, κ s ^ 2) * Real.sqrt (‖H e‖ ^ 2) := h
      _ ≤ st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  have hquad : (𝔼 s : Fin p.d → Bool, κ s ^ 2 * ⟪H (signVec s), signVec s⟫) ≤
      st ^ 2 * (2 * G ^ 2 * (p.r + 2) + 2 * η ^ 2 * p.r) := by
    have hpw : ∀ s, κ s ^ 2 * ⟪H (signVec s), signVec s⟫ ≤
        st ^ 2 * (2 * (⟪g, signVec s⟫ ^ 2 * ⟪H (signVec s), signVec s⟫) +
          2 * η ^ 2 * ⟪H (signVec s), signVec s⟫) := by
      intro s
      have hq := quad_nonneg I.geom (signVec s)
      have := (hκ2 s).trans (mul_le_mul_of_nonneg_left (hfd2 s) (sq_nonneg st))
      have := mul_le_mul_of_nonneg_right this hq
      nlinarith
    have h := Finset.expect_le_expect (s := Finset.univ) (fun s _ => hpw s)
    rw [← Finset.mul_expect, Finset.expect_add_distrib, ← Finset.mul_expect,
      ← Finset.mul_expect] at h
    have h2 := expect_D2q_le I g
    have h3 := expect_quad_le I
    have h4 : st ^ 2 * (2 * (𝔼 s : Fin p.d → Bool, ⟪g, signVec s⟫ ^ 2 * ⟪H (signVec s), signVec s⟫) +
        2 * η ^ 2 * (𝔼 s : Fin p.d → Bool, ⟪H (signVec s), signVec s⟫)) ≤
        st ^ 2 * (2 * G ^ 2 * (p.r + 2) + 2 * η ^ 2 * p.r) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * η ^ 2 by positivity)
      nlinarith
    linarith
  have hR : (𝔼 s : Fin p.d → Bool, (ρ ^ 2 * hnorm H e ^ 2 - 2 * ρ * (κ s * ⟪H e, signVec s⟫) +
      κ s ^ 2 * ⟪H (signVec s), signVec s⟫)) =
      ρ ^ 2 * hnorm H e ^ 2 - 2 * ρ * (𝔼 s : Fin p.d → Bool, κ s * ⟪H e, signVec s⟫) +
        (𝔼 s : Fin p.d → Bool, κ s ^ 2 * ⟪H (signVec s), signVec s⟫) := by
    rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, Fintype.expect_const,
      ← Finset.mul_expect]
  rw [hR] at hE
  have hle0 := hnorm_nonneg' (H := H) e
  have hsq0 : 0 ≤ Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) := Real.sqrt_nonneg _
  have hsqsq := Real.sq_sqrt (show 0 ≤ 2 * G ^ 2 + 2 * η ^ 2 by positivity)
  have hyoung : 2 * ρ * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e) ≤
      θ / 2 * hnorm H e ^ 2 + 4 / θ * st ^ 2 * (G ^ 2 + η ^ 2) := by
    have h1 : 2 * ρ * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e) ≤
        2 * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e) := by
      have : 0 ≤ st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e := by positivity
      nlinarith
    have h2 : 2 * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e) ≤
        θ / 2 * hnorm H e ^ 2 + 2 / θ * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2)) ^ 2 := by
      have hsq := sq_nonneg (θ / 2 * hnorm H e - st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2))
      have e1 : θ / 2 * hnorm H e ^ 2 + 2 / θ * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2)) ^ 2 -
          2 * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e) =
          2 / θ * (θ / 2 * hnorm H e - st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2)) ^ 2 := by
        field_simp; ring
      have : 0 ≤ 2 / θ * (θ / 2 * hnorm H e - st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2)) ^ 2 := by
        positivity
      linarith
    have h3 : 2 / θ * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2)) ^ 2 = 4 / θ * st ^ 2 * (G ^ 2 + η ^ 2) := by
      rw [mul_pow, hsqsq]; ring
    linarith
  have hρ2 : ρ ^ 2 * hnorm H e ^ 2 ≤ ρ ^ 2 * hnorm H e ^ 2 := le_rfl
  have hcross' : -2 * ρ * (𝔼 s : Fin p.d → Bool, κ s * ⟪H e, signVec s⟫) ≤
      2 * ρ * (st * Real.sqrt (2 * G ^ 2 + 2 * η ^ 2) * hnorm H e) := by
    have := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 * ρ by positivity)
    linarith
  nlinarith

lemma potential_parts (k : ℕ) (x z pt : Point p.d)
    (hΨ : potential p f H xstar k x z pt ≤ 4 * p.R ^ 2) :
    f x - f xstar ≤ 4 * p.R ^ 2 / sched p k ∧ ‖z - xstar‖ ≤ Real.sqrt 8 * p.R ∧
      lagWeight p (sched p k) * hnorm H (x - pt) ^ 2 ≤ 4 * p.R ^ 2 := by
  have hv := I.valid
  have hA := sched_pos hv k
  have hR := hv.R_pos
  have hf0 : 0 ≤ f x - f xstar := by
    have := I.min (Set.mem_univ x); simp only [Set.mem_ofPred_eq] at this; linarith
  have h1 : 0 ≤ sched p k * (f x - f xstar) := mul_nonneg hA.le hf0
  have h2 : 0 ≤ ‖z - xstar‖ ^ 2 / 2 := by positivity
  have h3 : 0 ≤ lagWeight p (sched p k) * hnorm H (x - pt) ^ 2 :=
    mul_nonneg (lagWeight_pos hv hA).le (sq_nonneg _)
  unfold potential at hΨ
  refine ⟨?_, ?_, by linarith⟩
  · rw [le_div_iff₀ hA]; linarith
  · have hz2 : ‖z - xstar‖ ^ 2 ≤ (Real.sqrt 8 * p.R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hz2

lemma ghost_bound (k : ℕ) (pt z : Point p.d) (hpt : ‖pt - xstar‖ ≤ Real.sqrt 8 * p.R)
    (hz : ‖z - xstar‖ ≤ Real.sqrt 8 * p.R) :
    ‖extrapolate p k pt z - xstar‖ ≤ Real.sqrt 8 * p.R := by
  have hv := I.valid
  have hA := sched_pos hv k
  have ha := weight_pos hv hA
  set A := sched p k
  set a := weight p A
  have e : extrapolate p k pt z - xstar =
      (A / (A + a)) • (pt - xstar) + (a / (A + a)) • (z - xstar) := by
    simp only [extrapolate]
    have : A / (A + a) + a / (A + a) = 1 := by field_simp
    rw [smul_sub, smul_sub]
    calc (A / (A + a)) • pt + (a / (A + a)) • z - xstar =
        (A / (A + a)) • pt + (a / (A + a)) • z - (A / (A + a) + a / (A + a)) • xstar := by
          rw [this, one_smul]
      _ = _ := by rw [add_smul]; abel
  rw [e]
  calc ‖(A / (A + a)) • (pt - xstar) + (a / (A + a)) • (z - xstar)‖ ≤
        ‖(A / (A + a)) • (pt - xstar)‖ + ‖(a / (A + a)) • (z - xstar)‖ := norm_add_le _ _
    _ = A / (A + a) * ‖pt - xstar‖ + a / (A + a) * ‖z - xstar‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity)]
    _ ≤ A / (A + a) * (Real.sqrt 8 * p.R) + a / (A + a) * (Real.sqrt 8 * p.R) :=
        add_le_add (mul_le_mul_of_nonneg_left hpt (by positivity))
          (mul_le_mul_of_nonneg_left hz (by positivity))
    _ = Real.sqrt 8 * p.R := by field_simp

lemma coupling (k : ℕ) (x z : Point p.d) :
    (sched p k + weight p (sched p k)) * (f (extrapolate p k x z) - f xstar) -
      sched p k * (f x - f xstar) ≤
        weight p (sched p k) * ⟪gradient f (extrapolate p k x z), z - xstar⟫ := by
  have hv := I.valid
  have hA := sched_pos hv k
  have ha := weight_pos hv hA
  have h1 := convex_lower I (extrapolate p k x z) (x - extrapolate p k x z)
  have h2 := convex_lower I (extrapolate p k x z) (xstar - extrapolate p k x z)
  rw [add_sub_cancel] at h1 h2
  have hkey : sched p k • (x - extrapolate p k x z) + weight p (sched p k) • (xstar - extrapolate p k x z) =
      -(weight p (sched p k) • (z - xstar)) := by
    simp only [extrapolate]
    have hAa : sched p k + weight p (sched p k) ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
  have hin : sched p k * ⟪gradient f (extrapolate p k x z), x - extrapolate p k x z⟫ +
      weight p (sched p k) * ⟪gradient f (extrapolate p k x z), xstar - extrapolate p k x z⟫ =
      -(weight p (sched p k) * ⟪gradient f (extrapolate p k x z), z - xstar⟫) := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hkey,
      inner_neg_right, real_inner_smul_right]
  nlinarith

lemma main_step (k : ℕ) (x z pt : Point p.d)
    (hΨ : potential p f H xstar k x z pt ≤ 4 * p.R ^ 2)
    (hpt : ‖pt - xstar‖ ≤ Real.sqrt 8 * p.R) :
    ‖extrapolate p k pt z - xstar‖ ≤ Real.sqrt 8 * p.R ∧
      (𝔼 s : Fin p.d → Bool, potential p f H xstar (k + 1)
        (xnext p f k (extrapolate p k x z) s) (znext p f k (extrapolate p k x z) z s)
        (extrapolate p k pt z)) ≤
        potential p f H xstar k x z pt + 9 * p.R ^ 2 / (32 * 2 ^ k) := by
  have hv := I.valid
  obtain ⟨hx, hz, he⟩ := potential_parts I k x z pt hΨ
  refine ⟨ghost_bound I k pt z hpt hz, ?_⟩
  have hA := sched_pos hv k
  have ha := weight_pos hv hA
  have hst := stepSize_pos hv hA
  have hR := hv.R_pos
  have hd := dR_pos hv
  have hr := hv.r_pos
  set y := extrapolate p k x z
  have hy := locality I k x z pt hx hz hpt he
  obtain ⟨_, _, hη0, _⟩ := clip_conditions I k y hy
  have hxs := xstep_expect I k y hy
  have hzs := zstep_expect I k y z hy
  have hls := lag_expect I k x z pt hy
  have hcp := coupling I k x z
  set A := sched p k
  set a := weight p A
  set st := stepSize p A
  set η := etaOf p k
  set g := gradient f y
  set G := ‖g‖
  set γ := lagWeight p A
  set γ' := lagWeight p (A + a)
  set ℓ2 := hnorm H (x - pt) ^ 2
  have hsucc : sched p (k + 1) = A + a := rfl
  have hE : (𝔼 s : Fin p.d → Bool, potential p f H xstar (k + 1) (xnext p f k y s)
      (znext p f k y z s) (extrapolate p k pt z)) =
      (A + a) * ((𝔼 s : Fin p.d → Bool, f (xnext p f k y s)) - f xstar) +
        (𝔼 s : Fin p.d → Bool, ‖znext p f k y z s - xstar‖ ^ 2) / 2 +
        γ' * (𝔼 s : Fin p.d → Bool, hnorm H (xnext p f k y s - extrapolate p k pt z) ^ 2) := by
    unfold potential
    rw [hsucc, Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
      ← Finset.mul_expect, Finset.expect_sub_distrib, Fintype.expect_const, Finset.expect_div]
  rw [hE]
  have hγdef : γ = a / (64 * st) := rfl
  have hγ' : γ' ≤ (1 + a / A) * γ := lagWeight_ratio hv hA
  have hγ0 : 0 < γ := lagWeight_pos hv hA
  have hγ'0 : 0 ≤ γ' := (lagWeight_pos hv (by positivity)).le
  have hθ4 : a / A ≤ 1 / 4 := by
    rw [div_le_iff₀ hA]; have := weight_le_quarter (p := p) hA; linarith
  have hcontr := contraction_aux hA ha hθ4
  have hw := weight_sq_le hv hA
  have hθr : a / A * (p.r + 2) ≤ 2 := by
    have h1 : a / A ≤ thetaCap p := by rw [div_le_iff₀ hA]; exact weight_le_cap (p := p)
    have := mul_le_mul_of_nonneg_right h1 (show 0 ≤ p.r + 2 by linarith)
    linarith [thetaCap_mul hv]
  have hcomb := combine_algebra (G := G) (η := η) (ℓ2 := ℓ2) (Dz := ‖z - xstar‖) hA ha hst
    (sq_nonneg _) hγ0 hd hr hγdef hγ' hcontr hw hθr
  have herr : 5 * ((A + a) * st) * η ^ 2 + a * η * ‖z - xstar‖ + a ^ 2 * p.d * η ^ 2 ≤
      9 * p.R ^ 2 / (32 * 2 ^ k) := by
    have hτ : 0 ≤ p.R / (32 * 2 ^ k) := by positivity
    have hτR : p.R / (32 * 2 ^ k) ≤ p.R := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have hW : 1 + (A + a) * st + a * Real.sqrt p.d + a ^ 2 * p.d ≤ errWeight p k := by
      unfold errWeight; rw [hsucc]
    have hηW : η ≤ p.R / (32 * 2 ^ k) / errWeight p k := by
      have := fdStep_eta_err hv k
      rw [div_div]; exact this
    have hDz : ‖z - xstar‖ ≤ 3 * p.R := by
      have h8 : Real.sqrt 8 ≤ 3 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      calc ‖z - xstar‖ ≤ Real.sqrt 8 * p.R := hz
        _ ≤ 3 * p.R := mul_le_mul_of_nonneg_right h8 hR.le
    have := error_aux (by positivity) ha.le (one_le_d hv) hη0 hDz hR hτ hτR hW hηW
    have e : 9 * (p.R / (32 * 2 ^ k) * p.R) = 9 * p.R ^ 2 / (32 * 2 ^ k) := by ring
    linarith
  have hxs' : (A + a) * ((𝔼 s : Fin p.d → Bool, f (xnext p f k y s)) - f xstar) ≤
      (A + a) * (f y - f xstar) - (A + a) * (st * (G ^ 2 / 4 - 17 / 4 * η ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hxs (show 0 ≤ A + a by positivity)
    linarith
  have hls' : γ' * (𝔼 s : Fin p.d → Bool, hnorm H (xnext p f k y s - extrapolate p k pt z) ^ 2) ≤
      γ' * (((A / (A + a)) ^ 2 + a / A / 2) * ℓ2 + 4 / (a / A) * st ^ 2 * (G ^ 2 + η ^ 2) +
        st ^ 2 * (2 * G ^ 2 * (p.r + 2) + 2 * η ^ 2 * p.r)) :=
    mul_le_mul_of_nonneg_left hls hγ'0
  unfold potential
  linarith

end

end OracleTemplate.MatrixGeneralizedZO
