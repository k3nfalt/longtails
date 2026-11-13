import LongTails.Algorithms.CompositeSherpa
import LongTails.Proofs.CompositeGeneralizedLocal
import LongTails.Proofs.SymmetricGeneralizedDescent
import LongTails.Proofs.RadiusFreeSherpaBasic

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeSherpa

open LongTails.Proofs.SymmetricGeneralizedDescent
open OracleTemplate.CompositeGeneralized (SymmetricSmooth)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Hyp (f ψ : E → ℝ) (g : E → E) (prox : ℝ → E → E → E) (L0 L1 M : ℝ) (xs : E) :
    Prop where
  hL0 : 0 < L0
  hL1 : 0 < L1
  hM : 0 ≤ M
  convex : ConvexOn ℝ univ f
  grad : ∀ x, HasGradientAt f (g x) x
  cont : Continuous g
  smooth : SymmetricSmooth g L0 L1
  ψconvex : ConvexOn ℝ univ ψ
  ψlip : ∀ x y, |ψ x - ψ y| ≤ M * ‖x - y‖
  proxSpec : ∀ a, 0 < a → ∀ z v,
    IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u) univ (prox a z v)
  min : IsMinOn (fun x => f x + ψ x) univ xs

variable {f ψ : E → ℝ} {g : E → E} {prox : ℝ → E → E → E} {L0 L1 M : ℝ} {xs : E}

lemma Hyp.ψ_sub_le (H : Hyp f ψ g prox L0 L1 M xs) (x y : E) : ψ x - ψ y ≤ M * ‖x - y‖ :=
  (le_abs_self _).trans (H.ψlip x y)

lemma Hyp.sSup_form (H : Hyp f ψ g prox L0 L1 M xs) (x y : E) :
    ‖g x - g y‖ ≤ (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖ := by
  apply H.smooth
  intro θ hθ
  apply le_csSup (RadiusFreeSherpa.segment_bddAbove H.cont x y)
  refine ⟨x + θ • (y - x), ?_, rfl⟩
  rw [segment_eq_image']
  exact ⟨θ, hθ, rfl⟩

lemma Hyp.subgrad (H : Hyp f ψ g prox L0 L1 M xs) (u : E) :
    ψ xs - ψ u ≤ ⟪g xs, u - xs⟫ :=
  CompositeGeneralized.optimality H.convex H.grad H.cont convex_univ H.ψconvex (mem_univ xs)
    H.min (mem_univ u)

lemma Hyp.gxs_le (H : Hyp f ψ g prox L0 L1 M xs) : ‖g xs‖ ≤ M := by
  by_contra hlt
  push Not at hlt
  have h := H.subgrad (xs - g xs)
  have hl := H.ψ_sub_le (xs - g xs) xs
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_self_eq_norm_sq] at h
  rw [sub_sub_cancel_left, norm_neg] at hl
  have hgpos : 0 < ‖g xs‖ := lt_of_le_of_lt H.hM hlt
  nlinarith [mul_lt_mul_of_pos_right hlt hgpos]

noncomputable def shifted (f : E → ℝ) (g : E → E) (xs : E) (x : E) : ℝ := f x - ⟪g xs, x⟫

noncomputable def shiftedGrad (g : E → E) (xs : E) (x : E) : E := g x - g xs

lemma Hyp.shifted_grad (H : Hyp f ψ g prox L0 L1 M xs) (x : E) :
    HasGradientAt (shifted f g xs) (shiftedGrad g xs x) x := by
  unfold shifted shiftedGrad
  have h1 := (H.grad x).hasFDerivAt
  have h2 : HasFDerivAt (fun y : E => ⟪g xs, y⟫) (innerSL ℝ (g xs)) x :=
    (innerSL ℝ (g xs)).hasFDerivAt
  have := h1.sub h2
  rw [hasGradientAt_iff_hasFDerivAt]
  convert this using 1
  ext w
  simp [InnerProductSpace.toDual_apply_apply]

lemma Hyp.shifted_convex (H : Hyp f ψ g prox L0 L1 M xs) :
    ConvexOn ℝ univ (shifted f g xs) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := H.convex.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [shifted, smul_eq_mul, inner_add_right, real_inner_smul_right] at h ⊢
  linarith

lemma Hyp.shifted_cont (H : Hyp f ψ g prox L0 L1 M xs) : Continuous (shiftedGrad g xs) :=
  H.cont.sub continuous_const

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma shiftedGrad_self (g : E → E) (xs : E) : shiftedGrad g xs xs = 0 := by
  simp [shiftedGrad]

lemma Hyp.shifted_min (H : Hyp f ψ g prox L0 L1 M xs) : IsMinOn (shifted f g xs) univ xs := by
  intro u _
  have h := Gradient.convex_support H.shifted_convex H.shifted_grad xs u
  rw [(shiftedGrad_self g xs), inner_zero_left] at h
  simp only [mem_ofPred_eq]
  linarith

lemma Hyp.shifted_norm_le (H : Hyp f ψ g prox L0 L1 M xs) (x : E) :
    ‖shiftedGrad g xs x‖ ≤ ‖g x‖ + M := by
  unfold shiftedGrad
  have := norm_sub_le (g x) (g xs)
  linarith [H.gxs_le]

lemma Hyp.shifted_norm_ge (H : Hyp f ψ g prox L0 L1 M xs) (x : E) :
    ‖g x‖ - M ≤ ‖shiftedGrad g xs x‖ := by
  unfold shiftedGrad
  have := norm_sub_norm_le (g x) (g xs)
  linarith [H.gxs_le]

lemma Hyp.shifted_sSup_form (H : Hyp f ψ g prox L0 L1 M xs) (x y : E) :
    ‖shiftedGrad g xs x - shiftedGrad g xs y‖ ≤
      (L0 + L1 * M + L1 * sSup ((fun z => ‖shiftedGrad g xs z‖) '' segment ℝ x y)) * ‖x - y‖ := by
  have he : shiftedGrad g xs x - shiftedGrad g xs y = g x - g y := by unfold shiftedGrad; abel
  rw [he]
  have hb : BddAbove ((fun z => ‖shiftedGrad g xs z‖) '' segment ℝ x y) :=
    RadiusFreeSherpa.segment_bddAbove H.shifted_cont x y
  have h := H.smooth x y (sSup ((fun z => ‖shiftedGrad g xs z‖) '' segment ℝ x y) + M) ?_
  · convert h using 2; ring
  intro θ hθ
  have hmem : x + θ • (y - x) ∈ segment ℝ x y := by
    rw [segment_eq_image']; exact ⟨θ, hθ, rfl⟩
  have h1 : ‖shiftedGrad g xs (x + θ • (y - x))‖ ≤
      sSup ((fun z => ‖shiftedGrad g xs z‖) '' segment ℝ x y) := le_csSup hb ⟨_, hmem, rfl⟩
  have h2 : ‖g (x + θ • (y - x))‖ ≤ ‖shiftedGrad g xs (x + θ • (y - x))‖ + M := by
    unfold shiftedGrad
    have := norm_sub_norm_le (g (x + θ • (y - x))) (g xs)
    linarith [H.gxs_le]
  linarith

lemma phiFun_nonneg {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hG : 0 ≤ G) :
    0 ≤ phiFun L0 L1 G := by
  unfold phiFun
  have := RadiusFreeSherpa.entropy_nonneg (u := L1 * G / L0) (by positivity)
  positivity

lemma entropy_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 + u) * Real.log (1 + u) - u ≤ (1 + v) * Real.log (1 + v) - v := by
  have h1u : 0 < 1 + u := by linarith
  have h1v : 0 < 1 + v := by linarith
  have hlog : Real.log ((1 + u) / (1 + v)) ≤ (1 + u) / (1 + v) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div h1u.ne' h1v.ne'] at hlog
  have hlu : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hfrac : (1 + v) * ((1 + u) / (1 + v) - 1) = u - v := by field_simp; ring
  have h2 : (1 + v) * (Real.log (1 + u) - Real.log (1 + v)) ≤ u - v := by
    rw [← hfrac]; exact mul_le_mul_of_nonneg_left hlog h1v.le
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) hlu]

lemma phiFun_mono {L0 L1 G G' : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hG : 0 ≤ G) (hGG : G ≤ G') :
    phiFun L0 L1 G ≤ phiFun L0 L1 G' := by
  unfold phiFun
  have h := entropy_mono (u := L1 * G / L0) (v := L1 * G' / L0) (by positivity)
    (by gcongr)
  have : 0 ≤ L0 / L1 ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left h this

lemma Hyp.phi_inequality (H : Hyp f ψ g prox L0 L1 M xs) (y : E)
    (hy : 0 < ‖shiftedGrad g xs y‖) :
    f y + ⟪g y, xs - y⟫ + phiFun (L0 + L1 * M) L1 ‖shiftedGrad g xs y‖ ≤ f xs := by
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  set L0' := L0 + L1 * M with hL0'def
  have hL0' : 0 < L0' := by rw [hL0'def]; positivity
  set G := ‖shiftedGrad g xs y‖ with hGdef
  set s := L1 * G / L0' with hs
  have hs0 : 0 < s := div_pos (mul_pos hL1 hy) hL0'
  have h1s : 0 < 1 + s := by linarith
  let v : E := G⁻¹ • shiftedGrad g xs y
  have hv : ‖v‖ = 1 := by
    show ‖G⁻¹ • shiftedGrad g xs y‖ = 1
    rw [norm_smul, norm_inv, norm_norm, ← hGdef, inv_mul_cancel₀ hy.ne']
  have hi : ⟪shiftedGrad g xs y, v⟫ = G := by
    show ⟪shiftedGrad g xs y, G⁻¹ • shiftedGrad g xs y⟫ = G
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← hGdef, pow_two, ← mul_assoc,
      inv_mul_cancel₀ hy.ne', one_mul]
  set T := Real.log (1 + s) / L1 with hT
  have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg (by linarith)) hL1.le
  have hgrow := objective_ray_growth H.shifted_grad H.shifted_cont hL1 H.shifted_sSup_form xs v
    (shiftedGrad_self g xs) hv hT0
  have hexp : Real.exp (L1 * T) = 1 + s := by
    rw [hT, mul_div_cancel₀ _ hL1.ne', Real.exp_log h1s]
  rw [hexp] at hgrow
  have hsupp := Gradient.convex_support H.shifted_convex H.shifted_grad y (xs + T • v)
  have he : xs + T • v - y = (xs - y) + T • v := by abel
  rw [he, inner_add_right, real_inner_smul_right, hi] at hsupp
  have hTG : T * G = L0' / L1 ^ 2 * (s * Real.log (1 + s)) := by
    rw [hT, hs]; field_simp
  have hphi : phiFun L0' L1 G = L0' / L1 ^ 2 * ((1 + s) * Real.log (1 + s) - s) := by
    unfold phiFun; rw [← hs]
  have hL1T : L1 * T = Real.log (1 + s) := by rw [hT]; field_simp
  rw [hL1T] at hgrow
  rw [hphi]
  have hsh1 : shifted f g xs (xs + T • v) = f (xs + T • v) - ⟪g xs, xs⟫ - T * ⟪g xs, v⟫ := by
    unfold shifted; rw [inner_add_right, real_inner_smul_right]; ring
  have hsh2 : shifted f g xs xs = f xs - ⟪g xs, xs⟫ := rfl
  have hsh3 : shifted f g xs y = f y - ⟪g xs, y⟫ := rfl
  have hsg : ⟪shiftedGrad g xs y, xs - y⟫ = ⟪g y, xs - y⟫ - ⟪g xs, xs - y⟫ := by
    unfold shiftedGrad; rw [inner_sub_left]
  rw [hsh1, hsh2] at hgrow
  rw [hsh1, hsh3, hsg] at hsupp
  have hxsy : ⟪g xs, xs - y⟫ = ⟪g xs, xs⟫ - ⟪g xs, y⟫ := inner_sub_right _ _ _
  nlinarith [hgrow, hsupp, hTG, hxsy]


lemma Hyp.prox_three (H : Hyp f ψ g prox L0 L1 M xs) {a : ℝ} (ha : 0 < a) (z v u : E) :
    a * (⟪v, prox a z v - u⟫ + ψ (prox a z v) - ψ u) ≤
      ‖z - u‖ ^ 2 / 2 - ‖prox a z v - u‖ ^ 2 / 2 - ‖prox a z v - z‖ ^ 2 / 2 :=
  CompositeGeneralized.prox_three_point convex_univ H.ψconvex ha (mem_univ _)
    (H.proxSpec a ha z v) (mem_univ u)

noncomputable def proxSub (prox : ℝ → E → E → E) (a : ℝ) (z v : E) : E :=
  (1 / a) • (z - prox a z v) - v

lemma Hyp.prox_subgrad (H : Hyp f ψ g prox L0 L1 M xs) {a : ℝ} (ha : 0 < a) (z v u : E) :
    ψ (prox a z v) + ⟪proxSub prox a z v, u - prox a z v⟫ ≤ ψ u := by
  have h := H.prox_three ha z v u
  set p := prox a z v
  have hid : ‖z - u‖ ^ 2 / 2 - ‖p - u‖ ^ 2 / 2 - ‖p - z‖ ^ 2 / 2 = -⟪z - p, u - p⟫ := by
    have e : z - u = (z - p) - (u - p) := by abel
    rw [e, norm_sub_sq_real, norm_sub_rev p z, norm_sub_rev p u]
    ring
  rw [hid] at h
  unfold proxSub
  rw [inner_sub_left, real_inner_smul_left]
  have hinner : ⟪v, p - u⟫ = -⟪v, u - p⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hinner] at h
  have h' : ⟪z - p, u - p⟫ ≤ a * (ψ u - ψ p + ⟪v, u - p⟫) := by linarith
  have := div_le_div_of_nonneg_right h' ha.le
  rw [mul_div_cancel_left₀ _ ha.ne'] at this
  have e : 1 / a * ⟪z - p, u - p⟫ = ⟪z - p, u - p⟫ / a := by ring
  rw [e]
  linarith

lemma Hyp.proxSub_norm_le (H : Hyp f ψ g prox L0 L1 M xs) {a : ℝ} (ha : 0 < a) (z v : E) :
    ‖proxSub prox a z v‖ ≤ M := by
  have h := H.prox_subgrad ha z v (prox a z v + proxSub prox a z v)
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h
  have hl := H.ψ_sub_le (prox a z v + proxSub prox a z v) (prox a z v)
  rw [add_sub_cancel_left] at hl
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ‖proxSub prox a z v‖ := lt_of_le_of_lt H.hM hlt
  nlinarith [mul_lt_mul_of_pos_right hlt hpos]

lemma Hyp.prox_nonexpansive (H : Hyp f ψ g prox L0 L1 M xs) {a : ℝ} (ha : 0 < a)
    (z v z' v' : E) :
    ‖prox a z v - prox a z' v'‖ ≤ ‖(z - a • v) - (z' - a • v')‖ := by
  have h1 := H.prox_subgrad ha z v (prox a z' v')
  have h2 := H.prox_subgrad ha z' v' (prox a z v)
  set p := prox a z v with hp
  set p' := prox a z' v' with hp'
  set X := (z - a • v) - (z' - a • v') with hX
  have hsum : ⟪proxSub prox a z v - proxSub prox a z' v', p' - p⟫ ≤ 0 := by
    rw [inner_sub_left]
    have e : ⟪proxSub prox a z' v', p - p'⟫ = -⟪proxSub prox a z' v', p' - p⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at h2
    linarith
  have hw : proxSub prox a z v - proxSub prox a z' v' = (1 / a) • X - (1 / a) • (p - p') := by
    have e : ∀ u : E, (1 / a) • (a • u) = u := fun u => by
      rw [smul_smul, one_div_mul_cancel ha.ne', one_smul]
    simp only [proxSub, p, p', X, smul_sub, e]
    abel
  rw [hw, inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hsum
  have hpp : ⟪p - p', p' - p⟫ = -‖p - p'‖ ^ 2 := by
    rw [← neg_sub p p', inner_neg_right, real_inner_self_eq_norm_sq]
  have e2 : ⟪X, p' - p⟫ = -⟪X, p - p'⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hpp, e2] at hsum
  have ha' : 0 < 1 / a := by positivity
  have h3 : 1 / a * (‖p - p'‖ ^ 2 - ⟪X, p - p'⟫) ≤ 0 := by linarith
  have h5 : ‖p - p'‖ ^ 2 - ⟪X, p - p'⟫ ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos ha' hc
    linarith
  have hcs : ⟪X, p - p'⟫ ≤ ‖X‖ * ‖p - p'‖ := real_inner_le_norm _ _
  have hn : 0 ≤ ‖p - p'‖ := norm_nonneg _
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have key : ‖p - p'‖ * ‖p - p'‖ ≤ ‖X‖ * ‖p - p'‖ := by rw [← pow_two]; linarith
    exact le_of_mul_le_mul_right key hpos

lemma Hyp.prox_fixed (H : Hyp f ψ g prox L0 L1 M xs) {a : ℝ} (ha : 0 < a) :
    prox a xs (g xs) = xs := by
  have h := H.prox_three ha xs (g xs) xs
  set p := prox a xs (g xs)
  rw [sub_self, norm_zero] at h
  have hs := H.subgrad p
  have hnn : 0 ≤ ⟪g xs, p - xs⟫ + ψ p - ψ xs := by linarith
  have h2 : 0 ≤ a * (⟪g xs, p - xs⟫ + ψ p - ψ xs) := mul_nonneg ha.le hnn
  have h3 : ‖p - xs‖ ^ 2 ≤ 0 := by nlinarith
  have h4 : ‖p - xs‖ = 0 := by nlinarith [norm_nonneg (p - xs)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

lemma curv_pos {L0 L1 M G : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hG : 0 ≤ G) :
    0 < curv L0 L1 M G := by unfold curv; positivity

lemma Hyp.move_bounds (H : Hyp f ψ g prox L0 L1 M xs) (y : E) :
    1 / (4 * curv L0 L1 M ‖g y‖) * (‖g y‖ - M) ≤ ‖prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y) - y‖ ∧
      ‖prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y) - y‖ ≤ 1 / (4 * curv L0 L1 M ‖g y‖) * (‖g y‖ + M) ∧
      L1 * ‖prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y) - y‖ ≤ 1 / 4 := by
  set lam := 1 / (4 * curv L0 L1 M ‖g y‖) with hlamdef
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hc : 0 < curv L0 L1 M ‖g y‖ := curv_pos hL0 hL1.le hM (norm_nonneg _)
  have hlam : 0 < lam := by positivity
  set p := prox lam y (g y)
  set δ := ‖p - y‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hup : δ ≤ lam * (‖g y‖ + M) := by
    have h := H.prox_three hlam y (g y) y
    rw [sub_self, norm_zero] at h
    have h1 : ⟪g y, p - y⟫ ≥ -(‖g y‖ * δ) := by
      have := real_inner_le_norm (g y) (-(p - y))
      rw [inner_neg_right, norm_neg] at this
      linarith
    have h2 : ψ p - ψ y ≥ -(M * δ) := by
      have := H.ψ_sub_le y p
      rw [norm_sub_rev] at this
      linarith
    have h3 : δ ^ 2 ≤ lam * ((‖g y‖ + M) * δ) := by nlinarith
    rcases hδ.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · nlinarith
  have hlow : lam * (‖g y‖ - M) ≤ δ := by
    have hw := H.proxSub_norm_le hlam y (g y)
    unfold proxSub at hw
    change ‖(1 / lam) • (y - p) - g y‖ ≤ M at hw
    have h1 : ‖g y‖ - ‖(1 / lam) • (y - p)‖ ≤ ‖(1 / lam) • (y - p) - g y‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / lam),
      norm_sub_rev] at h1
    have h2 : ‖g y‖ - M ≤ 1 / lam * δ := by linarith
    have := mul_le_mul_of_nonneg_left h2 hlam.le
    rw [← mul_assoc, mul_one_div_cancel hlam.ne', one_mul] at this
    exact this
  refine ⟨hlow, hup, ?_⟩
  have hc' : L1 * (‖g y‖ + M) ≤ curv L0 L1 M ‖g y‖ := by
    unfold curv; nlinarith [mul_nonneg hL1.le hM]
  calc L1 * δ ≤ L1 * (lam * (‖g y‖ + M)) := mul_le_mul_of_nonneg_left hup hL1.le
    _ = L1 * (‖g y‖ + M) / (4 * curv L0 L1 M ‖g y‖) := by rw [hlamdef]; ring
    _ ≤ curv L0 L1 M ‖g y‖ / (4 * curv L0 L1 M ‖g y‖) := by gcongr
    _ = 1 / 4 := by field_simp

lemma Hyp.step_descent (H : Hyp f ψ g prox L0 L1 M xs) (y : E) :
    f (prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y)) + ψ (prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y)) ≤
      f y + ψ y - 3 * curv L0 L1 M ‖g y‖ * ‖prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y) - y‖ ^ 2 := by
  set lam := 1 / (4 * curv L0 L1 M ‖g y‖) with hlamdef
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hc : 0 < curv L0 L1 M ‖g y‖ := curv_pos hL0 hL1.le hM (norm_nonneg _)
  have hlam : 0 < lam := by positivity
  obtain ⟨-, -, hr⟩ := H.move_bounds y
  set p := prox lam y (g y)
  set δ := ‖p - y‖
  have hf := CompositeGeneralized.ball_upper hL0.le hL1.le H.grad H.cont H.smooth
    (x := y) (u := y) (v := p) (r := δ) (by linarith) (by rw [sub_self, norm_zero]; exact norm_nonneg _)
    le_rfl
  have hψ := H.prox_three hlam y (g y) y
  rw [sub_self, norm_zero] at hψ
  have hψ' : ⟪g y, p - y⟫ + ψ p - ψ y ≤ -(δ ^ 2 / lam) := by
    have h1 : lam * (⟪g y, p - y⟫ + ψ p - ψ y) ≤ -δ ^ 2 := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hlam.le
    rw [mul_div_cancel_left₀ _ hlam.ne'] at h2
    have e : -δ ^ 2 / lam = -(δ ^ 2 / lam) := neg_div _ _
    linarith
  have hlame : δ ^ 2 / lam = 4 * curv L0 L1 M ‖g y‖ * δ ^ 2 := by rw [hlamdef]; field_simp
  have hcurv : L0 + L1 * ‖g y‖ ≤ curv L0 L1 M ‖g y‖ := by
    unfold curv; nlinarith [mul_nonneg hL1.le hM]
  have hδ2 : 0 ≤ δ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcurv hδ2]


lemma Hyp.shifted_descent_gap (H : Hyp f ψ g prox L0 L1 M xs) (y : E) :
    5 * ‖shiftedGrad g xs y‖ ^ 2 / (24 * (L0 + L1 * M + L1 * ‖shiftedGrad g xs y‖)) ≤
      shifted f g xs y - shifted f g xs xs := by
  have hL0' : 0 < L0 + L1 * M := by have := H.hL0; have := H.hL1; have := H.hM; positivity
  have hd := normalized_descent H.shifted_grad H.shifted_cont hL0' H.hL1 H.shifted_sSup_form y
  have hm := H.shifted_min (mem_univ (y - (1 / (4 * (L0 + L1 * M + L1 * ‖shiftedGrad g xs y‖))) •
    shiftedGrad g xs y))
  simp only [mem_ofPred_eq] at hm
  linarith

lemma Hyp.step_dist (H : Hyp f ψ g prox L0 L1 M xs) (y : E) :
    ‖prox (1 / (4 * curv L0 L1 M ‖g y‖)) y (g y) - xs‖ ≤ ‖y - xs‖ := by
  set lam := 1 / (4 * curv L0 L1 M ‖g y‖) with hlamdef
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hc : 0 < curv L0 L1 M ‖g y‖ := curv_pos hL0 hL1.le hM (norm_nonneg _)
  have hlam : 0 < lam := by positivity
  have hne := H.prox_nonexpansive hlam y (g y) xs (g xs)
  rw [H.prox_fixed hlam] at hne
  set w := shiftedGrad g xs y with hw
  have hwe : (y - lam • g y) - (xs - lam • g xs) = (y - xs) - lam • w := by
    simp only [hw, shiftedGrad, smul_sub]; abel
  rw [hwe] at hne
  refine hne.trans ?_
  have hgap := H.shifted_descent_gap y
  have hsupp := Gradient.convex_support H.shifted_convex H.shifted_grad y xs
  rw [← hw] at hsupp
  have hi : ⟪w, xs - y⟫ = -⟪w, y - xs⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hi] at hsupp
  set Lh := L0 + L1 * M + L1 * ‖w‖ with hLhdef
  have hLh : 0 < Lh := by rw [hLhdef]; positivity
  have hLhc : Lh ≤ curv L0 L1 M ‖g y‖ := by
    have := H.shifted_norm_le y
    rw [← hw] at this
    unfold curv; rw [hLhdef]; nlinarith
  have hcoc : ‖w‖ ^ 2 / (8 * curv L0 L1 M ‖g y‖) ≤ ⟪w, y - xs⟫ := by
    have h1 : 5 * ‖w‖ ^ 2 / (24 * Lh) ≤ ⟪w, y - xs⟫ := by linarith
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖w‖, mul_le_mul_of_nonneg_left hLhc (sq_nonneg ‖w‖)]
  have hlame : lam ^ 2 * ‖w‖ ^ 2 ≤ 2 * lam * ⟪w, y - xs⟫ := by
    have e : lam ^ 2 * ‖w‖ ^ 2 = 2 * lam * (‖w‖ ^ 2 / (8 * curv L0 L1 M ‖g y‖)) := by
      rw [hlamdef]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hcoc (by positivity)
  have hcomm : ⟪y - xs, w⟫ = ⟪w, y - xs⟫ := real_inner_comm _ _
  have key : ‖y - xs - lam • w‖ ^ 2 ≤ ‖y - xs‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, real_inner_smul_right,
      hcomm]
    nlinarith
  calc ‖y - xs - lam • w‖ = Real.sqrt (‖y - xs - lam • w‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖y - xs‖ ^ 2) := Real.sqrt_le_sqrt key
    _ = ‖y - xs‖ := Real.sqrt_sq (norm_nonneg _)

lemma gthr_facts {L0 L1 M G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hM : 0 ≤ M)
    (hG : 5 * M + L0 / L1 < G) :
    0 < G ∧ 4 / 5 * G ≤ G - M ∧ G + M ≤ 6 / 5 * G ∧ L1 * G ≤ curv L0 L1 M G ∧
      curv L0 L1 M G ≤ 12 / 5 * (L1 * G) ∧ L0 + L1 * M ≤ L1 * G := by
  have h1 : L0 / L1 < G - 5 * M := by linarith
  rw [div_lt_iff₀ hL1] at h1
  have hGpos : 0 < G := by nlinarith [div_pos hL0 hL1]
  have hMG : 5 * M ≤ G := by linarith [div_pos hL0 hL1]
  have hLG : L0 < L1 * G - 5 * L1 * M := by nlinarith
  refine ⟨hGpos, by linarith, by linarith, ?_, ?_, ?_⟩
  · unfold curv; nlinarith [mul_nonneg hL1.le hM]
  · unfold curv; nlinarith [mul_nonneg hL1.le hM]
  · nlinarith [mul_nonneg hL1.le hM]

lemma Hyp.gap_lower_raw (H : Hyp f ψ g prox L0 L1 M xs) (y : E) (hG : gthr L0 L1 M < ‖g y‖) :
    3 * (‖g y‖ - M) ^ 2 / (16 * curv L0 L1 M ‖g y‖) ≤ f y + ψ y - (f xs + ψ xs) := by
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  unfold gthr at hG
  obtain ⟨hGpos, h45, -, hLG, hc, hL0'⟩ := gthr_facts hL0 hL1 hM hG
  set G := ‖g y‖ with hGdef
  have hc0 : 0 < curv L0 L1 M G := curv_pos hL0 hL1.le hM (norm_nonneg _)
  obtain ⟨hlow, -, -⟩ := H.move_bounds y
  have hdesc := H.step_descent y
  set lam := 1 / (4 * curv L0 L1 M G) with hlam
  have hlampos : 0 < lam := by rw [hlam]; positivity
  set δ := ‖prox lam y (g y) - y‖
  have hmin := H.min (mem_univ (prox lam y (g y)))
  simp only [mem_ofPred_eq] at hmin
  have hδ2 : (lam * (G - M)) ^ 2 ≤ δ ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg hlampos.le (by linarith)) hlow
  have hkey : 3 * curv L0 L1 M G * (lam * (G - M)) ^ 2 ≤ 3 * curv L0 L1 M G * δ ^ 2 :=
    mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have hval : 3 * curv L0 L1 M G * (lam * (G - M)) ^ 2 = 3 * (G - M) ^ 2 / (16 * curv L0 L1 M G) := by
    rw [hlam]; field_simp; ring
  linarith

lemma gap_const_bound {L0 L1 M G c : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hM : 0 ≤ M)
    (hG : gthr L0 L1 M < G) (_hc : 0 ≤ c) (hc1 : c ≤ 3 / 25) :
    (L0 + L1 * M) * (3 / 25 - c) / (12 / 5 * L1 ^ 2) ≤
      3 * (G - M) ^ 2 / (16 * curv L0 L1 M G) - c * (G ^ 2 / curv L0 L1 M G) := by
  obtain ⟨hGpos, h45, -, hLG, hcb, hL0'⟩ := gthr_facts hL0 hL1 hM hG
  have hcpos : 0 < curv L0 L1 M G := curv_pos hL0 hL1.le hM hGpos.le
  have h1 : (4 / 5 * G) ^ 2 ≤ (G - M) ^ 2 := pow_le_pow_left₀ (by positivity) h45 2
  have h2 : 3 / 25 * (G ^ 2 / curv L0 L1 M G) ≤ 3 * (G - M) ^ 2 / (16 * curv L0 L1 M G) := by
    rw [show 3 / 25 * (G ^ 2 / curv L0 L1 M G) = 3 / 25 * G ^ 2 / curv L0 L1 M G by ring,
      div_le_div_iff₀ hcpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h1 hcpos.le]
  have h3 : (L0 + L1 * M) * (3 / 25 - c) / (12 / 5 * L1 ^ 2) ≤ (3 / 25 - c) * (G ^ 2 / curv L0 L1 M G) := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : (3 / 25 - c) * (G ^ 2 / curv L0 L1 M G) * (12 / 5 * L1 ^ 2) =
        (3 / 25 - c) * (G ^ 2 * (12 / 5 * L1 ^ 2) / curv L0 L1 M G) := by ring
    rw [h4, mul_comm (L0 + L1 * M)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [le_div_iff₀ hcpos]
    have h5 : (L0 + L1 * M) * curv L0 L1 M G ≤ L1 * G * (12 / 5 * (L1 * G)) :=
      mul_le_mul hL0' hcb hcpos.le (by positivity)
    nlinarith
  have e : (3 / 25 - c) * (G ^ 2 / curv L0 L1 M G) =
      3 / 25 * (G ^ 2 / curv L0 L1 M G) - c * (G ^ 2 / curv L0 L1 M G) := by ring
  linarith

lemma Hyp.gap_lower (H : Hyp f ψ g prox L0 L1 M xs) (y : E) (hG : gthr L0 L1 M < ‖g y‖) :
    (L0 + L1 * M) / (20 * L1 ^ 2) ≤ f y + ψ y - (f xs + ψ xs) := by
  have h1 := H.gap_lower_raw y hG
  have h2 := gap_const_bound (c := 0) H.hL0 H.hL1 H.hM hG le_rfl (by norm_num)
  have hc : 0 < curv L0 L1 M ‖g y‖ := curv_pos H.hL0 H.hL1.le H.hM (norm_nonneg _)
  have e : (L0 + L1 * M) * (3 / 25 - 0) / (12 / 5 * L1 ^ 2) = (L0 + L1 * M) / (20 * L1 ^ 2) := by
    field_simp; ring
  rw [e] at h2
  simp only [zero_mul, sub_zero] at h2
  linarith

lemma cweight_eq {L0 L1 M A G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hG : 0 < G) (hGM : M ≤ G) :
    0 < cweight L0 L1 M A G ∧
      cweight L0 L1 M A G ^ 2 = (A + cweight L0 L1 M A G) / (12 * curv L0 L1 M G) +
        cweight L0 L1 M A G * phiFun (L0 + L1 * M) L1 (G - M) / (2 * G ^ 2) := by
  have hc : 0 < curv L0 L1 M G := curv_pos hL0 hL1.le hM hG.le
  have hφ : 0 ≤ phiFun (L0 + L1 * M) L1 (G - M) :=
    phiFun_nonneg (by positivity) hL1 (by linarith)
  set b := 1 / (12 * curv L0 L1 M G) + phiFun (L0 + L1 * M) L1 (G - M) / (2 * G ^ 2) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  set c := 4 * A / (12 * curv L0 L1 M G) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hs : Real.sqrt (b ^ 2 + c) ^ 2 = b ^ 2 + c := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (b ^ 2 + c) := Real.sqrt_nonneg _
  have hw : cweight L0 L1 M A G = (b + Real.sqrt (b ^ 2 + c)) / 2 := rfl
  refine ⟨by rw [hw]; positivity, ?_⟩
  rw [hw]
  have hce : c = 4 * A / (12 * curv L0 L1 M G) := rfl
  have e : ((b + Real.sqrt (b ^ 2 + c)) / 2) ^ 2 = b * ((b + Real.sqrt (b ^ 2 + c)) / 2) + c / 4 := by
    nlinarith [hs]
  rw [e, hb, hcdef]
  field_simp
  ring

end OracleTemplate.CompositeSherpa
