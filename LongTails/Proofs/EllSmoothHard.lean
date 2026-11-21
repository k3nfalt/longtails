import LongTails.Proofs.EllSmoothChainHessian
import LongTails.Proofs.AbcHardFunction

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.EllSmoothHard

open LongTails.Proofs.EllSmoothProfiles
open LongTails.Proofs.AbcChainProfiles (pos rr abs_sub_le_sum pos_nonneg pos_of_nonneg pos_of_nonpos)
open LongTails.Proofs.EllSmoothChain LongTails.Proofs.EllSmoothChainHessian
open LongTails.Proofs.AbcHardFunction (sel sel_apply sel_norm sel_opNorm sel_adjoint adjoint_norm
  adjoint_congr)

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def W (y : ℝ) : ℝ := rc y - 2 * rc (y - 1) + rc (y - 2)

noncomputable def dW (y : ℝ) : ℝ := rr y - 2 * rr (y - 1) + rr (y - 2)

noncomputable def ddW (y : ℝ) : ℝ := pos y - 2 * pos (y - 1) + pos (y - 2)

lemma W_hasDerivAt (y : ℝ) : HasDerivAt W (dW y) y := by
  have h (a : ℝ) : HasDerivAt (fun s => rc (s - a)) (rr (y - a)) y := by
    have := (rc_hasDerivAt (y - a)).comp y ((hasDerivAt_id y).sub_const a)
    simp only [mul_one] at this
    exact this
  have h0 : HasDerivAt rc (rr y) y := rc_hasDerivAt y
  exact (h0.sub ((h 1).const_mul 2)).add (h 2)

lemma dW_hasDerivAt (y : ℝ) : HasDerivAt dW (ddW y) y := by
  have h (a : ℝ) : HasDerivAt (fun s => rr (s - a)) (pos (y - a)) y := by
    have := (rr_hasDerivAt (y - a)).comp y ((hasDerivAt_id y).sub_const a)
    simp only [mul_one] at this
    exact this
  have h0 : HasDerivAt rr (pos y) y := rr_hasDerivAt y
  exact (h0.sub ((h 1).const_mul 2)).add (h 2)

lemma ddW_nonneg (y : ℝ) : 0 ≤ ddW y := by
  simp only [ddW, pos, max_def]
  split_ifs <;> linarith

lemma ddW_le_one (y : ℝ) : ddW y ≤ 1 := by
  simp only [ddW, pos, max_def]
  split_ifs <;> linarith

lemma ddW_of_nonpos {y : ℝ} (h : y ≤ 0) : ddW y = 0 := by
  unfold ddW
  rw [pos_of_nonpos h, pos_of_nonpos (by linarith), pos_of_nonpos (by linarith)]
  ring

lemma ddW_of_two_le {y : ℝ} (h : 2 ≤ y) : ddW y = 0 := by
  unfold ddW
  rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith), pos_of_nonneg (by linarith)]
  ring

lemma dW_of_nonpos {y : ℝ} (h : y ≤ 0) : dW y = 0 := by
  unfold dW
  rw [rr_of_nonpos h, rr_of_nonpos (by linarith), rr_of_nonpos (by linarith)]
  ring

lemma dW_of_two_le {y : ℝ} (h : 2 ≤ y) : dW y = 1 := by
  unfold dW
  rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith), rr_of_nonneg (by linarith)]
  ring

lemma dW_monotone : Monotone dW :=
  monotone_of_deriv_nonneg (fun y => (dW_hasDerivAt y).differentiableAt)
    (fun y => by rw [(dW_hasDerivAt y).deriv]; exact ddW_nonneg y)

lemma dW_nonneg (y : ℝ) : 0 ≤ dW y := by
  rcases le_total y 0 with h | h
  · rw [dW_of_nonpos h]
  · have := dW_monotone h
    rwa [dW_of_nonpos le_rfl] at this

lemma dW_le_one (y : ℝ) : dW y ≤ 1 := by
  rcases le_total y 2 with h | h
  · have := dW_monotone h
    rwa [dW_of_two_le le_rfl] at this
  · rw [dW_of_two_le h]

lemma W_nonneg (y : ℝ) : 0 ≤ W y := by
  have hm : Monotone W := monotone_of_deriv_nonneg (fun y => (W_hasDerivAt y).differentiableAt)
    (fun y => by rw [(W_hasDerivAt y).deriv]; exact dW_nonneg y)
  have h0 : W 0 = 0 := by
    unfold W
    rw [rc_of_nonpos le_rfl, rc_of_nonpos (by norm_num), rc_of_nonpos (by norm_num)]
    ring
  rcases le_total y 0 with h | h
  · unfold W
    rw [rc_of_nonpos h, rc_of_nonpos (by linarith), rc_of_nonpos (by linarith)]
    norm_num
  · have := hm h
    rwa [h0] at this

variable (S : Shape) (n : ℕ)

noncomputable def rad : ℝ := 2 ^ 22 * ((n : ℝ) + 1) ^ 2 / S.mu ^ 2

noncomputable def kap : ℝ := S.mu ^ 2 / (52000 * ((n : ℝ) + 1))

noncomputable def lam : ℝ := 3 * rad S n ^ 2 / 2

lemma n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma n1_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma rad_pos : 0 < rad S n := by
  unfold rad
  have := S.hmu
  have := n1_pos n
  positivity

lemma kap_pos : 0 < kap S n := by
  unfold kap
  have := S.hmu
  have := n1_pos n
  positivity

lemma lam_pos : 0 < lam S n := by
  unfold lam
  have := rad_pos S n
  positivity

lemma rad_ge : 2 ^ 22 * ((n : ℝ) + 1) ^ 2 ≤ rad S n := by
  unfold rad
  have hmu := S.hmu
  have hmu' := S.hmu'
  rw [le_div_iff₀ (by positivity)]
  have h1 : S.mu ^ 2 ≤ 1 := by nlinarith
  have h2 : (0 : ℝ) ≤ 2 ^ 22 * ((n : ℝ) + 1) ^ 2 := by positivity
  nlinarith

lemma rad_ge' : 2 ^ 22 * ((n : ℝ) + 1) ≤ rad S n := by
  have h1 := rad_ge S n
  have h2 := n1_ge n
  nlinarith

lemma kap_rad : kap S n * rad S n = 2 ^ 22 / 52000 * ((n : ℝ) + 1) := by
  unfold kap rad
  have := S.hmu
  have := n1_pos n
  field_simp

lemma kap_le : kap S n ≤ S.mu / 52000 := by
  unfold kap
  have hmu := S.hmu
  have hmu' := S.hmu'
  have hn := n1_ge n
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma kap_tEnd : 2 * kap S n * (S.tEnd * ((n : ℝ) + 1)) ≤ S.mu / 2000 := by
  have ht := S.tEnd_le
  have hmu := S.hmu
  have hn := n1_pos n
  have hk := kap_pos S n
  have h1 : 2 * kap S n * (S.tEnd * ((n : ℝ) + 1)) ≤
      2 * kap S n * (13 / S.mu * ((n : ℝ) + 1)) := by gcongr
  refine h1.trans (le_of_eq ?_)
  unfold kap
  field_simp; ring

noncomputable def wallArg (s : ℝ) : ℝ := (s - rad S n ^ 2) / lam S n

noncomputable def wall (s : ℝ) : ℝ := kap S n * lam S n * W (wallArg S n s)

noncomputable def dwall (s : ℝ) : ℝ := kap S n * dW (wallArg S n s)

noncomputable def ddwall (s : ℝ) : ℝ := kap S n / lam S n * ddW (wallArg S n s)

lemma wallArg_hasDerivAt (s : ℝ) : HasDerivAt (wallArg S n) (1 / lam S n) s := by
  have := ((hasDerivAt_id s).sub_const (rad S n ^ 2)).div_const (lam S n)
  exact this

lemma wall_hasDerivAt (s : ℝ) : HasDerivAt (wall S n) (dwall S n s) s := by
  have h := ((W_hasDerivAt (wallArg S n s)).comp s (wallArg_hasDerivAt S n s)).const_mul
    (kap S n * lam S n)
  refine h.congr_deriv ?_
  unfold dwall
  have := lam_pos S n
  field_simp

lemma dwall_hasDerivAt (s : ℝ) : HasDerivAt (dwall S n) (ddwall S n s) s := by
  have h := ((dW_hasDerivAt (wallArg S n s)).comp s (wallArg_hasDerivAt S n s)).const_mul
    (kap S n)
  refine h.congr_deriv ?_
  unfold ddwall
  have := lam_pos S n
  field_simp

lemma wall_nonneg (s : ℝ) : 0 ≤ wall S n s := by
  unfold wall
  have := kap_pos S n
  have := lam_pos S n
  have := W_nonneg (wallArg S n s)
  positivity

lemma dwall_nonneg (s : ℝ) : 0 ≤ dwall S n s :=
  mul_nonneg (kap_pos S n).le (dW_nonneg _)

lemma dwall_le (s : ℝ) : dwall S n s ≤ kap S n := by
  unfold dwall
  have := kap_pos S n
  have := dW_le_one (wallArg S n s)
  nlinarith

lemma ddwall_nonneg (s : ℝ) : 0 ≤ ddwall S n s := by
  unfold ddwall
  have := kap_pos S n
  have := lam_pos S n
  have := ddW_nonneg (wallArg S n s)
  positivity

lemma ddwall_le (s : ℝ) : ddwall S n s ≤ kap S n / lam S n := by
  unfold ddwall
  have hk : 0 ≤ kap S n / lam S n := div_nonneg (kap_pos S n).le (lam_pos S n).le
  have := ddW_le_one (wallArg S n s)
  nlinarith

lemma wallArg_two_le {s : ℝ} (h : 4 * rad S n ^ 2 ≤ s) : 2 ≤ wallArg S n s := by
  unfold wallArg
  rw [le_div_iff₀ (lam_pos S n)]
  unfold lam
  linarith

lemma dwall_of_ge {s : ℝ} (h : 4 * rad S n ^ 2 ≤ s) : dwall S n s = kap S n := by
  unfold dwall
  rw [dW_of_two_le (wallArg_two_le S n h), mul_one]

lemma ddwall_of_ge {s : ℝ} (h : 4 * rad S n ^ 2 ≤ s) : ddwall S n s = 0 := by
  unfold ddwall
  rw [ddW_of_two_le (wallArg_two_le S n h), mul_zero]

noncomputable def cutArg (s : ℝ) : ℝ := (s - 4 * rad S n ^ 2) / (24 * rad S n ^ 2) + 1 / 2

noncomputable def cut (s : ℝ) : ℝ := 1 - psi (cutArg S n s)

noncomputable def dcut (s : ℝ) : ℝ := -(dpsi (cutArg S n s) / (24 * rad S n ^ 2))

noncomputable def ddcut (s : ℝ) : ℝ := -(ddpsi (cutArg S n s) / (24 * rad S n ^ 2) ^ 2)

lemma cutArg_hasDerivAt (s : ℝ) : HasDerivAt (cutArg S n) (1 / (24 * rad S n ^ 2)) s := by
  have := (((hasDerivAt_id s).sub_const (4 * rad S n ^ 2)).div_const
    (24 * rad S n ^ 2)).add_const (1 / 2 : ℝ)
  exact this

lemma cut_hasDerivAt (s : ℝ) : HasDerivAt (cut S n) (dcut S n s) s := by
  have h := ((psi_hasDerivAt (cutArg S n s)).comp s (cutArg_hasDerivAt S n s)).const_sub 1
  refine h.congr_deriv ?_
  unfold dcut
  ring

lemma dcut_hasDerivAt (s : ℝ) : HasDerivAt (dcut S n) (ddcut S n s) s := by
  have h := (((dpsi_hasDerivAt (cutArg S n s)).comp s (cutArg_hasDerivAt S n s)).div_const
    (24 * rad S n ^ 2)).neg
  refine h.congr_deriv ?_
  unfold ddcut
  have := rad_pos S n
  field_simp

lemma cut_nonneg (s : ℝ) : 0 ≤ cut S n s := by
  unfold cut
  linarith [psi_le_one (cutArg S n s)]

lemma cut_le_one (s : ℝ) : cut S n s ≤ 1 := by
  unfold cut
  linarith [psi_nonneg (cutArg S n s)]

lemma cutArg_le {s : ℝ} (h : s ≤ 4 * rad S n ^ 2) : cutArg S n s ≤ 1 / 2 := by
  unfold cutArg
  have hr := rad_pos S n
  have : (s - 4 * rad S n ^ 2) / (24 * rad S n ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

lemma cutArg_ge {s : ℝ} (h : 16 * rad S n ^ 2 ≤ s) : 1 ≤ cutArg S n s := by
  unfold cutArg
  have hr := rad_pos S n
  have : (1 / 2 : ℝ) ≤ (s - 4 * rad S n ^ 2) / (24 * rad S n ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

lemma cut_of_le {s : ℝ} (h : s ≤ 4 * rad S n ^ 2) : cut S n s = 1 := by
  unfold cut
  rw [psi_of_le (cutArg_le S n h), sub_zero]

lemma dcut_of_le {s : ℝ} (h : s ≤ 4 * rad S n ^ 2) : dcut S n s = 0 := by
  unfold dcut
  rw [dpsi_of_le (cutArg_le S n h), zero_div, neg_zero]

lemma ddcut_of_le {s : ℝ} (h : s ≤ 4 * rad S n ^ 2) : ddcut S n s = 0 := by
  unfold ddcut
  rw [ddpsi_of_le (cutArg_le S n h), zero_div, neg_zero]

lemma cut_of_ge {s : ℝ} (h : 16 * rad S n ^ 2 ≤ s) : cut S n s = 0 := by
  unfold cut
  rw [psi_of_ge (cutArg_ge S n h), sub_self]

lemma dcut_of_ge {s : ℝ} (h : 16 * rad S n ^ 2 ≤ s) : dcut S n s = 0 := by
  unfold dcut
  rw [dpsi_of_ge (cutArg_ge S n h), zero_div, neg_zero]

lemma ddcut_of_ge {s : ℝ} (h : 16 * rad S n ^ 2 ≤ s) : ddcut S n s = 0 := by
  unfold ddcut
  rw [ddpsi_of_ge (cutArg_ge S n h), zero_div, neg_zero]

lemma dcut_abs (s : ℝ) : |dcut S n s| ≤ 5 / (24 * rad S n ^ 2) := by
  unfold dcut
  have hr := rad_pos S n
  rw [abs_neg, abs_div, abs_of_nonneg (dpsi_nonneg _), abs_of_pos (by positivity)]
  gcongr
  exact dpsi_le _

lemma ddcut_abs (s : ℝ) : |ddcut S n s| ≤ 1 / (16 * rad S n ^ 4) := by
  unfold ddcut
  have hr := rad_pos S n
  rw [abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (24 * rad S n ^ 2) ^ 2)]
  have h := ddpsi_abs (cutArg S n s)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hr 4]

variable {n} {d : ℕ}

noncomputable def vfield (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d :=
  (sel π).adjoint (field S (sel π w))

noncomputable def bco (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ℝ :=
  2 * dcut S n (‖w‖ ^ 2) * chain S (sel π w) + 2 * dwall S n (‖w‖ ^ 2)

noncomputable def hval (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ℝ :=
  cut S n (‖w‖ ^ 2) * chain S (sel π w) + wall S n (‖w‖ ^ 2)

noncomputable def hgrad (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d :=
  cut S n (‖w‖ ^ 2) • vfield S π w + bco S π w • w

lemma normSq_hasFDerivAt (w : Space d) :
    HasFDerivAt (fun x : Space d => ‖x‖ ^ 2) (2 • innerSL ℝ w) w :=
  (hasStrictFDerivAt_norm_sq w).hasFDerivAt

lemma chainSel_hasFDerivAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasFDerivAt (fun x : Space d => chain S (sel π x))
      ((InnerProductSpace.toDual ℝ (Chain n) (field S (sel π w))).comp (sel π)) w :=
  ((chain_hasGradientAt S (sel π w)).hasFDerivAt).comp w (sel π).hasFDerivAt

lemma hval_hasGradientAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasGradientAt (hval S π) (hgrad S π w) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hc := (cut_hasDerivAt S n (‖w‖ ^ 2)).comp_hasFDerivAt w (normSq_hasFDerivAt w)
  have hF := chainSel_hasFDerivAt S π w
  have hw := (wall_hasDerivAt S n (‖w‖ ^ 2)).comp_hasFDerivAt w (normSq_hasFDerivAt w)
  have h := (hc.mul hF).add hw
  refine h.congr_fderiv ?_
  ext v
  simp only [hgrad, vfield, bco, InnerProductSpace.toDual_apply_apply, inner_add_left,
    inner_smul_left, ContinuousLinearMap.adjoint_inner_left, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, RCLike.conj_to_real, nsmul_eq_mul, Nat.cast_ofNat, Function.comp_apply]
  ring

lemma hval_gradient (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    gradient (hval S π) w = hgrad S π w := (hval_hasGradientAt S π w).gradient

lemma vfield_hasFDerivAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasFDerivAt (vfield S π)
      (((sel π).adjoint).comp ((fderiv ℝ (field S) (sel π w)).comp (sel π))) w :=
  ((sel π).adjoint.hasFDerivAt).comp w
    ((field_hasFDerivAt S (sel π w)).comp w (sel π).hasFDerivAt)

noncomputable def bD (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d →L[ℝ] ℝ :=
  (2 : ℝ) • (dcut S n (‖w‖ ^ 2) •
      ((InnerProductSpace.toDual ℝ (Chain n) (field S (sel π w))).comp (sel π)) +
    chain S (sel π w) • (ddcut S n (‖w‖ ^ 2) • ((2 : ℕ) • innerSL ℝ w))) +
  (2 : ℝ) • (ddwall S n (‖w‖ ^ 2) • ((2 : ℕ) • innerSL ℝ w))

lemma bco_hasFDerivAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasFDerivAt (bco S π) (bD S π w) w := by
  have hc := (dcut_hasDerivAt S n (‖w‖ ^ 2)).comp_hasFDerivAt w (normSq_hasFDerivAt w)
  have hF := chainSel_hasFDerivAt S π w
  have hw := (dwall_hasDerivAt S n (‖w‖ ^ 2)).comp_hasFDerivAt w (normSq_hasFDerivAt w)
  have h := ((hc.mul hF).const_mul 2).add (hw.const_mul 2)
  have he : bco S π = fun x : Space d =>
      2 * (dcut S n (‖x‖ ^ 2) * chain S (sel π x)) + 2 * dwall S n (‖x‖ ^ 2) := by
    funext x; unfold bco; ring
  rw [he]
  exact h

lemma hgrad_hasFDerivAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasFDerivAt (hgrad S π)
      (cut S n (‖w‖ ^ 2) • (((sel π).adjoint).comp ((fderiv ℝ (field S) (sel π w)).comp (sel π))) +
        (dcut S n (‖w‖ ^ 2) • ((2 : ℕ) • innerSL ℝ w)).smulRight (vfield S π w) +
        (bco S π w • ContinuousLinearMap.id ℝ (Space d) + (bD S π w).smulRight w)) w := by
  have hc := (cut_hasDerivAt S n (‖w‖ ^ 2)).comp_hasFDerivAt w (normSq_hasFDerivAt w)
  have hV := vfield_hasFDerivAt S π w
  have hb := bco_hasFDerivAt S π w
  exact (hc.smul hV).add (hb.smul (hasFDerivAt_id w))

lemma hgrad_differentiable (π : Fin (n + 1) ↪ Fin d) : Differentiable ℝ (hgrad S π) :=
  fun w => (hgrad_hasFDerivAt S π w).differentiableAt

lemma vfield_norm (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    ‖vfield S π w‖ ≤ ‖field S (sel π w)‖ := adjoint_norm π _

lemma sel_vfield (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    sel π (vfield S π w) = field S (sel π w) := sel_adjoint π _

lemma two_inner_norm (w h : Space d) : ‖((2 : ℕ) • innerSL ℝ w) h‖ ≤ 2 * ‖w‖ * ‖h‖ := by
  simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat,
    Real.norm_eq_abs, abs_mul, abs_two]
  have := abs_real_inner_le_norm w h
  nlinarith

lemma hgrad_fderiv_le (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    ‖fderiv ℝ (hgrad S π) w‖ ≤
      cut S n (‖w‖ ^ 2) * ‖fderiv ℝ (field S) (sel π w)‖ +
      4 * |dcut S n (‖w‖ ^ 2)| * ‖w‖ * ‖field S (sel π w)‖ + |bco S π w| +
      (4 * |ddcut S n (‖w‖ ^ 2)| * |chain S (sel π w)| + 4 * |ddwall S n (‖w‖ ^ 2)|) * ‖w‖ ^ 2 := by
  rw [(hgrad_hasFDerivAt S π w).fderiv]
  have hc0 := cut_nonneg S n (‖w‖ ^ 2)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  have hsel : ‖sel π h‖ ≤ ‖h‖ := sel_norm π h
  have h1 : ‖cut S n (‖w‖ ^ 2) • (sel π).adjoint (fderiv ℝ (field S) (sel π w) (sel π h))‖ ≤
      cut S n (‖w‖ ^ 2) * ‖fderiv ℝ (field S) (sel π w)‖ * ‖h‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc0, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hc0
    calc _ ≤ ‖fderiv ℝ (field S) (sel π w) (sel π h)‖ := adjoint_norm π _
      _ ≤ ‖fderiv ℝ (field S) (sel π w)‖ * ‖sel π h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsel (norm_nonneg _)
  have h2 : ‖(dcut S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h) • vfield S π w‖ ≤
      2 * |dcut S n (‖w‖ ^ 2)| * ‖w‖ * ‖field S (sel π w)‖ * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have ha := two_inner_norm w h
    rw [Real.norm_eq_abs] at ha
    have hv := vfield_norm S π w
    have hd0 := abs_nonneg (dcut S n (‖w‖ ^ 2))
    calc |dcut S n (‖w‖ ^ 2)| * |((2 : ℕ) • innerSL ℝ w) h| * ‖vfield S π w‖
        ≤ |dcut S n (‖w‖ ^ 2)| * (2 * ‖w‖ * ‖h‖) * ‖field S (sel π w)‖ := by
          gcongr
      _ = _ := by ring
  have h3 : ‖bco S π w • h‖ ≤ |bco S π w| * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hbD : |bD S π w h| ≤ (2 * |dcut S n (‖w‖ ^ 2)| * ‖field S (sel π w)‖ +
      (4 * |ddcut S n (‖w‖ ^ 2)| * |chain S (sel π w)| + 4 * |ddwall S n (‖w‖ ^ 2)|) * ‖w‖) *
        ‖h‖ := by
    simp only [bD, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
    have ha := two_inner_norm w h
    rw [Real.norm_eq_abs] at ha
    have hi : |⟪field S (sel π w), sel π h⟫| ≤ ‖field S (sel π w)‖ * ‖h‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hsel (norm_nonneg _))
    have e1 : |2 * (dcut S n (‖w‖ ^ 2) * ⟪field S (sel π w), sel π h⟫ +
        chain S (sel π w) * (ddcut S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h)) +
        2 * (ddwall S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h)| ≤
        2 * (|dcut S n (‖w‖ ^ 2)| * |⟪field S (sel π w), sel π h⟫| +
        |chain S (sel π w)| * (|ddcut S n (‖w‖ ^ 2)| * |((2 : ℕ) • innerSL ℝ w) h|)) +
        2 * (|ddwall S n (‖w‖ ^ 2)| * |((2 : ℕ) • innerSL ℝ w) h|) := by
      have t1 := abs_add_le (2 * (dcut S n (‖w‖ ^ 2) * ⟪field S (sel π w), sel π h⟫ +
        chain S (sel π w) * (ddcut S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h)))
        (2 * (ddwall S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h))
      have t2 := abs_add_le (dcut S n (‖w‖ ^ 2) * ⟪field S (sel π w), sel π h⟫)
        (chain S (sel π w) * (ddcut S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h))
      rw [abs_mul, abs_two, abs_mul, abs_two, abs_mul] at t1
      rw [abs_mul, abs_mul, abs_mul] at t2
      nlinarith
    refine e1.trans ?_
    have hd0 := abs_nonneg (dcut S n (‖w‖ ^ 2))
    have hdd0 := abs_nonneg (ddcut S n (‖w‖ ^ 2))
    have hch0 := abs_nonneg (chain S (sel π w))
    have hw0 := abs_nonneg (ddwall S n (‖w‖ ^ 2))
    have hin0 := abs_nonneg (((2 : ℕ) • innerSL ℝ w) h)
    have p1 := mul_le_mul_of_nonneg_left hi hd0
    have p2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha hdd0) hch0
    have p3 := mul_le_mul_of_nonneg_left ha hw0
    nlinarith
  have h4 : ‖bD S π w h • w‖ ≤ (2 * |dcut S n (‖w‖ ^ 2)| * ‖field S (sel π w)‖ +
      (4 * |ddcut S n (‖w‖ ^ 2)| * |chain S (sel π w)| + 4 * |ddwall S n (‖w‖ ^ 2)|) * ‖w‖) *
        ‖h‖ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hbD (norm_nonneg _)
  calc _ ≤ ‖cut S n (‖w‖ ^ 2) • (sel π).adjoint (fderiv ℝ (field S) (sel π w) (sel π h))‖ +
        ‖(dcut S n (‖w‖ ^ 2) * ((2 : ℕ) • innerSL ℝ w) h) • vfield S π w‖ +
        (‖bco S π w • h‖ + ‖bD S π w h • w‖) := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          · exact norm_add_le _ _
          · exact norm_add_le _ _
    _ ≤ _ := by nlinarith

end LongTails.Proofs.EllSmoothHard
