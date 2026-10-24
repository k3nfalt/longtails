import LongTails.Proofs.ConstrainedRegularization
import LongTails.Proofs.ProjectedClippedTuning

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ProjectedClippedExtragradient

open ConstrainedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_root_operator_bound {X : Set E} {F : E → E} (t : Tuning)
    (hF : GeneralizedMonotone.Hyp F t.L0 t.L1) (hR : 0 < t.R)
    {p q c : E} {r : ℝ} (hr : 0 ≤ r) (hp : p ∈ X) (hq : q ∈ X)
    (hnp : Normal X p (-(F p + r • (p - c)))) (hnq : Normal X q (-F q))
    (hG : ‖F q‖ ≤ t.G) (hd : ‖p - q‖ ≤ 4 * t.R) (hbias : r * ‖p - c‖ ≤ t.ε) :
    ‖F p‖ ≤ rootBound t := by
  let h := 4 * t.R / (1 + 8 * t.L1 * t.R)
  have h1 := hF.L1_nonneg
  have h0 := hF.L0_pos
  have hden : 0 < 1 + 8 * t.L1 * t.R := by positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hcap : t.L1 * h ≤ 1 / 2 := by
    dsimp [h]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  have hhR : h ≤ 4 * t.R := by
    dsimp [h]
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg h1 (sq_nonneg t.R)]
  have hn : ‖F p + -(F p + r • (p - c))‖ ≤ t.ε := by
    rw [show F p + -(F p + r • (p - c)) = -(r • (p - c)) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact hbias
  have ho := operator_normal_bound hF hp hq hnp hnq hh hcap hd
  have hMG := mul_le_mul_of_nonneg_left hG hh.le
  have hnoise := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 4 * t.R)
  have hL : 0 ≤ t.L0 + t.L1 * t.G := by
    have := (norm_nonneg (F q)).trans hG
    positivity
  have hLG := mul_le_mul_of_nonneg_left hG h1
  have hLG' := mul_le_mul_of_nonneg_right hLG (by positivity : 0 ≤ h * (4 * t.R + h))
  have hrr := mul_le_mul_of_nonneg_left hhR (mul_nonneg hL hh.le)
  have he : h * (1 + 8 * t.L1 * t.R) = 4 * t.R := by dsimp [h]; field_simp
  have hnoise' := congrArg (fun z : ℝ => t.ε * z) he
  apply (mul_le_mul_iff_right₀ hh).mp
  unfold rootBound
  nlinarith

omit [InnerProductSpace ℝ E] in
lemma path_distance_bound (t : Tuning) (hR : 0 < t.R) (p : ℕ → E) (q : E)
    (hinit : ‖p 0 - q‖ ≤ t.R) {n : ℕ}
    (hstep : ∀ s < n, ‖p (s + 1) - p s‖ ≤ radius t s / 4) : ‖p n - q‖ ≤ 2 * t.R := by
  have hsum : ∀ k ≤ n, ‖p k - q‖ ≤ t.R + (∑ s ∈ Finset.range k, radius t s) / 4 := by
    intro k hk
    induction k with
    | zero => simpa using hinit
    | succ k ih =>
      have hi := ih (by omega)
      have ht := norm_sub_le_norm_sub_add_norm_sub (p (k + 1)) (p k) q
      have hs := hstep k (by omega)
      rw [Finset.sum_range_succ]
      linarith
  have hh := hsum n le_rfl
  rw [radius_geometric_sum] at hh
  have := mul_nonneg hR.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
  nlinarith

lemma regularized_stage_transport {X : Set E} {F : E → E} (t : Tuning)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) (hR : 0 < t.R) (hε : 0 < t.ε)
    (s : ℕ) {c w p q : E} (hp : p ∈ X) (hq : q ∈ X)
    (hnp : Normal X p (-(F p + regularization t s • (p - c))))
    (hnq : Normal X q (-(F q + regularization t (s + 1) • (q - (1 / 2 : ℝ) • (c + w)))))
    (hw : ‖w - p‖ ≤ radius t s / 2) :
    ‖q - p‖ ≤ radius t s / 4 ∧ ‖q - w‖ ≤ radius t (s + 1) ∧
      ‖regularization t (s + 1) • (q - (1 / 2 : ℝ) • (c + w)) -
        regularization t s • (p - c)‖ ≤ t.ε / (2 ^ 20 * stageCount t) := by
  have hr := regularization_pos t hR hε s
  rw [regularization_succ] at hnq ⊢
  have ht := regularized_root_transport (regularization_pos t hR hε s) hmono hp hq hnp hnq
  refine ⟨by linarith [ht.1], ?_, ?_⟩
  · rw [radius_succ]
    exact ht.2.1.trans hw
  · have hm := mul_le_mul_of_nonneg_left hw
      (by positivity : 0 ≤ 2 * regularization t s)
    have he := regularization_radius t hR s
    linarith [ht.2.2]

omit [InnerProductSpace ℝ E] in
lemma path_bias_bound (t : Tuning) (hε : 0 ≤ t.ε) (v : ℕ → E)
    (hinit : ‖v 0‖ ≤ t.ε / (2 ^ 20 * stageCount t)) {n : ℕ} (hn : n < stageCount t)
    (hstep : ∀ s < n, ‖v (s + 1) - v s‖ ≤ t.ε / (2 ^ 20 * stageCount t)) :
    ‖v n‖ ≤ t.ε / 2 ^ 20 := by
  have hN : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have hsum : ∀ k ≤ n, ‖v k‖ ≤ (k + 1 : ℝ) * (t.ε / (2 ^ 20 * stageCount t)) := by
    intro k hk
    induction k with
    | zero => simpa using hinit
    | succ k ih =>
      have hi := ih (by omega)
      have ht := norm_add_le (v (k + 1) - v k) (v k)
      rw [sub_add_cancel] at ht
      have hs := hstep k (by omega)
      push_cast
      linarith
  have hn' : (n + 1 : ℝ) ≤ stageCount t := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_right hn' (by positivity : 0 ≤ t.ε / (2 ^ 20 * stageCount t))
  have he : (stageCount t : ℝ) * (t.ε / (2 ^ 20 * stageCount t)) = t.ε / 2 ^ 20 := by field_simp
  rw [he] at hm
  exact (hsum n le_rfl).trans hm

lemma local_operator_difference {F : E → E} {L0 L1 : ℝ}
    (hF : GeneralizedMonotone.Hyp F L0 L1) (x y : E) (hcap : L1 * ‖x - y‖ ≤ 1 / 2) :
    ‖F x - F y‖ ≤ 2 * (L0 + L1 * ‖F x‖) * ‖x - y‖ := by
  have hh := hF.local x y (by linarith)
  nlinarith [mul_nonneg (norm_nonneg (F x - F y)) (sub_nonneg.mpr hcap)]

lemma local_regularized_difference {F : E → E} {L0 L1 r M : ℝ}
    (hF : GeneralizedMonotone.Hyp F L0 L1) (hr : 0 ≤ r) (c x p : E)
    (hM : ‖F p‖ ≤ M) (hcap : L1 * ‖x - p‖ ≤ 1 / 2) :
    ‖(F x + r • (x - c)) - (F p + r • (p - c))‖ ≤
      (2 * (L0 + L1 * M) + r) * ‖x - p‖ := by
  have hl := local_operator_difference hF p x (by simpa only [norm_sub_rev p x] using hcap)
  rw [norm_sub_rev p x, norm_sub_rev (F p) (F x)] at hl
  have he : (F x + r • (x - c)) - (F p + r • (p - c)) = (F x - F p) + r • (x - p) := by module
  rw [he]
  have ht := norm_add_le (F x - F p) (r • (x - p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at ht
  have hm := mul_le_mul_of_nonneg_left hM hF.L1_nonneg
  have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (x - p))
  nlinarith

lemma residual_local_bounds {X : Set E} {P F : E → E} {L0 L1 M r γ C ε : ℝ}
    (hP : Proj X P) (hF : GeneralizedMonotone.Hyp F L0 L1)
    (hr : 0 ≤ r) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hC : L0 + L1 * M + L1 * ε + r ≤ C) (hsmall : γ * C ≤ 1 / 64)
    (p c x e : E) (hp : p ∈ X) (hn : Normal X p (-(F p + r • (p - c))))
    (hM : ‖F p‖ ≤ M) (hx : ‖x - p‖ ≤ γ * ε / 32) (he : ‖e‖ ≤ ε / 32) :
    ‖(F x + r • (x - c)) - (F p + r • (p - c))‖ ≤ 4 * C * ‖x - p‖ ∧
      ‖F (P (x - γ • (F x + r • (x - c) + e))) - F x‖ ≤
        4 * C * ‖P (x - γ • (F x + r • (x - c) + e)) - x‖ := by
  have h1 := hF.L1_nonneg
  have h0 := hF.L0_pos
  have hM0 := (norm_nonneg (F p)).trans hM
  have hC0 : 0 < C := by nlinarith [mul_nonneg h1 hM0, mul_nonneg h1 hε]
  have hLe : L1 * ε ≤ C := by nlinarith [mul_nonneg h1 hM0]
  have hγε := mul_le_mul_of_nonneg_left hLe hγ.le
  have hxL := mul_le_mul_of_nonneg_left hx h1
  have hxcap : L1 * ‖x - p‖ ≤ 1 / 2 := by nlinarith
  have hdiff := local_regularized_difference hF hr c x p hM hxcap
  have hcoef : 2 * (L0 + L1 * M) + r ≤ 4 * C := by
    nlinarith [mul_nonneg h1 hε]
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x - p)))
  refine ⟨hdiff', ?_⟩
  let y := P (x - γ • (F x + r • (x - c) + e))
  have hy := hP.noisy_root_distance (H := fun z => F z + r • (z - c)) hp hn hγ.le x e
  have hdiffγ := mul_le_mul_of_nonneg_left hdiff' hγ.le
  have hγC := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (x - p))
  have heγ := mul_le_mul_of_nonneg_left he hγ.le
  have hyp : ‖y - p‖ ≤ 3 * γ * ε / 32 := by dsimp [y]; nlinarith
  have hxy : ‖x - y‖ ≤ γ * ε / 8 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x p y
    rw [norm_sub_rev p y] at ht
    linarith
  have hxyL := mul_le_mul_of_nonneg_left hxy h1
  have hxycap : L1 * ‖x - y‖ ≤ 1 / 2 := by nlinarith
  have hFx := local_operator_difference hF p x (by simpa only [norm_sub_rev p x] using hxcap)
  rw [norm_sub_rev p x] at hFx
  have htri := norm_add_le (F x - F p) (F p)
  rw [sub_add_cancel] at htri
  rw [norm_sub_rev (F p) (F x)] at hFx
  have hA : L0 + L1 * M ≤ C := by nlinarith [mul_nonneg h1 hε]
  have hAM := mul_le_mul_of_nonneg_left hM h1
  have hAMd := mul_le_mul_of_nonneg_right hAM (norm_nonneg (x - p))
  have hAd := mul_le_mul_of_nonneg_right hA (norm_nonneg (x - p))
  have hFx' : ‖F x‖ ≤ M + 2 * C * ‖x - p‖ := by nlinarith
  have hFxL := mul_le_mul_of_nonneg_left hFx' h1
  have hcapC := mul_le_mul_of_nonneg_left hxcap hC0.le
  have hAx : L0 + L1 * ‖F x‖ ≤ 2 * C := by nlinarith
  have hl := local_operator_difference hF x y hxycap
  have hAx' := mul_le_mul_of_nonneg_right hAx (norm_nonneg (x - y))
  change ‖F y - F x‖ ≤ 4 * C * ‖y - x‖
  rw [norm_sub_rev (F y) (F x), norm_sub_rev y x]
  nlinarith

lemma tuned_residual_certificate {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε)
    (p c x e : E) (hp : p ∈ X)
    (hn : Normal X p (-(F p + regularization t (stageCount t - 1) • (p - c))))
    (hM : ‖F p‖ ≤ rootBound t)
    (hx : ‖x - p‖ ≤ radius t (stageCount t - 1) / 2)
    (he : ‖e‖ ≤ t.ε / 32)
    (hbias : regularization t (stageCount t - 1) * ‖p - c‖ ≤ t.ε / 4) :
    residualOutput P t c x (F x + e) ∈ X ∧
      ∃ η, Normal X (residualOutput P t c x (F x + e)) η ∧
        ‖F (residualOutput P t c x (F x + e)) + η‖ ≤ t.ε := by
  let r := regularization t (stageCount t - 1)
  let C := t.L0 + t.L1 * rootBound t + t.L1 * t.ε + r
  have hr : 0 < r := regularization_pos t hR hε _
  have hM0 : 0 ≤ rootBound t := (norm_nonneg (F p)).trans hM
  have h0 := hF.L0_pos
  have h1 := hF.L1_nonneg
  have hC : 0 < C := by dsimp [C]; positivity
  have hγ : 0 < finalStepSize t := by unfold finalStepSize; change 0 < 1 / (64 * C); positivity
  have hγC : finalStepSize t * C = 1 / 64 := by
    unfold finalStepSize
    change 1 / (64 * C) * C = 1 / 64
    field_simp
  have hxc := hx.trans (last_radius_certificate t h0 h1 hR hG hε)
  have hb := residual_local_bounds hP hF hr.le hγ hε.le (le_refl C) hγC.le
    p c x e hp hn hM hxc he
  have hrC : r ≤ C := by dsimp [C]; nlinarith [mul_nonneg h1 hM0, mul_nonneg h1 hε.le]
  have hγr := mul_le_mul_of_nonneg_left hrC hγ.le
  have hout : residualOutput P t c x (F x + e) =
      P (x - finalStepSize t • (F x + r • (x - c) + e)) := by
    unfold residualOutput ClippedExtragradient.regularizedReply
    congr 2
    module
  rw [hout]
  exact hP.regularized_residual_certificate hp hn hr.le hγ hε.le (by positivity : 0 ≤ 4 * C)
    (by nlinarith [hγC] : finalStepSize t * (4 * C) ≤ 1)
    (by nlinarith [hγC] : finalStepSize t * r ≤ 1) hxc he hbias hb.1 hb.2

end OracleTemplate.ProjectedClippedExtragradient
