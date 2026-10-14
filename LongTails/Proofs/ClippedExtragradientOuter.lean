import LongTails.Proofs.GeneralizedMonotoneRegularization
import LongTails.Proofs.ClippedExtragradientTuning

open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma initial_regularized_root {F : E → E} (t : Tuning)
    (hR : 0 < t.R) (hε : 0 < t.ε)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (x0 xstar p : E) (hstar : F xstar = 0) (hd : ‖x0 - xstar‖ ≤ t.R)
    (hp : HolderMonotone.reg F (regularization t 0) x0 p = 0) :
    ‖p - x0‖ ≤ radius t 0 ∧ ‖F p‖ ≤ t.ε / (8 * stageCount t) := by
  have hr := regularization_pos t hR hε 0
  have hi := HolderMonotone.anchor_dist hmono hr hp hstar
  have hd0 : radius t 0 = t.R := by simp [radius]
  have hdist : ‖p - x0‖ ≤ radius t 0 := by rw [hd0]; exact hi.trans hd
  refine ⟨hdist, ?_⟩
  rw [regularized_root_value hp, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hm := mul_le_mul_of_nonneg_left hdist hr.le
  rw [regularization_radius t hR.ne' 0] at hm
  exact hm

lemma transport_stage {F : E → E} (t : Tuning)
    (hR : 0 < t.R) (hε : 0 < t.ε)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (s : ℕ) (anchor output p q : E)
    (hp : HolderMonotone.reg F (regularization t s) anchor p = 0)
    (hq : HolderMonotone.reg F (regularization t (s + 1))
      ((1 / 2 : ℝ) • (anchor + output)) q = 0)
    (hgood : ‖output - p‖ ≤ radius t s / 2)
    (hF : ‖F p‖ ≤ (s + 1 : ℕ) * (t.ε / (8 * stageCount t))) :
    ‖q - output‖ ≤ radius t (s + 1) ∧
      ‖F q‖ ≤ (s + 2 : ℕ) * (t.ε / (8 * stageCount t)) := by
  have hr := regularization_pos t hR hε s
  rw [regularization_succ] at hq
  have ht := root_transport hr hmono hp hq
  refine ⟨?_, ?_⟩
  · rw [radius_succ]
    exact ht.2.1.trans hgood
  · have hh := norm_le_norm_sub_add (F q) (F p)
    have hm := mul_le_mul_of_nonneg_left hgood (show 0 ≤ 2 * regularization t s by positivity)
    have he : 2 * regularization t s * (radius t s / 2) = t.ε / (8 * stageCount t) := by
      calc
        _ = regularization t s * radius t s := by ring
        _ = _ := regularization_radius t hR.ne' s
    rw [he] at hm
    push_cast at hF ⊢
    linarith [ht.2.2]

lemma residual_from_close_root {F : E → E} {L0 L1 ε d : ℝ}
    (h0 : 0 ≤ L0) (h1 : 0 ≤ L1) (hε : 0 < ε) (hd : 0 ≤ d)
    (hc : Continuous F)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    {p w : E} (hroot : ‖F p‖ ≤ ε / 4) (hclose : ‖w - p‖ ≤ d / 2)
    (hscale : (L0 + L1 * ε) * d ≤ ε / 32) : ‖F w‖ ≤ ε := by
  have hLd : L1 * d ≤ 1 / 32 := by
    have hh := mul_nonneg h0 hd
    nlinarith
  have hdist : ‖p - w‖ ≤ d / 2 := by simpa only [norm_sub_rev] using hclose
  have hshort : L1 * ‖p - w‖ ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hdist h1
    linarith
  have hl := GeneralizedMonotone.local_bound h0 h1 hc hlip p w (by linarith)
  have hden := mul_nonneg (norm_nonneg (F p - F w))
    (show 0 ≤ 1 / 2 - L1 * ‖p - w‖ by linarith)
  have hlocal : ‖F p - F w‖ ≤ 2 * (L0 + L1 * ‖F p‖) * ‖p - w‖ := by nlinarith
  have hcoef : 0 ≤ L0 + L1 * ε := by positivity
  have hroot' : L0 + L1 * ‖F p‖ ≤ L0 + L1 * ε := by nlinarith
  have h1' := mul_le_mul_of_nonneg_right hroot' (norm_nonneg (p - w))
  have h2' := mul_le_mul_of_nonneg_left hdist hcoef
  have hn := norm_le_norm_sub_add (F w) (F p)
  rw [norm_sub_rev (F w) (F p)] at hn
  nlinarith

end OracleTemplate.ClippedExtragradient
