import LongTails.Proofs.UniversalRegularizedStep
import LongTails.Proofs.AnchoredExtragradientStep

open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

open HolderMonotone (reg)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_root_value {F : E → E} {r : ℝ} {c p : E}
    (hp : reg F r c p = 0) : F p = -(r • (p - c)) := by
  exact eq_neg_of_add_eq_zero_left hp

lemma root_nonexpansive {F : E → E} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {a b p q : E} (hp : reg F r a p = 0) (hq : reg F r b q = 0) :
    ‖p - q‖ ≤ ‖a - b‖ := by
  have he : F p - F q = r • (a - b) - r • (p - q) := by
    rw [regularized_root_value hp, regularized_root_value hq]
    module
  have hm := hmono p q
  rw [he, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hm
  have hf : ‖p - q‖ ^ 2 ≤ ⟪a - b, p - q⟫ := by
    by_contra hn
    have hn := lt_of_not_ge hn
    nlinarith [mul_pos hr (sub_pos.mpr hn)]
  have hi := real_inner_le_norm (a - b) (p - q)
  by_contra hn
  have hn := lt_of_not_ge hn
  nlinarith [norm_nonneg (p - q), norm_nonneg (a - b)]

noncomputable def regularizedZero [FiniteDimensional ℝ E] (F : E → E)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (r : ℝ) (hr : 0 < r) (c : E) : E :=
  Classical.choose (HolderMonotone.exists_reg_zero hc hmono hr c)

lemma regularizedZero_spec [FiniteDimensional ℝ E] (F : E → E)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (r : ℝ) (hr : 0 < r) (c : E) :
    reg F r c (regularizedZero F hc hmono r hr c) = 0 :=
  Classical.choose_spec (HolderMonotone.exists_reg_zero hc hmono hr c)

lemma regularizedZero_continuous [FiniteDimensional ℝ E] (F : E → E)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (r : ℝ) (hr : 0 < r) : Continuous (regularizedZero F hc hmono r hr) := by
  have hh : LipschitzWith 1 (regularizedZero F hc hmono r hr) :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      exact root_nonexpansive hr hmono (regularizedZero_spec F hc hmono r hr a)
        (regularizedZero_spec F hc hmono r hr b))
  exact hh.continuous

lemma root_transport {F : E → E} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {c w p q : E} (hp : reg F r c p = 0)
    (hq : reg F (2 * r) ((1 / 2 : ℝ) • (c + w)) q = 0) :
    ‖q - p‖ ≤ ‖w - p‖ / 2 ∧ ‖q - w‖ ≤ ‖w - p‖ ∧
      ‖F q - F p‖ ≤ 2 * r * ‖w - p‖ := by
  have he : F q - F p = r • (w - p) - (2 * r) • (q - p) := by
    rw [regularized_root_value hp, regularized_root_value hq]
    module
  have hm := hmono q p
  rw [he, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hm
  have hf : 2 * ‖q - p‖ ^ 2 ≤ ⟪w - p, q - p⟫ := by
    by_contra hn
    have hn := lt_of_not_ge hn
    nlinarith [mul_pos hr (sub_pos.mpr hn)]
  have hn : ‖q - p‖ ≤ ‖w - p‖ / 2 := by
    have hi := real_inner_le_norm (w - p) (q - p)
    by_contra hh
    have hh := lt_of_not_ge hh
    nlinarith [norm_nonneg (w - p), norm_nonneg (q - p)]
  refine ⟨hn, ?_, ?_⟩
  · have he' : q - w = (q - p) - (w - p) := by abel
    have hi : ⟪q - p, w - p⟫ = ⟪w - p, q - p⟫ := real_inner_comm _ _
    have hs := norm_sub_sq_real (q - p) (w - p)
    rw [← he', hi] at hs
    nlinarith [sq_nonneg ‖q - p‖, norm_nonneg (q - w), norm_nonneg (w - p)]
  · rw [he]
    have ht := norm_sub_le (r • (w - p)) ((2 * r) • (q - p))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hr, abs_of_pos (by positivity : 0 < 2 * r)] at ht
    nlinarith

lemma regularized_signal_bound {F : E → E} {r d ε : ℝ}
    (hr : 0 ≤ r) {c p x : E} (hp : reg F r c p = 0)
    (hF : ‖F p‖ ≤ ε) (hx : ‖x - p‖ ≤ 3 * d) :
    ‖F x‖ ≤ ‖reg F r c x‖ + 3 * r * d + ε := by
  have he : F x = (reg F r c x - r • (x - p)) + F p := by
    rw [regularized_root_value hp]
    unfold reg
    module
  have h1 := norm_add_le (reg F r c x - r • (x - p)) (F p)
  have h2 := norm_sub_le (reg F r c x) (r • (x - p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at h2
  have h3 := mul_le_mul_of_nonneg_left hx hr
  rw [← he] at h1
  linarith

lemma regularized_local {F : E → E} {L0 L1 r d ε : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hc : Continuous F)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    {c p x y : E} (hp : reg F r c p = 0) (hF : ‖F p‖ ≤ ε)
    (hx : ‖x - p‖ ≤ 3 * d) (hshort : L1 * ‖x - y‖ ≤ 1 / 2) :
    ‖reg F r c y - reg F r c x‖ ≤
      2 * (L0 + r + L1 * (ε + 4 * r * d) + L1 * ‖reg F r c x‖) * ‖x - y‖ := by
  have hloc := GeneralizedMonotone.local_bound hL0 hL1 hc hlip x y (by linarith)
  have hhalf : ‖F x - F y‖ ≤ 2 * (L0 + L1 * ‖F x‖) * ‖x - y‖ := by
    have hn := mul_nonneg (norm_nonneg (F x - F y)) (by linarith : 0 ≤ 1 / 2 - L1 * ‖x - y‖)
    nlinarith
  have hsignal := regularized_signal_bound hr hp hF hx
  have hreg := norm_add_le (F y - F x) (r • (y - x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, norm_sub_rev y x,
    norm_sub_rev (F y) (F x)] at hreg
  rw [HolderMonotone.reg_sub]
  have hsignal' := mul_le_mul_of_nonneg_left hsignal hL1
  have hmult := mul_le_mul_of_nonneg_right hsignal' (norm_nonneg (x - y))
  have hn := mul_nonneg (mul_nonneg hL1 (mul_nonneg hr hd)) (norm_nonneg (x - y))
  have hn' := mul_nonneg hr (norm_nonneg (x - y))
  nlinarith

end OracleTemplate.ClippedExtragradient
