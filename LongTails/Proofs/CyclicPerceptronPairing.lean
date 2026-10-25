import LongTails.Proofs.CyclicPerceptronBootstrap
import Mathlib.Analysis.InnerProductSpace.ProdL2

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronPairing

open LongTails.Setups.CyclicFullWidthPerceptron
open CyclicPerceptronBlocks CyclicPerceptronBounds CyclicPerceptronBootstrap

abbrev Hidden (d : ℕ) := WithLp 2 (ℝ × Features d)

noncomputable def hiddenHead {d : ℕ} (θ : Space d) : Hidden d :=
  WithLp.toLp 2 (θ.b, θ.head)

noncomputable def hiddenFeature {d : ℕ} (θ : Space d) (q : Input d) : Hidden d :=
  WithLp.toLp 2 (linearPart θ q)

lemma margin_hidden {d : ℕ} (θ : Space d) (q : Input d) :
    margin q θ = ⟪hiddenHead θ, hiddenFeature θ q⟫ := by
  simp [margin, hiddenHead, hiddenFeature, WithLp.prod_inner_apply, mul_comm]

lemma hidden_norm_le {d : ℕ} (a : ℝ) (v : Features d) :
    ‖WithLp.toLp 2 (a, v)‖ ≤ |a| + ‖v‖ := by
  have he := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a, v))
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs] at he
  nlinarith [abs_nonneg a, norm_nonneg v, norm_nonneg (WithLp.toLp 2 (a, v))]

lemma inner_perturbation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h e f : E) (a b : ℝ) :
    |⟪a • h + e, b • h + f⟫ - a * b * ‖h‖ ^ 2| ≤
      |a| * ‖h‖ * ‖f‖ + |b| * ‖h‖ * ‖e‖ + ‖e‖ * ‖f‖ := by
  have he : ⟪a • h + e, b • h + f⟫ - a * b * ‖h‖ ^ 2 =
      a * ⟪h, f⟫ + b * ⟪e, h⟫ + ⟪e, f⟫ := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [he]
  have ha := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm h f) (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm e h) (abs_nonneg b)
  have hc := abs_real_inner_le_norm e f
  have ht := abs_add_le (a * ⟪h, f⟫) (b * ⟪e, h⟫)
  have ht' := abs_add_le (a * ⟪h, f⟫ + b * ⟪e, h⟫) ⟪e, f⟫
  rw [abs_mul, abs_mul] at ht
  nlinarith

lemma small_perturbation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h e f : E) (a b η t : ℝ) (hη : 0 < η) (ht : 0 ≤ t) (ht₁ : t ≤ 1 / 4096)
    (hh : ‖h‖ ≤ 3) (ha : |a| ≤ 2) (hb : |b| ≤ 2 * η)
    (he : ‖e‖ ≤ 32 * t) (hf : ‖f‖ ≤ 8 * η * t) :
    |⟪a • h + e, b • h + f⟫ - a * b * ‖h‖ ^ 2| ≤ η / 2 := by
  have hbound : |a| * ‖h‖ * ‖f‖ + |b| * ‖h‖ * ‖e‖ + ‖e‖ * ‖f‖ ≤
      2 * 3 * (8 * η * t) + (2 * η) * 3 * (32 * t) + (32 * t) * (8 * η * t) := by
    gcongr
  have ht₂ : t ^ 2 ≤ t := by nlinarith
  have hpoly : 240 * t + 256 * t ^ 2 ≤ 1 / 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hpoly hη.le
  exact (inner_perturbation h e f a b).trans (by nlinarith)

lemma positive_inner_of_error (x L r η : ℝ) (hη : 0 < η) (hr : 9 / 10 ≤ r)
    (hL : η ≤ L) (he : |x - L * r ^ 2| ≤ η / 2) : 0 < x := by
  have hr₂ : (81 : ℝ) / 100 ≤ r ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg r)
  have hm' := mul_le_mul_of_nonneg_left hr₂ hη.le
  have ht := (abs_le.mp he).1
  nlinarith

lemma negative_inner_of_error (x L r η : ℝ) (hη : 0 < η) (hr : 9 / 10 ≤ r)
    (hL : L ≤ -η) (he : |x - L * r ^ 2| ≤ η / 2) : x < 0 := by
  have hr₂ : (81 : ℝ) / 100 ≤ r ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg r)
  have hm' := mul_le_mul_of_nonneg_left hr₂ hη.le
  have ht := (abs_le.mp he).2
  nlinarith

lemma reference_feature_bounds {d : ℕ} (η μ H : ℝ) (c : Coordinates d)
    (hη : 0 < η) (hμ : 0 < μ) (hμ₁ : μ ≤ 1) (hH : 1 ≤ H)
    (hsmall : η ^ 2 * H ≤ 1 / 1024) (hc : Envelope H c)
    (ha : |c.a - 1| ≤ 5 * η ^ 2 * H) :
    9 / 10 ≤ ‖hiddenFeature (realize η μ c) (1, 0)‖ ∧
      ‖hiddenFeature (realize η μ c) (1, 0)‖ ≤ 3 := by
  have he : hiddenFeature (realize η μ c) (1, 0) =
      WithLp.toLp 2 (c.a, -(η ^ 2 * μ) • c.X) := by
    simp [hiddenFeature, linearPart, realize]
  rw [he]
  have hnorm := hidden_norm_le c.a (-(η ^ 2 * μ) • c.X)
  have hfirst := WithLp.norm_fst_le ℝ (WithLp.toLp 2 (c.a, -(η ^ 2 * μ) • c.X))
  simp only [WithLp.toLp_fst, Real.norm_eq_abs] at hfirst
  have hp : η ^ 2 * μ * H ≤ 1 / 1024 := by
    have hm := mul_le_mul_of_nonneg_left hμ₁ (show 0 ≤ η ^ 2 * H by positivity)
    nlinarith
  have hx : ‖-(η ^ 2 * μ) • c.X‖ ≤ 4 * η ^ 2 * μ * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hc.X_bound (show 0 ≤ η ^ 2 * μ by positivity)
    nlinarith
  constructor
  · have ht := (abs_le.mp ha).1
    nlinarith [le_abs_self c.a]
  · nlinarith [hc.a_bound]

lemma head_norm_bound {d : ℕ} (η μ H : ℝ) (c : Coordinates d)
    (hη : 0 < η) (hμ : 0 < μ) (hμ₁ : μ ≤ 1) (hH : 1 ≤ H)
    (hsmall : η ^ 2 * H ≤ 1 / 1024) (hc : Envelope H c) :
    ‖hiddenHead (realize η μ c)‖ ≤ 5 * η * μ * H := by
  have hp : 16 * η ^ 2 * μ * H + 4 ≤ 5 := by
    have hm := mul_le_mul_of_nonneg_left hμ₁ (show 0 ≤ η ^ 2 * H by positivity)
    nlinarith
  have ht := hidden_norm_le (η ^ 3 * μ ^ 2 * c.B) (-(η * μ) • c.S)
  have hb : |η ^ 3 * μ ^ 2 * c.B| ≤ 16 * η ^ 3 * μ ^ 2 * H ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hc.B_bound (show 0 ≤ η ^ 3 * μ ^ 2 by positivity)
    nlinarith
  have hs : ‖-(η * μ) • c.S‖ ≤ 4 * η * μ * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hc.S_bound (show 0 ≤ η * μ by positivity)
    nlinarith
  change ‖WithLp.toLp 2 (η ^ 3 * μ ^ 2 * c.B, -(η * μ) • c.S)‖ ≤ _
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ η * μ * H by positivity)
  nlinarith

lemma residual_feature_bound {d : ℕ} (η μ H : ℝ) (c : Coordinates d) (u : Features d)
    (hη : 0 < η) (hμ : 0 < μ) (hμ₁ : μ ≤ 1) (hH : 1 ≤ H)
    (hsmall : η ^ 2 * H ≤ 1 / 1024) (hc : Envelope H c) (hu : ‖u‖ ≤ 1) :
    ‖hiddenFeature (realize η μ c) (0, u)‖ ≤ 3 := by
  have he : hiddenFeature (realize η μ c) (0, u) =
      WithLp.toLp 2 (-(η ^ 2 * μ) * ⟪c.R, u⟫, c.F u) := by
    simp [hiddenFeature, linearPart, realize, real_inner_smul_left]
  rw [he]
  have hp : η ^ 2 * μ * H ≤ 1 / 1024 := by
    have hm := mul_le_mul_of_nonneg_left hμ₁ (show 0 ≤ η ^ 2 * H by positivity)
    nlinarith
  have hi : |⟪c.R, u⟫| ≤ 4 * H := by
    have hm := mul_le_mul hc.R_bound hu (norm_nonneg _) (by positivity)
    exact (abs_real_inner_le_norm _ _).trans (by simpa using hm)
  have hr : |-(η ^ 2 * μ) * ⟪c.R, u⟫| ≤ 4 * η ^ 2 * μ * H := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ η ^ 2 * μ by positivity)
    nlinarith
  have hF : ‖c.F u‖ ≤ 2 := by
    have hm := mul_le_mul hc.matrix_bound hu (norm_nonneg _) (by norm_num)
    exact (c.F.le_opNorm u).trans (by simpa using hm)
  have ht := hidden_norm_le (-(η ^ 2 * μ) * ⟪c.R, u⟫) (c.F u)
  linarith

lemma hiddenHead_update {d : ℕ} (θ : Space d) (q : Input d) (η : ℝ) :
    hiddenHead (move θ η (direction q θ)) = hiddenHead θ + η • hiddenFeature θ q := rfl

lemma hiddenFeature_update {d : ℕ} (θ : Space d) (q x : Input d) (η : ℝ) :
    hiddenFeature (move θ η (direction q θ)) x = hiddenFeature θ x +
      (η * (q.1 * x.1 + ⟪q.2, x.2⟫)) • hiddenHead θ := by
  unfold hiddenFeature
  rw [linearPart_update]
  rfl

lemma hiddenFeature_negative {d : ℕ} (θ : Space d) (c μ : ℝ) (u : Features d) :
    hiddenFeature θ (-c, -μ • u) =
      -c • hiddenFeature θ (1, 0) - μ • hiddenFeature θ (0, u) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [hiddenFeature, linearPart, real_inner_smul_right]
    ring
  · simp [hiddenFeature, linearPart]
    module

lemma pairing_signs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h v gi gj : E) (η μ c cj t ℓ : ℝ) (hη : 0 < η) (hη₁ : η ^ 2 ≤ 1)
    (hμ : 0 ≤ μ) (hμt : μ ≤ t) (ht : 0 ≤ t) (ht₁ : t ≤ 1 / 4096)
    (hc : 1 ≤ c) (hc₂ : c ≤ 2) (hcj : 1 ≤ cj) (hcj₂ : cj ≤ 2) (hℓ : |ℓ| ≤ 5)
    (hh : 9 / 10 ≤ ‖h‖) (hh₃ : ‖h‖ ≤ 3) (hv : ‖v‖ ≤ 5 * η * t)
    (hgi : ‖gi‖ ≤ 3) (hgj : ‖gj‖ ≤ 3) :
    0 < ⟪h + η • v, η • h + v⟫ ∧
      ⟪-cj • h + (-μ • gj - (η * cj) • v), η • h + v⟫ < 0 ∧
      ⟪h - (η * c) • v, -(η * c) • h + (v - (η * μ) • gi)⟫ < 0 ∧
      0 < ⟪-cj • h + (-μ • gj + (η * ℓ) • v),
        -(η * c) • h + (v - (η * μ) • gi)⟫ := by
  have hc0 : 0 ≤ c := by linarith
  have hb : |-(η * c)| ≤ 2 * η := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  have hcj0 : 0 ≤ cj := by linarith
  have ha : |-cj| ≤ 2 := by simpa only [abs_neg, abs_of_nonneg hcj0] using hcj₂
  have hv' : ‖v‖ ≤ 8 * η * t := by nlinarith
  have hηv : ‖η • v‖ ≤ 5 * t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hm := mul_le_mul_of_nonneg_left hv hη.le
    have hm' := mul_le_mul_of_nonneg_right hη₁ ht
    nlinarith
  have hcv : ‖(η * c) • v‖ ≤ 10 * t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ η * c by positivity)
    have hm' := mul_le_mul hη₁ hc₂ hc0 (by norm_num)
    have hm'' := mul_le_mul_of_nonneg_right hm' ht
    nlinarith
  have hcjv : ‖(η * cj) • v‖ ≤ 10 * t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ η * cj by positivity)
    have hm' := mul_le_mul hη₁ hcj₂ hcj0 (by norm_num)
    have hm'' := mul_le_mul_of_nonneg_right hm' ht
    nlinarith
  have hℓv : ‖(η * ℓ) • v‖ ≤ 25 * t := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hη]
    have hm := mul_le_mul hℓ hv (norm_nonneg v) (by norm_num)
    have hm' := mul_le_mul_of_nonneg_left hm hη.le
    have hm'' := mul_le_mul_of_nonneg_right hη₁ ht
    nlinarith
  have hμg : ‖-μ • gj‖ ≤ 3 * t := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hμ]
    have hm := mul_le_mul hμt hgj (norm_nonneg gj) ht
    nlinarith
  have hf : ‖v - (η * μ) • gi‖ ≤ 8 * η * t := by
    have hg : ‖(η * μ) • gi‖ ≤ 3 * η * t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hm := mul_le_mul hμt hgi (norm_nonneg gi) ht
      have hm' := mul_le_mul_of_nonneg_left hm hη.le
      nlinarith
    exact (norm_sub_le _ _).trans (by linarith)
  have heP : ‖-μ • gj - (η * cj) • v‖ ≤ 32 * t :=
    (norm_sub_le _ _).trans (by linarith)
  have heN : ‖-μ • gj + (η * ℓ) • v‖ ≤ 32 * t :=
    (norm_add_le _ _).trans (by linarith)
  have heR : ‖-(η * c) • v‖ ≤ 32 * t := by
    simpa only [neg_smul, norm_neg] using (hcv.trans (by linarith : 10 * t ≤ 32 * t))
  have hP := small_perturbation h (η • v) v 1 η η t hη ht ht₁ hh₃
    (by norm_num) (by rw [abs_of_pos hη]; linarith) (by linarith) hv'
  have hPn := small_perturbation h (-μ • gj - (η * cj) • v) v (-cj) η η t
    hη ht ht₁ hh₃ ha (by rw [abs_of_pos hη]; linarith) heP hv'
  have hN := small_perturbation h (-(η * c) • v) (v - (η * μ) • gi) 1 (-(η * c)) η t
    hη ht ht₁ hh₃ (by norm_num) hb heR hf
  have hNn := small_perturbation h (-μ • gj + (η * ℓ) • v)
    (v - (η * μ) • gi) (-cj) (-(η * c)) η t hη ht ht₁ hh₃ ha hb heN hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [one_smul] using positive_inner_of_error _ (1 * η) ‖h‖ η hη hh (by simp) hP
  · exact negative_inner_of_error _ (-cj * η) ‖h‖ η hη hh (by nlinarith) hPn
  · have h := negative_inner_of_error _ (1 * -(η * c)) ‖h‖ η hη hh (by nlinarith) hN
    simpa only [one_smul, neg_smul, ← sub_eq_add_neg] using h
  · apply positive_inner_of_error _ (-cj * -(η * c)) ‖h‖ η hη hh _ hNn
    have hc' : 1 ≤ cj * c := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hc' hη.le
    nlinarith

lemma margin_after_update {d : ℕ} (θ : Space d) (q x : Input d) (η : ℝ) :
    margin x (move θ η (direction q θ)) =
      ⟪hiddenFeature θ x + (η * (q.1 * x.1 + ⟪q.2, x.2⟫)) • hiddenHead θ,
        hiddenHead θ + η • hiddenFeature θ q⟫ := by
  rw [margin_hidden, hiddenHead_update, hiddenFeature_update]
  exact real_inner_comm _ _

lemma unbalanced_margins {d : ℕ} (θ : Space d) (η μ c cj t : ℝ) (ui uj : Features d)
    (hη : 0 < η) (hη₁ : η ^ 2 ≤ 1) (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (hμt : μ ≤ t)
    (ht : 0 ≤ t) (ht₁ : t ≤ 1 / 4096) (hc : 1 ≤ c) (hc₂ : c ≤ 2) (hcj : 1 ≤ cj) (hcj₂ : cj ≤ 2)
    (hui : ‖ui‖ ≤ 1) (huj : ‖uj‖ ≤ 1)
    (hh : 9 / 10 ≤ ‖hiddenFeature θ (1, 0)‖) (hh₃ : ‖hiddenFeature θ (1, 0)‖ ≤ 3)
    (hv : ‖hiddenHead θ‖ ≤ 5 * η * t)
    (hgi : ‖hiddenFeature θ (0, ui)‖ ≤ 3) (hgj : ‖hiddenFeature θ (0, uj)‖ ≤ 3) :
    0 < margin (1, 0) (move θ η (direction (1, 0) θ)) ∧
      margin (-cj, -μ • uj) (move θ η (direction (1, 0) θ)) < 0 ∧
      margin (1, 0) (move θ η (direction (-c, -μ • ui) θ)) < 0 ∧
      0 < margin (-cj, -μ • uj) (move θ η (direction (-c, -μ • ui) θ)) := by
  have hij : |⟪ui, uj⟫| ≤ 1 := by
    exact (abs_real_inner_le_norm _ _).trans
      (by nlinarith [mul_le_mul hui huj (norm_nonneg _) (by norm_num)])
  have hℓ : |c * cj + μ ^ 2 * ⟪ui, uj⟫| ≤ 5 := by
    have hc' : c * cj ≤ 4 := by nlinarith
    have hcc : 0 ≤ c * cj := by positivity
    have hμ' : μ ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul hμ' hij (abs_nonneg _) (by norm_num)
    have ht := abs_add_le (c * cj) (μ ^ 2 * ⟪ui, uj⟫)
    simp only [abs_of_nonneg hcc, abs_mul, abs_of_nonneg (sq_nonneg μ)] at ht
    nlinarith
  obtain ⟨hP, hPn, hN, hNn⟩ := pairing_signs
    (hiddenFeature θ (1, 0)) (hiddenHead θ) (hiddenFeature θ (0, ui))
    (hiddenFeature θ (0, uj)) η μ c cj t (c * cj + μ ^ 2 * ⟪ui, uj⟫)
    hη hη₁ hμ hμt ht ht₁ hc hc₂ hcj hcj₂ hℓ hh hh₃ hv hgi hgj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [margin_after_update]
    simpa only [mul_one, inner_zero_left, add_zero, zero_add, add_comm] using hP
  · rw [margin_after_update, hiddenFeature_negative]
    simp only [one_mul, inner_zero_left, add_zero]
    convert hPn using 1; congr 1 <;> module
  · rw [margin_after_update, hiddenFeature_negative]
    simp only [mul_one, inner_zero_right, add_zero]
    convert hN using 1; congr 1 <;> module
  · rw [margin_after_update, hiddenFeature_negative, hiddenFeature_negative]
    simp only [real_inner_smul_left, real_inner_smul_right]
    convert hNn using 1; congr 1 <;> module

end LongTails.Proofs.CyclicPerceptronPairing
