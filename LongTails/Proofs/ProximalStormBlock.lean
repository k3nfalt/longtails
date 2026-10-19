import LongTails.Proofs.ProximalStormOuter

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

local notation "P" => Measure.infinitePi fun _ : ℕ => p


lemma lint_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) :
    ∫⁻ x, ENNReal.ofReal (u x) ∂μ + ∫⁻ x, ENNReal.ofReal (v x) ∂μ =
      ∫⁻ x, ENNReal.ofReal (u x + v x) ∂μ := by
  rw [← lintegral_add_left hu.ennreal_ofReal]
  exact lintegral_congr fun x => (ENNReal.ofReal_add (hu0 x) (hv0 x)).symm

lemma lint_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ} (hu : Measurable u)
    {k : ℝ} (hk : 0 ≤ k) :
    ENNReal.ofReal k * ∫⁻ x, ENNReal.ofReal (u x) ∂μ = ∫⁻ x, ENNReal.ofReal (k * u x) ∂μ := by
  rw [← lintegral_const_mul _ hu.ennreal_ofReal]
  exact lintegral_congr fun x => (ENNReal.ofReal_mul hk).symm

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.block_path (H : Hyp p f g Lbar Γ xstar) {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    {B : ℕ} (hB1 : 1 ≤ B) (hB : 6 * Γ ^ 2 ≤ B) (y z y' : E) :
    (A + aNext lam A) * (f y' - f xstar) +
        1 / 2 * ‖z - aNext lam A • gradient f y' - xstar‖ ^ 2 +
        1 / 2 * ((B : ℝ) * ((aNext lam A / B) ^ 2 * (Γ ^ 2 * ‖gradient f y'‖ ^ 2))) +
        (A + aNext lam A) / (3 * lam) * ‖y' - mixPt lam A y z‖ ^ 2 ≤
      outerPot f xstar (A, y, z) + 2 * (A + aNext lam A) / (3 * lam) *
        (lam ^ 2 * ‖phiGrad f lam (mixPt lam A y z) y'‖ ^ 2) := by
  have h := H.hpe_step hlam hA y z y'
  set aN := aNext lam A
  set A' := A + aN
  set xt := mixPt lam A y z
  set X2 := lam ^ 2 * ‖phiGrad f lam xt y'‖ ^ 2
  set Y2 := ‖y' - xt‖ ^ 2
  have haN := aNext_pos hlam hA
  have hA' : 0 < A' := by simp only [A']; linarith
  have hsq : aN ^ 2 = lam * A' := aNext_sq hlam hA
  have hX : ‖lam • phiGrad f lam xt y'‖ ^ 2 = X2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hX] at h
  have hv : lam ^ 2 * ‖gradient f y'‖ ^ 2 ≤ 2 * X2 + 2 * Y2 := by
    have he : lam • gradient f y' = lam • phiGrad f lam xt y' - (y' - xt) := by
      simp only [phiGrad, smul_add, smul_smul, mul_one_div_cancel hlam.ne', one_smul]; abel
    have hn : ‖lam • gradient f y'‖ ^ 2 ≤ 2 * ‖lam • phiGrad f lam xt y'‖ ^ 2 + 2 * Y2 := by
      rw [he, sub_eq_add_neg]
      have := NormalizedStorm.sq_norm_add_le (lam • phiGrad f lam xt y') (-(y' - xt))
      rwa [norm_neg] at this
    rw [hX, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hn
    exact hn
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  have hbatch : 1 / 2 * ((B : ℝ) * ((aN / B) ^ 2 * (Γ ^ 2 * ‖gradient f y'‖ ^ 2))) ≤
      A' / (6 * lam) * (X2 + Y2) := by
    have e : 1 / 2 * ((B : ℝ) * ((aN / B) ^ 2 * (Γ ^ 2 * ‖gradient f y'‖ ^ 2))) =
        A' * Γ ^ 2 / (2 * lam * B) * (lam ^ 2 * ‖gradient f y'‖ ^ 2) := by
      rw [div_pow, hsq]; field_simp
    rw [e]
    have hc : 0 ≤ A' * Γ ^ 2 / (2 * lam * B) := by positivity
    calc A' * Γ ^ 2 / (2 * lam * B) * (lam ^ 2 * ‖gradient f y'‖ ^ 2)
        ≤ A' * Γ ^ 2 / (2 * lam * B) * (2 * X2 + 2 * Y2) := mul_le_mul_of_nonneg_left hv hc
      _ = A' * Γ ^ 2 / (lam * B) * (X2 + Y2) := by field_simp
      _ ≤ A' / (6 * lam) * (X2 + Y2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hA'.le, hlam.le]
  have hpot : outerPot f xstar (A, y, z) = A * (f y - f xstar) + 1 / 2 * ‖z - xstar‖ ^ 2 := rfl
  rw [hpot]
  have hY2 : 0 ≤ Y2 := sq_nonneg _
  have hX2 : 0 ≤ X2 := by positivity
  have e1 : A' / (2 * lam) * Y2 = A' / (3 * lam) * Y2 + A' / (6 * lam) * Y2 := by
    field_simp; ring
  have e2 : 2 * A' / (3 * lam) * X2 = A' / (2 * lam) * X2 + A' / (6 * lam) * X2 := by
    field_simp; ring
  nlinarith

lemma Hyp.block_trunc (H : Hyp p f g Lbar Γ xstar) {Γh : ℝ} (hΓ : 1 ≤ Γh) (hΓΓ : Γ ≤ Γh)
    {W : ℕ} (hW : 800 * Γh ^ 2 ≤ (W : ℝ))
    {B : ℕ} (hB1 : 1 ≤ B) (hB : 6 * Γ ^ 2 ≤ B) {O : (ℕ → Ω) → ℝ × E × E} (hO : Measurable O)
    {n : ℕ} (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n → ξ i = ξ' i) → O ξ = O ξ') {A : ℝ}
    (hA : 0 ≤ A) (hOA : ∀ ξ, (O ξ).1 = A) (M : ℝ) :
    ∑ j ∈ Finset.range (W), ∫⁻ ξ, ENNReal.ofReal
        (wTrunc f (pLam Lbar Γh) M (mixPt (pLam Lbar Γh) A (O ξ).2.1 (O ξ).2.2) *
          outerPot f xstar (blockStep g (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) (pT0 Γh) (W) B
            j n (O ξ) ξ)) ∂P ≤
      (W : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar (O ξ)) ∂P := by
  have hL := H.Lbar_pos
  set lam := pLam Lbar Γh
  set eta := pEta Lbar Γh
  set a := pA Γh
  set T0 := pT0 Γh
  have hlam : 0 < lam := (tune_inner hL hΓ).lam_pos
  set aN := aNext lam A
  set A' := A + aN
  set c : ℝ := aN / B
  have haN := aNext_pos hlam hA
  have hA' : 0 < A' := by simp only [A']; linarith
  set X : (ℕ → Ω) → E := fun ξ => mixPt lam A (O ξ).2.1 (O ξ).2.2
  have hXm : Measurable X := by
    simp only [X, mixPt]
    exact ((hO.snd.fst).const_smul _).add ((hO.snd.snd).const_smul _)
  have hXdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n → ξ i = ξ' i) → X ξ = X ξ' := by
    intro ξ ξ' h; simp only [X]; rw [hdep ξ ξ' h]
  set w : (ℕ → Ω) → ℝ := fun ξ => wTrunc f lam M (X ξ)
  have hwm : Measurable w := (H.measurable_wTrunc hlam M).comp hXm
  have hw01 : ∀ ξ, 0 ≤ w ξ ∧ w ξ ≤ 1 := by
    intro ξ; simp only [w, wTrunc]; split_ifs <;> norm_num
  set yj : ℕ → (ℕ → Ω) → E := fun j ξ => (innerRun g lam eta a (X ξ) ξ n (T0 + j)).1
  have hym : ∀ j, Measurable (yj j) := fun j =>
    (measurable_innerRun H.meas lam eta a hXm n (T0 + j)).fst
  have hstep : ∀ ξ j, blockStep g lam eta a T0 W B j n (O ξ) ξ =
      (A', yj j ξ, (O ξ).2.2 - c • batchSum g (yj j ξ) ξ (n + T0 + W) B) := by
    intro ξ j
    simp only [blockStep, hOA, yj, X, c, aN, A']
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  have hcB : c * B = aN := by simp only [c]; field_simp
  have hfstar : ∀ x, 0 ≤ f x - f xstar := fun x => by
    have := H.min (mem_univ x); simp only [mem_ofPred_eq] at this; linarith
  set Ug : ℕ → (ℕ → Ω) → E := fun j ξ => (O ξ).2.2 - aN • gradient f (yj j ξ) - xstar
  have hUgm : ∀ j, Measurable (Ug j) := fun j =>
    ((hO.snd.snd).sub (((H.grad_continuous.measurable.comp (hym j))).const_smul _)).sub_const _
  set Xg : ℕ → (ℕ → Ω) → ℝ := fun j ξ => lam ^ 2 * ‖phiGrad f lam (X ξ) (yj j ξ)‖ ^ 2
  set Yg : ℕ → (ℕ → Ω) → ℝ := fun j ξ => ‖yj j ξ - X ξ‖ ^ 2
  set D2 : (ℕ → Ω) → ℝ := fun ξ => ‖X ξ - prox f lam (X ξ)‖ ^ 2
  set F4 : ℕ → (ℕ → Ω) → ℝ := fun j ξ => w ξ * (c ^ 2 * (Γ ^ 2 * ‖gradient f (yj j ξ)‖ ^ 2))
  have hXgm : ∀ j, Measurable (Xg j) := fun j =>
    (((H.phiGrad_continuous lam).measurable.comp (hXm.prodMk (hym j))).norm.pow_const 2).const_mul _
  have hYgm : ∀ j, Measurable (Yg j) := fun j => ((hym j).sub hXm).norm.pow_const 2
  have hD2m : Measurable D2 := (H.dist2_continuous hlam).measurable.comp hXm
  have hfm : Measurable f := H.f_continuous.measurable
  have hS1 : ∀ j, j < W → ∫⁻ ξ, ENNReal.ofReal (w ξ *
      outerPot f xstar (blockStep g lam eta a T0 W B j n (O ξ) ξ)) ∂P ≤
      ∫⁻ ξ, ENNReal.ofReal (w ξ * (A' * (f (yj j ξ) - f xstar))) ∂P +
        ENNReal.ofReal (1 / 2) * (∫⁻ ξ, ENNReal.ofReal (w ξ * ‖Ug j ξ‖ ^ 2) ∂P +
          (B : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (F4 j ξ) ∂P) := by
    intro j hj
    have hdepj : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n + T0 + W → ξ i = ξ' i) →
        w ξ = w ξ' ∧ Ug j ξ = Ug j ξ' ∧ yj j ξ = yj j ξ' := by
      intro ξ ξ' h
      have hX := hXdep ξ ξ' fun i hi => h i (by omega)
      have hO' := hdep ξ ξ' fun i hi => h i (by omega)
      have hy : yj j ξ = yj j ξ' := by
        simp only [yj]
        rw [innerRun_congr g lam eta a hXdep (T0 + j) ξ ξ' fun i hi => h i (by omega)]
      refine ⟨by simp only [w]; rw [hX], ?_, hy⟩
      simp only [Ug]; rw [hy, hO']
    have hbt := H.batch_tower w hwm (fun ξ => (hw01 ξ).1) (Ug j) (yj j) (hUgm j) (hym j)
      hdepj c B
    have hid : ∀ ξ, w ξ * outerPot f xstar (blockStep g lam eta a T0 W B j n (O ξ) ξ) =
        w ξ * (A' * (f (yj j ξ) - f xstar)) + 1 / 2 * (w ξ * ‖Ug j ξ - c • (batchSum g (yj j ξ)
          ξ (n + T0 + W) B - (B : ℝ) • gradient f (yj j ξ))‖ ^ 2) := by
      intro ξ
      rw [hstep ξ j]
      simp only [outerPot, Ug]
      have hv : (O ξ).2.2 - c • batchSum g (yj j ξ) ξ (n + T0 + W) B - xstar =
          (O ξ).2.2 - aN • gradient f (yj j ξ) - xstar - c • (batchSum g (yj j ξ) ξ
            (n + T0 + W) B - (B : ℝ) • gradient f (yj j ξ)) := by
        rw [smul_sub, smul_smul, hcB]; abel
      rw [hv]; ring
    have hm1 : Measurable fun ξ => ENNReal.ofReal (w ξ * (A' * (f (yj j ξ) - f xstar))) :=
      ENNReal.measurable_ofReal.comp (hwm.mul (((hfm.comp (hym j)).sub_const _).const_mul _))
    simp_rw [hid]
    calc ∫⁻ ξ, ENNReal.ofReal (w ξ * (A' * (f (yj j ξ) - f xstar)) + 1 / 2 * (w ξ *
          ‖Ug j ξ - c • (batchSum g (yj j ξ) ξ (n + T0 + W) B -
            (B : ℝ) • gradient f (yj j ξ))‖ ^ 2)) ∂P
        = ∫⁻ ξ, ENNReal.ofReal (w ξ * (A' * (f (yj j ξ) - f xstar))) ∂P +
          ENNReal.ofReal (1 / 2) * ∫⁻ ξ, ENNReal.ofReal (w ξ *
            ‖Ug j ξ - c • (batchSum g (yj j ξ) ξ (n + T0 + W) B -
              (B : ℝ) • gradient f (yj j ξ))‖ ^ 2) ∂P := by
          rw [← lintegral_const_mul]
          · rw [← lintegral_add_left hm1]
            refine lintegral_congr fun ξ => ?_
            rw [← ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_add (mul_nonneg (hw01 ξ).1 (mul_nonneg hA'.le (hfstar _)))
                (by have := (hw01 ξ).1; positivity)]
          · exact ENNReal.measurable_ofReal.comp (hwm.mul (((hUgm j).sub
              (((measurable_batchSum H.meas (hym j) _ _).sub ((H.grad_continuous.measurable.comp
                (hym j)).const_smul _)).const_smul _)).norm.pow_const 2))
      _ ≤ _ := by
          gcongr
  have hOeq : ∀ ξ, O ξ = (A, (O ξ).2.1, (O ξ).2.2) := fun ξ => Prod.ext (hOA ξ) rfl
  have hk1 : 0 ≤ A' / (3 * lam) := by positivity
  set k1 : ℝ≥0∞ := ENNReal.ofReal (A' / (3 * lam))
  have hS2 : ∀ j, ∫⁻ ξ, ENNReal.ofReal (w ξ * (A' * (f (yj j ξ) - f xstar))) ∂P +
        ENNReal.ofReal (1 / 2) * (∫⁻ ξ, ENNReal.ofReal (w ξ * ‖Ug j ξ‖ ^ 2) ∂P +
          (B : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (F4 j ξ) ∂P) +
        k1 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Yg j ξ) ∂P ≤
      ∫⁻ ξ, ENNReal.ofReal (w ξ * outerPot f xstar (O ξ)) ∂P +
        2 * k1 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P := by
    intro j
    have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => (hw01 ξ).1
    have m1 : Measurable fun ξ => w ξ * (A' * (f (yj j ξ) - f xstar)) :=
      hwm.mul (((hfm.comp (hym j)).sub_const _).const_mul _)
    have m2 : Measurable fun ξ => w ξ * ‖Ug j ξ‖ ^ 2 := hwm.mul ((hUgm j).norm.pow_const 2)
    have m3 : Measurable (F4 j) := hwm.mul ((((H.grad_continuous.measurable.comp
      (hym j)).norm.pow_const 2).const_mul _).const_mul _)
    have m4 : Measurable fun ξ => w ξ * Yg j ξ := hwm.mul (hYgm j)
    have m5 : Measurable fun ξ => w ξ * outerPot f xstar (O ξ) := by
      refine hwm.mul ?_
      unfold outerPot
      exact (hO.fst.mul ((hfm.comp hO.snd.fst).sub_const _)).add
        ((((hO.snd.snd).sub_const _).norm.pow_const 2).const_mul _)
    have m6 : Measurable fun ξ => w ξ * Xg j ξ := hwm.mul (hXgm j)
    have hB' : (B : ℝ≥0∞) = ENNReal.ofReal B := (ENNReal.ofReal_natCast B).symm
    have h2 : (2 : ℝ≥0∞) * k1 = ENNReal.ofReal (2 * A' / (3 * lam)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    have n1 : ∀ ξ, 0 ≤ w ξ * (A' * (f (yj j ξ) - f xstar)) := fun ξ =>
      mul_nonneg (hw0 ξ) (mul_nonneg hA'.le (hfstar _))
    have n2 : ∀ ξ, 0 ≤ w ξ * ‖Ug j ξ‖ ^ 2 := fun ξ => mul_nonneg (hw0 ξ) (sq_nonneg _)
    have n3 : ∀ ξ, 0 ≤ F4 j ξ := fun ξ => by simp only [F4]; have := hw0 ξ; positivity
    have n4 : ∀ ξ, 0 ≤ w ξ * Yg j ξ := fun ξ => mul_nonneg (hw0 ξ) (sq_nonneg _)
    have n5 : ∀ ξ, 0 ≤ w ξ * outerPot f xstar (O ξ) := fun ξ =>
      mul_nonneg (hw0 ξ) (H.outerPot_nonneg _ (by rw [hOA]; exact hA))
    have n6 : ∀ ξ, 0 ≤ w ξ * Xg j ξ := fun ξ => by simp only [Xg]; have := hw0 ξ; positivity
    have hBn : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have m23 : Measurable fun ξ => w ξ * ‖Ug j ξ‖ ^ 2 + (B : ℝ) * F4 j ξ := m2.add (m3.const_mul _)
    have m123 : Measurable fun ξ => w ξ * (A' * (f (yj j ξ) - f xstar)) +
        1 / 2 * (w ξ * ‖Ug j ξ‖ ^ 2 + (B : ℝ) * F4 j ξ) := m1.add (m23.const_mul _)
    rw [h2, hB', lint_smul m3 hBn, lint_add m2 n2 (fun ξ => mul_nonneg hBn (n3 ξ)),
      lint_smul m23 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      lint_add m1 n1 (fun ξ => mul_nonneg (by norm_num) (add_nonneg (n2 ξ)
        (mul_nonneg hBn (n3 ξ)))),
      lint_smul m4 hk1,
      lint_add m123
        (fun ξ => add_nonneg (n1 ξ) (mul_nonneg (by norm_num) (add_nonneg (n2 ξ)
          (mul_nonneg hBn (n3 ξ))))) (fun ξ => mul_nonneg hk1 (n4 ξ)),
      lint_smul m6 (by positivity : (0 : ℝ) ≤ 2 * A' / (3 * lam)),
      lint_add m5 n5 (fun ξ => mul_nonneg (by positivity) (n6 ξ))]
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
    have hp := H.block_path hlam hA hB1 hB (O ξ).2.1 (O ξ).2.2 (yj j ξ)
    rw [← hOeq ξ] at hp
    have := mul_le_mul_of_nonneg_left hp (hw0 ξ)
    simp only [F4, Ug, Yg, Xg, c, aN, A', X] at this ⊢
    nlinarith
  have hS3 := H.inner_relative hΓ hΓΓ hW hXm hXdep (wTrunc f lam M) (H.measurable_wTrunc hlam M)
    (fun x => by simp only [wTrunc]; split_ifs <;> norm_num) (n0 := n)
  set SX := ∑ j ∈ Finset.range W, ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P
  set SY := ∑ j ∈ Finset.range W, ∫⁻ ξ, ENNReal.ofReal (w ξ * Yg j ξ) ∂P
  set Dw := ∫⁻ ξ, ENNReal.ofReal (w ξ * D2 ξ) ∂P
  have hSX : SX ≤ ENNReal.ofReal ((W : ℝ) / 6) * Dw := hS3
  have hDw : Dw ≤ ENNReal.ofReal (max M 0) := by
    calc Dw ≤ ∫⁻ _ξ, ENNReal.ofReal (max M 0) ∂P := by
          refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
          simp only [w, D2, wTrunc]
          split_ifs with h
          · rw [one_mul]; exact h.trans (le_max_left _ _)
          · rw [zero_mul]; exact le_max_right _ _
      _ = ENNReal.ofReal (max M 0) := by simp
  have hDwt : Dw ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDw
  have hSXt : SX ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDwt) hSX
  have hpath : ∀ j ξ, D2 ξ ≤ 2 * Yg j ξ + 2 * Xg j ξ ∧ Yg j ξ ≤ 2 * Xg j ξ + 2 * D2 ξ := by
    intro j ξ
    have hd := H.dist_prox_le hlam (X ξ) (yj j ξ)
    have hd2 : ‖yj j ξ - prox f lam (X ξ)‖ ^ 2 ≤ Xg j ξ := by
      simp only [Xg]; rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hd 2
    constructor
    · have e : X ξ - prox f lam (X ξ) = -(yj j ξ - X ξ) + (yj j ξ - prox f lam (X ξ)) := by abel
      have := NormalizedStorm.sq_norm_add_le (-(yj j ξ - X ξ)) (yj j ξ - prox f lam (X ξ))
      rw [norm_neg, ← e] at this
      simp only [D2, Yg]; linarith
    · have e : yj j ξ - X ξ = (yj j ξ - prox f lam (X ξ)) + -(X ξ - prox f lam (X ξ)) := by abel
      have := NormalizedStorm.sq_norm_add_le (yj j ξ - prox f lam (X ξ)) (-(X ξ - prox f lam (X ξ)))
      rw [norm_neg, ← e] at this
      simp only [D2, Yg]; linarith
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => (hw01 ξ).1
  have hS4 : (W : ℝ≥0∞) * Dw ≤ 2 * SY + 2 * SX := by
    have hj : ∀ j, Dw ≤ 2 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Yg j ξ) ∂P +
        2 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P := by
      intro j
      have my : Measurable fun ξ => w ξ * Yg j ξ := hwm.mul (hYgm j)
      have mx : Measurable fun ξ => w ξ * Xg j ξ := hwm.mul (hXgm j)
      have my2 : Measurable fun ξ => 2 * (w ξ * Yg j ξ) := my.const_mul _
      have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      rw [h2, lint_smul my (by norm_num), lint_smul mx (by norm_num),
        lint_add my2 (fun ξ => by have := hw0 ξ; simp only [Yg]; positivity)
          (fun ξ => by have := hw0 ξ; simp only [Xg]; positivity)]
      refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left (hpath j ξ).1 (hw0 ξ)
      linarith
    calc (W : ℝ≥0∞) * Dw = ∑ _j ∈ Finset.range W, Dw := by simp
      _ ≤ ∑ j ∈ Finset.range W, (2 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Yg j ξ) ∂P +
          2 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P) := Finset.sum_le_sum fun j _ => hj j
      _ = 2 * SY + 2 * SX := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hSYb : SY ≤ 2 * SX + 2 * (W * Dw) := by
    have hj : ∀ j, ∫⁻ ξ, ENNReal.ofReal (w ξ * Yg j ξ) ∂P ≤
        2 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P + 2 * Dw := by
      intro j
      have mx : Measurable fun ξ => w ξ * Xg j ξ := hwm.mul (hXgm j)
      have md : Measurable fun ξ => w ξ * D2 ξ := hwm.mul hD2m
      have mx2 : Measurable fun ξ => 2 * (w ξ * Xg j ξ) := mx.const_mul _
      have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      rw [h2, lint_smul mx (by norm_num), lint_smul md (by norm_num),
        lint_add mx2 (fun ξ => by have := hw0 ξ; simp only [Xg]; positivity)
          (fun ξ => by have := hw0 ξ; simp only [D2]; positivity)]
      refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left (hpath j ξ).2 (hw0 ξ)
      linarith
    calc SY ≤ ∑ j ∈ Finset.range W, (2 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P + 2 * Dw) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = 2 * SX + 2 * (W * Dw) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  have hSYt : SY ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
    (by simp) hSXt, ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hDwt)⟩) hSYb
  have hkey : 2 * SX ≤ SY := by
    have h6 : 6 * SX ≤ 2 * SY + 2 * SX := by
      calc 6 * SX ≤ 6 * (ENNReal.ofReal ((W : ℝ) / 6) * Dw) := by gcongr
        _ = (W : ℝ≥0∞) * Dw := by
            rw [← mul_assoc, show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp,
              ← ENNReal.ofReal_mul (by norm_num), show (6 : ℝ) * ((W : ℝ) / 6) = W by ring,
              ENNReal.ofReal_natCast]
        _ ≤ 2 * SY + 2 * SX := hS4
    have h4 : 4 * SX + 2 * SX ≤ 2 * SY + 2 * SX := by
      calc 4 * SX + 2 * SX = 6 * SX := by ring
        _ ≤ _ := h6
    have h4' := (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by simp) hSXt)).mp h4
    have : 2 * (2 * SX) ≤ 2 * SY := by
      calc 2 * (2 * SX) = 4 * SX := by rw [← mul_assoc]; norm_num
        _ ≤ 2 * SY := h4'
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).mp this
  set Q := ∫⁻ ξ, ENNReal.ofReal (w ξ * outerPot f xstar (O ξ)) ∂P
  have hsum : ∑ j ∈ Finset.range W, ∫⁻ ξ, ENNReal.ofReal (w ξ *
      outerPot f xstar (blockStep g lam eta a T0 W B j n (O ξ) ξ)) ∂P + k1 * SY ≤
      (W : ℝ≥0∞) * Q + 2 * k1 * SX := by
    calc ∑ j ∈ Finset.range W, ∫⁻ ξ, ENNReal.ofReal (w ξ *
          outerPot f xstar (blockStep g lam eta a T0 W B j n (O ξ) ξ)) ∂P + k1 * SY
        ≤ ∑ j ∈ Finset.range W, (∫⁻ ξ, ENNReal.ofReal (w ξ * (A' * (f (yj j ξ) - f xstar))) ∂P +
          ENNReal.ofReal (1 / 2) * (∫⁻ ξ, ENNReal.ofReal (w ξ * ‖Ug j ξ‖ ^ 2) ∂P +
            (B : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (F4 j ξ) ∂P) +
          k1 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Yg j ξ) ∂P) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          gcongr with j hj
          exact hS1 j (Finset.mem_range.mp hj)
      _ ≤ ∑ j ∈ Finset.range W, (Q + 2 * k1 * ∫⁻ ξ, ENNReal.ofReal (w ξ * Xg j ξ) ∂P) :=
          Finset.sum_le_sum fun j _ => hS2 j
      _ = (W : ℝ≥0∞) * Q + 2 * k1 * SX := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
  have hfin : ∑ j ∈ Finset.range W, ∫⁻ ξ, ENNReal.ofReal (w ξ *
      outerPot f xstar (blockStep g lam eta a T0 W B j n (O ξ) ξ)) ∂P ≤ (W : ℝ≥0∞) * Q := by
    have h1 : (W : ℝ≥0∞) * Q + 2 * k1 * SX ≤ (W : ℝ≥0∞) * Q + k1 * SY := by
      have : 2 * k1 * SX ≤ k1 * SY := by
        calc 2 * k1 * SX = k1 * (2 * SX) := by ring
          _ ≤ k1 * SY := by gcongr
      exact add_le_add le_rfl this
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSYt)).mp
      (hsum.trans h1)
  refine hfin.trans ?_
  gcongr
  refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
  exact (by
    have h1 := (hw01 ξ).2
    have h2 := H.outerPot_nonneg (O ξ) (by rw [hOA]; exact hA)
    nlinarith)

lemma Hyp.block_le (H : Hyp p f g Lbar Γ xstar) {Γh : ℝ} (hΓ : 1 ≤ Γh) (hΓΓ : Γ ≤ Γh)
    {W : ℕ} (hW : 800 * Γh ^ 2 ≤ (W : ℝ))
    {B : ℕ} (hB1 : 1 ≤ B) (hB : 6 * Γ ^ 2 ≤ B) {O : (ℕ → Ω) → ℝ × E × E} (hO : Measurable O)
    {n : ℕ} (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n → ξ i = ξ' i) → O ξ = O ξ') {A : ℝ}
    (hA : 0 ≤ A) (hOA : ∀ ξ, (O ξ).1 = A) :
    ∑ j ∈ Finset.range (W), ∫⁻ ξ, ENNReal.ofReal
        (outerPot f xstar (blockStep g (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) (pT0 Γh) (W) B
            j n (O ξ) ξ)) ∂P ≤
      (W : ℝ≥0∞) * ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar (O ξ)) ∂P := by
  have hL := H.Lbar_pos
  have hlam : 0 < pLam Lbar Γh := (tune_inner hL hΓ).lam_pos
  set X : (ℕ → Ω) → E := fun ξ => mixPt (pLam Lbar Γh) A (O ξ).2.1 (O ξ).2.2
  have hXm : Measurable X := by
    simp only [X, mixPt]
    exact ((hO.snd.fst).const_smul _).add ((hO.snd.snd).const_smul _)
  set F : ℕ → (ℕ → Ω) → ℝ := fun j ξ => outerPot f xstar (blockStep g (pLam Lbar Γh)
    (pEta Lbar Γh) (pA Γh) (pT0 Γh) (W) B j n (O ξ) ξ)
  have hF0 : ∀ j ξ, 0 ≤ F j ξ := fun j ξ => H.outerPot_nonneg _ (by
    simp only [blockStep, hOA]; have := aNext_pos hlam hA; linarith)
  have hFm : ∀ j, Measurable (F j) := by
    intro j
    have hy := (measurable_innerRun H.meas (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) hXm n
      (pT0 Γh + j)).fst
    have hFeq : F j = fun ξ => outerPot f xstar (A + aNext (pLam Lbar Γh) A,
        (innerRun g (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) (X ξ) ξ n (pT0 Γh + j)).1,
        (O ξ).2.2 - (aNext (pLam Lbar Γh) A / B) • batchSum g
          (innerRun g (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) (X ξ) ξ n (pT0 Γh + j)).1 ξ
            (n + pT0 Γh + W) B) := by
      funext ξ; simp only [F, blockStep, hOA, X]
    rw [hFeq]
    unfold outerPot
    exact (((H.f_continuous.measurable.comp hy).sub_const _).const_mul _).add
      ((((hO.snd.snd.sub ((measurable_batchSum H.meas hy _ _).const_smul _)).sub_const _).norm.pow_const
        2).const_mul _)
  have hmono : ∀ j, Monotone fun M : ℕ => ∫⁻ ξ, ENNReal.ofReal
      (wTrunc f (pLam Lbar Γh) M (X ξ) * F j ξ) ∂P := by
    intro j M M' hMM
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
    apply mul_le_mul_of_nonneg_right _ (hF0 j ξ)
    simp only [wTrunc]
    split_ifs with h1 h2 <;> try norm_num
    exact absurd (h1.trans (by exact_mod_cast hMM)) h2
  have hsup : ∀ j, ∫⁻ ξ, ENNReal.ofReal (F j ξ) ∂P =
      ⨆ M : ℕ, ∫⁻ ξ, ENNReal.ofReal (wTrunc f (pLam Lbar Γh) M (X ξ) * F j ξ) ∂P := by
    intro j
    rw [← lintegral_iSup]
    · refine lintegral_congr fun ξ => ?_
      refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal ?_)
      · obtain ⟨M, hM⟩ := exists_nat_ge (‖X ξ - prox f (pLam Lbar Γh) (X ξ)‖ ^ 2)
        refine le_iSup_of_le M (le_of_eq ?_)
        simp only [wTrunc, hM, ite_true, one_mul]
      · have : wTrunc f (pLam Lbar Γh) M (X ξ) ≤ 1 := by
          simp only [wTrunc]; split_ifs <;> norm_num
        nlinarith [hF0 j ξ]
    · intro M
      exact (((H.measurable_wTrunc hlam M).comp hXm).mul (hFm j)).ennreal_ofReal
    · intro M M' hMM ξ
      refine ENNReal.ofReal_le_ofReal ?_
      apply mul_le_mul_of_nonneg_right _ (hF0 j ξ)
      simp only [wTrunc]
      split_ifs with h1 h2 <;> try norm_num
      exact absurd (h1.trans (by exact_mod_cast hMM)) h2
  simp only [F] at hsup
  simp_rw [hsup]
  rw [ENNReal.finsetSum_iSup_of_monotone hmono]
  exact iSup_le fun M => H.block_trunc hΓ hΓΓ hW hB1 hB hO hdep hA hOA M

end OracleTemplate.ProximalStorm
