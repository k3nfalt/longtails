import LongTails.Proofs.ScalarHeavyTailEstimator
import LongTails.Proofs.ScalarSearchExecution

open MeasureTheory Classical

set_option backward.isDefEq.respectTransparency false

namespace OracleTemplate.ScalarHeavyTailEstimator

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def finiteBlock (σ p u : ℝ) (samples : Fin (blockSize σ p u) → ℝ) : ℝ :=
  block σ p u (fun j => if h : j < blockSize σ p u then samples ⟨j, h⟩ else 0)

lemma measurable_finiteBlock (σ p u : ℝ) : Measurable (finiteBlock σ p u) := by
  have hm : Measurable (fun samples : Fin (blockSize σ p u) → ℝ => fun j : ℕ =>
      if h : j < blockSize σ p u then samples ⟨j, h⟩ else 0) := by
    apply measurable_pi_iff.mpr
    intro j
    split_ifs with hj
    · exact measurable_pi_apply (⟨j, hj⟩ : Fin (blockSize σ p u))
    · exact measurable_const
  exact (measurable_block measurable_id σ p u).comp hm

lemma finiteBlock_prefix (σ p u : ℝ) (samples : ℕ → ℝ) :
    finiteBlock σ p u (fun i => samples i) = block σ p u samples := by
  apply ScalarSearchExecution.block_reads
  intro j hj
  simp only [hj, dite_true]

lemma finiteBlock_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) :
    (Measure.pi fun _ : Fin (blockSize σ p u) => P).real
      {ξ | u < |finiteBlock σ p u (fun i => X (ξ i)) - μ|} ≤ 1 / 64 := by
  have hM : Measurable (fun ξ : Fin (blockSize σ p u) → Ω =>
      finiteBlock σ p u (fun i => X (ξ i))) :=
    (measurable_finiteBlock σ p u).comp (measurable_pi_iff.mpr (fun i => hX.comp (measurable_pi_apply i)))
  have hA := measurableSet_lt (measurable_const (a := u)) (continuous_abs.measurable.comp (hM.sub_const μ))
  have hpre := (StochasticGeneralized.prefix_preserving P (blockSize σ p u)).measure_preimage hA.nullMeasurableSet
  have h := block_tail hX hi hm hσ hu hp hp2 hpi hmoment
  unfold Measure.real at h ⊢
  simp only [Function.comp_def] at hpre
  rw [← hpre]
  have he (ξ : ℕ → Ω) : finiteBlock σ p u (fun i => X (ξ i)) =
      block σ p u (fun j => X (ξ j)) := finiteBlock_prefix σ p u (fun j => X (ξ j))
  simpa only [Set.preimage_ofPred_eq, he] using h

lemma estimate_product_tail_of_block {X : Ω → ℝ} (hX : Measurable X)
    (μ σ p u : ℝ) {c : ℝ} (hc : 1 ≤ c)
    (htail : (Measure.pi fun _ : Fin (blockSize σ p u) => P).real
      {ξ | u < |finiteBlock σ p u (fun i => X (ξ i)) - μ|} ≤ 1 / c ^ 2) (k : ℕ) :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin (blockSize σ p u) => P)
      {ξ | 3 * u < |RobustGradient.pilotCenter (6 * u)
        (fun i => finiteBlock σ p u (fun j => X (ξ i j))) - μ|} ≤
      ENNReal.ofReal ((2 / c) ^ k) := by
  have hmV : Measurable (fun ξ : Fin (blockSize σ p u) → Ω =>
      finiteBlock σ p u (fun i => X (ξ i))) :=
    (measurable_finiteBlock σ p u).comp (measurable_pi_iff.mpr (fun i => hX.comp (measurable_pi_apply i)))
  exact pilot_tail hmV μ u hc htail k

lemma measurable_estimate {X : Ω → ℝ} (hX : Measurable X) (σ p u : ℝ) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => estimate σ p u k (fun j => X (ξ j))) := by
  have hblocks : Measurable (fun ξ : ℕ → Ω => fun i : Fin k =>
      block σ p u (fun j => X (ξ (i.val * blockSize σ p u + j)))) := by
    apply measurable_pi_iff.mpr
    intro i
    have hstream : Measurable (fun ξ : ℕ → Ω => fun j : ℕ => ξ (i.val * blockSize σ p u + j)) :=
      measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
    exact (measurable_block hX σ p u).comp hstream
  exact (RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk hblocks)

lemma estimate_tail_of_block {X : Ω → ℝ} (hX : Measurable X)
    (μ σ p u : ℝ) {c : ℝ} (hc : 1 ≤ c)
    (hblock : (Measure.pi fun _ : Fin (blockSize σ p u) => P).real
      {ξ | u < |finiteBlock σ p u (fun i => X (ξ i)) - μ|} ≤ 1 / c ^ 2) (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 3 * u < |estimate σ p u k (fun j => X (ξ j)) - μ|} ≤
      ENNReal.ofReal ((2 / c) ^ k) := by
  let b := blockSize σ p u
  let V : (Fin k → Fin b → Ω) → ℝ := fun ξ => RobustGradient.pilotCenter (6 * u)
    (fun i => finiteBlock σ p u (fun j => X (ξ i j)))
  have hV : Measurable V := by
    have hblocks : Measurable (fun ξ : Fin k → Fin b → Ω => fun i : Fin k =>
        finiteBlock σ p u (fun j => X (ξ i j))) := by
      apply measurable_pi_iff.mpr
      intro i
      have hstream : Measurable (fun ξ : Fin k → Fin b → Ω => fun j : Fin b => X (ξ i j)) :=
        measurable_pi_iff.mpr (fun j => hX.comp ((measurable_pi_apply j).comp (measurable_pi_apply i)))
      exact (measurable_finiteBlock σ p u).comp hstream
    exact (RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk hblocks)

  have hA := measurableSet_lt (measurable_const (a := 3 * u)) (continuous_abs.measurable.comp (hV.sub_const μ))
  have hid := StochasticGeneralized.infinitePi_iid P
  have hb := FiniteVariance.infinite_block_law P (Measure.infinitePi fun _ : ℕ => P)
    hid.independent hid.marginal b
  have hpre := (StochasticGeneralized.prefix_preserving (Measure.pi fun _ : Fin b => P) k).comp hb
  have he (ξ : ℕ → Ω) : V (fun i j => ξ (i.val * b + j.val)) =
      estimate σ p u k (fun j => X (ξ j)) := by
    unfold V estimate
    congr 1
    funext i
    exact finiteBlock_prefix σ p u (fun j => X (ξ (i.val * b + j)))
  have hmeasure := hpre.measure_preimage hA.nullMeasurableSet
  have htail := estimate_product_tail_of_block hX μ σ p u hc hblock k
  change (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin b => P) {ξ | 3 * u < |V ξ - μ|} ≤ _ at htail
  simp only [Function.comp_def] at hmeasure
  rw [← hmeasure] at htail
  simpa only [Set.preimage_ofPred_eq, Function.comp_def, he] using htail

lemma estimate_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 3 * u < |estimate σ p u k (fun j => X (ξ j)) - μ|} ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
  have ht := finiteBlock_tail hX hi hm hσ hu hp hp2 hpi hmoment
  have h := estimate_tail_of_block hX μ σ p u (c := 8) (by norm_num)
    (by norm_num; exact ht) k
  norm_num at h ⊢
  exact h

lemma measurable_estimate_joint {Z : Type*} [MeasurableSpace Z]
    {g : Z → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (σ p u : ℝ) (k : ℕ) :
    Measurable (fun w : Z × (ℕ → Ω) => estimate σ p u k (fun j => g w.1 (w.2 j))) := by
  have hS : Measurable (fun w : Z × (ℕ → Ω) => fun j : ℕ => g w.1 (w.2 j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  exact (measurable_estimate measurable_id σ p u k).comp hS

lemma adaptive_estimate_tail {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] {g : Z → Ω → ℝ} {μ : Z → ℝ}
    (hg : Measurable (Function.uncurry g)) (hμ : Measurable μ)
    {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ z, Integrable (g z) P) (hm : ∀ z, (∫ ω, g z ω ∂P) = μ z)
    (hpi : ∀ z, Integrable (fun ω => |g z ω - μ z| ^ p) P)
    (hmoment : ∀ z, (∫ ω, |g z ω - μ z| ^ p ∂P) ≤ σ ^ p) (k : ℕ) :
    (Q.prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | 3 * u < |estimate σ p u k (fun j => g w.1 (w.2 j)) - μ w.1|} ≤
      (1 / 4 : ℝ) ^ k := by
  have hB := measurableSet_lt (measurable_const (a := 3 * u)) (continuous_abs.measurable.comp
    ((measurable_estimate_joint hg σ p u k).sub (hμ.comp measurable_fst)))
  have hpoint (z : Z) (_ : z ∉ (∅ : Set Z)) :
      (Measure.infinitePi fun _ : ℕ => P).real
        {ξ | 3 * u < |estimate σ p u k (fun j => g z (ξ j)) - μ z|} ≤ (1 / 4 : ℝ) ^ k := by
    have h := estimate_tail (hg.comp measurable_prodMk_left) (hi z) (hm z)
      hσ hu hp hp2 (hpi z) (hmoment z) k
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [Function.comp_def, Function.uncurry_apply_pair, Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 4 : ℝ) ^ k)] using ht
  have h := conditional_failure (P := Q) MeasurableSet.empty hB
    (by positivity : 0 ≤ (1 / 4 : ℝ) ^ k) (by simp : Q.real ∅ ≤ (0 : ℝ)) hpoint
  simpa only [Function.comp_def, Pi.sub_apply, zero_add] using h

lemma block_tail_raw {X : Ω → ℝ} (hX : Measurable X) {μ σ p u : ℝ}
    (hu : 0 < u) (hp : 0 ≤ p) (hraw : 128 * σ ≤ u)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | u < |block σ p u (fun j => X (ξ j)) - μ|} ≤ σ ^ p / u ^ p := by
  simp only [block, ite_eq_left hraw]
  let A := {ω | u < |X ω - μ|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hX.sub_const μ))
  have hmarg : MeasurePreserving (fun ξ : ℕ → Ω => ξ 0)
      (Measure.infinitePi fun _ : ℕ => P) P :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  change (Measure.infinitePi fun _ : ℕ => P).real ((fun ξ => ξ 0) ⁻¹' A) ≤ _
  unfold Measure.real
  rw [hmarg.measure_preimage hA.nullMeasurableSet]
  exact moment_tail hu hp hpi hmoment

lemma finiteBlock_failure_eq {X : Ω → ℝ} (hX : Measurable X) (μ σ p u : ℝ) :
    (Measure.pi fun _ : Fin (blockSize σ p u) => P).real
      {ξ | u < |finiteBlock σ p u (fun i => X (ξ i)) - μ|} =
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | u < |block σ p u (fun j => X (ξ j)) - μ|} := by
  have hM : Measurable (fun ξ : Fin (blockSize σ p u) → Ω =>
      finiteBlock σ p u (fun i => X (ξ i))) :=
    (measurable_finiteBlock σ p u).comp (measurable_pi_iff.mpr (fun i => hX.comp (measurable_pi_apply i)))
  have hA := measurableSet_lt (measurable_const (a := u)) (continuous_abs.measurable.comp (hM.sub_const μ))
  have hpre := (StochasticGeneralized.prefix_preserving P (blockSize σ p u)).measure_preimage hA.nullMeasurableSet
  unfold Measure.real
  simp only [Function.comp_def] at hpre
  rw [← hpre]
  congr 1
  congr 1
  ext ξ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [finiteBlock_prefix σ p u (fun j => X (ξ j))]

lemma finiteBlock_tail_raw_le {X : Ω → ℝ} (hX : Measurable X) {μ σ p u r : ℝ}
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 ≤ p) (hraw : 128 * σ ≤ u)
    (hr : σ / u ≤ r) (hr1 : r ≤ 1)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) :
    (Measure.pi fun _ : Fin (blockSize σ p u) => P).real
      {ξ | u < |finiteBlock σ p u (fun i => X (ξ i)) - μ|} ≤ r := by
  rw [finiteBlock_failure_eq hX]
  have ht := block_tail_raw hX hu (by linarith : 0 ≤ p) hraw hpi hmoment
  rw [← Real.div_rpow hσ hu.le] at ht
  exact ht.trans ((Real.rpow_le_self_of_le_one (div_nonneg hσ hu.le) (hr.trans hr1) hp).trans hr)

lemma finiteBlock_scale_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) (j : ℕ) :
    (Measure.pi fun _ : Fin (blockSize σ p (u * (2 : ℝ) ^ j)) => P).real
      {ξ | u * (2 : ℝ) ^ j < |finiteBlock σ p (u * (2 : ℝ) ^ j) (fun i => X (ξ i)) - μ|} ≤
      1 / ((2 : ℝ) ^ (3 + (j - noiseLevel σ u) / 2)) ^ 2 := by
  by_cases hj : noiseLevel σ u ≤ j
  · have hratio := coarse_scale_ratio hu j hj
    have hr1 : 1 / (128 * (2 : ℝ) ^ (j - noiseLevel σ u)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hpow : (1 : ℝ) ≤ 2 ^ (j - noiseLevel σ u) := one_le_pow₀ (by norm_num)
      linarith
    exact (finiteBlock_tail_raw_le hX hσ (by positivity) hp.le (coarse_scale_raw hu j hj)
      hratio hr1 hpi hmoment).trans (dyadic_block_confidence _)
  · have he : j - noiseLevel σ u = 0 := by omega
    simp only [he]
    norm_num
    exact finiteBlock_tail hX hi hm hσ (by positivity) hp hp2 hpi hmoment

lemma estimate_scale_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) (j : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 3 * (u * (2 : ℝ) ^ j) <
        |estimate σ p (u * (2 : ℝ) ^ j) (repetitions σ u j) (fun i => X (ξ i)) - μ|} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (16 * (j + 1))) := by
  let h := j - noiseLevel σ u
  have hb := finiteBlock_scale_tail hX hi hm hσ hu hp hp2 hpi hmoment j
  have ht := estimate_tail_of_block hX μ σ p (u * (2 : ℝ) ^ j)
    (c := (2 : ℝ) ^ (3 + h / 2)) (one_le_pow₀ (by norm_num)) hb (repetitions σ u j)
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  have he : 2 / (2 : ℝ) ^ (3 + h / 2) = (1 / 2 : ℝ) ^ (2 + h / 2) := by
    rw [one_div_pow]
    simp only [pow_add]
    norm_num
    ring
  rw [he, ← pow_mul]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  exact amplification_exponent j h

lemma adaptive_scale_tail {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] {g : Z → Ω → ℝ} {μ : Z → ℝ}
    (hg : Measurable (Function.uncurry g)) (hμ : Measurable μ)
    {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ z, Integrable (g z) P) (hm : ∀ z, (∫ ω, g z ω ∂P) = μ z)
    (hpi : ∀ z, Integrable (fun ω => |g z ω - μ z| ^ p) P)
    (hmoment : ∀ z, (∫ ω, |g z ω - μ z| ^ p ∂P) ≤ σ ^ p) (j : ℕ) :
    (Q.prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | 3 * (u * (2 : ℝ) ^ j) <
        |estimate σ p (u * (2 : ℝ) ^ j) (repetitions σ u j) (fun i => g w.1 (w.2 i)) - μ w.1|} ≤
      (1 / 2 : ℝ) ^ (16 * (j + 1)) := by
  have hB := measurableSet_lt (measurable_const (a := 3 * (u * (2 : ℝ) ^ j)))
    (continuous_abs.measurable.comp
      ((measurable_estimate_joint hg σ p (u * (2 : ℝ) ^ j) (repetitions σ u j)).sub
        (hμ.comp measurable_fst)))
  have hpoint (z : Z) (_ : z ∉ (∅ : Set Z)) :
      (Measure.infinitePi fun _ : ℕ => P).real
        {ξ | 3 * (u * (2 : ℝ) ^ j) <
          |estimate σ p (u * (2 : ℝ) ^ j) (repetitions σ u j) (fun i => g z (ξ i)) - μ z|} ≤
        (1 / 2 : ℝ) ^ (16 * (j + 1)) := by
    have h := estimate_scale_tail (hg.comp measurable_prodMk_left) (hi z) (hm z)
      hσ hu hp hp2 (hpi z) (hmoment z) j
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [Function.comp_def, Function.uncurry_apply_pair, Measure.real,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (16 * (j + 1)))] using ht
  have h := conditional_failure (P := Q) MeasurableSet.empty hB
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (16 * (j + 1))) (by simp : Q.real ∅ ≤ (0 : ℝ)) hpoint
  simpa only [Function.comp_def, Pi.sub_apply, zero_add] using h

lemma seed_prefix_tail_preserving {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (n : ℕ) :
    MeasurePreserving
      (fun w : Z × (ℕ → Ω) => ((w.1, fun i : Fin n => w.2 i), fun j => w.2 (n + j)))
      (Q.prod (Measure.infinitePi fun _ : ℕ => P))
      ((Q.prod (Measure.pi fun _ : Fin n => P)).prod (Measure.infinitePi fun _ : ℕ => P)) := by
  exact ((measurePreserving_prodAssoc Q (Measure.pi fun _ : Fin n => P)
    (Measure.infinitePi fun _ : ℕ => P)).symm MeasurableEquiv.prodAssoc).comp
    ((MeasurePreserving.id Q).prod (StochasticGeneralized.splitStream_preserving P n))

lemma prefix_adaptive_estimate_tail {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (n : ℕ)
    {g : ℝ → Ω → ℝ} {μ : ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (hμ : Measurable μ)
    (query : Z × (Fin n → Ω) → ℝ) (hq : Measurable query)
    {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (g x) P) (hm : ∀ x, (∫ ω, g x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |g x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |g x ω - μ x| ^ p ∂P) ≤ σ ^ p) (k : ℕ) :
    (Q.prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | 3 * u < |estimate σ p u k
        (fun j => g (query (w.1, fun i => w.2 i)) (w.2 (n + j))) -
        μ (query (w.1, fun i => w.2 i))|} ≤ (1 / 4 : ℝ) ^ k := by
  let G : (Z × (Fin n → Ω)) → Ω → ℝ := fun z ω => g (query z) ω
  let mean : (Z × (Fin n → Ω)) → ℝ := fun z => μ (query z)
  have hG : Measurable (Function.uncurry G) := hg.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hmean : Measurable mean := hμ.comp hq
  have h := adaptive_estimate_tail (Q.prod (Measure.pi fun _ : Fin n => P)) hG hmean
    hσ hu hp hp2 (fun z => hi (query z)) (fun z => hm (query z))
    (fun z => hpi (query z)) (fun z => hmoment (query z)) k
  have hA := measurableSet_lt (measurable_const (a := 3 * u))
    (continuous_abs.measurable.comp ((measurable_estimate_joint hG σ p u k).sub
      (hmean.comp measurable_fst)))
  have hpre := (seed_prefix_tail_preserving (P := P) Q n).measure_preimage hA.nullMeasurableSet
  unfold Measure.real at h ⊢
  simp only [Function.comp_def, Pi.sub_apply] at hpre
  rw [← hpre] at h
  exact h

lemma past_estimate_tail (n : ℕ) {g : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hμ : Measurable μ)
    (query : (Fin n → Ω) → ℝ) (hq : Measurable query)
    {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (g x) P) (hm : ∀ x, (∫ ω, g x ω ∂P) = μ x)
    (hpi : ∀ x, Integrable (fun ω => |g x ω - μ x| ^ p) P)
    (hmoment : ∀ x, (∫ ω, |g x ω - μ x| ^ p ∂P) ≤ σ ^ p) (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | 3 * u < |estimate σ p u k
        (fun j => g (query (fun i => ξ i)) (ξ (n + j))) - μ (query (fun i => ξ i))|} ≤
      (1 / 4 : ℝ) ^ k := by
  let G : (Fin n → Ω) → Ω → ℝ := fun z ω => g (query z) ω
  let mean : (Fin n → Ω) → ℝ := fun z => μ (query z)
  have hG : Measurable (Function.uncurry G) := hg.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hmean : Measurable mean := hμ.comp hq
  have h := adaptive_estimate_tail (Measure.pi fun _ : Fin n => P) hG hmean
    hσ hu hp hp2 (fun z => hi (query z)) (fun z => hm (query z))
    (fun z => hpi (query z)) (fun z => hmoment (query z)) k
  have hA := measurableSet_lt (measurable_const (a := 3 * u))
    (continuous_abs.measurable.comp ((measurable_estimate_joint hG σ p u k).sub
      (hmean.comp measurable_fst)))
  have hpre := (StochasticGeneralized.splitStream_preserving P n).measure_preimage hA.nullMeasurableSet
  unfold Measure.real at h ⊢
  simp only [Function.comp_def, Pi.sub_apply] at hpre
  rw [← hpre] at h
  exact h

lemma shift_preserving (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun j => ξ (n + j))
      (Measure.infinitePi fun _ : ℕ => P) (Measure.infinitePi fun _ : ℕ => P) :=
  (measurePreserving_snd (μ := Measure.pi fun _ : Fin n => P)
    (ν := Measure.infinitePi fun _ : ℕ => P)).comp (StochasticGeneralized.splitStream_preserving P n)

lemma paired_blocks_preserving {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (b n offset call : ℕ) :
    MeasurePreserving
      (fun w : (ℕ → Z) × (ℕ → Ω) => fun i : Fin n =>
        (w.1 (offset + i.val), fun j : Fin b => w.2 (call + i.val * b + j.val)))
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => P))
      (Measure.pi fun _ : Fin n => Q.prod (Measure.pi fun _ : Fin b => P)) := by
  have hid := StochasticGeneralized.infinitePi_iid P
  have hb := FiniteVariance.infinite_block_law P (Measure.infinitePi fun _ : ℕ => P)
    hid.independent hid.marginal b
  have hraw := ((StochasticGeneralized.prefix_preserving (Measure.pi fun _ : Fin b => P) n).comp hb).comp
    (shift_preserving (P := P) call)
  have htime := (StochasticGeneralized.prefix_preserving Q n).comp (shift_preserving (P := Q) offset)
  have hc := (measurePreserving_arrowProdEquivProdArrow Z (Fin b → Ω) (Fin n)
    (fun _ => Q) (fun _ => Measure.pi fun _ : Fin b => P)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow Z (Fin b → Ω) (Fin n))
  convert hc.comp (htime.prod hraw) using 1
  funext w i
  change (w.1 (offset + i.val), fun j : Fin b => w.2 (call + i.val * b + j.val)) =
    (w.1 (offset + i.val), fun j : Fin b => w.2 (call + (i.val * b + j.val)))
  simp only [Nat.add_assoc]

lemma four_product_swap_preserving {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun w : (A × B) × (C × D) => ((w.1.1, w.2.1), (w.1.2, w.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (MeasurePreserving.id a).prod
    ((measurePreserving_prodAssoc b c d).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h4 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h5 := (measurePreserving_prodAssoc a c (b.prod d)).symm MeasurableEquiv.prodAssoc
  convert h5.comp (h4.comp (h3.comp (h2.comp h1))) using 1
  funext w
  rfl

lemma past_future_preserving {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (Q : Measure U) (R : Measure T) [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (n : ℕ) :
    MeasurePreserving
      (fun w : (U × T) × (ℕ → Ω) => ((w.1.1, fun i : Fin n => w.2 i), (w.1.2, fun j => w.2 (n + j))))
      ((Q.prod R).prod (Measure.infinitePi fun _ : ℕ => P))
      ((Q.prod (Measure.pi fun _ : Fin n => P)).prod (R.prod (Measure.infinitePi fun _ : ℕ => P))) := by
  exact (four_product_swap_preserving Q R (Measure.pi fun _ : Fin n => P)
    (Measure.infinitePi fun _ : ℕ => P)).comp
      ((MeasurePreserving.id (Q.prod R)).prod (StochasticGeneralized.splitStream_preserving P n))

end OracleTemplate.ScalarHeavyTailEstimator
