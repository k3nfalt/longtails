import LongTails.Proofs.ClippedExtragradientIteration
import LongTails.Proofs.GeneralizedLipschitzSampling
import LongTails.Proofs.GeneralizedLipschitzExecution
open MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace
namespace LongTails.Proofs.GeneralizedLipschitzBurnin
open LongTails.Algorithms.GeneralizedLipschitzPilot
open LongTails.Proofs.GeneralizedLipschitzSampling
open LongTails.Proofs.GeneralizedLipschitzPilot
open LongTails.Proofs.GeneralizedLipschitzExecution
variable {A Ω E : Type} [MeasurableSpace A] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma independent_test_failure (p : Measure Ω) [IsProbabilityMeasure p]
    (H : Measure A) [IsProbabilityMeasure H] {X : Ω → E} (hX : Measurable X)
    {initial : A → ℝ} (hi : Measurable initial) (c : Config) (κ G0 : ℝ)
    (hκ : 0 < κ) (hG0 : 0 < G0) (j : ℕ)
    (hnq : 0 < c.momentCount) (hnqκ : 67108864 * κ ≤ (c.momentCount : ℝ))
    (hnm : 0 < c.meanCount) (hnmκ : 9216 * κ ≤ (c.meanCount : ℝ)) :
    let m := fun a => scale G0 (initial a) j
    let q := fun a => ∫ ω, ‖OracleTemplate.clip (256 * κ * m a) (X ω)‖ ^ 2 ∂p
    let v := fun a => ∫ ω, OracleTemplate.clip (256 * κ * m a) (X ω) ∂p
    (H.prod (Measure.infinitePi fun _ : ℕ => p))
      {z | q z.1 / 4 + κ * (m z.1) ^ 2 / 64 <
          |blockMoment c κ G0 (initial z.1) (fun i => X (z.2 i)) j - q z.1| ∨
        (q z.1 < κ * (m z.1) ^ 2 / 16 ∧
          m z.1 / 32 < ‖blockMean c κ G0 (initial z.1) (fun i => X (z.2 i)) j - v z.1‖)} ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ c.depth)) +
        ENNReal.ofReal ((1 / 2 : ℝ) ^ c.repetitions) := by
  dsimp only
  let m := fun a => scale G0 (initial a) j
  let q := fun a => ∫ ω, ‖OracleTemplate.clip (256 * κ * m a) (X ω)‖ ^ 2 ∂p
  let v := fun a => ∫ ω, OracleTemplate.clip (256 * κ * m a) (X ω) ∂p
  have hm : Measurable m := measurable_scale_family hi G0 j
  have hq : Measurable q := measurable_clipped_secondMoment p (hm.const_mul (256 * κ)) (hX.comp measurable_snd)
  have hv : Measurable v := measurable_clipped_mean p (hm.const_mul (256 * κ)) (hX.comp measurable_snd)
  have hd (i : ℕ) : Measurable (fun z : A × (ℕ → Ω) => X (z.2 i)) :=
    hX.comp ((measurable_pi_apply i).comp measurable_snd)
  have hmoment := measurable_blockMoment_family c κ G0 (hi.comp measurable_fst) hd j
  have hmean := measurable_blockMean_family c κ G0 (hi.comp measurable_fst) hd j
  have hs : MeasurableSet {z : A × (ℕ → Ω) |
      q z.1 / 4 + κ * (m z.1) ^ 2 / 64 <
          |blockMoment c κ G0 (initial z.1) (fun i => X (z.2 i)) j - q z.1| ∨
        (q z.1 < κ * (m z.1) ^ 2 / 16 ∧
          m z.1 / 32 < ‖blockMean c κ G0 (initial z.1) (fun i => X (z.2 i)) j - v z.1‖)} := by
    apply MeasurableSet.union
    · simp only [← Real.norm_eq_abs]
      exact measurableSet_lt (((hq.comp measurable_fst).div_const 4).add
        ((((hm.comp measurable_fst).pow_const 2).const_mul κ).div_const 64))
        ((hmoment.sub (hq.comp measurable_fst)).norm)
    · exact (measurableSet_lt (hq.comp measurable_fst)
        ((((hm.comp measurable_fst).pow_const 2).const_mul κ).div_const 16)).inter
        (measurableSet_lt ((hm.comp measurable_fst).div_const 32)
          ((hmean.sub (hv.comp measurable_fst)).norm))
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _ : A, ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ c.depth)) +
        ENNReal.ofReal ((1 / 2 : ℝ) ^ c.repetitions) ∂H := by
      apply lintegral_mono
      intro a
      have hmpos : 0 < scale G0 (initial a) j := hG0.trans_le (le_max_left _ _)
      apply (measure_union_le _ _).trans
      apply add_le_add
      · exact blockMoment_confidence p hX c κ G0 (initial a) j hκ hmpos hnq hnqκ
      · by_cases hsmall : q a < κ * (m a) ^ 2 / 16
        · exact (measure_mono (fun _ h => h.2)).trans
            (blockMean_confidence p hX c κ G0 (initial a) j hκ hmpos hsmall.le hnm hnmκ)
        · apply (measure_mono (t := ∅) ?_).trans (by simp)
          intro ξ hξ
          exact (hsmall hξ.1).elim
    _ = _ := by simp
lemma independent_tests_failure (p : Measure Ω) [IsProbabilityMeasure p]
    (H : Measure A) [IsProbabilityMeasure H] {X : Ω → E} (hX : Measurable X)
    {initial : A → ℝ} (hi : Measurable initial) (c : Config) (κ G0 : ℝ)
    (hκ : 0 < κ) (hG0 : 0 < G0)
    (hnq : 0 < c.momentCount) (hnqκ : 67108864 * κ ≤ (c.momentCount : ℝ))
    (hnm : 0 < c.meanCount) (hnmκ : 9216 * κ ≤ (c.meanCount : ℝ)) :
    let m := fun a j => scale G0 (initial a) j
    let q := fun a j => ∫ ω, ‖OracleTemplate.clip (256 * κ * m a j) (X ω)‖ ^ 2 ∂p
    let v := fun a j => ∫ ω, OracleTemplate.clip (256 * κ * m a j) (X ω) ∂p
    (H.prod (Measure.infinitePi fun _ : ℕ => p))
      (⋃ j : Fin c.scales, {z | q z.1 j / 4 + κ * (m z.1 j) ^ 2 / 64 <
          |blockMoment c κ G0 (initial z.1) (fun i => X (z.2 i)) j - q z.1 j| ∨
        (q z.1 j < κ * (m z.1 j) ^ 2 / 16 ∧
          m z.1 j / 32 < ‖blockMean c κ G0 (initial z.1) (fun i => X (z.2 i)) j - v z.1 j‖)}) ≤
      (c.scales : ℝ≥0∞) * (ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ c.depth)) +
        ENNReal.ofReal ((1 / 2 : ℝ) ^ c.repetitions)) := by
  dsimp only
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin c.scales,
        (ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ c.depth)) +
          ENNReal.ofReal ((1 / 2 : ℝ) ^ c.repetitions)) := by
      apply Finset.sum_le_sum
      intro j _
      exact independent_test_failure p H hX hi c κ G0 hκ hG0 j hnq hnqκ hnm hnmκ
    _ = _ := by simp [nsmul_eq_mul, mul_add]
lemma tuning_tests_failure_bound (κ δ : ℝ) (hδ : 0 < δ) :
    ((tuning κ δ).scales : ℝ≥0∞) *
      (ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ (tuning κ δ).depth)) +
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (tuning κ δ).repetitions)) ≤ ENNReal.ofReal (2 * δ / 3) := by
  let J := (tuning κ δ).scales
  have hJ : (0 : ℝ) < J := by
    exact_mod_cast (LongTails.Proofs.GeneralizedLipschitzPilot.tuning_counts_pos κ δ).2.1
  have ht := tuning_tail_bounds κ δ hδ
  calc
    _ = ENNReal.ofReal ((J : ℝ) * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ (tuning κ δ).depth) +
        (1 / 2 : ℝ) ^ (tuning κ δ).repetitions)) := by
      symm
      rw [ENNReal.ofReal_mul hJ.le, ENNReal.ofReal_add (by positivity) (by positivity)]
      simp [J]
    _ ≤ ENNReal.ofReal (2 * δ / 3) := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left (add_le_add ht.1 ht.2) hJ.le
      have he : (J : ℝ) * (δ / (3 * J) + δ / (3 * J)) = 2 * δ / 3 := by
        field_simp
        ring
      exact h.trans_eq he
def testsGood (p : Measure Ω) (X : Ω → E) (c : Config) (κ G0 initial : ℝ) (data : ℕ → E) : Prop :=
  ∀ j : Fin c.scales,
    let m := scale G0 initial j
    let q := ∫ ω, ‖OracleTemplate.clip (256 * κ * m) (X ω)‖ ^ 2 ∂p
    |blockMoment c κ G0 initial data j - q| ≤ q / 4 + κ * m ^ 2 / 64 ∧
      (q < κ * m ^ 2 / 16 →
        ‖blockMean c κ G0 initial data j - ∫ ω, OracleTemplate.clip (256 * κ * m) (X ω) ∂p‖ ≤ m / 32)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma testsGood_prefix (p : Measure Ω) (X : Ω → E) (c : Config) (κ G0 initial : ℝ)
    (data tail : ℕ → E) (hdata : ∀ k, data (c.rawCount + k) = tail k) :
    testsGood p X c κ G0 initial data ↔ testsGood p X {c with rawCount := 0} κ G0 initial tail := by
  simp only [testsGood, blockMoment_prefix c κ G0 initial _ data tail hdata,
    blockMean_prefix c κ G0 initial _ data tail hdata]

lemma independent_testsGood_failure {A : Type} [MeasurableSpace A]
    (p : Measure Ω) [IsProbabilityMeasure p] (H : Measure A) [IsProbabilityMeasure H]
    {X : Ω → E} (hX : Measurable X) {initial : A → ℝ} (hi : Measurable initial)
    (c : Config) (κ G0 : ℝ) (hκ : 0 < κ) (hG0 : 0 < G0)
    (hnq : 0 < c.momentCount) (hnqκ : 67108864 * κ ≤ (c.momentCount : ℝ))
    (hnm : 0 < c.meanCount) (hnmκ : 9216 * κ ≤ (c.meanCount : ℝ)) :
    (H.prod (Measure.infinitePi fun _ : ℕ => p))
      {z | ¬ testsGood p X c κ G0 (initial z.1) (fun i => X (z.2 i))} ≤
      (c.scales : ℝ≥0∞) * (ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ c.depth)) +
        ENNReal.ofReal ((1 / 2 : ℝ) ^ c.repetitions)) := by
  have h := independent_tests_failure p H hX hi c κ G0 hκ hG0 hnq hnqκ hnm hnmκ
  convert h using 1
  congr 1
  ext z
  simp only [testsGood, not_forall, not_and_or, not_le, exists_prop, Set.mem_ofPred_eq, Set.mem_iUnion]
omit [CompleteSpace E] in
lemma measurableSet_testsGood {A : Type} [MeasurableSpace A]
    (p : Measure Ω) [SFinite p] {X : A → Ω → E} (hX : Measurable (Function.uncurry X))
    (c : Config) (κ G0 : ℝ) {initial : A → ℝ} {data : A → ℕ → E}
    (hi : Measurable initial) (hd : ∀ k, Measurable (fun a => data a k)) :
    MeasurableSet {a | testsGood p (X a) c κ G0 (initial a) (data a)} := by
  simp only [testsGood, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  have hm := measurable_scale_family hi G0 j
  have hq := measurable_clipped_secondMoment (X := X) p (hm.const_mul (256 * κ)) hX
  have hv := measurable_clipped_mean (X := X) p (hm.const_mul (256 * κ)) hX
  have hmoment := measurable_blockMoment_family c κ G0 hi hd j
  have hmean := measurable_blockMean_family c κ G0 hi hd j
  have hs := measurableSet_le ((hmoment.sub hq).norm)
    ((hq.div_const 4).add (((hm.pow_const 2).const_mul κ).div_const 64))
  have hsmall := measurableSet_lt hq (((hm.pow_const 2).const_mul κ).div_const 16)
  have hvbound := measurableSet_le ((hmean.sub hv).norm) (hm.div_const 32)
  convert hs.inter (hsmall.compl.union hvbound) using 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Real.norm_eq_abs]
  tauto
def rawGood (p : Measure Ω) (X : Ω → E) (κ G0 δ initial : ℝ) : Prop :=
  let g := ‖∫ ω, X ω ∂p‖
  let K := 2 * κ + Real.sqrt (9 * ((tuning κ δ).rawCount : ℝ) / δ)
  g ≤ initial ∧ (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ 16 * κ * initial ^ 2 ∧
    initial ≤ 2 * K * max g G0

def pilotGood (p : Measure Ω) (X : Ω → E) (κ G0 δ : ℝ) (data : ℕ → E) : Prop :=
  let c := tuning κ δ
  let initial := rawScale G0 (fun i : Fin c.rawCount => data i)
  rawGood p X κ G0 δ initial ∧ testsGood p X c κ G0 initial data

omit [CompleteSpace E] in
lemma measurableSet_rawGood {A : Type} [MeasurableSpace A]
    (p : Measure Ω) [SFinite p] {X : A → Ω → E} (hX : Measurable (Function.uncurry X))
    (κ G0 δ : ℝ) {initial : A → ℝ} (hi : Measurable initial) :
    MeasurableSet {a | rawGood p (X a) κ G0 δ (initial a)} := by
  have hg : Measurable (fun a => ‖∫ ω, X a ω ∂p‖) :=
    hX.stronglyMeasurable.integral_prod_right.measurable.norm
  have hS : Measurable (fun a => ∫ ω, ‖X a ω‖ ^ 2 ∂p) :=
    (hX.norm.pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  exact (measurableSet_le hg hi).inter ((measurableSet_le hS ((hi.pow_const 2).const_mul (16 * κ))).inter
    (measurableSet_le hi ((hg.max measurable_const).const_mul
      (2 * (2 * κ + Real.sqrt (9 * ((tuning κ δ).rawCount : ℝ) / δ))))))

omit [CompleteSpace E] in
lemma measurableSet_pilotGood {A : Type} [MeasurableSpace A]
    (p : Measure Ω) [SFinite p] {X : A → Ω → E} (hX : Measurable (Function.uncurry X))
    (κ G0 δ : ℝ) {data : A → ℕ → E} (hd : ∀ k, Measurable (fun a => data a k)) :
    MeasurableSet {a | pilotGood p (X a) κ G0 δ (data a)} := by
  have hi := measurable_rawScale_family (fun i : Fin (tuning κ δ).rawCount => hd i) G0
  exact (measurableSet_rawGood p hX κ G0 δ hi).inter
    (measurableSet_testsGood p hX (tuning κ δ) κ G0 hi hd)

omit [CompleteSpace E] in
lemma rawGood_failure (p : Measure Ω) [IsProbabilityMeasure p] {X u v : Ω → E}
    (hX : Measurable X) (hXi : Integrable X p) (hu : Measurable u) (hui : Integrable u p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, X ω = u ω + v ω)
    {κ G0 δ : ℝ} (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hδ : 0 < δ)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, X z ∂p‖) :
    (Measure.pi fun _ : Fin (tuning κ δ).rawCount => p)
      {ξ | ¬rawGood p X κ G0 δ (rawScale G0 (fun i => X (ξ i)))} ≤ ENNReal.ofReal (δ / 3) := by
  have h := configured_raw_confidence hX hXi hu hui hu2 hsplit rfl hG0 hκ hδ huBound hv
  have he := ENNReal.ofReal_le_ofReal h
  simp only [Measure.real] at he
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he
lemma pilotGood_failure (p : Measure Ω) [IsProbabilityMeasure p] {X u v : Ω → E}
    (hX : Measurable X) (hXi : Integrable X p) (hu : Measurable u) (hui : Integrable u p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, X ω = u ω + v ω)
    {κ G0 δ : ℝ} (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hδ : 0 < δ)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, X z ∂p‖) :
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | ¬pilotGood p X κ G0 δ (fun i => X (ξ i))} ≤ ENNReal.ofReal δ := by
  classical
  let c := tuning κ δ
  let H := Measure.pi (fun _ : Fin c.rawCount => p)
  let Q := Measure.infinitePi (fun _ : ℕ => p)
  let initial := fun ξ : Fin c.rawCount → Ω => rawScale G0 (fun i => X (ξ i))
  let data := fun z : (Fin c.rawCount → Ω) × (ℕ → Ω) =>
    fun i => X ((OracleTemplate.StochasticGeneralized.splitStream c.rawCount).symm z i)
  have hd (i : ℕ) : Measurable (fun z => data z i) :=
    hX.comp ((measurable_pi_apply i).comp (OracleTemplate.StochasticGeneralized.splitStream c.rawCount).symm.measurable)
  have hi : Measurable initial := measurable_rawScale_family (fun i => hX.comp (measurable_pi_apply i)) G0
  have hs := (measurableSet_pilotGood (X := fun (_ : (Fin c.rawCount → Ω) × (ℕ → Ω)) ω => X ω)
    p (hX.comp measurable_snd) κ G0 δ hd).compl
  have hp := (OracleTemplate.StochasticGeneralized.splitStream_preserving p c.rawCount).measure_preimage hs.nullMeasurableSet
  have hraw := rawGood_failure p hX hXi hu hui hu2 hsplit hκ hG0 hδ huBound hv
  have hcounts := tuning_counts_pos κ δ
  have hbounds := tuning_count_bounds κ δ
  have htests := independent_testsGood_failure p H hX hi {c with rawCount := 0} κ G0
    (by linarith) hG0 hcounts.2.2.1 hbounds.2.1 hcounts.2.2.2.1 hbounds.2.2.1
  have ht : (H.prod Q) {z | ¬testsGood p X {c with rawCount := 0} κ G0 (initial z.1)
      (fun i => X (z.2 i))} ≤ ENNReal.ofReal (2 * δ / 3) :=
    htests.trans (tuning_tests_failure_bound κ δ hδ)
  have hr : (H.prod Q) {z : (Fin c.rawCount → Ω) × (ℕ → Ω) |
      ¬rawGood p X κ G0 δ (initial z.1)} ≤ ENNReal.ofReal (δ / 3) := by
    have he : {z : (Fin c.rawCount → Ω) × (ℕ → Ω) | ¬rawGood p X κ G0 δ (initial z.1)} =
        {ξ | ¬rawGood p X κ G0 δ (initial ξ)} ×ˢ Set.univ := by ext z; simp
    rw [he, Measure.prod_prod]
    simpa [Q, H, initial, c] using hraw
  have hsub : {z | ¬pilotGood p X κ G0 δ (data z)} ⊆
      {z | ¬rawGood p X κ G0 δ (initial z.1)} ∪
      {z | ¬testsGood p X {c with rawCount := 0} κ G0 (initial z.1) (fun i => X (z.2 i))} := by
    intro z hz
    have hinit : rawScale G0 (fun i : Fin c.rawCount => data z i) = initial z.1 := by
      dsimp [data, initial, OracleTemplate.StochasticGeneralized.splitStream]
      simp
    have htail (k : ℕ) : data z (c.rawCount + k) = X (z.2 k) := by
      dsimp [data, OracleTemplate.StochasticGeneralized.splitStream]
      simp
    have htest := testsGood_prefix p X c κ G0 (initial z.1) (data z) (fun i => X (z.2 i)) htail
    change ¬(rawGood p X κ G0 δ (rawScale G0 (fun i : Fin c.rawCount => data z i)) ∧
      testsGood p X c κ G0 (rawScale G0 (fun i : Fin c.rawCount => data z i)) (data z)) at hz
    rw [hinit, htest] at hz
    exact not_and_or.mp hz
  have hb := (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hr ht))
  have htotal : ENNReal.ofReal (δ / 3) + ENNReal.ofReal (2 * δ / 3) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [htotal] at hb
  change Q {ξ | ¬pilotGood p X κ G0 δ (data (OracleTemplate.StochasticGeneralized.splitStream c.rawCount ξ))} =
    (H.prod Q) {z | ¬pilotGood p X κ G0 δ (data z)} at hp
  rw [← hp] at hb
  simpa only [data, MeasurableEquiv.symm_apply_apply] using hb

omit [CompleteSpace E] in
lemma testsGood_at_reached_scale (p : Measure Ω) [IsProbabilityMeasure p]
    {X u v : Ω → E} (hX : Measurable X) (hXi : Integrable X p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, X ω = u ω + v ω)
    (c : Config) {κ G0 initial : ℝ} (hκ : 1 ≤ κ) (hG0 : 0 < G0)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, X z ∂p‖)
    (data : ℕ → E) (htests : testsGood p X c κ G0 initial data) (j : Fin c.scales)
    (hg : ‖∫ ω, X ω ∂p‖ ≤ scale G0 initial j) :
    let m := scale G0 initial j
    let q := ∫ ω, ‖OracleTemplate.clip (256 * κ * m) (X ω)‖ ^ 2 ∂p
    (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ 2 * q + 2 * G0 ^ 2 ∧
      |blockMoment c κ G0 initial data j - q| ≤ q / 4 + κ * m ^ 2 / 64 ∧
      (blockMoment c κ G0 initial data j < κ * m ^ 2 / 32 →
        |‖blockMean c κ G0 initial data j‖ - ‖∫ ω, X ω ∂p‖| ≤ 5 * m / 128) := by
  let m := scale G0 initial j
  let B := 256 * κ * m
  have hκpos : 0 < κ := by linarith
  have hG0m : G0 ≤ m := le_max_left _ _
  have hm : 0 < m := hG0.trans_le hG0m
  have hB : 0 < B := by dsimp [B]; positivity
  have hvhalf : ∀ᵐ ω ∂p, ‖v ω‖ ≤ B / 2 := by
    filter_upwards [hv] with ω hω
    have hh := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2 * κ)
    dsimp [B]
    change ‖v ω‖ ≤ 256 * κ * m / 2
    change 2 * κ * ‖∫ z, X z ∂p‖ ≤ 2 * κ * m at hh
    nlinarith [mul_pos hκpos hm]
  have hvfull : ∀ᵐ ω ∂p, ‖v ω‖ ≤ B := hvhalf.mono fun _ h => h.trans (by linarith)
  have hS := split_secondMoment_clipped hX hu2 hsplit hB.le hvfull
  have hbias := clipped_bias_bounded_part hX hXi hu2 hsplit hB hvhalf
  have hratio : (∫ ω, ‖u ω‖ ^ 2 ∂p) / (B / 2) ≤ m / 128 := by
    apply (div_le_iff₀ (by positivity : 0 < B / 2)).mpr
    have hs := pow_le_pow_left₀ hG0.le hG0m 2
    have hk := mul_le_mul_of_nonneg_right hκ (sq_nonneg m)
    dsimp [B]
    nlinarith
  have htest := htests j
  refine ⟨by dsimp [B, m] at hS; linarith, htest.1, ?_⟩
  intro hrejected
  have hq := moment_rejection_upper htest.1 hrejected
  have hmean := htest.2 hq
  have ht := norm_sub_le_norm_sub_add_norm_sub (blockMean c κ G0 initial data j)
    (∫ ω, OracleTemplate.clip B (X ω) ∂p) (∫ ω, X ω ∂p)
  rw [norm_sub_rev (∫ ω, OracleTemplate.clip B (X ω) ∂p)] at ht
  have hn := abs_norm_sub_norm_le (blockMean c κ G0 initial data j) (∫ ω, X ω ∂p)
  change ‖blockMean c κ G0 initial data j - ∫ ω, OracleTemplate.clip B (X ω) ∂p‖ ≤ m / 32 at hmean
  change |‖blockMean c κ G0 initial data j‖ - ‖∫ ω, X ω ∂p‖| ≤ 5 * m / 128
  linarith

omit [CompleteSpace E] in
lemma pilotGood_decision (p : Measure Ω) [IsProbabilityMeasure p]
    {X u v : Ω → E} (hX : Measurable X) (hXi : Integrable X p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, X ω = u ω + v ω)
    {κ G0 δ a : ℝ} (hκ : 1 ≤ κ) (hG0 : 0 < G0) (ha : 0 ≤ a)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, X z ∂p‖)
    (hgBound : ‖∫ z, X z ∂p‖ ≤ G0 + a)
    (hSBound : (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * a ^ 2)
    (data : ℕ → E) (hgood : pilotGood p X κ G0 δ data) :
    let c := tuning κ δ
    let initial := rawScale G0 (fun i : Fin c.rawCount => data i)
    match blockDecision c κ G0 data with
    | .terminal => ‖∫ ω, X ω ∂p‖ ≤ 64 * G0
    | .update j => j < c.scales ∧ 64 * G0 < scale G0 initial j ∧
        ‖∫ ω, X ω ∂p‖ ≤ scale G0 initial j ∧
        (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ 16 * κ * (scale G0 initial j) ^ 2 ∧
        scale G0 initial j / 16 ≤ a
    | .exhausted => False := by
  let c := tuning κ δ
  let initial := rawScale G0 (fun i : Fin c.rawCount => data i)
  let g := ‖∫ ω, X ω ∂p‖
  let S := ∫ ω, ‖X ω‖ ^ 2 ∂p
  let q := fun j => ∫ ω, ‖OracleTemplate.clip (256 * κ * scale G0 initial j) (X ω)‖ ^ 2 ∂p
  have hraw : rawGood p X κ G0 δ initial := hgood.1
  have htests : testsGood p X c κ G0 initial data := hgood.2
  have hzero : scale G0 initial 0 = initial := by
    have hfloor := rawScale_ge_floor G0 (fun i : Fin c.rawCount => data i)
    simp only [scale, pow_zero, div_one]
    apply max_eq_right
    dsimp [initial]
    linarith
  have hstats (j : ℕ) (_hlo : 0 ≤ j) (hj : j < 0 + c.scales) (hg : g ≤ scale G0 initial j) :=
    testsGood_at_reached_scale p hX hXi hu2 hsplit c hκ hG0 huBound hv data htests
      ⟨j, by omega⟩ hg
  have hinit : g ≤ scale G0 initial 0 ∧ S ≤ 16 * κ * (scale G0 initial 0) ^ 2 := by
    rw [hzero]
    exact ⟨hraw.1, hraw.2.1⟩
  have hinv := selection_preserves_bounds G0 initial κ g S (blockMoment c κ G0 initial data) q
    (blockMean c κ G0 initial data) hG0.le hκ c.scales 0 hstats hinit
  have hlast : scale G0 initial (0 + c.scales) ≤ max g G0 := by
    simpa only [Nat.zero_add] using configured_scale_cap hG0.le (by linarith : 0 < κ) hraw.2.2
  have hno := selection_no_exhaustion G0 initial κ g (blockMoment c κ G0 initial data)
    (blockMean c κ G0 initial data) hG0.le c.scales 0 (tuning_counts_pos κ δ).2.1
    (fun j hlo hhi hg => (hstats j hlo hhi hg).2.2) hinit.1 hlast
  change match select G0 initial κ (blockMoment c κ G0 initial data) (blockMean c κ G0 initial data) 0 c.scales with
    | .terminal => g ≤ 64 * G0
    | .update j => j < c.scales ∧ 64 * G0 < scale G0 initial j ∧ g ≤ scale G0 initial j ∧
        S ≤ 16 * κ * (scale G0 initial j) ^ 2 ∧ scale G0 initial j / 16 ≤ a
    | .exhausted => False
  cases he : select G0 initial κ (blockMoment c κ G0 initial data) (blockMean c κ G0 initial data) 0 c.scales with
  | terminal => simpa only [he] using hinv
  | exhausted => exact hno he
  | update j =>
    obtain ⟨_, hj, hm, haccept⟩ := select_update_spec G0 initial κ (blockMoment c κ G0 initial data)
      (blockMean c κ G0 initial data) c.scales 0 j he
    rw [he] at hinv
    have hj' : j < c.scales := by omega
    refine ⟨hj', hm, hinv.1, hinv.2, ?_⟩
    have hs := hstats j (by omega) hj hinv.1
    have hmpos : 0 < scale G0 initial j := by linarith
    have hκpos : 0 < κ := by linarith
    have hclip : q j ≤ S := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
        (split_secondMoment_integrable hX hu2 hsplit hv)
      filter_upwards [] with ω
      apply pow_le_pow_left₀ (norm_nonneg _)
      by_cases h : ‖X ω‖ ≤ 256 * κ * scale G0 initial j
      · rw [OracleTemplate.clip_eq_self h]
      · exact (OracleTemplate.norm_clip_le (by positivity) _).trans (le_of_not_ge h)
    exact pilot_accept_gap hκ hG0.le hm ha hs.2.1 (hclip.trans hSBound) hgBound hs.2.2 haccept

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma testsGood_congr_pilot (p : MeasureTheory.Measure Ω) (X : Ω → E) (c : Config) (κ G0 initial : ℝ)
    (data data' : ℕ → E) (he : ∀ i, i < c.rawCount + c.scales * c.scaleCalls → data i = data' i) :
    testsGood p X c κ G0 initial data ↔ testsGood p X c κ G0 initial data' := by
  unfold testsGood
  apply forall_congr'
  intro j
  rw [blockMoment_congr_pilot c κ G0 initial j.isLt data data' he,
    blockMean_congr_pilot c κ G0 initial j.isLt data data' he]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pilotGood_congr_pilot (p : MeasureTheory.Measure Ω) (X : Ω → E) (κ G0 δ : ℝ)
    (data data' : ℕ → E)
    (he : ∀ i, i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls → data i = data' i) :
    pilotGood p X κ G0 δ data ↔ pilotGood p X κ G0 δ data' := by
  dsimp [pilotGood]
  rw [rawScale_congr_pilot (tuning κ δ) G0 data data' he]
  exact and_congr Iff.rfl (testsGood_congr_pilot p X (tuning κ δ) κ G0 _ data data' he)

lemma good_update_drift (p : Measure Ω) [IsProbabilityMeasure p]
    {X u v : Ω → E} (hX : Measurable X) (hXi : Integrable X p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, X ω = u ω + v ω)
    (center x xstar : E) {R G κ G0 δ gap : ℝ} (hR : 0 ≤ R) (hG : 0 < G)
    (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hgap : 0 ≤ gap) (hstar : ‖xstar - center‖ ≤ R)
    (hsub : gap ≤ ⟪x - xstar, ∫ ω, X ω ∂p⟫)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, X z ∂p‖)
    (hgBound : ‖∫ z, X z ∂p‖ ≤ G0 + G * gap)
    (hSBound : (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * (G * gap) ^ 2)
    (data : ℕ → E) (hgood : pilotGood p X κ G0 δ data) {j : ℕ}
    (hupdate : blockDecision (tuning κ δ) κ G0 data = .update j) :
    let c := tuning κ δ
    let m := scale G0 (rawScale G0 (fun i : Fin c.rawCount => data i)) j
    (∫ ξ : Fin c.updateCount → Ω,
      ‖center + OracleTemplate.clip R (x - (1 / (128 * G * m)) •
        ((1 / (c.updateCount : ℝ)) • ∑ i, X (ξ i)) - center) - xstar‖ ^ 2
      ∂Measure.pi (fun _ : Fin c.updateCount => p)) ≤ ‖x - xstar‖ ^ 2 - 1 / (2048 * G ^ 2) := by
  let c := tuning κ δ
  let m := scale G0 (rawScale G0 (fun i : Fin c.rawCount => data i)) j
  have hdecision := pilotGood_decision p hX hXi hu2 hsplit hκ hG0 (mul_nonneg hG.le hgap)
    huBound hv hgBound hSBound data hgood
  dsimp only at hdecision
  rw [hupdate] at hdecision
  have hm : 0 < m := by dsimp [m]; linarith [hdecision.2.1]
  have hn : 0 < c.updateCount := (tuning_counts_pos κ δ).2.2.2.2.2
  have hnκ : 16 * κ ≤ (c.updateCount : ℝ) := (tuning_count_bounds κ δ).2.2.2
  have hX2 := split_secondMoment_integrable hX hu2 hsplit hv
  have hf := fresh_mean_moments hX hXi hX2 c.updateCount hn
  have hb := fresh_mean_secondMoment_bound hX hXi hX2 hdecision.2.2.1 hdecision.2.2.2.1 c.updateCount hn hnκ
  have hmean : Measurable (fun ξ : Fin c.updateCount → Ω => (1 / (c.updateCount : ℝ)) • ∑ i, X (ξ i)) := by fun_prop
  have hgap' : m / (16 * G) ≤ gap := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * G)).mpr
    dsimp [m] at *
    nlinarith [hdecision.2.2.2.2]
  exact pilot_step_drift center x xstar hR hG hm hstar hmean hf.1 hf.2.2.1
    (by rw [hf.2.1]; exact hsub) hgap' hb

noncomputable def trackedUpdate (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (samples : Fin (tuning κ δ).calls → Ω) : (E × Bool) × Bool := by
  classical
  let c := tuning κ δ
  let data := fun i => if h : i < c.calls then oracle s.1.1 (samples ⟨i, h⟩) else 0
  exact (blockUpdate c center R G G0 κ s.1 data,
    if s.2 = true ∧ (s.1.2 = true ∨ pilotGood p (oracle s.1.1) κ G0 δ data) then true else false)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_first (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (samples : Fin (tuning κ δ).calls → Ω) :
    (trackedUpdate p oracle center R G κ G0 δ s samples).1 =
      blockUpdate (tuning κ δ) center R G G0 κ s.1
        (fun i => if h : i < (tuning κ δ).calls then oracle s.1.1 (samples ⟨i, h⟩) else 0) := rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_clean (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (samples : Fin (tuning κ δ).calls → Ω)
    (h : (trackedUpdate p oracle center R G κ G0 δ s samples).2 = true) : s.2 = true := by
  classical
  dsimp [trackedUpdate] at h
  split_ifs at h with hc
  exact hc.1

omit [CompleteSpace E] in
lemma measurable_trackedUpdate (p : Measure Ω) [SFinite p] {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (center : E) (R G κ G0 δ : ℝ) :
    Measurable (Function.uncurry (trackedUpdate p oracle center R G κ G0 δ)) := by
  classical
  let c := tuning κ δ
  let data := fun z : ((E × Bool) × Bool) × (Fin c.calls → Ω) =>
    fun i => if h : i < c.calls then oracle z.1.1.1 (z.2 ⟨i, h⟩) else 0
  have hd (i : ℕ) : Measurable (fun z => data z i) := by
    dsimp [data]
    split_ifs
    · exact ho.comp (measurable_fst.fst.fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
    · exact measurable_const
  have hx : Measurable (Function.uncurry (fun z : ((E × Bool) × Bool) × (Fin c.calls → Ω) => oracle z.1.1.1)) :=
    ho.comp (measurable_fst.fst.fst.fst.prodMk measurable_snd)
  have hg := measurableSet_pilotGood p hx κ G0 δ hd
  have hc : MeasurableSet {z : ((E × Bool) × Bool) × (Fin c.calls → Ω) | z.1.2 = true} :=
    measurableSet_eq_fun measurable_fst.snd measurable_const
  have hf : MeasurableSet {z : ((E × Bool) × Bool) × (Fin c.calls → Ω) | z.1.1.2 = true} :=
    measurableSet_eq_fun measurable_fst.fst.snd measurable_const
  have hmark : Measurable (fun z : ((E × Bool) × Bool) × (Fin c.calls → Ω) =>
      if z.1.2 = true ∧ (z.1.1.2 = true ∨ pilotGood p (oracle z.1.1.1) κ G0 δ (data z)) then true else false) :=
    Measurable.ite (hc.inter (hf.union hg)) measurable_const measurable_const
  exact (measurable_blockUpdate_family c center R G G0 κ measurable_fst.fst hd).prodMk hmark
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_frozen (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (samples : Fin (tuning κ δ).calls → Ω) (hf : s.1.2 = true) :
    trackedUpdate p oracle center R G κ G0 δ s samples = s := by
  classical
  rcases s with ⟨⟨x, done⟩, clean⟩
  dsimp at hf
  subst done
  cases clean <;> simp [trackedUpdate, blockUpdate]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_mem_ball (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (hR : 0 ≤ R) (s : (E × Bool) × Bool)
    (samples : Fin (tuning κ δ).calls → Ω) (hs : ‖s.1.1 - center‖ ≤ R) :
    ‖(trackedUpdate p oracle center R G κ G0 δ s samples).1.1 - center‖ ≤ R := by
  rw [trackedUpdate_first]
  exact blockUpdate_mem_ball (tuning κ δ) center R G G0 κ hR s.1 _ hs

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_running (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (samples : Fin (tuning κ δ).calls → Ω)
    (hc : (trackedUpdate p oracle center R G κ G0 δ s samples).2 = true)
    (hr : (trackedUpdate p oracle center R G κ G0 δ s samples).1.2 = false) :
    s.2 = true ∧ s.1.2 = false := by
  refine ⟨trackedUpdate_clean p oracle center R G κ G0 δ s samples hc, ?_⟩
  cases hf : s.1.2 with
  | false => rfl
  | true =>
    rw [trackedUpdate_frozen p oracle center R G κ G0 δ s samples hf] at hr
    simp [hf] at hr

lemma pilotGood_failure_finite (p : Measure Ω) [IsProbabilityMeasure p] {X u v : Ω → E}
    (hX : Measurable X) (hXi : Integrable X p) (hu : Measurable u) (hui : Integrable u p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, X ω = u ω + v ω)
    {κ G0 δ : ℝ} (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hδ : 0 < δ)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, X z ∂p‖) :
    (Measure.pi fun _ : Fin (tuning κ δ).calls => p)
      {ξ | ¬pilotGood p X κ G0 δ (fun i => if h : i < (tuning κ δ).calls then X (ξ ⟨i, h⟩) else 0)} ≤
      ENNReal.ofReal δ := by
  let c := tuning κ δ
  let data := fun ξ : Fin c.calls → Ω => fun i => if h : i < c.calls then X (ξ ⟨i, h⟩) else 0
  have hd (i : ℕ) : Measurable (fun ξ => data ξ i) := by
    dsimp [data]
    split_ifs
    · exact hX.comp (measurable_pi_apply _)
    · exact measurable_const
  have hs := (measurableSet_pilotGood (X := fun (_ : Fin c.calls → Ω) ω => X ω)
    p (hX.comp measurable_snd) κ G0 δ hd).compl
  have hp := (OracleTemplate.StochasticGeneralized.prefix_preserving p c.calls).measure_preimage hs.nullMeasurableSet
  have hbound := pilotGood_failure p hX hXi hu hui hu2 hsplit hκ hG0 hδ huBound hv
  change (Measure.infinitePi fun _ : ℕ => p)
    {ξ | ¬pilotGood p X κ G0 δ (data (fun i : Fin c.calls => ξ i))} =
      (Measure.pi fun _ : Fin c.calls => p) {ξ | ¬pilotGood p X κ G0 δ (data ξ)} at hp
  rw [← hp]
  convert hbound using 1
  congr 1
  ext ξ
  apply not_congr
  apply pilotGood_congr_pilot
  intro i hi
  have hlt : i < c.calls := by dsimp [c, Config.calls] at *; omega
  simp [data, hlt]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_split_good_update (p : Measure Ω) (oracle : E → Ω → E)
    (center x : E) (R G κ G0 δ : ℝ)
    (a : Fin ((tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls) → Ω)
    (b : Fin (tuning κ δ).updateCount → Ω) {j : ℕ}
    (hgood : pilotGood p (oracle x) κ G0 δ (fun i =>
      if h : i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls then oracle x (a ⟨i, h⟩) else 0))
    (hupdate : blockDecision (tuning κ δ) κ G0 (fun i =>
      if h : i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls then oracle x (a ⟨i, h⟩) else 0) = .update j) :
    let c := tuning κ δ
    let initial := rawScale G0 (fun i : Fin c.rawCount => oracle x (a ⟨i, by have hi := i.isLt; dsimp [c] at hi ⊢; omega⟩))
    trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
      ((splitFinite (c.rawCount + c.scales * c.scaleCalls) c.updateCount).symm (a, b)) =
      ((center + OracleTemplate.clip R (x - (1 / (128 * G * scale G0 initial j)) •
        ((1 / (c.updateCount : ℝ)) • ∑ i, oracle x (b i)) - center), false), true) := by
  classical
  let c := tuning κ δ
  let N := c.rawCount + c.scales * c.scaleCalls
  let d0 := fun i => if h : i < N then oracle x (a ⟨i, h⟩) else 0
  let full := fun i => if h : i < c.calls then oracle x
    ((splitFinite N c.updateCount).symm (a, b) ⟨i, h⟩) else 0
  have he (i : ℕ) (hi : i < N) : full i = d0 i := by
    rw [show d0 i = oracle x (a ⟨i, hi⟩) by simp [d0, hi]]
    exact split_reply_prefix c (oracle x) a b i hi
  have hdec : blockDecision c κ G0 full = .update j :=
    (blockDecision_congr_pilot c κ G0 full d0 he).trans hupdate
  have hgf : pilotGood p (oracle x) κ G0 δ full :=
    (pilotGood_congr_pilot p (oracle x) κ G0 δ full d0 he).mpr hgood
  have hraw : rawScale G0 (fun i : Fin c.rawCount => full i) =
      rawScale G0 (fun i : Fin c.rawCount => oracle x (a ⟨i, by have hi := i.isLt; dsimp [c] at hi ⊢; omega⟩)) := by
    congr 1
    funext i
    exact split_reply_prefix c (oracle x) a b i (by have hi := i.isLt; dsimp [c] at hi ⊢; omega)
  have hsum : (∑ i : Fin c.updateCount, full (c.rawCount + c.scales * c.scaleCalls + i)) =
      ∑ i : Fin c.updateCount, oracle x (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact split_reply_update c (oracle x) a b i
  change (blockUpdate c center R G G0 κ (x, false) full,
    if true = true ∧ (false = true ∨ pilotGood p (oracle x) κ G0 δ full) then true else false) = _
  simp only [hgf, or_true, and_true, ↓reduceIte]
  simp only [blockUpdate, Bool.false_eq_true, ↓reduceIte, hdec]
  rw [hraw, hsum]

lemma trackedUpdate_failure (p : Measure Ω) [IsProbabilityMeasure p] (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool) (hc : s.2 = true)
    {u v : Ω → E} (hX : Measurable (oracle s.1.1)) (hXi : Integrable (oracle s.1.1) p)
    (hu : Measurable u) (hui : Integrable u p) (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p)
    (hsplit : ∀ᵐ ω ∂p, oracle s.1.1 ω = u ω + v ω) (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hδ : 0 < δ)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, oracle s.1.1 z ∂p‖) :
    (Measure.pi fun _ : Fin (tuning κ δ).calls => p)
      {ξ | (trackedUpdate p oracle center R G κ G0 δ s ξ).2 = false} ≤ ENNReal.ofReal δ := by
  have h := pilotGood_failure_finite p hX hXi hu hui hu2 hsplit hκ hG0 hδ huBound hv
  apply (measure_mono ?_).trans h
  intro ξ hξ hgood
  have ht : (trackedUpdate p oracle center R G κ G0 δ s ξ).2 = true := by
    dsimp only [trackedUpdate]
    simp only [hc, hgood, or_true, and_true, ↓reduceIte]
  rw [hξ] at ht
  contradiction

def runningIndicator (s : (E × Bool) × Bool) : ℝ := if s.2 = true ∧ s.1.2 = false then 1 else 0
def failureIndicator (s : (E × Bool) × Bool) : ℝ := if s.2 = false then 1 else 0
def potential (xstar : E) (s : (E × Bool) × Bool) : ℝ :=
  if s.2 = true ∧ s.1.2 = false then ‖s.1.1 - xstar‖ ^ 2 else 0
omit [NormedAddCommGroup E] [MeasurableSpace E] in
lemma runningIndicator_bounds (s : (E × Bool) × Bool) : 0 ≤ runningIndicator s ∧ runningIndicator s ≤ 1 := by
  unfold runningIndicator
  split_ifs <;> norm_num
omit [NormedAddCommGroup E] [MeasurableSpace E] in
lemma failureIndicator_bounds (s : (E × Bool) × Bool) : 0 ≤ failureIndicator s ∧ failureIndicator s ≤ 1 := by
  unfold failureIndicator
  split_ifs <;> norm_num
omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma potential_nonneg (xstar : E) (s : (E × Bool) × Bool) : 0 ≤ potential xstar s := by
  unfold potential
  split_ifs <;> positivity
omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma potential_bound (center xstar : E) {R : ℝ} (hstar : ‖xstar - center‖ ≤ R)
    (s : (E × Bool) × Bool) (hs : ‖s.1.1 - center‖ ≤ R) : potential xstar s ≤ 4 * R ^ 2 := by
  unfold potential
  split_ifs
  · have h := norm_sub_le_norm_sub_add_norm_sub s.1.1 center xstar
    rw [norm_sub_rev center xstar] at h
    have hh : ‖s.1.1 - xstar‖ ≤ 2 * R := by linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith
  · positivity
omit [NormedAddCommGroup E] [BorelSpace E] in
lemma measurable_runningIndicator : Measurable (runningIndicator (E := E)) :=
  Measurable.ite ((measurableSet_eq_fun measurable_snd measurable_const).inter
    (measurableSet_eq_fun measurable_fst.snd measurable_const)) measurable_const measurable_const
omit [NormedAddCommGroup E] [BorelSpace E] in
lemma measurable_failureIndicator : Measurable (failureIndicator (E := E)) :=
  Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const measurable_const
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_potential (xstar : E) : Measurable (potential xstar) :=
  Measurable.ite ((measurableSet_eq_fun measurable_snd measurable_const).inter
    (measurableSet_eq_fun measurable_fst.snd measurable_const))
    ((measurable_fst.fst.sub measurable_const).norm.pow_const 2) measurable_const

lemma tracked_split_update_integral (p : Measure Ω) [IsProbabilityMeasure p]
    (oracle : E → Ω → E) {u v : Ω → E} (center x xstar : E)
     (hX : Measurable (oracle x)) (hXi : Integrable (oracle x) p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, (oracle x) ω = u ω + v ω)
    {R G κ G0 δ gap : ℝ} (hR : 0 ≤ R) (hG : 0 < G)
    (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hgap : 0 ≤ gap) (hstar : ‖xstar - center‖ ≤ R)
    (hsub : gap ≤ ⟪x - xstar, ∫ ω, (oracle x) ω ∂p⟫)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, (oracle x) z ∂p‖)
    (hgBound : ‖∫ z, (oracle x) z ∂p‖ ≤ G0 + G * gap)
    (hSBound : (∫ ω, ‖(oracle x) ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * (G * gap) ^ 2)
    (a : Fin ((tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls) → Ω)
    (hgood : pilotGood p (oracle x) κ G0 δ (fun i =>
      if h : i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls then oracle x (a ⟨i, h⟩) else 0))
    {j : ℕ} (hupdate : blockDecision (tuning κ δ) κ G0 (fun i =>
      if h : i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls then oracle x (a ⟨i, h⟩) else 0) = .update j) :
    let c := tuning κ δ
    let next := fun b : Fin c.updateCount → Ω => trackedUpdate p oracle center R G κ G0 δ
      ((x, false), true) ((splitFinite (c.rawCount + c.scales * c.scaleCalls) c.updateCount).symm (a, b))
    (∫ b, potential xstar (next b) + (1 / (2048 * G ^ 2)) * runningIndicator (next b)
      ∂Measure.pi (fun _ : Fin c.updateCount => p)) ≤ ‖x - xstar‖ ^ 2 := by
  classical
  let c := tuning κ δ
  let N := c.rawCount + c.scales * c.scaleCalls
  let data := fun i => if h : i < N then oracle x (a ⟨i, h⟩) else 0
  let m := scale G0 (rawScale G0 (fun i : Fin c.rawCount => data i)) j
  let Y := fun b : Fin c.updateCount → Ω => (1 / (c.updateCount : ℝ)) • ∑ i, oracle x (b i)
  let z := fun b => center + OracleTemplate.clip R (x - (1 / (128 * G * m)) • Y b - center)
  have hraw : rawScale G0 (fun i : Fin c.rawCount => data i) =
      rawScale G0 (fun i : Fin c.rawCount => oracle x (a ⟨i, by have hi := i.isLt; dsimp [c] at hi ⊢; omega⟩)) := by
    congr 1
    funext i
    have hi : (i : ℕ) < N := by dsimp [N]; omega
    simp [data, hi]
  have he (b : Fin c.updateCount → Ω) :
      trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
        ((splitFinite N c.updateCount).symm (a, b)) = ((z b, false), true) := by
    have h := trackedUpdate_split_good_update p oracle center x R G κ G0 δ a b hgood hupdate
    dsimp only at h
    simpa only [z, Y, m, hraw] using h
  change (∫ b, potential xstar (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
      ((splitFinite N c.updateCount).symm (a, b))) + (1 / (2048 * G ^ 2)) * runningIndicator
      (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
      ((splitFinite N c.updateCount).symm (a, b))) ∂Measure.pi (fun _ : Fin c.updateCount => p)) ≤ _
  have heint : (∫ b, potential xstar (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
      ((splitFinite N c.updateCount).symm (a, b))) + (1 / (2048 * G ^ 2)) * runningIndicator
      (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
      ((splitFinite N c.updateCount).symm (a, b))) ∂Measure.pi (fun _ : Fin c.updateCount => p)) =
      (∫ b, ‖z b - xstar‖ ^ 2 + 1 / (2048 * G ^ 2) ∂Measure.pi (fun _ : Fin c.updateCount => p)) := by
    apply integral_congr_ae
    filter_upwards [] with b
    rw [he]
    simp [potential, runningIndicator]
  rw [heint]
  have hX2 := split_secondMoment_integrable hX hu2 hsplit hv
  have hf := fresh_mean_moments hX hXi hX2 c.updateCount (tuning_counts_pos κ δ).2.2.2.2.2
  have hm : Measurable Y := by dsimp [Y]; fun_prop
  have hz := (projected_step_integral center x xstar hR hstar (η := 1 / (128 * G * m)) hm hf.1 hf.2.2.1).1
  rw [integral_add hz (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have hb := good_update_drift p hX hXi hu2 hsplit center x xstar hR hG hκ hG0 hgap hstar hsub huBound hv hgBound hSBound data hgood hupdate
  dsimp only at hb
  change (∫ b, ‖z b - xstar‖ ^ 2 ∂Measure.pi (fun _ : Fin c.updateCount => p)) ≤ ‖x - xstar‖ ^ 2 - 1 / (2048 * G ^ 2) at hb
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_potential {P : Measure Ω} [IsProbabilityMeasure P]
    (center xstar : E) {R : ℝ} (hstar : ‖xstar - center‖ ≤ R)
    {s : Ω → (E × Bool) × Bool} (hs : Measurable s)
    (hb : ∀ ω, ‖(s ω).1.1 - center‖ ≤ R) : Integrable (fun ω => potential xstar (s ω)) P := by
  apply Integrable.mono' (integrable_const (4 * R ^ 2)) ((measurable_potential xstar).comp hs).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (potential_nonneg xstar (s ω))]
  exact potential_bound center xstar hstar (s ω) (hb ω)
omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
lemma integrable_runningIndicator {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Ω → (E × Bool) × Bool} (hs : Measurable s) : Integrable (fun ω => runningIndicator (s ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (measurable_runningIndicator.comp hs).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (runningIndicator_bounds (s ω)).1]
  exact (runningIndicator_bounds (s ω)).2
omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
lemma integrable_failureIndicator {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Ω → (E × Bool) × Bool} (hs : Measurable s) : Integrable (fun ω => failureIndicator (s ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (measurable_failureIndicator.comp hs).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (failureIndicator_bounds (s ω)).1]
  exact (failureIndicator_bounds (s ω)).2

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma tracked_split_inactive (p : Measure Ω) (oracle : E → Ω → E)
    (center x xstar : E) (R G κ G0 δ : ℝ)
    (a : Fin ((tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls) → Ω)
    (b : Fin (tuning κ δ).updateCount → Ω)
    (hinactive : ¬pilotGood p (oracle x) κ G0 δ (fun i =>
      if h : i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls then oracle x (a ⟨i, h⟩) else 0) ∨
      blockDecision (tuning κ δ) κ G0 (fun i =>
      if h : i < (tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls then oracle x (a ⟨i, h⟩) else 0) = .terminal) :
    let c := tuning κ δ
    let next := trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
      ((splitFinite (c.rawCount + c.scales * c.scaleCalls) c.updateCount).symm (a, b))
    potential xstar next = 0 ∧ runningIndicator next = 0 := by
  classical
  let c := tuning κ δ
  let N := c.rawCount + c.scales * c.scaleCalls
  let data := fun i => if h : i < N then oracle x (a ⟨i, h⟩) else 0
  let full := fun i => if h : i < c.calls then oracle x
    ((splitFinite N c.updateCount).symm (a, b) ⟨i, h⟩) else 0
  have he (i : ℕ) (hi : i < N) : full i = data i := by
    rw [show data i = oracle x (a ⟨i, hi⟩) by simp [data, hi]]
    exact split_reply_prefix c (oracle x) a b i hi
  have hgf := pilotGood_congr_pilot p (oracle x) κ G0 δ full data he
  have hdec := blockDecision_congr_pilot c κ G0 full data he
  change potential xstar (blockUpdate c center R G G0 κ (x, false) full,
    if true = true ∧ (false = true ∨ pilotGood p (oracle x) κ G0 δ full) then true else false) = 0 ∧
    runningIndicator (blockUpdate c center R G G0 κ (x, false) full,
    if true = true ∧ (false = true ∨ pilotGood p (oracle x) κ G0 δ full) then true else false) = 0
  rcases hinactive with hbad | hterminal
  · have hn : ¬pilotGood p (oracle x) κ G0 δ full := fun h => hbad (hgf.mp h)
    simp [potential, runningIndicator, hn]
  · have ht : blockDecision c κ G0 full = .terminal := hdec.trans hterminal
    simp [potential, runningIndicator, blockUpdate, ht]

lemma tracked_split_integral (p : Measure Ω) [IsProbabilityMeasure p]
    (oracle : E → Ω → E) {u v : Ω → E} (center x xstar : E)
     (hX : Measurable (oracle x)) (hXi : Integrable (oracle x) p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, (oracle x) ω = u ω + v ω)
    {R G κ G0 δ gap : ℝ} (hR : 0 ≤ R) (hG : 0 < G)
    (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hgap : 0 ≤ gap) (hstar : ‖xstar - center‖ ≤ R)
    (hsub : gap ≤ ⟪x - xstar, ∫ ω, (oracle x) ω ∂p⟫)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, (oracle x) z ∂p‖)
    (hgBound : ‖∫ z, (oracle x) z ∂p‖ ≤ G0 + G * gap)
    (hSBound : (∫ ω, ‖(oracle x) ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * (G * gap) ^ 2)
    (a : Fin ((tuning κ δ).rawCount + (tuning κ δ).scales * (tuning κ δ).scaleCalls) → Ω)
 :
    let c := tuning κ δ
    let next := fun b : Fin c.updateCount → Ω => trackedUpdate p oracle center R G κ G0 δ
      ((x, false), true) ((splitFinite (c.rawCount + c.scales * c.scaleCalls) c.updateCount).symm (a, b))
    (∫ b, potential xstar (next b) + (1 / (2048 * G ^ 2)) * runningIndicator (next b)
      ∂Measure.pi (fun _ : Fin c.updateCount => p)) ≤ ‖x - xstar‖ ^ 2 := by
  classical
  let c := tuning κ δ
  let N := c.rawCount + c.scales * c.scaleCalls
  let data := fun i => if h : i < N then oracle x (a ⟨i, h⟩) else 0
  by_cases hg : pilotGood p (oracle x) κ G0 δ data
  · have hd := pilotGood_decision p hX hXi hu2 hsplit hκ hG0 (mul_nonneg hG.le hgap)
      huBound hv hgBound hSBound data hg
    dsimp only at hd
    cases he : blockDecision c κ G0 data with
    | exhausted => rw [he] at hd; exact hd.elim
    | update j =>
      exact tracked_split_update_integral p oracle center x xstar hX hXi hu2 hsplit hR hG hκ hG0 hgap hstar hsub huBound hv hgBound hSBound a hg he
    | terminal =>
      have hz (b : Fin c.updateCount → Ω) := tracked_split_inactive p oracle center x xstar R G κ G0 δ a b (Or.inr he)
      have hi : (∫ b, potential xstar (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
          ((splitFinite N c.updateCount).symm (a, b))) + (1 / (2048 * G ^ 2)) * runningIndicator
          (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
          ((splitFinite N c.updateCount).symm (a, b))) ∂Measure.pi (fun _ : Fin c.updateCount => p)) = 0 := by
        calc _ = ∫ _ : Fin c.updateCount → Ω, (0 : ℝ) ∂Measure.pi (fun _ : Fin c.updateCount => p) := by
               apply integral_congr_ae
               filter_upwards [] with b
               rw [(hz b).1, (hz b).2, mul_zero, add_zero]
             _ = 0 := integral_zero _ _
      exact hi.le.trans (sq_nonneg _)
  · have hz (b : Fin c.updateCount → Ω) := tracked_split_inactive p oracle center x xstar R G κ G0 δ a b (Or.inl hg)
    have hi : (∫ b, potential xstar (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
        ((splitFinite N c.updateCount).symm (a, b))) + (1 / (2048 * G ^ 2)) * runningIndicator
        (trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
        ((splitFinite N c.updateCount).symm (a, b))) ∂Measure.pi (fun _ : Fin c.updateCount => p)) = 0 := by
      calc _ = ∫ _ : Fin c.updateCount → Ω, (0 : ℝ) ∂Measure.pi (fun _ : Fin c.updateCount => p) := by
             apply integral_congr_ae
             filter_upwards [] with b
             rw [(hz b).1, (hz b).2, mul_zero, add_zero]
           _ = 0 := integral_zero _ _
    exact hi.le.trans (sq_nonneg _)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_runningIndicator_le (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (ξ : Fin (tuning κ δ).calls → Ω) :
    runningIndicator (trackedUpdate p oracle center R G κ G0 δ s ξ) ≤ runningIndicator s := by
  classical
  unfold runningIndicator
  split_ifs with hn hs hs
  · rfl
  · exact (hs (trackedUpdate_running p oracle center R G κ G0 δ s ξ hn.1 hn.2)).elim
  · norm_num
  · rfl
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma trackedUpdate_inactive (p : Measure Ω) (oracle : E → Ω → E)
    (center xstar : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    (ξ : Fin (tuning κ δ).calls → Ω) (hs : ¬(s.2 = true ∧ s.1.2 = false)) :
    potential xstar (trackedUpdate p oracle center R G κ G0 δ s ξ) = 0 ∧
    runningIndicator (trackedUpdate p oracle center R G κ G0 δ s ξ) = 0 := by
  have hn : ¬((trackedUpdate p oracle center R G κ G0 δ s ξ).2 = true ∧
      (trackedUpdate p oracle center R G κ G0 δ s ξ).1.2 = false) :=
    fun h => hs (trackedUpdate_running p oracle center R G κ G0 δ s ξ h.1 h.2)
  simp only [potential, runningIndicator, hn, ↓reduceIte, and_self]

lemma tracked_running_integral (p : Measure Ω) [IsProbabilityMeasure p]
    (oracle : E → Ω → E) (ho : Measurable (Function.uncurry oracle)) {u v : Ω → E} (center x xstar : E)
     (hX : Measurable (oracle x)) (hXi : Integrable (oracle x) p)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p) (hsplit : ∀ᵐ ω ∂p, (oracle x) ω = u ω + v ω)
    {R G κ G0 δ gap : ℝ} (hR : 0 ≤ R) (hG : 0 < G)
    (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hgap : 0 ≤ gap) (hstar : ‖xstar - center‖ ≤ R)
    (hsub : gap ≤ ⟪x - xstar, ∫ ω, (oracle x) ω ∂p⟫)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, (oracle x) z ∂p‖)
    (hgBound : ‖∫ z, (oracle x) z ∂p‖ ≤ G0 + G * gap)
    (hSBound : (∫ ω, ‖(oracle x) ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * (G * gap) ^ 2)
    (hx : ‖x - center‖ ≤ R) :
    let c := tuning κ δ
    let next := trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
    (∫ ξ, potential xstar (next ξ) + (1 / (2048 * G ^ 2)) * runningIndicator (next ξ)
      ∂Measure.pi (fun _ : Fin c.calls => p)) ≤ ‖x - xstar‖ ^ 2 := by
  let c := tuning κ δ
  let N := c.rawCount + c.scales * c.scaleCalls
  let next := trackedUpdate p oracle center R G κ G0 δ ((x, false), true)
  let F := fun ξ => potential xstar (next ξ) + (1 / (2048 * G ^ 2)) * runningIndicator (next ξ)
  have hm : Measurable next := (measurable_trackedUpdate p ho center R G κ G0 δ).comp
    (measurable_const.prodMk measurable_id)
  have hb (ξ : Fin c.calls → Ω) : ‖(next ξ).1.1 - center‖ ≤ R :=
    trackedUpdate_mem_ball p oracle center R G κ G0 δ hR ((x, false), true) ξ hx
  have hi : Integrable F (Measure.pi fun _ : Fin c.calls => p) :=
    (integrable_potential center xstar hstar hm hb).add ((integrable_runningIndicator hm).const_mul _)
  have hp := (splitFinite_preserving p N c.updateCount).symm
  have hiF := hp.integrable_comp_of_integrable hi
  change (∫ ξ, F ξ ∂Measure.pi (fun _ : Fin c.calls => p)) ≤ _
  apply (hp.integral_comp' F).symm.trans_le
  apply (integral_prod _ hiF).trans_le
  have hcond (a : Fin N → Ω) := tracked_split_integral p oracle center x xstar hX hXi hu2 hsplit
    hR hG hκ hG0 hgap hstar hsub huBound hv hgBound hSBound a
  have h := integral_mono hiF.integral_prod_left (integrable_const (‖x - xstar‖ ^ 2)) hcond
  simpa only [integral_const, probReal_univ, one_smul] using h

section Iteration
variable {S : Type} [MeasurableSpace S]
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open OracleTemplate.ClippedExtragradient
lemma bounded_time_potential {advance : S → Ω → S}
    (ha : Measurable (Function.uncurry advance)) (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → S → ℝ) (hW : ∀ n, Measurable (W n)) {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (M : ℕ → ℝ)
    (hbound : ∀ n s, Inv s → ‖W n s‖ ≤ M n)
    (hstep : ∀ n s, Inv s → (∫ ω, W (n + 1) (advance s ω) ∂P) ≤ W n s)
    (k n : ℕ) (s : S) (hs : Inv s) :
    (∫ ξ : Fin k → Ω, W (n + k) (iterateSamples advance k s ξ)
      ∂Measure.pi (fun _ : Fin k => P)) ≤ W n s := by
  induction k generalizing n s with
  | zero => simp [iterateSamples, measureReal_def]
  | succ k ih =>
      let F : Ω × (Fin k → Ω) → ℝ := fun w =>
        W (n + (k + 1)) (iterateSamples advance k (advance s w.1) w.2)
      have hFm : Measurable F := ((hW _).comp (measurable_iterateSamples ha k)).comp
        ((ha.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
      have hFi : Integrable F (P.prod (Measure.pi fun _ : Fin k => P)) := by
        apply Integrable.of_bound hFm.aestronglyMeasurable (M (n + (k + 1)))
        exact Filter.Eventually.of_forall (fun w =>
          hbound _ _ (iterateSamples_invariant hinv k _ (hinv s hs w.1) w.2))
      have hAi : Integrable (fun ω => W (n + 1) (advance s ω)) P := by
        apply Integrable.of_bound (((hW _).comp ha).comp measurable_prodMk_left).aestronglyMeasurable (M (n + 1))
        exact Filter.Eventually.of_forall (fun ω => hbound _ _ (hinv s hs ω))
      have hcond (ω : Ω) : (∫ ξ : Fin k → Ω, F (ω, ξ)
          ∂Measure.pi (fun _ : Fin k => P)) ≤ W (n + 1) (advance s ω) := by
        simpa only [F, show n + (k + 1) = (n + 1) + k by omega] using ih (n + 1) _ (hinv s hs ω)
      have hh := (integral_mono hFi.integral_prod_left hAi hcond).trans (hstep n s hs)
      have hprod : (∫ w, F w ∂P.prod (Measure.pi fun _ : Fin k => P)) ≤ W n s := by
        rw [integral_prod F hFi]
        exact hh
      have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) 0).symm
      have he : (∫ ξ : Fin (k + 1) → Ω, W (n + (k + 1)) (iterateSamples advance (k + 1) s ξ)
          ∂Measure.pi (fun _ : Fin (k + 1) => P)) =
          ∫ w, F w ∂P.prod (Measure.pi fun _ : Fin k => P) := by
        rw [← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          iterateSamples, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      exact he.trans_le hprod
end Iteration

lemma trackedUpdate_failure_integral (p : Measure Ω) [IsProbabilityMeasure p] (oracle : E → Ω → E) (ho : Measurable (Function.uncurry oracle))
    (center : E) (R G κ G0 δ : ℝ) (s : (E × Bool) × Bool)
    {u v : Ω → E} (hX : Measurable (oracle s.1.1)) (hXi : Integrable (oracle s.1.1) p)
    (hu : Measurable u) (hui : Integrable u p) (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) p)
    (hsplit : ∀ᵐ ω ∂p, oracle s.1.1 ω = u ω + v ω) (hκ : 1 ≤ κ) (hG0 : 0 < G0) (hδ : 0 < δ)
    (huBound : (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2)
    (hv : ∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * κ * ‖∫ z, oracle s.1.1 z ∂p‖) :
    (∫ ξ : Fin (tuning κ δ).calls → Ω,
      failureIndicator (trackedUpdate p oracle center R G κ G0 δ s ξ)
      ∂Measure.pi (fun _ : Fin (tuning κ δ).calls => p)) ≤ failureIndicator s + δ := by
  classical
  let c := tuning κ δ
  let next := trackedUpdate p oracle center R G κ G0 δ s
  have hm : Measurable next := (measurable_trackedUpdate p ho center R G κ G0 δ).comp
    (measurable_const.prodMk measurable_id)
  by_cases hc : s.2 = true
  · have hb := trackedUpdate_failure p oracle center R G κ G0 δ s hc hX hXi hu hui hu2 hsplit hκ hG0 hδ huBound hv
    have he : MeasurableSet {ξ : Fin c.calls → Ω | (next ξ).2 = false} :=
      measurableSet_eq_fun hm.snd measurable_const
    have hi : (∫ ξ : Fin c.calls → Ω, failureIndicator (next ξ) ∂Measure.pi (fun _ : Fin c.calls => p)) =
        (Measure.pi (fun _ : Fin c.calls => p)).real {ξ | (next ξ).2 = false} := by
      simpa only [Set.indicator, Pi.one_apply, failureIndicator, Set.mem_ofPred_eq] using
        (integral_indicator_one (μ := Measure.pi (fun _ : Fin c.calls => p)) he)
    have ht := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal δ ≠ ⊤) hb
    rw [ENNReal.toReal_ofReal hδ.le] at ht
    change (∫ ξ : Fin c.calls → Ω, failureIndicator (next ξ) ∂Measure.pi (fun _ : Fin c.calls => p)) ≤ _
    rw [hi]
    simpa only [failureIndicator, hc, Bool.true_eq_false, ↓reduceIte, zero_add, Measure.real, next] using ht
  · have he (ξ : Fin c.calls → Ω) : failureIndicator (next ξ) = 1 := by
      have hn : (next ξ).2 = false := Bool.eq_false_iff.mpr (fun h => hc (trackedUpdate_clean p oracle center R G κ G0 δ s ξ h))
      simp [failureIndicator, hn]
    have hs : failureIndicator s = 1 := by simp [failureIndicator, Bool.eq_false_iff.mpr hc]
    change (∫ ξ : Fin c.calls → Ω, failureIndicator (next ξ) ∂Measure.pi (fun _ : Fin c.calls => p)) ≤ _
    simp only [he, hs, integral_const, probReal_univ, one_smul]
    linarith

section Survival
variable {S : Type} [MeasurableSpace S]
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open OracleTemplate.ClippedExtragradient
lemma bounded_survival_integral {advance : S → Ω → S}
    (ha : Measurable (Function.uncurry advance)) (P : Measure Ω) [IsProbabilityMeasure P]
    (V A : S → ℝ) (hV : Measurable V) (hA : Measurable A) {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) {M d : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ s, Inv s → 0 ≤ V s ∧ V s ≤ M)
    (hAbound : ∀ s, Inv s → 0 ≤ A s ∧ A s ≤ 1)
    (hmono : ∀ s, Inv s → ∀ ω, A (advance s ω) ≤ A s)
    (hstep : ∀ s, Inv s → (∫ ω, V (advance s ω) + d * A (advance s ω) ∂P) ≤ V s)
    (k : ℕ) (s : S) (hs : Inv s) :
    d * (k : ℝ) * (∫ ξ : Fin k → Ω, A (iterateSamples advance k s ξ)
      ∂Measure.pi (fun _ : Fin k => P)) ≤ V s := by
  let W := fun n : ℕ => fun s => V s + d * (n : ℝ) * A s
  have hW (n : ℕ) : Measurable (W n) := hV.add (hA.const_mul _)
  have hWB (n : ℕ) (s : S) (hs : Inv s) : ‖W n s‖ ≤ M + d * n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ W n s by have hv := (hbound s hs).1; have ha := (hAbound s hs).1; dsimp [W]; positivity)]
    dsimp [W]
    have h := mul_le_mul_of_nonneg_left (hAbound s hs).2 (mul_nonneg hd (Nat.cast_nonneg n))
    nlinarith [(hbound s hs).2]
  have hWS (n : ℕ) (s : S) (hs : Inv s) : (∫ ω, W (n + 1) (advance s ω) ∂P) ≤ W n s := by
    have hVi : Integrable (fun ω => V (advance s ω)) P := by
      apply Integrable.of_bound ((hV.comp ha).comp measurable_prodMk_left).aestronglyMeasurable M
      filter_upwards [] with ω
      change ‖V (advance s ω)‖ ≤ M
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound _ (hinv s hs ω)).1]
      exact (hbound _ (hinv s hs ω)).2
    have hAi : Integrable (fun ω => A (advance s ω)) P := by
      apply Integrable.of_bound ((hA.comp ha).comp measurable_prodMk_left).aestronglyMeasurable 1
      filter_upwards [] with ω
      change ‖A (advance s ω)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hAbound _ (hinv s hs ω)).1]
      exact (hAbound _ (hinv s hs ω)).2
    have hm := integral_mono hAi (integrable_const (A s)) (hmono s hs)
    simp only [integral_const, probReal_univ, one_smul] at hm
    have hh := hstep s hs
    rw [integral_add hVi (hAi.const_mul d), integral_const_mul] at hh
    have he : (fun ω => W (n + 1) (advance s ω)) =
        (fun ω => V (advance s ω) + (d * (n + 1 : ℕ)) * A (advance s ω)) := rfl
    rw [he, integral_add hVi (hAi.const_mul _), integral_const_mul]
    dsimp [W]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hm (mul_nonneg hd (Nat.cast_nonneg n))]
  have hw := bounded_time_potential ha P W hW hinv (fun n => M + d * n) hWB hWS k 0 s hs
  simp only [Nat.zero_add, W, Nat.cast_zero, mul_zero, zero_mul, add_zero] at hw
  have hstate : Measurable (fun ξ : Fin k → Ω => iterateSamples advance k s ξ) := (measurable_iterateSamples ha k).comp (measurable_const.prodMk measurable_id)
  have hAi : Integrable (fun ξ : Fin k → Ω => A (iterateSamples advance k s ξ)) (Measure.pi fun _ : Fin k => P) := by
    apply Integrable.of_bound (hA.comp hstate).aestronglyMeasurable 1
    filter_upwards [] with ξ
    have h := hAbound _ (iterateSamples_invariant hinv k s hs ξ)
    change ‖A (iterateSamples advance k s ξ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hWi : Integrable (fun ξ : Fin k → Ω => W k (iterateSamples advance k s ξ)) (Measure.pi fun _ : Fin k => P) := by
    apply Integrable.of_bound ((hW k).comp hstate).aestronglyMeasurable (M + d * k)
    exact Filter.Eventually.of_forall (fun ξ => hWB k _ (iterateSamples_invariant hinv k s hs ξ))
  have hh := integral_mono (hAi.const_mul (d * k)) hWi (fun ξ =>
    le_add_of_nonneg_left (hbound _ (iterateSamples_invariant hinv k s hs ξ)).1)
  rw [integral_const_mul] at hh
  exact hh.trans hw
end Survival

open LongTails.Setups.StochasticGeneralizedLipschitzConvex
omit [CompleteSpace E] in
lemma oracle_pilot_conditions (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (x : E) (hx : ‖x - center‖ ≤ R) :
    (‖∫ ω, oracle x ω ∂p‖ ≤ G0 + G * (f x - f xstar)) ∧
    ((∫ ω, ‖oracle x ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * (G * (f x - f xstar)) ^ 2) ∧
    ∃ u v : Ω → E, Measurable u ∧ Integrable u p ∧ Integrable (fun ω => ‖u ω‖ ^ 2) p ∧
      (∀ᵐ ω ∂p, oracle x ω = u ω + v ω) ∧ ((∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2) ∧
      (∀ᵐ ω ∂p, ‖v ω‖ ≤ 2 * (R * G) * ‖∫ z, oracle x z ∂p‖) := by
  have hgap : 0 ≤ f x - f xstar := sub_nonneg.mpr (hmin x)
  have hmul := mul_le_mul_of_nonneg_right hGG hgap
  have hm := oracle_moment_bounds ho hG0 x
  have hs := pow_le_pow_left₀ (mul_nonneg hG1 hgap) hmul 2
  refine ⟨hm.1.trans (by linarith), hm.2.2.trans (by linarith), ?_⟩
  obtain ⟨u, v, hu, _, he, hu2, hub, hv⟩ := ho.decomposition x
  have hui : Integrable u p := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hu2) hu.aestronglyMeasurable
    filter_upwards [] with ω
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖u ω‖ - 1)]
  refine ⟨u, v, hu, hui, hu2, he, hub, ?_⟩
  have hd := GeneralizedLipschitzConvex.gap_le_twice_radius f (∫ ω, oracle x ω ∂p) x center xstar
    hx (by simpa only [norm_sub_rev center xstar] using hstar) (ho.subgradient x xstar)
  have ht := mul_le_mul_of_nonneg_left hd hG
  filter_upwards [hv] with ω hω
  exact hω.trans (hmul.trans (by nlinarith))

lemma oracle_tracked_drift (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (s : (E × Bool) × Bool) (hx : ‖s.1.1 - center‖ ≤ R) :
    (∫ ξ : Fin (tuning (R * G) δ).calls → Ω,
      potential xstar (trackedUpdate p oracle center R G (R * G) G0 δ s ξ) +
      (1 / (2048 * G ^ 2)) * runningIndicator (trackedUpdate p oracle center R G (R * G) G0 δ s ξ)
      ∂Measure.pi (fun _ : Fin (tuning (R * G) δ).calls => p)) ≤ potential xstar s := by
  rcases s with ⟨⟨x, done⟩, clean⟩
  by_cases hs : clean = true ∧ done = false
  · rcases hs with ⟨rfl, rfl⟩
    obtain ⟨hg, hS, u, v, hu, hui, hu2, he, hub, hv⟩ :=
      oracle_pilot_conditions p ho hG0.le hG1 hG.le hGG hmin hstar x hx
    have hX : Measurable (oracle x) := ho.measurable.comp (measurable_const.prodMk measurable_id)
    have hsub : f x - f xstar ≤ ⟪x - xstar, ∫ ω, oracle x ω ∂p⟫ := by
      simpa only [real_inner_comm] using ho.subgradient x xstar
    simpa only [potential, and_self, ↓reduceIte] using
      tracked_running_integral p oracle ho.measurable center x xstar hX (ho.integrable x) hu2 he
        hR hG hκ hG0 (sub_nonneg.mpr (hmin x)) hstar hsub hub hv hg hS hx
  · have hz (ξ : Fin (tuning (R * G) δ).calls → Ω) :=
      trackedUpdate_inactive p oracle center xstar R G (R * G) G0 δ ((x, done), clean) ξ hs
    have hi : (∫ ξ : Fin (tuning (R * G) δ).calls → Ω,
        potential xstar (trackedUpdate p oracle center R G (R * G) G0 δ ((x, done), clean) ξ) +
        (1 / (2048 * G ^ 2)) * runningIndicator (trackedUpdate p oracle center R G (R * G) G0 δ ((x, done), clean) ξ)
        ∂Measure.pi (fun _ : Fin (tuning (R * G) δ).calls => p)) = 0 := by
      calc _ = ∫ _ : Fin (tuning (R * G) δ).calls → Ω, (0 : ℝ) ∂Measure.pi (fun _ : Fin (tuning (R * G) δ).calls => p) := by
             apply integral_congr_ae
             filter_upwards [] with ξ
             rw [(hz ξ).1, (hz ξ).2, mul_zero, add_zero]
           _ = 0 := integral_zero _ _
    rw [hi]
    exact potential_nonneg _ _

lemma oracle_tracked_failure (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hδ : 0 < δ) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (s : (E × Bool) × Bool) (hx : ‖s.1.1 - center‖ ≤ R) :
    (∫ ξ : Fin (tuning (R * G) δ).calls → Ω,
      failureIndicator (trackedUpdate p oracle center R G (R * G) G0 δ s ξ)
      ∂Measure.pi (fun _ : Fin (tuning (R * G) δ).calls => p)) ≤ failureIndicator s + δ := by
  obtain ⟨_, _, u, v, hu, hui, hu2, he, hub, hv⟩ :=
    oracle_pilot_conditions p ho hG0.le hG1 hG.le hGG hmin hstar s.1.1 hx
  have hX : Measurable (oracle s.1.1) := ho.measurable.comp (measurable_const.prodMk measurable_id)
  exact trackedUpdate_failure_integral p oracle ho.measurable center R G (R * G) G0 δ s hX
    (ho.integrable s.1.1) hu hui hu2 he hκ hG0 hδ hub hv

lemma oracle_tracked_finite (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hδ : 0 < δ) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (T : ℕ) :
    let c := tuning (R * G) δ
    let advance := trackedUpdate p oracle center R G (R * G) G0 δ
    let final := fun ξ : Fin T → (Fin c.calls → Ω) =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance T ((center, false), true) ξ
    (1 / (2048 * G ^ 2)) * (T : ℝ) *
        (∫ ξ, runningIndicator (final ξ) ∂Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin c.calls => p))) ≤ R ^ 2 ∧
      (∫ ξ, failureIndicator (final ξ) ∂Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin c.calls => p))) ≤ (T : ℝ) * δ := by
  let c := tuning (R * G) δ
  let advance := trackedUpdate p oracle center R G (R * G) G0 δ
  let Q := Measure.pi (fun _ : Fin c.calls => p)
  let Inv := fun s : (E × Bool) × Bool => ‖s.1.1 - center‖ ≤ R
  have hm : Measurable (Function.uncurry advance) := measurable_trackedUpdate p ho.measurable center R G (R * G) G0 δ
  have hinv (s) (hs : Inv s) (ξ : Fin c.calls → Ω) : Inv (advance s ξ) :=
    trackedUpdate_mem_ball p oracle center R G (R * G) G0 δ hR s ξ hs
  have hs : Inv ((center, false), true) := by simp [Inv, hR]
  have hV (s) (hs : Inv s) : 0 ≤ potential xstar s ∧ potential xstar s ≤ 4 * R ^ 2 :=
    ⟨potential_nonneg xstar s, potential_bound center xstar hstar s hs⟩
  have hA (s) (_hs : Inv s) : 0 ≤ runningIndicator s ∧ runningIndicator s ≤ 1 := runningIndicator_bounds s
  have hmono (s) (_hs : Inv s) (ξ : Fin c.calls → Ω) : runningIndicator (advance s ξ) ≤ runningIndicator s :=
    trackedUpdate_runningIndicator_le p oracle center R G (R * G) G0 δ s ξ
  have hstep (s) (hs : Inv s) : (∫ ξ, potential xstar (advance s ξ) +
      (1 / (2048 * G ^ 2)) * runningIndicator (advance s ξ) ∂Q) ≤ potential xstar s :=
    oracle_tracked_drift p ho hR hG0 hG1 hG hGG hκ hmin hstar s hs
  have hsurv := bounded_survival_integral hm Q (potential xstar) runningIndicator
    (measurable_potential xstar) measurable_runningIndicator hinv (by positivity : 0 ≤ 1 / (2048 * G ^ 2))
    hV hA hmono hstep T ((center, false), true) hs
  have hinit : potential xstar ((center, false), true) ≤ R ^ 2 := by
    simp only [potential, and_self, ↓reduceIte]
    rw [norm_sub_rev center xstar]
    exact pow_le_pow_left₀ (norm_nonneg _) hstar 2
  refine ⟨hsurv.trans hinit, ?_⟩
  have hfB (s) (_hs : Inv s) : ‖failureIndicator s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (failureIndicator_bounds s).1]
    exact (failureIndicator_bounds s).2
  have hfS (s) (hs : Inv s) : (∫ ξ, failureIndicator (advance s ξ) ∂Q) ≤ 1 * failureIndicator s + δ := by
    simpa only [one_mul] using oracle_tracked_failure p ho hG0 hδ hG1 hG hGG hκ hmin hstar s hs
  have hf := OracleTemplate.ClippedExtragradient.bounded_iterate_integral hm Q failureIndicator
    measurable_failureIndicator hinv hfB (by norm_num : (0 : ℝ) ≤ 1) hfS T ((center, false), true) hs
  simpa only [failureIndicator, Bool.true_eq_false, ↓reduceIte, one_pow, mul_zero, zero_add,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, mul_comm δ] using hf

omit [CompleteSpace E] in
lemma oracle_good_terminal (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (x : E) (hx : ‖x - center‖ ≤ R) (data : ℕ → E)
    (hg : pilotGood p (oracle x) (R * G) G0 δ data)
    (ht : blockDecision (tuning (R * G) δ) (R * G) G0 data = .terminal) :
    f x - f xstar ≤ 128 * R * G0 := by
  obtain ⟨hgm, hS, u, v, _, _, hu2, he, hub, hv⟩ :=
    oracle_pilot_conditions p ho hG0.le hG1 hG.le hGG hmin hstar x hx
  have hX : Measurable (oracle x) := ho.measurable.comp (measurable_const.prodMk measurable_id)
  have hdecision := pilotGood_decision p hX (ho.integrable x) hu2 he hκ hG0
    (mul_nonneg hG.le (sub_nonneg.mpr (hmin x))) hub hv hgm hS data hg
  dsimp only at hdecision
  rw [ht] at hdecision
  have hd := GeneralizedLipschitzConvex.gap_le_twice_radius f (∫ ω, oracle x ω ∂p) x center xstar
    hx (by simpa only [norm_sub_rev center xstar] using hstar) (ho.subgradient x xstar)
  have hb := mul_le_mul_of_nonneg_left hdecision (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)
  nlinarith

omit [CompleteSpace E] in
lemma oracle_tracked_success (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (s : (E × Bool) × Bool) (hx : ‖s.1.1 - center‖ ≤ R)
    (hs : s.2 = true → s.1.2 = true → f s.1.1 - f xstar ≤ 128 * R * G0)
    (ξ : Fin (tuning (R * G) δ).calls → Ω)
    (hn : (trackedUpdate p oracle center R G (R * G) G0 δ s ξ).2 = true)
    (hd : (trackedUpdate p oracle center R G (R * G) G0 δ s ξ).1.2 = true) :
    f (trackedUpdate p oracle center R G (R * G) G0 δ s ξ).1.1 - f xstar ≤ 128 * R * G0 := by
  classical
  by_cases hf : s.1.2 = true
  · have he := trackedUpdate_frozen p oracle center R G (R * G) G0 δ s ξ hf
    rw [he]
    exact hs (trackedUpdate_clean p oracle center R G (R * G) G0 δ s ξ hn) hf
  · have hf' : s.1.2 = false := Bool.eq_false_iff.mpr hf
    let c := tuning (R * G) δ
    let data := fun i => if h : i < c.calls then oracle s.1.1 (ξ ⟨i, h⟩) else 0
    have hg : pilotGood p (oracle s.1.1) (R * G) G0 δ data := by
      dsimp only [trackedUpdate] at hn
      split_ifs at hn with hh
      · exact hh.2.resolve_left hf
    have hd' : (blockUpdate c center R G G0 (R * G) s.1 data).2 = true := hd
    obtain ⟨hgm, hS, u, v, _, _, hu2, he, hub, hv⟩ :=
      oracle_pilot_conditions p ho hG0.le hG1 hG.le hGG hmin hstar s.1.1 hx
    have hX : Measurable (oracle s.1.1) := ho.measurable.comp (measurable_const.prodMk measurable_id)
    have hdecision := pilotGood_decision p hX (ho.integrable s.1.1) hu2 he hκ hG0
      (mul_nonneg hG.le (sub_nonneg.mpr (hmin s.1.1))) hub hv hgm hS data hg
    dsimp only at hdecision
    cases hdec : blockDecision c (R * G) G0 data with
    | exhausted => rw [hdec] at hdecision; exact hdecision.elim
    | update j => simp only [blockUpdate, hf', Bool.false_eq_true, ↓reduceIte, hdec] at hd'
    | terminal =>
      have hpoint : (trackedUpdate p oracle center R G (R * G) G0 δ s ξ).1.1 = s.1.1 := by
        rw [trackedUpdate_first]
        change (blockUpdate c center R G G0 (R * G) s.1 data).1 = s.1.1
        simp only [blockUpdate, hf', Bool.false_eq_true, ↓reduceIte, hdec]
      rw [hpoint]
      exact oracle_good_terminal p ho hR hG0 hG1 hG hGG hκ hmin hstar s.1.1 hx data hg hdec

omit [CompleteSpace E] in
lemma oracle_tracked_finite_invariant (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (T : ℕ)
    (ξ : Fin T → (Fin (tuning (R * G) δ).calls → Ω)) :
    let final := OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (trackedUpdate p oracle center R G (R * G) G0 δ) T ((center, false), true) ξ
    ‖final.1.1 - center‖ ≤ R ∧
      (final.2 = true → final.1.2 = true → f final.1.1 - f xstar ≤ 128 * R * G0) := by
  let Inv := fun s : (E × Bool) × Bool => ‖s.1.1 - center‖ ≤ R ∧
    (s.2 = true → s.1.2 = true → f s.1.1 - f xstar ≤ 128 * R * G0)
  apply OracleTemplate.ClippedExtragradient.iterateSamples_invariant (Inv := Inv)
  · intro s hs η
    exact ⟨trackedUpdate_mem_ball p oracle center R G (R * G) G0 δ hR s η hs.1,
      oracle_tracked_success p ho hR hG0 hG1 hG hGG hκ hmin hstar s hs.1 hs.2 η⟩
  · simp [Inv, hR]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma tracked_bad_event {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Ω → (E × Bool) × Bool} (hm : Measurable s) {f : E → ℝ} (hf : Measurable f)
    (xstar : E) (F : ℝ) (hs : ∀ ω, (s ω).2 = true → (s ω).1.2 = true → f (s ω).1.1 - f xstar ≤ F) :
    P.real {ω | F < f (s ω).1.1 - f xstar} ≤
      (∫ ω, failureIndicator (s ω) ∂P) + (∫ ω, runningIndicator (s ω) ∂P) := by
  classical
  let B := {ω | F < f (s ω).1.1 - f xstar}
  have hB : MeasurableSet B := measurableSet_lt measurable_const ((hf.comp hm.fst.fst).sub measurable_const)
  have hi : Integrable (B.indicator (fun _ => (1 : ℝ))) P := (integrable_const (1 : ℝ)).indicator hB
  have hfail := integrable_failureIndicator hm (P := P)
  have hrun := integrable_runningIndicator hm (P := P)
  have hpoint (ω : Ω) : B.indicator (fun _ => (1 : ℝ)) ω ≤ failureIndicator (s ω) + runningIndicator (s ω) := by
    by_cases hb : ω ∈ B
    · rw [Set.indicator_of_mem hb]
      by_cases hc : (s ω).2 = true
      · by_cases hd : (s ω).1.2 = true
        · exact (not_lt_of_ge (hs ω hc hd) hb).elim
        · have hd' := Bool.eq_false_iff.mpr hd
          simp [failureIndicator, runningIndicator, hc, hd']
      · have hc' := Bool.eq_false_iff.mpr hc
        simp [failureIndicator, runningIndicator, hc']
    · rw [Set.indicator_of_notMem hb]
      exact add_nonneg (failureIndicator_bounds _).1 (runningIndicator_bounds _).1
  have h := integral_mono hi (hfail.add hrun) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hfail hrun] at h
  have he : (∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂P) = P.real B := integral_indicator_one hB
  rw [he] at h
  exact h

lemma oracle_tracked_finite_gap (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (hf : Measurable f) (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hδ : 0 < δ) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (T : ℕ) (hT : 0 < T) :
    let c := tuning (R * G) δ
    let final := fun ξ : Fin T → (Fin c.calls → Ω) =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
        (trackedUpdate p oracle center R G (R * G) G0 δ) T ((center, false), true) ξ
    (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin c.calls => p)))
      {ξ | 128 * R * G0 < f (final ξ).1.1 - f xstar} ≤
      ENNReal.ofReal (2048 * (R * G) ^ 2 / T + T * δ) := by
  let c := tuning (R * G) δ
  let advance := trackedUpdate p oracle center R G (R * G) G0 δ
  let Q := Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin c.calls => p))
  let final := fun ξ : Fin T → (Fin c.calls → Ω) =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance T ((center, false), true) ξ
  have hm : Measurable final := (OracleTemplate.ClippedExtragradient.measurable_iterateSamples
    (measurable_trackedUpdate p ho.measurable center R G (R * G) G0 δ) T).comp
      (measurable_const.prodMk measurable_id)
  have hi (ξ : Fin T → (Fin c.calls → Ω)) := oracle_tracked_finite_invariant p ho hR hG0 hG1 hG hGG hκ hmin hstar T ξ
  have hb := tracked_bad_event (P := Q) hm hf xstar (128 * R * G0) (fun ξ => (hi ξ).2)
  have ht := oracle_tracked_finite p ho hR hG0 hδ hG1 hG hGG hκ hmin hstar T
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hc : 0 < (1 / (2048 * G ^ 2)) * (T : ℝ) := by positivity
  have hsurv : (∫ ξ, runningIndicator (final ξ) ∂Q) ≤ R ^ 2 / ((1 / (2048 * G ^ 2)) * (T : ℝ)) := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using ht.1
  have he : R ^ 2 / ((1 / (2048 * G ^ 2)) * (T : ℝ)) = 2048 * (R * G) ^ 2 / T := by
    field_simp
  rw [he] at hsurv
  have hr : Q.real {ξ | 128 * R * G0 < f (final ξ).1.1 - f xstar} ≤ 2048 * (R * G) ^ 2 / T + T * δ := by
    have hfail : (∫ ξ, failureIndicator (final ξ) ∂Q) ≤ (T : ℝ) * δ := ht.2
    linarith
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2048 * (R * G) ^ 2 / (T : ℝ) + T * δ)]
  exact hr

open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
lemma iterateSamples_eq_advance {S Ω : Type} (update : S → Ω → S) (samples : ℕ → Ω)
    (T k : ℕ) (s : S) :
    iterateSamples update T s (fun i => samples (k + i)) =
      OracleTemplate.StochasticGradient.advance (fun k s => update s (samples k)) T k s := by
  induction T generalizing k s with
  | zero => rfl
  | succ T ih =>
    simp only [iterateSamples, Fin.val_zero, Nat.add_zero, Fin.val_succ,
      OracleTemplate.StochasticGradient.advance]
    convert ih (k + 1) (update s (samples k)) using 1
    congr 1
    funext i
    congr 1
    omega
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma tracked_iterate_first (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (T : ℕ) (s : (E × Bool) × Bool)
    (ξ : Fin T → (Fin (tuning κ δ).calls → Ω)) :
    (iterateSamples (trackedUpdate p oracle center R G κ G0 δ) T s ξ).1 =
      iterateSamples (fun s samples => blockUpdate (tuning κ δ) center R G G0 κ s
        (fun i => if h : i < (tuning κ δ).calls then oracle s.1 (samples ⟨i, h⟩) else 0)) T s.1 ξ := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    simp only [iterateSamples]
    rw [ih, trackedUpdate_first]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma burninOutput_eq_tracked (p : Measure Ω) (oracle : E → Ω → E)
    (center : E) (R G κ G0 δ : ℝ) (hc : 0 < (tuning κ δ).calls)
    (P : ProbabilityMeasure (ℕ → Ω)) (T : ℕ) (ξ : ℕ → Ω) :
    burninOutput (tuning κ δ) hc center R G G0 κ T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
      (iterateSamples (trackedUpdate p oracle center R G κ G0 δ) T ((center, false), true)
        (fun k i => ξ (k * (tuning κ δ).calls + i))).1.1 := by
  rw [execute_burnin, tracked_iterate_first]
  have h := iterateSamples_eq_advance
    (fun s samples => blockUpdate (tuning κ δ) center R G G0 κ s
      (fun i => if h : i < (tuning κ δ).calls then oracle s.1 (samples ⟨i, h⟩) else 0))
    (fun k => fun i : Fin (tuning κ δ).calls => ξ (k * (tuning κ δ).calls + i)) T 0 (center, false)
  simp only [Nat.zero_add] at h
  exact congrArg Prod.fst h.symm

lemma finite_pilot_blocks_law (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P) (n T : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun k : Fin T => fun i : Fin n => ξ (k * n + i))
      P (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin n => p))) := by
  have hi := OracleTemplate.FiniteVariance.infinite_block_law p P h_samples.independent h_samples.marginal n
  have hp := OracleTemplate.StochasticGeneralized.prefix_preserving (Measure.pi (fun _ : Fin n => p)) T
  exact hp.comp hi
lemma burninOutput_confidence (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {R G G0 G1 δ : ℝ}
    (hf : Measurable f) (ho : IsOracle p f xstar oracle G0 G1) (hR : 0 ≤ R) (hG0 : 0 < G0) (hδ : 0 < δ) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hκ : 1 ≤ R * G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ R) (T : ℕ) (hT : 0 < T)
    (P : ProbabilityMeasure (ℕ → Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p (P : Measure _)) (hc : 0 < (tuning (R * G) δ).calls) :
    (P : Measure _) {ξ | 128 * R * G0 <
      f (burninOutput (tuning (R * G) δ) hc center R G G0 (R * G) T
        { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ) - f xstar} ≤
      ENNReal.ofReal (2048 * (R * G) ^ 2 / T + T * δ) := by
  let c := tuning (R * G) δ
  let Q := Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin c.calls => p))
  let final := fun ξ : Fin T → (Fin c.calls → Ω) =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
        (trackedUpdate p oracle center R G (R * G) G0 δ) T ((center, false), true) ξ
  let blocks := fun ξ : ℕ → Ω => fun k : Fin T => fun i : Fin c.calls => ξ (k * c.calls + i)
  have hp : MeasurePreserving blocks (P : Measure _) Q :=
    finite_pilot_blocks_law p (P : Measure _) h_samples c.calls T
  have hm : Measurable final := (OracleTemplate.ClippedExtragradient.measurable_iterateSamples
    (measurable_trackedUpdate p ho.measurable center R G (R * G) G0 δ) T).comp
      (measurable_const.prodMk measurable_id)
  have hbad : MeasurableSet {ξ | 128 * R * G0 < f (final ξ).1.1 - f xstar} :=
    measurableSet_lt measurable_const ((hf.comp hm.fst.fst).sub measurable_const)
  have he (ξ : ℕ → Ω) : burninOutput c hc center R G G0 (R * G) T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ = (final (blocks ξ)).1.1 :=
    burninOutput_eq_tracked p oracle center R G (R * G) G0 δ hc P T ξ
  have hset : {ξ | 128 * R * G0 < f (burninOutput c hc center R G G0 (R * G) T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ) - f xstar} =
      blocks ⁻¹' {ξ | 128 * R * G0 < f (final ξ).1.1 - f xstar} := by
    ext ξ
    change (128 * R * G0 < f (burninOutput c hc center R G G0 (R * G) T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ) - f xstar) ↔ _
    rw [he]
    rfl
  change (P : Measure _) {ξ | 128 * R * G0 < f (burninOutput c hc center R G G0 (R * G) T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ) - f xstar} ≤ _
  rw [hset]
  rw [hp.measure_preimage hbad.nullMeasurableSet]
  exact oracle_tracked_finite_gap p hf ho hR hG0 hδ hG1 hG hGG hκ hmin hstar T hT

lemma burnin_horizon_bound {κ : ℝ} (hκ : 1 ≤ κ) :
    let T := ⌈204800 * κ ^ 2⌉₊
    0 < T ∧ 0 < 1 / (100 * (T : ℝ)) ∧
      2048 * κ ^ 2 / T + T * (1 / (100 * (T : ℝ))) ≤ (1 / 50 : ℝ) := by
  let T := ⌈204800 * κ ^ 2⌉₊
  have hκp : 0 < κ := by linarith
  have hceil : 204800 * κ ^ 2 ≤ (T : ℝ) := Nat.le_ceil _
  have hTp : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hceil
  have hT : 0 < T := by exact_mod_cast hTp
  refine ⟨hT, by positivity, ?_⟩
  have hfirst : 2048 * κ ^ 2 / T ≤ (1 / 100 : ℝ) := by
    apply (div_le_iff₀ hTp).mpr
    linarith
  have hsecond : (T : ℝ) * (1 / (100 * (T : ℝ))) = (1 / 100 : ℝ) := by
    field_simp
  change 2048 * κ ^ 2 / T + T * (1 / (100 * (T : ℝ))) ≤ (1 / 50 : ℝ)
  rw [hsecond]
  linarith

end LongTails.Proofs.GeneralizedLipschitzBurnin
