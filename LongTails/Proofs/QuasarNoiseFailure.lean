import LongTails.Proofs.QuasarHardAdmissible
import LongTails.Proofs.QuasarHardProfiles
import LongTails.Proofs.TrajectoryExecution

open MeasureTheory Metric Classical
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.QuasarNoiseFailure

open LongTails.Setups HighDimensionalConstrainedQuasar OracleTemplate
open OracleTemplate.LocalHiddenConvex QuasarCoinLaw QuasarHardAdmissible QuasarHardProfiles

variable {d : ℕ}

noncomputable def offset (D : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (x - x0) i - D / 4

noncomputable def wellObjective (D ε γ : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ε * well (2 * γ / 3) (offset D x0 i x / (D / 16))

noncomputable def wellGradient (D ε γ : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (2 * ε / (D / 16) * wellSlope (2 * γ / 3) (offset D x0 i x / (D / 16))) •
    EuclideanSpace.single i (1 : ℝ)

noncomputable def wellCenter (D : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  x0 + (D / 4) • EuclideanSpace.single i (1 : ℝ)

lemma offset_apply_center (D : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : (x - wellCenter D x0 i) i = offset D x0 i x := by
  simp [wellCenter, offset]
  ring

lemma wellObjective_gradient (D ε γ : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (wellObjective D ε γ x0 i) (wellGradient D ε γ x0 i x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hproj (v : EuclideanSpace ℝ (Fin d)) :
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) v = v i := rfl
  have hp : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => offset D x0 i w / (D / 16))
      ((1 / (D / 16)) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
    have := ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt (x := x)).sub_const
      (x0 i + D / 4)
    convert this.const_smul (1 / (D / 16)) using 1
    funext w
    simp only [offset, Pi.smul_apply, hproj, smul_eq_mul, PiLp.sub_apply]
    ring
  have hc := (well_hasDerivAt (2 * γ / 3) (offset D x0 i x / (D / 16))).comp_hasFDerivAt x hp
  have hm := hc.const_mul (2 * ε)
  convert hm using 1
  · funext v
    rfl
  ext v
  rw [InnerProductSpace.toDual_apply_apply]
  simp only [wellGradient, inner_smul_left, EuclideanSpace.inner_single_left, smul_apply,
    smul_eq_mul, hproj, RCLike.conj_to_real, map_one, one_mul]
  ring

lemma wellGradient_lipschitz (D ε γ : ℝ) (hD : 0 < D) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖wellGradient D ε γ x0 i x - wellGradient D ε γ x0 i y‖ ≤ 2048 * ε / D ^ 2 * ‖x - y‖ := by
  have hβ : 0 ≤ 2 * γ / 3 := by positivity
  have hβ1 : 2 * γ / 3 ≤ 1 := by linarith
  have hsingle : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  unfold wellGradient
  rw [← sub_smul, norm_smul, hsingle, mul_one, Real.norm_eq_abs,
    ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε / (D / 16))]
  have hl := wellSlope_lipschitz hβ hβ1 (offset D x0 i x / (D / 16)) (offset D x0 i y / (D / 16))
  have he : offset D x0 i x / (D / 16) - offset D x0 i y / (D / 16) = (x i - y i) / (D / 16) := by
    simp only [offset, PiLp.sub_apply]; ring
  rw [he, abs_div, abs_of_pos (by positivity : 0 < D / 16)] at hl
  have hc : |x i - y i| ≤ ‖x - y‖ := by
    have := PiLp.norm_apply_le (p := 2) (x - y) i
    simpa using this
  calc 2 * ε / (D / 16) * |wellSlope (2 * γ / 3) (offset D x0 i x / (D / 16)) -
        wellSlope (2 * γ / 3) (offset D x0 i y / (D / 16))| ≤
        2 * ε / (D / 16) * (4 * (|x i - y i| / (D / 16))) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 2048 * ε / D ^ 2 * |x i - y i| := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

lemma wellObjective_center (D ε γ : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    wellObjective D ε γ x0 i (wellCenter D x0 i) = 0 := by
  have h : offset D x0 i (wellCenter D x0 i) = 0 := by simp [offset, wellCenter]
  simp [wellObjective, h, well_zero]

lemma wellObjective_nonneg (D ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (x0 : EuclideanSpace ℝ (Fin d))
    (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ wellObjective D ε γ x0 i x :=
  mul_nonneg (by positivity) (well_nonneg (by positivity) _)

lemma wellObjective_quasar (D ε γ : ℝ) (hD : 0 < D) (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    γ * (wellObjective D ε γ x0 i x - wellObjective D ε γ x0 i (wellCenter D x0 i)) ≤
      ⟪wellGradient D ε γ x0 i x, x - wellCenter D x0 i⟫ := by
  rw [wellObjective_center D ε γ, sub_zero]
  unfold wellGradient wellObjective
  rw [inner_smul_left, EuclideanSpace.inner_single_left, offset_apply_center]
  simp only [RCLike.conj_to_real, map_one, one_mul]
  have hq := well_quasar hγ hγ1 (offset D x0 i x / (D / 16))
  have he : 2 * ε / (D / 16) * wellSlope (2 * γ / 3) (offset D x0 i x / (D / 16)) *
      offset D x0 i x = 2 * ε * (wellSlope (2 * γ / 3) (offset D x0 i x / (D / 16)) *
        (offset D x0 i x / (D / 16))) := by field_simp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * ε)]

lemma wellGradient_far (D ε γ : ℝ) (hD : 0 < D) (hε : 0 ≤ ε) (hγ : 0 ≤ γ)
    (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) (x : EuclideanSpace ℝ (Fin d))
    (h : D / 8 ≤ |offset D x0 i x|) :
    ‖wellGradient D ε γ x0 i x‖ = 64 * γ * ε / (3 * D) := by
  unfold wellGradient
  have hu : 2 ≤ |offset D x0 i x / (D / 16)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < D / 16), le_div_iff₀ (by positivity)]
    linarith
  have hsingle : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  rw [norm_smul, hsingle, mul_one, Real.norm_eq_abs, abs_mul,
    wellSlope_far hu, abs_of_nonneg (by positivity : 0 ≤ 2 * ε / (D / 16)),
    abs_of_nonneg (by positivity : 0 ≤ 2 * γ / 3)]
  field_simp
  ring

lemma success_near (D ε γ : ℝ) (hD : 0 < D) (hε : 0 < ε) (hγ : 0 ≤ γ)
    (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) (x : EuclideanSpace ℝ (Fin d))
    (h : wellObjective D ε γ x0 i x ≤ ε) : |offset D x0 i x| < D / 8 := by
  by_contra hc
  push Not at hc
  have hu : 2 ≤ |offset D x0 i x / (D / 16)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < D / 16), le_div_iff₀ (by positivity)]
    linarith
  have := well_far (β := 2 * γ / 3) (by positivity) hu
  unfold wellObjective at h
  nlinarith

lemma near_count (D : ℝ) (hD : 0 < D) {M : ℕ} (e : Fin M ↪ Fin d) (x0 x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x - x0‖ ≤ D / 2) :
    (Finset.univ.filter (fun j : Fin M => |offset D x0 (e j) x| < D / 8)).card ≤ 16 := by
  set s := Finset.univ.filter (fun j : Fin M => |offset D x0 (e j) x| < D / 8) with hs
  have hlow : ∀ j ∈ s, D / 8 < (x - x0) (e j) := by
    intro j hj
    rw [hs, Finset.mem_filter] at hj
    have := neg_abs_le (offset D x0 (e j) x)
    simp only [offset] at this hj
    linarith [hj.2]
  have hsum : (s.card : ℝ) * (D / 8) ^ 2 ≤ ‖x - x0‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc (s.card : ℝ) * (D / 8) ^ 2 = ∑ _ ∈ s, (D / 8) ^ 2 := by simp
      _ ≤ ∑ j ∈ s, (x - x0) (e j) ^ 2 := Finset.sum_le_sum (fun j hj => by
          have := hlow j hj
          nlinarith)
      _ = ∑ m ∈ s.map e, (x - x0) m ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  have hx2 : ‖x - x0‖ ^ 2 ≤ (D / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hpos : 0 < (D / 8) ^ 2 := by positivity
  have h3 : (s.card : ℝ) * (D / 8) ^ 2 ≤ 16 * (D / 8) ^ 2 := by nlinarith
  have h4 : (s.card : ℝ) ≤ 16 := le_of_mul_le_mul_right h3 hpos
  exact_mod_cast h4

noncomputable def noisyGradient (p : Params) {M : ℕ} (e : Fin M ↪ Fin p.d) (ν : ℝ) (j : Fin M)
    (x : EuclideanSpace ℝ (Fin p.d)) (ω : Bool) : EuclideanSpace ℝ (Fin p.d) :=
  if ‖x - p.x0‖ ≤ p.D / 2 then
    (if |offset p.D p.x0 (e j) x| < p.D / 8 then wellGradient p.D p.ε p.γ p.x0 (e j) x
      else if ω then (1 / ν) • wellGradient p.D p.ε p.γ p.x0 (e j) x else 0)
  else 0

lemma wellGradient_continuous (D ε γ : ℝ) (hD : 0 < D) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) : Continuous (wellGradient D ε γ x0 i) := by
  apply LipschitzWith.continuous (K := ⟨2048 * ε / D ^ 2, by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  exact wellGradient_lipschitz D ε γ hD hε hγ hγ1 x0 i x y

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma noisyGradient_measurable (p : Params) (hD : 0 < p.D) (hε : 0 ≤ p.ε) (hγ : 0 ≤ p.γ)
    (hγ1 : p.γ ≤ 1) {M : ℕ} (e : Fin M ↪ Fin p.d) (ν : ℝ) (j : Fin M) :
    Measurable (Function.uncurry (noisyGradient p e ν j)) := by
  have hc := wellGradient_continuous p.D p.ε p.γ hD hε hγ hγ1 p.x0 (e j)
  have hoff : Continuous (fun x : EuclideanSpace ℝ (Fin p.d) => offset p.D p.x0 (e j) x) := by
    unfold offset; fun_prop
  have hball : MeasurableSet {z : EuclideanSpace ℝ (Fin p.d) × Bool | ‖z.1 - p.x0‖ ≤ p.D / 2} :=
    measurableSet_le ((measurable_fst.sub_const p.x0).norm) measurable_const
  have hnear : MeasurableSet {z : EuclideanSpace ℝ (Fin p.d) × Bool |
      |offset p.D p.x0 (e j) z.1| < p.D / 8} :=
    measurableSet_lt ((hoff.comp continuous_fst).abs.measurable) measurable_const
  have hω : MeasurableSet {z : EuclideanSpace ℝ (Fin p.d) × Bool | z.2 = true} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hg : Measurable (fun z : EuclideanSpace ℝ (Fin p.d) × Bool =>
      wellGradient p.D p.ε p.γ p.x0 (e j) z.1) := hc.measurable.comp measurable_fst
  have hg' : Measurable (fun z : EuclideanSpace ℝ (Fin p.d) × Bool =>
      (1 / ν) • wellGradient p.D p.ε p.γ p.x0 (e j) z.1) := hg.const_smul (1 / ν)
  change Measurable (fun z : EuclideanSpace ℝ (Fin p.d) × Bool => noisyGradient p e ν j z.1 z.2)
  unfold noisyGradient
  exact Measurable.ite hball (Measurable.ite hnear hg (Measurable.ite hω hg'
    measurable_const)) measurable_const

noncomputable def noiseLevel (p : Params) : ℝ := (64 * p.γ * p.ε / (3 * p.D * p.σ)) ^ 2

lemma noiseLevel_pos (p : Params) (hD : 0 < p.D) (hε : 0 < p.ε) (hγ : 0 < p.γ) (hσ : 0 < p.σ) :
    0 < noiseLevel p := by unfold noiseLevel; positivity

lemma noiseLevel_le (p : Params) (hD : 0 < p.D) (hε : 0 < p.ε) (hγ : 0 < p.γ) (hσ : 0 < p.σ)
    (hband : 64 * p.γ * p.ε ≤ p.σ * p.D) : noiseLevel p ≤ 1 / 9 := by
  unfold noiseLevel
  have hq : 64 * p.γ * p.ε / (3 * p.D * p.σ) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h0 : 0 ≤ 64 * p.γ * p.ε / (3 * p.D * p.σ) := by positivity
  nlinarith

noncomputable def noiseInstance (p : Params) {M : ℕ} (e : Fin M ↪ Fin p.d) (j : Fin M) :
    StochasticConstrainedQuasar.Instance p.toStochastic :=
  ballInstance p (wellObjective p.D p.ε p.γ p.x0 (e j)) (wellCenter p.D p.x0 (e j))

noncomputable def noiseOracle (p : Params) {M : ℕ} (e : Fin M ↪ Fin p.d) (hν0 : 0 ≤ noiseLevel p)
    (hν1 : noiseLevel p ≤ 1) (j : Fin M) :
    Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) 2 :=
  ballOracle p hν0 hν1 (noisyGradient p e (noiseLevel p) j)

lemma wellCenter_dist (D : ℝ) (hD : 0 < D) (x0 : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ‖wellCenter D x0 i - x0‖ = D / 4 := by
  have hsingle : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  rw [wellCenter, add_sub_cancel_left, norm_smul, hsingle, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  ring

lemma noise_admissible (p : Params) (hD : 0 < p.D) (hε : 0 < p.ε) (hγ : 0 < p.γ)
    (hγ1 : p.γ ≤ 1) (hσ : 0 < p.σ) (hband : 64 * p.γ * p.ε ≤ p.σ * p.D)
    (hLD : 2048 * p.ε ≤ p.L * p.D ^ 2) {M : ℕ} (e : Fin M ↪ Fin p.d) (j : Fin M) :
    spec.admissible p (noiseInstance p e j)
      (noiseOracle p e (noiseLevel_pos p hD hε hγ hσ).le
        ((noiseLevel_le p hD hε hγ hσ hband).trans (by norm_num)) j) := by
  have hν := noiseLevel_pos p hD hε hγ hσ
  apply ball_admissible p hD _ _ _ (wellGradient p.D p.ε p.γ p.x0 (e j))
  · rw [wellCenter_dist p.D hD]; linarith
  · exact wellObjective_gradient p.D p.ε p.γ p.x0 (e j)
  · intro x y
    have h := wellGradient_lipschitz p.D p.ε p.γ hD hε.le hγ.le hγ1 p.x0 (e j) x y
    have hc : 2048 * p.ε / p.D ^ 2 ≤ p.L := by rw [div_le_iff₀ (by positivity)]; linarith
    exact h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  · intro x
    rw [wellObjective_center]
    exact wellObjective_nonneg p.D p.ε p.γ hε.le hγ.le p.x0 (e j) x
  · intro x
    exact wellObjective_quasar p.D p.ε p.γ hD hε.le hγ hγ1 p.x0 (e j) x
  · exact noisyGradient_measurable p hD hε.le hγ.le hγ1 e _ j
  · intro x hx
    have hx' : ‖x - p.x0‖ ≤ p.D / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    unfold noisyGradient
    simp only [hx', ↓reduceIte, Bool.false_eq_true]
    split_ifs
    · rw [← add_smul]; simp
    · rw [smul_smul, mul_one_div_cancel hν.ne', one_smul, smul_zero, add_zero]
  · intro x hx
    have hx' : ‖x - p.x0‖ ≤ p.D / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    unfold noisyGradient
    simp only [hx', ↓reduceIte, Bool.false_eq_true]
    split_ifs with hn
    · simp; positivity
    · push Not at hn
      have hg := wellGradient_far p.D p.ε p.γ hD hε.le hγ.le p.x0 (e j) x hn
      set G := wellGradient p.D p.ε p.γ p.x0 (e j) x
      have h1 : (1 / noiseLevel p) • G - G = (1 / noiseLevel p - 1) • G := by
        rw [sub_smul, one_smul]
      rw [h1, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hg]
      have hνd : noiseLevel p = (64 * p.γ * p.ε / (3 * p.D)) ^ 2 / p.σ ^ 2 := by
        unfold noiseLevel; field_simp
      have hs : (64 * p.γ * p.ε / (3 * p.D)) ^ 2 = noiseLevel p * p.σ ^ 2 := by
        rw [hνd]; field_simp
      rw [hs]
      have hν1 : noiseLevel p ≤ 1 := (noiseLevel_le p hD hε hγ hσ hband).trans (by norm_num)
      have he : noiseLevel p * ((1 / noiseLevel p - 1) ^ 2 * (noiseLevel p * p.σ ^ 2)) +
          (1 - noiseLevel p) * (noiseLevel p * p.σ ^ 2) = (1 - noiseLevel p) * p.σ ^ 2 := by
        field_simp; ring
      rw [he]
      nlinarith [sq_nonneg p.σ]

noncomputable def silentReply (p : Params) (q : Fin 2 × EuclideanSpace ℝ (Fin p.d)) :
    EuclideanSpace ℝ (Fin p.d) :=
  if q.1 = 0 then 0 else ballProj p.x0 (p.D / 2) q.2

noncomputable def nearSet (p : Params) {M : ℕ} (e : Fin M ↪ Fin p.d)
    (x : EuclideanSpace ℝ (Fin p.d)) : Finset (Fin M) :=
  if ‖x - p.x0‖ ≤ p.D / 2 then
    Finset.univ.filter (fun j : Fin M => |offset p.D p.x0 (e j) x| < p.D / 8) else ∅

lemma nearSet_card (p : Params) (hD : 0 < p.D) {M : ℕ} (e : Fin M ↪ Fin p.d)
    (x : EuclideanSpace ℝ (Fin p.d)) : (nearSet p e x).card ≤ 16 := by
  unfold nearSet
  split_ifs with h
  · exact near_count p.D hD e p.x0 x h
  · simp

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma silent_execution (p : Params) {M : ℕ} (e : Fin M ↪ Fin p.d) (hν0 : 0 ≤ noiseLevel p)
    (hν1 : noiseLevel p ≤ 1) (j : Fin M)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ) (seed : A.Seed) (ξ : ℕ → Bool)
    (hsil : ∀ t < b 0 + b 1, ξ t = false)
    (hvis : ∀ t < b 0 + b 1, j ∉ nearSet p e
      ((A.query ((fun s => A.update s (silentReply p (A.query s)))^[t] (A.initial seed))).2) ∨
      (A.query ((fun s => A.update s (silentReply p (A.query s)))^[t] (A.initial seed))).1 ≠ 0) :
    ∃ τ ≤ b 0 + b 1, execute (noiseOracle p e hν0 hν1 j) A b seed ξ =
      A.output ((fun s => A.update s (silentReply p (A.query s)))^[τ] (A.initial seed)) := by
  have h := execute_eq_trajectory (noiseOracle p e hν0 hν1 j) A b seed ξ (silentReply p) (by
    intro history hl
    rw [Fin.sum_univ_two] at hl
    have hs := hsil history.length hl
    rcases hvis history.length hl with hv | hv
    · generalize hq : A.query _ = q at hv ⊢
      obtain ⟨i, x⟩ := q
      simp only [noiseOracle, ballOracle, silentReply]
      split_ifs with hi
      · simp only [noisyGradient, hs, Bool.false_eq_true, ↓reduceIte]
        unfold nearSet at hv
        split_ifs with hb hn
        · simp only [hb, ↓reduceIte] at hv
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩) hv
        · rfl
        · rfl
      · rfl
    · generalize hq : A.query _ = q at hv ⊢
      obtain ⟨i, x⟩ := q
      simp only [noiseOracle, ballOracle, silentReply]
      simp only at hv
      simp [hv])
  rw [Fin.sum_univ_two] at h
  exact h

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma noise_exists_failure (p : Params) (hD : 0 < p.D) (hε : 0 < p.ε) (hγ : 0 < p.γ)
    (hγ1 : p.γ ≤ 1) (hσ : 0 < p.σ) (hband : 64 * p.γ * p.ε ≤ p.σ * p.D)
    (hLD : 2048 * p.ε ≤ p.L * p.D ^ 2) (hδ0 : 0 ≤ p.δ) (hδ1 : p.δ ≤ 1) {K M : ℕ}
    (hM : 64 * K + 64 ≤ M)
    (hMd : M ≤ p.d) (hsilent : 2 * p.δ < (1 - noiseLevel p) ^ K)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ) (hK : b 0 + b 1 = K) :
    ∃ (I : spec.Instance (spec.publicInput p))
      (O : Oracle (spec.Query (spec.publicInput p)) (spec.Reply (spec.publicInput p)) spec.numOracles),
      spec.admissible p I O ∧
        ¬ spec.successful p I (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A b seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  by_contra hcon
  push Not at hcon
  have hν := noiseLevel_pos p hD hε hγ hσ
  have hν1 : noiseLevel p ≤ 1 := (noiseLevel_le p hD hε hγ hσ hband).trans (by norm_num)
  let e : Fin M ↪ Fin p.d := Fin.castLEEmb hMd
  let Pm : Measure (A.Seed × (ℕ → Bool)) :=
    (A.law : Measure A.Seed).prod
      ((coinPath (noiseLevel p) hν.le hν1 : ProbabilityMeasure (ℕ → Bool)) : Measure (ℕ → Bool))
  have : IsProbabilityMeasure Pm := by dsimp [Pm]; infer_instance
  let out := fun (j : Fin M) (ω : A.Seed × (ℕ → Bool)) =>
    execute (noiseOracle p e hν.le hν1 j) A b ω.1 ω.2
  let S := fun j : Fin M => {ω : A.Seed × (ℕ → Bool) | out j ω ∈ closedBall p.x0 (p.D / 2) ∧
    wellObjective p.D p.ε p.γ p.x0 (e j) (out j ω) -
      wellObjective p.D p.ε p.γ p.x0 (e j) (wellCenter p.D p.x0 (e j)) ≤ p.ε}
  have hsucc (j : Fin M) := hcon (noiseInstance p e j) (noiseOracle p e hν.le hν1 j)
    (noise_admissible p hD hε hγ hγ1 hσ hband hLD e j)
  have hmeasS (j : Fin M) : MeasurableSet (S j) := by
    obtain ⟨hm, _⟩ := hsucc j
    have hcont : Continuous (wellObjective p.D p.ε p.γ p.x0 (e j)) := by
      have hd : Differentiable ℝ (wellObjective p.D p.ε p.γ p.x0 (e j)) := fun z =>
        (wellObjective_gradient p.D p.ε p.γ p.x0 (e j) z).hasFDerivAt.differentiableAt
      exact hd.continuous
    have hm' : Measurable (out j) := hm
    exact (measurableSet_closedBall.preimage hm').inter
      (measurableSet_le ((hcont.measurable.comp hm').sub_const _) measurable_const)
  have hprob (j : Fin M) : ENNReal.ofReal (1 - p.δ) ≤ Pm (S j) := by
    obtain ⟨_, hfail⟩ := hsucc j
    have hc : Pm (S j)ᶜ ≤ ENNReal.ofReal p.δ := hfail
    have hsum := measure_add_measure_compl (μ := Pm) (hmeasS j)
    rw [measure_univ] at hsum
    have hfin : Pm (S j)ᶜ ≠ ⊤ := measure_ne_top _ _
    have : Pm (S j) = 1 - Pm (S j)ᶜ := by
      rw [← hsum, ENNReal.add_sub_cancel_right hfin]
    rw [this, ENNReal.ofReal_sub _ hδ0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hc 1
  let Sil : Set (A.Seed × (ℕ → Bool)) := Set.univ ×ˢ {ξ | ∀ t < K, ξ t = false}
  have hmeasSil : MeasurableSet Sil := MeasurableSet.univ.prod (silent_measurable K)
  have hPSil : Pm Sil = ENNReal.ofReal (1 - noiseLevel p) ^ K := by
    simp only [Pm, Sil, Measure.prod_prod, measure_univ, one_mul]
    exact coinPath_silent hν.le hν1 K
  have hpoint (ω : A.Seed × (ℕ → Bool)) :
      2 * (∑ j : Fin M, (S j).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) +
        (M : ENNReal) * Sil.indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω ≤ 2 * (M : ENNReal) := by
    by_cases hs : ω ∈ Sil
    · rw [Set.indicator_of_mem hs]
      set traj := fun t => (fun s => A.update s (silentReply p (A.query s)))^[t] (A.initial ω.1)
      let V := (Finset.range K).biUnion (fun t => if (A.query (traj t)).1 = 0 then
        nearSet p e (A.query (traj t)).2 else ∅)
      let N := (Finset.range (K + 1)).biUnion (fun t => nearSet p e (A.output (traj t)))
      have hV : V.card ≤ 16 * K := by
        calc V.card ≤ ∑ t ∈ Finset.range K, (if (A.query (traj t)).1 = 0 then
              nearSet p e (A.query (traj t)).2 else ∅).card := Finset.card_biUnion_le
          _ ≤ ∑ _t ∈ Finset.range K, 16 := Finset.sum_le_sum (fun t _ => by
              split_ifs
              · exact nearSet_card p hD e _
              · simp)
          _ = 16 * K := by simp [mul_comm]
      have hN : N.card ≤ 16 * (K + 1) := by
        calc N.card ≤ ∑ t ∈ Finset.range (K + 1), (nearSet p e (A.output (traj t))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _t ∈ Finset.range (K + 1), 16 := Finset.sum_le_sum (fun t _ => nearSet_card p hD e _)
          _ = 16 * (K + 1) := by simp [mul_comm]
      have hsub : ∀ j : Fin M, ω ∈ S j → j ∈ V ∪ N := by
        intro j hj
        by_contra hjn
        rw [Finset.mem_union, not_or] at hjn
        obtain ⟨hjV, hjN⟩ := hjn
        have hsil' : ∀ t < b 0 + b 1, ω.2 t = false := by
          rw [hK]; exact (Set.mem_prod.mp hs).2
        obtain ⟨τ, hτ, he⟩ := silent_execution p e hν.le hν1 j A b ω.1 ω.2 hsil' (by
          intro t ht
          by_cases hq : (A.query (traj t)).1 = 0
          · left
            intro hmem
            apply hjV
            exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr (by omega), by
              simp only [hq, ↓reduceIte]; exact hmem⟩
          · right; exact hq)
        obtain ⟨hin, hval⟩ := hj
        change execute (noiseOracle p e hν.le hν1 j) A b ω.1 ω.2 ∈ closedBall p.x0 (p.D / 2) at hin
        change wellObjective p.D p.ε p.γ p.x0 (e j) (execute (noiseOracle p e hν.le hν1 j) A b ω.1 ω.2) -
          wellObjective p.D p.ε p.γ p.x0 (e j) (wellCenter p.D p.x0 (e j)) ≤ p.ε at hval
        rw [he] at hin hval
        rw [wellObjective_center, sub_zero] at hval
        have hnear := success_near p.D p.ε p.γ hD hε hγ.le p.x0 (e j) _ hval
        have hin' : ‖A.output (traj τ) - p.x0‖ ≤ p.D / 2 := by
          rw [← dist_eq_norm]; exact mem_closedBall.mp hin
        apply hjN
        refine Finset.mem_biUnion.mpr ⟨τ, Finset.mem_range.mpr (by omega), ?_⟩
        unfold nearSet
        simp only [hin', ↓reduceIte]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩
      have hcount : (∑ j : Fin M, (S j).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) ≤
          ((V ∪ N).card : ENNReal) := by
        calc _ ≤ ∑ j : Fin M, if j ∈ V ∪ N then (1 : ENNReal) else 0 := by
              apply Finset.sum_le_sum
              intro j _
              by_cases hj : ω ∈ S j
              · rw [Set.indicator_of_mem hj]
                simp [hsub j hj]
              · rw [Set.indicator_of_notMem hj]; simp
          _ = _ := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
              simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
              congr 1
              congr 1
              ext j
              simp
      have hUN : (V ∪ N).card ≤ 32 * K + 16 := by
        have := Finset.card_union_le V N
        omega
      have hfinal : 2 * ((V ∪ N).card : ENNReal) + (M : ENNReal) * 1 ≤ 2 * (M : ENNReal) := by
        have hn : 2 * (V ∪ N).card + M * 1 ≤ 2 * M := by omega
        exact_mod_cast hn
      simp only [Pi.one_apply]
      calc _ ≤ 2 * ((V ∪ N).card : ENNReal) + (M : ENNReal) * 1 := by gcongr
        _ ≤ _ := hfinal
    · rw [Set.indicator_of_notMem hs, mul_zero, add_zero]
      have hle : (∑ j : Fin M, (S j).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) ≤ M := by
        calc _ ≤ ∑ _j : Fin M, (1 : ENNReal) := Finset.sum_le_sum (fun j _ => by
              by_cases hj : ω ∈ S j
              · rw [Set.indicator_of_mem hj]; simp
              · rw [Set.indicator_of_notMem hj]; simp)
          _ = M := by simp
      gcongr
  have hint : 2 * (∑ j : Fin M, Pm (S j)) + (M : ENNReal) * Pm Sil ≤ 2 * (M : ENNReal) := by
    have he : (∑ j : Fin M, Pm (S j)) =
        ∫⁻ ω, ∑ j : Fin M, (S j).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω ∂Pm := by
      rw [lintegral_finsetSum _ (fun j _ => (measurable_one.indicator (hmeasS j)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [lintegral_indicator_one (hmeasS j)]
    have hs : Pm Sil = ∫⁻ ω, Sil.indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω ∂Pm :=
      (lintegral_indicator_one hmeasSil).symm
    have hmS : Measurable (fun ω => ∑ j : Fin M,
        (S j).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) :=
      Finset.measurable_sum _ (fun j _ => measurable_one.indicator (hmeasS j))
    rw [he, hs, ← lintegral_const_mul _ hmS, ← lintegral_const_mul _
      (measurable_one.indicator hmeasSil), ← lintegral_add_left (hmS.const_mul _)]
    calc _ ≤ ∫⁻ _, 2 * (M : ENNReal) ∂Pm := lintegral_mono hpoint
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hlow : (M : ENNReal) * ENNReal.ofReal (1 - p.δ) ≤ ∑ j : Fin M, Pm (S j) := by
    calc _ = ∑ _ : Fin M, ENNReal.ofReal (1 - p.δ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hprob j)
  rw [hPSil] at hint
  have hcomb : 2 * ((M : ENNReal) * ENNReal.ofReal (1 - p.δ)) +
      (M : ENNReal) * ENNReal.ofReal (1 - noiseLevel p) ^ K ≤ 2 * (M : ENNReal) := by
    calc _ ≤ 2 * (∑ j : Fin M, Pm (S j)) + (M : ENNReal) * ENNReal.ofReal (1 - noiseLevel p) ^ K := by
          gcongr
      _ ≤ _ := hint
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hreal : 2 * ((M : ℝ) * (1 - p.δ)) + (M : ℝ) * (1 - noiseLevel p) ^ K ≤ 2 * (M : ℝ) := by
    have hpow : ENNReal.ofReal (1 - noiseLevel p) ^ K = ENNReal.ofReal ((1 - noiseLevel p) ^ K) :=
      (ENNReal.ofReal_pow (by linarith) K).symm
    rw [hpow] at hcomb
    have h1 : 2 * ((M : ENNReal) * ENNReal.ofReal (1 - p.δ)) +
        (M : ENNReal) * ENNReal.ofReal ((1 - noiseLevel p) ^ K) =
        ENNReal.ofReal (2 * ((M : ℝ) * (1 - p.δ)) + (M : ℝ) * (1 - noiseLevel p) ^ K) := by
      have h : 0 ≤ 1 - p.δ := by linarith
      have hnn : 0 ≤ (1 - noiseLevel p) ^ K := pow_nonneg (by linarith) K
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    have h2 : 2 * (M : ENNReal) = ENNReal.ofReal (2 * (M : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [h1, h2] at hcomb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcomb
  nlinarith

end LongTails.Proofs.QuasarNoiseFailure
