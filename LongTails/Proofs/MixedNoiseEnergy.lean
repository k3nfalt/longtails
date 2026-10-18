import LongTails.Proofs.MixedNoiseEstimator
import LongTails.Proofs.MixedNoiseGeometry

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OracleTemplate.MixedNoise

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω : Type} [MeasurableSpace Ω]

lemma integrated_regular_anchor_energy (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (hi : ∀ (seed : RepresentativeSeed cfg) k,
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p))
    {l n : ℕ} (hl : l ≤ cfg.m) (hT : cfg.T = n * 4 ^ l) :
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, if t < 4 ^ l then 0 else
      ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) ≤
    ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
      ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let A := fun seed ξ => ∑ t ∈ Finset.range cfg.T, if t < 4 ^ l then 0 else
    ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2
  let B := fun seed ξ => ∑ t ∈ Finset.range cfg.T,
    ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
  have hA (seed : RepresentativeSeed cfg) : Integrable (A seed) P := by
    apply integrable_finsetSum
    intro t ht
    by_cases htl : t < 4 ^ l
    · simp only [htl, ↓reduceIte]
      exact integrable_const 0
    · simp only [htl, ↓reduceIte]
      exact hi seed _
  have hB (seed : RepresentativeSeed cfg) : Integrable (B seed) P :=
    integrable_finsetSum _ (fun t ht => hi seed t)
  change (∫ seed, (∫ ξ, A seed ξ ∂P) ∂_) ≤ ∫ seed, (∫ ξ, B seed ξ ∂P) ∂_
  rw [← integral_uniform_measure_comm P A hA, ← integral_uniform_measure_comm P B hB]
  apply integral_mono (integrable_uniform_integral P A hA) (integrable_uniform_integral P B hB)
  intro ξ
  dsimp only [A, B]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have he (t : ℕ) :
      (∫ seed, (if t < 4 ^ l then 0 else
        ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2)
          ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
      if t < 4 ^ l then 0 else
        ∫ seed, ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2
          ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
    split_ifs <;> simp
  simp_rw [he]
  exact regular_anchor_energy cfg g x0 ξ (fun x => ‖G x‖ ^ 2) (fun x => sq_nonneg _) hl hT

lemma integrated_weighted_anchor_energy (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (hi : ∀ (seed : RepresentativeSeed cfg) k,
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p))
    {l n : ℕ} (hl : l ≤ cfg.m) (hT : cfg.T = n * 4 ^ l)
    (w : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hwi : ∀ t < cfg.T, t < 4 ^ l → w t ≤ a)
    (hwr : ∀ t < cfg.T, 4 ^ l ≤ t → w t ≤ b) :
    (∑ t ∈ Finset.range cfg.T, w t *
      (∫ seed, (∫ ξ,
        ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p))
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure)) ≤
      a * (4 : ℝ) ^ l * ‖G x0‖ ^ 2 + b *
        (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
          ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
            ∂(Measure.infinitePi fun _ : ℕ => p))
          ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let u := fun t => ∫ seed, (∫ ξ,
    ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2 ∂P) ∂Q
  have hinit (t : ℕ) (ht : t < cfg.T) (hsmall : t < 4 ^ l) : u t = ‖G x0‖ ^ 2 := by
    dsimp [u]
    simp_rw [anchorIndex_initial cfg _ hsmall, batchState_initial_point]
    simp [P, Q]
  have hreg := integrated_regular_anchor_energy p cfg g G x0 hi hl hT
  have hterm (t : ℕ) : (if t < 4 ^ l then 0 else u t) =
      ∫ seed, (∫ ξ, (if t < 4 ^ l then 0 else
        ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2) ∂P) ∂Q := by
    by_cases ht : t < 4 ^ l <;> simp [ht, u]
  have hreg' : (∑ t ∈ Finset.range cfg.T, if t < 4 ^ l then 0 else u t) ≤
      ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
        ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2 ∂P) ∂Q := by
    simp_rw [hterm]
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    have he (seed : RepresentativeSeed cfg) :
        (∑ t ∈ Finset.range cfg.T, ∫ ξ, (if t < 4 ^ l then 0 else
          ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2) ∂P) =
        ∫ ξ, ∑ t ∈ Finset.range cfg.T, (if t < 4 ^ l then 0 else
          ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2) ∂P := by
      symm
      apply integral_finsetSum
      intro t ht
      by_cases hs : t < 4 ^ l
      · simp only [hs, ↓reduceIte]
        exact integrable_const 0
      · simp only [hs, ↓reduceIte]
        exact hi seed _
    simp_rw [he]
    exact hreg
  have h := weighted_anchor_exposure cfg.T (4 ^ l) u w (‖G x0‖ ^ 2) _ a b
    (fun t ht => integral_nonneg (fun seed => integral_nonneg (fun ξ => sq_nonneg _)))
    (sq_nonneg _) ha hb hinit hwi hwr hreg'
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

lemma integrated_spatial_energy (p : Measure Ω)
    (cfg : Config) (g : E → Ω → E) (x0 : E)
    (hi : ∀ (seed : RepresentativeSeed cfg) k,
      MemLp (fun ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs k) 2
        (Measure.infinitePi fun _ : ℕ => p))
    {l : ℕ} (hl : l < cfg.m) (w : ℕ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw : ∀ t < cfg.T, w t ≤ b) :
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t *
      ‖(batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l) -
        (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1))‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) ≤
    81 * b * ((4 : ℝ) ^ l) ^ 2 *
      (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
        ‖(batchState cfg g x0 seed ξ cfg.tasks.length).xs (t + 1) -
          (batchState cfg g x0 seed ξ cfg.tasks.length).xs t‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p))
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  have hdiff (seed : RepresentativeSeed cfg) (a b : ℕ) :
      Integrable (fun ξ => ‖X seed ξ a - X seed ξ b‖ ^ 2) P := by
    have h := (hi seed a).sub (hi seed b)
    exact (OracleTemplate.TwoSidedPL.memLp_two_iff_sq h.aestronglyMeasurable).mp h
  have hD (seed : RepresentativeSeed cfg) :
      Integrable (fun ξ => ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2) P :=
    integrable_finsetSum _ (fun t ht => hdiff seed (t + 1) t)
  have hA (seed : RepresentativeSeed cfg) :
      Integrable (fun ξ => ∑ t ∈ Finset.range cfg.T, w t *
        ‖X seed ξ (anchorIndex cfg seed t l) - X seed ξ (anchorIndex cfg seed t (l + 1))‖ ^ 2) P :=
    integrable_finsetSum _ (fun t ht => (hdiff seed _ _).const_mul _)
  have hpoint (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) :
      (∑ t ∈ Finset.range cfg.T, w t *
        ‖X seed ξ (anchorIndex cfg seed t l) - X seed ξ (anchorIndex cfg seed t (l + 1))‖ ^ 2) ≤
      81 * b * ((4 : ℝ) ^ l) ^ 2 *
        ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2 := by
    calc
      _ ≤ ∑ t ∈ Finset.range cfg.T, b *
          ‖X seed ξ (anchorIndex cfg seed t l) - X seed ξ (anchorIndex cfg seed t (l + 1))‖ ^ 2 :=
        Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_right (hw t (Finset.mem_range.mp ht))
          (sq_nonneg _))
      _ = b * ∑ t ∈ Finset.range cfg.T,
          ‖X seed ξ (anchorIndex cfg seed t l) - X seed ξ (anchorIndex cfg seed t (l + 1))‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ b * (81 * ((4 : ℝ) ^ l) ^ 2 *
          ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hierarchy_spatial_energy cfg seed (X seed ξ) hl) hb
      _ = _ := by ring
  have hbound (seed : RepresentativeSeed cfg) :
      (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t *
        ‖X seed ξ (anchorIndex cfg seed t l) - X seed ξ (anchorIndex cfg seed t (l + 1))‖ ^ 2 ∂P) ≤
      81 * b * ((4 : ℝ) ^ l) ^ 2 *
        ∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2 ∂P := by
    rw [← integral_const_mul]
    exact integral_mono (hA seed) ((hD seed).const_mul _) (hpoint seed)
  change (∫ seed, _ ∂Q) ≤ _
  rw [← integral_const_mul]
  exact integral_mono Integrable.of_finite Integrable.of_finite hbound

lemma edge_energy_expansion (p : Measure Ω)
    (cfg : Config) (g : E → Ω → E) (G : E → E) (r M σ : ℝ) (x0 : E)
    (hi : ∀ (seed : RepresentativeSeed cfg) k,
      MemLp (fun ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs k) 2
        (Measure.infinitePi fun _ : ℕ => p))
    (hgi : ∀ (seed : RepresentativeSeed cfg) k,
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p))
    {l : ℕ} (hl : l < cfg.m) (w : ℕ → ℝ) :
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t *
      kernelVariance (decide (l = cfg.m)) G r M σ
        ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l),
          (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1)))
        ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
    r * (∑ t ∈ Finset.range cfg.T, w t *
      (∫ seed, (∫ ξ,
        ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p))
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure)) +
    r * (∑ t ∈ Finset.range cfg.T, w t *
      (∫ seed, (∫ ξ,
        ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1)))‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p))
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure)) +
    M ^ 2 * (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t *
      ‖(batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l) -
        (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1))‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  let A := fun seed ξ t => ‖G (X seed ξ (anchorIndex cfg seed t l))‖ ^ 2
  let B := fun seed ξ t => ‖G (X seed ξ (anchorIndex cfg seed t (l + 1)))‖ ^ 2
  let D := fun seed ξ t =>
    ‖X seed ξ (anchorIndex cfg seed t l) - X seed ξ (anchorIndex cfg seed t (l + 1))‖ ^ 2
  let K := fun seed ξ t => r * (A seed ξ t + B seed ξ t) + M ^ 2 * D seed ξ t
  have hA (seed : RepresentativeSeed cfg) (t : ℕ) : Integrable (fun ξ => A seed ξ t) P := hgi seed _
  have hB (seed : RepresentativeSeed cfg) (t : ℕ) : Integrable (fun ξ => B seed ξ t) P := hgi seed _
  have hD (seed : RepresentativeSeed cfg) (t : ℕ) : Integrable (fun ξ => D seed ξ t) P := by
    have h := (hi seed (anchorIndex cfg seed t l)).sub (hi seed (anchorIndex cfg seed t (l + 1)))
    exact (OracleTemplate.TwoSidedPL.memLp_two_iff_sq h.aestronglyMeasurable).mp h
  have hK (seed : RepresentativeSeed cfg) (t : ℕ) : Integrable (fun ξ => K seed ξ t) P :=
    (((hA seed t).add (hB seed t)).const_mul r).add ((hD seed t).const_mul (M ^ 2))
  have hv (seed : RepresentativeSeed cfg) (t : ℕ) :
      (∫ ξ, K seed ξ t ∂P) = r * ((∫ ξ, A seed ξ t ∂P) + (∫ ξ, B seed ξ t ∂P)) +
        M ^ 2 * (∫ ξ, D seed ξ t ∂P) := by
    dsimp only [K]
    have hAB : Integrable (fun ξ => A seed ξ t + B seed ξ t) P := (hA seed t).add (hB seed t)
    have hRAB : Integrable (fun ξ => r * (A seed ξ t + B seed ξ t)) P := hAB.const_mul r
    have hMD : Integrable (fun ξ => M ^ 2 * D seed ξ t) P := (hD seed t).const_mul _
    rw [integral_add hRAB hMD, integral_const_mul, integral_add (hA seed t) (hB seed t),
      integral_const_mul]
  have hv' (t : ℕ) : (∫ seed, (∫ ξ, K seed ξ t ∂P) ∂Q) =
      r * ((∫ seed, (∫ ξ, A seed ξ t ∂P) ∂Q) + (∫ seed, (∫ ξ, B seed ξ t ∂P) ∂Q)) +
        M ^ 2 * (∫ seed, (∫ ξ, D seed ξ t ∂P) ∂Q) := by
    simp_rw [hv]
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
      integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
  simp only [kernelVariance, decide_eq_true_eq, Nat.ne_of_lt hl, ↓reduceIte]
  change (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t * K seed ξ t ∂P) ∂Q) =
    r * (∑ t ∈ Finset.range cfg.T, w t * (∫ seed, (∫ ξ, A seed ξ t ∂P) ∂Q)) +
      r * (∑ t ∈ Finset.range cfg.T, w t * (∫ seed, (∫ ξ, B seed ξ t ∂P) ∂Q)) +
      M ^ 2 * (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t * D seed ξ t ∂P) ∂Q)
  rw [← integral_uniform_weighted_sum P (Finset.range cfg.T) w K (fun seed t ht => hK seed t),
    ← integral_uniform_weighted_sum P (Finset.range cfg.T) w D (fun seed t ht => hD seed t)]
  dsimp only [Q] at hv' ⊢
  simp_rw [hv']
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  ring

lemma edge_energy_bound (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (G : E → E) (r M σ : ℝ) (x0 : E)
    (hi : ∀ (seed : RepresentativeSeed cfg) k,
      MemLp (fun ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs k) 2
        (Measure.infinitePi fun _ : ℕ => p))
    (hgi : ∀ (seed : RepresentativeSeed cfg) k,
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p))
    {l n n' : ℕ} (hl : l < cfg.m) (hT : cfg.T = n * 4 ^ l) (hT' : cfg.T = n' * 4 ^ (l + 1))
    (w : ℕ → ℝ) (a b : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : ∀ t < cfg.T, w t ≤ b) (hws : ∀ t < cfg.T, t < 4 ^ (l + 1) → w t ≤ a) :
    let P := Measure.infinitePi fun _ : ℕ => p
    let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
    let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
    let V := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2 ∂P) ∂Q
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t *
      kernelVariance (decide (l = cfg.m)) G r M σ
        (X seed ξ (anchorIndex cfg seed t l), X seed ξ (anchorIndex cfg seed t (l + 1))) ∂P) ∂Q) ≤
      2 * r * b * S + 5 * r * a * (4 : ℝ) ^ l * ‖G x0‖ ^ 2 +
        81 * M ^ 2 * b * ((4 : ℝ) ^ l) ^ 2 * V := by
  dsimp only
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
  let V := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2 ∂P) ∂Q
  have hleft := integrated_weighted_anchor_energy p cfg g G x0 hgi hl.le hT w a b ha hb
    (fun t ht hsmall => hws t ht (by rw [pow_succ]; omega)) (fun t ht _ => hw t ht)
  have hright := integrated_weighted_anchor_energy p cfg g G x0 hgi (by omega : l + 1 ≤ cfg.m)
    hT' w a b ha hb hws (fun t ht _ => hw t ht)
  have hsp := integrated_spatial_energy p cfg g x0 hi hl w b hb hw
  rw [edge_energy_expansion p cfg g G r M σ x0 hi hgi hl w]
  calc
    _ ≤ r * (a * (4 : ℝ) ^ l * ‖G x0‖ ^ 2 + b * S) +
        r * (a * (4 : ℝ) ^ (l + 1) * ‖G x0‖ ^ 2 + b * S) +
        M ^ 2 * (81 * b * ((4 : ℝ) ^ l) ^ 2 * V) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hleft hr)
        (mul_le_mul_of_nonneg_left hright hr)) (mul_le_mul_of_nonneg_left hsp (sq_nonneg M))
    _ = _ := by rw [pow_succ (4 : ℝ) l]; ring

lemma root_energy_bound (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (G : E → E) (r M σ : ℝ) (x0 : E)
    (hgi : ∀ (seed : RepresentativeSeed cfg) k,
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p))
    {n : ℕ} (hT : cfg.T = n * 4 ^ cfg.m)
    (w : ℕ → ℝ) (a b : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : ∀ t < cfg.T, w t ≤ b) (hws : ∀ t < cfg.T, t < 4 ^ cfg.m → w t ≤ a) :
    let P := Measure.infinitePi fun _ : ℕ => p
    let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
    let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t *
      kernelVariance true G r M σ
        (X seed ξ (anchorIndex cfg seed t cfg.m), X seed ξ (anchorIndex cfg seed t (cfg.m + 1))) ∂P) ∂Q) ≤
      r * b * S + r * a * (4 : ℝ) ^ cfg.m * ‖G x0‖ ^ 2 + cfg.T * σ ^ 2 * b := by
  dsimp only
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  let A := fun seed ξ t => ‖G (X seed ξ (anchorIndex cfg seed t cfg.m))‖ ^ 2
  let K := fun seed ξ t => r * A seed ξ t + σ ^ 2
  let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
  have hA (seed : RepresentativeSeed cfg) (t : ℕ) : Integrable (fun ξ => A seed ξ t) P := hgi seed _
  have hK (seed : RepresentativeSeed cfg) (t : ℕ) : Integrable (fun ξ => K seed ξ t) P :=
    ((hA seed t).const_mul r).add (integrable_const _)
  have hv (seed : RepresentativeSeed cfg) (t : ℕ) :
      (∫ ξ, K seed ξ t ∂P) = r * (∫ ξ, A seed ξ t ∂P) + σ ^ 2 := by
    dsimp only [K]
    rw [integral_add ((hA seed t).const_mul r) (integrable_const _), integral_const_mul]
    simp
  have hv' (t : ℕ) : (∫ seed, (∫ ξ, K seed ξ t ∂P) ∂Q) =
      r * (∫ seed, (∫ ξ, A seed ξ t ∂P) ∂Q) + σ ^ 2 := by
    simp_rw [hv]
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
    simp [Q]
  have hroot := integrated_weighted_anchor_energy p cfg g G x0 hgi le_rfl hT w a b ha hb
    hws (fun t ht _ => hw t ht)
  have hsum : (∑ t ∈ Finset.range cfg.T, w t) ≤ cfg.T * b := by
    calc
      _ ≤ ∑ _t ∈ Finset.range cfg.T, b := Finset.sum_le_sum (fun t ht => hw t (Finset.mem_range.mp ht))
      _ = _ := by simp [nsmul_eq_mul]
  simp only [kernelVariance, ↓reduceIte]
  change (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, w t * K seed ξ t ∂P) ∂Q) ≤
    r * b * S + r * a * (4 : ℝ) ^ cfg.m * ‖G x0‖ ^ 2 + cfg.T * σ ^ 2 * b
  calc
    _ = ∑ t ∈ Finset.range cfg.T,
        w t * (r * (∫ seed, (∫ ξ, A seed ξ t ∂P) ∂Q) + σ ^ 2) := by
      rw [← integral_uniform_weighted_sum P (Finset.range cfg.T) w K (fun seed t ht => hK seed t)]
      dsimp only [Q] at hv' ⊢
      simp_rw [hv']
    _ = r * (∑ t ∈ Finset.range cfg.T, w t * (∫ seed, (∫ ξ, A seed ξ t ∂P) ∂Q)) +
        σ ^ 2 * (∑ t ∈ Finset.range cfg.T, w t) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ r * (a * (4 : ℝ) ^ cfg.m * ‖G x0‖ ^ 2 + b * S) + σ ^ 2 * (cfg.T * b) :=
      add_le_add (mul_le_mul_of_nonneg_left hroot hr) (mul_le_mul_of_nonneg_left hsum (sq_nonneg σ))
    _ = _ := by ring

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma integrated_estimator_moment_bound (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : NNReal} (hG : LipschitzWith L G) (r M σ : ℝ)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) :
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
      ‖(∑ l ∈ Finset.range (cfg.m + 1),
          (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l) -
        G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) ≤
    ∑ l ∈ Finset.range (cfg.m + 1),
      ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, componentWeight cfg t l *
        kernelVariance (decide (l = cfg.m)) G r M σ
          ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l),
            (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1)))
          ∂(Measure.infinitePi fun _ : ℕ => p))
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let A := fun seed ξ t =>
    ‖(∑ l ∈ Finset.range (cfg.m + 1),
        (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l) -
      G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
  let W := fun seed ξ t l => kernelVariance (decide (l = cfg.m)) G r M σ
    ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l),
      (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1)))
  have H (seed : RepresentativeSeed cfg) (t : ℕ) (ht : t < cfg.T) :=
    actual_estimator_moment_bound p cfg g hg G hG r M σ hgi hmean hnoise hbound hdiff hmixed
      x0 seed t ht
  have hA (seed : RepresentativeSeed cfg) (t : ℕ) (ht : t ∈ Finset.range cfg.T) :
      Integrable (fun ξ => A seed ξ t) P := (H seed t (Finset.mem_range.mp ht)).1
  have hW (seed : RepresentativeSeed cfg) (t l : ℕ) : Integrable (fun ξ => W seed ξ t l) P := by
    have hX := (batchState_memLp p cfg g hg G hG r σ hnoise hbound x0 seed cfg.tasks.length).1
    exact kernelVariance_integrable (decide (l = cfg.m)) G hG r M σ _ (hX _) (hX _)
  change (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, A seed ξ t ∂P) ∂Q) ≤
    ∑ l ∈ Finset.range (cfg.m + 1),
      ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, componentWeight cfg t l * W seed ξ t l ∂P) ∂Q
  calc
    _ = ∑ t ∈ Finset.range cfg.T, ∫ seed, (∫ ξ, A seed ξ t ∂P) ∂Q := by
      simpa only [one_mul] using
        (integral_uniform_weighted_sum P (Finset.range cfg.T) (fun _ => 1) A hA).symm
    _ ≤ ∑ t ∈ Finset.range cfg.T, ∫ seed,
        (∑ l ∈ Finset.range (cfg.m + 1), componentWeight cfg t l * ∫ ξ, W seed ξ t l ∂P) ∂Q := by
      apply Finset.sum_le_sum
      intro t ht
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro seed
      exact (H seed t (Finset.mem_range.mp ht)).2
    _ = ∑ t ∈ Finset.range cfg.T, ∑ l ∈ Finset.range (cfg.m + 1),
        componentWeight cfg t l * ∫ seed, (∫ ξ, W seed ξ t l ∂P) ∂Q := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp_rw [integral_const_mul]
    _ = ∑ l ∈ Finset.range (cfg.m + 1), ∑ t ∈ Finset.range cfg.T,
        componentWeight cfg t l * ∫ seed, (∫ ξ, W seed ξ t l ∂P) ∂Q := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      exact integral_uniform_weighted_sum P (Finset.range cfg.T) (fun t => componentWeight cfg t l)
        (fun seed ξ t => W seed ξ t l) (fun seed t ht => hW seed t l)

lemma aggregate_error_energy (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : NNReal} (hG : LipschitzWith L G) (r M σ : ℝ)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) (hr : 0 ≤ r)
    (hdiv : ∀ l ≤ cfg.m, ∃ n, cfg.T = n * 4 ^ l)
    (a b : ℕ → ℝ) (a0 b0 : ℝ)
    (ha : ∀ l < cfg.m, 0 ≤ a l) (hb : ∀ l < cfg.m, 0 ≤ b l) (ha0 : 0 ≤ a0) (hb0 : 0 ≤ b0)
    (hw : ∀ l < cfg.m, ∀ t < cfg.T, componentWeight cfg t l ≤ b l)
    (hws : ∀ l < cfg.m, ∀ t < cfg.T, t < 4 ^ (l + 1) → componentWeight cfg t l ≤ a l)
    (hw0 : ∀ t < cfg.T, componentWeight cfg t cfg.m ≤ b0)
    (hws0 : ∀ t < cfg.T, t < 4 ^ cfg.m → componentWeight cfg t cfg.m ≤ a0) :
    let P := Measure.infinitePi fun _ : ℕ => p
    let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
    let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    let S := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖G (X seed ξ t)‖ ^ 2 ∂P) ∂Q
    let V := ∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T, ‖X seed ξ (t + 1) - X seed ξ t‖ ^ 2 ∂P) ∂Q
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
      ‖(∑ l ∈ Finset.range (cfg.m + 1),
          (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l) - G (X seed ξ t)‖ ^ 2 ∂P) ∂Q) ≤
    (∑ l ∈ Finset.range cfg.m, (2 * r * b l * S + 5 * r * a l * (4 : ℝ) ^ l * ‖G x0‖ ^ 2 +
      81 * M ^ 2 * b l * ((4 : ℝ) ^ l) ^ 2 * V)) +
      (r * b0 * S + r * a0 * (4 : ℝ) ^ cfg.m * ‖G x0‖ ^ 2 + cfg.T * σ ^ 2 * b0) := by
  dsimp only
  have hX (seed : RepresentativeSeed cfg) (k : ℕ) :=
    (batchState_memLp p cfg g hg G hG r σ hnoise hbound x0 seed cfg.tasks.length).1 k
  have hGi (seed : RepresentativeSeed cfg) (k : ℕ) :
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) := by
    have h := lipschitz_comp_memLp hG (hX seed k)
    exact (OracleTemplate.TwoSidedPL.memLp_two_iff_sq h.aestronglyMeasurable).mp h
  apply (integrated_estimator_moment_bound p cfg g hg G hG r M σ hgi hmean hnoise hbound hdiff hmixed x0).trans
  rw [Finset.sum_range_succ]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro l hl
    have hlm := Finset.mem_range.mp hl
    obtain ⟨n, hn⟩ := hdiv l hlm.le
    obtain ⟨n', hn'⟩ := hdiv (l + 1) (by omega)
    exact edge_energy_bound p cfg g G r M σ x0 hX hGi hlm hn hn'
      (fun t => componentWeight cfg t l) (a l) (b l) hr (ha l hlm) (hb l hlm)
      (hw l hlm) (hws l hlm)
  · obtain ⟨n, hn⟩ := hdiv cfg.m le_rfl
    simpa only [decide_true] using
      root_energy_bound p cfg g G r M σ x0 hGi hn (fun t => componentWeight cfg t cfg.m)
        a0 b0 hr ha0 hb0 hw0 hws0

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma integrated_inexact_path_energy {Seed : Type} [Fintype Seed] [Nonempty Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    {W : Type} [MeasurableSpace W] (P : Measure W) [IsProbabilityMeasure P]
    {f : E → ℝ} {G : E → E} {L η Δ : ℝ}
    (hgrad : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (X U : Seed → W → ℕ → E) (x0 : E) (T : ℕ)
    (hX0 : ∀ s ω, X s ω 0 = x0)
    (hstep : ∀ s ω k, k < T → X s ω (k + 1) = X s ω k - η • U s ω k)
    (hgap : ∀ y, f x0 - f y ≤ Δ)
    (hGi : ∀ s k, MemLp (fun ω => G (X s ω k)) 2 P)
    (hUi : ∀ s k, MemLp (fun ω => U s ω k) 2 P) :
    let Q := (PMF.uniformOfFintype Seed).toMeasure
    η / 2 * (∫ s, (∫ ω, ∑ k ∈ Finset.range T, ‖G (X s ω k)‖ ^ 2 ∂P) ∂Q) +
      η / 2 * (1 - L * η) * (∫ s, (∫ ω, ∑ k ∈ Finset.range T, ‖U s ω k‖ ^ 2 ∂P) ∂Q) ≤
      Δ + η / 2 * (∫ s, (∫ ω, ∑ k ∈ Finset.range T, ‖U s ω k - G (X s ω k)‖ ^ 2 ∂P) ∂Q) := by
  dsimp only
  let Q := (PMF.uniformOfFintype Seed).toMeasure
  let A := fun s ω => ∑ k ∈ Finset.range T, ‖G (X s ω k)‖ ^ 2
  let B := fun s ω => ∑ k ∈ Finset.range T, ‖U s ω k‖ ^ 2
  let R := fun s ω => ∑ k ∈ Finset.range T, ‖U s ω k - G (X s ω k)‖ ^ 2
  have hsq (v : W → E) (hv : MemLp v 2 P) : Integrable (fun ω => ‖v ω‖ ^ 2) P :=
    (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hv.aestronglyMeasurable).mp hv
  have hA (s : Seed) : Integrable (A s) P := integrable_finsetSum _ (fun k hk => hsq _ (hGi s k))
  have hB (s : Seed) : Integrable (B s) P := integrable_finsetSum _ (fun k hk => hsq _ (hUi s k))
  have hR (s : Seed) : Integrable (R s) P :=
    integrable_finsetSum _ (fun k hk => hsq _ ((hUi s k).sub (hGi s k)))
  have hpoint (s : Seed) (ω : W) :
      η / 2 * A s ω + η / 2 * (1 - L * η) * B s ω ≤ Δ + η / 2 * R s ω := by
    exact inexact_path_energy hgrad hlip (X s ω) (U s ω) T (hstep s ω)
      (fun y => by simpa only [hX0 s ω] using hgap y)
  have hint (s : Seed) :
      η / 2 * (∫ ω, A s ω ∂P) + η / 2 * (1 - L * η) * (∫ ω, B s ω ∂P) ≤
        Δ + η / 2 * (∫ ω, R s ω ∂P) := by
    have h := integral_mono (((hA s).const_mul _).add ((hB s).const_mul _))
      ((integrable_const Δ).add ((hR s).const_mul _)) (hpoint s)
    simp only [Pi.add_apply] at h
    rw [integral_add (((hA s).const_mul _)) ((hB s).const_mul _),
      integral_add (integrable_const Δ) ((hR s).const_mul _)] at h
    simpa only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  have h := integral_mono (μ := Q) (f := fun s => η / 2 * (∫ ω, A s ω ∂P) +
      η / 2 * (1 - L * η) * (∫ ω, B s ω ∂P))
    (g := fun s => Δ + η / 2 * (∫ ω, R s ω ∂P))
    Integrable.of_finite Integrable.of_finite hint
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite] at h
  simpa [Q, integral_const_mul] using h

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma integrated_displacement_energy {Seed : Type} [MeasurableSpace Seed]
    {W : Type} [MeasurableSpace W] (P : Measure W) (Q : Measure Seed)
    (X U : Seed → W → ℕ → E) (η : ℝ) (T : ℕ)
    (hstep : ∀ s ω k, k < T → X s ω (k + 1) = X s ω k - η • U s ω k) :
    (∫ s, (∫ ω, ∑ k ∈ Finset.range T, ‖X s ω (k + 1) - X s ω k‖ ^ 2 ∂P) ∂Q) =
      η ^ 2 * (∫ s, (∫ ω, ∑ k ∈ Finset.range T, ‖U s ω k‖ ^ 2 ∂P) ∂Q) := by
  have he (s : Seed) (ω : W) :
      (∑ k ∈ Finset.range T, ‖X s ω (k + 1) - X s ω k‖ ^ 2) =
        η ^ 2 * ∑ k ∈ Finset.range T, ‖U s ω k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hstep s ω k (Finset.mem_range.mp hk)]
    have hh : X s ω k - η • U s ω k - X s ω k = -(η • U s ω k) := by abel
    rw [hh, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [he, integral_const_mul]

lemma averaged_gradient_bound {η L Δ S V R G ε : ℝ} (T : ℕ)
    (hη : 0 < η) (hηL : L * η = 1 / 2)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hG0 : 0 ≤ G) (hG : G ≤ 2 * L * Δ)
    (hT : 8 * Δ ≤ η * T * ε ^ 2)
    (hdescent : η / 2 * S + η / 2 * (1 - L * η) * V ≤ Δ + η / 2 * R)
    (herror : R ≤ 5 * S / 4096 + 6 * G / 4096 + 81 * V / 4096 + T * ε ^ 2 / 4096) :
    S ≤ T * ε ^ 2 := by
  have h := absorb_error_energy hη hηL hV (by positivity : 0 ≤ (T : ℝ) * ε ^ 2 / 4096) hG hdescent
    (show R ≤ S / 4 + V / 4 + G + T * ε ^ 2 / 4096 by nlinarith only [herror, hS, hV, hG0])
  have hn : 0 ≤ η * T * ε ^ 2 := by positivity
  have hle : η * S ≤ η * (T * ε ^ 2) := by nlinarith only [h, hT, hn]
  exact (mul_le_mul_iff_right₀ hη).mp hle

end OracleTemplate.MixedNoise
