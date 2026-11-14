import LongTails.Proofs.AffineResidualGap
import LongTails.Proofs.AffineResidualRegret

namespace LongTails.Proofs.AffineResidualWeighted

open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Proofs.AffineResidualSaddle
open LongTails.Proofs.AffineResidualRegret

lemma weighted_curvature (β : ℝ) (k : ℕ) :
    cumulativeCurvature (β ^ 2) (fun j => iterationWeight β j / 2) k +
      iterationWeight β k / 2 = curvature β k := by
  simp only [cumulativeCurvature, curvature, Finset.sum_range_succ]
  ring

lemma weighted_noise_cap {β τ B : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hB : 0 ≤ B) (hcap : 4 * B ≤ β * τ) (k : ℕ) {b : ℝ} (hb : |b| ≤ B) :
    |iterationWeight β k * b / (curvature β k * τ)| ≤ 1 := by
  have hw := weight_positive hβ k
  have hA := curvature_positive hβ k
  have hr := weight_ratio_bound hβ k
  have hcross : iterationWeight β k * β ≤ 4 * curvature β k :=
    (div_le_div_iff₀ hA hβ).mp hr
  rw [abs_div, abs_mul, abs_of_pos hw, abs_of_pos (mul_pos hA hτ)]
  apply (div_le_iff₀ (mul_pos hA hτ)).mpr
  have h1 := mul_le_mul_of_nonneg_left hb hw.le
  have h2 := mul_le_mul_of_nonneg_left hcap hA.le
  have h3 := mul_le_mul_of_nonneg_right hcross hB
  nlinarith

lemma weighted_stability_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {β μ τ : ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hτ : 0 < τ)
    (k : ℕ) (g : E) (b p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ‖iterationWeight β k • g‖ ^ 2 / (2 * (curvature β k * μ)) +
      1 / (curvature β k * τ) * ∑ i, p i * (iterationWeight β k * b i) ^ 2 ≤
        2 / μ * ‖g‖ ^ 2 + 4 / τ * ∑ i, p i * (b i) ^ 2 := by
  have hA := curvature_positive hβ k
  have hs : (∑ i, p i * (iterationWeight β k * b i) ^ 2) =
      (iterationWeight β k) ^ 2 * ∑ i, p i * (b i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have he : (iterationWeight β k) ^ 2 * ‖g‖ ^ 2 / (2 * (curvature β k * μ)) +
      1 / (curvature β k * τ) * ((iterationWeight β k) ^ 2 * ∑ i, p i * (b i) ^ 2) =
      ((iterationWeight β k) ^ 2 / curvature β k) *
        (‖g‖ ^ 2 / (2 * μ) + (∑ i, p i * (b i) ^ 2) / τ) := by
    field_simp
  rw [he]
  have hsum : 0 ≤ ∑ i, p i * (b i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  have hn : 0 ≤ ‖g‖ ^ 2 / (2 * μ) + (∑ i, p i * (b i) ^ 2) / τ := by positivity
  have hh := mul_le_mul_of_nonneg_right (weight_square_ratio_bound hβ k) hn
  convert hh using 1
  ring

section WeightedRegret

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def weightedAuxiliary (C : Set E) (μ τ β : ℝ) (initial : State ι E)
    (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (k : ℕ) : State ι E :=
  auxiliaryPredictor C μ τ (β ^ 2) initial (fun j => iterationWeight β j / 2) center
    (fun j => iterationWeight β j • g j) (fun j i => iterationWeight β j * b j i) k

omit [Nonempty ι] in
lemma weightedAuxiliary_prefix (C : Set E) (μ τ β : ℝ) (initial : State ι E)
    (center otherCenter : ℕ → State ι E) (g otherG : ℕ → E) (b otherB : ℕ → ι → ℝ)
    (k : ℕ) (hc : ∀ j ≤ k, center j = otherCenter j)
    (hg : ∀ j < k, g j = otherG j) (hb : ∀ j < k, b j = otherB j) :
    weightedAuxiliary C μ τ β initial center g b k =
      weightedAuxiliary C μ τ β initial otherCenter otherG otherB k := by
  have hp : cumulativePrimal μ (β ^ 2) initial (fun j => iterationWeight β j / 2) center (fun j => iterationWeight β j • g j) k =
      cumulativePrimal μ (β ^ 2) initial (fun j => iterationWeight β j / 2) otherCenter (fun j => iterationWeight β j • otherG j) k := by
    unfold cumulativePrimal
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [hc j (Finset.mem_range.mp hj).le, hg j (Finset.mem_range.mp hj)]
  have hd : cumulativeDual τ (β ^ 2) initial (fun j => iterationWeight β j / 2) center (fun j i => iterationWeight β j * b j i) k =
      cumulativeDual τ (β ^ 2) initial (fun j => iterationWeight β j / 2) otherCenter (fun j i => iterationWeight β j * otherB j i) k := by
    funext i
    unfold cumulativeDual
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [hc j (Finset.mem_range.mp hj).le, hb j (Finset.mem_range.mp hj)]
  unfold weightedAuxiliary auxiliaryPredictor
  rw [hp, hd, hc k le_rfl]

omit [Nonempty ι] in
lemma pairing_scale (w : ℝ) (g : E) (b : ι → ℝ) (u v : State ι E) :
    pairing (w • g) (fun i => w * b i) u v = w * pairing g b u v := by
  simp only [pairing, real_inner_smul_left, mul_assoc, ← Finset.mul_sum, mul_add]

lemma weighted_auxiliary_regret {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ β B : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 0 < β)
    (hB : 0 ≤ B) (hcap : 4 * B ≤ β * τ)
    (initial : State ι E) (hi : ∀ i, 0 < initial.probability i)
    (hisum : ∑ i, initial.probability i = 1)
    (center : ℕ → State ι E) (hc : ∀ k i, 0 < (center k).probability i)
    (hcsum : ∀ k, ∑ i, (center k).probability i = 1)
    (g : ℕ → E) (b : ℕ → ι → ℝ) (N : ℕ) (hb : ∀ k < N, ∀ i, |b k i| ≤ B)
    {u : State ι E} (hu : u ∈ kernelDomain C) :
    (∑ k ∈ Finset.range N, iterationWeight β k *
      pairing (g k) (b k) (weightedAuxiliary C μ τ β initial center g b k) u) ≤
      β ^ 2 * potential μ τ u initial +
        (∑ k ∈ Finset.range N, iterationWeight β k / 2 * potential μ τ u (center k)) +
        ∑ k ∈ Finset.range N,
          (2 / μ * ‖g k‖ ^ 2 + 4 / τ *
            ∑ i, (weightedAuxiliary C μ τ β initial center g b k).probability i * (b k i) ^ 2) := by
  have hw : ∀ k, 0 ≤ iterationWeight β k / 2 := fun k =>
    div_nonneg (weight_positive hβ k).le (by norm_num)
  have ha : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hh := auxiliary_regret hC hne hconv hμ hτ ha initial hi hisum
    (fun k => iterationWeight β k / 2) hw center hc hcsum
    (fun k => iterationWeight β k • g k) (fun k i => iterationWeight β k * b k i) N
    (by
      intro k hk i
      rw [weighted_curvature]
      exact weighted_noise_cap hβ hτ hB hcap k (hb k hk i)) hu
  simp_rw [pairing_scale, weighted_curvature] at hh
  have he : (∑ k ∈ Finset.range N,
      (‖iterationWeight β k • g k‖ ^ 2 / (2 * (curvature β k * μ)) +
        1 / (curvature β k * τ) * ∑ i,
          (weightedAuxiliary C μ τ β initial center g b k).probability i *
            (iterationWeight β k * b k i) ^ 2)) ≤
      ∑ k ∈ Finset.range N, (2 / μ * ‖g k‖ ^ 2 + 4 / τ *
        ∑ i, (weightedAuxiliary C μ τ β initial center g b k).probability i * (b k i) ^ 2) := by
    apply Finset.sum_le_sum
    intro k _
    apply weighted_stability_bound hβ hμ hτ
    intro i
    exact ((auxiliaryPredictor_spec hC hne hconv hμ hτ ha initial
      (fun k => iterationWeight β k / 2) hw center
      (fun k => iterationWeight β k • g k) (fun k i => iterationWeight β k * b k i) k).1.2.1 i)
  exact hh.trans (add_le_add le_rfl he)

end WeightedRegret

lemma reweight_step {w η : ℝ} (hη : 0 < η) (hwη : w * η = 8)
    {gap slack energy next drop variance noise : ℝ} (hd : 0 ≤ drop) (hv : 0 ≤ variance)
    (hstep : η * (gap + slack / 2) ≤ energy - (1 + η / 2) * next - drop +
      η ^ 2 / (1 + η / 2) * variance + η * noise) :
    w * gap + w / 2 * slack ≤ w ^ 2 / 8 * energy -
      (w ^ 2 / 8 + w / 2) * next + 8 * variance + w * noise := by
  let q := w ^ 2 / 8
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqη : q * η = w := by
    dsimp [q]
    nlinarith [congrArg (fun x : ℝ => w * x) hwη]
  have hqη2 : q * η ^ 2 = 8 := by
    calc
      q * η ^ 2 = (q * η) * η := by ring
      _ = 8 := by rw [hqη, hwη]
  have hm := mul_le_mul_of_nonneg_left hstep hq
  have hl : q * (η * (gap + slack / 2)) = w * gap + w / 2 * slack := by
    rw [← mul_assoc, hqη]
    ring
  have hr : q * (energy - (1 + η / 2) * next - drop +
      η ^ 2 / (1 + η / 2) * variance + η * noise) =
      q * energy - (q + w / 2) * next - q * drop +
        8 / (1 + η / 2) * variance + w * noise := by
    calc
      _ = q * energy - (q + (q * η) / 2) * next - q * drop +
        (q * η ^ 2) / (1 + η / 2) * variance + (q * η) * noise := by ring
      _ = _ := by rw [hqη, hqη2]
  rw [hl, hr] at hm
  have he : 8 / (1 + η / 2) ≤ (8 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + η / 2)).mpr
    linarith
  have hh := mul_le_mul_of_nonneg_right he hv
  have hn := mul_nonneg hq hd
  dsimp only [q] at hm hn
  linarith

lemma weighted_step_gap {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot ι E)
    (f : ι → E → ℝ) (field : ι → E → E)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hfield : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    {μ τ β : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 0 < β) (D : ℝ) (k : ℕ)
    (state : State ι E) (hs : ∀ i, 0 < state.probability i)
    (hssum : ∑ i, state.probability i = 1)
    (sample : E) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (u : State ι E) (hu : u ∈ kernelDomain C) :
    let v := predictor C s τ μ (stepSize β k) state
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ (stepSize β k) state v sample b
    let mean := ∑ i, v.probability i • (field i v.point - s.field i)
    let meanDual := fun i => D - (f i v.point - LongTails.Algorithms.AffineSoftmaxEstimator.affine s i v.point)
    iterationWeight β k * AffineResidualGap.saddleGap f s.anchor μ τ v u +
      iterationWeight β k / 2 * potential μ τ u v ≤
        (iterationWeight β k) ^ 2 / 8 * potential μ τ u state -
          ((iterationWeight β k) ^ 2 / 8 + iterationWeight β k / 2) * potential μ τ u n +
            (4 / μ * ‖sample‖ ^ 2 + 8 / τ * (∑ i, v.probability i * (b i) ^ 2) +
              iterationWeight β k * pairing (mean - sample) (fun i => meanDual i - b i) v u) := by
  let η := stepSize β k
  let v := predictor C s τ μ η state
  have hη : 0 < η := div_pos (by norm_num) (weight_positive hβ k)
  have hwη : iterationWeight β k * η = 8 := by
    dsimp only [η, stepSize]
    field_simp [(weight_positive hβ k).ne']
  have hv := predictor_probability_pos C s τ μ η state
  have hvsum := predictor_probability_sum C s τ μ η state
  have hd := potential_nonneg hμ.le hτ.le (fun i => (hv i).le) hs hvsum hssum
  have hsum : 0 ≤ ∑ i, v.probability i * (b i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv i).le (sq_nonneg _)
  have hvar : 0 ≤ ‖sample‖ ^ 2 / (2 * μ) + (∑ i, v.probability i * (b i) ^ 2) / τ := by positivity
  have ht := AffineResidualGap.step_gap_bound hC hne hconv s f field hf hfield
    hμ hτ hη D state sample b hb u hu.1 hu.2.2
  have hh := reweight_step hη hwη hd hvar
    (gap := AffineResidualGap.saddleGap f s.anchor μ τ v u)
    (slack := potential μ τ u v) (energy := potential μ τ u state)
    (next := potential μ τ u (correction (OracleTemplate.SaddlePoint.project C) s τ μ η state v sample b))
    (noise := pairing ((∑ i, v.probability i • (field i v.point - s.field i)) - sample)
      (fun i => (D - (f i v.point - LongTails.Algorithms.AffineSoftmaxEstimator.affine s i v.point)) - b i) v u)
    (by
      convert ht using 1
      field_simp
      ring)
  dsimp only [v, η] at hh
  dsimp only
  convert hh using 1
  ring

lemma energy_coefficient_step {β : ℝ} (hβ : 1 ≤ β) (k : ℕ) :
    (iterationWeight β (k + 1)) ^ 2 / 8 ≤
      (iterationWeight β k) ^ 2 / 8 + iterationWeight β k / 2 := by
  simp only [iterationWeight, Nat.cast_add, Nat.cast_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma initial_energy_coefficient {β : ℝ} (hβ : 1 ≤ β) :
    (iterationWeight β 0) ^ 2 / 8 ≤ β ^ 2 / 2 := by
  norm_num [iterationWeight]
  nlinarith [sq_nonneg (β - 1)]

lemma energy_telescope {β : ℝ} (hβ : 1 ≤ β) (energy : ℕ → ℝ)
    (henergy : ∀ k, 0 ≤ energy k) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      ((iterationWeight β k) ^ 2 / 8 * energy k -
        ((iterationWeight β k) ^ 2 / 8 + iterationWeight β k / 2) * energy (k + 1))) ≤
      (iterationWeight β 0) ^ 2 / 8 * energy 0 -
        (iterationWeight β N) ^ 2 / 8 * energy N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hc := mul_le_mul_of_nonneg_right (energy_coefficient_step hβ N) (henergy (N + 1))
      linarith

lemma weighted_gap_telescope {β : ℝ} (hβ : 1 ≤ β)
    (energy slack gap error : ℕ → ℝ) (henergy : ∀ k, 0 ≤ energy k) (N : ℕ)
    (hstep : ∀ k < N,
      iterationWeight β k * gap k + iterationWeight β k / 2 * slack k ≤
        (iterationWeight β k) ^ 2 / 8 * energy k -
          ((iterationWeight β k) ^ 2 / 8 + iterationWeight β k / 2) * energy (k + 1) + error k) :
    (∑ k ∈ Finset.range N, iterationWeight β k * gap k) +
      (∑ k ∈ Finset.range N, iterationWeight β k / 2 * slack k) ≤
        β ^ 2 / 2 * energy 0 + ∑ k ∈ Finset.range N, error k := by
  have hs := Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have ht := energy_telescope hβ energy henergy N
  have hi := mul_le_mul_of_nonneg_right (initial_energy_coefficient hβ) (henergy 0)
  have hn : 0 ≤ (iterationWeight β N) ^ 2 / 8 * energy N :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (henergy N)
  linarith

lemma remove_noise_comparator {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ β B : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 1 ≤ β)
    (hB : 0 ≤ B) (hcap : 4 * B ≤ β * τ)
    (state center : ℕ → State ι E)
    (hs : ∀ k i, 0 < (state k).probability i)
    (hssum : ∀ k, ∑ i, (state k).probability i = 1)
    (hc : ∀ k i, 0 < (center k).probability i)
    (hcsum : ∀ k, ∑ i, (center k).probability i = 1)
    (g : ℕ → E) (b : ℕ → ι → ℝ) (gap error : ℕ → ℝ)
    (N : ℕ) (hb : ∀ k < N, ∀ i, |b k i| ≤ B)
    {u : State ι E} (hu : u ∈ kernelDomain C)
    (hstep : ∀ k < N,
      iterationWeight β k * gap k + iterationWeight β k / 2 * potential μ τ u (center k) ≤
        (iterationWeight β k) ^ 2 / 8 * potential μ τ u (state k) -
          ((iterationWeight β k) ^ 2 / 8 + iterationWeight β k / 2) *
            potential μ τ u (state (k + 1)) +
              (error k + iterationWeight β k * pairing (g k) (b k) (center k) u)) :
    (∑ k ∈ Finset.range N, iterationWeight β k * gap k) ≤
      3 * β ^ 2 / 2 * potential μ τ u (state 0) +
        ∑ k ∈ Finset.range N,
          (error k + 2 / μ * ‖g k‖ ^ 2 + 4 / τ *
            ∑ i, (weightedAuxiliary C μ τ β (state 0) center g b k).probability i * (b k i) ^ 2 +
              iterationWeight β k * pairing (g k) (b k) (center k)
                (weightedAuxiliary C μ τ β (state 0) center g b k)) := by
  have hβ' : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have ht := weighted_gap_telescope hβ
    (fun k => potential μ τ u (state k)) (fun k => potential μ τ u (center k)) gap
    (fun k => error k + iterationWeight β k * pairing (g k) (b k) (center k) u)
    (fun k => potential_nonneg hμ.le hτ.le hu.2.1 (hs k) hu.2.2 (hssum k)) N hstep
  have hr := weighted_auxiliary_regret hC hne hconv hμ hτ hβ' hB hcap (state 0)
    (hs 0) (hssum 0) center hc hcsum g b N hb hu
  have he (k : ℕ) : pairing (g k) (b k) (center k) u =
      pairing (g k) (b k) (center k) (weightedAuxiliary C μ τ β (state 0) center g b k) +
        pairing (g k) (b k) (weightedAuxiliary C μ τ β (state 0) center g b k) u :=
    pairing_chain _ _ _ _ _
  simp_rw [he, mul_add] at ht
  simp only [Finset.sum_add_distrib] at ht hr ⊢
  linarith

end LongTails.Proofs.AffineResidualWeighted
