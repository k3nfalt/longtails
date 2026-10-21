import LongTails.Proofs.MuonProcess
import LongTails.Proofs.MuonMomentum
import LongTails.Proofs.MuonTuning
import LongTails.Proofs.LaggedAlignment
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace LongTails.Proofs.MuonTraining

open MeasureTheory
open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.ValidatedMuon

noncomputable def alignment {m n : ℕ} {Ω : Type*} (f : Space m n → ℝ)
    (α η : ℝ) (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (t : ℕ) (ξ : ℕ → Ω) : ℝ :=
  nuclearNorm (gradient f (trajectory α η g ξ state 0 t).1) -
    inner ℝ (gradient f (trajectory α η g ξ state 0 t).1)
      (polar (trajectory α η g ξ state 0 (t + 1)).2)

lemma alignment_nonneg {m n : ℕ} {Ω : Type*} (f : Space m n → ℝ)
    (α η : ℝ) (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (t : ℕ) (ξ : ℕ → Ω) : 0 ≤ alignment f α η g state t ξ :=
  (MatrixSmooth.polar_alignment_deficit _ _).1

lemma alignment_le {m n : ℕ} {Ω : Type*} (f : Space m n → ℝ)
    (α η : ℝ) (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (t : ℕ) (ξ : ℕ → Ω) :
    alignment f α η g state t ξ ≤
      2 * nuclearNorm (gradient f (trajectory α η g ξ state 0 t).1) :=
  (MatrixSmooth.polar_alignment_deficit _ _).2.1

lemma adapted_alignment {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Space m n → ℝ) (α η : ℝ) (g : Space m n → Ω → Space m n)
    (hg : Measurable (Function.uncurry g)) (state : Space m n × Space m n) (t : ℕ) :
    Measurable[MuonProcess.past (t + 1)] (alignment f α η g state t) := by
  have hx := (MuonProcess.adapted_trajectory α η g hg state 0 t).fst
  have hx' : Measurable[MuonProcess.past (t + 1)]
      (fun ξ => (trajectory α η g ξ state 0 t).1) :=
    hx.mono (MuonProcess.past_mono (by omega)) le_rfl
  have hm := (MuonProcess.adapted_trajectory α η g hg state 0 (t + 1)).snd
  rw [Nat.zero_add] at hm
  have hgrad := (MuonProcess.measurable_gradient f).comp hx'
  exact ((MatrixCovariance.continuous_nuclearNorm m n).measurable.comp hgrad).sub
    (hgrad.inner ((measurable_polar m n).comp hm))

lemma conditional_cutoff_alignment {m n : ℕ} {f : Space m n → ℝ} {s L α η B : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (state : Space m n × Space m n) (start j : ℕ)
    (A : (ℕ → model.Ω) → Prop) [DecidablePred A]
    (hremote : ∀ ξ, A ξ → nuclearNorm ((trajectory α η model.sample ξ state 0 start).2 -
      gradient f (trajectory α η model.sample ξ state 0 start).1) ≤ B)
    (hZ : Integrable (fun ξ => if A ξ then
      alignment f α η model.sample state (start + j) ξ else 0) P) :
    ∀ᵐ ξ ∂P, P[(fun ξ => if A ξ then alignment f α η model.sample state (start + j) ξ else 0) |
      MuonProcess.past start] ξ ≤
        2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α + 2 * (Real.sqrt α * s) := by
  let X := fun t ξ => (trajectory α η model.sample ξ state 0 t).1
  let w := fun i => α * (1 - α) ^ (j + 1 - 1 - i)
  have hX (t : ℕ) : Measurable[MuonProcess.past t] (X t) := by
    have ht := (MuonProcess.adapted_trajectory α η model.sample
      model.jointly_measurable state 0 t).fst
    rw [Nat.zero_add] at ht
    exact ht
  have hm := MuonProcess.model_weighted_noise_bounds model h hX start (j + 1) w
  have hmean : ∀ᵐ ξ ∂P, P[(fun ξ => nuclearNorm (∑ i ∈ Finset.range (j + 1),
      w i • (model.sample (X (start + i) ξ) (ξ (start + i)) -
        gradient f (X (start + i) ξ)))) | MuonProcess.past start] ξ ≤ Real.sqrt α * s := by
    filter_upwards [hm.2.2.2] with ξ hξ
    exact hξ.trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (MuonMomentum.ema_reverse_weight_square_sum hα.le hα1 (j + 1))) hs)
  apply MuonProcess.conditional_affine_bound (MuonProcess.past_le start) hZ
    (hm.1.integrable (by norm_num)) (by norm_num : (0 : ℝ) ≤ 2) _ hmean
  intro ξ
  exact MuonMomentum.trajectory_cutoff_alignment_bound hL hα hα1 hη hB hlip
    model.sample ξ state start j (A ξ) (hremote ξ)

def cutoff {m n : ℕ} {Ω : Type*} (f : Space m n → ℝ)
    (α η Δ B : ℝ) (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (start t : ℕ) (ξ : ℕ → Ω) : Prop :=
  (∀ u ≤ t, f (trajectory α η g ξ state 0 u).1 ≤ f state.1 + Δ) ∧
    nuclearNorm ((trajectory α η g ξ state 0 start).2 -
      gradient f (trajectory α η g ξ state 0 start).1) ≤ B

noncomputable def stoppedAlignment {m n : ℕ} {Ω : Type*} (f : Space m n → ℝ)
    (α η Δ B : ℝ) (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (start t : ℕ) (ξ : ℕ → Ω) : ℝ := by
  classical
  exact if cutoff f α η Δ B g state start t ξ then alignment f α η g state t ξ else 0

lemma adapted_cutoff {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Space m n → ℝ) (hf : Measurable f) (α η Δ B : ℝ)
    (g : Space m n → Ω → Space m n) (hg : Measurable (Function.uncurry g))
    (state : Space m n × Space m n) {start t : ℕ} (hst : start ≤ t) :
    MeasurableSet[MuonProcess.past (t + 1)] {ξ | cutoff f α η Δ B g state start t ξ} := by
  have hx (u : ℕ) (hu : u ≤ t) : Measurable[MuonProcess.past (t + 1)]
      (fun ξ => trajectory α η g ξ state 0 u) :=
    (MuonProcess.adapted_trajectory α η g hg state 0 u).mono
      (MuonProcess.past_mono (by omega)) le_rfl
  change MeasurableSet[MuonProcess.past (t + 1)]
    ({ξ | ∀ u ≤ t, f (trajectory α η g ξ state 0 u).1 ≤ f state.1 + Δ} ∩
      {ξ | nuclearNorm ((trajectory α η g ξ state 0 start).2 -
        gradient f (trajectory α η g ξ state 0 start).1) ≤ B})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun hu =>
      measurableSet_le (hf.comp (hx u hu).fst) measurable_const))
  · exact measurableSet_le ((MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      ((hx start hst).snd.sub ((MuonProcess.measurable_gradient f).comp (hx start hst).fst)))
      measurable_const

lemma adapted_stoppedAlignment {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Space m n → ℝ) (hf : Measurable f) (α η Δ B : ℝ)
    (g : Space m n → Ω → Space m n) (hg : Measurable (Function.uncurry g))
    (state : Space m n × Space m n) {start t : ℕ} (hst : start ≤ t) :
    Measurable[MuonProcess.past (t + 1)] (stoppedAlignment f α η Δ B g state start t) := by
  classical
  exact Measurable.ite (adapted_cutoff f hf α η Δ B g hg state hst)
    (adapted_alignment f α η g hg state t) measurable_const

lemma stoppedAlignment_bounds {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ}
    {L Δ fmin : ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (α η B : ℝ)
    (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (hgap : f state.1 - fmin ≤ Δ) (start t : ℕ) (ξ : ℕ → Ω) :
    0 ≤ stoppedAlignment f α η Δ B g state start t ξ ∧
      stoppedAlignment f α η Δ B g state start t ξ ≤ 4 * Real.sqrt (L * Δ) := by
  classical
  by_cases hA : cutoff f α η Δ B g state start t ξ
  · simp only [stoppedAlignment, ite_eq_left hA]
    refine ⟨alignment_nonneg f α η g state t ξ, ?_⟩
    have hf := hA.1 t le_rfl
    have hb := MatrixSmooth.gradient_self_bound_nonnegative hgrad hlip hL hmin
      (trajectory α η g ξ state 0 t).1
    have hgap' : f (trajectory α η g ξ state 0 t).1 - fmin ≤ 2 * Δ := by linarith
    have hm := mul_le_mul_of_nonneg_left hgap' (show 0 ≤ 2 * L by positivity)
    have hs := Real.sq_sqrt (mul_nonneg hL hΔ)
    have hn := nuclearNorm_nonneg (gradient f (trajectory α η g ξ state 0 t).1)
    have hroot := Real.sqrt_nonneg (L * Δ)
    have hg : nuclearNorm (gradient f (trajectory α η g ξ state 0 t).1) ≤
        2 * Real.sqrt (L * Δ) := by nlinarith
    exact (alignment_le f α η g state t ξ).trans (by linarith)
  · simp only [stoppedAlignment, ite_eq_right hA]
    exact ⟨le_rfl, by positivity⟩

lemma integrable_stoppedAlignment {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P] {f : Space m n → ℝ}
    {L Δ fmin : ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (α η B : ℝ)
    (g : Space m n → Ω → Space m n) (hg : Measurable (Function.uncurry g))
    (state : Space m n × Space m n) (hgap : f state.1 - fmin ≤ Δ)
    {start t : ℕ} (hst : start ≤ t) :
    Integrable (stoppedAlignment f α η Δ B g state start t) P := by
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hgrad x).continuousAt)).measurable
  have hm := (adapted_stoppedAlignment f hf α η Δ B g hg state hst).mono
    (MuonProcess.past_le _) le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable (4 * Real.sqrt (L * Δ))
  filter_upwards [] with ξ
  have hb := stoppedAlignment_bounds hL hΔ hgrad hlip hmin α η B g state hgap start t ξ
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma conditional_stoppedAlignment {m n : ℕ} {f : Space m n → ℝ} {s L α η B Δ fmin : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (state : Space m n × Space m n)
    (hgap : f state.1 - fmin ≤ Δ) (start j : ℕ) :
    ∀ᵐ ξ ∂P, P[stoppedAlignment f α η Δ B model.sample state start (start + j) |
      MuonProcess.past start] ξ ≤
        2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α + 2 * (Real.sqrt α * s) := by
  classical
  exact conditional_cutoff_alignment model h hL hs hα hα1 hη hB hlip state start j
    (cutoff f α η Δ B model.sample state start (start + j)) (fun _ hA => hA.2)
    (integrable_stoppedAlignment hL hΔ hgrad hlip hmin α η B model.sample
      model.jointly_measurable state hgap (Nat.le_add_right start j))

lemma stopped_residue_prefix_tail {m n : ℕ} {f : Space m n → ℝ} {s L α η B Δ fmin : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    (hL : 0 < L) (hs : 0 ≤ s) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (hB : 0 ≤ B) (hΔ : 0 < Δ)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (state : Space m n × Space m n)
    (hgap : f state.1 - fmin ≤ Δ) (j T : ℕ) (u : ℝ) :
    let μ := 2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α + 2 * (Real.sqrt α * s)
    let Z := fun (r : Fin (j + 1)) i =>
      stoppedAlignment f α η Δ B model.sample state
        (r.val + (j + 1) * i) (r.val + (j + 1) * i + j)
    P.real {ξ | ∃ (r : Fin (j + 1)) (N : ℕ), N ≤ T ∧
      2 * μ * N + (4 * Real.sqrt (L * Δ)) * u ≤ ∑ i ∈ Finset.range N, Z r i ξ} ≤
        (j + 1 : ℕ) * (T + 1) * Real.exp (-u) := by
  let μ := 2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α + 2 * (Real.sqrt α * s)
  let Z := fun (r : Fin (j + 1)) i =>
    stoppedAlignment f α η Δ B model.sample state
      (r.val + (j + 1) * i) (r.val + (j + 1) * i + j)
  let F := fun (r : Fin (j + 1)) i => MuonProcess.past (Ω := model.Ω) (r.val + (j + 1) * i)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hgrad x).continuousAt)).measurable
  have ha (r : Fin (j + 1)) (i : ℕ) : Measurable[F r (i + 1)] (Z r i) := by
    have hh := adapted_stoppedAlignment f hf α η Δ B model.sample model.jointly_measurable state
      (Nat.le_add_right (r.val + (j + 1) * i) j)
    rw [show r.val + (j + 1) * i + j + 1 = r.val + (j + 1) * (i + 1) by ring] at hh
    exact hh
  have hb (r : Fin (j + 1)) (i : ℕ) (ξ : ℕ → model.Ω) :
      0 ≤ Z r i ξ ∧ Z r i ξ ≤ 4 * Real.sqrt (L * Δ) :=
    stoppedAlignment_bounds hL.le hΔ.le hgrad hlip hmin α η B model.sample state hgap _ _ ξ
  have hm (r : Fin (j + 1)) (i : ℕ) : ∀ᵐ ξ ∂P, P[Z r i | F r i] ξ ≤ μ :=
    conditional_stoppedAlignment model h hL.le hs hα hα1 hη hB hΔ.le hgrad hlip hmin
      state hgap _ j
  have hp (r : Fin (j + 1)) (N : ℕ) : StronglyMeasurable[F r N]
      (fun ξ => Real.exp ((∑ i ∈ Finset.range N, Z r i ξ) / (4 * Real.sqrt (L * Δ)))) := by
    apply Measurable.stronglyMeasurable
    apply Measurable.exp
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i hi
    apply (ha r i).mono _ le_rfl
    apply MuonProcess.past_mono
    exact Nat.add_le_add_left (Nat.mul_le_mul_left (j + 1)
      (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))) r.val
  have hh := LaggedAlignment.finite_family_prefix_tail (P := P) (m := F)
    (fun r i => MuonProcess.past_le (r.val + (j + 1) * i))
    (Z := Z) (μ := μ) (show 0 < 4 * Real.sqrt (L * Δ) by positivity)
    (fun r i => (ha r i).mono (MuonProcess.past_le _) le_rfl)
    (fun r i ξ => (hb r i ξ).1) (fun r i ξ => (hb r i ξ).2) hp hm T u
  simpa only [Fintype.card_fin] using hh

lemma trajectory_descent {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ} {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (α : ℝ) (g : Space m n → Ω → Space m n) (state : Space m n × Space m n)
    (ξ : ℕ → Ω) (t : ℕ) :
    f (trajectory α η g ξ state 0 (t + 1)).1 ≤
      f (trajectory α η g ξ state 0 t).1 -
        η * nuclearNorm (gradient f (trajectory α η g ξ state 0 t).1) +
          η * alignment f α η g state t ξ + L / 2 * η ^ 2 := by
  have hd := MatrixSmooth.polar_descent hgrad hlip hL hη
    (trajectory α η g ξ state 0 t).1 (trajectory α η g ξ state 0 (t + 1)).2
  rw [MuonMomentum.trajectory_point]
  dsimp [alignment]
  linarith

lemma training_control_of_residues {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ}
    {L Δ fmin α η B μ u : ℝ} {j T : ℕ}
    (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hη : 0 ≤ η) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (hj : 1 ≤ j) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (g : Space m n → Ω → Space m n)
    (state : Space m n × Space m n) (hgap : f state.1 - fmin ≤ Δ) (ξ : ℕ → Ω)
    (hremote : ∀ t ≤ T, nuclearNorm ((trajectory α η g ξ state 0 t).2 -
      gradient f (trajectory α η g ξ state 0 t).1) ≤ B)
    (hres : ∀ r < j + 1, ∀ N ≤ T,
      (∑ i ∈ Finset.range N, stoppedAlignment f α η Δ B g state
        (r + (j + 1) * i) (r + (j + 1) * i + j) ξ) ≤
          2 * μ * N + (4 * Real.sqrt (L * Δ)) * u)
    (hmargin : ∀ N ≤ T, η * (2 * μ * N +
      (j + 1 : ℕ) * (2 * μ + (4 * Real.sqrt (L * Δ)) * (1 + u))) +
        N * (L / 2 * η ^ 2) ≤ Δ) :
    (∀ t ≤ T, f (trajectory α η g ξ state 0 t).1 ≤ f state.1 + Δ) ∧
      η * (∑ t ∈ Finset.range T,
        nuclearNorm (gradient f (trajectory α η g ξ state 0 t).1)) ≤
          Δ + η * (2 * μ * T +
            (j + 1 : ℕ) * (2 * μ + (4 * Real.sqrt (L * Δ)) * (1 + u))) +
              T * (L / 2 * η ^ 2) := by
  classical
  let W := fun t => stoppedAlignment f α η Δ B g state (t - j) t ξ
  have hW (t : ℕ) : 0 ≤ W t ∧ W t ≤ 4 * Real.sqrt (L * Δ) :=
    stoppedAlignment_bounds hL hΔ hgrad hlip hmin α η B g state hgap (t - j) t ξ
  have hc (N : ℕ) (hN : N ≤ T) : (∑ i ∈ Finset.range N, W i) ≤
      2 * μ * N + (j + 1 : ℕ) * (2 * μ + (4 * Real.sqrt (L * Δ)) * (1 + u)) := by
    apply LaggedAlignment.prefix_bound_with_warmup hj hμ (by positivity) hu
      (fun i => (hW i).1) (fun i _ => (hW i).2) _ hN
    intro r hr N hN
    simpa only [W, Nat.add_sub_cancel] using hres r hr N hN
  have he (t : ℕ) (ht : t < T)
      (hprev : ∀ v ≤ t, f (trajectory α η g ξ state 0 v).1 ≤ f state.1 + Δ) :
      alignment f α η g state t ξ = W t := by
    have hA : cutoff f α η Δ B g state (t - j) t ξ :=
      ⟨hprev, hremote (t - j) (le_trans (Nat.sub_le _ _) ht.le)⟩
    simp only [W, stoppedAlignment, ite_eq_left hA]
  have hd (t : ℕ) (_ht : t < T) := trajectory_descent hL hη hgrad hlip α g state ξ t
  have hsub := LaggedAlignment.stopped_sublevel hη
    (fun i (_hi : i < T) => nuclearNorm_nonneg (gradient f (trajectory α η g ξ state 0 i).1))
    hd he hc hmargin
  have hsub' : ∀ t ≤ T, f (trajectory α η g ξ state 0 t).1 ≤ f state.1 + Δ := by
    simpa only [trajectory] using hsub
  refine ⟨hsub', ?_⟩
  apply LaggedAlignment.average_from_descent
    (f := fun t => f (trajectory α η g ξ state 0 t).1)
    (g := fun t => nuclearNorm (gradient f (trajectory α η g ξ state 0 t).1))
    (z := fun t => alignment f α η g state t ξ) hη hd
    (hmin (trajectory α η g ξ state 0 T).1) hgap
  have heq : (∑ i ∈ Finset.range T, alignment f α η g state i ξ) =
      ∑ i ∈ Finset.range T, W i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiT := Finset.mem_range.mp hi
    exact he i hiT (fun v hv => hsub' v (le_trans hv hiT.le))
  rw [heq]
  exact hc T le_rfl

lemma residue_overhead_bound {e a x H μ u : ℝ} {K : ℕ}
    (he : 0 ≤ e) (_ha : 0 ≤ a) (hx : 1 ≤ x) (hH : 1 ≤ H)
    (hμ : μ ≤ e / 8) (hu : u ≤ 6 * H) (hK : (K : ℝ) ≤ 3 * a * H) :
    (K : ℝ) * (2 * μ + 4 * e * x * (1 + u)) ≤ 96 * e * a * x * H ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hxH : 1 ≤ x * H := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left (show 1 + u ≤ 7 * H by linarith)
    (show 0 ≤ 4 * e * x by positivity)
  have heScale := mul_le_mul_of_nonneg_left hxH he
  have hi : 2 * μ + 4 * e * x * (1 + u) ≤ 32 * e * x * H := by nlinarith
  calc
    _ ≤ (K : ℝ) * (32 * e * x * H) := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg K)
    _ ≤ (3 * a * H) * (32 * e * x * H) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by ring

lemma training_margin {η e Δ L μ b : ℝ} {T N : ℕ}
    (hη : 0 ≤ η) (_he : 0 ≤ e) (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (hN : N ≤ T) (hscale : η * e * T = Δ)
    (hmean : μ ≤ e / 8) (hoverhead : η * b ≤ Δ / 4)
    (hstep : L * η ≤ e / 2) :
    η * (2 * μ * N + b) + N * (L / 2 * η ^ 2) ≤ 3 * Δ / 4 := by
  have hNT : (N : ℝ) ≤ T := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 * η * T by positivity)
  have hs := mul_le_mul_of_nonneg_left hstep (show 0 ≤ η * T / 2 by positivity)
  have hn := mul_le_mul_of_nonneg_right hNT
    (show 0 ≤ 2 * η * μ + L / 2 * η ^ 2 by positivity)
  nlinarith

lemma training_sum_tail {m n : ℕ} {f : Space m n → ℝ} {s L α η B Δ fmin e γ u : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    (hL : 0 < L) (hs : 0 ≤ s) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 < η) (hB : 0 ≤ B) (hΔ : 0 < Δ) (he : 0 ≤ e) (hγ : 0 < γ) (hu : 0 ≤ u)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (x0 : Space m n) (hgap : f x0 - fmin ≤ Δ)
    {j T : ℕ} (hj : 1 ≤ j) (hT : 0 < T)
    (hremoteBound : 2 * (nuclearNorm (gradient f x0) + T * (L * η)) +
      s * Real.sqrt (2 * (T : ℝ) / γ) ≤ B)
    (hscale : η * e * T = Δ)
    (hmean : 2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α +
      2 * (Real.sqrt α * s) ≤ e / 8)
    (hoverhead : η * ((j + 1 : ℕ) *
      (2 * (2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α + 2 * (Real.sqrt α * s)) +
        (4 * Real.sqrt (L * Δ)) * (1 + u))) ≤ Δ / 4)
    (hstep : L * η ≤ e / 2) :
    P.real {ξ | 2 * e * T < ∑ t ∈ Finset.range T,
      nuclearNorm (gradient f (trajectory α η model.sample ξ (x0, 0) 0 t).1)} ≤
        γ / 2 + (j + 1 : ℕ) * (T + 1) * Real.exp (-u) := by
  classical
  let μ := 2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α + 2 * (Real.sqrt α * s)
  let X := fun t ξ => (trajectory α η model.sample ξ (x0, 0) 0 t).1
  let E := {ξ | ∃ t < T, s * Real.sqrt (2 * (T : ℝ) / γ) <
    nuclearNorm (model.sample (X t ξ) (ξ t) - gradient f (X t ξ))}
  let F := {ξ | ∃ (r : Fin (j + 1)) (N : ℕ), N ≤ T ∧
    2 * μ * N + (4 * Real.sqrt (L * Δ)) * u ≤
      ∑ i ∈ Finset.range N, stoppedAlignment f α η Δ B model.sample (x0, 0)
        (r.val + (j + 1) * i) (r.val + (j + 1) * i + j) ξ}
  have hμ : 0 ≤ μ := by dsimp [μ]; positivity
  have hX (t : ℕ) : Measurable[MuonProcess.past t] (X t) := by
    have ht := (MuonProcess.adapted_trajectory α η model.sample
      model.jointly_measurable (x0, 0) 0 t).fst
    rw [Nat.zero_add] at ht
    exact ht
  have hE : P.real E ≤ γ / 2 := MuonProcess.model_noise_max_tail model h hX hs hγ hT
  have hF : P.real F ≤ (j + 1 : ℕ) * (T + 1) * Real.exp (-u) :=
    stopped_residue_prefix_tail model h hL hs hα hα1 hη.le hB hΔ hgrad hlip hmin
      (x0, 0) hgap j T u
  have hsub : {ξ | 2 * e * T < ∑ t ∈ Finset.range T, nuclearNorm (gradient f (X t ξ))} ⊆
      E ∪ F := by
    intro ξ hlarge
    by_contra hbad
    have hnE : ξ ∉ E := fun hh => hbad (Or.inl hh)
    have hnF : ξ ∉ F := fun hh => hbad (Or.inr hh)
    have hnoise (t : ℕ) (ht : t < T) : nuclearNorm
        (model.sample (X t ξ) (ξ t) - gradient f (X t ξ)) ≤
          s * Real.sqrt (2 * (T : ℝ) / γ) := by
      exact le_of_not_gt (fun hh => hnE ⟨t, ht, hh⟩)
    have hr := MuonMomentum.trajectory_tracker_bound hL.le hα.le hα1 hη.le
      (show 0 ≤ s * Real.sqrt (2 * (T : ℝ) / γ) by positivity)
      hlip model.sample ξ x0 T hnoise
    have hres (r : ℕ) (hr : r < j + 1) (N : ℕ) (hN : N ≤ T) :
        (∑ i ∈ Finset.range N, stoppedAlignment f α η Δ B model.sample (x0, 0)
          (r + (j + 1) * i) (r + (j + 1) * i + j) ξ) ≤
            2 * μ * N + (4 * Real.sqrt (L * Δ)) * u := by
      exact (lt_of_not_ge (fun hh => hnF ⟨⟨r, hr⟩, N, hN, hh⟩)).le
    have hm (N : ℕ) (hN : N ≤ T) := training_margin hη.le he hL.le hμ hN
      hscale hmean hoverhead hstep
    have hc := training_control_of_residues hL.le hΔ.le hη.le hμ hu hj hgrad hlip hmin
      model.sample (x0, 0) hgap ξ (fun t ht => (hr t ht).trans hremoteBound) hres
      (fun N hN => (hm N hN).trans (by linarith))
    have hmT := hm T le_rfl
    have hlarge' := mul_lt_mul_of_pos_left hlarge hη
    dsimp [X] at hlarge'
    nlinarith [hc.2]
  calc
    _ ≤ P.real (E ∪ F) := measureReal_mono hsub (by finiteness)
    _ ≤ P.real E + P.real F := measureReal_union_le E F
    _ ≤ _ := add_le_add hE hF

lemma training_tuned_tail {m n : ℕ} {f : Space m n → ℝ} {s L Δ fmin e a D H γ : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    (hL : 0 < L) (hs : 0 ≤ s) (hΔ : 0 < Δ) (he : 0 < e)
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hscale : L * Δ = D * e ^ 2) (hnoise : 4096 * s ^ 2 ≤ a * e ^ 2)
    (hexp : Real.exp H = 1073741824 * a * D / γ)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (x0 : Space m n) (hgap : f x0 - fmin ≤ Δ) :
    let T := ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊
    let η := Δ / (e * T)
    P.real {ξ | 2 * e * T < ∑ t ∈ Finset.range T,
      nuclearNorm (gradient f (trajectory (1 / a) η model.sample ξ (x0, 0) 0 t).1)} ≤ γ := by
  let T := ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊
  let K := ⌈2 * a * H⌉₊
  let η := Δ / (e * T)
  let B := e * H * Real.exp H / 4194304
  let μ := 2 * (1 - 1 / a) ^ K * B + 2 * (L * η) / (1 / a) +
    2 * (Real.sqrt (1 / a) * s)
  have ha0 : 0 < a := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨hTpos, hTlo, hThi⟩ := MuonTuning.training_count_bounds ha hD hH
  obtain ⟨hKpos, hKlo, hKhi⟩ := MuonTuning.lag_count_bounds ha hH
  have ht : 0 < (T : ℝ) := by exact_mod_cast hTpos
  have hη : 0 < η := by dsimp [η]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hα : 0 < 1 / a := by positivity
  have hα1 : 1 / a ≤ 1 := (div_le_one ha0).mpr ha
  have hbud := MuonTuning.training_budget_suffices ha0.le hD0 hTlo
  have hnoise' := MuonTuning.noise_scale he hs ha0 hnoise
  have hdrift := MuonTuning.drift_scale he ha0 hTpos hscale hbud.1
  have hdec : (1 - 1 / a) ^ K * B ≤ e / 64 :=
    (mul_le_mul_of_nonneg_right (MuonTuning.ema_decay ha hKlo) hB).trans
      (MuonTuning.exponential_cutoff he.le le_rfl)
  have hmean : μ ≤ e / 8 := by dsimp [μ]; linarith
  have hstep : L * η ≤ e / 2 := by
    have haη := mul_le_mul_of_nonneg_right ha (show 0 ≤ L * η by positivity)
    have heq : L * η / (1 / a) = a * (L * η) := by simp [div_eq_mul_inv, mul_comm, mul_left_comm]
    change L * η / (1 / a) ≤ e / 64 at hdrift
    rw [heq] at hdrift
    linarith
  have hηscale : η * e * T = Δ := MuonTuning.step_scale he hTpos
  have hLηT : (T : ℝ) * (L * η) = e * D := by
    dsimp [η]
    field_simp
    nlinarith [hscale]
  have hg0 : nuclearNorm (gradient f x0) ≤ 2 * e * D := by
    apply MuonTuning.initial_gradient_scale he.le hD
    have hg := MatrixSmooth.gradient_self_bound hgrad hlip hL hmin x0
    have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * L by positivity)
    nlinarith [hscale]
  have hR := MuonTuning.noise_radius_bound he.le ha hD hH hγ hγ1 hnoise hThi
  have hremote : 2 * (nuclearNorm (gradient f x0) + T * (L * η)) +
      s * Real.sqrt (2 * (T : ℝ) / γ) ≤ B := by
    rw [hLηT]
    exact MuonTuning.tracker_threshold he.le ha hD hH hγ hγ1 hg0 hR hexp
  have hx : 1 ≤ Real.sqrt D := by
    have hh := Real.sq_sqrt hD0
    have hn := Real.sqrt_nonneg D
    nlinarith
  have hsqrt := MuonTuning.sqrt_gap_scale he.le hD0 hscale
  have hov : (K : ℝ) * (2 * μ + 4 * Real.sqrt (L * Δ) * (1 + 6 * H)) ≤
      96 * e * a * Real.sqrt D * H ^ 2 := by
    rw [hsqrt]
    convert residue_overhead_bound he.le ha0.le hx hH hmean (le_refl (6 * H)) hKhi using 1
    ring
  have hoverhead : η * ((K : ℝ) * (2 * μ + 4 * Real.sqrt (L * Δ) * (1 + 6 * H))) ≤ Δ / 4 :=
    (mul_le_mul_of_nonneg_left hov hη.le).trans
      (MuonTuning.overhead_scale he hΔ.le hTpos hbud.2)
  have hj : 1 ≤ K - 1 := by omega
  have hjK : K - 1 + 1 = K := by omega
  have htail := training_sum_tail model h hL hs hα hα1 hη hB hΔ he.le hγ
    (show 0 ≤ 6 * H by positivity) hgrad hlip hmin x0 hgap hj hTpos hremote hηscale
    (by simpa only [hjK] using hmean) (by simpa only [hjK] using hoverhead) hstep
  have hprob := MuonTuning.residue_tail_bound ha hD hH0 hγ hγ1 hTpos hKhi hThi hexp
  change P.real {ξ | 2 * e * T < ∑ t ∈ Finset.range T,
    nuclearNorm (gradient f (trajectory (1 / a) η model.sample ξ (x0, 0) 0 t).1)} ≤ γ
  simp only [hjK] at htail
  linarith

end LongTails.Proofs.MuonTraining
