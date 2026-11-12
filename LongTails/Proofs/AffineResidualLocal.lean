import LongTails.Proofs.AffineResidualMoments

namespace LongTails.Proofs.AffineResidualLocal

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot affine smoothValue gibbsWeight)
open LongTails.Proofs.AffineResidualSaddle
open LongTails.Proofs.AffineResidualRegret
open LongTails.Proofs.AffineResidualTrajectory
open LongTails.Proofs.AffineResidualMoments
open LongTails.Proofs.AffineResidualOutput
open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (C : Set E) (s : Snapshot ι E) (τ μ β D : ℝ)
  (f : ι → E → ℝ) (field : ι → E → E) (initial : State ι E)

omit [CompleteSpace E] in
lemma localPlan_observable_finite_range {X : Type*}
    (L r α : ℝ) (reply : ι × E → ℝ × E) (observe : E → X) :
    (Set.range (fun ω => observe (Program.eval reply (localPlan C s τ μ L r α ω)))).Finite := by
  simp_rw [localPlan, AffineResidualExecution.outputPlan_eval]
  exact AffineResidualSampling.solverState_observable_finite_range C
    (OracleTemplate.SaddlePoint.project C) s τ μ _ _ reply _ _
    (fun state => observe (averageOutput _ s.anchor _ state.2))

omit [CompleteSpace E] in
lemma localPlan_observable_measurable {X : Type*} [MeasurableSpace X]
    (L r α : ℝ) (reply : ι × E → ℝ × E) (observe : E → X) :
    Measurable (fun ω => observe (Program.eval reply (localPlan C s τ μ L r α ω))) := by
  simp_rw [localPlan, AffineResidualExecution.outputPlan_eval]
  exact AffineResidualSampling.solverState_observable_measurable C
    (OracleTemplate.SaddlePoint.project C) s τ μ _ _ reply _ _
    (fun state => observe (averageOutput _ s.anchor _ state.2))

omit [CompleteSpace E] in
lemma localPlan_observable_integrable {X : Type*} [NormedAddCommGroup X]
    (L r α : ℝ) (reply : ι × E → ℝ × E) (observe : E → X)
    (P : Measure (ℕ → StepSeed)) [IsFiniteMeasure P] :
    Integrable (fun ω => observe (Program.eval reply (localPlan C s τ μ L r α ω))) P := by
  simp_rw [localPlan, AffineResidualExecution.outputPlan_eval]
  exact AffineResidualSampling.solverState_observable_integrable C
    (OracleTemplate.SaddlePoint.project C) s τ μ _ _ reply _ _
    (fun state => observe (averageOutput _ s.anchor _ state.2)) P

lemma localOffset_bounds (m : ℕ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) :
    1 ≤ localOffset m τ L r ∧
      4 * ((m : ℝ) * (L * r ^ 2 / 2)) ≤ localOffset m τ L r * τ := by
  have hn := Nat.le_ceil (8 * m * L * r ^ 2 / τ)
  have hc : 0 ≤ (⌈8 * m * L * r ^ 2 / τ⌉₊ : ℝ) := Nat.cast_nonneg _
  have hh := (div_le_iff₀ hτ).mp hn
  dsimp only [localOffset]
  constructor
  · linarith
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (mul_nonneg hL (sq_nonneg r))]

lemma horizon_suffices {β A V α : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hV : 0 ≤ V) (hα : 0 < α) :
    let N := ⌈4 * β * Real.sqrt (A / α) + 64 * V / α + 1⌉₊
    0 < N ∧ 3 * β ^ 2 * A / (N : ℝ) ^ 2 + 32 * V / N ≤ α := by
  let N := ⌈4 * β * Real.sqrt (A / α) + 64 * V / α + 1⌉₊
  have hn := Nat.le_ceil (4 * β * Real.sqrt (A / α) + 64 * V / α + 1)
  have hfirst : 0 ≤ 4 * β * Real.sqrt (A / α) := by positivity
  have hsecond : 0 ≤ 64 * V / α := by positivity
  have hN : 0 < (N : ℝ) := by dsimp only [N]; linarith
  have hs : 4 * β * Real.sqrt (A / α) ≤ (N : ℝ) := by dsimp only [N]; linarith
  have hv : 64 * V / α ≤ (N : ℝ) := by dsimp only [N]; linarith
  have hsq := (sq_le_sq₀ hfirst hN.le).mpr hs
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hA hα.le)] at hsq
  have hm := mul_le_mul_of_nonneg_right hsq hα.le
  have he : 4 ^ 2 * β ^ 2 * (A / α) * α = 16 * β ^ 2 * A := by field_simp; ring
  rw [he] at hm
  have h1 : 3 * β ^ 2 * A / (N : ℝ) ^ 2 ≤ 3 * α / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    nlinarith
  have h2 : 32 * V / (N : ℝ) ≤ α / 2 := by
    apply (div_le_iff₀ hN).mpr
    have hh := (div_le_iff₀ hα).mp hv
    nlinarith
  refine ⟨by exact_mod_cast hN, ?_⟩
  change 3 * β ^ 2 * A / (N : ℝ) ^ 2 + 32 * V / N ≤ α
  linarith

lemma weighted_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → ℝ) (e : Ω → ℕ → ℝ)
    {β A V : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (N : ℕ) (hN : 0 < N) (hg : Integrable g P)
    (he : ∀ k, Integrable (fun ω => e ω k) P)
    (hm : ∀ k, (∫ ω, e ω k ∂P) ≤ 16 * V)
    (hb : ∀ ω, (∑ k ∈ Finset.range N, iterationWeight β k) * g ω ≤
      3 * β ^ 2 / 2 * A + ∑ k ∈ Finset.range N, e ω k) :
    (∫ ω, g ω ∂P) ≤ 3 * β ^ 2 * A / (N : ℝ) ^ 2 + 32 * V / N := by
  let W := ∑ k ∈ Finset.range N, iterationWeight β k
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hw := weight_sum_lower hβ N
  have hW : 0 < W := lt_of_lt_of_le (by positivity) hw
  have hs : Integrable (fun ω => ∑ k ∈ Finset.range N, e ω k) P :=
    integrable_finsetSum _ (fun k _ => he k)
  have hi := integral_mono (hg.const_mul W)
    ((integrable_const (3 * β ^ 2 / 2 * A)).add hs) hb
  simp only [Pi.add_apply] at hi
  simp only [integral_const_mul, integral_add (integrable_const _) hs,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_finsetSum _ (fun k _ => he k)] at hi
  have hm' := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hm k)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hm'
  have htop : 0 ≤ 3 * β ^ 2 / 2 * A + (N : ℝ) * (16 * V) := by positivity
  have hfirst : (∫ ω, g ω ∂P) ≤ (3 * β ^ 2 / 2 * A + N * (16 * V)) / W := by
    apply (le_div_iff₀ hW).mpr
    nlinarith
  have hsecond := div_le_div_of_nonneg_left htop (by positivity : 0 < (N : ℝ) ^ 2 / 2) hw
  apply hfirst.trans (hsecond.trans_eq ?_)
  field_simp
  ring

lemma output_gap_pathwise (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 1 ≤ β) (hD : 0 ≤ D)
    (hcap : 4 * ((Fintype.card ι : ℝ) * D) ≤ β * τ)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hi : initial.point ∈ C) (hip : ∀ i, initial.probability i = (Fintype.card ι : ℝ)⁻¹)
    (hres : ∀ x ∈ C, ∀ i, 0 ≤ D - (f i x - affine s i x) ∧ D - (f i x - affine s i x) ≤ D)
    (z : E) (hz : z ∈ C) {r : ℝ} (hdist : ‖z - initial.point‖ ≤ 2 * r)
    (N : ℕ) (hN : 0 < N) (ω : ℕ → StepSeed) :
    let out := Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
      (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial ω N)
    (∑ k ∈ Finset.range N, iterationWeight β k) *
      (regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor out -
        regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor z) ≤
      3 * β ^ 2 / 2 * (2 * μ * r ^ 2 + τ * Real.log (Fintype.card ι)) +
        ∑ k ∈ Finset.range N, remainder C s τ μ β D f field initial ω k := by
  let v := predicted C s τ μ β D f field initial ω
  let W := ∑ k ∈ Finset.range N, iterationWeight β k
  let out := Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
    (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial ω N)
  let u : State ι E := ⟨z, gibbsWeight τ (fun i => f i out)⟩
  have hβ' : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have hW : 0 < W := Finset.sum_pos (fun k _ => weight_positive hβ' k)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
  have hx : out = W⁻¹ • ∑ k ∈ Finset.range N, iterationWeight β k • (v k).point := by
    dsimp only [out]
    rw [outputPlan_eq_average]
    simp only [averageOutput, ite_eq_right (Nat.ne_of_gt hN)]
    rfl
  have hu : u ∈ kernelDomain C := ⟨hz,
    fun i => (AffineSoftmaxResidual.gibbsWeight_pos τ (fun i => f i out) i).le,
    AffineSoftmaxResidual.gibbsWeight_sum τ (fun i => f i out)⟩
  have hcomp := weighted_output_gap_sum hconv f hf s.anchor hμ.le hτ
    (fun k : Fin N => v k) (fun k : Fin N => iterationWeight β k)
    (fun k => (weight_positive hβ' k).le)
    (by simpa only [Fin.sum_univ_eq_sum_range] using hW)
    (fun k => predicted_mem C s τ μ β D f field initial ω hC hne k)
    (fun k i => (predicted_probability_pos C s τ μ β D f field initial ω k i).le)
    (fun k => predicted_probability_sum C s τ μ β D f field initial ω k) z
  dsimp only at hcomp
  rw [Fin.sum_univ_eq_sum_range (fun k => iterationWeight β k • (v k).point)] at hcomp
  simp only [Fin.sum_univ_eq_sum_range] at hcomp
  dsimp only [W] at hx
  rw [← hx] at hcomp
  rw [Fin.sum_univ_eq_sum_range (fun k => iterationWeight β k *
    AffineResidualGap.saddleGap f s.anchor μ τ (v k) u)] at hcomp
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hi' : ∀ i, 0 < initial.probability i := fun i => by rw [hip]; positivity
  have hisum : ∑ i, initial.probability i = 1 := by
    simp_rw [hip]
    simp [nsmul_eq_mul, hcard.ne']
  have hp := pathwise_gap C s τ μ β D f field initial ω hC hne hconv hμ hτ hβ hD hcap hf hg
    hi hi' hisum (fun k => hres _ (predicted_mem C s τ μ β D f field initial ω hC hne k)) N u hu
  have hinit := uniform_initial_potential hμ.le hτ.le u initial hu.2.1 hu.2.2 hip hdist
  have hiBound := mul_le_mul_of_nonneg_left hinit (by positivity : 0 ≤ 3 * β ^ 2 / 2)
  change W * (regularized _ μ s.anchor out - regularized _ μ s.anchor z) ≤ _
  change W * (regularized _ μ s.anchor out - regularized _ μ s.anchor z) ≤
    ∑ k ∈ Finset.range N, iterationWeight β k * AffineResidualGap.saddleGap f s.anchor μ τ (v k) u at hcomp
  change (∑ k ∈ Finset.range N, iterationWeight β k * AffineResidualGap.saddleGap f s.anchor μ τ (v k) u) ≤
    3 * β ^ 2 / 2 * potential μ τ u initial +
      ∑ k ∈ Finset.range N, remainder C s τ μ β D f field initial ω k at hp
  linarith

lemma output_gap_expected (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 1 ≤ β) (hD : 0 ≤ D)
    (hcap : 4 * ((Fintype.card ι : ℝ) * D) ≤ β * τ)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hi : initial.point ∈ C) (hip : ∀ i, initial.probability i = (Fintype.card ι : ℝ)⁻¹)
    (hres : ∀ x ∈ C, ∀ i, 0 ≤ D - (f i x - affine s i x) ∧ D - (f i x - affine s i x) ≤ D)
    (z : E) (hz : z ∈ C) {r : ℝ} (hdist : ‖z - initial.point‖ ≤ 2 * r)
    {M : ℝ} (hgrad : ∀ x ∈ C, ∀ i, ‖field i x - s.field i‖ ≤ M)
    (N : ℕ) (hN : 0 < N) :
    (∫ ω, regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor
      (Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
        (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial ω N)) -
      regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor z
      ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤
      3 * β ^ 2 * (2 * μ * r ^ 2 + τ * Real.log (Fintype.card ι)) / (N : ℝ) ^ 2 +
        32 * (M ^ 2 / μ + (Fintype.card ι : ℝ) * D ^ 2 / τ) / N := by
  let P : Measure (ℕ → StepSeed) := Measure.infinitePi fun _ : ℕ =>
    (volume : Measure unitInterval).prod volume
  let F := regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor
  have hgout : Integrable (fun ω => F (Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
      (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial ω N)) - F z) P := by
    simp_rw [AffineResidualExecution.outputPlan_eval]
    exact AffineResidualSampling.solverState_observable_integrable C
      (OracleTemplate.SaddlePoint.project C) s τ μ β D
      (fun q => (f q.1 q.2, field q.1 q.2)) initial N
      (fun state => F (averageOutput β initial.point N state.2) - F z) P
  have hlog : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by
    exact_mod_cast Fintype.card_pos)
  have hmoment := remainder_moment C s τ μ β D f field initial hC hne hμ hτ hgrad hres
  exact weighted_integral_bound P _ (remainder C s τ μ β D f field initial)
    (by linarith) (by positivity) (by positivity) N hN hgout
    (fun k => (hmoment k).1) (fun k => (hmoment k).2)
    (fun ω => output_gap_pathwise C s τ μ β D f field initial hC hne hconv hμ hτ hβ hD
      hcap hf hg hi hip hres z hz hdist N hN ω)

lemma smooth_output_gap_expected (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hμ : 0 < μ) (hτ : 0 < τ) (hβ : 1 ≤ β) {L r : ℝ} (hL : 0 ≤ L) (hD : D = L * r ^ 2 / 2)
    (hcap : 4 * ((Fintype.card ι : ℝ) * D) ≤ β * τ)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hi : initial.point ∈ C) (hip : ∀ i, initial.probability i = (Fintype.card ι : ℝ)⁻¹)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖field i x - field i y‖ ≤ L * ‖x - y‖)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = field i s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (z : E) (hz : z ∈ C)
    (N : ℕ) (hN : 0 < N) :
    (∫ ω, regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor
      (Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
        (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial ω N)) -
      regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor z
      ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤
      3 * β ^ 2 * (2 * μ * r ^ 2 + τ * Real.log (Fintype.card ι)) / (N : ℝ) ^ 2 +
        32 * ((L * r) ^ 2 / μ + (Fintype.card ι : ℝ) * D ^ 2 / τ) / N := by
  have hb (x : E) (hx : x ∈ C) (i : ι) :=
    AffineResidualGap.snapshot_residual_bounds s f field hL hf hg hlip ha hvalue hfield
      hx (hradius x hx) i
  have hd : ‖z - initial.point‖ ≤ 2 * r := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z s.anchor initial.point
    rw [norm_sub_rev s.anchor initial.point] at ht
    linarith [hradius z hz, hradius initial.point hi]
  apply output_gap_expected C s τ μ β D f field initial hC hne hconv hμ hτ hβ
    (by rw [hD]; positivity) hcap hf hg hi hip _ z hz hd _ N hN
  · intro x hx i
    constructor <;> linarith [(hb x hx i).1.1, (hb x hx i).1.2]
  · intro x hx i
    exact (hb x hx i).2

omit [CompleteSpace E] in
lemma outputPlan_mem (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hβ : 0 < β) (N : ℕ) (hN : 0 < N) (ω : ℕ → StepSeed) :
    Program.eval (fun q => (f q.1 q.2, field q.1 q.2))
      (outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ β D initial ω N) ∈ C := by
  rw [outputPlan_eq_average]
  apply averageOutput_mem hconv hβ initial.point N hN
  intro k _
  exact predicted_mem C s τ μ β D f field initial ω hC hne k

lemma localSteps_pos (m : ℕ) [NeZero m] {τ μ L r α : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hα : 0 < α) :
    0 < localSteps m τ μ L r α := by
  have hb := (localOffset_bounds m hτ hL (r := r)).1
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  exact (horizon_suffices (by linarith : 0 ≤ localOffset m τ L r)
    (by positivity : 0 ≤ 2 * μ * r ^ 2 + τ * Real.log m)
    (by positivity : 0 ≤ (L * r) ^ 2 / μ + (m : ℝ) * (L * r ^ 2 / 2) ^ 2 / τ) hα).1

omit [CompleteSpace E] in
lemma localPlan_mem (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {L r α : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hα : 0 < α)
    (ω : ℕ → StepSeed) :
    Program.eval (fun q => (f q.1 q.2, field q.1 q.2)) (localPlan C s τ μ L r α ω) ∈ C := by
  have hb := (localOffset_bounds (Fintype.card ι) hτ hL (r := r)).1
  exact outputPlan_mem C s τ μ _ _ f field _ hC hne hconv (by linarith)
    _ (localSteps_pos (Fintype.card ι) hτ hμ hL hα) ω

lemma localPlan_accuracy (hC : IsCompact C) (hconv : Convex ℝ C)
    {L r α : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hα : 0 < α)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖field i x - field i y‖ ≤ L * ‖x - y‖)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = field i s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (z : E) (hz : z ∈ C) :
    (∫ ω, regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor
      (Program.eval (fun q => (f q.1 q.2, field q.1 q.2)) (localPlan C s τ μ L r α ω)) -
      regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor z
      ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ α := by
  have hb := localOffset_bounds (Fintype.card ι) hτ hL (r := r)
  have hlog : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by
    exact_mod_cast Fintype.card_pos)
  have hn := horizon_suffices (by linarith : 0 ≤ localOffset (Fintype.card ι) τ L r)
    (by positivity : 0 ≤ 2 * μ * r ^ 2 + τ * Real.log (Fintype.card ι))
    (by positivity : 0 ≤ (L * r) ^ 2 / μ + (Fintype.card ι : ℝ) * (L * r ^ 2 / 2) ^ 2 / τ) hα
  have hh := smooth_output_gap_expected C s τ μ (localOffset (Fintype.card ι) τ L r)
    (L * r ^ 2 / 2) f field ⟨s.anchor, fun _ => (Fintype.card ι : ℝ)⁻¹⟩
    hC ⟨s.anchor, ha⟩ hconv hμ hτ hb.1 hL rfl hb.2 hf hg ha (fun _ => rfl)
    hlip ha hvalue hfield hradius z hz (localSteps (Fintype.card ι) τ μ L r α) hn.1
  exact hh.trans hn.2

lemma localPlan_distance [MeasurableSpace E] [BorelSpace E]
    (hC : IsCompact C) (hconv : Convex ℝ C)
    {L G r α : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hα : 0 < α)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (z : E) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor) C z) :
    (∫ ω, ‖Program.eval (fun q => (f q.1 q.2, gradient (f q.1) q.2))
      (localPlan C s τ μ L r α ω) - z‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ 2 * α / μ := by
  let Q : ProbabilityMeasure (ℕ → StepSeed) :=
    ⟨Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval).prod volume), inferInstance⟩
  have hF := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hconv hf hg hbound
  have hFg x (hx : x ∈ C) : HasGradientAt (fun y => smoothValue τ (fun i => f i y))
      (gradient (fun y => smoothValue τ (fun i => f i y)) x) x := by
    have h := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
      hτ.ne' (fun i => hg i x hx)
    rw [h.gradient]
    exact h
  exact AffineSoftmaxRegularization.expected_regularized_distance_le Q hC hF hFg hμ s.anchor hz hmin
    _ (localPlan_observable_measurable C s τ μ L r α _ id)
    (fun ω => localPlan_mem C s τ μ f (fun i => gradient (f i)) hC ⟨s.anchor, ha⟩ hconv
      hμ hτ hL hα ω)
    (localPlan_accuracy C s τ μ f (fun i => gradient (f i)) hC hconv hμ hτ hL hα
      hf hg hlip ha hvalue hfield hradius z hz)

lemma proxPlan_accuracy (m : ℕ) [NeZero m] (f : Fin m → E → ℝ) (field : Fin m → E → E)
    (hC : IsCompact C) (hconv : Convex ℝ C) (center : E) (hc : center ∈ C)
    {L r α : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hα : 0 < α)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖field i x - field i y‖ ≤ L * ‖x - y‖)
    (hradius : ∀ x ∈ C, ‖x - center‖ ≤ r) (z : E) (hz : z ∈ C)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, field i x)) :
    (∫ ω, regularized (fun y => smoothValue τ (fun i => f i y)) μ center
      (Program.eval reply (proxPlan m C center τ μ L r α ω)) -
      regularized (fun y => smoothValue τ (fun i => f i y)) μ center z
      ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ α := by
  have he (ω : ℕ → StepSeed) := AffineResidualExecution.eval_eq_of_queriesWithin reply
    (fun q => (f q.1 q.2, field q.1 q.2)) (fun q => q.2 ∈ C)
    (proxPlan m C center τ μ L r α ω)
    (AffineResidualExecution.proxPlan_queriesWithin m hC center hc τ μ L r α ω reply)
    (fun q hq => hreply q.1 q.2 hq)
  simp_rw [he, proxPlan, Program.eval_bind, AffineSoftmaxExecution.cachePlan_eval]
  exact localPlan_accuracy C ⟨center, fun i => f i center, fun i => field i center⟩ τ μ f field
    hC hconv hμ hτ hL hα hf hg hlip hc (fun _ => rfl) (fun _ => rfl) hradius z hz

end LongTails.Proofs.AffineResidualLocal
