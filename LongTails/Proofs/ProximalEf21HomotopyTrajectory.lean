import LongTails.Proofs.ProximalEf21Initialization
import LongTails.Proofs.ProximalEf21CountedBudget

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21HomotopyTrajectory

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21StochasticContraction
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21InnerTrajectory
open LongTails.Proofs.ProximalEf21Regularization
open LongTails.Proofs.ProximalEf21Initialization
open LongTails.Proofs.ProximalEf21ScalarCore
open LongTails.Proofs.ProximalEf21Schedule
open LongTails.Proofs.ProximalEf21CountedBudget

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} {L : ℝ}

noncomputable def stageGeometry (G : ConvexCompositeGeometry (E := E) n L) (s : ℕ) :
    InnerGeometry (E := E) n (mu L s) (3 * L) :=
  G.regularized (mu L s) (mu_positive G.hL s) (mu_le_initial G.hL s)

structure HomotopyTrajectory (P : Measure Ω) (G : ConvexCompositeGeometry (E := E) n L)
    (x0 : E) (R σ δ H : ℝ) where
  run : ∀ s, Trajectory P (stageGeometry G s) (1 / (12288 * L)) (gamma L δ) δ
    (σ ^ 2 / (batches L R σ δ s : ℝ)) ((mu L s) • (G.xstar - x0))
  initial_point : ∀ᵐ ω ∂P, (run 0).x 0 ω = x0
  transfer_x : ∀ s, ∀ᵐ ω ∂P,
    (run (s + 1)).x 0 ω = (run s).x (ProximalEf21CountedBudget.length L R δ H s) ω
  transfer_m : ∀ s i, ∀ᵐ ω ∂P,
    (run (s + 1)).m 0 i ω = (run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω
  transfer_v : ∀ s i, ∀ᵐ ω ∂P,
    (run (s + 1)).v 0 i ω = (run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω

namespace HomotopyTrajectory

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (G : ConvexCompositeGeometry (E := E) n L)
variable (x0 : E) {R σ δ H ε : ℝ}
variable (r : HomotopyTrajectory P G x0 R σ δ H)

noncomputable def output (ε : ℝ) (ω : Ω) : E :=
  (r.run (lastStage L R ε)).x
    (ProximalEf21CountedBudget.length L R δ H (lastStage L R ε)) ω

lemma actual_proximal_update (s t : ℕ) :
    ∀ᵐ ω ∂P, (r.run s).x (t + 1) ω =
      G.prox (gamma L δ) ((r.run s).x t ω -
        gamma L δ • workerMean (fun i => (r.run s).v t i ω)) :=
  (r.run s).proximal_update t

lemma actual_momentum_update (s t : ℕ) (i : Fin n) :
    ∀ᵐ ω ∂P, (r.run s).m (t + 1) i ω =
      (1 - mu L s * gamma L δ) • (r.run s).m t i ω +
      (mu L s * gamma L δ) •
        (G.grad i ((r.run s).x (t + 1) ω) +
          (mu L s) • ((r.run s).x (t + 1) ω - x0) + (r.run s).noise t i ω) := by
  filter_upwards [(r.run s).momentum_update t i] with ω hω
  rw [hω]
  congr 2
  change G.grad i ((r.run s).x (t + 1) ω) +
      (mu L s) • ((r.run s).x (t + 1) ω - G.xstar) +
      (mu L s) • (G.xstar - x0) + (r.run s).noise t i ω = _
  simp only [smul_sub]
  abel

lemma auxiliary_scale : (1 / (12288 * L) : ℝ) = 1 / (4096 * (3 * L)) := by ring

lemma execution_scale (hL : 0 < L) (hδ : 0 < δ) :
    0 < gamma L δ ∧ gamma L δ ≤ δ * (1 / (12288 * L)) / 128 := by
  constructor
  · unfold gamma
    positivity
  · unfold gamma
    ring_nf

lemma stage_potential_nonnegative (s t : ℕ) :
    0 ≤ ∫ ω, (stageGeometry G s).potential (1 / (12288 * L))
      ((r.run s).x t ω) (fun i => (r.run s).m t i ω) (fun i => (r.run s).v t i ω) ∂P := by
  have hL : 0 < L := G.hL
  have hscale : mu L s * (1 / (12288 * L)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (mu_le_initial G.hL s)
      (show 0 ≤ 1 / (12288 * L) by positivity)
    have hid : 2 * L * (1 / (12288 * L)) = (1 / 6144 : ℝ) := by
      field_simp [ne_of_gt G.hL]
      <;> ring
    rw [hid] at h
    linarith
  apply integral_nonneg_of_ae
  filter_upwards [(r.run s).feasible t] with ω hx
  exact (stageGeometry G s).potential_nonnegative (by positivity) hscale _ hx _ _

lemma initial_error_integrable (i : Fin n) :
    Integrable (fun ω => ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2) P ∧
    Integrable (fun ω => ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2) P := by
  have hL : 0 < L := G.hL
  have hv := ((r.run 0).v_lp 0 i).sub ((r.run 0).m_lp 0 i)
  have hm := ((r.run 0).m_lp 0 i).sub (memLp_const (G.grad i x0))
  exact ⟨(memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv,
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm⟩

lemma initial_potential_le (hx0 : x0 ∈ G.domain) (hR : 0 < R)
    (hdistance : ‖x0 - G.xstar‖ ≤ R)
    (hH : 8192 * (G.gap x0 + L * R ^ 2 +
      ((n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂P) +
        (n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2 ∂P)) / L) ≤ H) :
    (∫ ω, (stageGeometry G 0).potential (1 / (12288 * L))
      ((r.run 0).x 0 ω) (fun i => (r.run 0).m 0 i ω) (fun i => (r.run 0).v 0 i ω) ∂P) ≤ H := by
  have hL : 0 < L := G.hL
  have hiV : Integrable
      (fun ω => (n : ℝ)⁻¹ * ∑ i, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2) P := by
    exact (integrable_finset_sum _ (fun i _ => (r.initial_error_integrable P G x0 i).1)).const_mul _
  have hiW : Integrable
      (fun ω => (n : ℝ)⁻¹ * ∑ i, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2) P := by
    exact (integrable_finset_sum _ (fun i _ => (r.initial_error_integrable P G x0 i).2)).const_mul _
  have hiR : Integrable (fun ω => 8192 * (G.gap x0 + L * R ^ 2 +
      ((n : ℝ)⁻¹ * (∑ i, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2) +
        (n : ℝ)⁻¹ * (∑ i, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2)) / L)) P := by
    exact ((integrable_const _).add ((hiV.add hiW).div_const L)).const_mul 8192
  have hbound := integral_mono_ae
    ((r.run 0).potential_integrable P (stageGeometry G 0) _ 0) hiR (by
      filter_upwards [r.initial_point] with ω hx
      rw [hx]
      simpa only [stageGeometry, mu, pow_zero, div_one] using
        G.initial_potential_bound x0 hx0 hR hdistance
          (fun i => (r.run 0).m 0 i ω) (fun i => (r.run 0).v 0 i ω))
  have hIV : (∫ ω, (n : ℝ)⁻¹ * ∑ i,
      ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂P) =
      (n : ℝ)⁻¹ * ∑ i, ∫ ω, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂P := by
    rw [integral_const_mul, integral_finset_sum]
    intro i hi
    exact (r.initial_error_integrable P G x0 i).1
  have hIW : (∫ ω, (n : ℝ)⁻¹ * ∑ i,
      ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2 ∂P) =
      (n : ℝ)⁻¹ * ∑ i, ∫ ω, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2 ∂P := by
    rw [integral_const_mul, integral_finset_sum]
    intro i hi
    exact (r.initial_error_integrable P G x0 i).2
  rw [integral_const_mul, integral_add (integrable_const _) ((hiV.add hiW).div_const L),
    integral_const, integral_div, integral_add hiV hiW, hIV, hIW] at hbound
  simpa using hbound.trans hH

lemma within_stage (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdistance : ‖x0 - G.xstar‖ ≤ R) (s k : ℕ) :
    (∫ ω, (stageGeometry G s).potential (1 / (12288 * L))
      ((r.run s).x k ω) (fun i => (r.run s).m k i ω) (fun i => (r.run s).v k i ω) ∂P) ≤
      Real.exp (-mu L s * gamma L δ * k / 512) *
        (∫ ω, (stageGeometry G s).potential (1 / (12288 * L))
          ((r.run s).x 0 ω) (fun i => (r.run s).m 0 i ω) (fun i => (r.run s).v 0 i ω) ∂P) +
      4096 * mu L s * R ^ 2 := by
  have hL : 0 < L := G.hL
  obtain ⟨hγ, hγb⟩ := execution_scale G.hL hδ
  have hμ : 0 < mu L s := mu_positive G.hL s
  have hB : (0 : ℝ) < batches L R σ δ s := by exact_mod_cast batches_positive L R σ δ s
  have hu := (r.run s).inner_contraction_unrolled P (stageGeometry G s) _
    hδ hδ1 (auxiliary_scale (L := L)) hγ hγb (by positivity) k
  have hb := regularization_offset_norm (mu_positive G.hL s).le x0 G.xstar hdistance
  have hb2 : ‖(mu L s) • (G.xstar - x0)‖ ^ 2 ≤ (mu L s) ^ 2 * R ^ 2 := by
    nlinarith [norm_nonneg ((mu L s) • (G.xstar - x0))]
  have hbs := mul_le_mul_of_nonneg_left hb2
    (show 0 ≤ 3072 / mu L s by positivity)
  have hbSimpl : 3072 / mu L s * ((mu L s) ^ 2 * R ^ 2) =
      3072 * mu L s * R ^ 2 := by
    field_simp [ne_of_gt (mu_positive G.hL s)]
    <;> ring
  rw [hbSimpl] at hbs
  have hnoise := mul_le_mul_of_nonneg_left
    (batch_floor (σ := σ) G.hL hR hδ s) (by norm_num : (0 : ℝ) ≤ 1024)
  have hnoiseId : 1024 * gamma L δ * (σ ^ 2 / (batches L R σ δ s : ℝ)) =
      1024 * (gamma L δ * σ ^ 2 / (batches L R σ δ s : ℝ)) := by ring
  rw [hnoiseId] at hu
  have hbId : 3072 / mu L s * ‖(mu L s) • (G.xstar - x0)‖ ^ 2 =
      3072 * ‖(mu L s) • (G.xstar - x0)‖ ^ 2 / mu L s := by ring
  rw [hbId] at hbs
  linarith

lemma stage_transfer (s : ℕ) :
    (∫ ω, (stageGeometry G (s + 1)).potential (1 / (12288 * L))
      ((r.run (s + 1)).x 0 ω) (fun i => (r.run (s + 1)).m 0 i ω)
      (fun i => (r.run (s + 1)).v 0 i ω) ∂P) ≤
      (15 / 7 : ℝ) *
        (∫ ω, (stageGeometry G s).potential (1 / (12288 * L))
          ((r.run s).x (ProximalEf21CountedBudget.length L R δ H s) ω)
          (fun i => (r.run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω)
          (fun i => (r.run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω) ∂P) := by
  have hL : 0 < L := G.hL
  have hμ := mu_positive G.hL (s + 1)
  have h2μ : 2 * mu L (s + 1) ≤ 2 * L := by
    rw [← mu_dyadic]
    exact mu_le_initial G.hL s
  have hscale : (2 * mu L (s + 1)) * (1 / (12288 * L)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h2μ (show 0 ≤ 1 / (12288 * L) by positivity)
    have hi : 2 * L * (1 / (12288 * L)) = (1 / 6144 : ℝ) := by
      field_simp [ne_of_gt G.hL]
      <;> ring
    rw [hi] at h
    linarith
  have hm : ∀ᵐ ω ∂P, ∀ i,
      (r.run (s + 1)).m 0 i ω =
        (r.run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω :=
    (ae_all_iff).mpr (r.transfer_m s)
  have hv : ∀ᵐ ω ∂P, ∀ i,
      (r.run (s + 1)).v 0 i ω =
        (r.run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω :=
    (ae_all_iff).mpr (r.transfer_v s)
  have hpoint : ∀ᵐ ω ∂P,
      (stageGeometry G (s + 1)).potential (1 / (12288 * L))
        ((r.run (s + 1)).x 0 ω) (fun i => (r.run (s + 1)).m 0 i ω)
        (fun i => (r.run (s + 1)).v 0 i ω) ≤
      (15 / 7 : ℝ) * (stageGeometry G s).potential (1 / (12288 * L))
        ((r.run s).x (ProximalEf21CountedBudget.length L R δ H s) ω)
        (fun i => (r.run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω)
        (fun i => (r.run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω) := by
    filter_upwards [r.transfer_x s, hm, hv,
      (r.run s).feasible (ProximalEf21CountedBudget.length L R δ H s)] with ω hx hmω hvω hf
    rw [hx, funext hmω, funext hvω]
    have ht := G.regularized_potential_transfer hμ h2μ (by positivity) hscale
      ((r.run s).x (ProximalEf21CountedBudget.length L R δ H s) ω) hf
      (fun i => (r.run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω)
      (fun i => (r.run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω)
    simpa only [stageGeometry, ← mu_dyadic L s] using ht
  have hi1 := (r.run (s + 1)).potential_integrable P (stageGeometry G (s + 1)) _ 0
  have hi0 := (r.run s).potential_integrable P (stageGeometry G s) _
    (ProximalEf21CountedBudget.length L R δ H s)
  have hi := integral_mono_ae hi1 (hi0.const_mul (15 / 7)) hpoint
  simpa only [integral_const_mul] using hi

lemma stage_invariant (hx0 : x0 ∈ G.domain) (hR : 0 < R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hHnonneg : 0 ≤ H)
    (hdistance : ‖x0 - G.xstar‖ ≤ R)
    (hH : 8192 * (G.gap x0 + L * R ^ 2 +
      ((n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂P) +
        (n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2 ∂P)) / L) ≤ H) :
    ∀ s, (∫ ω, (stageGeometry G s).potential (1 / (12288 * L))
      ((r.run s).x (ProximalEf21CountedBudget.length L R δ H s) ω)
      (fun i => (r.run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω)
      (fun i => (r.run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω) ∂P) ≤
      8192 * mu L s * R ^ 2 := by
  have hL : 0 < L := G.hL
  intro s
  induction s with
  | zero =>
      have hi := r.initial_potential_le P G x0 hx0 hR hdistance hH
      have hu := r.within_stage P G x0 hR hδ hδ1 hdistance 0
        (ProximalEf21CountedBudget.length L R δ H 0)
      have hm := mul_le_mul_of_nonneg_left hi
        (Real.exp_pos (-mu L 0 * gamma L δ *
          (ProximalEf21CountedBudget.length L R δ H 0 : ℝ) / 512)).le
      have hd := initial_length_decay G.hL hR hδ hHnonneg
      linarith
  | succ s ih =>
      have ht := r.stage_transfer P G x0 s
      have hu := r.within_stage P G x0 hR hδ hδ1 hdistance (s + 1)
        (ProximalEf21CountedBudget.length L R δ H (s + 1))
      have hd := positive_length_decay (R := R) (H := H) G.hL hδ (Nat.succ_ne_zero s)
      have hnonneg := r.stage_potential_nonnegative P G x0 (s + 1) 0
      have hd' := mul_le_mul_of_nonneg_right hd hnonneg
      have hdyadic := mu_dyadic L s
      have hμpos := mu_positive G.hL (s + 1)
      have hspos : 0 ≤ 8192 * mu L (s + 1) * R ^ 2 := by positivity
      rw [hdyadic] at ih
      nlinarith only [ht, hu, hd', ih, hspos]

lemma expected_accuracy (hx0 : x0 ∈ G.domain) (hR : 0 < R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hHnonneg : 0 ≤ H)
    (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2)
    (hdistance : ‖x0 - G.xstar‖ ≤ R)
    (hH : 8192 * (G.gap x0 + L * R ^ 2 +
      ((n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂P) +
        (n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2 ∂P)) / L) ≤ H) :
    Integrable (fun ω => G.gap (r.output ε ω)) P ∧
    (∫ ω, G.gap (r.output ε ω) ∂P) ≤ ε := by
  have hL : 0 < L := G.hL
  let s := lastStage L R ε
  let k := ProximalEf21CountedBudget.length L R δ H s
  have hμpos := mu_positive G.hL s
  have hreg (x : E) : (stageGeometry G s).gap x =
      G.gap x + mu L s / 2 * ‖x - G.xstar‖ ^ 2 :=
    G.regularized_gap (mu_positive G.hL s) (mu_le_initial G.hL s) x
  have hxlp := ((r.run s).x_lp k).sub (memLp_const G.xstar)
  have hsq := (memLp_two_iff_integrable_sq_norm hxlp.aestronglyMeasurable).mp hxlp
  have hgapint : Integrable (fun ω => G.gap ((r.run s).x k ω)) P := by
    have hid : (fun ω => G.gap ((r.run s).x k ω)) =
        (fun ω => (stageGeometry G s).gap ((r.run s).x k ω) -
          mu L s / 2 * ‖(r.run s).x k ω - G.xstar‖ ^ 2) := by
      funext ω
      rw [hreg]
      ring
    rw [hid]
    exact ((r.run s).gap_integrable k).sub (hsq.const_mul _)
  have hregularized := integral_mono_ae hgapint ((r.run s).gap_integrable k) (by
    filter_upwards [] with ω
    rw [hreg]
    have hn : 0 ≤ mu L s / 2 * ‖(r.run s).x k ω - G.xstar‖ ^ 2 := by positivity
    linarith)
  have hscale : mu L s * (1 / (12288 * L)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (mu_le_initial G.hL s)
      (show 0 ≤ 1 / (12288 * L) by positivity)
    have hid : 2 * L * (1 / (12288 * L)) = (1 / 6144 : ℝ) := by
      field_simp [ne_of_gt G.hL]
      <;> ring
    rw [hid] at h
    linarith
  have hcontrol := (r.run s).objective_control P (stageGeometry G s) _ (by positivity) hscale k
  have hinv := r.stage_invariant P G x0 hx0 hR hδ hδ1 hHnonneg hdistance hH s
  have hterminal := terminal_regularization_bounds G.hL hR hε hεL
  change ε / (32768 * R ^ 2) < mu L s ∧ mu L s ≤ ε / (16384 * R ^ 2) at hterminal
  have hfin := mul_le_mul_of_nonneg_right hterminal.2 (sq_nonneg R)
  have hid : ε / (16384 * R ^ 2) * R ^ 2 = ε / 16384 := by
    field_simp [ne_of_gt hR]
    <;> ring
  rw [hid] at hfin
  refine ⟨hgapint, ?_⟩
  change (∫ ω, G.gap ((r.run s).x k ω) ∂P) ≤ ε
  nlinarith only [hregularized, hcontrol, hinv, hfin, hε.le]

lemma theorem1_expected_accuracy_and_cost (hx0 : x0 ∈ G.domain) (hR : 0 < R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hHnonneg : 0 ≤ H)
    (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2)
    (hdistance : ‖x0 - G.xstar‖ ≤ R)
    (hH : 8192 * (G.gap x0 + L * R ^ 2 +
      ((n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂P) +
        (n : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).m 0 i ω - G.grad i x0‖ ^ 2 ∂P)) / L) ≤ H) :
    (∀ᵐ ω ∂P, r.output ε ω ∈ G.domain) ∧
    Integrable (fun ω => G.gap (r.output ε ω)) P ∧
    (∫ ω, G.gap (r.output ε ω) ∂P) ≤ ε ∧
    (∑ s ∈ Finset.range (lastStage L R ε + 1),
      batches L R σ δ s * ProximalEf21CountedBudget.length L R δ H s) ≤
      ⌈1152921504606846976 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 +
        (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2)))⌉₊ ∧
    (∑ s ∈ Finset.range (lastStage L R ε + 1), ProximalEf21CountedBudget.length L R δ H s) ≤
      ⌈1152921504606846976 * (L * R ^ 2 / (δ * ε) + Real.log (2 + H / (L * R ^ 2)) / δ)⌉₊ := by
  have hL : 0 < L := G.hL
  have ha := r.expected_accuracy P G x0 hx0 hR hδ hδ1 hHnonneg hε hεL hdistance hH
  refine ⟨(r.run (lastStage L R ε)).feasible _, ha.1, ha.2, ?_, ?_⟩
  · exact counted_sample_budget G.hL hR hδ hδ1 hHnonneg hε hεL
  · exact counted_round_budget G.hL hR hδ hδ1 hHnonneg hε hεL

end HomotopyTrajectory

end LongTails.Proofs.ProximalEf21HomotopyTrajectory
