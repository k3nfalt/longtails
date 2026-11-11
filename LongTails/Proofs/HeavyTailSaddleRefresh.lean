import LongTails.Proofs.HeavyTailSaddleExecution
import LongTails.Proofs.PowerMirrorMoments
import LongTails.Proofs.RobustPilotConfidence

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailSaddleRefresh

lemma refresh_contraction : (31 / 32 : ℝ) ^ 256 ≤ 1 / 156 := by
  norm_num

lemma deterministic_radius {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : E → E} {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hl : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (u start : E) (hu : G u = 0) (hstart : ‖start - u‖ ≤ 13 * R / 8) :
    ‖(fun x => x - (1 / (4 * L)) • G x)^[256] start - u‖ ≤ R / 96 := by
  calc
    _ ≤ (31 / 32 : ℝ) ^ 256 * ‖start - u‖ :=
      HeavyTailSaddleGeometry.fast_orbit_distance hL hm hl u start hu 256
    _ ≤ (31 / 32 : ℝ) ^ 256 * (13 * R / 8) := by gcongr
    _ ≤ (1 / 156 : ℝ) * (13 * R / 8) :=
      mul_le_mul_of_nonneg_right refresh_contraction (by positivity)
    _ = R / 96 := by ring

lemma batch_tuning {p r : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hr : 0 ≤ r) :
    let n := 1 + ⌈((2 : ℝ) ^ 24 * r ^ p) ^ (1 / (p - 1))⌉₊
    0 < n ∧ 1152 * (24 : ℝ) ^ p * r ^ p / (n : ℝ) ^ (p - 1) ≤ 1 / 16 := by
  intro n
  have hn : 0 < n := by dsimp [n]; omega
  have hbase : 0 ≤ (2 : ℝ) ^ 24 * r ^ p := by positivity
  have he : ((2 : ℝ) ^ 24 * r ^ p) ^ (1 / (p - 1)) ≤ (n : ℝ) := by
    have hh := Nat.le_ceil (((2 : ℝ) ^ 24 * r ^ p) ^ (1 / (p - 1)))
    dsimp [n]
    push_cast
    linarith
  have hpower := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) he
    (show 0 ≤ p - 1 by linarith)
  rw [one_div, Real.rpow_inv_rpow hbase (by linarith : p - 1 ≠ 0)] at hpower
  have h24 : (24 : ℝ) ^ p ≤ 576 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 24) hp2
    norm_num [Real.rpow_two] at hh
    exact hh
  have hc : 16 * 1152 * (24 : ℝ) ^ p ≤ (2 : ℝ) ^ 24 := by norm_num at ⊢; linarith
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr p)
  refine ⟨hn, ?_⟩
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)).mpr
  nlinarith only [hh, hpower]

lemma noise_tuning {p σ L R : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hL : 0 < L) (hR : 0 < R) :
    let n := LongTails.Algorithms.HeavyTailSaddleEstimator.refreshBatch p σ L R
    0 < n ∧ 1152 * (1 / (4 * L)) ^ p * σ ^ p / (n : ℝ) ^ (p - 1) ≤
      (R / 96) ^ p / 16 := by
  intro n
  have hb := batch_tuning hp hp2 (div_nonneg hσ (mul_pos hL hR).le)
  change 0 < n ∧ 1152 * (24 : ℝ) ^ p * (σ / (L * R)) ^ p / (n : ℝ) ^ (p - 1) ≤ 1 / 16 at hb
  have hscale : (R / 96) ^ p * ((24 : ℝ) ^ p * (σ / (L * R)) ^ p) =
      (1 / (4 * L)) ^ p * σ ^ p := by
    calc
      _ = ((R / 96) * 24 * (σ / (L * R))) ^ p := by
        rw [Real.mul_rpow (by positivity) (div_nonneg hσ (mul_pos hL hR).le),
          Real.mul_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 24)]
        ring
      _ = ((1 / (4 * L)) * σ) ^ p := by congr 1; field_simp; ring
      _ = _ := Real.mul_rpow (by positivity) hσ
  refine ⟨hb.1, ?_⟩
  calc
    _ = (R / 96) ^ p * (1152 * (24 : ℝ) ^ p * (σ / (L * R)) ^ p /
        (n : ℝ) ^ (p - 1)) := by rw [mul_assoc, ← hscale]; ring
    _ ≤ (R / 96) ^ p * (1 / 16) :=
      mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg (by positivity) _)
    _ = _ := by ring

lemma replica_confidence {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let M := LongTails.Algorithms.HeavyTailSaddleEstimator.refreshRepetitions δ
    0 < M ∧ (1 / 2 : ℝ) ^ M ≤ δ := by
  intro M
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  have hM : 4 * Real.log (1 / δ) ≤ (M : ℝ) := by
    have hh := Nat.le_ceil (4 * Real.log (1 / δ))
    dsimp [M, LongTails.Algorithms.HeavyTailSaddleEstimator.refreshRepetitions]
    push_cast
    linarith
  refine ⟨by dsimp [M, LongTails.Algorithms.HeavyTailSaddleEstimator.refreshRepetitions]; omega, ?_⟩
  have hh : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have he := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  calc
    _ ≤ Real.exp (-(1 / 2 : ℝ)) ^ M := pow_le_pow_left₀ (by norm_num) hh M
    _ = Real.exp ((M : ℝ) * (-(1 / 2 : ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.mpr (by linarith)
    _ = δ := by
      rw [Real.log_div one_ne_zero hδ.ne', Real.log_one]
      simpa using Real.exp_log hδ

lemma center_tail {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → E} (hX : Measurable X)
    (u θ : E) {R p : ℝ} (hR : 0 < R) (hp : 0 < p)
    (hθ : ‖θ - u‖ ≤ R / 96)
    (hpi : Integrable (fun ω => ‖X ω - θ‖ ^ p) P)
    (hbound : (∫ ω, ‖X ω - θ‖ ^ p ∂P) ≤ (R / 96) ^ p / 16) (M : ℕ) :
    (Measure.pi fun _ : Fin M => P)
      {ξ | R / 16 < ‖OracleTemplate.RobustGradient.pilotCenter (R / 8) (fun i => X (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ M) := by
  have hnoise := PowerMirrorMoments.norm_tail_le_power hp (show 0 < R / 96 by positivity)
    hpi hbound
  have hsub : {ω | R / 48 < ‖X ω - u‖} ⊆ {ω | R / 96 < ‖X ω - θ‖} := by
    intro ω hω
    have hh := norm_sub_le_norm_sub_add_norm_sub (X ω) θ u
    change R / 48 < ‖X ω - u‖ at hω
    change R / 96 < ‖X ω - θ‖
    linarith
  have hb : P.real {ω | R / 48 < ‖X ω - u‖} ≤ 1 / 16 := by
    have hh := (measureReal_mono (μ := P) hsub).trans hnoise
    have he : ((R / 96) ^ p / 16) / (R / 96) ^ p = 1 / 16 := by
      field_simp [(Real.rpow_pos_of_pos (show 0 < R / 96 by positivity) p).ne']
    simpa only [he] using hh
  have hh := OracleTemplate.RobustGradient.pilotCenter_failure_probability (P := P) hX u (R / 8)
    (by convert hb using 1; norm_num [div_div]) M
  convert hh using 1; norm_num [div_div]

lemma prefix_replica_law {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) p P) {F : (ℕ → Ω) → E} (hF : Measurable F)
    (K M : ℕ) (hprefix : ∀ ξ ζ, (∀ j < K, ξ j = ζ j) → F ξ = F ζ) :
    ProbabilityTheory.IdentDistrib
      (fun ξ : ℕ → Ω => fun i : Fin M => F (fun j => ξ (K * i.val + j)))
      (fun ξ : Fin M → (ℕ → Ω) => fun i => F (ξ i))
      P (Measure.pi fun _ : Fin M => P) := by
  classical
  let pad : Ω := Classical.choice (nonempty_of_isProbabilityMeasure p)
  let extend := fun (v : Fin K → Ω) (j : ℕ) => if hj : j < K then v ⟨j, hj⟩ else pad
  have hext : Measurable extend := by
    apply Measurable.of_eval
    intro j
    dsimp [extend]
    split_ifs <;> fun_prop
  let G := fun (v : Fin M → Fin K → Ω) => fun i => F (extend (v i))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (hext.comp (measurable_pi_apply i))
  have heq (ξ : ℕ → Ω) : F (extend (fun j : Fin K => ξ j)) = F ξ := by
    apply hprefix
    intro j hj
    simp [extend, hj]
  let Q := Measure.pi fun _ : Fin K => p
  have hb := OracleTemplate.FiniteVariance.infinite_block_law p P hIID.independent hIID.marginal K
  have hi := (OracleTemplate.StochasticGeneralized.infinitePi_iid Q).independent.precomp
    (g := fun i : Fin M => i.val) Fin.val_injective
  have hp : MeasurePreserving (fun ξ : ℕ → Fin K → Ω => fun i : Fin M => ξ i.val)
      (Measure.infinitePi fun _ : ℕ => Q) (Measure.pi fun _ : Fin M => Q) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [(OracleTemplate.StochasticGeneralized.infinitePi_iid Q).marginal] using
      hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply i.val).aemeasurable)
  have ha := hp.comp hb
  have hpre : P.map (fun ξ : ℕ → Ω => fun j : Fin K => ξ j) = Q := by
    have hi := hIID.independent.precomp (g := fun j : Fin K => j.val) Fin.val_injective
    simpa only [hIID.marginal] using
      hi.map_fun_eq_pi_map (fun j : Fin K => (hIID.measurable j.val).aemeasurable)
  have hb' : MeasurePreserving
      (fun ξ : Fin M → (ℕ → Ω) => fun i : Fin M => fun j : Fin K => ξ i j)
      (Measure.pi fun _ : Fin M => P) (Measure.pi fun _ : Fin M => Q) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
      (fun ξ : ℕ → Ω => fun j : Fin K => ξ j)).aemeasurable)]
    simp only [hpre]
  have hd : ProbabilityTheory.IdentDistrib
      (fun ξ : ℕ → Ω => fun i : Fin M => fun j : Fin K => ξ (i.val * K + j.val))
      (fun ξ : Fin M → (ℕ → Ω) => fun i : Fin M => fun j : Fin K => ξ i j)
      P (Measure.pi fun _ : Fin M => P) :=
    ⟨ha.measurable.aemeasurable, hb'.measurable.aemeasurable, ha.map_eq.trans hb'.map_eq.symm⟩
  have hh := hd.comp hG
  convert hh using 1
  · funext ξ i
    simpa only [Function.comp_def, G, Nat.mul_comm] using
      (heq (fun j => ξ (K * i.val + j))).symm
  · funext ξ i
    exact (heq (ξ i)).symm

lemma endpoint_confidence {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P)
    {field : E → E} {oracle : E → Ω → E}
    (hf : Measurable field) (ho : Measurable (Function.uncurry oracle))
    {L R p σ δ : ℝ} (hL : 0 < L) (hR : 0 < R) (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field x - field y, x - y⟫)
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hoi : ∀ x, Integrable (oracle x) pnoise)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - field x‖ ^ p) pnoise)
    (homean : ∀ x, (∫ ω, oracle x ω ∂pnoise) = field x)
    (hoV : ∀ x, (∫ ω, ‖oracle x ω - field x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (u start : E) (hu : field u = 0) (hstart : ‖start - u‖ ≤ 13 * R / 8) :
    let n := LongTails.Algorithms.HeavyTailSaddleEstimator.refreshBatch p σ L R
    let step := fun x (ζ : Fin n → Ω) =>
      x - (1 / (4 * L)) • ((n : ℝ)⁻¹ • ∑ i : Fin n, oracle x (ζ i))
    let endpoint := fun ξ : ℕ → Ω => HeavyTailedProductProcess.trajectory step 256 start
      (fun k (i : Fin n) => ξ (k * n + i.val))
    let M := LongTails.Algorithms.HeavyTailSaddleEstimator.refreshRepetitions δ
    P {ξ | R / 16 < ‖OracleTemplate.RobustGradient.pilotCenter (R / 8)
      (fun i : Fin M => endpoint (fun j => ξ (256 * n * i.val + j))) - u‖} ≤
        ENNReal.ofReal δ := by
  intro n step endpoint M
  let T := fun x => x - (1 / (4 * L)) • field x
  let θ := T^[256] start
  have ht := noise_tuning hp hp2 hσ hL hR
  change 0 < n ∧ 1152 * (1 / (4 * L)) ^ p * σ ^ p / (n : ℝ) ^ (p - 1) ≤
    (R / 96) ^ p / 16 at ht
  have hc0 (N : ℕ) :
      Integrable (fun ξ => ‖HeavyTailedProductProcess.trajectory step N start
        (fun k (i : Fin n) => ξ (k * n + i.val)) - T^[N] start‖ ^ p) P ∧
      (∫ ξ, ‖HeavyTailedProductProcess.trajectory step N start
        (fun k (i : Fin n) => ξ (k * n + i.val)) - T^[N] start‖ ^ p ∂P) ≤
        192 * (1 / (4 * L)) ^ p * (6 * σ ^ p / (n : ℝ) ^ (p - 1)) := by
    have hc := HeavyTailSaddleMultilevel.coupled_batched_gradient_moment pnoise P hIID
      hf ho hL hp.le hp2 (Real.rpow_nonneg hσ p) hm hl hoi hop homean hoV n ht.1 N start
    let C := fun ξ : ℕ → Ω =>
      let blocks := fun k (i : Fin n) => ξ (k * n + i.val)
      ‖(HeavyTailedProductProcess.trajectory (fun (z : E × E) ζ => (step z.1 ζ, T z.2))
        N (start, start) blocks).1 -
        (HeavyTailedProductProcess.trajectory (fun (z : E × E) ζ => (step z.1 ζ, T z.2))
          N (start, start) blocks).2‖ ^ p
    change Integrable C P ∧ (∫ ξ, C ξ ∂P) ≤
      192 * (1 / (4 * L)) ^ p * (6 * σ ^ p / (n : ℝ) ^ (p - 1)) at hc
    dsimp [C] at hc
    simp_rw [HeavyTailSaddleExecution.coupled_trajectory_fst,
      HeavyTailSaddleExecution.coupled_trajectory_snd] at hc
    exact hc
  have hc := hc0 256
  change Integrable (fun ξ => ‖endpoint ξ - θ‖ ^ p) P ∧
    (∫ ξ, ‖endpoint ξ - θ‖ ^ p ∂P) ≤
      192 * (1 / (4 * L)) ^ p * (6 * σ ^ p / (n : ℝ) ^ (p - 1)) at hc
  have hbound : (∫ ξ, ‖endpoint ξ - θ‖ ^ p ∂P) ≤ (R / 96) ^ p / 16 := by
    apply hc.2.trans
    convert ht.2 using 1; ring
  have hs : Measurable (Function.uncurry step) := by dsimp [step, Function.uncurry]; fun_prop
  have hblocks : Measurable (fun ξ : ℕ → Ω => fun k (i : Fin n) => ξ (k * n + i.val)) := by
    fun_prop
  have he0 (N : ℕ) : Measurable (fun ξ : ℕ → Ω =>
      HeavyTailedProductProcess.trajectory step N start
        (fun k (i : Fin n) => ξ (k * n + i.val))) :=
    (HeavyTailedProductProcess.trajectory_measurable hs N).comp
      (measurable_const.prodMk hblocks)
  have he : Measurable endpoint := he0 256
  have hdet : ‖θ - u‖ ≤ R / 96 := deterministic_radius hL hR.le hm hl u start hu hstart
  have htail := center_tail P he u θ hR (show 0 < p by linarith) hdet hc.1 hbound M
  have hideal := htail.trans (ENNReal.ofReal_le_ofReal (replica_confidence hδ hδ1).2)
  have hlaw := prefix_replica_law pnoise P hIID he (256 * n) M (by
    intro ξ ζ hξ
    apply HeavyTailSaddleExecution.trajectory_prefix_congr
    intro k hk
    funext i
    apply hξ
    calc
      k * n + i.val < k * n + n := Nat.add_lt_add_left i.isLt _
      _ = (k + 1) * n := by ring
      _ ≤ 256 * n := Nat.mul_le_mul_right n hk)
  have hcenter : Measurable (fun v : Fin M → E =>
      OracleTemplate.RobustGradient.pilotCenter (R / 8) v) :=
    (OracleTemplate.RobustGradient.measurable_pilotCenter M).comp
      (measurable_const.prodMk measurable_id)
  have heq := hlaw.measure_mem_eq
    (s := {v | R / 16 < ‖OracleTemplate.RobustGradient.pilotCenter (R / 8) v - u‖})
    (measurableSet_lt measurable_const ((hcenter.sub_const u).norm))
  exact heq.trans_le hideal

open LongTails.Algorithms.HeavyTailSaddleEstimator
open LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution

lemma executed_refresh_confidence {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    [AddCommGroup F] [Module ℝ F]
    (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P)
    (g : E × F → Ω → E × F) (correction : E × F → E × F) (v : F)
    {field : E → E} {oracle : E → Ω → E}
    (hga : ∀ x ω, (g (x, v) ω + correction (x, v)).1 = oracle x ω)
    (hf : Measurable field) (ho : Measurable (Function.uncurry oracle))
    {L R p σ δ : ℝ} (hL : 0 < L) (hR : 0 < R) (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field x - field y, x - y⟫)
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hoi : ∀ x, Integrable (oracle x) pnoise)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - field x‖ ^ p) pnoise)
    (homean : ∀ x, (∫ ω, oracle x ω ∂pnoise) = field x)
    (hoV : ∀ x, (∫ ω, ‖oracle x ω - field x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (u start : E) (hu : field u = 0) (hstart : ‖start - u‖ ≤ 13 * R / 8) :
    P {ξ | R / 16 < ‖evalAt (fun k x => g x (ξ k))
      (tunedRefreshPlan p σ L R δ start v correction) 0 - u‖} ≤ ENNReal.ofReal δ := by
  have hh := endpoint_confidence pnoise P hIID hf ho hL hR hp hp2 hσ hδ hδ1
    hm hl hoi hop homean hoV u start hu hstart
  have heq (ξ : ℕ → Ω) := HeavyTailSaddleExecution.eval_refresh_plan_corrected g ξ
    256 (refreshBatch p σ L R) (refreshRepetitions δ) (by unfold refreshBatch; omega)
    (1 / (4 * L)) R start v correction 0
  dsimp only at heq
  simp_rw [hga, Nat.zero_add] at heq
  simpa only [tunedRefreshPlan, heq] using hh

lemma refresh_plan_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h n M : ℕ) (hn : 0 < n)
    (η R : ℝ) (call : ℕ) :
    Measurable (fun w : A × (ℕ → Ω) =>
      evalAt (fun j x => g x (w.2 j))
        (refreshPlan h n M hn η R (start w.1) (dual w.1) (correction w.1)) call) := by
  let c := fun a x ω => (g (x, dual a) ω + correction a (x, dual a)).1
  have hcm : Measurable (fun w : (A × E) × Ω => c w.1.1 w.1.2 w.2) := by
    apply Measurable.fst
    apply Measurable.add
    · exact hg.comp ((measurable_fst.snd.prodMk (hv.comp measurable_fst.fst)).prodMk measurable_snd)
    · exact hc.comp (measurable_fst.fst.prodMk
        (measurable_fst.snd.prodMk (hv.comp measurable_fst.fst)))
  have ht := HeavyTailSaddleExecution.batched_endpoint_measurable hcm hx η h n
  let endpoint := fun w : A × (ℕ → Ω) =>
    HeavyTailedProductProcess.trajectory
      (fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, c w.1 x (ζ i)))
      h (start w.1) (fun k (i : Fin n) => w.2 (k * n + i.val))
  have hvec : Measurable (fun w : A × (ℕ → Ω) => fun i : Fin M =>
      endpoint (w.1, fun j => w.2 (call + h * n * i.val + j))) := by
    apply Measurable.of_eval
    intro i
    exact ht.comp (by fun_prop)
  have hm := (OracleTemplate.RobustGradient.measurable_pilotCenter M).comp
    ((measurable_const (a := R / 8)).prodMk hvec)
  convert hm using 1
  funext w
  exact HeavyTailSaddleExecution.eval_refresh_plan_corrected g w.2 h n M hn η R
    (start w.1) (dual w.1) (correction w.1) call

lemma seeded_append_failure {S Ω U : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace U] (Q : Measure S) [IsProbabilityMeasure Q]
    (p : Measure Ω) [IsProbabilityMeasure p] {length : S → ℕ}
    (hl : Measurable length) (X : S × (ℕ → Ω) → U) (hX : Measurable X)
    (hdep : ∀ s ξ ζ, (∀ j, j < length s → ξ j = ζ j) → X (s, ξ) = X (s, ζ))
    {bad : Set (U × (ℕ → Ω))} (hbad : MeasurableSet bad)
    {B : Set U} (hB : MeasurableSet B) {ε₀ ε₁ : ENNReal}
    (hrough : (Q.prod (Measure.infinitePi fun _ : ℕ => p)) {w | X w ∈ B} ≤ ε₀)
    (hcond : ∀ u, u ∉ B → (Measure.infinitePi fun _ : ℕ => p) {ξ | (u, ξ) ∈ bad} ≤ ε₁) :
    (Q.prod (Measure.infinitePi fun _ : ℕ => p))
      {w | (X w, fun j => w.2 (length w.1 + j)) ∈ bad} ≤ ε₀ + ε₁ := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let R := (Q.prod P).map (fun w => (w.1, X w))
  have hj : Measurable (fun w : S × (ℕ → Ω) => (w.1, X w)) := measurable_fst.prodMk hX
  have : IsProbabilityMeasure R := (Measure.isProbabilityMeasure_map_iff hj.aemeasurable).mpr inferInstance
  have hbad' : MeasurableSet {w : (S × U) × (ℕ → Ω) | (w.1.2, w.2) ∈ bad} :=
    hbad.preimage (measurable_fst.snd.prodMk measurable_snd)
  have hB' : MeasurableSet {w : S × U | w.2 ∈ B} := hB.preimage measurable_snd
  have hr : R {w : S × U | w.2 ∈ B} ≤ ε₀ := by
    rw [Measure.map_apply hj hB']
    exact hrough
  have hb := StochasticEnvelopeFreshness.product_failure_probability R P hbad' hB' hr
    (fun w hw => hcond w.2 hw)
  have hp := StochasticEnvelopeFreshness.seed_prefix_tail_preserving p Q hl X hX hdep
  have he := hp.measure_preimage hbad'.nullMeasurableSet
  exact he.trans_le hb
lemma refreshed_epoch_failure {S Ω E F : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (Q : Measure S) [IsProbabilityMeasure Q] (p : Measure Ω) [IsProbabilityMeasure p]
    {length : S → ℕ} (hl : Measurable length) (X : S × (ℕ → Ω) → F × F)
    (hX : Measurable X)
    (hdep : ∀ s ξ ζ, (∀ j, j < length s → ξ j = ζ j) → X (s, ξ) = X (s, ζ))
    {q : F → ℝ} (hq : Measurable q) (U : F → E) (hUm : Measurable U)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖) (u : F) (ref : E)
    {m B : ℝ} (hm : 0 < m) (hB : 0 < B)
    (hsc : ∀ v, m * ‖v - u‖ ^ 2 ≤ 2 * (q v - q u))
    (href : m * ‖ref - U u‖ ^ 2 ≤ B)
    (next : F → (ℕ → Ω) → E) (hn : Measurable (Function.uncurry next))
    {ε₀ ε₁ : ENNReal}
    (hrough : (Q.prod (Measure.infinitePi fun _ : ℕ => p))
      {w | 25 * B / 128 < q (X w).1 - q u + m / 2 * ‖(X w).2 - u‖ ^ 2} ≤ ε₀)
    (hrefresh : ∀ v, ‖ref - U v‖ ≤ 13 * Real.sqrt (B / m) / 8 →
      (Measure.infinitePi fun _ : ℕ => p) {ξ | Real.sqrt (B / m) / 16 < ‖next v ξ - U v‖} ≤ ε₁) :
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => p)
    let output := fun w => next (X w).1 (fun j => w.2 (length w.1 + j))
    P {w | B / 2 < m * ‖output w - U u‖ ^ 2 ∨
      B / 2 < q (X w).1 - q u + m / 2 * ‖(X w).1 - u‖ ^ 2 ∨
      Real.sqrt (B / m) / 16 < ‖output w - U (X w).1‖} ≤ ε₀ + ε₁ := by
  intro P output
  let bad : Set ((F × F) × (ℕ → Ω)) := {w | B / 2 < m * ‖next w.1.1 w.2 - U u‖ ^ 2 ∨
    B / 2 < q w.1.1 - q u + m / 2 * ‖w.1.1 - u‖ ^ 2 ∨
    Real.sqrt (B / m) / 16 < ‖next w.1.1 w.2 - U w.1.1‖}
  let bad0 : Set (F × F) := {v | 25 * B / 128 < q v.1 - q u + m / 2 * ‖v.2 - u‖ ^ 2}
  have hnext : Measurable (fun w : (F × F) × (ℕ → Ω) => next w.1.1 w.2) :=
    hn.comp (measurable_fst.fst.prodMk measurable_snd)
  have h1 : Measurable (fun w : (F × F) × (ℕ → Ω) => m * ‖next w.1.1 w.2 - U u‖ ^ 2) := by fun_prop
  have h2 : Measurable (fun w : (F × F) × (ℕ → Ω) => q w.1.1 - q u + m / 2 * ‖w.1.1 - u‖ ^ 2) := by fun_prop
  have h3 : Measurable (fun w : (F × F) × (ℕ → Ω) => ‖next w.1.1 w.2 - U w.1.1‖) := by fun_prop
  have hb : MeasurableSet bad := (measurableSet_lt measurable_const h1).union
    ((measurableSet_lt measurable_const h2).union (measurableSet_lt measurable_const h3))
  have hb0 : MeasurableSet bad0 := measurableSet_lt measurable_const
    (show Measurable (fun v : F × F => q v.1 - q u + m / 2 * ‖v.2 - u‖ ^ 2) by fun_prop)
  apply seeded_append_failure Q p hl X hX hdep hb hb0 hrough
  intro v hv
  have he : q v.1 - q u + m / 2 * ‖v.2 - u‖ ^ 2 ≤ 25 * B / 128 := le_of_not_gt hv
  have hgeo := HeavyTailSaddleGeometry.refresh_halving_geometry hm hB v.1 v.2 u ref (U v.1) U hU
    he (hsc v.1) href (by simp only [sub_self, norm_zero]; positivity)
  have hp := hrefresh v.1 hgeo.1
  apply (measure_mono ?_).trans hp
  intro ξ hx
  by_contra hc
  have hn' : ‖next v.1 ξ - U v.1‖ ≤ Real.sqrt (B / m) / 16 := le_of_not_gt hc
  have hg := HeavyTailSaddleGeometry.refresh_halving_geometry hm hB v.1 v.2 u ref (next v.1 ξ) U hU
    he (hsc v.1) href hn'
  rcases hx with hx | hx | hx
  · exact (not_lt_of_ge hg.2.1) hx
  · exact (not_lt_of_ge hg.2.2) hx
  · exact (not_lt_of_ge hn') hx

lemma halving_plan_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {ref : A → E} {initial : A → F × F} {correction : A → E × F → E × F}
    (hr : Measurable ref) (hi : Measurable initial) (hc : Measurable (Function.uncurry correction))
    (p σ L m H B δ : ℝ) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    Measurable (fun w : A × ((ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (halvingPlan p σ L m H B δ w.2.1 (ref w.1) (initial w.1) (correction w.1)) 0) := by
  intro J n
  let N := epochSteps m H (δ / 2)
  let α := epochMomentum m H (δ / 2)
  let length := fun seeds : ℕ → Fin n → Fin (J + 1) =>
    slotCalls (fun j => batchCalls (kernelHorizon L m) (extendLevels (seeds j)) n) N 0
  let X := fun w : A × ((ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
    evalAt (fun k x => g x (w.2.2 k))
      (epochPlan p σ L m H B α w.2.1 (ref w.1) (correction w.1) N (initial w.1)) 0
  have hX : Measurable X := HeavyTailSaddleExecution.epoch_plan_measurable hg hr hi hc p σ L m H B α N
  have hl : Measurable length := HeavyTailSaddleExecution.epoch_calls_measurable p σ L m H B N 0
  have ht := (StochasticEnvelopeFreshness.measurable_seed_shift hl).comp
    (measurable_snd : Measurable (fun w : A × ((ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω)) => w.2))
  have hn := refresh_plan_measurable (A := A × F) hg
    (start := fun v => ref v.1) (dual := fun v => v.2) (correction := fun v => correction v.1)
    (hr.comp measurable_fst) measurable_snd (hc.comp (measurable_fst.fst.prodMk measurable_snd))
    256 (refreshBatch p σ L (Real.sqrt (B / m))) (refreshRepetitions (δ / 2))
    (by unfold refreshBatch; omega) (1 / (4 * L)) (Real.sqrt (B / m)) 0
  have hm := (hn.comp ((measurable_fst.prodMk hX.fst).prodMk ht)).prodMk hX.fst
  convert hm using 1
  funext w
  rw [HeavyTailSaddleExecution.eval_halving_plan]
  simp only [Nat.zero_add]
  apply Prod.ext
  · have hh := StochasticEnvelopeExecution.evalAt_shift (fun k x => g x (w.2.2 k))
      (tunedRefreshPlan p σ L (Real.sqrt (B / m)) (δ / 2) (ref w.1) (X w).1 (correction w.1))
      (length w.2.1) 0
    simpa only [Nat.add_zero, Function.comp_def, tunedRefreshPlan] using hh.symm
  · rfl

lemma refinement_stage_measurable {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {correction : E × F → E × F} (hc : Measurable correction)
    (p σ L m H B δ : ℝ) (K j : ℕ) :
    Measurable (fun w : (E × F) ×
      (HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (w.2.1 j)
          w.1.1 (w.1.2, w.1.2) correction) 0) := by
  have hh := halving_plan_measurable (A := E × F) hg
    (ref := Prod.fst) (initial := fun z => (z.2,z.2)) (correction := fun _ => correction)
    measurable_fst (measurable_snd.prodMk measurable_snd) (hc.comp measurable_snd)
    p σ L m H (refinementEnvelope B j) (δ / (K + 1))
  let projection := fun w : (E × F) ×
      (HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B) × (ℕ → Ω)) =>
        (w.1, (w.2.1 j, w.2.2))
  have hproj : Measurable projection := by fun_prop
  exact hh.comp hproj

lemma refinement_stage_cost_measurable (p σ L m H B δ : ℝ) (K j : ℕ) :
    Measurable (fun seed : HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B) =>
      halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (seed j)) := by
  exact (measurable_const.add (HeavyTailSaddleExecution.epoch_calls_measurable
    p σ L m H (refinementEnvelope B j) (epochSteps m H (δ / (K + 1) / 2)) 0)).comp
      (measurable_pi_apply j)
lemma refinement_plan_law {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {correction : E × F → E × F} (hc : Measurable correction)
    (p σ L m H B δ : ℝ) (K : ℕ) (state : E × F) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) : Measure S)
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
        (refinementPlan p σ L m H B δ K w.1 state correction) 0)
      (StochasticEnvelopeFreshness.idealRun
        (fun j z (w : S × (ℕ → Ω)) => evalAt (fun k x => g x (w.2 k))
          (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (w.1 j)
            z.1 (z.2,z.2) correction) 0) K 0 state)
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise))
      (Measure.infinitePi fun _ : ℕ => Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)) := by
  intro S Q
  exact StochasticEnvelopeExecution.substituted_statePlan_identDistrib Q pnoise
    (fun j (seed : S) => halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (seed j))
    (refinement_stage_cost_measurable p σ L m H B δ K)
    (fun j (seed : S) (z : E × F) => halvingPlan p σ L m H (refinementEnvelope B j)
      (δ / (K + 1)) (seed j) z.1 (z.2,z.2) correction)
    g (fun _ z => z) (fun _ _ z => z)
    (refinement_stage_measurable hg hc p σ L m H B δ K)
    (fun _ => measurable_id) (fun _ => measurable_snd) K state

lemma refinement_calls_measurable (p σ L m H B δ : ℝ) (K : ℕ) :
    Measurable (refinementCalls p σ L m H B δ K) := by
  let cost := fun j (seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) =>
    halvingCalls p σ L m H (refinementEnvelope B j) (δ/(K+1)) (seeds j j)
  have hc (j : ℕ) : Measurable (cost j) :=
    (refinement_stage_cost_measurable p σ L m H B δ K j).comp (measurable_pi_apply j)
  have hh (N slot : ℕ) : Measurable (fun seeds => slotCalls (fun j => cost j seeds) N slot) := by
    induction N generalizing slot with
    | zero => exact measurable_const
    | succ N ih => exact (ih (slot+1)).add (hc slot)
  exact hh K 0

lemma refinement_plan_parameter_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {initial : A → E × F} {correction : A → E × F → E × F}
    (hi : Measurable initial) (hc : Measurable (Function.uncurry correction))
    (p σ L m H B δ : ℝ) (K : ℕ) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (refinementPlan p σ L m H B δ K w.2.1 (initial w.1) (correction w.1)) 0) := by
  intro S
  let cost := fun j (seed : S) => halvingCalls p σ L m H (refinementEnvelope B j) (δ/(K+1)) (seed j)
  let step := fun (a : A) j (z : E × F) (w : S × (ℕ → Ω)) =>
    evalAt (fun k x => g x (w.2 k))
      (halvingPlan p σ L m H (refinementEnvelope B j) (δ/(K+1)) (w.1 j) z.1 (z.2,z.2) (correction a)) 0
  have hs (j : ℕ) : Measurable (fun w : (A × (E × F)) × (S × (ℕ → Ω)) =>
      step w.1.1 j w.1.2 w.2) := by
    have hh := halving_plan_measurable (A := A × (E × F)) hg
      (ref := fun v => v.2.1) (initial := fun v => (v.2.2,v.2.2))
      (correction := fun v => correction v.1)
      measurable_snd.fst (measurable_snd.snd.prodMk measurable_snd.snd)
      (hc.comp (measurable_fst.fst.prodMk measurable_snd))
      p σ L m H (refinementEnvelope B j) (δ/(K+1))
    let projection := fun w : (A × (E × F)) × (S × (ℕ → Ω)) => (w.1,(w.2.1 j,w.2.2))
    exact hh.comp (show Measurable projection by fun_prop)
  have hh := HeavyTailSaddleExecution.parameter_freshRun_measurable (cost := cost)
    (refinement_stage_cost_measurable p σ L m H B δ K) hs K 0
  have ht := hh.comp (show Measurable
    (fun w : A × ((ℕ → S) × (ℕ → Ω)) => ((w.1,initial w.1),w.2)) by fun_prop)
  convert ht using 1
  funext w
  rw [HeavyTailSaddleExecution.eval_refinement_plan, StochasticEnvelopeExecution.cursorRun_freshRun]
  simp only [Nat.zero_add]
  rfl

lemma capped_refinement_parameter_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {initial : A → E × F} {correction : A → E × F → E × F}
    (hi : Measurable initial) (hc : Measurable (Function.uncurry correction))
    (p σ L m H B δ η : ℝ) (K : ℕ) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (cappedRefinementPlan p σ L m H B δ η K w.2.1 (initial w.1) (correction w.1)) 0) := by
  intro S
  unfold cappedRefinementPlan
  apply LongTails.Proofs.HeavyTailSaddleExecution.capped_plan_output_measurable
  · exact (refinement_calls_measurable p σ L m H B δ K).comp (measurable_fst.comp measurable_snd)
  · exact hi.comp measurable_fst
  · exact refinement_plan_parameter_measurable hg hi hc p σ L m H B δ K

lemma capped_refinement_failure {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F)
    (p σ L m H B δ η : ℝ) (hη : 0 < η) (K : ℕ) (initial : E × F) (bad : Set (E × F)) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) : Measure S)
    let P := (Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise)
    P {w | evalAt (fun k x => g x (w.2 k))
      (refinementPlan p σ L m H B δ K w.1 initial correction) 0 ∈ bad} ≤ ENNReal.ofReal δ →
    P {w | evalAt (fun k x => g x (w.2 k))
      (cappedRefinementPlan p σ L m H B δ η K w.1 initial correction) 0 ∈ bad}
      ≤ ENNReal.ofReal δ + ENNReal.ofReal η := by
  intro S Q P hbad
  exact LongTails.Proofs.HeavyTailSaddleExecution.capped_plan_product_failure (Measure.infinitePi fun _ : ℕ => Q)
    (Measure.infinitePi fun _ : ℕ => pnoise) (refinementCalls p σ L m H B δ K)
    (refinement_calls_measurable p σ L m H B δ K)
    (fun seeds => refinementPlan p σ L m H B δ K seeds initial correction)
    (fun ξ k x => g x (ξ k)) initial initial (refinementCap p σ L m H B δ η K) 0 bad hbad
    (LongTails.Proofs.HeavyTailSaddleExecution.refinement_overflow_probability p σ L m H B δ η hη K)

lemma recovery_profile_coordinate_law (p σ L μ ζ initialBound : ℝ) (j : ℕ) :
    MeasurePreserving (fun s : RecoveryProfile p σ L μ ζ initialBound => s j)
      (recoveryProfileLaw p σ L μ ζ initialBound : Measure _)
      (Measure.infinitePi fun _ : ℕ =>
        (halvingProfileLaw (recoveryStageBatch p σ L μ ζ initialBound j)
          (recoveryStageDepth p σ L μ ζ initialBound j) : Measure _)) := by
  refine ⟨measurable_pi_apply j, ?_⟩
  exact Measure.infinitePi_map_eval _ j

end LongTails.Proofs.HeavyTailSaddleRefresh
