import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import LongTails.Setups.RipmLastIterate
import LongTails.Algorithms.RipmOutput
import LongTails.Proofs.RipmRates
import LongTails.Proofs.RipmExecution
import LongTails.Proofs.RipmSmoothGeometry
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic

open MeasureTheory
open LongTails.Setups.RipmGeneral
open LongTails.Algorithms.RipmOutput

namespace LongTails.Proofs.RipmAccuracy

noncomputable section

lemma log_horizon_accuracy (B k epsilon : ℝ) (hB : 0 ≤ B)
    (hk : 0 < k) (hepsilon : 0 < epsilon) :
    let s := 1 + k * B / epsilon
    let T := ⌈(64 * s * (1 + Real.log s)) ^ 2⌉₊
    1 ≤ T ∧ k * B / Real.sqrt T * (1 + 4 * Real.log ((T : ℝ) + 1)) ≤ epsilon := by
  dsimp only
  let s := 1 + k * B / epsilon
  let a := 64 * s * (1 + Real.log s)
  let T := ⌈a ^ 2⌉₊
  have hs1 : 1 ≤ s := by
    have h := div_nonneg (mul_nonneg hk.le hB) hepsilon.le
    dsimp [s]
    linarith
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hlog : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hu : 0 < 1 + Real.log s := by positivity
  have ha64 : 64 ≤ a := by
    have hprod := mul_nonneg (sub_nonneg.mpr hs1) hlog
    dsimp [a]
    nlinarith
  have ha : 0 < a := by linarith
  have hceil : a ^ 2 ≤ (T : ℝ) := Nat.le_ceil _
  have hceilup : (T : ℝ) < a ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg a)
  have hTreal : (1 : ℝ) ≤ T := by nlinarith
  have hT : 1 ≤ T := by exact_mod_cast hTreal
  have hsqrt : a ≤ Real.sqrt T := (Real.le_sqrt ha.le (Nat.cast_nonneg T)).mpr hceil
  have hsqrt0 : 0 < Real.sqrt T := lt_of_lt_of_le ha hsqrt
  have hlogu : Real.log (1 + Real.log s) ≤ Real.log s := by
    have hle : 1 + Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs]
    exact Real.log_le_log hu hle
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog64 : Real.log 64 ≤ 6 := by
    have heq : Real.log 64 = 6 * Real.log 2 := by
      calc
        Real.log 64 = Real.log ((2 : ℝ) ^ (6 : ℕ)) := congrArg Real.log (by norm_num)
        _ = 6 * Real.log 2 := by simpa only [Nat.cast_ofNat] using Real.log_pow 2 6
    rw [heq]
    linarith
  have hloga : Real.log a ≤ 6 + 2 * Real.log s := by
    have heq : Real.log a = Real.log 64 + Real.log s + Real.log (1 + Real.log s) := by
      change Real.log (64 * s * (1 + Real.log s)) = _
      rw [Real.log_mul (mul_ne_zero (by norm_num) hs.ne') hu.ne',
        Real.log_mul (by norm_num) hs.ne']
    rw [heq]
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  have hTup : (T : ℝ) + 1 ≤ 3 * a ^ 2 := by nlinarith
  have hlogT : Real.log ((T : ℝ) + 1) ≤ 14 + 4 * Real.log s := by
    have h := Real.log_le_log (show 0 < (T : ℝ) + 1 by positivity) hTup
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 ha.ne'), Real.log_pow] at h
    norm_num at h
    linarith
  have hlogT0 : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by linarith only [hTreal])
  have hfactor : 1 + 4 * Real.log ((T : ℝ) + 1) ≤ 64 * (1 + Real.log s) := by
    linarith
  have hkb : 0 ≤ k * B := mul_nonneg hk.le hB
  have hsmall : k * B / s ≤ epsilon := by
    apply (div_le_iff₀ hs).mpr
    have heq : (k * B / epsilon) * epsilon = k * B := div_mul_cancel₀ _ hepsilon.ne'
    dsimp [s]
    nlinarith
  have hrate : k * B / Real.sqrt T * (1 + 4 * Real.log ((T : ℝ) + 1)) ≤ epsilon := by
    calc
      _ ≤ k * B / a * (64 * (1 + Real.log s)) :=
        mul_le_mul (div_le_div_of_nonneg_left hkb ha hsqrt) hfactor
          (by positivity) (div_nonneg hkb ha.le)
      _ = k * B / s := by
        dsimp [a]
        field_simp [hs.ne', hu.ne']
      _ ≤ epsilon := hsmall
  exact ⟨hT, hrate⟩


lemma general_tuning_legal (p : LongTails.Setups.RipmGeneral.Params) (hp : LongTails.Setups.RipmGeneral.valid p) :
    1 ≤ LongTails.Setups.RipmGeneral.horizon p ∧ 0 < LongTails.Setups.RipmGeneral.step p ∧
      LongTails.Setups.RipmGeneral.step p * p.L < 1 / 4 := by
  rcases hp with ⟨hm, hL, hLg, hD, hDelta, hS, hepsilon, hC⟩
  have hC0 : 0 < p.C := by linarith
  have hC2 : 0 < p.C - 2 := by linarith
  have hB : 0 ≤ LongTails.Setups.RipmGeneral.boundScale p := by
    change 0 ≤ p.C * p.L * p.D2 + 2 * p.Delta +
      (4 * p.S / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L
    positivity
  have hT : 1 ≤ LongTails.Setups.RipmGeneral.horizon p :=
    (log_horizon_accuracy (LongTails.Setups.RipmGeneral.boundScale p) 3 p.epsilon
      hB (by norm_num) hepsilon).1
  have hTpos : 0 < ((LongTails.Setups.RipmGeneral.horizon p : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < LongTails.Setups.RipmGeneral.horizon p by omega)
  have hsqrt : 0 < Real.sqrt (LongTails.Setups.RipmGeneral.horizon p) := Real.sqrt_pos.2 hTpos
  have heta : 0 < LongTails.Setups.RipmGeneral.step p := by
    change 0 < 1 / (p.C * p.L * Real.sqrt (LongTails.Setups.RipmGeneral.horizon p))
    positivity
  have hpower := LongTails.Proofs.RipmWeights.power_bound p.L p.C
    (LongTails.Setups.RipmGeneral.horizon p) hL (by linarith) hT
  rcases hpower with ⟨hgamma, hmu, hmu1, heq, hle, hhalf, hbound⟩
  have hstep : LongTails.Setups.RipmGeneral.step p * p.L ≤ 1 / p.C := hle
  have hquarter : 1 / p.C < (1 : ℝ) / 4 := by
    apply (div_lt_div_iff₀ hC0 (show (0 : ℝ) < 4 by norm_num)).2
    linarith
  exact ⟨hT, heta, hstep.trans_lt hquarter⟩

lemma general_source_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (p : LongTails.Setups.RipmGeneral.Params) (hp : LongTails.Setups.RipmGeneral.valid p)
    (I : Core.Problem p.d p.m) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin p.m)
    (hsource : Core.SourceAssumptions I p.L p.Lg p.xstar sigmaSq)
    (hSigma : sigmaSq ≤ p.S) (hD : ‖p.x0 - p.xstar‖ ^ 2 ≤ p.D2)
    (hDelta : Core.objective I p.x0 - Core.objective I p.xstar ≤ p.Delta)
    (hsamples : Core.Sampling I P (LongTails.Setups.RipmGeneral.step p) p.x0 i j) :
    LongTails.Setups.RipmGeneral.admissible p I (sourceOracle I P i j) ∧
      ∀ omega,
        OracleTemplate.execute (sourceOracle I P i j) (method (LongTails.Setups.RipmGeneral.publicInput p))
          (fun _ => LongTails.Setups.RipmGeneral.horizon p + 1) ()
          (fun k => (i (k / 2) omega, j (k / 2) omega)) =
        lastIterate I (LongTails.Setups.RipmGeneral.step p) p.x0 i j (LongTails.Setups.RipmGeneral.horizon p) omega := by
  classical
  let eta := LongTails.Setups.RipmGeneral.step p
  let T := LongTails.Setups.RipmGeneral.horizon p
  let O := sourceOracle I P i j
  let Path := ℕ → I.Sample × Fin p.m
  let enc : Ω → Path := fun omega k => (i (k / 2) omega, j (k / 2) omega)
  let a : ℕ → Path → I.Sample := fun t path => (path (2 * t)).1
  let b : ℕ → Path → Fin p.m := fun t path => (path (2 * t + 1)).2
  have heta : 0 < eta := (general_tuning_legal p hp).2.1
  have he : Measurable enc := Measurable.of_eval (fun k =>
    (hsamples.1.measurable (k / 2)).prodMk (hsamples.2 (k / 2)).1)
  have ha (t : ℕ) : Measurable (a t) := measurable_fst.comp (measurable_pi_apply (2 * t))
  have hb (t : ℕ) : Measurable (b t) := measurable_snd.comp (measurable_pi_apply (2 * t + 1))
  have hae (t : ℕ) (omega : Ω) : a t (enc omega) = i t omega := by
    change i ((2 * t) / 2) omega = i t omega
    congr 1
    omega
  have hbe (t : ℕ) (omega : Ω) : b t (enc omega) = j t omega := by
    change j ((2 * t + 1) / 2) omega = j t omega
    congr 1
    omega
  have htraj (n : ℕ) (omega : Ω) :
      Core.trajectory I eta p.x0 a b n (enc omega) =
        Core.trajectory I eta p.x0 i j n omega := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Core.prox (I.regularizers (b n (enc omega))) (eta * p.m)
        (Core.trajectory I eta p.x0 a b n (enc omega) -
          eta • I.grad (a n (enc omega)) (Core.trajectory I eta p.x0 a b n (enc omega))) =
        Core.prox (I.regularizers (j n omega)) (eta * p.m)
        (Core.trajectory I eta p.x0 i j n omega -
          eta • I.grad (i n omega) (Core.trajectory I eta p.x0 i j n omega))
      rw [hae, hbe, ih]
  have hmapa (t : ℕ) : (P.toMeasure.map enc).map (a t) = I.law.toMeasure := by
    rw [Measure.map_map (ha t) he]
    have hfun : a t ∘ enc = i t := funext (hae t)
    rw [hfun]
    exact hsamples.1.marginal t
  have hindep {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (f : Path → A) (g : Path → B) (hf : Measurable f) (hg : Measurable g)
      (hfg : ProbabilityTheory.IndepFun (f ∘ enc) (g ∘ enc) P.toMeasure) :
      ProbabilityTheory.IndepFun f g (P.toMeasure.map enc) := by
    apply ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro s t hs ht
    rw [Measure.map_apply he ((hf hs).inter (hg ht)),
      Measure.map_apply he (hf hs), Measure.map_apply he (hg ht)]
    simpa only [Set.preimage_inter, Set.preimage_comp] using
      hfg.measure_inter_preimage_eq_mul s t hs ht
  have hs : Core.Sampling I O.law eta p.x0 a b := by
    constructor
    · refine ⟨ha, ?_, hmapa⟩
      change ProbabilityTheory.iIndepFun a (P.toMeasure.map enc)
      apply ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
      intro S sets hsets
      have hinter : MeasurableSet (⋂ t ∈ S, a t ⁻¹' sets t) := by
        apply MeasurableSet.iInter
        intro t
        apply MeasurableSet.iInter
        intro ht
        exact ha t (hsets t ht)
      rw [Measure.map_apply he hinter]
      have hsingle (t : ℕ) (ht : t ∈ S) :
          P.toMeasure.map enc (a t ⁻¹' sets t) = P.toMeasure (i t ⁻¹' sets t) := by
        rw [Measure.map_apply he (ha t (hsets t ht))]
        congr 1
        ext omega
        simp only [Set.mem_preimage, hae]
      rw [Finset.prod_congr rfl hsingle]
      have hset : enc ⁻¹' (⋂ t ∈ S, a t ⁻¹' sets t) = ⋂ t ∈ S, i t ⁻¹' sets t := by
        ext omega
        simp only [Set.mem_preimage, Set.mem_iInter, hae]
      rw [hset]
      exact hsamples.1.independent.measure_inter_preimage_eq_mul S hsets
    · intro t
      let hist : Path → (Fin (t + 1) → Core.Vec p.d) :=
        fun path s => Core.trajectory I eta p.x0 a b s path
      have hh : Measurable hist := Measurable.of_eval (fun s =>
        LongTails.Proofs.RipmRegularity.trajectory_measurable I p.L p.Lg eta p.x0 p.xstar
          sigmaSq a b hsource heta ha hb s)
      have hhenc : hist ∘ enc =
          (fun omega => fun s : Fin (t + 1) => Core.trajectory I eta p.x0 i j s omega) := by
        funext omega s
        exact htraj s omega
      have hia : ProbabilityTheory.IndepFun (a t) hist (P.toMeasure.map enc) := by
        apply hindep (a t) hist (ha t) hh
        have hi : ProbabilityTheory.IndepFun (i t)
            (fun omega => fun s : Fin (t + 1) => Core.trajectory I eta p.x0 i j s omega) P.toMeasure :=
          (hsamples.2 t).2.1
        have hai : a t ∘ enc = i t := funext (hae t)
        rw [hai, hhenc]
        exact hi
      have hjb : ProbabilityTheory.IndepFun (b t) hist (P.toMeasure.map enc) := by
        apply hindep (b t) hist (hb t) hh
        have hj : ProbabilityTheory.IndepFun (j t)
            (fun omega => fun s : Fin (t + 1) => Core.trajectory I eta p.x0 i j s omega) P.toMeasure :=
          (hsamples.2 t).2.2.1
        have hbj : b t ∘ enc = j t := funext (hbe t)
        rw [hbj, hhenc]
        exact hj
      refine ⟨hb t, hia, hjb, ?_⟩
      obtain ⟨hm, hjlaw⟩ := (hsamples.2 t).2.2.2
      refine ⟨hm, ?_⟩
      change (P.toMeasure.map enc).map (b t) = _
      rw [Measure.map_map (hb t) he]
      have hbj : b t ∘ enc = j t := funext (hbe t)
      rw [hbj]
      exact hjlaw
  let decodeI : (k : ℕ) → O.Seed k → I.Sample := fun _ s => s.1
  let decodeJ : (k : ℕ) → O.Seed k → Fin p.m := fun _ s => s.2
  have hO : Core.OracleExact I O decodeI decodeJ := by
    refine ⟨fun _ => ⟨measurable_fst, measurable_snd⟩, ?_⟩
    intro history q seed
    constructor
    · intro hq
      change (if q.1 = 0 then I.grad seed.1 q.2.2
        else Core.prox (I.regularizers seed.2) q.2.1 q.2.2) = _
      rw [ite_eq_left hq]
    · intro hq _hscale
      have hq0 : q.1 ≠ 0 := by rw [hq]; decide
      change (if q.1 = 0 then I.grad seed.1 q.2.2
        else Core.prox (I.regularizers seed.2) q.2.1 q.2.2) = _
      rw [ite_eq_right hq0]
  constructor
  · exact ⟨sigmaSq, decodeI, decodeJ, hsource, hSigma, hD, hDelta, hO, hs⟩
  · intro omega
    have hc := LongTails.Proofs.RipmExecution.execute_correspondence
      (LongTails.Setups.RipmGeneral.publicInput p) I O decodeI decodeJ hO heta hsource.countPos T () (enc omega)
    exact hc.trans (htraj (T + 1) omega)


lemma general_rate_to_accuracy (p : LongTails.Setups.RipmGeneral.Params) (hp : LongTails.Setups.RipmGeneral.valid p)
    (D2 Delta sigmaSq R : ℝ) (hD0 : 0 ≤ D2) (hD : D2 ≤ p.D2)
    (hDelta0 : 0 ≤ Delta) (hDelta : Delta ≤ p.Delta)
    (hSigma0 : 0 ≤ sigmaSq) (hSigma : sigmaSq ≤ p.S)
    (hR : R ≤ LongTails.Proofs.RipmRates.generalBound (LongTails.Setups.RipmGeneral.horizon p) p.m p.C p.L p.Lg D2 Delta sigmaSq) :
    R ≤ p.epsilon := by
  obtain ⟨hm, hL, hLg, hDp, hDelp, hSp, heps, hC⟩ := hp
  let B := LongTails.Setups.RipmGeneral.boundScale p
  let T := LongTails.Setups.RipmGeneral.horizon p
  let s := Real.sqrt T
  let N := (4 * sigmaSq / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L
  let Np := (4 * p.S / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L
  have hC0 : 0 < p.C := by linarith
  have hC2 : 0 < p.C - 2 := by linarith
  have hLg2 : 0 ≤ p.Lg ^ 2 := pow_nonneg hLg 2
  have hB : 0 ≤ B := by
    change 0 ≤ p.C * p.L * p.D2 + 2 * p.Delta +
      (4 * p.S / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L
    positivity
  have hhor := log_horizon_accuracy B 3 p.epsilon hB (by norm_num) heps
  change 1 ≤ T ∧ 3 * B / s * (1 + 4 * Real.log ((T : ℝ) + 1)) ≤ p.epsilon at hhor
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hhor.1
  have hTp : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTr
  have hs : 0 < s := Real.sqrt_pos.mpr hTp
  have hs1 : 1 ≤ s := (Real.le_sqrt (by norm_num) hTp.le).mpr (by simpa using hTr)
  have hs2 : s ^ 2 = (T : ℝ) := Real.sq_sqrt hTp.le
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hN : N ≤ Np := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSigma (by norm_num)) hC2.le) le_rfl
  have hDterm : p.C * p.L * D2 ≤ p.C * p.L * p.D2 :=
    mul_le_mul le_rfl hD hD0 (by positivity)
  have hDelterm : Delta / s ≤ p.Delta := by
    have h := div_le_div_of_nonneg_left hDelta0 (by norm_num : (0 : ℝ) < 1) hs1
    rw [div_one] at h
    exact h.trans hDelta
  have hrecip : 1 / (T : ℝ) ≤ 1 := (div_le_iff₀ hTp).mpr (by linarith)
  have hnoise : N * (1 / T + 4 * Real.log ((T : ℝ) + 1)) ≤
      Np * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 1 / (T : ℝ) + 4 * Real.log ((T : ℝ) + 1) ≤ 1 + 4 * Real.log ((T : ℝ) + 1) by linarith) hN0
    have h2 := mul_le_mul_of_nonneg_right hN
      (show 0 ≤ 1 + 4 * Real.log ((T : ℝ) + 1) by positivity)
    exact h1.trans h2
  have hinit : p.C * p.L * p.D2 + 2 * p.Delta ≤
      (p.C * p.L * p.D2 + 2 * p.Delta) * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
    have h := mul_nonneg (show 0 ≤ p.C * p.L * p.D2 + 2 * p.Delta by positivity) hlog
    nlinarith only [h]
  let G := (p.C * p.L * D2 + 2 * Delta / s + N * (1 / T + 4 * Real.log ((T : ℝ) + 1))) / s
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hG : G ≤ B / s * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
    have hbracket : p.C * p.L * D2 + 2 * Delta / s + N * (1 / T + 4 * Real.log ((T : ℝ) + 1)) ≤
        B * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
      have hDel2 : 2 * Delta / s ≤ 2 * p.Delta := by
        rw [show 2 * Delta / s = 2 * (Delta / s) by ring]
        exact mul_le_mul_of_nonneg_left hDelterm (by norm_num)
      change _ ≤ (p.C * p.L * p.D2 + 2 * p.Delta + Np) * _
      calc
        _ ≤ (p.C * p.L * p.D2 + 2 * p.Delta) * (1 + 4 * Real.log ((T : ℝ) + 1)) +
            Np * (1 + 4 * Real.log ((T : ℝ) + 1)) :=
          add_le_add ((add_le_add hDterm hDel2).trans hinit) hnoise
        _ = _ := by ring
    calc
      G ≤ (B * (1 + 4 * Real.log ((T : ℝ) + 1))) / s :=
        div_le_div_of_nonneg_right hbracket hs.le
      _ = _ := by ring
  have he : 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have harg : 8 / (Real.exp 1 * p.C) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (Real.exp_pos 1) hC0)).mpr
    have hprod := mul_pos (sub_pos.mpr he) (sub_pos.mpr hC)
    nlinarith
  have hexp : Real.exp (8 / (Real.exp 1 * p.C)) ≤ 3 := by
    exact (Real.exp_le_exp.mpr harg).trans Real.exp_one_lt_three.le
  have heq : LongTails.Proofs.RipmRates.generalBound T p.m p.C p.L p.Lg D2 Delta sigmaSq =
      Real.exp (8 / (Real.exp 1 * p.C)) * G := by
    delta LongTails.Proofs.RipmRates.generalBound
    dsimp [G, N, s]
    change 0 < Real.sqrt T at hs
    change (Real.sqrt T) ^ 2 = (T : ℝ) at hs2
    generalize Real.sqrt T = u at hs hs2 ⊢
    rw [← hs2]
    field_simp [hC0.ne', hC2.ne', hL.ne', hs.ne']
    ring
  change R ≤ LongTails.Proofs.RipmRates.generalBound T p.m p.C p.L p.Lg D2 Delta sigmaSq at hR
  rw [heq] at hR
  have hr := hR.trans (mul_le_mul_of_nonneg_right hexp hG0)
  have hmajor := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 3)
  have hfinal : 3 * (B / s * (1 + 4 * Real.log ((T : ℝ) + 1))) =
      3 * B / s * (1 + 4 * Real.log ((T : ℝ) + 1)) := by ring
  rw [hfinal] at hmajor
  exact hr.trans (hmajor.trans hhor.2)


lemma general_execution_accuracy (p : LongTails.Setups.RipmGeneral.Params) (hp : LongTails.Setups.RipmGeneral.valid p)
    (I : Core.Problem p.d p.m)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2)
    (hO : LongTails.Setups.RipmGeneral.admissible p I O) :
    let A := method (LongTails.Setups.RipmGeneral.publicInput p)
    let out := fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      OracleTemplate.execute O A (fun _ => LongTails.Setups.RipmGeneral.horizon p + 1) seed.1 seed.2
    let P : ProbabilityMeasure (A.Seed × ((k : ℕ) → O.Seed k)) :=
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩
    Measurable out ∧
      Integrable (fun omega => Core.objective I (out omega) - Core.objective I p.xstar)
        (P : Measure _) ∧
      (∫ omega, Core.objective I (out omega) - Core.objective I p.xstar ∂(P : Measure _)) ≤
        p.epsilon := by
  obtain ⟨sigmaSq, decodeI, decodeJ, hS, hSigma, hD, hDelta, hExact, hSamples⟩ := hO
  have hlegal := general_tuning_legal p hp
  let T := LongTails.Setups.RipmGeneral.horizon p
  let eta := LongTails.Setups.RipmGeneral.step p
  let i := fun (t : ℕ) (omega : (k : ℕ) → O.Seed k) => decodeI (2 * t) (omega (2 * t))
  let j := fun (t : ℕ) (omega : (k : ℕ) → O.Seed k) => decodeJ (2 * t + 1) (omega (2 * t + 1))
  let X := lastIterate I eta p.x0 i j T
  let A := method (LongTails.Setups.RipmGeneral.publicInput p)
  let out := fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
    OracleTemplate.execute O A (fun _ => T + 1) seed.1 seed.2
  have hout : out = (fun seed => X seed.2) := by
    funext seed
    exact LongTails.Proofs.RipmExecution.execute_correspondence
      (LongTails.Setups.RipmGeneral.publicInput p) I O decodeI decodeJ hExact hlegal.2.1
      hS.countPos T seed.1 seed.2
  have hsampling : Core.Sampling I O.law eta p.x0 i j := hSamples
  have hmeas : Measurable X := LongTails.Proofs.RipmRegularity.trajectory_measurable
    I p.L p.Lg eta p.x0 p.xstar sigmaSq i j hS hlegal.2.1
    hsampling.1.measurable (fun k => (hsampling.2 k).1) (T + 1)
  have hint : Integrable (fun omega => Core.objective I (X omega) - Core.objective I p.xstar)
      O.law.toMeasure :=
    (LongTails.Proofs.RipmRegularity.objective_integrable I O.law p.L p.Lg eta
      p.x0 p.xstar sigmaSq i j hS hlegal.2.1 hsampling (T + 1)).sub' (integrable_const _)
  have hSigma0 : 0 ≤ sigmaSq := by
    obtain ⟨v, hv, hi, heq⟩ := hS.solutionMoment
    rw [← heq]
    exact integral_nonneg (fun s => sq_nonneg _)
  have hDelta0 : 0 ≤ Core.objective I p.x0 - Core.objective I p.xstar :=
    sub_nonneg.mpr (hS.minimizer (Set.mem_univ p.x0))
  have hC : 4 < p.C := hp.2.2.2.2.2.2.2
  have hrate := LongTails.Proofs.RipmRates.general_rate I O.law p.L p.Lg
    p.x0 p.xstar sigmaSq i j hS T hlegal.1 p.C hC hsampling
  have hacc := general_rate_to_accuracy p hp (‖p.x0 - p.xstar‖ ^ 2)
    (Core.objective I p.x0 - Core.objective I p.xstar) sigmaSq
    (∫ omega, Core.objective I (X omega) - Core.objective I p.xstar ∂O.law.toMeasure)
    (sq_nonneg _) hD hDelta0 hDelta hSigma0 hSigma hrate
  change Measurable out ∧
    Integrable (fun omega => Core.objective I (out omega) - Core.objective I p.xstar)
      ((A.law : Measure _).prod (O.law : Measure _)) ∧
    (∫ omega, Core.objective I (out omega) - Core.objective I p.xstar
      ∂((A.law : Measure _).prod (O.law : Measure _))) ≤ p.epsilon
  rw [hout]
  refine ⟨hmeas.comp measurable_snd, hint.comp_snd _, ?_⟩
  let gap := fun (omega : (k : ℕ) → O.Seed k) =>
    Core.objective I (X omega) - Core.objective I p.xstar
  change (∫ seed : A.Seed × ((k : ℕ) → O.Seed k), gap seed.2
    ∂((A.law : Measure _).prod (O.law : Measure _))) ≤ p.epsilon
  rw [integral_fun_snd gap, probReal_univ, one_smul]
  exact hacc


lemma general_cost (p : LongTails.Setups.RipmGeneral.Params)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2)
    (seed : (method (LongTails.Setups.RipmGeneral.publicInput p)).Seed) (omega : (k : ℕ) → O.Seed k)
    (q : Fin 2) :
    ((OracleTemplate.executeWithTrace O (method (LongTails.Setups.RipmGeneral.publicInput p))
      (fun _ => LongTails.Setups.RipmGeneral.horizon p + 1) seed omega).2.countP
        (fun entry => entry.1.1 == q)) = LongTails.Setups.RipmGeneral.horizon p + 1 := by
  exact LongTails.Proofs.RipmExecution.trace_cost (LongTails.Setups.RipmGeneral.publicInput p)
    O (LongTails.Setups.RipmGeneral.horizon p) seed omega q

lemma target_tuning_legal (p : LongTails.Setups.RipmLastIterate.Params) (hp : LongTails.Setups.RipmLastIterate.valid p) :
    1 ≤ LongTails.Setups.RipmLastIterate.horizon p ∧ 0 < LongTails.Setups.RipmLastIterate.step p ∧
      LongTails.Setups.RipmLastIterate.step p * p.L < 1 / 4 := by
  rcases hp with ⟨hm, hL, hLg, hD, hDelta, hS, hepsilon⟩
  have hB : 0 ≤ LongTails.Setups.RipmLastIterate.boundScale p := by
    change 0 ≤ p.L * p.D2 + p.Delta + (p.S + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L
    positivity
  have hT : 1 ≤ LongTails.Setups.RipmLastIterate.horizon p :=
    (log_horizon_accuracy (LongTails.Setups.RipmLastIterate.boundScale p) 10 p.epsilon
      hB (by norm_num) hepsilon).1
  have hTpos : 0 < ((LongTails.Setups.RipmLastIterate.horizon p : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < LongTails.Setups.RipmLastIterate.horizon p by omega)
  have hsqrt : 0 < Real.sqrt (LongTails.Setups.RipmLastIterate.horizon p) := Real.sqrt_pos.2 hTpos
  have heta : 0 < LongTails.Setups.RipmLastIterate.step p := by
    change 0 < 1 / (5 * p.L * Real.sqrt (LongTails.Setups.RipmLastIterate.horizon p))
    positivity
  have hpower := LongTails.Proofs.RipmWeights.power_bound p.L 5
    (LongTails.Setups.RipmLastIterate.horizon p) hL (by norm_num) hT
  rcases hpower with ⟨hgamma, hmu, hmu1, heq, hle, hhalf, hbound⟩
  have hstep : LongTails.Setups.RipmLastIterate.step p * p.L ≤ (1 : ℝ) / 5 := hle
  exact ⟨hT, heta, hstep.trans_lt (by norm_num)⟩

lemma target_source_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (p : LongTails.Setups.RipmLastIterate.Params) (hp : LongTails.Setups.RipmLastIterate.valid p)
    (I : Core.Problem p.d p.m) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin p.m)
    (hsource : Core.SourceAssumptions I p.L p.Lg p.xstar sigmaSq)
    (hSigma : sigmaSq ≤ p.S) (hD : ‖p.x0 - p.xstar‖ ^ 2 ≤ p.D2)
    (hDelta : Core.objective I p.x0 - Core.objective I p.xstar ≤ p.Delta)
    (hsamples : Core.Sampling I P (LongTails.Setups.RipmLastIterate.step p) p.x0 i j) :
    LongTails.Setups.RipmLastIterate.admissible p I (sourceOracle I P i j) ∧
      ∀ omega,
        OracleTemplate.execute (sourceOracle I P i j) (method (LongTails.Setups.RipmLastIterate.publicInput p))
          (fun _ => LongTails.Setups.RipmLastIterate.horizon p + 1) ()
          (fun k => (i (k / 2) omega, j (k / 2) omega)) =
        lastIterate I (LongTails.Setups.RipmLastIterate.step p) p.x0 i j (LongTails.Setups.RipmLastIterate.horizon p) omega := by
  classical
  let eta := LongTails.Setups.RipmLastIterate.step p
  let T := LongTails.Setups.RipmLastIterate.horizon p
  let O := sourceOracle I P i j
  let Path := ℕ → I.Sample × Fin p.m
  let enc : Ω → Path := fun omega k => (i (k / 2) omega, j (k / 2) omega)
  let a : ℕ → Path → I.Sample := fun t path => (path (2 * t)).1
  let b : ℕ → Path → Fin p.m := fun t path => (path (2 * t + 1)).2
  have heta : 0 < eta := (target_tuning_legal p hp).2.1
  have he : Measurable enc := Measurable.of_eval (fun k =>
    (hsamples.1.measurable (k / 2)).prodMk (hsamples.2 (k / 2)).1)
  have ha (t : ℕ) : Measurable (a t) := measurable_fst.comp (measurable_pi_apply (2 * t))
  have hb (t : ℕ) : Measurable (b t) := measurable_snd.comp (measurable_pi_apply (2 * t + 1))
  have hae (t : ℕ) (omega : Ω) : a t (enc omega) = i t omega := by
    change i ((2 * t) / 2) omega = i t omega
    congr 1
    omega
  have hbe (t : ℕ) (omega : Ω) : b t (enc omega) = j t omega := by
    change j ((2 * t + 1) / 2) omega = j t omega
    congr 1
    omega
  have htraj (n : ℕ) (omega : Ω) :
      Core.trajectory I eta p.x0 a b n (enc omega) =
        Core.trajectory I eta p.x0 i j n omega := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Core.prox (I.regularizers (b n (enc omega))) (eta * p.m)
        (Core.trajectory I eta p.x0 a b n (enc omega) -
          eta • I.grad (a n (enc omega)) (Core.trajectory I eta p.x0 a b n (enc omega))) =
        Core.prox (I.regularizers (j n omega)) (eta * p.m)
        (Core.trajectory I eta p.x0 i j n omega -
          eta • I.grad (i n omega) (Core.trajectory I eta p.x0 i j n omega))
      rw [hae, hbe, ih]
  have hmapa (t : ℕ) : (P.toMeasure.map enc).map (a t) = I.law.toMeasure := by
    rw [Measure.map_map (ha t) he]
    have hfun : a t ∘ enc = i t := funext (hae t)
    rw [hfun]
    exact hsamples.1.marginal t
  have hindep {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (f : Path → A) (g : Path → B) (hf : Measurable f) (hg : Measurable g)
      (hfg : ProbabilityTheory.IndepFun (f ∘ enc) (g ∘ enc) P.toMeasure) :
      ProbabilityTheory.IndepFun f g (P.toMeasure.map enc) := by
    apply ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro s t hs ht
    rw [Measure.map_apply he ((hf hs).inter (hg ht)),
      Measure.map_apply he (hf hs), Measure.map_apply he (hg ht)]
    simpa only [Set.preimage_inter, Set.preimage_comp] using
      hfg.measure_inter_preimage_eq_mul s t hs ht
  have hs : Core.Sampling I O.law eta p.x0 a b := by
    constructor
    · refine ⟨ha, ?_, hmapa⟩
      change ProbabilityTheory.iIndepFun a (P.toMeasure.map enc)
      apply ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
      intro S sets hsets
      have hinter : MeasurableSet (⋂ t ∈ S, a t ⁻¹' sets t) := by
        apply MeasurableSet.iInter
        intro t
        apply MeasurableSet.iInter
        intro ht
        exact ha t (hsets t ht)
      rw [Measure.map_apply he hinter]
      have hsingle (t : ℕ) (ht : t ∈ S) :
          P.toMeasure.map enc (a t ⁻¹' sets t) = P.toMeasure (i t ⁻¹' sets t) := by
        rw [Measure.map_apply he (ha t (hsets t ht))]
        congr 1
        ext omega
        simp only [Set.mem_preimage, hae]
      rw [Finset.prod_congr rfl hsingle]
      have hset : enc ⁻¹' (⋂ t ∈ S, a t ⁻¹' sets t) = ⋂ t ∈ S, i t ⁻¹' sets t := by
        ext omega
        simp only [Set.mem_preimage, Set.mem_iInter, hae]
      rw [hset]
      exact hsamples.1.independent.measure_inter_preimage_eq_mul S hsets
    · intro t
      let hist : Path → (Fin (t + 1) → Core.Vec p.d) :=
        fun path s => Core.trajectory I eta p.x0 a b s path
      have hh : Measurable hist := Measurable.of_eval (fun s =>
        LongTails.Proofs.RipmRegularity.trajectory_measurable I p.L p.Lg eta p.x0 p.xstar
          sigmaSq a b hsource heta ha hb s)
      have hhenc : hist ∘ enc =
          (fun omega => fun s : Fin (t + 1) => Core.trajectory I eta p.x0 i j s omega) := by
        funext omega s
        exact htraj s omega
      have hia : ProbabilityTheory.IndepFun (a t) hist (P.toMeasure.map enc) := by
        apply hindep (a t) hist (ha t) hh
        have hi : ProbabilityTheory.IndepFun (i t)
            (fun omega => fun s : Fin (t + 1) => Core.trajectory I eta p.x0 i j s omega) P.toMeasure :=
          (hsamples.2 t).2.1
        have hai : a t ∘ enc = i t := funext (hae t)
        rw [hai, hhenc]
        exact hi
      have hjb : ProbabilityTheory.IndepFun (b t) hist (P.toMeasure.map enc) := by
        apply hindep (b t) hist (hb t) hh
        have hj : ProbabilityTheory.IndepFun (j t)
            (fun omega => fun s : Fin (t + 1) => Core.trajectory I eta p.x0 i j s omega) P.toMeasure :=
          (hsamples.2 t).2.2.1
        have hbj : b t ∘ enc = j t := funext (hbe t)
        rw [hbj, hhenc]
        exact hj
      refine ⟨hb t, hia, hjb, ?_⟩
      obtain ⟨hm, hjlaw⟩ := (hsamples.2 t).2.2.2
      refine ⟨hm, ?_⟩
      change (P.toMeasure.map enc).map (b t) = _
      rw [Measure.map_map (hb t) he]
      have hbj : b t ∘ enc = j t := funext (hbe t)
      rw [hbj]
      exact hjlaw
  let decodeI : (k : ℕ) → O.Seed k → I.Sample := fun _ s => s.1
  let decodeJ : (k : ℕ) → O.Seed k → Fin p.m := fun _ s => s.2
  have hO : Core.OracleExact I O decodeI decodeJ := by
    refine ⟨fun _ => ⟨measurable_fst, measurable_snd⟩, ?_⟩
    intro history q seed
    constructor
    · intro hq
      change (if q.1 = 0 then I.grad seed.1 q.2.2
        else Core.prox (I.regularizers seed.2) q.2.1 q.2.2) = _
      rw [ite_eq_left hq]
    · intro hq _hscale
      have hq0 : q.1 ≠ 0 := by rw [hq]; decide
      change (if q.1 = 0 then I.grad seed.1 q.2.2
        else Core.prox (I.regularizers seed.2) q.2.1 q.2.2) = _
      rw [ite_eq_right hq0]
  constructor
  · exact ⟨sigmaSq, decodeI, decodeJ, hsource, hSigma, hD, hDelta, hO, hs⟩
  · intro omega
    have hc := LongTails.Proofs.RipmExecution.execute_correspondence
      (LongTails.Setups.RipmLastIterate.publicInput p) I O decodeI decodeJ hO heta hsource.countPos T () (enc omega)
    exact hc.trans (htraj (T + 1) omega)


lemma target_rate_to_accuracy (p : LongTails.Setups.RipmLastIterate.Params) (hp : LongTails.Setups.RipmLastIterate.valid p)
    (D2 Delta sigmaSq R : ℝ) (hD0 : 0 ≤ D2) (hD : D2 ≤ p.D2)
    (hDelta0 : 0 ≤ Delta) (hDelta : Delta ≤ p.Delta)
    (hSigma0 : 0 ≤ sigmaSq) (hSigma : sigmaSq ≤ p.S)
    (hR : R ≤ LongTails.Proofs.RipmRates.targetBound (LongTails.Setups.RipmLastIterate.horizon p) p.m p.L p.Lg D2 Delta sigmaSq) :
    R ≤ p.epsilon := by
  obtain ⟨hm, hL, hLg, hDp, hDelp, hSp, heps⟩ := hp
  let B := LongTails.Setups.RipmLastIterate.boundScale p
  let T := LongTails.Setups.RipmLastIterate.horizon p
  let s := Real.sqrt T
  let N := (sigmaSq + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L
  let Np := (p.S + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L
  have hLg2 : 0 ≤ p.Lg ^ 2 := pow_nonneg hLg 2
  have hB : 0 ≤ B := by
    change 0 ≤ p.L * p.D2 + p.Delta + (p.S + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L
    positivity
  have hhor := log_horizon_accuracy B 10 p.epsilon hB (by norm_num) heps
  change 1 ≤ T ∧ 10 * B / s * (1 + 4 * Real.log ((T : ℝ) + 1)) ≤ p.epsilon at hhor
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hhor.1
  have hTp : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTr
  have hs : 0 < s := Real.sqrt_pos.mpr hTp
  have hs1 : 1 ≤ s := (Real.le_sqrt (by norm_num) hTp.le).mpr (by simpa using hTr)
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hN : N ≤ Np := div_le_div_of_nonneg_right (by linarith) hL.le
  have hDterm : p.L * D2 ≤ p.L * p.D2 := mul_le_mul le_rfl hD hD0 hL.le
  have hDelterm : Delta / s ≤ p.Delta := by
    have h := div_le_div_of_nonneg_left hDelta0 (by norm_num : (0 : ℝ) < 1) hs1
    rw [div_one] at h
    exact h.trans hDelta
  have hrecip : 1 / (T : ℝ) ≤ 1 := (div_le_iff₀ hTp).mpr (by linarith)
  have hnoise : N * (1 / T + 4 * Real.log ((T : ℝ) + 1)) ≤
      Np * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 1 / (T : ℝ) + 4 * Real.log ((T : ℝ) + 1) ≤ 1 + 4 * Real.log ((T : ℝ) + 1) by linarith) hN0
    have h2 := mul_le_mul_of_nonneg_right hN
      (show 0 ≤ 1 + 4 * Real.log ((T : ℝ) + 1) by positivity)
    exact h1.trans h2
  have hinit : p.L * p.D2 + p.Delta ≤
      (p.L * p.D2 + p.Delta) * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
    have h := mul_nonneg (show 0 ≤ p.L * p.D2 + p.Delta by positivity) hlog
    nlinarith only [h]
  have hbracket : p.L * D2 + Delta / s + N * (1 / T + 4 * Real.log ((T : ℝ) + 1)) ≤
      B * (1 + 4 * Real.log ((T : ℝ) + 1)) := by
    change _ ≤ (p.L * p.D2 + p.Delta + Np) * _
    calc
      _ ≤ (p.L * p.D2 + p.Delta) * (1 + 4 * Real.log ((T : ℝ) + 1)) +
          Np * (1 + 4 * Real.log ((T : ℝ) + 1)) :=
        add_le_add ((add_le_add hDterm hDelterm).trans hinit) hnoise
      _ = _ := by ring
  have hr := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ 10 / s by positivity)
  change R ≤ 10 / s * (p.L * D2 + Delta / s + N * (1 / T + 4 * Real.log ((T : ℝ) + 1))) at hR
  have heq : 10 / s * (B * (1 + 4 * Real.log ((T : ℝ) + 1))) =
      10 * B / s * (1 + 4 * Real.log ((T : ℝ) + 1)) := by ring
  rw [heq] at hr
  exact hR.trans (hr.trans hhor.2)


lemma target_execution_accuracy (p : LongTails.Setups.RipmLastIterate.Params) (hp : LongTails.Setups.RipmLastIterate.valid p)
    (I : Core.Problem p.d p.m)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2)
    (hO : LongTails.Setups.RipmLastIterate.admissible p I O) :
    let A := method (LongTails.Setups.RipmLastIterate.publicInput p)
    let out := fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      OracleTemplate.execute O A (fun _ => LongTails.Setups.RipmLastIterate.horizon p + 1) seed.1 seed.2
    let P : ProbabilityMeasure (A.Seed × ((k : ℕ) → O.Seed k)) :=
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩
    Measurable out ∧
      Integrable (fun omega => Core.objective I (out omega) - Core.objective I p.xstar)
        (P : Measure _) ∧
      (∫ omega, Core.objective I (out omega) - Core.objective I p.xstar ∂(P : Measure _)) ≤
        p.epsilon := by
  obtain ⟨sigmaSq, decodeI, decodeJ, hS, hSigma, hD, hDelta, hExact, hSamples⟩ := hO
  have hlegal := target_tuning_legal p hp
  let T := LongTails.Setups.RipmLastIterate.horizon p
  let eta := LongTails.Setups.RipmLastIterate.step p
  let i := fun (t : ℕ) (omega : (k : ℕ) → O.Seed k) => decodeI (2 * t) (omega (2 * t))
  let j := fun (t : ℕ) (omega : (k : ℕ) → O.Seed k) => decodeJ (2 * t + 1) (omega (2 * t + 1))
  let X := lastIterate I eta p.x0 i j T
  let A := method (LongTails.Setups.RipmLastIterate.publicInput p)
  let out := fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
    OracleTemplate.execute O A (fun _ => T + 1) seed.1 seed.2
  have hout : out = (fun seed => X seed.2) := by
    funext seed
    exact LongTails.Proofs.RipmExecution.execute_correspondence
      (LongTails.Setups.RipmLastIterate.publicInput p) I O decodeI decodeJ hExact hlegal.2.1
      hS.countPos T seed.1 seed.2
  have hsampling : Core.Sampling I O.law eta p.x0 i j := hSamples
  have hmeas : Measurable X := LongTails.Proofs.RipmRegularity.trajectory_measurable
    I p.L p.Lg eta p.x0 p.xstar sigmaSq i j hS hlegal.2.1
    hsampling.1.measurable (fun k => (hsampling.2 k).1) (T + 1)
  have hint : Integrable (fun omega => Core.objective I (X omega) - Core.objective I p.xstar)
      O.law.toMeasure :=
    (LongTails.Proofs.RipmRegularity.objective_integrable I O.law p.L p.Lg eta
      p.x0 p.xstar sigmaSq i j hS hlegal.2.1 hsampling (T + 1)).sub' (integrable_const _)
  have hSigma0 : 0 ≤ sigmaSq := by
    obtain ⟨v, hv, hi, heq⟩ := hS.solutionMoment
    rw [← heq]
    exact integral_nonneg (fun s => sq_nonneg _)
  have hDelta0 : 0 ≤ Core.objective I p.x0 - Core.objective I p.xstar :=
    sub_nonneg.mpr (hS.minimizer (Set.mem_univ p.x0))
  have hdist0 : 0 ≤ Core.distanceSq I p.x0 := sq_nonneg _
  have hdist : Core.distanceSq I p.x0 ≤ p.D2 := by
    have hmem : p.xstar ∈ Core.solutionSet I := hS.minimizer
    have hle := Metric.infDist_le_dist_of_mem hmem (x := p.x0)
    rw [dist_eq_norm] at hle
    have h0 := Metric.infDist_nonneg (x := p.x0) (s := Core.solutionSet I)
    change Metric.infDist p.x0 (Core.solutionSet I) ^ 2 ≤ p.D2
    exact ((sq_le_sq₀ h0 (norm_nonneg (p.x0 - p.xstar))).mpr hle).trans hD
  have hrate := LongTails.Proofs.RipmRates.theorem41 I O.law p.L p.Lg
    p.x0 p.xstar sigmaSq i j hS T hlegal.1 hsampling
  have hacc := target_rate_to_accuracy p hp (Core.distanceSq I p.x0)
    (Core.objective I p.x0 - Core.objective I p.xstar) sigmaSq
    (∫ omega, Core.objective I (X omega) - Core.objective I p.xstar ∂O.law.toMeasure)
    hdist0 hdist hDelta0 hDelta hSigma0 hSigma hrate
  change Measurable out ∧
    Integrable (fun omega => Core.objective I (out omega) - Core.objective I p.xstar)
      ((A.law : Measure _).prod (O.law : Measure _)) ∧
    (∫ omega, Core.objective I (out omega) - Core.objective I p.xstar
      ∂((A.law : Measure _).prod (O.law : Measure _))) ≤ p.epsilon
  rw [hout]
  refine ⟨hmeas.comp measurable_snd, hint.comp_snd _, ?_⟩
  let gap := fun (omega : (k : ℕ) → O.Seed k) =>
    Core.objective I (X omega) - Core.objective I p.xstar
  change (∫ seed : A.Seed × ((k : ℕ) → O.Seed k), gap seed.2
    ∂((A.law : Measure _).prod (O.law : Measure _))) ≤ p.epsilon
  rw [integral_fun_snd gap, probReal_univ, one_smul]
  exact hacc


lemma target_cost (p : LongTails.Setups.RipmLastIterate.Params)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2)
    (seed : (method (LongTails.Setups.RipmLastIterate.publicInput p)).Seed) (omega : (k : ℕ) → O.Seed k)
    (q : Fin 2) :
    ((OracleTemplate.executeWithTrace O (method (LongTails.Setups.RipmLastIterate.publicInput p))
      (fun _ => LongTails.Setups.RipmLastIterate.horizon p + 1) seed omega).2.countP
        (fun entry => entry.1.1 == q)) = LongTails.Setups.RipmLastIterate.horizon p + 1 := by
  exact LongTails.Proofs.RipmExecution.trace_cost (LongTails.Setups.RipmLastIterate.publicInput p)
    O (LongTails.Setups.RipmLastIterate.horizon p) seed omega q

end

end LongTails.Proofs.RipmAccuracy
