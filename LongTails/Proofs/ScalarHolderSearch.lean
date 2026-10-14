import LongTails.Algorithms.ScalarHolderSearch
import LongTails.Proofs.ScalarSearchBudget
import LongTails.Proofs.ScalarGradientSearch
import LongTails.Proofs.ScalarSearchProbability

open MeasureTheory Classical

set_option backward.isDefEq.respectTransparency false

namespace OracleTemplate.ScalarHolderSearch

lemma time_tail_preserving (q : LongTails.Setups.ScalarHolderStochastic.Params) (n : ℕ) :
    MeasurePreserving
      (fun seed : (ℕ → ℝ) × (ℕ → Fin (16 * depth q)) =>
        ((seed.1, fun i : Fin n => seed.2 i), fun j => seed.2 (n + j)))
      (seedLaw q : Measure _)
      (((Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)).prod
        (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure)).prod
        (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure)) :=
  ScalarHeavyTailEstimator.seed_prefix_tail_preserving
    (P := (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure)
    (Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)) n

lemma probe_prefix_preserving (q : LongTails.Setups.ScalarHolderStochastic.Params) (n : ℕ) :
    MeasurePreserving
      (fun seed : (ℕ → ℝ) × (ℕ → Fin (16 * depth q)) => ((fun i : Fin n => seed.1 i), seed.2))
      (seedLaw q : Measure _)
      ((Measure.pi fun _ : Fin n => (unitLaw : Measure ℝ)).prod
        (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure)) :=
  (StochasticGeneralized.prefix_preserving (unitLaw : Measure ℝ) n).prod (MeasurePreserving.id _)

lemma depth_pos (q : LongTails.Setups.ScalarHolderStochastic.Params) : 0 < depth q := by
  unfold depth
  omega

lemma depth_accuracy (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    q.H * (distance q / (2 : ℝ) ^ depth q) ^ q.ν ≤ q.ε / 8 := by
  let K := (8 * q.H / q.ε) ^ (1 / q.ν)
  have hK : 0 < K := by dsimp [K]; positivity
  have hR : 0 < distance q := by unfold distance; positivity
  have hpow : K ^ q.ν = 8 * q.H / q.ε := by
    dsimp [K]
    rw [one_div, Real.rpow_inv_rpow (by positivity) hν.ne']
  have hl := ScalarHeavyTailEstimator.dyadic_ceil_lower (distance q * K)
  have hceil : ⌈Real.logb 2 (max 1 (distance q * K))⌉₊ ≤ depth q := le_max_right _ _
  have hscale : distance q * K ≤ (2 : ℝ) ^ depth q :=
    hl.trans (pow_le_pow_right₀ (by norm_num) hceil)
  have hwidth : distance q / (2 : ℝ) ^ depth q ≤ 1 / K := by
    apply (div_le_div_iff₀ (by positivity) hK).mpr
    simpa using hscale
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ distance q / (2 : ℝ) ^ depth q) hwidth hν.le
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hK.le, Real.one_rpow, hpow] at hrpow
  have h := mul_le_mul_of_nonneg_left hrpow hH.le
  have he : q.H * (1 / (8 * q.H / q.ε)) = q.ε / 8 := by field_simp
  rwa [he] at h

lemma levelCalls_sum (q : LongTails.Setups.ScalarHolderStochastic.Params) (n : ℕ) :
    levelCalls q n = ∑ j ∈ Finset.range n, probeCalls q j * probes j := by
  induction n with
  | zero => simp [levelCalls]
  | succ n ih => simp only [levelCalls, Finset.sum_range_succ, ih]

lemma probe_scale (q : LongTails.Setups.ScalarHolderStochastic.Params) (j : ℕ) :
    scale q j / 12 = q.ε / 48 * (2 : ℝ) ^ j := by unfold scale; ring

lemma discovery_cost_bound (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) (hp : 1 < q.p) (hp2 : q.p ≤ 2) :
    (discoveryCalls q : ℝ) ≤ 1024 * (2 : ℝ) ^ (28 / (q.p - 1)) *
      (132 * (4 : ℝ) ^ ScalarHeavyTailEstimator.noiseLevel q.σ (q.ε / 48) +
        194 * (2 : ℝ) ^ levels q + 165 * (q.σ / (q.ε / 48)) ^ (q.p / (q.p - 1)) + 33) := by
  have hsum := ScalarHeavyTailEstimator.discovery_calls_sum hσ (by positivity : 0 < q.ε / 48) hp hp2 (levels q)
  have hzero := ScalarHeavyTailEstimator.calls_bound hσ (by positivity : 0 < q.ε / 48) hp hp2 33
  have hk : ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) 0 = 33 := by
    simp [ScalarHeavyTailEstimator.repetitions]
  have hnear : (probeCalls q 0 : ℝ) ≤ 33 * (2 : ℝ) ^ (28 / (q.p - 1)) *
      (1 + (q.σ / (q.ε / 48)) ^ (q.p / (q.p - 1))) := by
    simpa only [probeCalls, hk, probe_scale, pow_zero, mul_one, Nat.cast_ofNat] using hzero
  have hlevel : (levelCalls q (levels q + 1) : ℝ) = 1024 *
      ∑ j ∈ Finset.range (levels q + 1), (2 : ℝ) ^ j *
        (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48 * (2 : ℝ) ^ j)
          (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j) : ℝ) := by
    rw [levelCalls_sum]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [probeCalls, probes, probe_scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    ring
  unfold discoveryCalls
  push_cast
  rw [hlevel]
  nlinarith

lemma scale_pos (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε) (j : ℕ) : 0 < scale q j := by
  unfold scale
  positivity

lemma inspect_accuracy (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (j : ℕ) (near : Bool) (point value g : ℝ) (flag : Bool) (x : ℝ)
    (hne : near = true → j = 0) (herr : |value - g| ≤ scale q j / 4)
    (hout : inspect q j near point value = some (flag, x)) :
    x = point ∧ (flag = true → |g| ≤ q.ε) ∧ (flag = false → 0 < g) := by
  cases near with
  | false =>
    simp only [inspect, Bool.false_eq_true, ↓reduceIte] at hout
    split_ifs at hout with hv
    · have he := Option.some.inj hout
      cases he
      have he := (abs_le.mp herr).2
      have hs := scale_pos q hε j
      constructor
      · rfl
      constructor
      · simp
      · intro _
        linarith
  | true =>
    have hj : j = 0 := hne rfl
    subst j
    simp only [scale, pow_zero, mul_one] at herr
    simp only [inspect, ↓reduceIte] at hout
    split_ifs at hout with hv
    · have he := Option.some.inj hout
      cases he
      constructor
      · rfl
      constructor
      · intro hflag
        have ha : |value| ≤ q.ε / 2 := of_decide_eq_true hflag
        have ht := abs_sub_le g value 0
        rw [abs_sub_comm g value] at ht
        simp only [sub_zero] at ht
        linarith
      · intro hflag
        have ha : ¬ |value| ≤ q.ε / 2 := of_decide_eq_false hflag
        have he := (abs_le.mp herr).2
        have hvp : q.ε / 2 < value := by
          by_contra hn
          exact ha (abs_le.mpr ⟨by linarith, le_of_not_gt hn⟩)
        linarith

lemma inspect_near_detects (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (point value g : ℝ) (herr : |value - g| ≤ q.ε / 16) (hg : -q.ε / 4 ≤ g) :
    (inspect q 0 true point value).isSome = true := by
  have hv : -q.ε / 2 ≤ value := by have he := (abs_le.mp herr).1; linarith
  simp [inspect, hv]

lemma inspect_level_detects (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (j : ℕ) (point value g : ℝ) (herr : |value - g| ≤ scale q j / 4) (hg : scale q j ≤ g) :
    (inspect q j false point value).isSome = true := by
  have hv : scale q j / 2 ≤ value := by
    have he := (abs_le.mp herr).1
    have hs := scale_pos q hε j
    linarith
  simp [inspect, hv]

lemma attemptsPlan_none_iff (q : LongTails.Setups.ScalarHolderStochastic.Params) (s hi : ℝ) (times : ℕ → ℕ)
    (g : ℕ → ℝ → ℝ) (n offset call : ℕ) (result : Option ℝ) :
    ScalarSearchExecution.evalOracle g (attemptsPlan q s hi times n offset result) call = none ↔
      result = none ∧ ∀ i < n, 3 * q.ε / 4 < |(ScalarSearchExecution.evalOracle g
        (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) (times (offset + i)))
        (call + attemptCalls q * i)).2| := by
  induction n generalizing offset call result with
  | zero => simp [attemptsPlan, ScalarSearchExecution.evalOracle]
  | succ n ih =>
    rw [attemptsPlan, ScalarSearchExecution.evalOracle_bind, ih]
    simp only [attemptCalls, Nat.forall_lt_succ_left, Nat.add_zero, Nat.mul_zero, Nat.add_assoc, Nat.mul_add, Nat.mul_one]
    cases result with
    | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
              split_ifs <;> simp_all [Nat.add_comm, Nat.add_assoc]
    | some x => simp

lemma attemptsPlan_some_accuracy (q : LongTails.Setups.ScalarHolderStochastic.Params) (s hi : ℝ) (times : ℕ → ℕ)
    (g : ℕ → ℝ → ℝ) (μ : ℝ → ℝ) (n offset call : ℕ) (result : Option ℝ)
    (hinitial : ∀ x, result = some x → |μ x| ≤ q.ε)
    (hvalid : ∀ i < n,
      let pair := ScalarSearchExecution.evalOracle g
        (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) (times (offset + i)))
        (call + attemptCalls q * i)
      |pair.2| ≤ 3 * q.ε / 4 → |μ pair.1| ≤ q.ε) :
    ∀ x, ScalarSearchExecution.evalOracle g (attemptsPlan q s hi times n offset result) call = some x →
      |μ x| ≤ q.ε := by
  induction n generalizing offset call result with
  | zero => simpa [attemptsPlan, ScalarSearchExecution.evalOracle] using hinitial
  | succ n ih =>
    rw [attemptsPlan, ScalarSearchExecution.evalOracle_bind]
    apply ih
    · intro x hx
      split_ifs at hx with hsome haccept
      · exact hinitial x hx
      · have h := hvalid 0 (by omega) haccept
        simp only [Option.some.injEq] at hx
        simpa only [Nat.add_zero, Nat.mul_zero] using hx ▸ h
    · intro i hi'
      simpa only [attemptCalls, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hvalid (i + 1) (by omega)

lemma root_record_tail (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (hO : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s hi : ℝ} (hs : |s| = 1) (hhi : 0 ≤ hi) (hR : hi ≤ distance q)
    (hlo : s * deriv f q.x0 < 0) (hhiPos : 0 < s * deriv f (q.x0 + s * hi)) (call : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => P).prod (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).real
      {w | 17 * q.ε / 32 < |deriv f (q.x0 + s * ScalarNoisySearch.recordedPoint 0
        (ScalarNoisySearch.trace q.ε (depth q) (2 * depth q)
          (ScalarSearchExecution.walkReplies (fun j x => oracle x (w.1 j)) q.σ q.p q.ε q.x0 s call)
          [.interval 0 hi 0] w.2))|} ≤ 3 / 4 := by
  let D := depth q
  let g : ℝ → ℝ := fun x => s * deriv f (q.x0 + s * x)
  let replies : (ℕ → q.Ω) → ℕ → List ScalarNoisySearch.Node → Fin 3 → ℝ := fun ξ =>
    ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) q.σ q.p q.ε q.x0 s call
  let paths : (ℕ → q.Ω) → ℕ → List ScalarNoisySearch.Node := fun ξ =>
    ScalarNoisySearch.trace q.ε D (2 * D) (replies ξ) [.interval 0 hi 0]
  let A : Set (ℕ → q.Ω) := {ξ | (D : ℝ) < ∑ t : Fin (16 * D),
    (ScalarNoisySearch.badStep g q.ε (replies ξ t (paths ξ t)) (paths ξ t) : ℝ)}
  have hμ : Measurable (deriv f) :=
    (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hD : 0 < D := depth_pos q
  let : NeZero (16 * D) := ⟨by omega⟩
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (ScalarNoisySearch.measurable_walk_bad_count hO.measurable hμ q.σ q.p q.ε q.x0 s D call
      (16 * D) [.interval 0 hi 0])
  have hPA : (Measure.infinitePi fun _ : ℕ => P).real A ≤ 1 / 16 :=
    ScalarSearchProbability.walk_bad_steps P hO.measurable hμ hσ hε hp hp2 hs
      hO.integrable hO.unbiased hO.moment_integrable hO.moment D call hD [.interval 0 hi 0]
  have hraw (j : ℕ) : Measurable (Function.uncurry (fun (ξ : ℕ → q.Ω) x => oracle x (ξ j))) :=
    hO.measurable.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hpaths (t : ℕ) : Measurable (fun ξ => paths ξ t) :=
    ScalarNoisySearch.measurable_trace q.ε D (2 * D) _
      (fun j => ScalarNoisySearch.measurable_walkReplies
        (fun k (ξ : ℕ → q.Ω) x => oracle x (ξ k)) hraw q.σ q.p q.ε q.x0 s call j)
      (fun _ => [.interval 0 hi 0]) measurable_const t
  have hm (ξ : ℕ → q.Ω) (hξ : ξ ∉ A) :
      5 * D ≤ ∑ t ∈ Finset.range (16 * D), ScalarNoisySearch.acceptableStep g q.ε (paths ξ t) := by
    have hcount : (∑ t : Fin (16 * D), ScalarNoisySearch.badStep g q.ε
        (replies ξ t (paths ξ t)) (paths ξ t)) ≤ D := by
      apply (Nat.cast_le (α := ℝ)).mp
      push_cast
      exact le_of_not_gt hξ
    have hbad : (∑ t ∈ Finset.range (16 * D), ScalarNoisySearch.badStep g q.ε
        (replies ξ t (paths ξ t)) (paths ξ t)) ≤ D := by
      rwa [← Fin.sum_univ_eq_sum_range]
    exact ScalarNoisySearch.holder_trace_occupation hε hH.le hν.le
      (ScalarGradientSearch.oriented_holder hs hholder) D hD hhi hR
      (by simpa [g] using hlo) hhiPos (depth_accuracy q hH hν hΔ hε) (replies ξ) hbad
  have ht := ScalarSearchProbability.uniform_occupation_tail (Measure.infinitePi fun _ : ℕ => P)
    (N := 16 * D) (m := 5 * D) (by omega) g hg q.ε 0 paths hpaths A hA hPA hm
  have hDr : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have he : (1 / 16 : ℝ) + (1 - ((5 * D : ℕ) : ℝ) / (16 * D : ℕ)) = 3 / 4 := by
    push_cast
    field_simp
    ring
  rw [he] at ht
  simpa only [paths, replies, g, abs_mul, hs, one_mul] using ht

lemma root_attempt_reject_tail (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (hO : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s hi : ℝ} (hs : |s| = 1) (hhi : 0 ≤ hi) (hR : hi ≤ distance q)
    (hlo : s * deriv f q.x0 < 0) (hhiPos : 0 < s * deriv f (q.x0 + s * hi)) (call : ℕ) :
    ((PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => P)).real {w |
      3 * q.ε / 4 < |(ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) w.1.val) call).2|} ≤ 4 / 5 := by
  let T := (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure
  let R := Measure.infinitePi fun _ : ℕ => P
  let pair := fun w : Fin (16 * depth q) × (ℕ → q.Ω) =>
    ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
      (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) w.1.val) call
  have hμ : Measurable (deriv f) :=
    (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hm : Measurable pair := ScalarNoisySearch.measurable_rootAttempt
    hO.measurable q.σ q.p q.ε q.x0 s hi (depth q) call
  let A := {w | 17 * q.ε / 32 < |deriv f (pair w).1|}
  let B := {w | q.ε / 16 < |(pair w).2 - deriv f (pair w).1|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hμ.comp (measurable_fst.comp hm)))
  have hr := root_record_tail q P hO hH hν hΔ hε hσ hp hp2 hholder hs hhi hR hlo hhiPos call
  have hswap := (Measure.measurePreserving_swap (μ := R) (ν := T)).measure_preimage hA.nullMeasurableSet
  have hPA : (T.prod R).real A ≤ 3 / 4 := by
    unfold Measure.real
    rw [← hswap]
    simpa only [A, pair, R, T, Measure.real, Set.preimage_ofPred_eq, Prod.swap, ScalarSearchExecution.rootAttemptPlan_evalOracle] using hr
  have hPB : (T.prod R).real B ≤ 1 / 4096 :=
    ScalarSearchProbability.root_validation_tail P hO.measurable hμ hσ hε hp hp2
      hO.integrable hO.unbiased hO.moment_integrable hO.moment (depth q) call hi
  have hsub : {w | 3 * q.ε / 4 < |(pair w).2|} ⊆ A ∪ B := by
    intro w hw
    by_contra hn
    have hna : |deriv f (pair w).1| ≤ 17 * q.ε / 32 := by simpa [A] using (not_or.mp hn).1
    have hnb : |(pair w).2 - deriv f (pair w).1| ≤ q.ε / 16 := by simpa [B] using (not_or.mp hn).2
    have ht := abs_add_le ((pair w).2 - deriv f (pair w).1) (deriv f (pair w).1)
    have he : (pair w).2 - deriv f (pair w).1 + deriv f (pair w).1 = (pair w).2 := by ring
    rw [he] at ht
    change 3 * q.ε / 4 < |(pair w).2| at hw
    linarith
  exact (measureReal_mono hsub).trans ((measureReal_union_le A B).trans (by linarith))

lemma attemptCalls_pos (q : LongTails.Setups.ScalarHolderStochastic.Params) : 0 < attemptCalls q := by
  have h : 0 < ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6 := by
    unfold ScalarHeavyTailEstimator.calls ScalarHeavyTailEstimator.blockSize
    split_ifs <;> positivity
  unfold attemptCalls
  omega

lemma attempts_none_tail (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (hO : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s hi : ℝ} (hs : |s| = 1) (hhi : 0 ≤ hi) (hR : hi ≤ distance q)
    (hlo : s * deriv f q.x0 < 0) (hhiPos : 0 < s * deriv f (q.x0 + s * hi)) (n offset call : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => P)).real {w |
      ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (attemptsPlan q s hi (fun j => (w.1 j).val) n offset none) call = none} ≤ (4 / 5 : ℝ) ^ n := by
  let E : Set (Fin (16 * depth q) × (ℕ → q.Ω)) := {w | 3 * q.ε / 4 <
    |(ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
      (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) w.1.val) 0).2|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (continuous_abs.measurable.comp
    (measurable_snd.comp (ScalarNoisySearch.measurable_rootAttempt hO.measurable q.σ q.p q.ε q.x0 s hi (depth q) 0)))
  have hreads : ∀ time (a c : ℕ → q.Ω), (∀ j < attemptCalls q, a j = c j) →
      ((time, a) ∈ E ↔ (time, c) ∈ E) := by
    intro time a c hac
    have he := ScalarSearchExecution.evalOracle_congr (fun j x => oracle x (a j))
      (fun j x => oracle x (c j))
      (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) time.val) 0 (by
        intro j hj hj' x
        exact congrArg (oracle x) (hac j (by simpa only [Nat.zero_add, attemptCalls] using hj')))
    simp only [E, Set.mem_ofPred_eq, he]
  have ht := ScalarSearchProbability.independent_trials_tail P
    (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure
    (attemptCalls q) n offset call (attemptCalls_pos q) E hE hreads
    (root_attempt_reject_tail q P hO hH hν hΔ hε hσ hp hp2 hholder hs hhi hR hlo hhiPos 0)
  have heq : {w : (ℕ → Fin (16 * depth q)) × (ℕ → q.Ω) |
      ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (attemptsPlan q s hi (fun j => (w.1 j).val) n offset none) call = none} =
      {w | ∀ i : Fin n, (w.1 (offset + i.val), fun j => w.2 (call + i.val * attemptCalls q + j)) ∈ E} := by
    ext w
    rw [Set.mem_ofPred_eq, attemptsPlan_none_iff]
    simp only [true_and, E, Set.mem_ofPred_eq]
    have hshift (i : Fin n) : ScalarSearchExecution.evalOracle
        (fun j x => oracle x (w.2 (call + i.val * attemptCalls q + j)))
        (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) (w.1 (offset + i.val)).val) 0 =
        ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) (w.1 (offset + i.val)).val)
        (call + i.val * attemptCalls q) :=
      ScalarSearchExecution.evalOracle_shift (fun j x => oracle x (w.2 j)) _ _ 0
    simp only [hshift, Nat.mul_comm]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [heq]
  exact ht

lemma attempts_accuracy_tail (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (hO : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s hi : ℝ} (hs : |s| = 1) (hhi : 0 ≤ hi) (hR : hi ≤ distance q)
    (hlo : s * deriv f q.x0 < 0) (hhiPos : 0 < s * deriv f (q.x0 + s * hi)) (n offset call : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => P)).real {w |
      q.ε < |deriv f ((ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (attemptsPlan q s hi (fun j => (w.1 j).val) n offset none) call).getD q.x0)|} ≤
      (4 / 5 : ℝ) ^ n + n / 4096 := by
  let T := (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure
  let R := Measure.infinitePi fun _ : ℕ => P
  let S := (Measure.infinitePi fun _ : ℕ => T).prod R
  let result := fun w : (ℕ → Fin (16 * depth q)) × (ℕ → q.Ω) =>
    ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
      (attemptsPlan q s hi (fun j => (w.1 j).val) n offset none) call
  let A := {w | result w = none}
  let pair := fun (i : Fin n) (w : Fin (16 * depth q) × (ℕ → q.Ω)) =>
    ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
      (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) w.1.val)
      (call + attemptCalls q * i.val)
  let E := fun i : Fin n => {w | |(pair i w).2| ≤ 3 * q.ε / 4 ∧ q.ε < |deriv f (pair i w).1|}
  let B := fun i : Fin n => {w : (ℕ → Fin (16 * depth q)) × (ℕ → q.Ω) |
    (w.1 (offset + i.val), w.2) ∈ E i}
  have hμ : Measurable (deriv f) :=
    (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hpair (i : Fin n) : Measurable (pair i) :=
    ScalarNoisySearch.measurable_rootAttempt hO.measurable q.σ q.p q.ε q.x0 s hi (depth q) _
  have hE (i : Fin n) : MeasurableSet (E i) :=
    (measurableSet_le (continuous_abs.measurable.comp (measurable_snd.comp (hpair i))) measurable_const).inter
      (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hμ.comp (measurable_fst.comp (hpair i)))))
  have hPB (i : Fin n) : S.real (B i) ≤ 1 / 4096 := by
    have hpre := ((measurePreserving_eval_infinitePi (fun _ : ℕ => T) (offset + i.val)).prod
      (MeasurePreserving.id R)).measure_preimage (hE i).nullMeasurableSet
    have ht := ScalarSearchProbability.root_false_accept_tail P hO.measurable hμ
      (x0 := q.x0) (s := s) hσ hε hp hp2 hO.integrable hO.unbiased hO.moment_integrable hO.moment
      (depth q) (call + attemptCalls q * i.val) hi
    change (T.prod R).real (E i) ≤ 1 / 4096 at ht
    unfold Measure.real at ht ⊢
    rw [← hpre] at ht
    exact ht
  have hPA : S.real A ≤ (4 / 5 : ℝ) ^ n :=
    attempts_none_tail q P hO hH hν hΔ hε hσ hp hp2 hholder hs hhi hR hlo hhiPos n offset call
  have hsum : S.real (⋃ i : Fin n, B i) ≤ n / 4096 := by
    calc
      _ ≤ ∑ i : Fin n, S.real (B i) := measureReal_iUnion_fintype_le B
      _ ≤ ∑ _ : Fin n, (1 / 4096 : ℝ) := Finset.sum_le_sum (fun i _ => hPB i)
      _ = _ := by simp; ring
  have hsub : {w | q.ε < |deriv f ((result w).getD q.x0)|} ⊆ A ∪ ⋃ i : Fin n, B i := by
    intro w hw
    by_cases ha : w ∈ A
    · exact Or.inl ha
    by_cases hb : w ∈ ⋃ i : Fin n, B i
    · exact Or.inr hb
    have hvalid : ∀ i < n,
        let pair := ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
          (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) (w.1 (offset + i)).val)
          (call + attemptCalls q * i)
        |pair.2| ≤ 3 * q.ε / 4 → |deriv f pair.1| ≤ q.ε := by
      intro i hi'
      dsimp only
      intro haccept
      by_contra hn
      apply hb
      exact Set.mem_iUnion.mpr ⟨⟨i, hi'⟩, haccept, lt_of_not_ge hn⟩
    have hacc := attemptsPlan_some_accuracy q s hi (fun j => (w.1 j).val)
      (fun j x => oracle x (w.2 j)) (deriv f) n offset call none (by simp) hvalid
    cases hr : result w with
    | none => exact False.elim (ha hr)
    | some x =>
      have hx := hacc x hr
      have hx' : q.ε < |deriv f x| := by simpa only [Set.mem_ofPred_eq, hr, Option.getD_some] using hw
      exact False.elim (not_lt_of_ge hx hx')
  exact (measureReal_mono hsub).trans ((measureReal_union_le A _).trans (by linarith))

lemma measurable_attempts_value {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (endpoint : Z → ℝ) (hend : Measurable endpoint)
    (times : Z → ℕ → Fin (16 * depth q)) (htimes : ∀ i, Measurable (fun z => times z i))
    (n offset call : ℕ) (result : Z → Option ℝ)
    (hvalue : Measurable (fun z => (result z).getD q.x0))
    (hflag : MeasurableSet {z | (result z).isSome = true}) :
    Measurable (fun z => (ScalarSearchExecution.evalOracle (fun j x => g j z x)
      (attemptsPlan q s (endpoint z) (fun j => (times z j).val) n offset (result z)) call).getD q.x0) ∧
    MeasurableSet {z | (ScalarSearchExecution.evalOracle (fun j x => g j z x)
      (attemptsPlan q s (endpoint z) (fun j => (times z j).val) n offset (result z)) call).isSome = true} := by
  induction n generalizing offset call result with
  | zero => simpa only [attemptsPlan, ScalarSearchExecution.evalOracle] using And.intro hvalue hflag
  | succ n ih =>
    let pair : Z → ℝ × ℝ := fun z => ScalarSearchExecution.evalOracle (fun j x => g j z x)
      (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s (endpoint z) (depth q) (times z offset).val) call
    have hpair : Measurable pair := ScalarNoisySearch.measurable_rootAttempt_variable g hg
      q.σ q.p q.ε q.x0 s (depth q) call endpoint hend (fun z => times z offset) (htimes offset)
    have haccept : MeasurableSet {z | |(pair z).2| ≤ 3 * q.ε / 4} :=
      measurableSet_le (continuous_abs.measurable.comp (measurable_snd.comp hpair)) measurable_const
    let next : Z → Option ℝ := fun z => if (result z).isSome then result z else
      if |(pair z).2| ≤ 3 * q.ε / 4 then some (pair z).1 else none
    have heval : (fun z => (next z).getD q.x0) = fun z =>
        if (result z).isSome then (result z).getD q.x0 else
          if |(pair z).2| ≤ 3 * q.ε / 4 then (pair z).1 else q.x0 := by
      funext z
      dsimp only [next]
      split_ifs <;> rfl
    have hv : Measurable (fun z => (next z).getD q.x0) := by
      rw [heval]
      exact Measurable.ite hflag hvalue (Measurable.ite haccept (measurable_fst.comp hpair) measurable_const)
    have heflag : {z | (next z).isSome = true} =
        {z | (result z).isSome = true} ∪ {z | |(pair z).2| ≤ 3 * q.ε / 4} := by
      ext z
      simp only [next, Set.mem_ofPred_eq, Set.mem_union]
      split_ifs <;> simp_all
    have hf : MeasurableSet {z | (next z).isSome = true} := by rw [heflag]; exact hflag.union haccept
    simpa only [attemptsPlan, ScalarSearchExecution.evalOracle_bind, next, pair] using
      ih (offset + 1) (call + attemptCalls q) next hv hf

lemma conditional_attempts_accuracy {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (hO : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s : ℝ} (hs : |s| = 1) (hlo : s * deriv f q.x0 < 0)
    (endpoint : Z → ℝ) (hend : Measurable endpoint) (A : Set Z) (hA : MeasurableSet A)
    {α : ℝ} (hPA : Q.real A ≤ α)
    (hbracket : ∀ z ∉ A, 0 ≤ endpoint z ∧ endpoint z ≤ distance q ∧
      0 < s * deriv f (q.x0 + s * endpoint z)) (n offset call : ℕ) :
    (Q.prod ((Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => P))).real {w |
      q.ε < |deriv f ((ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2.2 j))
        (attemptsPlan q s (endpoint w.1) (fun j => (w.2.1 j).val) n offset none) call).getD q.x0)|} ≤
      α + ((4 / 5 : ℝ) ^ n + n / 4096) := by
  let W := Z × ((ℕ → Fin (16 * depth q)) × (ℕ → q.Ω))
  let g : ℕ → W → ℝ → ℝ := fun j w x => oracle x (w.2.2 j)
  have hg (j : ℕ) : Measurable (Function.uncurry (g j)) := hO.measurable.comp
    (measurable_snd.prodMk ((measurable_pi_apply j).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have he : Measurable (fun w : W => endpoint w.1) := hend.comp measurable_fst
  have ht (i : ℕ) : Measurable (fun w : W => w.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hval := (measurable_attempts_value q s g hg (fun w : W => endpoint w.1) he
    (fun w : W => w.2.1) ht n offset call (fun _ => none) measurable_const (by simp)).1
  have hμ : Measurable (deriv f) :=
    (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hB := measurableSet_lt (measurable_const (a := q.ε))
    (continuous_abs.measurable.comp (hμ.comp hval))
  have hpoint (z : Z) (hz : z ∉ A) :=
    attempts_accuracy_tail q P hO hH hν hΔ hε hσ hp hp2 hholder hs
      (hbracket z hz).1 (hbracket z hz).2.1 hlo (hbracket z hz).2.2 n offset call
  have h := ScalarHeavyTailEstimator.conditional_failure hA hB
    (by positivity : (0 : ℝ) ≤ (4 / 5 : ℝ) ^ n + n / 4096) hPA hpoint
  simpa only [g, Function.comp_def] using h

lemma conditional_active_attempts_accuracy {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (hO : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s : ℝ} (hs : |s| = 1) (hlo : s * deriv f q.x0 < 0)
    (endpoint : Z → ℝ) (hend : Measurable endpoint) (A : Set Z) (hA : MeasurableSet A)
    (C : Set Z) (hC : MeasurableSet C)
    {α : ℝ} (hPA : Q.real A ≤ α)
    (hbracket : ∀ z ∉ A, z ∈ C → 0 ≤ endpoint z ∧ endpoint z ≤ distance q ∧
      0 < s * deriv f (q.x0 + s * endpoint z)) (n offset call : ℕ) :
    (Q.prod ((Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => P))).real {w |
      w.1 ∈ C ∧ q.ε < |deriv f ((ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2.2 j))
        (attemptsPlan q s (endpoint w.1) (fun j => (w.2.1 j).val) n offset none) call).getD q.x0)|} ≤
      α + ((4 / 5 : ℝ) ^ n + n / 4096) := by
  let W := Z × ((ℕ → Fin (16 * depth q)) × (ℕ → q.Ω))
  let g : ℕ → W → ℝ → ℝ := fun j w x => oracle x (w.2.2 j)
  have hg (j : ℕ) : Measurable (Function.uncurry (g j)) := hO.measurable.comp
    (measurable_snd.prodMk ((measurable_pi_apply j).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have he : Measurable (fun w : W => endpoint w.1) := hend.comp measurable_fst
  have ht (i : ℕ) : Measurable (fun w : W => w.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hval := (measurable_attempts_value q s g hg (fun w : W => endpoint w.1) he
    (fun w : W => w.2.1) ht n offset call (fun _ => none) measurable_const (by simp)).1
  have hμ : Measurable (deriv f) :=
    (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hB := measurableSet_lt (measurable_const (a := q.ε))
    (continuous_abs.measurable.comp (hμ.comp hval))
  have hBC := (hC.preimage measurable_fst).inter hB
  have hpoint (z : Z) (hz : z ∉ A) :
      ((Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
        (Measure.infinitePi fun _ : ℕ => P)).real {w |
          z ∈ C ∧ q.ε < |deriv f ((ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
            (attemptsPlan q s (endpoint z) (fun j => (w.1 j).val) n offset none) call).getD q.x0)|} ≤
        (4 / 5 : ℝ) ^ n + n / 4096 := by
    by_cases hc : z ∈ C
    · simpa only [hc, true_and] using
        attempts_accuracy_tail q P hO hH hν hΔ hε hσ hp hp2 hholder hs
          (hbracket z hz hc).1 (hbracket z hz hc).2.1 hlo (hbracket z hz hc).2.2 n offset call
    · simp only [hc, false_and, Set.ofPred_false, measureReal_empty]
      positivity
  have h := ScalarHeavyTailEstimator.conditional_failure hA hBC
    (by positivity : (0 : ℝ) ≤ (4 / 5 : ℝ) ^ n + n / 4096) hPA hpoint
  convert h using 1
  congr 1

lemma discovery_capped_mass (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hmean : -q.ε / 32 ≤ ∫ u, g (distance q * u) ∂(unitLaw : Measure ℝ))
    (hcap : ∀ x ∈ Set.Icc 0 (distance q), g x ≤ 2 * scale q (levels q))
    (hR : 0 ≤ distance q) :
    448 ≤ 1024 * (unitLaw : Measure ℝ).real {u | -q.ε / 4 ≤ g (distance q * u)} +
      ∑ j : Fin (levels q + 1), (probes j.val : ℝ) *
        (unitLaw : Measure ℝ).real {u | scale q j.val ≤ g (distance q * u)} := by
  have hc : Continuous (fun u => g (distance q * u)) := hg.comp (continuous_const.mul continuous_id)
  have hi : Integrable (fun u => g (distance q * u)) (unitLaw : Measure ℝ) := hc.integrableOn_Icc
  have hbound : ∀ᵐ u ∂(unitLaw : Measure ℝ), g (distance q * u) ≤ q.ε / 4 * 2 ^ (levels q + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hx : distance q * u ∈ Set.Icc 0 (distance q) := by
      constructor
      · exact mul_nonneg hR hu.1
      · simpa using mul_le_mul_of_nonneg_left hu.2 hR
    have hh := hcap _ hx
    simpa only [scale, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have hm : -(q.ε / 32) ≤ ∫ u, g (distance q * u) ∂(unitLaw : Measure ℝ) := by linarith
  have h := ScalarGradientSearch.dyadic_cover_mass (unitLaw : Measure ℝ) hc.measurable hi
    (by positivity : 0 ≤ q.ε / 4) (levels q + 1) hm hbound
  have he : (2048 / q.ε) * (q.ε / 4 - q.ε / 32) = (448 : ℝ) := by field_simp; ring
  calc
    448 = (2048 / q.ε) * (q.ε / 4 - q.ε / 32) := he.symm
    _ ≤ (2048 / q.ε) * (2 * (q.ε / 4) * (unitLaw : Measure ℝ).real {u | -(q.ε / 4) ≤ g (distance q * u)} +
      ∑ j : Fin (levels q + 1), 2 * (q.ε / 4 * 2 ^ j.val) *
        (unitLaw : Measure ℝ).real {u | q.ε / 4 * 2 ^ j.val ≤ g (distance q * u)}) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · have hn : -(q.ε / 4) = -q.ε / 4 := by ring
        rw [hn]
        field_simp
        ring
      · apply Finset.sum_congr rfl
        intro j hj
        unfold scale probes
        push_cast
        field_simp
        ring

lemma oriented_mean_lower (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    {f : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (deriv f x) x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {lower s : ℝ} (hs : |s| = 1) (hlower : ∀ x, lower ≤ f x) (hgap : f q.x0 - lower ≤ q.Δ) :
    -q.ε / 32 ≤ ∫ u, s * deriv f (q.x0 + s * (distance q * u)) ∂(unitLaw : Measure ℝ) := by
  have hgc := ScalarGradientSearch.continuous_of_holder hH.le hν
    (ScalarGradientSearch.oriented_holder hs hholder (x0 := q.x0))
  have h := ScalarGradientSearch.uniform_derivative_lower
    (R := distance q) (by unfold distance; positivity)
    (ScalarGradientSearch.oriented_derivative hderiv q.x0 s) hgc
    (fun y => hlower (q.x0 + s * y)) (by simpa using hgap)
  have he : -q.Δ / distance q = -q.ε / 32 := by unfold distance; field_simp
  rw [he] at h
  exact h

lemma top_scale_lower (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε) :
    q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) ≤ scale q (levels q) := by
  let M := q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν))
  have h := ScalarHeavyTailEstimator.dyadic_ceil_lower
    (4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε)
  change 4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε ≤ (2 : ℝ) ^ levels q at h
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ q.ε / 4)
  have he : q.ε / 4 * (4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε) = M := by
    dsimp [M]
    field_simp
  rw [he] at hh
  exact hh

lemma discovery_peak_mass (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (g : ℝ → ℝ) (hzero : g 0 ≤ 0)
    (hholder : ∀ x y, |g x - g y| ≤ q.H * |x - y| ^ q.ν)
    {z : ℝ} (hz : z ∈ Set.Icc 0 (distance q)) (hpeak : 2 * scale q (levels q) ≤ g z) :
    128 ≤ (probes (levels q) : ℝ) * (unitLaw : Measure ℝ).real
      {u | scale q (levels q) ≤ g (distance q * u)} := by
  let S := scale q (levels q)
  let w := (S / q.H) ^ (1 / q.ν)
  have hS : 0 < S := scale_pos q hε _
  have hw : 0 < w := by dsimp [w]; positivity
  have hR : 0 < distance q := by unfold distance; positivity
  have hscale : q.H * w ^ q.ν = S := by
    dsimp [w]
    rw [one_div, Real.rpow_inv_rpow (by positivity) hν.ne']
    field_simp
  have hgap : q.Δ ≤ S * w := ScalarGradientSearch.peak_width_gap hH hΔ hν (top_scale_lower q hε)
  have hm := ScalarGradientSearch.uniform_peak_mass hH.le hν.le hw.le hS hR hz hscale.le hzero hpeak hholder
  have hcount : (probes (levels q) : ℝ) = 4096 / q.ε * S := by
    dsimp [S, scale, probes]
    push_cast
    field_simp
    ring
  have he : (4096 / q.ε * S) * (w / distance q) = 128 * (S * w / q.Δ) := by
    unfold distance
    field_simp
    ring
  have hratio : 1 ≤ S * w / q.Δ := (le_div_iff₀ hΔ).mpr (by simpa using hgap)
  calc
    128 ≤ (probes (levels q) : ℝ) * (w / distance q) := by rw [hcount, he]; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

lemma discovery_hit_mass (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (g : ℝ → ℝ) (hzero : g 0 ≤ 0)
    (hholder : ∀ x y, |g x - g y| ≤ q.H * |x - y| ^ q.ν)
    (hmean : -q.ε / 32 ≤ ∫ u, g (distance q * u) ∂(unitLaw : Measure ℝ)) :
    128 ≤ 1024 * (unitLaw : Measure ℝ).real {u | -q.ε / 4 ≤ g (distance q * u)} +
      ∑ j : Fin (levels q + 1), (probes j.val : ℝ) *
        (unitLaw : Measure ℝ).real {u | scale q j.val ≤ g (distance q * u)} := by
  have hg := ScalarGradientSearch.continuous_of_holder hH.le hν hholder
  by_cases hc : ∀ x ∈ Set.Icc 0 (distance q), g x ≤ 2 * scale q (levels q)
  · have h := discovery_capped_mass q hε g hg hmean hc (by unfold distance; positivity)
    linarith
  · push Not at hc
    obtain ⟨z, hz, hpeak⟩ := hc
    have hp := discovery_peak_mass q hH hν hΔ hε g hzero hholder hz hpeak.le
    have hs := Finset.single_le_sum
      (f := fun j : Fin (levels q + 1) => (probes j.val : ℝ) *
        (unitLaw : Measure ℝ).real {u | scale q j.val ≤ g (distance q * u)})
      (fun j _ => by positivity) (Finset.mem_univ (⟨levels q, by omega⟩ : Fin (levels q + 1)))
    have hn : 0 ≤ 1024 * (unitLaw : Measure ℝ).real {u | -q.ε / 4 ≤ g (distance q * u)} := by positivity
    exact hp.trans (hs.trans (by linarith))

lemma probePlan_none_iff (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ) (j : ℕ) (near : Bool)
    (samples : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (n offset call : ℕ) (result : Option (Bool × ℝ)) :
    ScalarSearchExecution.evalOracle g (probePlan q s j near samples n offset result) call = none ↔
      result = none ∧ ∀ i < n, inspect q j near (distance q * samples (offset + i))
        (s * ScalarSearchExecution.evalOracle g
          (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
            (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
            (q.x0 + s * (distance q * samples (offset + i))))
          (call + probeCalls q j * i)) = none := by
  induction n generalizing offset call result with
  | zero => simp [probePlan, ScalarSearchExecution.evalOracle]
  | succ n ih =>
    rw [probePlan, ScalarSearchExecution.evalOracle_bind, ih]
    simp only [probeCalls, Nat.forall_lt_succ_left, Nat.add_zero, Nat.mul_zero,
      Nat.add_assoc, Nat.mul_add, Nat.mul_one]
    cases result with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp [Nat.add_comm]
    | some v => simp

lemma probePlan_some_property (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ) (j : ℕ) (near : Bool)
    (samples : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (V : Bool × ℝ → Prop)
    (n offset call : ℕ) (result : Option (Bool × ℝ))
    (hinitial : ∀ v, result = some v → V v)
    (hvalid : ∀ i < n, ∀ v, inspect q j near (distance q * samples (offset + i))
        (s * ScalarSearchExecution.evalOracle g
          (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
            (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
            (q.x0 + s * (distance q * samples (offset + i))))
          (call + probeCalls q j * i)) = some v → V v) :
    ∀ v, ScalarSearchExecution.evalOracle g (probePlan q s j near samples n offset result) call = some v → V v := by
  induction n generalizing offset call result with
  | zero => simpa only [probePlan, ScalarSearchExecution.evalOracle] using hinitial
  | succ n ih =>
    rw [probePlan, ScalarSearchExecution.evalOracle_bind]
    apply ih
    · intro v hv
      split_ifs at hv with hsome
      · exact hinitial v hv
      · simpa only [Nat.add_zero, Nat.mul_zero] using hvalid 0 (by omega) v hv
    · intro i hi
      simpa only [probeCalls, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hvalid (i + 1) (by omega)

lemma discovery_miss_probability (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (g : ℝ → ℝ) (hzero : g 0 ≤ 0)
    (hholder : ∀ x y, |g x - g y| ≤ q.H * |x - y| ^ q.ν)
    (hmean : -q.ε / 32 ≤ ∫ u, g (distance q * u) ∂(unitLaw : Measure ℝ)) :
    (Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)).real {ξ |
      (∀ i : Fin 1024, g (distance q * ξ i.val) < -q.ε / 4) ∧
      ∀ j : Fin (levels q + 1), ∀ i : Fin (probes j.val),
        g (distance q * ξ (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)) <
          scale q j.val} ≤ Real.exp (-128) := by
  let I := Sum (Fin 1024) ((j : Fin (levels q + 1)) × Fin (probes j.val))
  let index : I → ℕ
    | .inl i => i.val
    | .inr v => 1024 + (∑ k ∈ Finset.Ico (v.1.val + 1) (levels q + 1), probes k) + v.2.val
  let events : I → Set ℝ
    | .inl _ => {u | -q.ε / 4 ≤ g (distance q * u)}
    | .inr v => {u | scale q v.1.val ≤ g (distance q * u)}
  have hinj : Function.Injective index := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext hab)
      | inr b => dsimp [index] at hab; have ha := a.isLt; omega
    | inr a =>
      cases b with
      | inl b => dsimp [index] at hab; have hb := b.isLt; omega
      | inr b =>
        dsimp [index] at hab
        have he : (∑ k ∈ Finset.Ico (a.1.val + 1) (levels q + 1), probes k) + a.2.val =
            (∑ k ∈ Finset.Ico (b.1.val + 1) (levels q + 1), probes k) + b.2.val := by omega
        exact congrArg Sum.inr (ScalarSearchProbability.reverse_block_index_injective probes (levels q + 1) he)
  have hg := ScalarGradientSearch.continuous_of_holder hH.le hν hholder
  have hm (i : I) : MeasurableSet (events i) := by
    cases i <;> exact measurableSet_le measurable_const (hg.measurable.comp (by fun_prop))
  have hmass : 128 ≤ ∑ i : I, (unitLaw : Measure ℝ).real (events i) := by
    simpa only [I, events, Fintype.sum_sum_type, Fintype.sum_sigma, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
      discovery_hit_mass q hH hν hΔ hε g hzero hholder hmean
  let A : Set (I → ℝ) := {ξ | ∀ i, ξ i ∉ events i}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => (hm i).compl.preimage (measurable_pi_apply i))
  have ht : (Measure.pi fun _ : I => (unitLaw : Measure ℝ)).real A ≤ Real.exp (-128) :=
    (ScalarSearchProbability.no_hits (unitLaw : Measure ℝ) events hm).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hpre := (ScalarSearchProbability.indexed_samples_preserving (unitLaw : Measure ℝ) index hinj).measure_preimage
    hA.nullMeasurableSet
  unfold Measure.real at ht ⊢
  rw [← hpre] at ht
  convert ht using 1
  congr 2
  ext ξ
  simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, hl⟩ i
    cases i with
    | inl i => simpa only [index, events, Set.mem_ofPred_eq, not_le] using hn i
    | inr v => simpa only [index, events, Set.mem_ofPred_eq, not_le] using hl v.1 v.2
  · intro h
    constructor
    · intro i
      simpa only [index, events, Set.mem_ofPred_eq, not_le] using h (.inl i)
    · intro j i
      simpa only [index, events, Set.mem_ofPred_eq, not_le] using h (.inr ⟨j, i⟩)

lemma levelsPlan_none_iff (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (samples : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (n offset call : ℕ) (result : Option (Bool × ℝ)) :
    ScalarSearchExecution.evalOracle g (levelsPlan q s samples n offset result) call = none ↔
      result = none ∧ ∀ j < n,
        ScalarSearchExecution.evalOracle g
          (probePlan q s j false samples (probes j)
            (offset + ∑ k ∈ Finset.Ico (j + 1) n, probes k) none)
          (call + ∑ k ∈ Finset.Ico (j + 1) n, probeCalls q k * probes k) = none := by
  induction n generalizing offset call result with
  | zero => simp [levelsPlan, ScalarSearchExecution.evalOracle]
  | succ n ih =>
    rw [levelsPlan, ScalarSearchExecution.evalOracle_bind, ih]
    rw [probePlan_none_iff]
    constructor
    · rintro ⟨⟨hr, ht⟩, hl⟩
      refine ⟨hr, ?_⟩
      intro j hj
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hj
      · simpa only [Finset.Ico_self, Finset.sum_empty, Nat.add_zero,
          probePlan_none_iff, true_and] using ht
      · have h := hl j hj
        simpa only [Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hj),
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · rintro ⟨hr, hl⟩
      refine ⟨⟨hr, ?_⟩, ?_⟩
      · have h := hl n (by omega)
        simpa only [Finset.Ico_self, Finset.sum_empty, Nat.add_zero,
          probePlan_none_iff, true_and] using h
      · intro j hj
        have h := hl j (by omega)
        simpa only [Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hj),
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma levelsPlan_some_property (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (samples : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (V : Bool × ℝ → Prop)
    (n offset call : ℕ) (result : Option (Bool × ℝ))
    (hinitial : ∀ v, result = some v → V v)
    (hvalid : ∀ j < n, ∀ r : Option (Bool × ℝ), (∀ v, r = some v → V v) →
      ∀ v, ScalarSearchExecution.evalOracle g
        (probePlan q s j false samples (probes j)
          (offset + ∑ k ∈ Finset.Ico (j + 1) n, probes k) r)
        (call + ∑ k ∈ Finset.Ico (j + 1) n, probeCalls q k * probes k) = some v → V v) :
    ∀ v, ScalarSearchExecution.evalOracle g (levelsPlan q s samples n offset result) call = some v → V v := by
  induction n generalizing offset call result with
  | zero => simpa only [levelsPlan, ScalarSearchExecution.evalOracle] using hinitial
  | succ n ih =>
    rw [levelsPlan, ScalarSearchExecution.evalOracle_bind]
    apply ih
    · simpa only [Finset.Ico_self, Finset.sum_empty, Nat.add_zero] using
        hvalid n (by omega) result hinitial
    · intro j hj r hr
      have h := hvalid j (by omega) r hr
      simpa only [Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hj),
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma discoveryPlan_none_iff (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (samples : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (call : ℕ) :
    ScalarSearchExecution.evalOracle g (discoveryPlan q s samples) call = none ↔
      ScalarSearchExecution.evalOracle g (probePlan q s 0 true samples 1024 0 none) call = none ∧
      ∀ j < levels q + 1, ScalarSearchExecution.evalOracle g
        (probePlan q s j false samples (probes j)
          (1024 + ∑ k ∈ Finset.Ico (j + 1) (levels q + 1), probes k) none)
        (call + probeCalls q 0 * 1024 +
          ∑ k ∈ Finset.Ico (j + 1) (levels q + 1), probeCalls q k * probes k) = none := by
  rw [discoveryPlan, ScalarSearchExecution.evalOracle_bind, levelsPlan_none_iff]

lemma probe_estimate_tail {Z : Type*} {Ω : Type} [MeasurableSpace Z] [MeasurableSpace Ω]
    (Q : Measure Z) [IsProbabilityMeasure Q] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) {f : ℝ → ℝ} {oracle : ℝ → Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hf : Measurable (deriv f)) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε)
    (hp : 1 < q.p) (hp2 : q.p ≤ 2) (query : Z → ℝ) (hq : Measurable query)
    (j call : ℕ) :
    (Q.prod (Measure.infinitePi fun _ : ℕ => P)).real {w |
      scale q j / 4 < |ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
          (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j) (query w.1)) call -
        deriv f (query w.1)|} ≤ (1 / 2 : ℝ) ^ (16 * (j + 1)) := by
  let G : Z → Ω → ℝ := fun z ω => oracle (query z) ω
  let mean : Z → ℝ := fun z => deriv f (query z)
  have hG : Measurable (Function.uncurry G) :=
    ho.measurable.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable mean := hf.comp hq
  have ht := ScalarHeavyTailEstimator.adaptive_scale_tail (P := P) Q hG hm hσ
    (by positivity : 0 < q.ε / 48) hp hp2
    (fun z => ho.integrable (query z)) (fun z => ho.unbiased (query z))
    (fun z => ho.moment_integrable (query z)) (fun z => ho.moment (query z)) j
  have hA := measurableSet_lt (measurable_const (a := 3 * (q.ε / 48 * (2 : ℝ) ^ j)))
    (continuous_abs.measurable.comp
      ((ScalarHeavyTailEstimator.measurable_estimate_joint hG q.σ q.p
        (q.ε / 48 * (2 : ℝ) ^ j) (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)).sub
        (hm.comp measurable_fst)))
  have hpre := ((MeasurePreserving.id Q).prod
    (ScalarHeavyTailEstimator.shift_preserving (P := P) call)).measure_preimage hA.nullMeasurableSet
  unfold Measure.real at ht ⊢
  simp only [Function.comp_def, Pi.sub_apply] at hpre
  rw [← hpre] at ht
  have he : 3 * (q.ε / 48 * (2 : ℝ) ^ j) = scale q j / 4 := by unfold scale; ring
  simpa only [ScalarSearchExecution.estimatePlan_evalOracle_full, probe_scale, he,
    G, mean, Function.comp_def, Pi.sub_apply, Set.preimage_ofPred_eq, Prod.map_fst, Prod.map_snd, id_eq] using ht

lemma discovery_error_union {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (n : ℕ)
    (near : Fin 1024 → Set Z) (events : (j : Fin n) → Fin (probes j.val) → Set Z)
    (hn : ∀ i, Q.real (near i) ≤ (1 / 2 : ℝ) ^ 16)
    (he : ∀ j i, Q.real (events j i) ≤ (1 / 2 : ℝ) ^ (16 * (j.val + 1))) :
    Q.real ((⋃ i, near i) ∪ ⋃ j, ⋃ i, events j i) ≤ 1 / 16 := by
  have hnear : Q.real (⋃ i, near i) ≤ 1024 * (1 / 2 : ℝ) ^ 16 := by
    apply (measureReal_iUnion_fintype_le near).trans
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hn i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  have hlevels : Q.real (⋃ j, ⋃ i, events j i) ≤
      ∑ j : Fin n, (probes j.val : ℝ) * (1 / 2 : ℝ) ^ (16 * (j.val + 1)) := by
    apply (measureReal_iUnion_fintype_le (fun j => ⋃ i, events j i)).trans
    apply Finset.sum_le_sum
    intro j hj
    apply (measureReal_iUnion_fintype_le (events j)).trans
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => he j i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hsum := ScalarSearchProbability.probe_failure_sum n
  have heq : (∑ j : Fin n, (probes j.val : ℝ) * (1 / 2 : ℝ) ^ (16 * (j.val + 1))) =
      ∑ j ∈ Finset.range n, 1024 * (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (16 * (j + 1)) := by
    simp only [probes, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => 1024 * (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (16 * (j + 1))) n
  rw [heq] at hlevels
  exact (measureReal_union_le _ _).trans ((add_le_add hnear hlevels).trans hsum)

lemma discovery_estimates_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) {f : ℝ → ℝ} {oracle : ℝ → Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hf : Measurable (deriv f)) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε)
    (hp : 1 < q.p) (hp2 : q.p ≤ 2) (s : ℝ) (call : ℕ) :
    let error := fun (j index start : ℕ) (w : (ℕ → ℝ) × (ℕ → Ω)) =>
      scale q j / 4 < |ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
          (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
          (q.x0 + s * (distance q * w.1 index))) start -
        deriv f (q.x0 + s * (distance q * w.1 index))|
    ((Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)).prod
      (Measure.infinitePi fun _ : ℕ => P)).real
      ((⋃ i : Fin 1024, {w | error 0 i.val (call + probeCalls q 0 * i.val) w}) ∪
       ⋃ j : Fin (levels q + 1), ⋃ i : Fin (probes j.val), {w |
         error j.val
           (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)
           (call + probeCalls q 0 * 1024 +
             (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probeCalls q k * probes k) +
             probeCalls q j.val * i.val) w}) ≤ 1 / 16 := by
  dsimp only
  apply discovery_error_union
  · intro i
    exact probe_estimate_tail (Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)) P q ho hf
      hσ hε hp hp2 (fun ξ => q.x0 + s * (distance q * ξ i.val)) (by fun_prop) 0 _
  · intro j i
    exact probe_estimate_tail (Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)) P q ho hf
      hσ hε hp hp2 (fun ξ => q.x0 + s * (distance q * ξ
        (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)))
      (by fun_prop) j.val _

lemma discovery_none_true_miss (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (s : ℝ) (samples : ℕ → ℝ) (oracle : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (call : ℕ) :
    let value := fun j index start => s * ScalarSearchExecution.evalOracle oracle
      (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
        (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
        (q.x0 + s * (distance q * samples index))) start
    (∀ i : Fin 1024, |value 0 i.val (call + probeCalls q 0 * i.val) -
      g (distance q * samples i.val)| ≤ q.ε / 16) →
    (∀ j : Fin (levels q + 1), ∀ i : Fin (probes j.val),
      let index := 1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val
      let start := call + probeCalls q 0 * 1024 +
        (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probeCalls q k * probes k) +
        probeCalls q j.val * i.val
      |value j.val index start - g (distance q * samples index)| ≤ scale q j.val / 4) →
    ScalarSearchExecution.evalOracle oracle (discoveryPlan q s samples) call = none →
    (∀ i : Fin 1024, g (distance q * samples i.val) < -q.ε / 4) ∧
    ∀ j : Fin (levels q + 1), ∀ i : Fin (probes j.val),
      g (distance q * samples
        (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)) < scale q j.val := by
  dsimp only
  intro hn hl hnone
  obtain ⟨hnone, hlevels⟩ := (discoveryPlan_none_iff q s samples oracle call).mp hnone
  have hninspect := (probePlan_none_iff q s 0 true samples oracle 1024 0 call none).mp hnone
  constructor
  · intro i
    apply lt_of_not_ge
    intro hhit
    have h := inspect_near_detects q hε (distance q * samples i.val) _ _ (hn i) hhit
    have he := hninspect.2 i.val i.isLt
    simp only [Nat.zero_add] at he
    rw [he] at h
    simp at h
  · intro j i
    apply lt_of_not_ge
    intro hhit
    have h := inspect_level_detects q hε j.val
      (distance q * samples (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val))
      _ _ (hl j i) hhit
    have he := (probePlan_none_iff q s j.val false samples oracle (probes j.val)
      (1024 + ∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k)
      (call + probeCalls q 0 * 1024 +
        ∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probeCalls q k * probes k) none).mp
      (hlevels j.val j.isLt)
    rw [he.2 i.val i.isLt] at h
    simp at h

lemma discoveryPlan_some_property (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (samples : ℕ → ℝ) (oracle : ℕ → ℝ → ℝ) (V : Bool × ℝ → Prop) (call : ℕ)
    (hnear : ∀ v, ScalarSearchExecution.evalOracle oracle
      (probePlan q s 0 true samples 1024 0 none) call = some v → V v)
    (hlevels : ∀ j < levels q + 1, ∀ r : Option (Bool × ℝ), (∀ v, r = some v → V v) →
      ∀ v, ScalarSearchExecution.evalOracle oracle
        (probePlan q s j false samples (probes j)
          (1024 + ∑ k ∈ Finset.Ico (j + 1) (levels q + 1), probes k) r)
        (call + probeCalls q 0 * 1024 +
          ∑ k ∈ Finset.Ico (j + 1) (levels q + 1), probeCalls q k * probes k) = some v → V v) :
    ∀ v, ScalarSearchExecution.evalOracle oracle (discoveryPlan q s samples) call = some v → V v := by
  rw [discoveryPlan, ScalarSearchExecution.evalOracle_bind]
  exact levelsPlan_some_property q s samples oracle V (levels q + 1) 1024
    (call + probeCalls q 0 * 1024) _ hnear hlevels

lemma probePlan_some_accuracy (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (s : ℝ) (j : ℕ) (near : Bool) (hne : near = true → j = 0)
    (samples : ℕ → ℝ) (oracle : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (n offset call : ℕ) (result : Option (Bool × ℝ))
    (hinitial : ∀ v, result = some v → v.2 ∈ Set.Icc 0 (distance q) ∧
      (v.1 = true → |g v.2| ≤ q.ε) ∧ (v.1 = false → 0 < g v.2))
    (hpoints : ∀ i < n, distance q * samples (offset + i) ∈ Set.Icc 0 (distance q))
    (herror : ∀ i < n, |s * ScalarSearchExecution.evalOracle oracle
      (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
        (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
        (q.x0 + s * (distance q * samples (offset + i)))) (call + probeCalls q j * i) -
        g (distance q * samples (offset + i))| ≤ scale q j / 4) :
    ∀ v, ScalarSearchExecution.evalOracle oracle (probePlan q s j near samples n offset result) call = some v →
      v.2 ∈ Set.Icc 0 (distance q) ∧ (v.1 = true → |g v.2| ≤ q.ε) ∧ (v.1 = false → 0 < g v.2) := by
  apply probePlan_some_property q s j near samples oracle _ n offset call result hinitial
  intro i hi v hv
  obtain ⟨hx, hg⟩ := inspect_accuracy q hε j near _ _ _ v.1 v.2 hne (herror i hi) hv
  rw [hx]
  exact ⟨hpoints i hi, hg⟩

lemma measurable_inspect {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (j : ℕ) (near : Bool)
    (point value : Z → ℝ) (hp : Measurable point) (hv : Measurable value) :
    Measurable (fun z => ((inspect q j near (point z) (value z)).getD (false, 0)).2) ∧
    MeasurableSet {z | (inspect q j near (point z) (value z)).isSome = true} ∧
    MeasurableSet {z | ((inspect q j near (point z) (value z)).getD (false, 0)).1 = true} := by
  classical
  cases near with
  | false =>
    have h : MeasurableSet {z | scale q j / 2 ≤ value z} := measurableSet_le measurable_const hv
    constructor
    · have ht : Measurable (fun z => if scale q j / 2 ≤ value z then point z else (0 : ℝ)) :=
        Measurable.ite h hp measurable_const
      convert ht using 1
      funext z
      simp only [inspect, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> rfl
    constructor
    · convert h using 1
      ext z
      simp only [inspect, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    · convert MeasurableSet.empty (α := Z) using 1
      ext z
      simp only [inspect, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      split_ifs <;> simp
  | true =>
    have h : MeasurableSet {z | -q.ε / 2 ≤ value z} := measurableSet_le measurable_const hv
    have ha : MeasurableSet {z | |value z| ≤ q.ε / 2} :=
      measurableSet_le (continuous_abs.measurable.comp hv) measurable_const
    constructor
    · have ht : Measurable (fun z => if -q.ε / 2 ≤ value z then point z else (0 : ℝ)) :=
        Measurable.ite h hp measurable_const
      convert ht using 1
      funext z
      simp only [inspect, ↓reduceIte]
      split_ifs <;> rfl
    constructor
    · convert h using 1
      ext z
      simp only [inspect, ↓reduceIte, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    · convert h.inter ha using 1
      ext z
      simp only [inspect, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_inter_iff]
      split_ifs <;> simp_all

lemma measurable_probePlan_value {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ) (j : ℕ) (near : Bool)
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (samples : Z → ℕ → ℝ) (hsamples : ∀ k, Measurable (fun z => samples z k))
    (n offset call : ℕ) (result : Z → Option (Bool × ℝ))
    (hvalue : Measurable (fun z => ((result z).getD (false, 0)).2))
    (hflag : MeasurableSet {z | (result z).isSome = true})
    (htrue : MeasurableSet {z | ((result z).getD (false, 0)).1 = true}) :
    Measurable (fun z => ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (probePlan q s j near (samples z) n offset (result z)) call).getD (false, 0)).2) ∧
    MeasurableSet {z | (ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (probePlan q s j near (samples z) n offset (result z)) call).isSome = true} ∧
    MeasurableSet {z | ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (probePlan q s j near (samples z) n offset (result z)) call).getD (false, 0)).1 = true} := by
  classical
  induction n generalizing offset call result with
  | zero => simpa only [probePlan, ScalarSearchExecution.evalOracle] using ⟨hvalue, hflag, htrue⟩
  | succ n ih =>
    let point : Z → ℝ := fun z => distance q * samples z offset
    let value : Z → ℝ := fun z => s * ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
        (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j) (q.x0 + s * point z)) call
    have hpoint : Measurable point := measurable_const.mul (hsamples offset)
    have hquery : Measurable (fun z => q.x0 + s * point z) := by fun_prop
    have hstream : Measurable (fun z => fun i : ℕ => g (call + i) z (q.x0 + s * point z)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact (hg _).comp (measurable_id.prodMk hquery)
    have hestimate := ScalarHeavyTailEstimator.measurable_estimate (X := fun x : ℝ => x)
      measurable_id q.σ q.p (scale q j / 12) (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
    have hv : Measurable value := by
      unfold value
      simp only [ScalarSearchExecution.estimatePlan_evalOracle_full]
      exact measurable_const.mul (hestimate.comp hstream)
    obtain ⟨hipoint, hisome, hitrue⟩ := measurable_inspect q j near point value hpoint hv
    let next : Z → Option (Bool × ℝ) := fun z => if (result z).isSome then result z else
      inspect q j near (point z) (value z)
    have hnvalue : Measurable (fun z => ((next z).getD (false, 0)).2) := by
      have ht : Measurable (fun z => if (result z).isSome then ((result z).getD (false, 0)).2
          else ((inspect q j near (point z) (value z)).getD (false, 0)).2) :=
        Measurable.ite hflag hvalue hipoint
      convert ht using 1
      funext z
      dsimp only [next]
      split_ifs <;> rfl
    have hnsome : MeasurableSet {z | (next z).isSome = true} := by
      convert hflag.union hisome using 1
      ext z
      simp only [next, Set.mem_ofPred_eq, Set.mem_union]
      split_ifs <;> simp_all
    have hntrue : MeasurableSet {z | ((next z).getD (false, 0)).1 = true} := by
      convert (hflag.inter htrue).union (hflag.compl.inter hitrue) using 1
      ext z
      simp only [next, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      split_ifs <;> simp_all
    simpa only [probePlan, ScalarSearchExecution.evalOracle_bind, next, point, value] using
      ih (offset + 1) (call + probeCalls q j) next hnvalue hnsome hntrue

lemma measurable_levelsPlan_value {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (samples : Z → ℕ → ℝ) (hsamples : ∀ k, Measurable (fun z => samples z k))
    (n offset call : ℕ) (result : Z → Option (Bool × ℝ))
    (hvalue : Measurable (fun z => ((result z).getD (false, 0)).2))
    (hflag : MeasurableSet {z | (result z).isSome = true})
    (htrue : MeasurableSet {z | ((result z).getD (false, 0)).1 = true}) :
    Measurable (fun z => ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (levelsPlan q s (samples z) n offset (result z)) call).getD (false, 0)).2) ∧
    MeasurableSet {z | (ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (levelsPlan q s (samples z) n offset (result z)) call).isSome = true} ∧
    MeasurableSet {z | ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (levelsPlan q s (samples z) n offset (result z)) call).getD (false, 0)).1 = true} := by
  induction n generalizing offset call result with
  | zero => simpa only [levelsPlan, ScalarSearchExecution.evalOracle] using ⟨hvalue, hflag, htrue⟩
  | succ n ih =>
    obtain ⟨hv, hs, ht⟩ := measurable_probePlan_value q s n false g hg samples hsamples
      (probes n) offset call result hvalue hflag htrue
    simpa only [levelsPlan, ScalarSearchExecution.evalOracle_bind] using
      ih (offset + probes n) (call + probeCalls q n * probes n) _ hv hs ht

lemma measurable_discoveryPlan_value {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (samples : Z → ℕ → ℝ) (hsamples : ∀ k, Measurable (fun z => samples z k)) (call : ℕ) :
    Measurable (fun z => ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (discoveryPlan q s (samples z)) call).getD (false, 0)).2) ∧
    MeasurableSet {z | (ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (discoveryPlan q s (samples z)) call).isSome = true} ∧
    MeasurableSet {z | ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (discoveryPlan q s (samples z)) call).getD (false, 0)).1 = true} := by
  obtain ⟨hv, hs, ht⟩ := measurable_probePlan_value q s 0 true g hg samples hsamples
    1024 0 call (fun _ => none) measurable_const (by simp) (by simp)
  simpa only [discoveryPlan, ScalarSearchExecution.evalOracle_bind] using
    measurable_levelsPlan_value q s g hg samples hsamples (levels q + 1) 1024
      (call + probeCalls q 0 * 1024) _ hv hs ht

lemma discovery_certificate (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (hR : 0 ≤ distance q) (s : ℝ) (samples : ℕ → ℝ) (oracle : ℕ → ℝ → ℝ)
    (g : ℝ → ℝ) (call : ℕ) (hpoints : ∀ i, samples i ∈ Set.Icc 0 1) :
    let value := fun j index start => s * ScalarSearchExecution.evalOracle oracle
      (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
        (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
        (q.x0 + s * (distance q * samples index))) start
    (∀ i : Fin 1024, |value 0 i.val (call + probeCalls q 0 * i.val) -
      g (distance q * samples i.val)| ≤ q.ε / 16) →
    (∀ j : Fin (levels q + 1), ∀ i : Fin (probes j.val),
      let index := 1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val
      let start := call + probeCalls q 0 * 1024 +
        (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probeCalls q k * probes k) +
        probeCalls q j.val * i.val
      |value j.val index start - g (distance q * samples index)| ≤ scale q j.val / 4) →
    ¬ ((∀ i : Fin 1024, g (distance q * samples i.val) < -q.ε / 4) ∧
      ∀ j : Fin (levels q + 1), ∀ i : Fin (probes j.val),
        g (distance q * samples
          (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)) < scale q j.val) →
    ∃ v, ScalarSearchExecution.evalOracle oracle (discoveryPlan q s samples) call = some v ∧
      v.2 ∈ Set.Icc 0 (distance q) ∧ (v.1 = true → |g v.2| ≤ q.ε) ∧ (v.1 = false → 0 < g v.2) := by
  dsimp only
  intro hn hl hhit
  have hp (i : ℕ) : distance q * samples i ∈ Set.Icc 0 (distance q) :=
    ⟨mul_nonneg hR (hpoints i).1, by simpa using mul_le_mul_of_nonneg_left (hpoints i).2 hR⟩
  have hnot : ScalarSearchExecution.evalOracle oracle (discoveryPlan q s samples) call ≠ none := by
    intro he
    exact hhit (discovery_none_true_miss q hε s samples oracle g call hn hl he)
  have hcert : ∀ v, ScalarSearchExecution.evalOracle oracle (discoveryPlan q s samples) call = some v →
      v.2 ∈ Set.Icc 0 (distance q) ∧ (v.1 = true → |g v.2| ≤ q.ε) ∧ (v.1 = false → 0 < g v.2) := by
    refine discoveryPlan_some_property q s samples oracle
      (fun v => v.2 ∈ Set.Icc 0 (distance q) ∧ (v.1 = true → |g v.2| ≤ q.ε) ∧
        (v.1 = false → 0 < g v.2)) call ?_ ?_
    · refine probePlan_some_accuracy q hε s 0 true (by simp) samples oracle g 1024 0 call none ?_ ?_ ?_
      · simp
      · intro i hi
        exact hp _
      · intro i hi
        have h := hn ⟨i, hi⟩
        simpa only [Nat.zero_add, scale, pow_zero, mul_one, div_div, show (4 : ℝ) * 4 = 16 by norm_num] using h
    · intro j hj r hr
      refine probePlan_some_accuracy q hε s j false (by simp) samples oracle g (probes j)
        (1024 + ∑ k ∈ Finset.Ico (j + 1) (levels q + 1), probes k)
        (call + probeCalls q 0 * 1024 +
          ∑ k ∈ Finset.Ico (j + 1) (levels q + 1), probeCalls q k * probes k) r hr ?_ ?_
      · intro i hi
        exact hp _
      · intro i hi
        exact hl ⟨j, hj⟩ ⟨i, hi⟩
  cases he : ScalarSearchExecution.evalOracle oracle (discoveryPlan q s samples) call with
  | none => exact False.elim (hnot he)
  | some v => exact ⟨v, rfl, hcert v he⟩

lemma probe_samples_support :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)),
      ∀ i, ξ i ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (unitLaw : Measure ℝ)) i).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Icc)

lemma discovery_prefix {Ω : Type*}
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ) (samples : ℕ → ℝ)
    (oracle : ℝ → Ω → ℝ) (ξ : ℕ → Ω) (call : ℕ) :
    ScalarSearchExecution.evalOracle (fun k x => oracle x (ξ k)) (discoveryPlan q s samples) call =
      let past : Fin (call + discoveryCalls q) → Ω := fun i => ξ i.val
      ScalarSearchExecution.evalOracle
        (fun k x => if h : k < call + discoveryCalls q then oracle x (past ⟨k, h⟩) else 0)
        (discoveryPlan q s samples) call := by
  dsimp only
  apply ScalarSearchExecution.evalOracle_congr
  intro k hk hk' x
  simp only [hk', ↓reduceDIte]

lemma measurable_discovery_endpoint {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (s : ℝ)
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (samples : Z → ℕ → ℝ) (hsamples : ∀ k, Measurable (fun z => samples z k)) (call : ℕ) :
    Measurable (fun z => match ScalarSearchExecution.evalOracle (fun k x => g k z x)
        (discoveryPlan q s (samples z)) call with
      | some (false, x) => x
      | _ => distance q) := by
  classical
  obtain ⟨hv, hs, ht⟩ := measurable_discoveryPlan_value q s g hg samples hsamples call
  have hm : Measurable (fun z =>
      if (ScalarSearchExecution.evalOracle (fun k x => g k z x)
          (discoveryPlan q s (samples z)) call).isSome = true ∧
          ¬ ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
          (discoveryPlan q s (samples z)) call).getD (false, 0)).1 = true
      then ((ScalarSearchExecution.evalOracle (fun k x => g k z x)
          (discoveryPlan q s (samples z)) call).getD (false, 0)).2 else distance q) :=
    Measurable.ite (hs.inter ht.compl) hv measurable_const
  convert hm using 1
  funext z
  cases he : ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (discoveryPlan q s (samples z)) call with
  | none => simp
  | some v => rcases v with ⟨flag, x⟩; cases flag <;> simp

def DiscoveryCertified (q : LongTails.Setups.ScalarHolderStochastic.Params) (g : ℝ → ℝ)
    (result : Option (Bool × ℝ)) : Prop :=
  ∃ v, result = some v ∧ v.2 ∈ Set.Icc 0 (distance q) ∧
    (v.1 = true → |g v.2| ≤ q.ε) ∧ (v.1 = false → 0 < g v.2)

lemma discoveryCertified_iff (q : LongTails.Setups.ScalarHolderStochastic.Params) (g : ℝ → ℝ)
    (result : Option (Bool × ℝ)) :
    DiscoveryCertified q g result ↔ result.isSome = true ∧
      (result.getD (false, 0)).2 ∈ Set.Icc 0 (distance q) ∧
      ((result.getD (false, 0)).1 = true → |g (result.getD (false, 0)).2| ≤ q.ε) ∧
      (¬ (result.getD (false, 0)).1 = true → 0 < g (result.getD (false, 0)).2) := by
  cases result with
  | none => simp [DiscoveryCertified]
  | some v => rcases v with ⟨flag, x⟩; cases flag <;> simp [DiscoveryCertified]

lemma measurableSet_discoveryCertified {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (g : ℝ → ℝ) (hg : Measurable g)
    (result : Z → Option (Bool × ℝ))
    (hv : Measurable (fun z => ((result z).getD (false, 0)).2))
    (hs : MeasurableSet {z | (result z).isSome = true})
    (ht : MeasurableSet {z | ((result z).getD (false, 0)).1 = true}) :
    MeasurableSet {z | DiscoveryCertified q g (result z)} := by
  have hp := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (distance q))).preimage hv
  have ha := measurableSet_le (continuous_abs.measurable.comp (hg.comp hv))
    (measurable_const (a := q.ε))
  have hpos := measurableSet_lt (measurable_const (a := (0 : ℝ))) (hg.comp hv)
  convert hs.inter (hp.inter ((ht.compl.union ha).inter (ht.union hpos))) using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_preimage, discoveryCertified_iff, imp_iff_not_or, not_not, Function.comp_def]

lemma discovery_certificate_tail (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hderiv : ∀ x, HasDerivAt f (deriv f x) x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {lower s : ℝ} (hs : |s| = 1) (hlower : ∀ x, lower ≤ f x) (hgap : f q.x0 - lower ≤ q.Δ)
    (hzero : s * deriv f q.x0 ≤ 0) (call : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)).prod
      (Measure.infinitePi fun _ : ℕ => P)).real {w |
      ¬ DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x))
        (ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
          (discoveryPlan q s w.1) call)} ≤ 1 / 16 + Real.exp (-128) := by
  let Q := Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)
  let R := Measure.infinitePi fun _ : ℕ => P
  let S := Q.prod R
  let g : ℝ → ℝ := fun x => s * deriv f (q.x0 + s * x)
  let value := fun (j index start : ℕ) (w : (ℕ → ℝ) × (ℕ → q.Ω)) =>
    ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
      (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
        (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)
        (q.x0 + s * (distance q * w.1 index))) start
  let error := fun (j index start : ℕ) (w : (ℕ → ℝ) × (ℕ → q.Ω)) =>
    scale q j / 4 < |value j index start w - deriv f (q.x0 + s * (distance q * w.1 index))|
  let E := (⋃ i : Fin 1024, {w | error 0 i.val (call + probeCalls q 0 * i.val) w}) ∪
    ⋃ j : Fin (levels q + 1), ⋃ i : Fin (probes j.val), {w |
      error j.val
        (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)
        (call + probeCalls q 0 * 1024 +
          (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probeCalls q k * probes k) +
          probeCalls q j.val * i.val) w}
  let F : Set (ℕ → ℝ) := {ξ |
    (∀ i : Fin 1024, g (distance q * ξ i.val) < -q.ε / 4) ∧
    ∀ j : Fin (levels q + 1), ∀ i : Fin (probes j.val),
      g (distance q * ξ (1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val)) <
        scale q j.val}
  have hf := (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hgholder := ScalarGradientSearch.oriented_holder hs hholder (x0 := q.x0)
  have hg : Measurable g := (ScalarGradientSearch.continuous_of_holder hH.le hν hgholder).measurable
  have hE : S.real E ≤ 1 / 16 := discovery_estimates_tail P q ho hf hσ hε hp hp2 s call
  have hFmeas : MeasurableSet F := by
    simp only [F, Set.ofPred_and, Set.ofPred_forall]
    apply MeasurableSet.inter
    · apply MeasurableSet.iInter
      intro i
      exact measurableSet_lt (hg.comp (by fun_prop)) measurable_const
    · apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro i
      exact measurableSet_lt (hg.comp (by fun_prop)) measurable_const
  have hF : S.real {w | w.1 ∈ F} ≤ Real.exp (-128) := by
    have ht := discovery_miss_probability q hH hν hΔ hε g
      (by simpa [g] using hzero) hgholder
      (oriented_mean_lower q hH hν hΔ hε hderiv hholder hs hlower hgap)
    have he := (measurePreserving_fst (μ := Q) (ν := R)).measure_preimage hFmeas.nullMeasurableSet
    change Q.real F ≤ _ at ht
    unfold Measure.real at ht ⊢
    rw [← he] at ht
    exact ht
  have hsupport : ∀ᵐ w ∂S, ∀ i, w.1 i ∈ Set.Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Q) (ν := R)).quasiMeasurePreserving.ae probe_samples_support
  have hsub : {w | ¬ DiscoveryCertified q g
      (ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k)) (discoveryPlan q s w.1) call)} ≤ᵐ[S]
      E ∪ {w | w.1 ∈ F} := by
    filter_upwards [hsupport] with w hpoints
    intro hbad
    by_cases hw : w ∈ E
    · exact Or.inl hw
    apply Or.inr
    by_contra hmiss
    have hbound (j index start : ℕ) (hn : ¬ error j index start w) :
        |s * value j index start w - g (distance q * w.1 index)| ≤ scale q j / 4 := by
      have he : |s * value j index start w - g (distance q * w.1 index)| =
          |value j index start w - deriv f (q.x0 + s * (distance q * w.1 index))| := by
        dsimp only [g]
        rw [← mul_sub, abs_mul, hs, one_mul]
      rw [he]
      exact le_of_not_gt hn
    have hn (i : Fin 1024) : |s * value 0 i.val (call + probeCalls q 0 * i.val) w -
        g (distance q * w.1 i.val)| ≤ q.ε / 16 := by
      have he : scale q 0 / 4 = q.ε / 16 := by unfold scale; norm_num; ring
      rw [← he]
      apply hbound
      intro h
      exact hw (Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩))
    have hl (j : Fin (levels q + 1)) (i : Fin (probes j.val)) :
        let index := 1024 + (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probes k) + i.val
        let start := call + probeCalls q 0 * 1024 +
          (∑ k ∈ Finset.Ico (j.val + 1) (levels q + 1), probeCalls q k * probes k) +
          probeCalls q j.val * i.val
        |s * value j.val index start w - g (distance q * w.1 index)| ≤ scale q j.val / 4 := by
      dsimp only
      apply hbound
      intro h
      exact hw (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨i, h⟩⟩))
    exact hbad (discovery_certificate q hε (by unfold distance; positivity) s w.1
      (fun k x => oracle x (w.2 k)) g call hpoints hn hl hmiss)
  have hm := ENNReal.toReal_mono (measure_ne_top S _) (measure_mono_ae hsub)
  exact hm.trans ((measureReal_union_le E {w | w.1 ∈ F}).trans (add_le_add hE hF))

lemma past_discovery_certificate_tail (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hderiv : ∀ x, HasDerivAt f (deriv f x) x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {lower s : ℝ} (hs : |s| = 1) (hlower : ∀ x, lower ≤ f x) (hgap : f q.x0 - lower ≤ q.Δ)
    (hzero : s * deriv f q.x0 ≤ 0) (call : ℕ) :
    let N := call + discoveryCalls q
    ((Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)).prod
      (Measure.pi fun _ : Fin N => P)).real {w |
      ¬ DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x))
        (ScalarSearchExecution.evalOracle
          (fun k x => if h : k < N then oracle x (w.2 ⟨k, h⟩) else 0)
          (discoveryPlan q s w.1) call)} ≤ 1 / 16 + Real.exp (-128) := by
  let N := call + discoveryCalls q
  let Q := Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)
  let G : ℕ → ((ℕ → ℝ) × (Fin N → q.Ω)) → ℝ → ℝ := fun k w x =>
    if h : k < N then oracle x (w.2 ⟨k, h⟩) else 0
  have hG (k : ℕ) : Measurable (Function.uncurry (G k)) := by
    dsimp only [G, Function.uncurry]
    split_ifs with hk
    · exact ho.measurable.comp (measurable_snd.prodMk
        ((measurable_pi_apply (⟨k, hk⟩ : Fin N)).comp (measurable_snd.comp measurable_fst)))
    · exact measurable_const
  have hf := (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  obtain ⟨hv, hsome, hflag⟩ := measurable_discoveryPlan_value q s G hG
    (fun w => w.1) (by intro k; fun_prop) call
  have hcert := measurableSet_discoveryCertified q (fun x => s * deriv f (q.x0 + s * x))
    (by fun_prop) (fun w => ScalarSearchExecution.evalOracle (fun k x => G k w x)
      (discoveryPlan q s w.1) call) hv hsome hflag
  have hpre := ((MeasurePreserving.id Q).prod
    (StochasticGeneralized.prefix_preserving P N)).measure_preimage hcert.compl.nullMeasurableSet
  have ht := discovery_certificate_tail q P ho hH hν hΔ hε hσ hp hp2 hderiv hholder hs hlower hgap hzero call
  dsimp only
  unfold Measure.real at ht ⊢
  simp only [Set.compl_ofPred] at hpre
  rw [← hpre]
  convert ht using 1
  congr 2
  ext w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, G, Prod.map_fst, Prod.map_snd, id_eq]
  rw [discovery_prefix q s w.1 oracle w.2 call]

lemma measurable_estimatePlan_value {Z : Type*} [MeasurableSpace Z]
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (σ p u : ℝ) (k call : ℕ) (query : Z → ℝ) (hq : Measurable query) :
    Measurable (fun z => ScalarSearchExecution.evalOracle (fun j x => g j z x)
      (ScalarSearchPlans.estimatePlan σ p u k (query z)) call) := by
  have hstream : Measurable (fun z => fun j : ℕ => g (call + j) z (query z)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (hg _).comp (measurable_id.prodMk hq)
  have he := ScalarHeavyTailEstimator.measurable_estimate (X := fun x : ℝ => x) measurable_id σ p u k
  simpa only [ScalarSearchExecution.estimatePlan_evalOracle_full, Function.comp_def] using he.comp hstream

lemma initial_estimate_tail (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) (hp : 1 < q.p) (hp2 : q.p ≤ 2) :
    (Measure.infinitePi fun _ : ℕ => P).real {ξ |
      q.ε / 16 < |ScalarSearchExecution.evalOracle (fun k x => oracle x (ξ k))
        (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0 - deriv f q.x0|} ≤ 1 / 4096 := by
  have ht := ScalarHeavyTailEstimator.estimate_tail
    (ho.measurable.comp measurable_prodMk_left) (ho.integrable q.x0) (ho.unbiased q.x0)
    hσ (by positivity : 0 < q.ε / 48) hp hp2 (ho.moment_integrable q.x0) (ho.moment q.x0) 6
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  have he : 3 * (q.ε / 48) = q.ε / 16 := by ring
  simpa only [ScalarSearchExecution.estimatePlan_evalOracle_full, Nat.zero_add, Measure.real, he,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 4 : ℝ) ^ 6), Function.comp_def,
    Function.uncurry_apply_pair, show (1 / 4 : ℝ) ^ 6 = 1 / 4096 by norm_num,
    ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 4096 : ℝ))] using h

lemma past_initial_estimate_tail (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (N : ℕ) (hN : ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6 ≤ N) :
    (Measure.pi fun _ : Fin N => P).real {ξ |
      q.ε / 16 < |ScalarSearchExecution.evalOracle
        (fun k x => if h : k < N then oracle x (ξ ⟨k, h⟩) else 0)
        (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0 - deriv f q.x0|} ≤ 1 / 4096 := by
  let G : ℕ → (Fin N → q.Ω) → ℝ → ℝ := fun k ξ x =>
    if h : k < N then oracle x (ξ ⟨k, h⟩) else 0
  have hG (k : ℕ) : Measurable (Function.uncurry (G k)) := by
    dsimp only [G, Function.uncurry]
    split_ifs with hk
    · exact ho.measurable.comp (measurable_snd.prodMk
        ((measurable_pi_apply (⟨k, hk⟩ : Fin N)).comp measurable_fst))
    · exact measurable_const
  have hm := measurable_estimatePlan_value G hG q.σ q.p (q.ε / 48) 6 0
    (fun _ => q.x0) measurable_const
  have hA := measurableSet_lt (measurable_const (a := q.ε / 16))
    (continuous_abs.measurable.comp (hm.sub_const (deriv f q.x0)))
  have hpre := (StochasticGeneralized.prefix_preserving P N).measure_preimage hA.nullMeasurableSet
  have ht := initial_estimate_tail q P ho hσ hε hp hp2
  unfold Measure.real at ht ⊢
  simp only [Function.comp_def] at hpre
  rw [← hpre]
  convert ht using 1
  congr 2
  ext ξ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, G]
  have heval : ScalarSearchExecution.evalOracle (fun k x => if h : k < N then oracle x (ξ k) else 0)
      (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0 =
      ScalarSearchExecution.evalOracle (fun k x => oracle x (ξ k))
        (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0 := by
    apply ScalarSearchExecution.evalOracle_congr
    intro k hk hk' x
    have hkn : k < N := lt_of_lt_of_le (by simpa using hk') hN
    simp only [hkn, ↓reduceDIte]
  rw [heval]

lemma plan_evalOracle (q : LongTails.Setups.ScalarHolderStochastic.Params) (samples : ℕ → ℝ) (times : ℕ → ℕ)
    (g : ℕ → ℝ → ℝ) :
    ScalarSearchExecution.evalOracle g (plan q samples times) 0 =
      let first := ScalarSearchExecution.evalOracle g
        (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
      let s : ℝ := if first ≤ 0 then 1 else -1
      let discovered := ScalarSearchExecution.evalOracle g (discoveryPlan q s samples)
        (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6)
      let endpoint := match discovered with | some (false, x) => x | _ => distance q
      let result := ScalarSearchExecution.evalOracle g (attemptsPlan q s endpoint times 32 0 none)
        (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6 + discoveryCalls q)
      if |first| ≤ q.ε / 2 then q.x0 else
        match discovered with | some (true, x) => q.x0 + s * x | _ => result.getD q.x0 := by
  simp only [plan, ScalarSearchExecution.evalOracle_bind, ScalarSearchExecution.evalOracle_map, Nat.zero_add]
  rfl

lemma measurable_plan_value {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (samples : Z → ℕ → ℝ) (hsamples : ∀ k, Measurable (fun z => samples z k))
    (times : Z → ℕ → Fin (16 * depth q)) (htimes : ∀ k, Measurable (fun z => times z k)) :
    Measurable (fun z => ScalarSearchExecution.evalOracle (fun k x => g k z x)
      (plan q (samples z) (fun k => (times z k).val)) 0) := by
  classical
  let c := ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6
  let first : Z → ℝ := fun z => ScalarSearchExecution.evalOracle (fun k x => g k z x)
    (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
  have hfirst : Measurable first := measurable_estimatePlan_value g hg q.σ q.p (q.ε / 48) 6 0
    (fun _ => q.x0) measurable_const
  let found := fun (s : ℝ) z => ScalarSearchExecution.evalOracle (fun k x => g k z x)
    (discoveryPlan q s (samples z)) c
  let endpoint := fun (s : ℝ) z => match found s z with | some (false, x) => x | _ => distance q
  let result := fun (s : ℝ) z => ScalarSearchExecution.evalOracle (fun k x => g k z x)
    (attemptsPlan q s (endpoint s z) (fun k => (times z k).val) 32 0 none) (c + discoveryCalls q)
  let output := fun (s : ℝ) z => if |first z| ≤ q.ε / 2 then q.x0 else
    match found s z with | some (true, x) => q.x0 + s * x | _ => (result s z).getD q.x0
  have houtput (s : ℝ) : Measurable (output s) := by
    obtain ⟨hv, hs, ht⟩ := measurable_discoveryPlan_value q s g hg samples hsamples c
    have hend : Measurable (endpoint s) := measurable_discovery_endpoint q s g hg samples hsamples c
    have hr := (measurable_attempts_value q s g hg (endpoint s) hend times htimes
      32 0 (c + discoveryCalls q) (fun _ => none) measurable_const (by simp)).1
    have hstop : MeasurableSet {z | |first z| ≤ q.ε / 2} :=
      measurableSet_le (continuous_abs.measurable.comp hfirst) measurable_const
    have hm : Measurable (fun z => if |first z| ≤ q.ε / 2 then q.x0 else
        if ((found s z).getD (false, 0)).1 = true then
          q.x0 + s * ((found s z).getD (false, 0)).2 else (result s z).getD q.x0) :=
      Measurable.ite hstop measurable_const
        (Measurable.ite ht (measurable_const.add (measurable_const.mul hv)) hr)
    convert hm using 1
    funext z
    dsimp only [output]
    by_cases hstop : |first z| ≤ q.ε / 2
    · simp only [hstop, ↓reduceIte]
    · simp only [hstop, ↓reduceIte]
      cases he : found s z with
      | none => simp
      | some v => rcases v with ⟨flag, x⟩; cases flag <;> simp
  have hm : Measurable (fun z => if first z ≤ 0 then output 1 z else output (-1) z) :=
    Measurable.ite (measurableSet_le hfirst measurable_const) (houtput 1) (houtput (-1))
  convert hm using 1
  funext z
  rw [plan_evalOracle]
  dsimp only [first, output, result, endpoint, found, c]
  split_ifs <;> rfl

lemma conditional_output_accuracy {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) (P : Measure q.Ω) [IsProbabilityMeasure P]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {s : ℝ} (hs : |s| = 1) (hlo : s * deriv f q.x0 < 0)
    (first : Z → ℝ) (hfirst : Measurable first)
    (found : Z → Option (Bool × ℝ))
    (hv : Measurable (fun z => ((found z).getD (false, 0)).2))
    (hsome : MeasurableSet {z | (found z).isSome = true})
    (hflag : MeasurableSet {z | ((found z).getD (false, 0)).1 = true})
    (endpoint : Z → ℝ) (hend : Measurable endpoint)
    (hendpoint : ∀ z, endpoint z = match found z with | some (false, x) => x | _ => distance q)
    {α β : ℝ} (hinit : Q.real {z | q.ε / 16 < |first z - deriv f q.x0|} ≤ α)
    (hdiscovery : Q.real {z | ¬ DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x)) (found z)} ≤ β)
    (n : ℕ) :
    (Q.prod ((Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => P))).real {w |
      q.ε < |deriv f (if |first w.1| ≤ q.ε / 2 then q.x0 else
        if ((found w.1).getD (false, 0)).1 = true then q.x0 + s * ((found w.1).getD (false, 0)).2
        else (ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2.2 j))
          (attemptsPlan q s (endpoint w.1) (fun j => (w.2.1 j).val) n 0 none) 0).getD q.x0)|} ≤
      2 * (α + β) + (4 / 5 : ℝ) ^ n + n / 4096 := by
  let F := {z | q.ε / 16 < |first z - deriv f q.x0|}
  let D := {z | ¬ DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x)) (found z)}
  let A := F ∪ D
  let C := {z | q.ε / 2 < |first z| ∧ ¬ ((found z).getD (false, 0)).1 = true}
  let R := (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure).prod
    (Measure.infinitePi fun _ : ℕ => P)
  let B := {w : Z × ((ℕ → Fin (16 * depth q)) × (ℕ → q.Ω)) |
    w.1 ∈ C ∧ q.ε < |deriv f ((ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2.2 j))
      (attemptsPlan q s (endpoint w.1) (fun j => (w.2.1 j).val) n 0 none) 0).getD q.x0)|}
  have hf := (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hF : MeasurableSet F := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hfirst.sub_const (deriv f q.x0)))
  have hD : MeasurableSet D :=
    (measurableSet_discoveryCertified q (fun x => s * deriv f (q.x0 + s * x))
      (by fun_prop) found hv hsome hflag).compl
  have hA : MeasurableSet A := hF.union hD
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp hfirst)).inter hflag.compl
  have hPA : Q.real A ≤ α + β := (measureReal_union_le F D).trans (add_le_add hinit hdiscovery)
  have hbracket (z : Z) (hz : z ∉ A) (hc : z ∈ C) :
      0 ≤ endpoint z ∧ endpoint z ≤ distance q ∧ 0 < s * deriv f (q.x0 + s * endpoint z) := by
    have hd : DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x)) (found z) := by
      by_contra h
      exact hz (Or.inr h)
    obtain ⟨⟨flag, x⟩, he, hx, hacc, hpos⟩ := hd
    have hn : flag = false := by
      have hn := hc.2
      rw [he] at hn
      cases flag <;> simp_all
    subst flag
    have hept : endpoint z = x := by rw [hendpoint z, he]
    rw [hept]
    exact ⟨hx.1, hx.2, hpos rfl⟩
  have hPB : (Q.prod R).real B ≤ α + β + ((4 / 5 : ℝ) ^ n + n / 4096) :=
    conditional_active_attempts_accuracy q P Q ho hH hν hΔ hε hσ hp hp2 hholder hs hlo
      endpoint hend A hA C hC hPA hbracket n 0 0
  have hPA' : (Q.prod R).real {w | w.1 ∈ A} ≤ α + β := by
    have he := (measurePreserving_fst (μ := Q) (ν := R)).measure_preimage hA.nullMeasurableSet
    unfold Measure.real at hPA ⊢
    rwa [← he] at hPA
  apply (measureReal_mono (s₂ := {w | w.1 ∈ A} ∪ B) ?_ (by finiteness)).trans
  · have h := (measureReal_union_le {w | w.1 ∈ A} B).trans (add_le_add hPA' hPB)
    linarith
  · intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    by_cases ha : w.1 ∈ A
    · exact Or.inl ha
    have herr : |first w.1 - deriv f q.x0| ≤ q.ε / 16 := by
      apply le_of_not_gt
      intro h
      exact ha (Or.inl h)
    have hd : DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x)) (found w.1) := by
      by_contra h
      exact ha (Or.inr h)
    by_cases hstop : |first w.1| ≤ q.ε / 2
    · have hacc := ScalarGradientSearch.reliable_initial_acceptance herr hstop
      simp only [hstop, ↓reduceIte] at hw
      linarith
    by_cases htrue : ((found w.1).getD (false, 0)).1 = true
    · obtain ⟨⟨flag, x⟩, he, hx, hacc, hpos⟩ := hd
      have ht : flag = true := by simpa only [he, Option.getD_some] using htrue
      have hh := hacc ht
      rw [abs_mul, hs, one_mul] at hh
      simp only [hstop, ↓reduceIte, he, Option.getD_some, ht] at hw
      exact False.elim (not_lt_of_ge hh hw)
    · exact Or.inr ⟨⟨lt_of_not_ge hstop, htrue⟩, by simpa only [hstop, htrue, Bool.false_eq_true, ↓reduceIte] using hw⟩

lemma measurable_conditional_output {Z : Type*} [MeasurableSpace Z]
    (q : LongTails.Setups.ScalarHolderStochastic.Params) {oracle : ℝ → q.Ω → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (s : ℝ)
    (first : Z → ℝ) (hfirst : Measurable first)
    (found : Z → Option (Bool × ℝ))
    (hv : Measurable (fun z => ((found z).getD (false, 0)).2))
    (hflag : MeasurableSet {z | ((found z).getD (false, 0)).1 = true})
    (endpoint : Z → ℝ) (hend : Measurable endpoint) (n : ℕ) :
    Measurable (fun w : Z × ((ℕ → Fin (16 * depth q)) × (ℕ → q.Ω)) =>
      if |first w.1| ≤ q.ε / 2 then q.x0 else
        if ((found w.1).getD (false, 0)).1 = true then q.x0 + s * ((found w.1).getD (false, 0)).2
        else (ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2.2 j))
          (attemptsPlan q s (endpoint w.1) (fun j => (w.2.1 j).val) n 0 none) 0).getD q.x0) := by
  let W := Z × ((ℕ → Fin (16 * depth q)) × (ℕ → q.Ω))
  let G : ℕ → W → ℝ → ℝ := fun j w x => oracle x (w.2.2 j)
  have hG (j : ℕ) : Measurable (Function.uncurry (G j)) := ho.comp
    (measurable_snd.prodMk ((measurable_pi_apply j).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have he : Measurable (fun w : W => endpoint w.1) := hend.comp measurable_fst
  have ht (j : ℕ) : Measurable (fun w : W => w.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hr := (measurable_attempts_value q s G hG (fun w : W => endpoint w.1) he
    (fun w : W => w.2.1) ht n 0 0 (fun _ => none) measurable_const (by simp)).1
  exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp (hfirst.comp measurable_fst)) measurable_const)
    measurable_const (Measurable.ite (hflag.preimage measurable_fst)
      (measurable_const.add (measurable_const.mul (hv.comp measurable_fst))) hr)

lemma optionFlag_output (r : Option (Bool × ℝ)) (x0 s default : ℝ) :
    (match r with | some (true, x) => x0 + s * x | _ => default) =
      if (r.getD (false, 0)).1 = true then x0 + s * (r.getD (false, 0)).2 else default := by
  cases r with
  | none => rfl
  | some v => rcases v with ⟨flag, x⟩; cases flag <;> rfl

lemma plan_fixed_orientation (q : LongTails.Setups.ScalarHolderStochastic.Params) (hε : 0 < q.ε)
    (samples : ℕ → ℝ) (times : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (value : ℝ)
    (herr : |ScalarSearchExecution.evalOracle g
      (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0 - value| ≤ q.ε / 16) :
    let first := ScalarSearchExecution.evalOracle g
      (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
    let s : ℝ := if value ≤ 0 then 1 else -1
    let found := ScalarSearchExecution.evalOracle g (discoveryPlan q s samples)
      (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6)
    let endpoint := match found with | some (false, x) => x | _ => distance q
    ScalarSearchExecution.evalOracle g (plan q samples times) 0 =
      if |first| ≤ q.ε / 2 then q.x0 else
        if (found.getD (false, 0)).1 = true then q.x0 + s * (found.getD (false, 0)).2
        else (ScalarSearchExecution.evalOracle g (attemptsPlan q s endpoint times 32 0 none)
          (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6 + discoveryCalls q)).getD q.x0 := by
  dsimp only
  rw [plan_evalOracle]
  dsimp only
  by_cases hstop : |ScalarSearchExecution.evalOracle g
      (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0| ≤ q.ε / 2
  · simp only [hstop, ↓reduceIte]
  · have hs := (ScalarGradientSearch.reliable_initial_orientation hε herr (lt_of_not_ge hstop)).1
    simp only [hstop, ↓reduceIte, hs]
    exact optionFlag_output _ _ _ _

lemma fixed_orientation_output_tail (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hderiv : ∀ x, HasDerivAt f (deriv f x) x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {lower s : ℝ} (hs : |s| = 1) (hlower : ∀ x, lower ≤ f x) (hgap : f q.x0 - lower ≤ q.Δ)
    (hlo : s * deriv f q.x0 < 0) :
    let c := ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6
    ((seedLaw q : Measure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q)))).prod (Measure.infinitePi fun _ : ℕ => P)).real {w |
      let first := ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
      let found := ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (discoveryPlan q s w.1.1) c
      let endpoint := match found with | some (false, x) => x | _ => distance q
      q.ε < |deriv f (if |first| ≤ q.ε / 2 then q.x0 else
        if (found.getD (false, 0)).1 = true then q.x0 + s * (found.getD (false, 0)).2
        else (ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
          (attemptsPlan q s endpoint (fun k => (w.1.2 k).val) 32 0 none) (c + discoveryCalls q)).getD q.x0)|} ≤
      2 * (1 / 4096 + (1 / 16 + Real.exp (-128))) + (4 / 5 : ℝ) ^ 32 + 32 / 4096 := by
  let c := ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6
  let N := c + discoveryCalls q
  let U := Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)
  let T := Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure
  let Q := U.prod (Measure.pi fun _ : Fin N => P)
  let G : ℕ → ((ℕ → ℝ) × (Fin N → q.Ω)) → ℝ → ℝ := fun k w x =>
    if h : k < N then oracle x (w.2 ⟨k, h⟩) else 0
  have hG (k : ℕ) : Measurable (Function.uncurry (G k)) := by
    dsimp only [G, Function.uncurry]
    split_ifs with hk
    · exact ho.measurable.comp (measurable_snd.prodMk
        ((measurable_pi_apply (⟨k, hk⟩ : Fin N)).comp (measurable_snd.comp measurable_fst)))
    · exact measurable_const
  let first := fun w => ScalarSearchExecution.evalOracle (fun k x => G k w x)
    (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
  let found := fun w => ScalarSearchExecution.evalOracle (fun k x => G k w x) (discoveryPlan q s w.1) c
  let endpoint := fun w => match found w with | some (false, x) => x | _ => distance q
  have hfirst : Measurable first := measurable_estimatePlan_value G hG q.σ q.p (q.ε / 48) 6 0
    (fun _ => q.x0) measurable_const
  obtain ⟨hv, hsome, hflag⟩ := measurable_discoveryPlan_value q s G hG
    (fun w => w.1) (by intro k; fun_prop) c
  have hend : Measurable endpoint := measurable_discovery_endpoint q s G hG
    (fun w => w.1) (by intro k; fun_prop) c
  have hinit : Q.real {w | q.ε / 16 < |first w - deriv f q.x0|} ≤ 1 / 4096 := by
    have ht := past_initial_estimate_tail q P ho hσ hε hp hp2 N (by dsimp [N, c]; omega)
    let F : (Fin N → q.Ω) → ℝ := fun ξ => ScalarSearchExecution.evalOracle
      (fun k x => if h : k < N then oracle x (ξ ⟨k, h⟩) else 0)
      (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
    have hF : Measurable F := hfirst.comp ((measurable_const (a := fun _ : ℕ => (0 : ℝ))).prodMk measurable_id)
    have hA := measurableSet_lt (measurable_const (a := q.ε / 16))
      (continuous_abs.measurable.comp (hF.sub_const (deriv f q.x0)))
    have hpre := (measurePreserving_snd (μ := U) (ν := Measure.pi fun _ : Fin N => P)).measure_preimage
      hA.nullMeasurableSet
    unfold Measure.real at ht ⊢
    simp only [Function.comp_def] at hpre
    rw [← hpre] at ht
    exact ht
  have hdiscovery : Q.real {w | ¬ DiscoveryCertified q (fun x => s * deriv f (q.x0 + s * x)) (found w)} ≤
      1 / 16 + Real.exp (-128) :=
    past_discovery_certificate_tail q P ho hH hν hΔ hε hσ hp hp2 hderiv hholder hs hlower hgap hlo.le c
  have ht := conditional_output_accuracy q P Q ho hH hν hΔ hε hσ hp hp2 hholder hs hlo
    first hfirst found hv hsome hflag endpoint hend (fun _ => rfl) hinit hdiscovery 32
  have hm := measurable_conditional_output q ho.measurable s first hfirst found hv hflag endpoint hend 32
  have hf := (ScalarGradientSearch.continuous_of_holder hH.le hν hholder).measurable
  have hA := measurableSet_lt (measurable_const (a := q.ε))
    (continuous_abs.measurable.comp (hf.comp hm))
  have hpre := (ScalarHeavyTailEstimator.past_future_preserving (P := P) U T N).measure_preimage hA.nullMeasurableSet
  unfold Measure.real at ht ⊢
  simp only [Function.comp_def] at hpre
  rw [← hpre] at ht
  have hfirsteq (w : ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) × (ℕ → q.Ω)) :
      first (w.1.1, fun i : Fin N => w.2 i.val) =
      ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0 := by
    apply ScalarSearchExecution.evalOracle_congr
    intro k hk hk' x
    have hkc : k < c := by simpa only [Nat.zero_add] using hk'
    have hkn : k < N := hkc.trans_le (Nat.le_add_right _ _)
    simp only [G, hkn, ↓reduceDIte]
  have hfoundeq (w : ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) × (ℕ → q.Ω)) :
      found (w.1.1, fun i : Fin N => w.2 i.val) =
      ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k)) (discoveryPlan q s w.1.1) c :=
    (discovery_prefix q s w.1.1 oracle w.2 c).symm
  convert ht using 1
  congr 2
  ext w
  have hshift {k : ℕ} (p : QueryPlan ℝ ℝ (Option ℝ) k) :
      ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 (N + j))) p 0 =
        ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j)) p N := by
    simpa only [Nat.add_zero] using ScalarSearchExecution.evalOracle_shift
      (fun j x => oracle x (w.2 j)) p N 0
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hfirsteq, hfoundeq, endpoint, hshift, N, c]

lemma total_failure_bound :
    (1 / 4096 : ℝ) + 2 * (1 / 4096 + (1 / 16 + Real.exp (-128))) +
      (4 / 5 : ℝ) ^ 32 + 32 / 4096 ≤ 1 / 3 := by
  have hx : (128 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128) hx
  have he : Real.exp (-128) ≤ 1 / 128 := by simpa only [Real.exp_neg, one_div] using hi
  have hr : (4 / 5 : ℝ) ^ 32 + 32 / 4096 ≤ 1 / 16 := by norm_num
  linarith

lemma plan_accuracy_tail (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle P f oracle q.σ q.p)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (hderiv : ∀ x, HasDerivAt f (deriv f x) x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {lower : ℝ} (hlower : ∀ x, lower ≤ f x) (hgap : f q.x0 - lower ≤ q.Δ) :
    ((seedLaw q : Measure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q)))).prod (Measure.infinitePi fun _ : ℕ => P)).real {w |
      q.ε < |deriv f (ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (plan q w.1.1 (fun k => (w.1.2 k).val)) 0)|} ≤ 1 / 3 := by
  let R := Measure.infinitePi fun _ : ℕ => P
  let S := (seedLaw q : Measure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q)))).prod R
  let first := fun ξ : ℕ → q.Ω => ScalarSearchExecution.evalOracle (fun k x => oracle x (ξ k))
    (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0
  let F := {w : ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) × (ℕ → q.Ω) |
    q.ε / 16 < |first w.2 - deriv f q.x0|}
  have hm : Measurable first := measurable_estimatePlan_value (fun k (ξ : ℕ → q.Ω) (x : ℝ) => oracle x (ξ k))
    (fun k => ho.measurable.comp (measurable_snd.prodMk ((measurable_pi_apply k).comp measurable_fst)))
    q.σ q.p (q.ε / 48) 6 0 (fun _ => q.x0) measurable_const
  have hA := measurableSet_lt (measurable_const (a := q.ε / 16))
    (continuous_abs.measurable.comp (hm.sub_const (deriv f q.x0)))
  have hF : S.real F ≤ 1 / 4096 := by
    have ht := initial_estimate_tail q P ho hσ hε hp hp2
    have hpre := (measurePreserving_snd (μ := (seedLaw q : Measure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))))) (ν := R)).measure_preimage
      hA.nullMeasurableSet
    unfold Measure.real at ht ⊢
    simp only [Function.comp_def] at hpre
    rw [← hpre] at ht
    exact ht
  by_cases hsmall : |deriv f q.x0| ≤ 7 * q.ε / 16
  · apply (measureReal_mono (s₂ := F) ?_ (by finiteness)).trans (hF.trans (by norm_num))
    intro w hw
    by_contra hn
    have herr : |first w.2 - deriv f q.x0| ≤ q.ε / 16 := le_of_not_gt hn
    have hstop : |first w.2| ≤ q.ε / 2 := by
      have he := abs_le.mp herr
      have hv := abs_le.mp hsmall
      apply abs_le.mpr
      constructor <;> linarith
    simp only [Set.mem_ofPred_eq] at hw
    rw [plan_evalOracle] at hw
    dsimp only at hw
    change |ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
      (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0) 0| ≤ q.ε / 2 at hstop
    simp only [hstop, ↓reduceIte] at hw
    linarith
  · let s : ℝ := if deriv f q.x0 ≤ 0 then 1 else -1
    have hs : |s| = 1 := by dsimp [s]; split_ifs <;> norm_num
    have hlo : s * deriv f q.x0 < 0 := by
      dsimp [s]
      split_ifs with hsign
      · have hv : deriv f q.x0 < 0 := by
          by_contra hn
          have he : deriv f q.x0 = 0 := le_antisymm hsign (le_of_not_gt hn)
          simp only [he, abs_zero] at hsmall
          exact hsmall (by positivity)
        simpa using hv
      · have hv := lt_of_not_ge hsign
        simpa using neg_neg_of_pos hv
    let c := ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6
    let G := {w : ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) × (ℕ → q.Ω) |
      let found := ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k)) (discoveryPlan q s w.1.1) c
      let endpoint := match found with | some (false, x) => x | _ => distance q
      q.ε < |deriv f (if |first w.2| ≤ q.ε / 2 then q.x0 else
        if (found.getD (false, 0)).1 = true then q.x0 + s * (found.getD (false, 0)).2
        else (ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
          (attemptsPlan q s endpoint (fun k => (w.1.2 k).val) 32 0 none) (c + discoveryCalls q)).getD q.x0)|}
    have hG : S.real G ≤ 2 * (1 / 4096 + (1 / 16 + Real.exp (-128))) +
        (4 / 5 : ℝ) ^ 32 + 32 / 4096 :=
      fixed_orientation_output_tail q P ho hH hν hΔ hε hσ hp hp2 hderiv hholder hs hlower hgap hlo
    apply (measureReal_mono (s₂ := F ∪ G) ?_ (by finiteness)).trans
    · have h := (measureReal_union_le F G).trans (add_le_add hF hG)
      exact h.trans (by linarith [total_failure_bound])
    · intro w hw
      by_cases he : w ∈ F
      · exact Or.inl he
      apply Or.inr
      have herr : |first w.2 - deriv f q.x0| ≤ q.ε / 16 := le_of_not_gt he
      simp only [Set.mem_ofPred_eq] at hw
      rw [plan_fixed_orientation q hε w.1.1 (fun k => (w.1.2 k).val)
        (fun k x => oracle x (w.2 k)) (deriv f q.x0) herr] at hw
      exact hw

lemma execute_algorithm (q : LongTails.Setups.ScalarHolderStochastic.Params) (O : Oracle ℝ ℝ)
    (K : ℕ) (hK : executionCalls q ≤ K)
    (seed : (ℕ → ℝ) × (ℕ → Fin (16 * depth q))) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm q) (fun _ => K) seed ξ =
      ScalarSearchExecution.evalOracle (fun k x => O.answer k (0, x) (ξ k))
        (plan q seed.1 (fun k => (seed.2 k).val)) 0 :=
  ScalarSearchExecution.execute_plan (seedLaw q) q.x0 q.x0 (executionCalls q) K
    (fun seed => plan q seed.1 (fun k => (seed.2 k).val)) O seed ξ hK

lemma measurable_plan_output (q : LongTails.Setups.ScalarHolderStochastic.Params) {oracle : ℝ → q.Ω → ℝ}
    (ho : Measurable (Function.uncurry oracle)) :
    Measurable (fun w : ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) × (ℕ → q.Ω) =>
      ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
        (plan q w.1.1 (fun k => (w.1.2 k).val)) 0) := by
  let W := ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) × (ℕ → q.Ω)
  let G : ℕ → W → ℝ → ℝ := fun k w x => oracle x (w.2 k)
  have hG (k : ℕ) : Measurable (Function.uncurry (G k)) :=
    ho.comp (measurable_snd.prodMk ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)))
  exact measurable_plan_value q G hG (fun w => w.1.1) (by intro k; fun_prop)
    (fun w => w.1.2) (by intro k; fun_prop)

lemma execution_successful (q : LongTails.Setups.ScalarHolderStochastic.Params) (hq : LongTails.Setups.ScalarHolderStochastic.spec.valid q)
    (μ : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (μ : Measure _) (P : Measure _))
    {f : ℝ → ℝ} {oracle : ℝ → q.Ω → ℝ}
    (ho : LongTails.Setups.ScalarHolderStochastic.IsGradientOracle (μ : Measure _) f oracle q.σ q.p)
    (hderiv : ∀ x, HasDerivAt f (deriv f x) x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν)
    {lower : ℝ} (hlower : ∀ x, lower ≤ f x) (hgap : f q.x0 - lower ≤ q.Δ)
    (K : ℕ) (hK : executionCalls q ≤ K) :
    LongTails.Setups.ScalarHolderStochastic.spec.successful q f
      (fun w => (execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
        (algorithm q) (fun _ => K) w.1 w.2))
      ⟨(seedLaw q : Measure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q)))).prod (P : Measure _), inferInstance⟩ := by
  rcases hq with ⟨hH, hν, hν1, hΔ, hσ, hp, hp2, hε⟩
  have hlaw : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (μ : Measure q.Ω) := by
    have h := hIID.stream_law.map_eq
    change (P : Measure (ℕ → q.Ω)).map id = _ at h
    simpa only [Measure.map_id] using h
  change Measurable _ ∧ _
  constructor
  · simpa only [execute_algorithm q _ K hK] using measurable_plan_output q ho.measurable
  · simp only [execute_algorithm q _ K hK]
    change ((seedLaw q : Measure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q)))).prod
      (P : Measure (ℕ → q.Ω))) {w | q.ε < |deriv f
        (ScalarSearchExecution.evalOracle (fun k x => oracle x (w.2 k))
          (plan q w.1.1 (fun k => (w.1.2 k).val)) 0)|} ≤ _
    rw [hlaw]
    have h := plan_accuracy_tail q (μ : Measure _) ho hH hν hΔ hε hσ hp hp2 hderiv hholder hlower hgap
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 3)] using h

end OracleTemplate.ScalarHolderSearch
