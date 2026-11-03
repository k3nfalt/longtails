import LongTails.Proofs.StochasticCompositeGeneralizedMoments
import LongTails.Proofs.StoppedVectorConcentration
import LongTails.Proofs.TerminalClippingConcentration
import Mathlib.MeasureTheory.Integral.Pi
import LongTails.Proofs.TerminalClippingEnergy
import LongTails.Proofs.AdamHeavyTailedProcess
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.GeneralizedLipschitzSampling

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.RobustGradient

lemma squared_sum_energy_tuning {K V r : ℝ} (hK : 0 ≤ K) (hV : 0 ≤ V) (hr : 0 ≤ r)
    (hKr : K ≤ r) (hVr : 4 * V ≤ r ^ 2) (hd : 0 < V + K * r) :
    let t := 1 / (64 * (V + K * r))
    t * (2 * K * r + K ^ 2) ≤ 1 ∧
      t * V + 2 * t ^ 2 * (4 * r ^ 2 + K ^ 2) * V - t * r ^ 2 ≤
        -(r ^ 2 / (128 * (V + K * r))) := by
  dsimp only
  set t := 1 / (64 * (V + K * r)) with ht
  have ht0 : 0 ≤ t := by positivity
  have htd : t * (V + K * r) = 1 / 64 := by rw [ht]; field_simp
  have htv : t * V ≤ 1 / 64 := by nlinarith [mul_nonneg ht0 (mul_nonneg hK hr)]
  have hkk : K ^ 2 ≤ K * r := by nlinarith [mul_nonneg hK (sub_nonneg.mpr hKr)]
  have hk2 : K ^ 2 ≤ r ^ 2 := by nlinarith
  have hsmall : t * (2 * K * r + K ^ 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hkk ht0
    nlinarith [mul_nonneg ht0 hV]
  refine ⟨hsmall, ?_⟩
  have hfirst : t * V ≤ t * r ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_left hVr ht0
    nlinarith
  have hsecond : 2 * t ^ 2 * (4 * r ^ 2 + K ^ 2) * V ≤ 10 * t ^ 2 * r ^ 2 * V := by
    have := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 2 * t ^ 2 * V by positivity)
    nlinarith
  have hthird : 10 * t ^ 2 * r ^ 2 * V ≤ 10 / 64 * t * r ^ 2 := by
    have := mul_le_mul_of_nonneg_left htv (show 0 ≤ 10 * t * r ^ 2 by positivity)
    nlinarith
  have he : r ^ 2 / (128 * (V + K * r)) = t * r ^ 2 / 2 := by
    rw [ht]; field_simp; ring
  rw [he]
  nlinarith [mul_nonneg ht0 (sq_nonneg r)]

lemma clipped_batch_bernstein_tuning {m V B a R ε ell : ℝ}
    (hm : 0 < m) (hV : 0 ≤ V) (hB : 0 ≤ B) (ha : 0 < a) (hR : 0 < R)
    (hε : 0 < ε) (hell : 1 ≤ ell) (haT : a ≤ 4 * R ^ 2 / ε)
    (hbatch : 1099511627776 * (V * a * ell ^ 2 / ε + B * a * ell ^ 2 / R) ≤ m) :
    let u := R / (64 * a * Real.sqrt ell)
    128 * ell * (m * V + 3 * B * (m * u)) ≤ (m * u) ^ 2 := by
  have hl : 0 < ell := by linarith
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hl
  have hs2 := Real.sq_sqrt hl.le
  have hsle : Real.sqrt ell ≤ ell := by nlinarith [Real.sqrt_nonneg ell]
  have hden : 0 < 64 * a * Real.sqrt ell := by positivity
  have hpart1 : 1099511627776 * (V * a * ell ^ 2 / ε) ≤ m := by
    have hn : 0 ≤ B * a * ell ^ 2 / R := by positivity
    linarith
  have hpart2 : 1099511627776 * (B * a * ell ^ 2 / R) ≤ m := by
    have hn : 0 ≤ V * a * ell ^ 2 / ε := by positivity
    linarith
  have hpa : a * ε ≤ 4 * R ^ 2 := (le_div_iff₀ hε).mp haT
  have hp1 : 1099511627776 * V * a * ell ^ 2 ≤ m * ε := by
    apply (div_le_iff₀ hε).mp
    convert hpart1 using 1
    ring
  have hp2 : 1099511627776 * B * a * ell ^ 2 ≤ m * R := by
    apply (div_le_iff₀ hR).mp
    convert hpart2 using 1
    ring
  have hp3 : 1048576 * V * a ^ 2 * ell ^ 2 ≤ m * R ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hp1 ha.le
    have h2 := mul_le_mul_of_nonneg_left hpa hm.le
    nlinarith [mul_nonneg hV (mul_nonneg (sq_nonneg a) (sq_nonneg ell))]
  have hp4 : 49152 * B * a * ell * Real.sqrt ell ≤ m * R := by
    have h1 := mul_le_mul_of_nonneg_left hsle (show 0 ≤ B * a * ell by positivity)
    nlinarith [mul_nonneg hB (mul_nonneg ha.le (sq_nonneg ell))]
  dsimp only
  apply (mul_le_mul_iff_left₀ (show 0 < (64 * a * Real.sqrt ell) ^ 2 by positivity)).mp
  field_simp
  have he : 128 * ell * 64 * a * Real.sqrt ell * (V * 64 * a * Real.sqrt ell + 3 * B * R) =
      524288 * V * a ^ 2 * ell ^ 2 + 24576 * B * a * ell * Real.sqrt ell * R := by
    ring_nf
    rw [hs2]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hp4 hR.le]

lemma heavy_clip_bias_tuning {σ α B R ε ell : ℝ} (hσ : 0 < σ) (hα : 1 < α)
    (hR : 0 < R) (hε : 0 < ε) (hell : 0 < ell)
    (hB : 2 * (1048576 * σ ^ α * R * ell / ε) ^ (1 / (α - 1)) ≤ B) :
    σ ^ α / (B / 2) ^ (α - 1) ≤ ε / (1048576 * R * ell) := by
  have hσp : 0 < σ ^ α := Real.rpow_pos_of_pos hσ _
  have hT : 0 < 1048576 * σ ^ α * R * ell / ε := by positivity
  have hroot : 0 < (1048576 * σ ^ α * R * ell / ε) ^ (1 / (α - 1)) :=
    Real.rpow_pos_of_pos hT _
  have hB0 : 0 < B / 2 := by linarith
  have hp := Real.rpow_le_rpow hroot.le
    (show (1048576 * σ ^ α * R * ell / ε) ^ (1 / (α - 1)) ≤ B / 2 by linarith)
    (show 0 ≤ α - 1 by linarith)
  rw [← Real.rpow_mul hT.le, one_div_mul_cancel (by linarith : α - 1 ≠ 0), Real.rpow_one] at hp
  have hd := div_le_div_of_nonneg_left hσp.le hT hp
  apply hd.trans_eq
  field_simp

lemma heavy_bias_threshold {a R ε ell : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hε : 0 < ε) (hell : 1 ≤ ell) (haT : a ≤ 4 * R ^ 2 / ε) :
    ε / (1048576 * R * ell) ≤ R / (64 * a * Real.sqrt ell) := by
  have hl : 0 < ell := by linarith
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hl
  have hs2 := Real.sq_sqrt hl.le
  have hsle : Real.sqrt ell ≤ ell := by nlinarith [Real.sqrt_nonneg ell]
  have haε : a * ε ≤ 4 * R ^ 2 := (le_div_iff₀ hε).mp haT
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_right haε hs.le
  have h2 := mul_le_mul_of_nonneg_left hsle (show 0 ≤ 4 * R ^ 2 by positivity)
  nlinarith [mul_nonneg (sq_nonneg R) hl.le]

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

lemma guarded_centered_heavy_moments {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ : ℝ} (hB : 0 < B)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) (c : E) :
    let U := fun ω => guardedError B u c (V ω)
    let Z := fun ω => U ω - ∫ z, U z ∂P
    Measurable Z ∧ Integrable Z P ∧ Integrable (fun ω => ‖Z ω‖ ^ 2) P ∧
      (∫ ω, Z ω ∂P) = 0 ∧ (∀ ω, ‖Z ω‖ ≤ 3 * B) ∧
      (∫ ω, ‖Z ω‖ ^ 2 ∂P) ≤ (2 * B) ^ (2 - p) * σ ^ p := by
  dsimp only
  have h := guardedError_heavy_moments hV hi hmean hB hp hp2 hmi hm c
  have hU : Measurable (fun ω => guardedError B u c (V ω)) :=
    measurable_guardedError.comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk hV)))
  have hvar := TerminalClipping.centered_second_moment h.1 h.2.1
  refine ⟨hU.sub_const _, h.1.sub (integrable_const _), hvar.1, ?_, ?_,
    hvar.2.trans h.2.2.1⟩
  · rw [integral_sub h.1 (integrable_const _), integral_const]
    simp
  · intro ω
    have hμ : ‖∫ z, guardedError B u c (V z) ∂P‖ ≤ 3 * B / 2 := by
      simpa using norm_integral_le_of_norm_le_const (μ := P)
        (Filter.Eventually.of_forall (fun z => guardedError_bound hB.le u c (V z)))
    have ht := norm_sub_le (guardedError B u c (V ω)) (∫ z, guardedError B u c (V z) ∂P)
    have hb := guardedError_bound hB.le u c (V ω)
    linarith

noncomputable def stoppedSumStep (r : ℝ) (s x : E) : E :=
  if ‖s‖ ≤ r then s + x else s

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_stoppedSumStep (r : ℝ) :
    Measurable (fun z : E × E => stoppedSumStep r z.1 z.2) := by
  unfold stoppedSumStep
  exact (measurable_fst.add measurable_snd).ite
    (measurableSet_le measurable_fst.norm measurable_const) measurable_fst

omit [SecondCountableTopology E] in
lemma stoppedSumStep_exp_control {X : Ω → E} (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v r t : ℝ} (hK : 0 ≤ K) (hv0 : 0 ≤ v) (ht : 0 ≤ t) (s : E)
    (hb : ∀ ω, ‖X ω‖ ≤ K) (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (hs : t * (2 * K * r + K ^ 2) ≤ 1) :
    Integrable (fun ω => Real.exp (t * ‖stoppedSumStep r s (X ω)‖ ^ 2)) P ∧
    (∫ ω, Real.exp (t * ‖stoppedSumStep r s (X ω)‖ ^ 2) ∂P) ≤
      Real.exp (t * ‖s‖ ^ 2 + t * v + 2 * t ^ 2 * (4 * r ^ 2 + K ^ 2) * v) := by
  by_cases hsr : ‖s‖ ≤ r
  · have hsmall : t * (2 * K * ‖s‖ + K ^ 2) ≤ 1 := by
      apply le_trans ?_ hs
      gcongr
    have hm := squared_sum_increment_mgf hX hi hi2 hz ht s hb hv hsmall
    have he : (fun ω => Real.exp (t * ‖stoppedSumStep r s (X ω)‖ ^ 2)) =
        fun ω => Real.exp (t * ‖s‖ ^ 2) *
          Real.exp (t * (2 * ⟪s, X ω⟫ + ‖X ω‖ ^ 2)) := by
      funext ω
      simp only [stoppedSumStep, ite_eq_left hsr, norm_add_sq_real, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    refine ⟨hm.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hmul := mul_le_mul_of_nonneg_left hm.2 (Real.exp_nonneg (t * ‖s‖ ^ 2))
    rw [← Real.exp_add] at hmul
    apply hmul.trans
    apply Real.exp_le_exp.mpr
    have hs2 : ‖s‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsr 2
    nlinarith [mul_le_mul_of_nonneg_left hs2 (show 0 ≤ 8 * t ^ 2 * v by positivity)]
  · simp only [stoppedSumStep, ite_eq_right hsr]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ t * v := mul_nonneg ht hv0
    have h2 : 0 ≤ 2 * t ^ 2 * (4 * r ^ 2 + K ^ 2) * v := by positivity
    linarith

open LongTails.Proofs.StoppedVectorConcentration
open LongTails.Proofs.AdaptiveOracleConcentration

lemma iid_stopped_sum_exp_control {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {ξ : ℕ → Ξ → Ω}
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ Q)
    (hlaw : ∀ i, Q.map (ξ i) = P)
    {X : Ω → E} (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v r t : ℝ} (hK : 0 ≤ K) (hv0 : 0 ≤ v) (ht : 0 ≤ t)
    (hb : ∀ ω, ‖X ω‖ ≤ K) (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (hs : t * (2 * K * r + K ^ 2) ≤ 1) (n : ℕ) :
    Integrable (fun ω => Real.exp (t * ‖stoppedSum (fun i => X (ξ i ω)) r n‖ ^ 2)) Q ∧
    (∫ ω, Real.exp (t * ‖stoppedSum (fun i => X (ξ i ω)) r n‖ ^ 2) ∂Q) ≤
      Real.exp (n * (t * v + 2 * t ^ 2 * (4 * r ^ 2 + K ^ 2) * v)) := by
  let Y : (n : ℕ) → (Fin n → Ω) × Ω → E := fun _ z => X z.2
  let S := historyStoppedSum Y r
  let state : (n : ℕ) → (Fin n → Ω) → ℝ := fun n a => t * ‖S n a‖ ^ 2
  let inc : (n : ℕ) → (Fin n → Ω) × Ω → ℝ := fun n z =>
    t * (‖stoppedSumStep r (S n z.1) (X z.2)‖ ^ 2 - ‖S n z.1‖ ^ 2)
  let c := t * v + 2 * t ^ 2 * (4 * r ^ 2 + K ^ 2) * v
  have hS (n : ℕ) : Measurable (S n) :=
    history_stopped_sum_measurable (fun _ => hX.comp measurable_snd) r n
  have hstate (n : ℕ) : Measurable (state n) := ((hS n).norm.pow_const 2).const_mul t
  have hinc (n : ℕ) : Measurable (inc n) :=
    (((measurable_stoppedSumStep r).comp
      (((hS n).comp measurable_fst).prodMk (hX.comp measurable_snd))).norm.pow_const 2 |>.sub
        (((hS n).comp measurable_fst).norm.pow_const 2)).const_mul t
  have hlocal (n : ℕ) (a : Fin n → Ω) :
      Integrable (fun z => Real.exp (inc n (a, z))) P ∧
      (∫ z, Real.exp (inc n (a, z)) ∂P) ≤ Real.exp c := by
    have h := stoppedSumStep_exp_control hX hi hi2 hz hK hv0 ht (S n a) hb hv hs
    have he : (fun z => Real.exp (inc n (a, z))) = fun z =>
        Real.exp (-(t * ‖S n a‖ ^ 2)) * Real.exp (t * ‖stoppedSumStep r (S n a) (X z)‖ ^ 2) := by
      funext z
      rw [← Real.exp_add]
      dsimp [inc]
      congr 1
      ring
    rw [he]
    refine ⟨h.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left h.2 (Real.exp_nonneg (-(t * ‖S n a‖ ^ 2)))
    rw [← Real.exp_add] at hh
    convert hh using 1
    congr 1
    dsimp [c]
    ring
  have hzero (ω : Ξ) : state 0 (fun i => ξ i ω) = 0 := by
    simp [state, S, historyStoppedSum]
  have hstep (n : ℕ) (ω : Ξ) : state (n + 1) (fun i => ξ i ω) =
      state n (fun i => ξ i ω) + inc n ((fun i => ξ i ω), ξ n ω) := by
    dsimp [state, inc, S, historyStoppedSum, Y, stoppedSumStep, Fin.init]
    simp only [Fin.init_def, Fin.val_castSucc]
    ring_nf
    rfl
  have h := iid_exponential_recursion hξ hind hlaw hstate hinc hzero hstep
    (fun n a => (hlocal n a).1) (fun n a => (hlocal n a).2) n
  have he (ω : Ξ) : state n (fun i => ξ i ω) =
      t * ‖stoppedSum (fun i => X (ξ i ω)) r n‖ ^ 2 := by
    dsimp [state, S]
    rw [history_stopped_sum_eq]
  simpa only [he] using h

lemma iid_vector_bernstein_large {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {ξ : ℕ → Ξ → Ω}
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ Q)
    (hlaw : ∀ i, Q.map (ξ i) = P)
    {X : Ω → E} (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v r : ℝ} (hK : 0 ≤ K) (hv0 : 0 ≤ v) (hr : 0 ≤ r)
    (hb : ∀ ω, ‖X ω‖ ≤ K) (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (n : ℕ) (hKr : K ≤ r) (hVr : 4 * (n : ℝ) * v ≤ r ^ 2)
    (hd : 0 < (n : ℝ) * v + K * r) :
    Q.real {ω | r < ‖∑ i ∈ Finset.range n, X (ξ i ω)‖} ≤
      Real.exp (-(r ^ 2 / (128 * ((n : ℝ) * v + K * r)))) := by
  let t := 1 / (64 * ((n : ℝ) * v + K * r))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htune := squared_sum_energy_tuning hK (mul_nonneg (Nat.cast_nonneg n) hv0)
    hr hKr (by nlinarith) hd
  have h := iid_stopped_sum_exp_control hξ hind hlaw hX hi hi2 hz hK hv0 ht hb hv htune.1 n
  have htail := exponential_tail_of_bound ht h.1 h.2 (r ^ 2)
  have hsub : {ω | r < ‖∑ i ∈ Finset.range n, X (ξ i ω)‖} ⊆
      {ω | r ^ 2 ≤ ‖stoppedSum (fun i => X (ξ i ω)) r n‖ ^ 2} := by
    intro ω hω
    by_contra hn
    have hn' : ‖stoppedSum (fun i => X (ξ i ω)) r n‖ ≤ r := by
      simp only [Set.mem_ofPred_eq, not_le] at hn
      nlinarith [norm_nonneg (stoppedSum (fun i => X (ξ i ω)) r n)]
    rw [stopped_sum_eq_unstopped hn'] at hn'
    exact (not_le.mpr hω) hn'
  apply (measureReal_mono hsub).trans (htail.trans ?_)
  apply Real.exp_le_exp.mpr
  convert htune.2 using 1
  dsimp only [t]
  ring

lemma iid_vector_bernstein_level {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {ξ : ℕ → Ξ → Ω}
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ Q)
    (hlaw : ∀ i, Q.map (ξ i) = P)
    {X : Ω → E} (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v r ell : ℝ} (hK : 0 < K) (hv0 : 0 ≤ v) (hr : 0 < r) (hell : 1 ≤ ell)
    (hb : ∀ ω, ‖X ω‖ ≤ K) (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (n : ℕ) (hsize : 128 * ell * ((n : ℝ) * v + K * r) ≤ r ^ 2) :
    Q.real {ω | r < ‖∑ i ∈ Finset.range n, X (ξ i ω)‖} ≤ Real.exp (-ell) := by
  have hn : 0 ≤ (n : ℝ) * v := mul_nonneg (Nat.cast_nonneg n) hv0
  have hd : 0 < (n : ℝ) * v + K * r := by positivity
  have hdom : 128 * ((n : ℝ) * v + K * r) ≤ r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hell (show 0 ≤ 128 * ((n : ℝ) * v + K * r) by positivity)
    nlinarith
  have hKr : K ≤ r := by
    by_contra hh
    have hmul := mul_pos hr (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith [mul_pos hK hr]
  have hVr : 4 * (n : ℝ) * v ≤ r ^ 2 := by nlinarith [mul_pos hK hr]
  have h := iid_vector_bernstein_large hξ hind hlaw hX hi hi2 hz hK.le hv0 hr.le hb hv n hKr hVr hd
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hfrac : ell ≤ r ^ 2 / (128 * ((n : ℝ) * v + K * r)) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  linarith

open OracleTemplate.StochasticGeneralized

lemma finite_vector_mean_bernstein {X : Ω → E} (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v u ell : ℝ} (hK : 0 < K) (hv0 : 0 ≤ v) (hu : 0 < u) (hell : 1 ≤ ell)
    (hb : ∀ ω, ‖X ω‖ ≤ K) (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (n : ℕ) (hn : 0 < n)
    (hsize : 128 * ell * ((n : ℝ) * v + K * ((n : ℝ) * u)) ≤ ((n : ℝ) * u) ^ 2) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | u < ‖(1 / (n : ℝ)) • ∑ i, X (ξ i)‖} ≤ Real.exp (-ell) := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hIID := infinitePi_iid P
  have h := iid_vector_bernstein_level hIID.measurable hIID.independent hIID.marginal
    hX hi hi2 hz hK hv0 (mul_pos hnr hu) hell hb hv n hsize
  have hmeas : Measurable (fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, X (ξ i)) := by
    fun_prop
  have hset : MeasurableSet {ξ : Fin n → Ω | u < ‖(1 / (n : ℝ)) • ∑ i, X (ξ i)‖} :=
    measurableSet_lt measurable_const hmeas.norm
  rw [← (prefix_preserving P n).measureReal_preimage hset.nullMeasurableSet]
  convert h using 1
  congr 1
  ext ξ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hnr)]
  rw [Fin.sum_univ_eq_sum_range (fun i => X (ξ i)) n, one_div_mul_eq_div, lt_div_iff₀ hnr]
  constructor <;> intro hh <;> nlinarith

lemma finite_guarded_heavy_mean_tail {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ a R ε ell : ℝ} (hB : 0 < B)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hmoment : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) (c : E)
    (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε) (hell : 1 ≤ ell)
    (haT : a ≤ 4 * R ^ 2 / ε) (m : ℕ) (hm : 0 < m)
    (hbatch : 1099511627776 * ((2 * B) ^ (2 - p) * σ ^ p * a * ell ^ 2 / ε +
      B * a * ell ^ 2 / R) ≤ (m : ℝ))
    (hbias : σ ^ p / (B / 2) ^ (p - 1) ≤ R / (64 * a * Real.sqrt ell)) :
    (Measure.pi fun _ : Fin m => P).real
      {ξ | R / (32 * a * Real.sqrt ell) <
        ‖(1 / (m : ℝ)) • ∑ i, guardedError B u c (V (ξ i))‖} ≤ Real.exp (-ell) := by
  let U := fun ω => guardedError B u c (V ω)
  let μ := ∫ ω, U ω ∂P
  let Z := fun ω => U ω - μ
  let v := (2 * B) ^ (2 - p) * σ ^ p
  let r := R / (64 * a * Real.sqrt ell)
  have hl : 0 < ell := by linarith
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hl
  have hr : 0 < r := by dsimp [r]; positivity
  have hσp : 0 ≤ σ ^ p := (integral_nonneg
    (fun ω => Real.rpow_nonneg (norm_nonneg (V ω - u)) p)).trans hmoment
  have hv : 0 ≤ v := mul_nonneg (Real.rpow_nonneg (by positivity) _) hσp
  have hZ := guarded_centered_heavy_moments hV hi hmean hB hp hp2 hmi hmoment c
  have htune := clipped_batch_bernstein_tuning (by exact_mod_cast hm) hv hB.le ha hR hε
    hell haT hbatch
  have ht := finite_vector_mean_bernstein hZ.1 hZ.2.1 hZ.2.2.1 hZ.2.2.2.1
    (by positivity : 0 < 3 * B) hv hr hell hZ.2.2.2.2.1 hZ.2.2.2.2.2 m hm htune
  have hb : ‖μ‖ ≤ r := (guardedError_heavy_moments hV hi hmean hB hp hp2 hmi hmoment c).2.2.2.trans hbias
  apply (measureReal_mono ?_).trans ht
  intro ξ hξ
  change r < ‖(1 / (m : ℝ)) • ∑ i, Z (ξ i)‖
  have he := finite_mean_centered (X := U) μ m hm ξ
  change (1 / (m : ℝ)) • ∑ i, U (ξ i) - μ = (1 / (m : ℝ)) • ∑ i, Z (ξ i) at he
  rw [← he]
  have htri : ‖(1 / (m : ℝ)) • ∑ i, U (ξ i)‖ ≤
      ‖(1 / (m : ℝ)) • ∑ i, U (ξ i) - μ‖ + ‖μ‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le ((1 / (m : ℝ)) • ∑ i, U (ξ i) - μ) μ
  have hscale : R / (32 * a * Real.sqrt ell) = 2 * r := by dsimp [r]; field_simp; ring
  change R / (32 * a * Real.sqrt ell) < ‖(1 / (m : ℝ)) • ∑ i, U (ξ i)‖ at hξ
  rw [hscale] at hξ
  linarith

lemma finite_centered_clip_heavy_tail {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ a R ε ell : ℝ} (hB : 0 < B)
    (hσ : 0 < σ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hmoment : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) (c : E) (hc : ‖u - c‖ ≤ B / 2)
    (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε) (hell : 1 ≤ ell)
    (haT : a ≤ 4 * R ^ 2 / ε) (m : ℕ) (hm : 0 < m)
    (hclip : 2 * (1048576 * σ ^ p * R * ell / ε) ^ (1 / (p - 1)) ≤ B)
    (hbatch : 1099511627776 * ((2 * B) ^ (2 - p) * σ ^ p * a * ell ^ 2 / ε +
      B * a * ell ^ 2 / R) ≤ (m : ℝ)) :
    (Measure.pi fun _ : Fin m => P).real
      {ξ | R / (32 * a * Real.sqrt ell) <
        ‖(1 / (m : ℝ)) • ∑ i, centeredClip B c (V (ξ i)) - u‖} ≤ Real.exp (-ell) := by
  have hbias := (heavy_clip_bias_tuning hσ hp hR hε (by linarith) hclip).trans
    (heavy_bias_threshold ha hR hε hell haT)
  have h := finite_guarded_heavy_mean_tail hV hi hmean hB hp.le hp2 hmi hmoment c
    ha hR hε hell haT m hm hbatch hbias
  simp_rw [finite_mean_centered u m hm]
  simpa only [guardedError_eq hc] using h

lemma finite_guarded_heavy_mean_moments {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ : ℝ} (hB : 0 < B)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) (c : E) (n : ℕ) (hn : 0 < n) :
    let avg := fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, guardedError B u c (V (ξ i))
    let Q := Measure.pi fun _ : Fin n => P
    Integrable avg Q ∧ Integrable (fun ξ => ‖avg ξ‖ ^ 2) Q ∧
      ‖∫ ξ, avg ξ ∂Q‖ ≤ σ ^ p / (B / 2) ^ (p - 1) ∧
      (∫ ξ, ‖avg ξ‖ ^ 2 ∂Q) ≤ 2 * (σ ^ p / (B / 2) ^ (p - 1)) ^ 2 +
        2 * ((2 * B) ^ (2 - p) * σ ^ p) / n := by
  have hU : Measurable (fun ω => guardedError B u c (V ω)) :=
    measurable_guardedError.comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk hV)))
  have h := guardedError_heavy_moments hV hi hmean hB hp hp2 hmi hm c
  have hb := LongTails.Proofs.GeneralizedLipschitzSampling.fresh_mean_moments hU h.1 h.2.1 n hn
  dsimp only
  refine ⟨hb.1, hb.2.2.1, ?_, hb.2.2.2.trans ?_⟩
  · rw [hb.2.1]
    exact h.2.2.2
  · have hμ := pow_le_pow_left₀ (norm_nonneg _) h.2.2.2 2
    have hv := div_le_div_of_nonneg_right h.2.2.1 (Nat.cast_nonneg n)
    simp only [mul_div_assoc] at hv ⊢
    linarith

open OracleTemplate.StochasticGeneralized
open LongTails.Proofs.StoppedVectorConcentration

lemma adaptive_nonnegative_energy_tail {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {energy : (n : ℕ) → S → (Fin n → Ω) → ℝ} {mean : S → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (he : ∀ n, Measurable (Function.uncurry (energy n))) (hm : Measurable mean)
    {b θ C t : ℝ} (hθ : 0 ≤ θ) (hsmall : θ * b ≤ 1)
    (he0 : ∀ s z, 0 ≤ energy (cost s) s z)
    (heb : ∀ s z, energy (cost s) s z ≤ b)
    (hmean : ∀ s, (∫ z, energy (cost s) s z ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ mean s)
    (k : ℕ) (s : S)
    (hcap : ∀ ξ, accumulated cost next (fun _ s _ => mean s) k s ξ ≤ C) :
    (Measure.infinitePi (fun _ : ℕ => p)).real
      {ξ | t ≤ accumulated cost next energy k s ξ} ≤ Real.exp (2 * θ * C - θ * t) := by
  let inc := fun n s z => θ * energy n s z + (-2 * θ) * mean s
  have hinc (n : ℕ) : Measurable (Function.uncurry (inc n)) :=
    ((he n).const_mul θ).add ((hm.comp measurable_fst).const_mul (-2 * θ))
  have hstep (s : S) : Integrable (fun z => Real.exp (inc (cost s) s z))
      (Measure.pi fun _ : Fin (cost s) => p) ∧
      (∫ z, Real.exp (inc (cost s) s z) ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ 1 := by
    have h := bounded_nonnegative_mgf (P := Measure.pi fun _ : Fin (cost s) => p) ((he (cost s)).comp measurable_prodMk_left)
      (he0 s) (heb s) hθ hsmall
    have hi : Integrable (fun z => Real.exp (inc (cost s) s z))
        (Measure.pi fun _ : Fin (cost s) => p) := by
      simpa only [inc, Real.exp_add, Function.comp_def, Function.uncurry_apply_pair] using h.1.mul_const (Real.exp ((-2 * θ) * mean s))
    refine ⟨hi, ?_⟩
    simp only [inc, Real.exp_add, integral_mul_const]
    calc
      _ ≤ Real.exp (2 * θ * mean s) * Real.exp ((-2 * θ) * mean s) :=
        mul_le_mul_of_nonneg_right (h.2.trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hmean s) (by positivity)))) (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        congr 1
        ring
  have h := accumulated_exp_control p hc hn hinc (fun s => (hstep s).1)
    (fun s => (hstep s).2) k s
  have ht := exponential_tail_of_bound (θ := 1) (V := 0) (by norm_num)
    (by simpa using h.1) (by simpa using h.2) (θ * t - 2 * θ * C)
  apply (measureReal_mono (μ := Measure.infinitePi fun _ : ℕ => p) ?_).trans
    (ht.trans_eq ?_)
  · intro ξ hξ
    change θ * t - 2 * θ * C ≤ accumulated cost next inc k s ξ
    rw [show inc = fun n s z => θ * energy n s z + (-2 * θ) *
      (fun _ s _ => mean s) n s z from rfl, accumulated_linear]
    have ha := mul_le_mul_of_nonneg_left hξ hθ
    have hb := mul_le_mul_of_nonneg_left (hcap ξ) (show 0 ≤ 2 * θ by positivity)
    linarith
  · congr 1
    ring


lemma adaptive_compensated_tail {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ} {compensator : S → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n))) (hv : Measurable compensator)
    {θ C t : ℝ} (hθ : 0 ≤ θ)
    (hstep : ∀ s, Integrable (fun z => Real.exp (θ * increment (cost s) s z))
      (Measure.pi fun _ : Fin (cost s) => p) ∧
      (∫ z, Real.exp (θ * increment (cost s) s z)
        ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ Real.exp (compensator s))
    (k : ℕ) (s : S)
    (hcap : ∀ ξ, accumulated cost next (fun _ s _ => compensator s) k s ξ ≤ C) :
    (Measure.infinitePi (fun _ : ℕ => p)).real
      {ξ | t ≤ accumulated cost next increment k s ξ} ≤ Real.exp (C - θ * t) := by
  let inc := fun n s z => θ * increment n s z + (-1) * compensator s
  have hm (n : ℕ) : Measurable (Function.uncurry (inc n)) :=
    ((hi n).const_mul θ).add ((hv.comp measurable_fst).const_mul (-1))
  have hs (s : S) : Integrable (fun z => Real.exp (inc (cost s) s z))
      (Measure.pi fun _ : Fin (cost s) => p) ∧
      (∫ z, Real.exp (inc (cost s) s z) ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ 1 := by
    simpa only [inc, neg_one_mul, ← sub_eq_add_neg] using
      TerminalClipping.compensated_mgf (hstep s).1 (hstep s).2
  have h := accumulated_exp_control p hc hn hm (fun s => (hs s).1) (fun s => (hs s).2) k s
  have ht := exponential_tail_of_bound (θ := 1) (V := 0) (by norm_num)
    (by simpa using h.1) (by simpa using h.2) (θ * t - C)
  apply (measureReal_mono (μ := Measure.infinitePi fun _ : ℕ => p) ?_).trans
    (ht.trans_eq ?_)
  · intro ξ hξ
    change θ * t - C ≤ accumulated cost next inc k s ξ
    rw [show inc = fun n s z => θ * increment n s z + (-1) *
      (fun _ s _ => compensator s) n s z from rfl, accumulated_linear]
    have ha := mul_le_mul_of_nonneg_left hξ hθ
    have hb := hcap ξ
    linarith
  · congr 1
    ring


lemma finite_centered_inner_mgf {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E}
    (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v θ a : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (d : E)
    (hb : ∀ ω, ‖X ω‖ ≤ K) (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    {n : ℕ} (hn : 0 < n) (hsmall : 2 * (θ * a / n) * K * ‖d‖ ≤ 1) :
    Integrable (fun ξ : Fin n → Ω => Real.exp
      (θ * a * ⟪d, (1 / (n : ℝ)) • ∑ i, X (ξ i)⟫)) (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin n → Ω, Real.exp
      (θ * a * ⟪d, (1 / (n : ℝ)) • ∑ i, X (ξ i)⟫) ∂Measure.pi (fun _ => P)) ≤
      Real.exp (θ ^ 2 * a ^ 2 * ‖d‖ ^ 2 * v / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := TerminalClipping.centered_inner_mgf hX hi hi2
    (by positivity : 0 ≤ θ * a / n) (-d) hb hv (by simpa using hsmall)
  simp only [hz, sub_zero, inner_neg_right, neg_mul_neg, norm_neg] at h
  have he (ξ : Fin n → Ω) :
      Real.exp (θ * a * ⟪d, (1 / (n : ℝ)) • ∑ i, X (ξ i)⟫) =
        ∏ i, Real.exp ((θ * a / n) * ⟪X (ξ i), d⟫) := by
    rw [← Real.exp_sum]
    congr 1
    rw [inner_smul_right, inner_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm d]
    ring
  simp_rw [he]
  refine ⟨Integrable.fintype_prod (fun _ => h.1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun ω => Real.exp ((θ * a / n) * ⟪X ω, d⟫))]
  calc
    _ ≤ ∏ _ : Fin n, Real.exp ((θ * a / n) ^ 2 * ‖d‖ ^ 2 * v) :=
      Finset.prod_le_prod₀ (fun _ _ => integral_nonneg (fun _ => Real.exp_nonneg _))
        (fun _ _ => h.2)
    _ = Real.exp (θ ^ 2 * a ^ 2 * ‖d‖ ^ 2 * v / n) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      congr 1
      field_simp


open LongTails.Proofs.AdamHeavyTailedProcess

lemma adaptive_failure_count_bound {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {failure : (n : ℕ) → S → (Fin n → Ω) → ℝ} {allowance : S → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hf : ∀ n, Measurable (Function.uncurry (failure n))) (ha : Measurable allowance)
    (hf0 : ∀ n s b, 0 ≤ failure n s b) (hf1 : ∀ n s b, failure n s b ≤ 1)
    (ha0 : ∀ s, 0 ≤ allowance s) (ha1 : ∀ s, allowance s ≤ 1)
    (hmean : ∀ s, (∫ b, failure (cost s) s b ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ allowance s)
    (k : ℕ) (s : S) {C : ℝ}
    (hcap : ∀ ξ, accumulated cost next (fun _ s _ => allowance s) k s ξ ≤ C) :
    (Measure.infinitePi (fun _ : ℕ => p)).real
      {ξ | 1 ≤ accumulated cost next failure k s ξ} ≤ C := by
  let inc := fun n s b => failure n s b - allowance s
  have hi (n : ℕ) : Measurable (Function.uncurry (inc n)) :=
    (hf n).sub (ha.comp measurable_fst)
  have hb (n : ℕ) (s : S) (b : Fin n → Ω) : |inc n s b| ≤ 2 := by
    dsimp only [inc]
    rw [abs_le]
    constructor <;> linarith [hf0 n s b, hf1 n s b, ha0 s, ha1 s]
  have hfb (n : ℕ) (s : S) (b : Fin n → Ω) : |failure n s b| ≤ 1 := by
    rw [abs_of_nonneg (hf0 n s b)]
    exact hf1 n s b
  have hmu (s : S) : (∫ b, inc (cost s) s b
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ 0 := by
    have hfi : Integrable (failure (cost s) s) (Measure.pi fun _ : Fin (cost s) => p) :=
      Integrable.of_bound ((hf (cost s)).comp measurable_prodMk_left).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun b => by simpa only [Real.norm_eq_abs] using hfb _ s b))
    dsimp only [inc]
    rw [integral_sub hfi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    linarith [hmean s]
  have hcomp := accumulated_expectation_bound p hc hn hi hb hmu k s
  have hcompI := accumulated_integrable p hc hn hi hb k s
  have hfI := accumulated_integrable p hc hn hf hfb k s
  have hp (ξ : ℕ → Ω) : accumulated cost next failure k s ξ ≤
      accumulated cost next inc k s ξ + C := by
    have he : inc = fun n s b => 1 * failure n s b + (-1) *
        (fun _ s _ => allowance s) n s b := by funext n s b; dsimp only [inc]; ring
    rw [he, accumulated_linear]
    linarith [hcap ξ]
  have hE : (∫ ξ, accumulated cost next failure k s ξ
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ C := by
    have hh := integral_mono hfI (hcompI.add (integrable_const C)) hp
    simp only [Pi.add_apply] at hh
    rw [integral_add hcompI (integrable_const C)] at hh
    simp only [integral_const, probReal_univ, one_smul] at hh
    simp only [mul_zero] at hcomp
    linarith
  have hnonneg (ξ : ℕ → Ω) : 0 ≤ accumulated cost next failure k s ξ := by
    rw [accumulated_eq_sum]
    exact Finset.sum_nonneg (fun j _ => hf0 _ _ _)
  have ht := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hnonneg) hfI 1
  apply le_trans ?_ hE
  simpa only [one_mul] using ht



lemma weighted_energy_mean_tuning {a R ε ell b v m : ℝ}
    (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε) (hell : 0 < ell)
    (hb0 : 0 ≤ b) (hm : 0 < m)
    (haT : a ≤ 4 * R ^ 2 / ε)
    (hb : b ≤ ε / (1048576 * R * ell))
    (hbatch : 1099511627776 * v * a * ell ^ 2 / ε ≤ m) :
    a ^ 2 * (2 * b ^ 2 + 2 * v / m) ≤
      10 * ε * a / (1099511627776 * ell ^ 2) := by
  have hb2 := pow_le_pow_left₀ hb0 hb 2
  have hA : a * ε ≤ 4 * R ^ 2 := (le_div_iff₀ hε).mp haT
  have hV : v / m ≤ ε / (1099511627776 * a * ell ^ 2) := by
    apply (div_le_div_iff₀ hm (by positivity)).mpr
    have hh := (div_le_iff₀ hε).mp hbatch
    nlinarith
  have hB : a ^ 2 * (2 * b ^ 2) ≤ 8 * ε * a / (1099511627776 * ell ^ 2) := by
    calc
      _ = 2 * a ^ 2 * b ^ 2 := by ring
      _ ≤ 2 * a ^ 2 * (ε / (1048576 * R * ell)) ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ ≤ _ := by
        field_simp
        nlinarith [mul_le_mul_of_nonneg_left hA (show 0 ≤ a * ε by positivity)]
  have hN : a ^ 2 * (2 * v / m) ≤ 2 * ε * a / (1099511627776 * ell ^ 2) := by
    calc
      _ = 2 * a ^ 2 * (v / m) := by ring
      _ ≤ 2 * a ^ 2 * (ε / (1099511627776 * a * ell ^ 2)) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      _ = _ := by field_simp
  calc
    _ = a ^ 2 * (2 * b ^ 2) + a ^ 2 * (2 * v / m) := by ring
    _ ≤ 8 * ε * a / (1099511627776 * ell ^ 2) +
        2 * ε * a / (1099511627776 * ell ^ 2) := add_le_add hB hN
    _ = _ := by ring


lemma finite_clipped_energy_mean {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ a R ε ell : ℝ} (hB : 0 < B)
    (hσ : 0 < σ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hmoment : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) (c : E) (hc : ‖u - c‖ ≤ B / 2)
    (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε) (hell : 0 < ell)
    (haT : a ≤ 4 * R ^ 2 / ε) (m : ℕ) (hm : 0 < m)
    (hclip : 2 * (1048576 * σ ^ p * R * ell / ε) ^ (1 / (p - 1)) ≤ B)
    (hbatch : 1099511627776 * (2 * B) ^ (2 - p) * σ ^ p * a * ell ^ 2 / ε ≤ (m : ℝ)) :
    let err := fun ξ : Fin m → Ω => (1 / (m : ℝ)) • ∑ i, centeredClip B c (V (ξ i)) - u
    Integrable (fun ξ => a ^ 2 * ‖err ξ‖ ^ 2) (Measure.pi fun _ => P) ∧
      (∫ ξ, a ^ 2 * ‖err ξ‖ ^ 2 ∂Measure.pi (fun _ => P)) ≤
        10 * ε * a / (1099511627776 * ell ^ 2) := by
  have hh := finite_guarded_heavy_mean_moments hV hi hmean hB hp.le hp2 hmi hmoment c m hm
  dsimp only at hh ⊢
  simp only [guardedError_eq hc] at hh
  simp_rw [finite_mean_centered u m hm]
  refine ⟨hh.2.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left hh.2.2.2 (sq_nonneg a)).trans
  apply weighted_energy_mean_tuning ha hR hε hell (by positivity)
    (by exact_mod_cast hm) haT (heavy_clip_bias_tuning hσ hp hR hε hell hclip)
  simpa only [mul_assoc] using hbatch



lemma signed_batch_smallness {a R ell ell0 B m D : ℝ}
    (ha : 0 ≤ a) (hR : 0 < R) (hell0 : 1 ≤ ell0) (hell : ell0 ≤ ell)
    (hB : 0 ≤ B) (hm : 0 < m) (hD : D ≤ 4 * R)
    (hbatch : 1099511627776 * B * a * ell ^ 2 / R ≤ m) :
    2 * ((64 * ell0 / R ^ 2) * a / m) * (3 * B) * D ≤ 1 := by
  have hl : 0 ≤ ell0 := by linarith
  have hl2 : ell0 ≤ ell ^ 2 := by nlinarith
  have hc : 1536 * ell0 ≤ 1099511627776 * ell ^ 2 := by nlinarith [sq_nonneg ell]
  have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg hB ha)
  have hb := (div_le_iff₀ hR).mp hbatch
  have hh : 1536 * ell0 * a * B ≤ R * m := by nlinarith
  calc
    _ ≤ 2 * ((64 * ell0 / R ^ 2) * a / m) * (3 * B) * (4 * R) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (1536 * ell0 * a * B) / (R * m) := by field_simp; ring
    _ ≤ 1 := (div_le_one (by positivity)).mpr hh


lemma signed_batch_compensation {a R ε ell ell0 v m D θ : ℝ}
    (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε) (hell0 : 0 < ell0) (hell : ell0 ≤ ell)
    (hv : 0 ≤ v) (hm : 0 < m) (hD0 : 0 ≤ D) (hD : D ≤ 4 * R)
    (hbatch : 1099511627776 * v * a * ell ^ 2 / ε ≤ m) :
    θ ^ 2 * a ^ 2 * D ^ 2 * v / m ≤
      16 * θ ^ 2 * R ^ 2 * ε * a / (1099511627776 * ell0 ^ 2) := by
  have hl : 0 < ell := hell0.trans_le hell
  have hV : v / m ≤ ε / (1099511627776 * a * ell ^ 2) := by
    apply (div_le_div_iff₀ hm (by positivity)).mpr
    have hh := (div_le_iff₀ hε).mp hbatch
    nlinarith
  have hD2 : D ^ 2 ≤ 16 * R ^ 2 := by nlinarith
  calc
    _ = θ ^ 2 * a ^ 2 * D ^ 2 * (v / m) := by ring
    _ ≤ θ ^ 2 * a ^ 2 * (16 * R ^ 2) * (ε / (1099511627776 * a * ell ^ 2)) := by
      gcongr
    _ = 16 * θ ^ 2 * R ^ 2 * ε * a / (1099511627776 * ell ^ 2) := by field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr


end OracleTemplate.RobustGradient
