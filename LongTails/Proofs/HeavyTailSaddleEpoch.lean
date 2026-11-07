import LongTails.Proofs.HeavyTailSaddleRecovery
import LongTails.Proofs.HeavyTailSaddleRefresh
import LongTails.Proofs.ComponentEnvelopeGeometry
import LongTails.Proofs.HeavyTailSaddleExecution
import LongTails.Proofs.HeavyTailSaddleEnergy
open MeasureTheory
open LongTails.Algorithms.HeavyTailSaddleEstimator
open LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution
namespace LongTails.Proofs.HeavyTailSaddleEpoch
open HeavyTailedProductProcess HeavyTailSaddleEnergy

def prefixRun {S Z : Type*} (step : S → Z → S) (start : S) : (n : ℕ) → (Fin n → Z) → S
  | 0, _ => start
  | n + 1, v => step (prefixRun step start n (fun i => v i.castSucc)) (v (Fin.last n))

lemma prefixRun_measurable {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]
    {step : S → Z → S} (hs : Measurable (Function.uncurry step)) (start : S) (n : ℕ) :
    Measurable (prefixRun step start n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact hs.comp ((ih.comp (by fun_prop)).prodMk (measurable_pi_apply (Fin.last n)))

lemma prefixRun_trajectory {S Z : Type*} (step : S → Z → S) (start : S) (n : ℕ) (ξ : ℕ → Z) :
    prefixRun step start n (fun i => ξ i) = trajectory step n start ξ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [prefixRun, trajectory_succ_last, Fin.val_castSucc, Fin.val_last] using congrArg (fun s => step s (ξ n)) ih

lemma trajectory_epoch_probability {S Z Ω : Type*} [MeasurableSpace S] [MeasurableSpace Z]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Z) [IsProbabilityMeasure Q] {ξ : ℕ → Ω → Z}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {step : S → Z → S} (hs : Measurable (Function.uncurry step))
    {energy : S → ℝ} (he : Measurable energy) {inc : S → Z → ℝ}
    (hi : Measurable (Function.uncurry inc)) (start : S)
    {a B ell V A : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 < B)
    (hell : 0 < ell) (hV : 0 ≤ V) (hA : 0 < A)
    (hvariance : 512 * ell * V ≤ a * A * B) (hstart : energy start ≤ B)
    (hstep : ∀ s z, energy (step s z) ≤ (1 - a) * energy s + inc s z)
    (hmgf : ∀ s, energy s ≤ 4 * B → ∀ t : ℝ, 0 ≤ t → t ≤ ell / (300 * B) →
      Integrable (fun z => Real.exp (t * inc s z)) Q ∧
      (∫ z, Real.exp (t * inc s z) ∂Q) ≤
        Real.exp (t * a * B / 128 + t ^ 2 * (17 * B * V / A)))
    (N : ℕ) (hdecay : (1 - a) ^ N ≤ 1 / 16) :
    P {ω | (∃ n ≤ N, 4 * B < energy (trajectory step n start (fun k => ξ k ω))) ∨
      25 * B / 128 < energy (trajectory step N start (fun k => ξ k ω))} ≤
      (N + 1 : ℕ) * ENNReal.ofReal (Real.exp (-ell / 2500)) := by
  classical
  let good := fun (j : ℕ) (v : Fin j → Z) => ∀ i : Fin (j + 1),
    energy (prefixRun step start i.val (fun k => v (k.castLE (Nat.le_of_lt_succ i.isLt)))) ≤ 4 * B
  let increment := fun (j : ℕ) (w : (Fin j → Z) × Z) => inc (prefixRun step start j w.1) w.2
  let en := fun ω n => energy (trajectory step n start (fun k => ξ k ω))
  let total : Ω → ℕ → ℝ := fun ω => Nat.rec (0 : ℝ) (fun n prev => (1 - a) * prev +
    if good n (fun i => ξ i ω) then increment n ((fun i => ξ i ω), ξ n ω) else 0)
  have hg (j : ℕ) : MeasurableSet {v | good j v} := by
    change MeasurableSet {v : Fin j → Z | ∀ i : Fin (j + 1),
      energy (prefixRun step start i.val (fun k => v (k.castLE (Nat.le_of_lt_succ i.isLt)))) ≤ 4 * B}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (he.comp ((prefixRun_measurable hs start i.val).comp (by fun_prop))) measurable_const
  have him (j : ℕ) : Measurable (increment j) :=
    hi.comp (((prefixRun_measurable hs start j).comp measurable_fst).prodMk measurable_snd)
  have hgood (j : ℕ) (ω : Ω) : good j (fun i => ξ i ω) ↔ ∀ k ≤ j, en ω k ≤ 4 * B := by
    dsimp only [good, en]
    constructor
    · intro h k hk
      have hh := h ⟨k, by omega⟩
      simpa only [Fin.val_castLE, prefixRun_trajectory step start k (fun k => ξ k ω)] using hh
    · intro h i
      simpa only [Fin.val_castLE, prefixRun_trajectory step start i.val (fun k => ξ k ω)] using h i.val (Nat.le_of_lt_succ i.isLt)
  have hinc (j : ℕ) (ω : Ω) : increment j ((fun i => ξ i ω), ξ j ω) =
      inc (trajectory step j start (fun k => ξ k ω)) (ξ j ω) := by
    dsimp only [increment]
    rw [prefixRun_trajectory step start j (fun k => ξ k ω)]
  apply killed_energy_epoch_probability P (ρ := 1 - a) hB (by linarith) (by linarith)
    (energy := en) (total := total)
    (increment := fun ω j => inc (trajectory step j start (fun k => ξ k ω)) (ξ j ω))
    (fun _ => hstart) (fun _ => rfl)
  · intro ω n hn
    dsimp only [en]
    rw [trajectory_succ_last]
    exact hstep _ _
  · intro ω n hn
    dsimp only [total, Nat.rec]
    simp only [hinc, hgood]
  · intro n hn
    have ht := stopped_weighted_tail hIID hg him ha ha1 hB hell hV hA hvariance
      (fun j v hv t ht htop => hmgf _ (by
        have hh := hv (Fin.last j)
        simpa only [Fin.val_last, Fin.castLE_refl] using hh) t ht htop) n
    have heq (ω : Ω) : total ω n = ∑ j ∈ Finset.range n,
        (1 - a) ^ (n - 1 - j) *
          (if good j (fun i => ξ i ω) then increment j ((fun i => ξ i ω), ξ j ω) else 0) :=
      discounted_recursion_sum rfl (fun _ => rfl) n
    simpa only [heq] using ht
  · exact hdecay
open scoped RealInnerProductSpace
open OracleTemplate.TemporalDiscrepancy
lemma accelerated_epoch_probability {E Z Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Z) [IsProbabilityMeasure Q]
    {ξ : ℕ → Ω → Z}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    {f : E → ℝ} {g : E → E} {K : E → Z → E}
    (hf : Measurable f) (hg : Measurable g) (hK : Measurable (Function.uncurry K))
    {m H B ell : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hell : 2304 ≤ ell)
    (u : E) (hmin : ∀ v, f u ≤ f v)
    (hsc : ∀ x y, f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsm : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ + H / 2 * ‖y - x‖ ^ 2)
    (state : E × E) (hstart : f state.1 - f u + m / 2 * ‖state.2 - u‖ ^ 2 ≤ B)
    (hkernel : ∀ s : E × E, f s.1 - f u + m / 2 * ‖s.2 - u‖ ^ 2 ≤ 4 * B →
      let a := Real.sqrt m / (Real.sqrt H * ell)
      let error := fun z => K (acceleratedQuery a s) z - g (acceleratedQuery a s)
      Integrable error Q ∧ Integrable (fun z => ‖error z‖ ^ 2) Q ∧
        (∀ z, ‖error z‖ ≤ 48 * Real.sqrt (H * B)) ∧
        ‖∫ z, error z ∂Q‖ ≤ Real.sqrt (m * B) / 1024 ∧
        (∫ z, ‖error z‖ ^ 2 ∂Q) ≤ Real.sqrt (m * B) * Real.sqrt (H * B) / 512)
    (N : ℕ) (hdecay : (1 - Real.sqrt m / (Real.sqrt H * ell)) ^ N ≤ 1 / 16) :
    let a := Real.sqrt m / (Real.sqrt H * ell)
    let step := fun s z => acceleratedUpdate a m s (K (acceleratedQuery a s) z)
    let en := fun s : E × E => f s.1 - f u + m / 2 * ‖s.2 - u‖ ^ 2
    P {ω | (∃ n ≤ N, 4 * B < en (trajectory step n state (fun k => ξ k ω))) ∨
      25 * B / 128 < en (trajectory step N state (fun k => ξ k ω))} ≤
      (N + 1 : ℕ) * ENNReal.ofReal (Real.exp (-ell / 2500)) := by
  intro a step en
  let A := H * ell ^ 2
  let V := Real.sqrt (m * B) * Real.sqrt (H * B) / 512
  let err := fun (s : E × E) z => K (acceleratedQuery a s) z - g (acceleratedQuery a s)
  let z0 := fun s : E × E => (acceleratedUpdate a m s (g (acceleratedQuery a s))).2 - u
  let inc := fun s z => -a * ⟪z0 s, err s z⟫ + a ^ 2 / m * ‖err s z‖ ^ 2
  have hc := kernel_epoch_calibration hm hmH hB hell
  change 0 < a ∧ a ≤ 1 ∧ 0 < A ∧ a ^ 2 * A = m ∧ _ at hc
  have hH : 0 < H := lt_of_lt_of_le hm hmH
  have hHA : H ≤ A := le_mul_of_one_le_right hH.le (by nlinarith : 1 ≤ ell ^ 2)
  have hsmA (x y : E) : f y ≤ f x + ⟪g x, y - x⟫ + A / 2 * ‖y - x‖ ^ 2 := by
    have hh := hsm x y
    have hn := mul_nonneg (sub_nonneg.mpr hHA) (sq_nonneg ‖y - x‖)
    nlinarith only [hh, hn]
  have hstepA : A * a ^ 2 ≤ m := by rw [mul_comm]; exact hc.2.2.2.1.le
  have hnoise (s : E × E) (z : Z) := accelerated_noisy_step hm hc.1.le hc.2.1 hstepA
    s.1 s.2 u (g (acceleratedQuery a s)) (err s z) hmin
    (hsc (acceleratedQuery a s)) (hsmA (acceleratedQuery a s))
  have hstep : ∀ s z, en (step s z) ≤ (1 - a) * en s + inc s z := by
    intro s z
    have hh := (hnoise s z).1
    have heq : g (acceleratedQuery a s) + err s z = K (acceleratedQuery a s) z := by
      dsimp [err]
      abel
    rw [heq, Prod.mk.eta] at hh
    simpa only [en, step, inc, z0, sub_eq_add_neg, neg_mul, add_assoc] using hh
  have hme : Measurable en := by dsimp [en]; fun_prop
  have hms : Measurable (Function.uncurry step) := by
    dsimp [step, Function.uncurry, acceleratedUpdate, acceleratedQuery]
    fun_prop
  have hmi : Measurable (Function.uncurry inc) := by
    dsimp [inc, z0, err, Function.uncurry, acceleratedUpdate, acceleratedQuery]
    fun_prop
  apply trajectory_epoch_probability P Q (V := V) (A := A) hIID hms hme hmi state hc.1 hc.2.1 hB
    (by linarith) (by dsimp [V]; positivity) hc.2.2.1 hc.2.2.2.2.2.2 hstart hstep
  · intro s hs t ht htop
    have hk := hkernel s hs
    have hz : m * ‖z0 s‖ ^ 2 ≤ 8 * B := by
      have hzero := accelerated_noisy_step hm hc.1.le hc.2.1 hstepA
        s.1 s.2 u (g (acceleratedQuery a s)) (0 : E) hmin
        (hsc (acceleratedQuery a s)) (hsmA (acceleratedQuery a s))
      have hd := (le_div_iff₀ hm).mp hzero.2
      dsimp only [z0]
      simp only [Prod.mk.eta] at hd
      dsimp only [en] at hs
      nlinarith only [hd, hs]
    have hmerr : Measurable (err s) := by dsimp [err]; fun_prop
    exact calibrated_kernel_increment_mgf Q hmerr hk.1 hk.2.1 hm hmH hB hell ht htop
      (z0 s) hz hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
  · exact hdecay

lemma epoch_query_bounds {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    {f : E → ℝ} {g : E → E} {U : E → F} {m H B ell : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hell : 2304 ≤ ell)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ H * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : E) (hu : g u = 0) (hmin : ∀ x, f u ≤ f x)
    (hU : ∀ x y, ‖U x - U y‖ ≤ ‖x - y‖) (ref : F)
    (href : m * ‖ref - U u‖ ^ 2 ≤ B) (s : E × E)
    (hs : f s.1 - f u + m / 2 * ‖s.2 - u‖ ^ 2 ≤ 4 * B) :
    let a := Real.sqrt m / (Real.sqrt H * ell)
    m * ‖ref - U (acceleratedQuery a s)‖ ^ 2 ≤ 16 * B ∧
      ‖g (acceleratedQuery a s)‖ ≤ 9 * Real.sqrt (H * B) := by
  intro a
  have hH : 0 < H := lt_of_lt_of_le hm hmH
  have hc := HeavyTailSaddleEnergy.kernel_epoch_calibration hm hmH hB hell
  have ha : 0 ≤ a := hc.1.le
  have hd : m * ‖s.1 - u‖ ^ 2 ≤ 2 * (f s.1 - f u) := by
    have hh := hsc u s.1
    rw [hu, inner_zero_left] at hh
    nlinarith only [hh]
  have hgap : 0 ≤ f s.1 - f u := sub_nonneg.mpr (hmin _)
  refine ⟨HeavyTailSaddleEnergy.frozen_reference_query_bound ha hm hB s.1 s.2 u ref U
    hU hgap hs hd href, ?_⟩
  have hstep : a ^ 2 * H ≤ m := by
    have he : H ≤ H * ell ^ 2 := le_mul_of_one_le_right hH.le (by nlinarith : 1 ≤ ell ^ 2)
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg a)
    exact hh.trans_eq hc.2.2.2.1
  have hgrad := HeavyTailSaddleEnergy.accelerated_query_gradient_sq hm hH.le ha hstep
    s.1 s.2 u g hgap hs hd (OracleTemplate.ComponentEnvelope.smooth_gradient_gap hH hg hl hmin s.1)
    (hl (acceleratedQuery a s) s.1)
  have hsqrt := Real.sq_sqrt (mul_pos hH hB).le
  have hn := Real.sqrt_nonneg (H * B)
  change ‖g (acceleratedQuery a s)‖ ^ 2 ≤ 72 * H * B at hgrad
  nlinarith [norm_nonneg (g (acceleratedQuery a s))]

lemma idealRun_trajectory {S A Ω : Type*} (step : A → S × (ℕ → Ω) → A)
    (N call : ℕ) (state : A) (ξ : ℕ → S × (ℕ → Ω)) :
    StochasticEnvelopeFreshness.idealRun (fun _ => step) N call state ξ =
      HeavyTailedProductProcess.trajectory step N state ξ := by
  induction N generalizing call state ξ with
  | zero => rfl
  | succ N ih => exact ih (call + 1) (step state (ξ 0)) (fun j => ξ (j + 1))
lemma executed_epoch_probability {E X Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [MeasurableSpace Ω]
    (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {raw : X × E → Ω → X × E} (hraw : Measurable (Function.uncurry raw))
    (ref : X) {correction : X × E → X × E} (hcorr : Measurable correction)
    (p σ Lfast : ℝ)
    {f : E → ℝ} {g : E → E}
    (hf : Measurable f) (hg : Measurable g)
    {m H B ell : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hell : 2304 ≤ ell)
    (u : E) (hmin : ∀ v, f u ≤ f v)
    (hsc : ∀ x y, f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsm : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ + H / 2 * ‖y - x‖ ^ 2)
    (state : E × E) (hstart : f state.1 - f u + m / 2 * ‖state.2 - u‖ ^ 2 ≤ B)
    (hkernel : ∀ s : E × E, f s.1 - f u + m / 2 * ‖s.2 - u‖ ^ 2 ≤ 4 * B →
      let a := Real.sqrt m / (Real.sqrt H * ell)
      let J := kernelDepth p σ m B
      let n := kernelBatch p σ m H B J
      let Q := (Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J + 1)))).prod
        (Measure.infinitePi fun _ : ℕ => pnoise)
      let error := fun z : (Fin n → Fin (J + 1)) × (ℕ → Ω) =>
        evalAt (fun k x => raw x (z.2 k))
          (tunedKernelPlan p σ Lfast m H B (extendLevels z.1) ref (acceleratedQuery a s) correction) 0 -
            g (acceleratedQuery a s)
      Integrable error Q ∧ Integrable (fun z => ‖error z‖ ^ 2) Q ∧
        (∀ z, ‖error z‖ ≤ 48 * Real.sqrt (H * B)) ∧
        ‖∫ z, error z ∂Q‖ ≤ Real.sqrt (m * B) / 1024 ∧
        (∫ z, ‖error z‖ ^ 2 ∂Q) ≤ Real.sqrt (m * B) * Real.sqrt (H * B) / 512)
    (N : ℕ) (hdecay : (1 - Real.sqrt m / (Real.sqrt H * ell)) ^ N ≤ 1 / 16) :
    let a := Real.sqrt m / (Real.sqrt H * ell)
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    let S := Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J + 1)))
    let P := (Measure.infinitePi fun _ : ℕ => S).prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let output := fun w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω) =>
      evalAt (fun k x => raw x (w.2 k)) (epochPlan p σ Lfast m H B a w.1 ref correction N state) 0
    P {w | 25 * B / 128 < f (output w).1 - f u + m / 2 * ‖(output w).2 - u‖ ^ 2} ≤
      (N + 1 : ℕ) * ENNReal.ofReal (Real.exp (-ell / 2500)) := by
  intro a J n S P output
  let Q := S.prod (Measure.infinitePi fun _ : ℕ => pnoise)
  let K := fun (v : E) (z : (Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
    evalAt (fun k x => raw x (z.2 k))
      (tunedKernelPlan p σ Lfast m H B (extendLevels z.1) ref v correction) 0
  let step := fun s z => acceleratedUpdate a m s (K (acceleratedQuery a s) z)
  let en := fun s : E × E => f s.1 - f u + m / 2 * ‖s.2 - u‖ ^ 2
  have hK : Measurable (Function.uncurry K) := by
    have hh := HeavyTailSaddleExecution.extended_clipped_batch_measurable (A := E) hraw
      (start := fun _ => ref) (dual := id) (correction := fun _ => correction)
      measurable_const measurable_id (hcorr.comp measurable_snd)
      (kernelHorizon Lfast m) n J (1 / (4 * Lfast)) (32 * Real.sqrt (H * B)) 0
    exact hh.comp (show Measurable (fun w : E × ((Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
      (w.2.1, (w.1, w.2.2))) by fun_prop)
  have hp := accelerated_epoch_probability (Measure.infinitePi fun _ : ℕ => Q) Q
    (OracleTemplate.StochasticGeneralized.infinitePi_iid Q)
    hf hg hK hm hmH hB hell u hmin hsc hsm state hstart hkernel N hdecay
  have hd := HeavyTailSaddleExecution.epoch_plan_law pnoise hraw p σ Lfast m H B a ref hcorr N state
  have hen : Measurable en := by dsimp [en]; fun_prop
  have heq := hd.measure_mem_eq (s := {v | 25 * B / 128 < en v})
    (measurableSet_lt measurable_const hen)
  have hideal : (Measure.infinitePi fun _ : ℕ => Q)
      {w | 25 * B / 128 < en (StochasticEnvelopeFreshness.idealRun (fun _ => step) N 0 state w)} ≤
      (N + 1 : ℕ) * ENNReal.ofReal (Real.exp (-ell / 2500)) := by
    simp only [idealRun_trajectory]
    exact (measure_mono (fun w hw => Or.inr hw)).trans hp
  exact heq.trans_le hideal

lemma epoch_kernel_properties {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F)
    {field : F → E → E} {dual : F → E → F} {a : F → E → Ω → E} {b : F → E → Ω → F}
    (hg : Measurable (Function.uncurry g)) (hc : Measurable correction)
    (hga : ∀ v x ω, (g (x, v) ω + correction (x, v)).1 = a v x ω)
    (hgb : ∀ v x ω, -(g (x, v) ω + correction (x, v)).2 = b v x ω)
    (hf : ∀ v, Measurable (field v)) (ha : ∀ v, Measurable (Function.uncurry (a v)))
    (hb : ∀ v, Measurable (Function.uncurry (b v))) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ v x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field v x - field v y, x - y⟫)
    (hl : ∀ v x y, ‖field v x - field v y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ v x y, ‖dual v x - dual v y‖ ≤ L * ‖x - y‖)
    (hai : ∀ v x, Integrable (a v x) pnoise) (hbi : ∀ v x, Integrable (b v x) pnoise)
    (hap : ∀ v x, Integrable (fun ω => ‖a v x ω - field v x‖ ^ p) pnoise)
    (hbp : ∀ v x, Integrable (fun ω => ‖b v x ω - dual v x‖ ^ p) pnoise)
    (ham : ∀ v x, ∫ ω, a v x ω ∂pnoise = field v x)
    (hbm : ∀ v x, ∫ ω, b v x ω ∂pnoise = dual v x)
    (haV : ∀ v x, (∫ ω, ‖a v x ω - field v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ v x, (∫ ω, ‖b v x ω - dual v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    {m H B ell : ℝ} (hmp : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hell : 2304 ≤ ell)
    {q : F → ℝ} (U : F → E)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖) (hzero : ∀ v, field v (U v) = 0)
    (hqg : ∀ v, HasGradientAt q (dual v (U v)) v)
    (hql : ∀ v w, ‖dual v (U v) - dual w (U w)‖ ≤ H * ‖v - w‖)
    (hqsc : ∀ v w, q v + ⟪dual v (U v), w - v⟫ + m / 2 * ‖w - v‖ ^ 2 ≤ q w)
    (u : F) (hu : dual u (U u) = 0) (hmin : ∀ v, q u ≤ q v)
    (ref : E) (href : m * ‖ref - U u‖ ^ 2 ≤ B)
    (s : F × F) (hs : q s.1 - q u + m / 2 * ‖s.2 - u‖ ^ 2 ≤ 4 * B) :
    let α := Real.sqrt m / (Real.sqrt H * ell)
    let v := acceleratedQuery α s
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    let Q := (Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J + 1)))).prod
      (Measure.infinitePi fun _ : ℕ => pnoise)
    let error := fun z : (Fin n → Fin (J + 1)) × (ℕ → Ω) =>
      evalAt (fun k x => g x (z.2 k))
        (tunedKernelPlan p σ L m H B (extendLevels z.1) ref v correction) 0 - dual v (U v)
    Integrable error Q ∧ Integrable (fun z => ‖error z‖ ^ 2) Q ∧
      (∀ z, ‖error z‖ ≤ 48 * Real.sqrt (H * B)) ∧
      ‖∫ z, error z ∂Q‖ ≤ Real.sqrt (m * B) / 1024 ∧
      (∫ z, ‖error z‖ ^ 2 ∂Q) ≤ Real.sqrt (m * B) * Real.sqrt (H * B) / 512 := by
  intro α v J n Q error
  have hbnd := epoch_query_bounds hmp hmH hB hell hqg hql hqsc u hu hmin hU ref href s hs
  exact HeavyTailSaddleExecution.tuned_kernel_properties pnoise g correction v hg hc
    (hga v) (hgb v) (hf v) (ha v) (hb v) hL hp hp2 hσ (hm v) (hl v) (hdl v)
    (hai v) (hbi v) (hap v) (hbp v) (ham v) (hbm v) (haV v) (hbV v)
    hmp hmH hB ref (U v) (hzero v) hbnd.1 hbnd.2

lemma epoch_success_probability {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F)
    {field : F → E → E} {dual : F → E → F} {a : F → E → Ω → E} {b : F → E → Ω → F}
    (hg : Measurable (Function.uncurry g)) (hc : Measurable correction)
    (hga : ∀ v x ω, (g (x, v) ω + correction (x, v)).1 = a v x ω)
    (hgb : ∀ v x ω, -(g (x, v) ω + correction (x, v)).2 = b v x ω)
    (hf : ∀ v, Measurable (field v)) (ha : ∀ v, Measurable (Function.uncurry (a v)))
    (hb : ∀ v, Measurable (Function.uncurry (b v))) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ v x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field v x - field v y, x - y⟫)
    (hl : ∀ v x y, ‖field v x - field v y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ v x y, ‖dual v x - dual v y‖ ≤ L * ‖x - y‖)
    (hai : ∀ v x, Integrable (a v x) pnoise) (hbi : ∀ v x, Integrable (b v x) pnoise)
    (hap : ∀ v x, Integrable (fun ω => ‖a v x ω - field v x‖ ^ p) pnoise)
    (hbp : ∀ v x, Integrable (fun ω => ‖b v x ω - dual v x‖ ^ p) pnoise)
    (ham : ∀ v x, ∫ ω, a v x ω ∂pnoise = field v x)
    (hbm : ∀ v x, ∫ ω, b v x ω ∂pnoise = dual v x)
    (haV : ∀ v x, (∫ ω, ‖a v x ω - field v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ v x, (∫ ω, ‖b v x ω - dual v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    {m H B δ : ℝ} (hmp : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {q : F → ℝ} (U : F → E)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖) (hzero : ∀ v, field v (U v) = 0)
    (hqg : ∀ v, HasGradientAt q (dual v (U v)) v)
    (hql : ∀ v w, ‖dual v (U v) - dual w (U w)‖ ≤ H * ‖v - w‖)
    (hqsc : ∀ v w, q v + ⟪dual v (U v), w - v⟫ + m / 2 * ‖w - v‖ ^ 2 ≤ q w)
    (u : F) (hu : dual u (U u) = 0) (hmin : ∀ v, q u ≤ q v)
    (ref : E) (href : m * ‖ref - U u‖ ^ 2 ≤ B)
    (state : F × F) (hstart : q state.1 - q u + m / 2 * ‖state.2 - u‖ ^ 2 ≤ B) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    let S := Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J + 1)))
    let P := (Measure.infinitePi fun _ : ℕ => S).prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let output := fun w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω) =>
      evalAt (fun k x => g x (w.2 k))
        (epochPlan p σ L m H B (epochMomentum m H δ) w.1 ref correction (epochSteps m H δ) state) 0
    P {w | 25 * B / 128 < q (output w).1 - q u + m / 2 * ‖(output w).2 - u‖ ^ 2} ≤
      ENNReal.ofReal δ := by
  intro J n S P output
  have hH : 0 < H := lt_of_lt_of_le hmp hmH
  have ht := HeavyTailSaddleEnergy.epoch_explicit_tuning hmp hmH hδ hδ1
  have hqm : Measurable q :=
    (continuous_iff_continuousAt.mpr (fun v => (hqg v).differentiableAt.continuousAt)).measurable
  have hgl : LipschitzWith (Real.toNNReal H) (fun v => dual v (U v)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, Real.coe_toNNReal H hH.le] using hql x y
  have hker (s : F × F) (hs : q s.1 - q u + m / 2 * ‖s.2 - u‖ ^ 2 ≤ 4 * B) :=
    epoch_kernel_properties pnoise g correction hg hc hga hgb hf ha hb hL hp hp2 hσ
      hm hl hdl hai hbi hap hbp ham hbm haV hbV hmp hmH hB ht.1 U hU hzero
      hqg hql hqsc u hu hmin ref href s hs
  have he := executed_epoch_probability pnoise hg ref hc p σ L hqm hgl.continuous.measurable
    hmp hmH hB ht.1 u hmin hqsc (OracleTemplate.Gradient.smooth_upper_bound hqg hql)
    state hstart hker (epochSteps m H δ) ht.2.2.2.1
  apply he.trans
  calc
    _ = ENNReal.ofReal ((epochSteps m H δ + 1 : ℝ) * Real.exp (-epochLog m H δ / 2500)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_add]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal ht.2.2.2.2.1

lemma halving_success_probability {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F)
    {field : F → E → E} {dual : F → E → F} {a : F → E → Ω → E} {b : F → E → Ω → F}
    (hg : Measurable (Function.uncurry g)) (hc : Measurable correction)
    (hga : ∀ v x ω, (g (x, v) ω + correction (x, v)).1 = a v x ω)
    (hgb : ∀ v x ω, -(g (x, v) ω + correction (x, v)).2 = b v x ω)
    (hf : ∀ v, Measurable (field v)) (ha : ∀ v, Measurable (Function.uncurry (a v)))
    (hb : ∀ v, Measurable (Function.uncurry (b v))) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ v x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field v x - field v y, x - y⟫)
    (hl : ∀ v x y, ‖field v x - field v y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ v x y, ‖dual v x - dual v y‖ ≤ L * ‖x - y‖)
    (hai : ∀ v x, Integrable (a v x) pnoise) (hbi : ∀ v x, Integrable (b v x) pnoise)
    (hap : ∀ v x, Integrable (fun ω => ‖a v x ω - field v x‖ ^ p) pnoise)
    (hbp : ∀ v x, Integrable (fun ω => ‖b v x ω - dual v x‖ ^ p) pnoise)
    (ham : ∀ v x, ∫ ω, a v x ω ∂pnoise = field v x)
    (hbm : ∀ v x, ∫ ω, b v x ω ∂pnoise = dual v x)
    (haV : ∀ v x, (∫ ω, ‖a v x ω - field v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ v x, (∫ ω, ‖b v x ω - dual v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    {m H B δ : ℝ} (hmp : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {q : F → ℝ} (U : F → E)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖) (hzero : ∀ v, field v (U v) = 0)
    (hqg : ∀ v, HasGradientAt q (dual v (U v)) v)
    (hql : ∀ v w, ‖dual v (U v) - dual w (U w)‖ ≤ H * ‖v - w‖)
    (hqsc : ∀ v w, q v + ⟪dual v (U v), w - v⟫ + m / 2 * ‖w - v‖ ^ 2 ≤ q w)
    (u : F) (hu : dual u (U u) = 0) (hmin : ∀ v, q u ≤ q v)
    (ref : E) (href : m * ‖ref - U u‖ ^ 2 ≤ B)
    (state : F × F) (hstart : q state.1 - q u + m / 2 * ‖state.2 - u‖ ^ 2 ≤ B) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    let S := Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J + 1)))
    let P := (Measure.infinitePi fun _ : ℕ => S).prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let output := fun w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω) =>
      evalAt (fun k x => g x (w.2 k)) (halvingPlan p σ L m H B δ w.1 ref state correction) 0
    P {w | B / 2 < m * ‖(output w).1 - U u‖ ^ 2 ∨
      B / 2 < q (output w).2 - q u + m / 2 * ‖(output w).2 - u‖ ^ 2 ∨
      Real.sqrt (B / m) / 16 < ‖(output w).1 - U (output w).2‖} ≤ ENNReal.ofReal δ := by
  intro J n S P output
  let Q := Measure.infinitePi fun _ : ℕ => S
  let N := epochSteps m H (δ / 2)
  let α := epochMomentum m H (δ / 2)
  let length := fun seeds : ℕ → Fin n → Fin (J + 1) =>
    slotCalls (fun j => batchCalls (kernelHorizon L m) (extendLevels (seeds j)) n) N 0
  let X := fun w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω) =>
    evalAt (fun k x => g x (w.2 k)) (epochPlan p σ L m H B α w.1 ref correction N state) 0
  let next := fun (v : F) (ξ : ℕ → Ω) =>
    evalAt (fun k x => g x (ξ k)) (tunedRefreshPlan p σ L (Real.sqrt (B / m)) (δ / 2) ref v correction) 0
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 ≤ 1 := by linarith
  have hR : 0 < Real.sqrt (B / m) := Real.sqrt_pos.mpr (div_pos hB hmp)
  have hXm : Measurable X := by
    have hh := HeavyTailSaddleExecution.epoch_plan_measurable (A := Unit) hg
      (ref := fun _ => ref) (initial := fun _ => state) (correction := fun _ => correction)
      measurable_const measurable_const (hc.comp measurable_snd) p σ L m H B α N
    exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)
  have hlen : Measurable length := HeavyTailSaddleExecution.epoch_calls_measurable p σ L m H B N 0
  have hdep (seeds : ℕ → Fin n → Fin (J + 1)) (ξ ζ : ℕ → Ω)
      (h : ∀ j, j < length seeds → ξ j = ζ j) : X (seeds, ξ) = X (seeds, ζ) := by
    apply StochasticEnvelopeExecution.evalAt_prefix_congr
    intro k hk x
    simpa only [Nat.zero_add] using congrArg (g x) (h k hk)
  have hqm : Measurable q :=
    (continuous_iff_continuousAt.mpr (fun v => (hqg v).differentiableAt.continuousAt)).measurable
  have hUl : LipschitzWith 1 U := LipschitzWith.of_dist_le_mul (fun v w => by simpa [dist_eq_norm] using hU v w)
  have hd (v : F) : m * ‖v - u‖ ^ 2 ≤ 2 * (q v - q u) := by
    have hh := hqsc u v
    rw [hu, inner_zero_left] at hh
    nlinarith only [hh]
  have hnext : Measurable (Function.uncurry next) := by
    exact HeavyTailSaddleRefresh.refresh_plan_measurable (A := F) hg
      (start := fun _ => ref) (dual := id) (correction := fun _ => correction)
      measurable_const measurable_id (hc.comp measurable_snd)
      256 (refreshBatch p σ L (Real.sqrt (B / m))) (refreshRepetitions (δ / 2))
      (by unfold refreshBatch; omega) (1 / (4 * L)) (Real.sqrt (B / m)) 0
  have hrough := epoch_success_probability pnoise g correction hg hc hga hgb hf ha hb hL hp hp2 hσ
    hm hl hdl hai hbi hap hbp ham hbm haV hbV hmp hmH hB hδ2 hδ21 U hU hzero
    hqg hql hqsc u hu hmin ref href state hstart
  have hrefresh (v : F) (hv : ‖ref - U v‖ ≤ 13 * Real.sqrt (B / m) / 8) :=
    HeavyTailSaddleRefresh.executed_refresh_confidence pnoise (Measure.infinitePi fun _ : ℕ => pnoise)
      (OracleTemplate.StochasticGeneralized.infinitePi_iid pnoise) g correction v (hga v) (hf v) (ha v)
      hL hR hp hp2 hσ hδ2 hδ21 (hm v) (hl v) (hai v) (hap v) (ham v) (haV v) (U v) ref (hzero v) hv
  have hprob := HeavyTailSaddleRefresh.refreshed_epoch_failure Q pnoise hlen X hXm hdep hqm U hUl.continuous.measurable
    hU u ref hmp hB hd href next hnext hrough hrefresh
  let refreshed := fun w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω) =>
    next (X w).1 (fun j => w.2 (length w.1 + j))
  have heq (w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω)) : output w = (refreshed w, (X w).1) := by
    dsimp only [output]
    rw [HeavyTailSaddleExecution.eval_halving_plan]
    simp only [Nat.zero_add]
    apply Prod.ext
    · have hh := StochasticEnvelopeExecution.evalAt_shift (fun k x => g x (w.2 k))
        (tunedRefreshPlan p σ L (Real.sqrt (B / m)) (δ / 2) ref (X w).1 correction) (length w.1) 0
      simpa only [Nat.add_zero] using hh.symm
    · rfl
  simp_rw [heq]
  refine hprob.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

lemma trajectory_advance {S Z : Type*} (T : S → Z → S) (N call : ℕ)
    (s : S) (ξ : ℕ → Z) :
    trajectory T N s (fun j => ξ (call + j)) =
      OracleTemplate.StochasticGradient.advance (fun k s => T s (ξ k)) N call s := by
  induction N generalizing call s with
  | zero => rfl
  | succ N ih =>
    simpa only [trajectory, OracleTemplate.StochasticGradient.advance, Nat.add_zero,
      Nat.add_assoc, Nat.add_comm 1] using ih (call + 1) (T s (ξ call))

lemma trajectory_certificate_failure {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (T : S → Z → S)
    (hT : Measurable (Function.uncurry T)) (good : Set S) (hg : MeasurableSet good)
    (cert : Set (S × Z)) (hc : MeasurableSet cert)
    (hpreserve : ∀ s z, s ∈ good → (s,z) ∈ cert → T s z ∈ good)
    {η : ℝ} (hη : 0 ≤ η)
    (hprob : ∀ s ∈ good, P.real {z | (s,z) ∉ cert} ≤ η)
    (K : ℕ) (s : S) (hs : s ∈ good) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | trajectory T K s ξ ∉ good ∨ ∃ j < K, (trajectory T j s ξ, ξ j) ∉ cert}
      ≤ ENNReal.ofReal (K * η) := by
  let bad : Set (S × Z) := {w | w.1 ∈ good ∧ w ∉ cert}
  have hb : MeasurableSet bad := (hg.preimage measurable_fst).inter hc.compl
  have hp (v : S) : P.real {z | (v,z) ∈ bad} ≤ η := by
    by_cases hv : v ∈ good
    · simpa only [bad, Set.mem_ofPred_eq, hv, true_and] using hprob v hv
    · simpa only [bad, Set.mem_ofPred_eq, hv, false_and, Set.ofPred_false,
        measureReal_empty] using hη
  have hbound := (StochasticEnvelopeFreshness.fixed_step_failure_probability
    P T hT bad hb hp K s).2
  refine (measure_mono ?_).trans hbound
  intro ξ hξ
  by_contra hn
  have hlocal (j : ℕ) (hj : j < K) :
      ¬ (trajectory T j s ξ ∈ good ∧ (trajectory T j s ξ, ξ j) ∉ cert) := by
    intro hh
    apply hn
    refine ⟨j, hj, ?_⟩
    simpa only [← trajectory_advance, Nat.zero_add, bad, Set.mem_ofPred_eq] using hh
  have hall (j : ℕ) (hj : j ≤ K) : trajectory T j s ξ ∈ good := by
    induction j with
    | zero => exact hs
    | succ j ih =>
      have hprev := ih (by omega)
      rw [trajectory_succ_last]
      exact hpreserve _ _ hprev (by by_contra hh; exact hlocal j (by omega) ⟨hprev, hh⟩)
  rcases hξ with hn | ⟨j, hj, hn⟩
  · exact hn (hall K le_rfl)
  · exact hlocal j hj ⟨hall j (Nat.le_of_lt hj), hn⟩

lemma counter_trajectory {S A Ω : Type*} (step : ℕ → A → S × (ℕ → Ω) → A)
    (N call : ℕ) (state : A) (ξ : ℕ → S × (ℕ → Ω)) :
    trajectory (fun (v : ℕ × A) z => (v.1 + 1, step v.1 v.2 z)) N (call, state) ξ =
      (call + N, StochasticEnvelopeFreshness.idealRun step N call state ξ) := by
  induction N generalizing call state ξ with
  | zero => rfl
  | succ N ih =>
    simpa only [trajectory, StochasticEnvelopeFreshness.idealRun, Nat.add_assoc,
      Nat.add_comm 1] using ih (call + 1) (step call state (ξ 0)) (fun j => ξ (j + 1))

lemma inhomogeneous_certificate_failure {S A Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure (S × (ℕ → Ω))) [IsProbabilityMeasure P]
    (step : ℕ → A → S × (ℕ → Ω) → A)
    (ht : ∀ j, Measurable (Function.uncurry (step j)))
    (good : ℕ → Set A) (hg : ∀ j, MeasurableSet (good j))
    (cert : ℕ → Set (A × (S × (ℕ → Ω)))) (hc : ∀ j, MeasurableSet (cert j))
    (hpreserve : ∀ j s z, s ∈ good j → (s,z) ∈ cert j → step j s z ∈ good (j + 1))
    {η : ℝ} (hη : 0 ≤ η)
    (hprob : ∀ j s, s ∈ good j → P.real {z | (s,z) ∉ cert j} ≤ η)
    (K : ℕ) (s : A) (hs : s ∈ good 0) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | StochasticEnvelopeFreshness.idealRun step K 0 s ξ ∉ good K ∨
        ∃ j < K, (StochasticEnvelopeFreshness.idealRun step j 0 s ξ, ξ j) ∉ cert j}
      ≤ ENNReal.ofReal (K * η) := by
  let T := fun (v : ℕ × A) z => (v.1 + 1, step v.1 v.2 z)
  let G : Set (ℕ × A) := {v | v.2 ∈ good v.1}
  let C : Set ((ℕ × A) × (S × (ℕ → Ω))) := {w | (w.1.2,w.2) ∈ cert w.1.1}
  have hG : MeasurableSet G := by
    have hh := MeasurableSet.iUnion (fun j : ℕ => (measurableSet_singleton j).prod (hg j))
    convert hh using 1
    ext v
    simp [G]
  have hC : MeasurableSet C := by
    have hh := MeasurableSet.iUnion (fun j : ℕ => (measurableSet_singleton j).prod (hc j))
    have he : (⋃ j : ℕ, ({j} : Set ℕ) ×ˢ cert j) = {w | w.2 ∈ cert w.1} := by
      ext v
      simp
    rw [he] at hh
    exact hh.preimage (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hT : Measurable (Function.uncurry T) := by
    have hh : Measurable (fun w : ℕ × (A × (S × (ℕ → Ω))) =>
        step w.1 w.2.1 w.2.2) := measurable_from_prod_countable_right (fun j => ht j)
    exact (measurable_fst.fst.add measurable_const).prodMk
      (hh.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hh := trajectory_certificate_failure P T hT G hG C hC
    (fun v z hv hz => hpreserve v.1 v.2 z hv hz) hη
    (fun v hv => hprob v.1 v.2 hv) K (0,s) hs
  simpa only [T, G, C, counter_trajectory, Nat.zero_add, Set.mem_ofPred_eq] using hh
lemma idealRun_succ_last {S A Ω : Type*} (step : ℕ → A → S × (ℕ → Ω) → A)
    (K : ℕ) (s : A) (ξ : ℕ → S × (ℕ → Ω)) :
    StochasticEnvelopeFreshness.idealRun step (K + 1) 0 s ξ =
      step K (StochasticEnvelopeFreshness.idealRun step K 0 s ξ) (ξ K) := by
  have hh := trajectory_succ_last
    (fun (v : ℕ × A) z => (v.1 + 1, step v.1 v.2 z)) K (0,s) ξ
  simpa only [counter_trajectory, Nat.zero_add] using congrArg Prod.snd hh

lemma inhomogeneous_terminal_certificate {S A Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure (S × (ℕ → Ω))) [IsProbabilityMeasure P]
    (step : ℕ → A → S × (ℕ → Ω) → A)
    (ht : ∀ j, Measurable (Function.uncurry (step j)))
    (good cert : ℕ → Set A) (hg : ∀ j, MeasurableSet (good j))
    (hc : ∀ j, MeasurableSet (cert j)) {η : ℝ} (hη : 0 ≤ η)
    (hprob : ∀ j s, s ∈ good j →
      P.real {z | step j s z ∉ good (j + 1) ∨ step j s z ∉ cert j} ≤ η)
    (K : ℕ) (hK : 0 < K) (s : A) (hs : s ∈ good 0) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | StochasticEnvelopeFreshness.idealRun step K 0 s ξ ∉ good K ∨
        StochasticEnvelopeFreshness.idealRun step K 0 s ξ ∉ cert (K - 1)}
      ≤ ENNReal.ofReal (K * η) := by
  let transition := fun j => (Function.uncurry (step j)) ⁻¹' (good (j+1) ∩ cert j)
  have hh := inhomogeneous_certificate_failure P step ht good hg transition
    (fun j => ((hg (j+1)).inter (hc j)).preimage (ht j))
    (fun _ _ _ _ h => h.1) hη
    (fun j s h => by simpa only [transition, Set.mem_preimage, Set.mem_inter_iff,
      Function.uncurry_def, not_and_or] using hprob j s h) K s hs
  refine (measure_mono ?_).trans hh
  intro ξ hξ
  rcases hξ with h | h
  · exact Or.inl h
  · right
    refine ⟨K-1, by omega, ?_⟩
    intro hn
    have he : K - 1 + 1 = K := by omega
    have hl := idealRun_succ_last step (K-1) s ξ
    rw [he] at hl
    exact h (hl.symm ▸ hn.2)

lemma executed_refinement_probability {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {correction : E × F → E × F} (hc : Measurable correction)
    (p σ L m H B δ : ℝ) (hδ : 0 ≤ δ) (K : ℕ) (hK : 0 < K)
    (good cert : ℕ → Set (E × F)) (hgood : ∀ j, MeasurableSet (good j))
    (hcert : ∀ j, MeasurableSet (cert j)) (state : E × F) (hs : state ∈ good 0) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) : Measure S)
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let step := fun j z (w : S × (ℕ → Ω)) => evalAt (fun k x => g x (w.2 k))
      (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (w.1 j)
        z.1 (z.2,z.2) correction) 0
    (∀ j z, z ∈ good j → P.real {w | step j z w ∉ good (j+1) ∨ step j z w ∉ cert j}
      ≤ δ / (K + 1)) →
    let output := fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
      (refinementPlan p σ L m H B δ K w.1 state correction) 0
    ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise))
      {w | output w ∉ good K ∨ output w ∉ cert (K - 1)} ≤ ENNReal.ofReal δ := by
  intro S Q P step hprob output
  have ht : ∀ j, Measurable (Function.uncurry (step j)) :=
    HeavyTailSaddleRefresh.refinement_stage_measurable hg hc p σ L m H B δ K
  have hh := inhomogeneous_terminal_certificate P step ht good cert hgood hcert
    (show 0 ≤ δ / (K + 1) by positivity) hprob K hK state hs
  have hd := HeavyTailSaddleRefresh.refinement_plan_law pnoise hg hc p σ L m H B δ K state
  have he := hd.measure_mem_eq (s := (good K)ᶜ ∪ (cert (K-1))ᶜ)
    ((hgood K).compl.union (hcert (K-1)).compl)
  have hb : (K : ℝ) * (δ / (K + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < K + 1)]
    nlinarith
  exact he.trans_le (hh.trans (ENNReal.ofReal_le_ofReal hb))
lemma refinement_stage_success_probability {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F)
    {field : F → E → E} {dual : F → E → F} {a : F → E → Ω → E} {b : F → E → Ω → F}
    (hg : Measurable (Function.uncurry g)) (hc : Measurable correction)
    (hga : ∀ v x ω, (g (x, v) ω + correction (x, v)).1 = a v x ω)
    (hgb : ∀ v x ω, -(g (x, v) ω + correction (x, v)).2 = b v x ω)
    (hf : ∀ v, Measurable (field v)) (ha : ∀ v, Measurable (Function.uncurry (a v)))
    (hb : ∀ v, Measurable (Function.uncurry (b v))) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ v x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field v x - field v y, x - y⟫)
    (hl : ∀ v x y, ‖field v x - field v y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ v x y, ‖dual v x - dual v y‖ ≤ L * ‖x - y‖)
    (hai : ∀ v x, Integrable (a v x) pnoise) (hbi : ∀ v x, Integrable (b v x) pnoise)
    (hap : ∀ v x, Integrable (fun ω => ‖a v x ω - field v x‖ ^ p) pnoise)
    (hbp : ∀ v x, Integrable (fun ω => ‖b v x ω - dual v x‖ ^ p) pnoise)
    (ham : ∀ v x, ∫ ω, a v x ω ∂pnoise = field v x)
    (hbm : ∀ v x, ∫ ω, b v x ω ∂pnoise = dual v x)
    (haV : ∀ v x, (∫ ω, ‖a v x ω - field v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ v x, (∫ ω, ‖b v x ω - dual v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    {m H B δ : ℝ} (hmp : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {q : F → ℝ} (U : F → E)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖) (hzero : ∀ v, field v (U v) = 0)
    (hqg : ∀ v, HasGradientAt q (dual v (U v)) v)
    (hql : ∀ v w, ‖dual v (U v) - dual w (U w)‖ ≤ H * ‖v - w‖)
    (hqsc : ∀ v w, q v + ⟪dual v (U v), w - v⟫ + m / 2 * ‖w - v‖ ^ 2 ≤ q w)
    (u : F) (hu : dual u (U u) = 0) (hmin : ∀ v, q u ≤ q v)
    (K j : ℕ) (ref : E) (href : m * ‖ref - U u‖ ^ 2 ≤ refinementEnvelope B j)
    (state : F × F) (hstart : q state.1 - q u + m / 2 * ‖state.2 - u‖ ^ 2 ≤ refinementEnvelope B j) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) : Measure S)
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let output := fun w : S × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
      (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (w.1 j) ref state correction) 0
    P.real {w | refinementEnvelope B (j+1) < m * ‖(output w).1 - U u‖ ^ 2 ∨
      refinementEnvelope B (j+1) < q (output w).2 - q u + m / 2 * ‖(output w).2 - u‖ ^ 2 ∨
      Real.sqrt (refinementEnvelope B j / m) / 16 < ‖(output w).1 - U (output w).2‖}
      ≤ δ / (K + 1) := by
  intro S Q P output
  have hBj : 0 < refinementEnvelope B j := by unfold refinementEnvelope; positivity
  have hd : 0 < δ / (K + 1) := by positivity
  have hd1 : δ / (K + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hh := halving_success_probability pnoise g correction hg hc hga hgb hf ha hb
    hL hp hp2 hσ hm hl hdl hai hbi hap hbp ham hbm haV hbV hmp hmH hBj hd hd1
    U hU hzero hqg hql hqsc u hu hmin ref href state hstart
  let output0 := fun w : (ℕ → Fin (refinementBatch p σ m H B j) →
      Fin (refinementDepth p σ m B j + 1)) × (ℕ → Ω) =>
    evalAt (fun k x => g x (w.2 k))
      (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) w.1 ref state correction) 0
  have ho : Measurable output0 := by
    have h := HeavyTailSaddleRefresh.halving_plan_measurable (A := Unit) hg
      (ref := fun _ => ref) (initial := fun _ => state) (correction := fun _ => correction)
      measurable_const measurable_const (hc.comp measurable_snd)
      p σ L m H (refinementEnvelope B j) (δ / (K + 1))
    exact h.comp ((measurable_const (a := ())).prodMk measurable_id)
  have hqm : Measurable q :=
    (continuous_iff_continuousAt.mpr (fun v => (hqg v).differentiableAt.continuousAt)).measurable
  have hUm : Measurable U := (LipschitzWith.of_dist_le_mul (K := 1)
    (fun v w => by simpa [dist_eq_norm] using hU v w)).continuous.measurable
  let bad := {w | refinementEnvelope B j / 2 < m * ‖(output0 w).1 - U u‖ ^ 2 ∨
    refinementEnvelope B j / 2 < q (output0 w).2 - q u + m / 2 * ‖(output0 w).2 - u‖ ^ 2 ∨
    Real.sqrt (refinementEnvelope B j / m) / 16 < ‖(output0 w).1 - U (output0 w).2‖}
  have hb : MeasurableSet bad := by
    have h1 := measurableSet_lt (measurable_const (a := refinementEnvelope B j / 2))
      (show Measurable (fun w : (ℕ → Fin (refinementBatch p σ m H B j) → Fin (refinementDepth p σ m B j + 1)) × (ℕ → Ω) => m * ‖(output0 w).1 - U u‖ ^ 2) by fun_prop)
    have h2 := measurableSet_lt (measurable_const (a := refinementEnvelope B j / 2))
      (show Measurable (fun w : (ℕ → Fin (refinementBatch p σ m H B j) → Fin (refinementDepth p σ m B j + 1)) × (ℕ → Ω) => q (output0 w).2 - q u + m / 2 * ‖(output0 w).2 - u‖ ^ 2) by fun_prop)
    have h3 := measurableSet_lt (measurable_const (a := Real.sqrt (refinementEnvelope B j / m) / 16))
      (show Measurable (fun w : (ℕ → Fin (refinementBatch p σ m H B j) → Fin (refinementDepth p σ m B j + 1)) × (ℕ → Ω) => ‖(output0 w).1 - U (output0 w).2‖) by fun_prop)
    exact h1.union (h2.union h3)
  have hmap := (HeavyTailSaddleExecution.halving_profile_coordinate_law
    (refinementBatch p σ m H B) (refinementDepth p σ m B) j).prod
      (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => pnoise))
  have he := hmap.measure_preimage hb.nullMeasurableSet
  have hmeasure : P {w | refinementEnvelope B (j+1) < m * ‖(output w).1 - U u‖ ^ 2 ∨
      refinementEnvelope B (j+1) < q (output w).2 - q u + m / 2 * ‖(output w).2 - u‖ ^ 2 ∨
      Real.sqrt (refinementEnvelope B j / m) / 16 < ‖(output w).1 - U (output w).2‖}
      ≤ ENNReal.ofReal (δ / (K + 1)) := by
    rw [HeavyTailSaddleRecovery.refinement_envelope_succ]
    exact he.trans_le hh
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure).trans_eq (ENNReal.toReal_ofReal hd.le)
lemma refinement_success_probability {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F)
    {field : F → E → E} {dual : F → E → F} {a : F → E → Ω → E} {b : F → E → Ω → F}
    (hg : Measurable (Function.uncurry g)) (hc : Measurable correction)
    (hga : ∀ v x ω, (g (x, v) ω + correction (x, v)).1 = a v x ω)
    (hgb : ∀ v x ω, -(g (x, v) ω + correction (x, v)).2 = b v x ω)
    (hf : ∀ v, Measurable (field v)) (ha : ∀ v, Measurable (Function.uncurry (a v)))
    (hb : ∀ v, Measurable (Function.uncurry (b v))) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ v x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field v x - field v y, x - y⟫)
    (hl : ∀ v x y, ‖field v x - field v y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ v x y, ‖dual v x - dual v y‖ ≤ L * ‖x - y‖)
    (hai : ∀ v x, Integrable (a v x) pnoise) (hbi : ∀ v x, Integrable (b v x) pnoise)
    (hap : ∀ v x, Integrable (fun ω => ‖a v x ω - field v x‖ ^ p) pnoise)
    (hbp : ∀ v x, Integrable (fun ω => ‖b v x ω - dual v x‖ ^ p) pnoise)
    (ham : ∀ v x, ∫ ω, a v x ω ∂pnoise = field v x)
    (hbm : ∀ v x, ∫ ω, b v x ω ∂pnoise = dual v x)
    (haV : ∀ v x, (∫ ω, ‖a v x ω - field v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ v x, (∫ ω, ‖b v x ω - dual v x‖ ^ p ∂pnoise) ≤ σ ^ p)
    {m H B δ : ℝ} (hmp : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {q : F → ℝ} (U : F → E)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖) (hzero : ∀ v, field v (U v) = 0)
    (hqg : ∀ v, HasGradientAt q (dual v (U v)) v)
    (hql : ∀ v w, ‖dual v (U v) - dual w (U w)‖ ≤ H * ‖v - w‖)
    (hqsc : ∀ v w, q v + ⟪dual v (U v), w - v⟫ + m / 2 * ‖w - v‖ ^ 2 ≤ q w)
    (u : F) (hu : dual u (U u) = 0) (hmin : ∀ v, q u ≤ q v)
    (K : ℕ) (hK : 0 < K) (ref : E) (href : m * ‖ref - U u‖ ^ 2 ≤ B)
    (start : F) (hstart : q start - q u + m / 2 * ‖start - u‖ ^ 2 ≤ B) :
    let S := HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) : Measure S)
    let P := (Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let output := fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
      (refinementPlan p σ L m H B δ K w.1 (ref,start) correction) 0
    P {w | refinementEnvelope B K < m * ‖(output w).1 - U u‖ ^ 2 ∨
      refinementEnvelope B K < q (output w).2 - q u + m / 2 * ‖(output w).2 - u‖ ^ 2 ∨
      Real.sqrt (refinementEnvelope B (K-1) / m) / 16 < ‖(output w).1 - U (output w).2‖}
      ≤ ENNReal.ofReal δ := by
  intro S Q P output
  let good := fun j => {z : E × F | m * ‖z.1 - U u‖ ^ 2 ≤ refinementEnvelope B j ∧
    q z.2 - q u + m / 2 * ‖z.2 - u‖ ^ 2 ≤ refinementEnvelope B j}
  let cert := fun j => {z : E × F | ‖z.1 - U z.2‖ ≤ Real.sqrt (refinementEnvelope B j / m) / 16}
  have hqm : Measurable q :=
    (continuous_iff_continuousAt.mpr (fun v => (hqg v).differentiableAt.continuousAt)).measurable
  have hUm : Measurable U := (LipschitzWith.of_dist_le_mul (K := 1)
    (fun v w => by simpa [dist_eq_norm] using hU v w)).continuous.measurable
  have hgood (j : ℕ) : MeasurableSet (good j) := by
    have h1 := measurableSet_le
      (show Measurable (fun z : E × F => m * ‖z.1 - U u‖ ^ 2) by fun_prop)
      (measurable_const (a := refinementEnvelope B j))
    have h2 := measurableSet_le
      (show Measurable (fun z : E × F => q z.2 - q u + m / 2 * ‖z.2 - u‖ ^ 2) by fun_prop)
      (measurable_const (a := refinementEnvelope B j))
    exact h1.inter h2
  have hcert (j : ℕ) : MeasurableSet (cert j) := by
    apply measurableSet_le <;> fun_prop
  have hs : (ref,start) ∈ good 0 := by
    simpa only [good, Set.mem_ofPred_eq, refinementEnvelope, pow_zero, div_one] using And.intro href hstart
  have hh := executed_refinement_probability pnoise hg hc p σ L m H B δ hδ.le K hK
    good cert hgood hcert (ref,start) hs
  have hlocal : ∀ j (z : E × F), z ∈ good j →
      (Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)).real
        {w : S × (ℕ → Ω) |
          let out := evalAt (fun k x => g x (w.2 k))
            (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K+1)) (w.1 j)
              z.1 (z.2,z.2) correction) 0
          out ∉ good (j+1) ∨ out ∉ cert j} ≤ δ / (K+1) := by
    intro j z hz
    have hj := refinement_stage_success_probability pnoise g correction hg hc hga hgb hf ha hb
      hL hp hp2 hσ hm hl hdl hai hbi hap hbp ham hbm haV hbV hmp hmH hB hδ hδ1
      U hU hzero hqg hql hqsc u hu hmin K j z.1 hz.1 (z.2,z.2) hz.2
    simpa only [good, cert, Set.mem_ofPred_eq, not_and_or, not_le, or_assoc] using hj
  have hresult := hh hlocal
  simpa only [good, cert, Set.mem_ofPred_eq, not_and_or, not_le, or_assoc] using hresult

lemma recovery_stage_parameter_measurable {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ ζ initialBound δ : ℝ) (j : ℕ) :
    let S := RecoveryProfile p σ L μ ζ initialBound
    Measurable (fun w : (E × ((E × F) × F)) × (S × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
          (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
          (recoveryHalvings L μ ζ initialBound j) (w.2.1 j) w.1.2.1
          (proximalCorrection L (recoveryMass μ j-μ) w.1.1 w.1.2.2)) 0) := by
  intro S
  have hc : Measurable (Function.uncurry
      (fun a : E × ((E × F) × F) => proximalCorrection L (recoveryMass μ j-μ) a.1 a.2.2)) :=
    (HeavyTailSaddleRecovery.proximal_correction_measurable L (recoveryMass μ j-μ)).comp
      (show Measurable (fun w : (E × ((E × F) × F)) × (E × F) => ((w.1.1,w.1.2.2),w.2)) by fun_prop)
  have hh := HeavyTailSaddleRefresh.capped_refinement_parameter_measurable hg
    (initial := fun a : E × ((E × F) × F) => a.2.1) measurable_snd.fst hc
    p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
    (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
    (recoveryHalvings L μ ζ initialBound j)
  exact hh.comp (show Measurable (fun w : (E × ((E × F) × F)) × (S × (ℕ → Ω)) =>
    (w.1,(w.2.1 j,w.2.2))) by fun_prop)

lemma recovery_plan_law {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ ζ initialBound δ : ℝ) (center : E) (initial : E × F) :
    let S := RecoveryProfile p σ L μ ζ initialBound
    let Q := (recoveryProfileLaw p σ L μ ζ initialBound : Measure S)
    let child := fun j (seed : S) (state : (E × F) × F) =>
      cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
        (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
        (recoveryHalvings L μ ζ initialBound j) (seed j) state.1
        (proximalCorrection L (recoveryMass μ j-μ) center state.2)
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
        (recoveryPlan p σ L μ ζ initialBound δ w.1 center initial) 0)
      (fun samples => (StochasticEnvelopeFreshness.idealRun
        (fun j (state : (E × F) × F) (w : S × (ℕ → Ω)) =>
          let out := evalAt (fun k x => g x (w.2 k)) (child j w.1 state) 0
          (out,state.2+recoveryMass μ j • out.2))
        (recoveryStages L μ) 0 (initial,0) samples).1)
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise))
      (Measure.infinitePi fun _ : ℕ => Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)) := by
  intro S Q child
  have hs (j : ℕ) : Measurable (fun w : ((E × F) × F) × (S × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k)) (child j w.2.1 w.1) 0) :=
    (recovery_stage_parameter_measurable hg p σ L μ ζ initialBound δ j).comp
      (show Measurable (fun w : ((E × F) × F) × (S × (ℕ → Ω)) => ((center,w.1),w.2)) by fun_prop)
  have hh := StochasticEnvelopeExecution.substituted_statePlan_identDistrib Q pnoise
    (fun j (_ : S) => recoveryStageCap p σ L μ ζ initialBound δ j)
    (fun _ => measurable_const) child g (fun _ state => state)
    (fun j (state : (E × F) × F) (out : E × F) => (out,state.2+recoveryMass μ j • out.2))
    hs (fun _ => measurable_id) (fun _ => by fun_prop) (recoveryStages L μ) (initial,0)
  have hp := hh.comp measurable_fst
  convert hp using 1
  · funext w
    exact evalAt_map (fun k x => g x (w.2 k)) Prod.fst _ 0
  · rfl

open OracleTemplate.PLMinimax HeavyTailSaddleRecovery HeavyTailSaddleMultilevel HeavyTailSaddleRefresh

lemma proximal_refinement_success_probability {E F Ω : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (Pnoise : Measure Ω) [IsProbabilityMeasure Pnoise]
    (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) Pnoise) (hyi : ∀ z, Integrable (oy z) Pnoise)
    (hxm : ∀ z, ∫ ω, ox z ω ∂Pnoise = gx z.1 z.2)
    (hym : ∀ z, ∫ ω, oy z ω ∂Pnoise = gy z.1 z.2)
    {p σ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p) Pnoise)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p ∂Pnoise) ≤ σ^p)
    {m B δ η : ℝ} (hμm : μ ≤ m) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (center : E) (shift : F) (K : ℕ) (hK : 0 < K) (ref : E) (start : F) :
    let U := innerPrimal f L center
    let q := fun y => -dual f L center y+(m-μ)/2*‖y‖^2-⟪shift,y⟫
    ∀ u : F, -gy (U u) u+(m-μ) • u-shift = 0 →
    m*‖ref-U u‖^2 ≤ B → q start-q u+m/2*‖start-u‖^2 ≤ B →
    let Hs := 15*L+m-μ
    let S := HalvingProfile (refinementBatch p σ m Hs B) (refinementDepth p σ m B)
    let Q := (halvingProfileLaw (refinementBatch p σ m Hs B) (refinementDepth p σ m B) : Measure S)
    let P := (Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => Pnoise)
    let output := fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
      (cappedRefinementPlan p σ (3*L) m Hs B δ η K w.1 (ref,start)
        (proximalCorrection L (m-μ) center shift)) 0
    P {w | refinementEnvelope B K < m*‖(output w).1-U u‖^2 ∨
      refinementEnvelope B K < q (output w).2-q u+m/2*‖(output w).2-u‖^2 ∨
      Real.sqrt (refinementEnvelope B (K-1)/m)/16 < ‖(output w).1-U (output w).2‖}
      ≤ ENNReal.ofReal δ+ENNReal.ofReal η := by
  intro U q u hu href hstart Hs S Q P output
  let field := fun v x => gx x v+(2*L) • (x-center)
  let dualField := fun v x => -gy x v+((m-μ) • v-shift)
  let a := fun v x ω => ox (x,v) ω+(2*L) • (x-center)
  let b := fun v x ω => -oy (x,v) ω+((m-μ) • v-shift)
  let g := fun z ω => (ox z ω,oy z ω)
  let correction := proximalCorrection L (m-μ) center shift
  have hgeom := proximal_corrected_fields H (m-μ) center shift
  have hstats := proximal_corrected_oracle Pnoise (fun z => gx z.1 z.2) (fun z => gy z.1 z.2)
    ox oy hox hoy hxi hyi hxm hym (by linarith : 0 ≤ p) hpi hpV L (m-μ) center shift
  rcases hstats with ⟨ha,hb,hai,hbi,ham,hbm,hap,hbp,haV,hbV⟩
  have hq := proximal_regularized_dual_geometry H hsc (sub_nonneg.mpr hμm) center shift
  have hmp : 0 < m := lt_of_lt_of_le H.hμ hμm
  have hqg : ∀ v, HasGradientAt q (dualField v (U v)) v := by
    simpa only [q,dualField,U,sub_eq_add_neg,add_assoc] using hq.1
  have hqsc : ∀ v w, q v+⟪dualField v (U v),w-v⟫+m/2*‖w-v‖^2 ≤ q w := by
    have he : μ+(m-μ)=m := by ring
    have hh := hq.2.1
    dsimp only at hh
    rw [he] at hh
    simpa only [q,dualField,U,sub_eq_add_neg,add_assoc] using hh
  have huz : dualField u (U u) = 0 := by simpa only [dualField,sub_eq_add_neg,add_assoc] using hu
  have hmin (v : F) : q u ≤ q v := by
    have hh := hqsc u v
    rw [huz,inner_zero_left,add_zero] at hh
    have hn := mul_nonneg (show 0 ≤ m/2 by positivity) (sq_nonneg ‖v-u‖)
    linarith
  have hql : ∀ v w, ‖dualField v (U v)-dualField w (U w)‖ ≤ Hs*‖v-w‖ := by
    intro v w
    have hh := hq.2.2.1 v w
    have hh' : ‖dualField v (U v)-dualField w (U w)‖ ≤ (2*L+(m-μ))*‖v-w‖ := by
      simpa only [dualField,U,sub_eq_add_neg,add_assoc] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right (by dsimp [Hs]; linarith [H.hL]) (norm_nonneg _))
  have hf (v : F) : Measurable (field v) :=
    (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (3*L))
      (fun x y => by
        simpa only [dist_eq_norm, Real.coe_toNNReal _ (show 0 ≤ 3*L by linarith [H.hL])]
          using hgeom.2.1 v x y)).continuous.measurable
  have hg : Measurable (Function.uncurry g) := hox.prodMk hoy
  have hc : Measurable correction :=
    (proximal_correction_measurable L (m-μ)).comp
      (show Measurable (fun z : E × F => ((center,shift),z)) by fun_prop)
  let bad := {z : E × F | refinementEnvelope B K < m*‖z.1-U u‖^2 ∨
    refinementEnvelope B K < q z.2-q u+m/2*‖z.2-u‖^2 ∨
    Real.sqrt (refinementEnvelope B (K-1)/m)/16 < ‖z.1-U z.2‖}
  apply capped_refinement_failure Pnoise g correction p σ (3*L) m Hs B δ η hη K (ref,start) bad
  apply refinement_success_probability Pnoise g correction hg hc
    (field := field) (dual := dualField) (a := a) (b := b)
    (fun _ _ _ => rfl) (fun v x ω => by dsimp [g,correction,proximalCorrection,b]; abel)
    hf ha hb (by linarith [H.hL]) hp hp2 hσ
    hgeom.1 hgeom.2.1
    (by simpa only [dualField,sub_eq_add_neg,add_assoc] using hgeom.2.2.1)
    hai hbi hap hbp ham hbm haV hbV
    hmp (by dsimp [Hs]; linarith [H.hμL,H.hL]) hB hδ hδ1 U
    (H.innerPrimal_lipschitz center) hgeom.2.2.2 hqg hql hqsc u huz hmin K hK ref href start hstart

lemma executed_recovery_probability {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ ζ initialBound δ : ℝ) (hδ : 0 ≤ δ) (center : E) (initial : E × F)
    (good cert : ℕ → Set ((E × F) × F))
    (hgood : ∀ j, MeasurableSet (good j)) (hcert : ∀ j, MeasurableSet (cert j))
    (hinit : (initial,0) ∈ good 0) (bad : Set (E × F)) (hbad : MeasurableSet bad)
    (hterminal : ∀ state, state ∈ good (recoveryStages L μ) →
      state ∈ cert (recoveryStages L μ-1) → state.1 ∉ bad) :
    let S := RecoveryProfile p σ L μ ζ initialBound
    let Q := (recoveryProfileLaw p σ L μ ζ initialBound : Measure S)
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let step := fun j (state : (E × F) × F) (w : S × (ℕ → Ω)) =>
      let out := evalAt (fun k x => g x (w.2 k))
        (cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
          (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
          (recoveryHalvings L μ ζ initialBound j) (w.1 j) state.1
          (proximalCorrection L (recoveryMass μ j-μ) center state.2)) 0
      (out,state.2+recoveryMass μ j • out.2)
    (∀ j state, state ∈ good j →
      P.real {w | step j state w ∉ good (j+1) ∨ step j state w ∉ cert j} ≤ δ/(recoveryStages L μ+1)) →
    ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise))
      {w | evalAt (fun k x => g x (w.2 k))
        (recoveryPlan p σ L μ ζ initialBound δ w.1 center initial) 0 ∈ bad} ≤ ENNReal.ofReal δ := by
  intro S Q P step hprob
  have ht (j : ℕ) : Measurable (Function.uncurry (step j)) := by
    have hr := (recovery_stage_parameter_measurable hg p σ L μ ζ initialBound δ j).comp
      (show Measurable (fun w : ((E × F) × F) × (S × (ℕ → Ω)) => ((center,w.1),w.2)) by fun_prop)
    exact hr.prodMk (measurable_fst.snd.add (hr.snd.const_smul (recoveryMass μ j)))
  have hJ : 0 < recoveryStages L μ := by unfold recoveryStages; omega
  have hh := inhomogeneous_terminal_certificate P step ht good cert hgood hcert
    (show 0 ≤ δ/(recoveryStages L μ+1) by positivity) hprob (recoveryStages L μ) hJ (initial,0) hinit
  have hd := recovery_plan_law pnoise hg p σ L μ ζ initialBound δ center initial
  have he := hd.measure_mem_eq hbad
  have hb : (recoveryStages L μ : ℝ)*(δ/(recoveryStages L μ+1)) ≤ δ := by
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : (0:ℝ)<recoveryStages L μ+1)]
    nlinarith
  refine he.trans_le ((measure_mono ?_).trans (hh.trans (ENNReal.ofReal_le_ofReal hb)))
  intro samples hs
  by_cases hg' : StochasticEnvelopeFreshness.idealRun step (recoveryStages L μ) 0 (initial,0) samples ∈ good (recoveryStages L μ)
  · by_cases hc' : StochasticEnvelopeFreshness.idealRun step (recoveryStages L μ) 0 (initial,0) samples ∈ cert (recoveryStages L μ-1)
    · exact False.elim (hterminal _ hg' hc' hs)
    · exact Or.inr hc'
  · exact Or.inl hg'

open StochasticEnvelopeExecution StochasticEnvelopeFreshness

lemma eval_recovery_plan {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E × F → Ω → E × F) (p σ L μ ζ initialBound δ : ℝ) (center : E) (initial : E × F)
    (seeds : ℕ → RecoveryProfile p σ L μ ζ initialBound) (ξ : ℕ → Ω) :
    let S := RecoveryProfile p σ L μ ζ initialBound
    let cost := fun j (_ : S) => recoveryStageCap p σ L μ ζ initialBound δ j
    let child := fun j (seed : S) (state : (E × F) × F) =>
      cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
        (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
        (recoveryHalvings L μ ζ initialBound j) (seed j) state.1
        (proximalCorrection L (recoveryMass μ j-μ) center state.2)
    evalAt (fun k x => g x (ξ k)) (recoveryPlan p σ L μ ζ initialBound δ seeds center initial) 0 =
      (freshRun cost (fun j state (w : S × (ℕ → Ω)) =>
        let out := evalAt (fun k x => g x (w.2 k)) (child j w.1 state) 0
        (out,state.2+recoveryMass μ j • out.2)) (recoveryStages L μ) 0 (initial,0) (seeds,ξ)).1 := by
  intro S cost child
  let update := fun j (state : (E × F) × F) (out : E × F) => (out,state.2+recoveryMass μ j • out.2)
  have he := evalAt_substituted_statePlan cost child g (fun _ state => state) update
    seeds ξ (recoveryStages L μ) 0 0 (initial,0)
  rw [cursorRun_freshRun] at he
  simp only [slotCalls,Nat.zero_add] at he
  calc
    _ = (evalAt (fun k x => g x (ξ k))
        (substitutePlan (fun j => cost j (seeds j)) (fun j => child j (seeds j))
          (statePlan (fun _ state => state) update (recoveryStages L μ) 0 (initial,0)) 0) 0).1 :=
      evalAt_map (fun k x => g x (ξ k)) Prod.fst _ 0
    _ = _ := congrArg Prod.fst he

lemma recovery_plan_parameter_measurable {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ ζ initialBound δ : ℝ) :
    let S := RecoveryProfile p σ L μ ζ initialBound
    Measurable (fun w : (E × (E × F)) × ((ℕ → S) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (recoveryPlan p σ L μ ζ initialBound δ w.2.1 w.1.1 w.1.2) 0) := by
  intro S
  let cost := fun j (_ : S) => recoveryStageCap p σ L μ ζ initialBound δ j
  let step := fun center j (state : (E × F) × F) (w : S × (ℕ → Ω)) =>
    let out := evalAt (fun k x => g x (w.2 k))
      (cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
        (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
        (recoveryHalvings L μ ζ initialBound j) (w.1 j) state.1
        (proximalCorrection L (recoveryMass μ j-μ) center state.2)) 0
    (out,state.2+recoveryMass μ j • out.2)
  have hs (j : ℕ) : Measurable (fun w : (E × ((E × F) × F)) × (S × (ℕ → Ω)) =>
      step w.1.1 j w.1.2 w.2) := by
    have hr := recovery_stage_parameter_measurable hg p σ L μ ζ initialBound δ j
    exact hr.prodMk (measurable_fst.snd.snd.add (hr.snd.const_smul (recoveryMass μ j)))
  have hh := HeavyTailSaddleExecution.parameter_freshRun_measurable (cost := cost)
    (fun _ => measurable_const) hs (recoveryStages L μ) 0
  have ht := (hh.comp (show Measurable
    (fun w : (E × (E × F)) × ((ℕ → S) × (ℕ → Ω)) => ((w.1.1,(w.1.2,0)),w.2)) by fun_prop)).fst
  convert ht using 1
  funext w
  exact eval_recovery_plan g p σ L μ ζ initialBound δ w.1.1 w.1.2 w.2.1 w.2.2

lemma recovery_stage_success_probability {E F Ω : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (Pnoise : Measure Ω) [IsProbabilityMeasure Pnoise]
    (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) Pnoise) (hyi : ∀ z, Integrable (oy z) Pnoise)
    (hxm : ∀ z, ∫ ω, ox z ω ∂Pnoise = gx z.1 z.2)
    (hym : ∀ z, ∫ ω, oy z ω ∂Pnoise = gy z.1 z.2)
    {p σ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p) Pnoise)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p ∂Pnoise) ≤ σ^p)
    {ζ δ : ℝ} (hζ : 0 < ζ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (center : E) (initialBound : ℝ) (root : ℕ → F → F)
    (hroot : ∀ k b, -gy (innerPrimal f L center (root k b)) (root k b)+
      (recoveryMass μ k-μ) • root k b-b = 0) (j : ℕ) (state : (E × F) × F) :
    let U := innerPrimal f L center
    let base := fun v => -dual f L center v
    let gradient := fun v => -gy (U v) v
    state ∈ recoveryGood base U root L μ ζ initialBound j →
    let S := RecoveryProfile p σ L μ ζ initialBound
    let Q := (recoveryProfileLaw p σ L μ ζ initialBound : Measure S)
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => Pnoise)
    let output := fun w : S × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
      (cappedRefinementPlan p σ (3*L) (recoveryMass μ j) (recoverySmoothness L μ j)
        (recoveryEnvelope L μ ζ initialBound j) (recoveryConfidence L μ δ) (recoveryConfidence L μ δ)
        (recoveryHalvings L μ ζ initialBound j) (w.1 j) state.1
        (proximalCorrection L (recoveryMass μ j-μ) center state.2)) 0
    P.real {w | (output w,state.2+recoveryMass μ j • (output w).2) ∉ recoveryGood base U root L μ ζ initialBound (j+1) ∨
      (output w,state.2+recoveryMass μ j • (output w).2) ∉ recoveryCertificate gradient U L μ ζ j}
      ≤ δ/(recoveryStages L μ+1) := by
  intro U base gradient hgood S Q P output
  let m := recoveryMass μ j
  let Hs := recoverySmoothness L μ j
  let B := recoveryEnvelope L μ ζ initialBound j
  let K := recoveryHalvings L μ ζ initialBound j
  let d := recoveryConfidence L μ δ
  let q := recoveryShiftedObjective base μ j state.2
  let u := root j state.2
  let S0 := HalvingProfile (refinementBatch p σ m Hs B) (refinementDepth p σ m B)
  let output0 := fun w : (ℕ → S0) × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
    (cappedRefinementPlan p σ (3*L) m Hs B d d K w.1 state.1 (proximalCorrection L (m-μ) center state.2)) 0
  have hd : 0 < d := by dsimp [d,recoveryConfidence]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d,recoveryConfidence]
    rw [div_le_iff₀ (by positivity : (0:ℝ)<2*(recoveryStages L μ+1))]
    nlinarith
  have henv := recovery_refinement_envelopes (L := L) H.hμ hζ initialBound j
  have hphys := proximal_refinement_success_probability H hsc Pnoise ox oy hox hoy hxi hyi hxm hym
    hp hp2 hσ hpi hpV (recovery_mass_ge H.hμ.le j) henv.1 hd hd1 hd
    center state.2 K henv.2.1 state.1.1 state.1.2 u (hroot j state.2) hgood.1 hgood.2.1
  have hg : Measurable (Function.uncurry (fun z ω => (ox z ω,oy z ω))) := hox.prodMk hoy
  have hc : Measurable (proximalCorrection L (m-μ) center state.2) :=
    (proximal_correction_measurable L (m-μ)).comp
      (show Measurable (fun z : E × F => ((center,state.2),z)) by fun_prop)
  have ho : Measurable output0 := by
    have hh := capped_refinement_parameter_measurable (A := Unit) hg
      (initial := fun _ => state.1) (correction := fun _ => proximalCorrection L (m-μ) center state.2)
      measurable_const (hc.comp measurable_snd) p σ (3*L) m Hs B d d K
    exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)
  have hgeo := recovery_stage_geometry H hsc center j state.2
  have hqm : Measurable q :=
    (continuous_iff_continuousAt.mpr (fun v => (hgeo.1 v).differentiableAt.continuousAt)).measurable
  have hUm : Measurable U := (LipschitzWith.of_dist_le_mul (K := 1)
    (fun v w => by simpa [dist_eq_norm] using H.innerPrimal_lipschitz center v w)).continuous.measurable
  let bad := {w : (ℕ → S0) × (ℕ → Ω) |
    refinementEnvelope B K < m*‖(output0 w).1-U u‖^2 ∨
    refinementEnvelope B K < q (output0 w).2-q u+m/2*‖(output0 w).2-u‖^2 ∨
    Real.sqrt (refinementEnvelope B (K-1)/m)/16 < ‖(output0 w).1-U (output0 w).2‖}
  have hb : MeasurableSet bad := by
    have h1 := measurableSet_lt (measurable_const (a := refinementEnvelope B K))
      (show Measurable (fun w : (ℕ → S0) × (ℕ → Ω) => m*‖(output0 w).1-U u‖^2) by fun_prop)
    have h2 := measurableSet_lt (measurable_const (a := refinementEnvelope B K))
      (show Measurable (fun w : (ℕ → S0) × (ℕ → Ω) => q (output0 w).2-q u+m/2*‖(output0 w).2-u‖^2) by fun_prop)
    have h3 := measurableSet_lt (measurable_const (a := Real.sqrt (refinementEnvelope B (K-1)/m)/16))
      (show Measurable (fun w : (ℕ → S0) × (ℕ → Ω) => ‖(output0 w).1-U (output0 w).2‖) by fun_prop)
    exact h1.union (h2.union h3)
  have hmap := (recovery_profile_coordinate_law p σ L μ ζ initialBound j).prod
    (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => Pnoise))
  have hmeasure := (hmap.measure_preimage hb.nullMeasurableSet).trans_le hphys
  have hcur (x : F) : m/2*‖x-u‖^2 ≤ q x-q u := by
    have hh := hgeo.2.1 u x
    have hz := hroot j state.2
    change recoveryShiftedGradient gradient μ j state.2 u = 0 at hz
    rw [hz,inner_zero_left,add_zero] at hh
    linarith only [hh]
  have hbound : P {w | (output w,state.2+m • (output w).2) ∉ recoveryGood base U root L μ ζ initialBound (j+1) ∨
      (output w,state.2+m • (output w).2) ∉ recoveryCertificate gradient U L μ ζ j}
      ≤ ENNReal.ofReal d+ENNReal.ofReal d := by
    refine (measure_mono ?_).trans hmeasure
    intro w hfail
    by_contra hnot
    change ¬(refinementEnvelope B K < m*‖(output w).1-U u‖^2 ∨
      refinementEnvelope B K < q (output w).2-q u+m/2*‖(output w).2-u‖^2 ∨
      Real.sqrt (refinementEnvelope B (K-1)/m)/16 < ‖(output w).1-U (output w).2‖) at hnot
    simp only [not_or,not_lt] at hnot
    let bnext := state.2+m • (output w).2
    have hngeo := recovery_stage_geometry H hsc center (j+1) bnext
    have hnext (x : F) : m*‖x-root (j+1) bnext‖^2 ≤
        recoveryShiftedObjective base μ (j+1) bnext x-recoveryShiftedObjective base μ (j+1) bnext (root (j+1) bnext) := by
      have hh := hngeo.2.1 (root (j+1) bnext) x
      have hz := hroot (j+1) bnext
      change recoveryShiftedGradient gradient μ (j+1) bnext (root (j+1) bnext)=0 at hz
      rw [hz,inner_zero_left,add_zero] at hh
      have hmhalf : recoveryMass μ (j+1)/2=m := by rw [recovery_mass_succ]; dsimp [m]; ring
      rw [hmhalf] at hh
      linarith only [hh]
    have hp' := recovery_stage_preserves base gradient U root H.hμ (by linarith [H.hμL,H.hL]) hζ
      (H.innerPrimal_lipschitz center) initialBound j state (output w) hgood
      hgeo.1 hgeo.2.2 hcur hnext hnot.2.1 hnot.2.2
    exact hfail.elim (fun h => h hp'.1) (fun h => h hp'.2)
  have hbound' : P {w | (output w,state.2+m • (output w).2) ∉ recoveryGood base U root L μ ζ initialBound (j+1) ∨
      (output w,state.2+m • (output w).2) ∉ recoveryCertificate gradient U L μ ζ j}
      ≤ ENNReal.ofReal (2*d) := by
    simpa only [two_mul,ENNReal.ofReal_add hd.le hd.le] using hbound
  have hr := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound').trans_eq (ENNReal.toReal_ofReal (show 0 ≤ 2*d by positivity))
  have he : 2*d=δ/(recoveryStages L μ+1) := by
    dsimp [d,recoveryConfidence]
    field_simp
  exact hr.trans_eq he

open LongTails.Setups.StochasticTwoSidedPL LongTails.Setups.WeaklyConvexHeavyTailed
lemma recovery_success_probability {E F Ω : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (Pnoise : Measure Ω) [IsProbabilityMeasure Pnoise]
    (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) Pnoise) (hyi : ∀ z, Integrable (oy z) Pnoise)
    (hxm : ∀ z, ∫ ω, ox z ω ∂Pnoise = gx z.1 z.2)
    (hym : ∀ z, ∫ ω, oy z ω ∂Pnoise = gy z.1 z.2)
    {p σ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p) Pnoise)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p ∂Pnoise) ≤ σ^p)
    {ζ δ : ℝ} (hζ : 0 < ζ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (center : E) (initialBound : ℝ) (initial : E × F) (u : F)
    (hu : gy (innerPrimal f L center u) u = 0)
    (href : μ*‖initial.1-innerPrimal f L center u‖^2 ≤ initialBound)
    (hstart : -dual f L center initial.2-(-dual f L center u)+μ/2*‖initial.2-u‖^2 ≤ initialBound) :
    let S := RecoveryProfile p σ L μ ζ initialBound
    let Q := (recoveryProfileLaw p σ L μ ζ initialBound : Measure S)
    let P := (Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => Pnoise)
    let output := fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
      (recoveryPlan p σ L μ ζ initialBound δ w.1 center initial) 0
    P {w | ζ < proxObj (maxValue f) L center (output w).1-dual f L center (output w).2} ≤ ENNReal.ofReal δ := by
  intro S Q P output
  let U := innerPrimal f L center
  let base := fun v => -dual f L center v
  let gradient := fun v => -gy (U v) v
  obtain ⟨root,hzero,hr,_⟩ := recovery_root_maps H hsc center
  have hgeo0 := recovery_stage_geometry H hsc center 0 0
  have hSC0 : ∀ x y, base x+⟪gradient x,y-x⟫+μ/2*‖y-x‖^2 ≤ base y := by
    simpa [recoveryShiftedObjective,recoveryShiftedGradient,recoveryMass,base,gradient,U] using hgeo0.2.1
  have hzr : gradient (root 0 0)=0 := by
    simpa [recoveryShiftedGradient,recoveryMass,gradient,U] using hzero 0 0
  have hzu : gradient u=0 := by dsimp [gradient,U]; rw [hu,neg_zero]
  have heq : root 0 0=u := strongly_convex_stationary_unique H.hμ hSC0 hzr hzu
  have hinit := recovery_initial_good base U root L μ ζ initialBound initial u heq href hstart
  have hdual : Measurable (dual f L center) :=
    (continuous_iff_continuousAt.mpr (fun v => (H.dual_hasGradient center v).differentiableAt.continuousAt)).measurable
  have hb : Measurable base := hdual.neg
  have hUm : Measurable U := (LipschitzWith.of_dist_le_mul (K := 1)
    (fun v w => by simpa [dist_eq_norm] using H.innerPrimal_lipschitz center v w)).continuous.measurable
  have hgm : Measurable gradient := by
    suffices hl : LipschitzWith (Real.toNNReal (2*L)) gradient from hl.continuous.measurable
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ (show 0 ≤ 2*L by linarith [H.hL])]
    change ‖-gy (U v) v - -gy (U w) w‖ ≤ 2*L*‖v-w‖
    rw [neg_sub_neg,norm_sub_rev]
    exact H.dual_gradient_lipschitz center v w
  let good := recoveryGood base U root L μ ζ initialBound
  let cert := recoveryCertificate gradient U L μ ζ
  have hgood (j : ℕ) : MeasurableSet (good j) := recovery_good_measurable hb hUm hr L μ ζ initialBound j
  have hcert (j : ℕ) : MeasurableSet (cert j) := recovery_certificate_measurable hgm hUm L μ ζ j
  let bad := {z : E × F | ζ < proxObj (maxValue f) L center z.1-dual f L center z.2}
  have hmax : Measurable (maxValue f) := H.value_continuous.measurable
  have hbad : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    unfold proxObj
    fun_prop
  have hterminal (state : (E × F) × F) (hg' : state ∈ good (recoveryStages L μ))
      (hc' : state ∈ cert (recoveryStages L μ-1)) : state.1 ∉ bad := by
    have hh := recovery_terminal_joint_gap H hζ center root initialBound state hg' hc'
    change ¬ζ < proxObj (maxValue f) L center state.1.1-dual f L center state.1.2
    exact not_lt.mpr (hh.trans (by linarith))
  have hg : Measurable (Function.uncurry (fun z ω => (ox z ω,oy z ω))) := hox.prodMk hoy
  have hh := executed_recovery_probability Pnoise hg p σ L μ ζ initialBound δ hδ.le center initial
    good cert hgood hcert hinit bad hbad hterminal
  apply hh
  intro j state hs
  exact recovery_stage_success_probability H hsc Pnoise ox oy hox hoy hxi hyi hxm hym hp hp2 hσ hpi hpV
    hζ hδ hδ1 center initialBound root (fun k b => hzero k b) j state hs

end LongTails.Proofs.HeavyTailSaddleEpoch
