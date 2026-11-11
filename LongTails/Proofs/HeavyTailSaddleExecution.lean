import LongTails.Algorithms.HeavyTailSaddleEstimator
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.StochasticEnvelopeExecution
import LongTails.Proofs.HeavyTailedProductProcess
import LongTails.Proofs.HeavyTailSaddleMultilevel

open scoped RealInnerProductSpace

open MeasureTheory OracleTemplate
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient
open LongTails.Algorithms.HeavyTailSaddleEstimator
open LongTails.Proofs.RecursiveEnvelopeExecution

namespace LongTails.Proofs.HeavyTailSaddleExecution

variable {E F : Type} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

omit [Module ℝ F] in
lemma fast_steps_prefix (h : ℕ) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (g : ℕ → E × F → E × F) (u : ℕ → E)
    (hu0 : u 0 = start)
    (hu : ∀ k < h, u (k + 1) = u k - η • (g k (u k, dual) + correction (u k, dual)).1)
    (k : ℕ) (hk : k ≤ h) :
    advance (fun i s => (fastSteps h η start dual correction).update s (g i (s.2.1, dual)))
      k 0 (0, start, 0) = (k, u k, 0) := by
  dsimp only [fastSteps]
  induction k with
  | zero => simp [advance, hu0]
  | succ k ih =>
    have hkh : k < h := by omega
    rw [advance_add, ih (by omega)]
    simp [advance, hkh, hu k hkh]

omit [Module ℝ F] in
lemma fast_steps_output (h : ℕ) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (g : ℕ → E × F → E × F) (u : ℕ → E)
    (hu0 : u 0 = start)
    (hu : ∀ k < h, u (k + 1) = u k - η • (g k (u k, dual) + correction (u k, dual)).1) :
    (fastSteps h η start dual correction).output
      (advance (fun i s => (fastSteps h η start dual correction).update s (g i (s.2.1, dual)))
        (h + 1) 0 (0, start, 0)) = -(g h (u h, dual) + correction (u h, dual)).2 := by
  erw [advance_add, fast_steps_prefix h η start dual correction g u hu0 hu h le_rfl]
  simp [advance, fastSteps]

lemma execute_fast_level {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h n : ℕ) (hn : 0 < n) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (u : ℕ → E) (hu0 : u 0 = start)
    (hu : ∀ k < h, u (k + 1) = u k - η •
      ((n : ℝ)⁻¹ • ∑ i : Fin n, g (u k, dual) (ξ (k * n + i.val)) +
        correction (u k, dual)).1) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => g z ω }
      (fastLevel h n hn η start dual correction) (fun _ => (h + 1) * n) () ξ =
      -((n : ℝ)⁻¹ • ∑ i : Fin n, g (u h, dual) (ξ (h * n + i.val)) +
        correction (u h, dual)).2 := by
  unfold fastLevel
  erw [execute_batched]
  exact fast_steps_output h η start dual correction
    (fun k z => (n : ℝ)⁻¹ • ∑ i : Fin n, g z (ξ (k * n + i.val))) u hu0 hu

lemma execute_fast_level_trajectory {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h n : ℕ) (hn : 0 < n) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) :
    let step := fun (x : E) (ζ : Fin n → Ω) => x - η •
      ((n : ℝ)⁻¹ • ∑ i : Fin n, g (x, dual) (ζ i) + correction (x, dual)).1
    let u := HeavyTailedProductProcess.trajectory step h start
      (fun k (i : Fin n) => ξ (k * n + i.val))
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => g z ω }
      (fastLevel h n hn η start dual correction) (fun _ => (h + 1) * n) () ξ =
      -((n : ℝ)⁻¹ • ∑ i : Fin n, g (u, dual) (ξ (h * n + i.val)) +
        correction (u, dual)).2 := by
  intro step u
  apply execute_fast_level P g ξ h n hn η start dual correction
    (fun k => HeavyTailedProductProcess.trajectory step k start
      (fun k (i : Fin n) => ξ (k * n + i.val))) rfl
  intro k hk
  rw [HeavyTailedProductProcess.trajectory_succ_last]

lemma batch_add_const {X : Type*} [AddCommGroup X] [Module ℝ X]
    (n : ℕ) (hn : 0 < n) (v : Fin n → X) (c : X) :
    (n : ℝ)⁻¹ • ∑ i : Fin n, (v i + c) = (n : ℝ)⁻¹ • ∑ i : Fin n, v i + c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_add_distrib, smul_add]
  simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn0]

lemma execute_fast_level_corrected {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h n : ℕ) (hn : 0 < n) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) :
    let a := fun x ω => (g (x, dual) ω + correction (x, dual)).1
    let b := fun x ω => -(g (x, dual) ω + correction (x, dual)).2
    let step := fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i))
    let u := HeavyTailedProductProcess.trajectory step h start
      (fun k (i : Fin n) => ξ (k * n + i.val))
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => g z ω }
      (fastLevel h n hn η start dual correction) (fun _ => (h + 1) * n) () ξ =
        (n : ℝ)⁻¹ • ∑ i : Fin n, b u (ξ (h * n + i.val)) := by
  intro a b step u
  have hfst (x : E) (ζ : Fin n → Ω) :
      ((n : ℝ)⁻¹ • ∑ i : Fin n, g (x, dual) (ζ i) + correction (x, dual)).1 =
        (n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i) := by
    rw [← batch_add_const n hn]
    simp only [Prod.smul_fst, Prod.fst_sum]
    rfl
  have hsnd (x : E) (ζ : Fin n → Ω) :
      -((n : ℝ)⁻¹ • ∑ i : Fin n, g (x, dual) (ζ i) + correction (x, dual)).2 =
        (n : ℝ)⁻¹ • ∑ i : Fin n, b x (ζ i) := by
    rw [← batch_add_const n hn]
    simp only [Prod.smul_snd, Prod.snd_sum, b, Finset.sum_neg_distrib, smul_neg]
  have hh := execute_fast_level_trajectory P g ξ h n hn η start dual correction
  dsimp only at hh
  simp_rw [hfst, hsnd] at hh
  exact hh

lemma execute_primal_level_corrected {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h n : ℕ) (hn : 0 < n) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) :
    let a := fun x ω => (g (x, dual) ω + correction (x, dual)).1
    let step := fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i))
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => g z ω }
      (primalLevel n hn η start dual correction) (fun _ => h * n) () ξ =
      HeavyTailedProductProcess.trajectory step h start
        (fun k (i : Fin n) => ξ (k * n + i.val)) := by
  intro a step
  have hfst (x : E) (ζ : Fin n → Ω) :
      ((n : ℝ)⁻¹ • ∑ i : Fin n, g (x, dual) (ζ i) + correction (x, dual)).1 =
        (n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i) := by
    rw [← batch_add_const n hn]
    simp only [Prod.smul_fst, Prod.fst_sum]
    rfl
  unfold primalLevel
  erw [execute_batched]
  change advance (fun k x => x - η •
      ((n : ℝ)⁻¹ • ∑ i : Fin n, g (x, dual) (ξ (k * n + i.val)) + correction (x, dual)).1)
      h 0 start = _
  simp_rw [hfst]
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [advance_add, HeavyTailedProductProcess.trajectory_succ_last]
    simpa only [advance, Nat.add_zero, Nat.zero_add, step] using congrArg
      (fun x => step x (fun i : Fin n => ξ (h * n + i.val))) ih

lemma coupled_trajectory_fst {X Y Ω : Type*} (A : X → Ω → X) (T : Y → Y)
    (n : ℕ) (x : X) (y : Y) (ξ : ℕ → Ω) :
    (HeavyTailedProductProcess.trajectory
      (fun (z : X × Y) ω => (A z.1 ω, T z.2)) n (x, y) ξ).1 =
      HeavyTailedProductProcess.trajectory A n x ξ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last,
        HeavyTailedProductProcess.trajectory_succ_last]
      exact congrArg (fun z => A z (ξ n)) ih

lemma coupled_trajectory_snd {X Y Ω : Type*} (A : X → Ω → X) (T : Y → Y)
    (n : ℕ) (x : X) (y : Y) (ξ : ℕ → Ω) :
    (HeavyTailedProductProcess.trajectory
      (fun (z : X × Y) ω => (A z.1 ω, T z.2)) n (x, y) ξ).2 = T^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last]
      change T _ = T^[n + 1] y
      rw [ih, Function.iterate_succ_apply']

lemma trajectory_prefix_congr {S Ω : Type*} (step : S → Ω → S)
    (n : ℕ) (s : S) (ξ ζ : ℕ → Ω) (h : ∀ k < n, ξ k = ζ k) :
    HeavyTailedProductProcess.trajectory step n s ξ =
      HeavyTailedProductProcess.trajectory step n s ζ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last,
        HeavyTailedProductProcess.trajectory_succ_last,
        ih (fun k hk => h k (by omega)), h n (by omega)]

lemma trajectory_next_law {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) p P) {step : S → Ω → S}
    (hs : Measurable (Function.uncurry step)) (n : ℕ) (s : S) :
    MeasurePreserving (fun ξ => (HeavyTailedProductProcess.trajectory step n s ξ, ξ n))
      P ((P.map (HeavyTailedProductProcess.trajectory step n s)).prod p) := by
  classical
  let pad : Ω := Classical.choice (nonempty_of_isProbabilityMeasure p)
  let extend := fun (v : Fin n → Ω) (k : ℕ) => if h : k < n then v ⟨k, h⟩ else pad
  have hext : Measurable extend := by
    apply Measurable.of_eval
    intro k
    dsimp [extend]
    split_ifs <;> fun_prop
  let F := fun v => HeavyTailedProductProcess.trajectory step n s (extend v)
  have hF : Measurable F :=
    (HeavyTailedProductProcess.trajectory_measurable hs n).comp
      (measurable_const.prodMk hext)
  have heq (ξ : ℕ → Ω) : F (fun i : Fin n => ξ i) =
      HeavyTailedProductProcess.trajectory step n s ξ := by
    apply trajectory_prefix_congr
    intro k hk
    simp [extend, hk]
  have hind : ProbabilityTheory.IndepFun (HeavyTailedProductProcess.trajectory step n s)
      (fun ξ : ℕ → Ω => ξ n) P := by
    have hh := (hIID.prefix_tail_independent n).comp hF (measurable_pi_apply 0)
    simpa only [Function.comp_def, heq, Nat.add_zero] using hh
  have ht : Measurable (HeavyTailedProductProcess.trajectory step n s) :=
    (HeavyTailedProductProcess.trajectory_measurable hs n).comp
      (measurable_const.prodMk measurable_id)
  refine ⟨ht.prodMk (measurable_pi_apply n), ?_⟩
  rw [hind.map_prod_eq_prod_map_map ht.aemeasurable
    (measurable_pi_apply n).aemeasurable, hIID.marginal n]

lemma trajectory_reply_moment {X Y Ω : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [MeasurableSpace Ω]
    (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P) {step : X → Ω → X}
    (hs : Measurable (Function.uncurry step)) (n : ℕ) (start u : X)
    {field : X → Y} {oracle : X → Ω → Y}
    (ho : Measurable (Function.uncurry oracle))
    {L p V W : ℝ} (hL : 0 ≤ L) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hl : ∀ x, ‖field x - field u‖ ≤ L * ‖x - u‖)
    (hoi : ∀ x, Integrable (oracle x) pnoise)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - field x‖ ^ p) pnoise)
    (homean : ∀ x, ∫ ω, oracle x ω ∂pnoise = field x)
    (hoV : ∀ x, (∫ ω, ‖oracle x ω - field x‖ ^ p ∂pnoise) ≤ V)
    (hXi : Integrable (fun ξ =>
      ‖HeavyTailedProductProcess.trajectory step n start ξ - u‖ ^ p) P)
    (hXW : (∫ ξ, ‖HeavyTailedProductProcess.trajectory step n start ξ - u‖ ^ p ∂P) ≤ W) :
    let error := fun ξ =>
      ‖oracle (HeavyTailedProductProcess.trajectory step n start ξ) (ξ n) - field u‖ ^ p
    Integrable error P ∧ (∫ ξ, error ξ ∂P) ≤ L ^ p * W + 6 * V := by
  intro error
  let U := HeavyTailedProductProcess.trajectory step n start
  have hU : Measurable U := (HeavyTailedProductProcess.trajectory_measurable hs n).comp
    (measurable_const.prodMk measurable_id)
  let μ := P.map U
  let : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr inferInstance
  have hmap : MeasurePreserving U P μ := ⟨hU, rfl⟩
  have hmoment : Measurable (fun x : X => ‖x - u‖ ^ p) := by fun_prop
  have hi : Integrable (fun x : X => ‖x - u‖ ^ p) μ :=
    (hmap.integrable_comp hmoment.aestronglyMeasurable).mp hXi
  have hW : (∫ x, ‖x - u‖ ^ p ∂μ) ≤ W := by
    rw [← hmap.map_eq, integral_map_of_stronglyMeasurable hU hmoment.stronglyMeasurable]
    exact hXW
  have h := HeavyTailSaddleMultilevel.fresh_output_moment pnoise μ ho measurable_id
    hL hp hp2 hl hoi hop homean hoV hi hW
  have hpair := trajectory_next_law pnoise P hIID hs n start
  have he : Measurable (fun z : X × Ω => ‖oracle z.1 z.2 - field u‖ ^ p) :=
    (ho.sub measurable_const).norm.pow_const p
  refine ⟨hpair.integrable_comp_of_integrable h.1, ?_⟩
  have heq := integral_map_of_stronglyMeasurable (μ := P) hpair.measurable he.stronglyMeasurable
  rw [hpair.map_eq] at heq
  exact heq.symm.trans_le h.2

lemma fast_reply_moment {X Y Ω : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P)
    {field : X → X} {dual : X → Y} {a : X → Ω → X} {b : X → Ω → Y}
    (hf : Measurable field) (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {L p V : ℝ}
    (hL : 0 < L) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hV : 0 ≤ V)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ inner ℝ (field x - field y) (x - y))
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ x y, ‖dual x - dual y‖ ≤ L * ‖x - y‖)
    (hai : ∀ x, Integrable (a x) pnoise) (hbi : ∀ x, Integrable (b x) pnoise)
    (hap : ∀ x, Integrable (fun ω => ‖a x ω - field x‖ ^ p) pnoise)
    (hbp : ∀ x, Integrable (fun ω => ‖b x ω - dual x‖ ^ p) pnoise)
    (ham : ∀ x, ∫ ω, a x ω ∂pnoise = field x)
    (hbm : ∀ x, ∫ ω, b x ω ∂pnoise = dual x)
    (haV : ∀ x, (∫ ω, ‖a x ω - field x‖ ^ p ∂pnoise) ≤ V)
    (hbV : ∀ x, (∫ ω, ‖b x ω - dual x‖ ^ p ∂pnoise) ≤ V)
    (batch : ℕ) (hbatch : 0 < batch) (h : ℕ) (start : X) :
    let η := 1 / (4 * L)
    let A := fun x (ζ : Fin batch → Ω) => (batch : ℝ)⁻¹ • ∑ i : Fin batch, a x (ζ i)
    let B := fun x (ζ : Fin batch → Ω) => (batch : ℝ)⁻¹ • ∑ i : Fin batch, b x (ζ i)
    let step := fun x ζ => x - η • A x ζ
    let T := fun x => x - η • field x
    let error := fun ξ : ℕ → Ω =>
      let blocks := fun k (i : Fin batch) => ξ (k * batch + i.val)
      ‖B (HeavyTailedProductProcess.trajectory step h start blocks) (blocks h) -
        dual (T^[h] start)‖ ^ p
    Integrable error P ∧ (∫ ξ, error ξ ∂P) ≤ 324 * V / (batch : ℝ) ^ (p - 1) := by
  intro η A B step T error
  let Q := Measure.pi fun _ : Fin batch => pnoise
  let R := Measure.infinitePi fun _ : ℕ => Q
  let v := 6 * V / (batch : ℝ) ^ (p - 1)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA (x : X) := HeavyTailSaddleMultilevel.finite_batch_oracle_properties pnoise
    (ha.comp (measurable_const.prodMk measurable_id)) hp hp2
    (hai x) (ham x) (hap x) (haV x) batch hbatch
  have hB (x : X) := HeavyTailSaddleMultilevel.finite_batch_oracle_properties pnoise
    (hb.comp (measurable_const.prodMk measurable_id)) hp hp2
    (hbi x) (hbm x) (hbp x) (hbV x) batch hbatch
  have hAm : Measurable (Function.uncurry A) := by dsimp [A, Function.uncurry]; fun_prop
  have hBm : Measurable (Function.uncurry B) := by dsimp [B, Function.uncurry]; fun_prop
  have hs : Measurable (Function.uncurry step) := by dsimp [step]; fun_prop
  have hcouple := HeavyTailSaddleMultilevel.coupled_gradient_moment Q hf hAm hL hp hp2 hv hm hl
    (fun x => (hA x).1) (fun x => (hA x).2.2.1)
    (fun x => (hA x).2.1) (fun x => (hA x).2.2.2) h start
  let C := fun ξ : ℕ → Fin batch → Ω =>
      ‖(HeavyTailedProductProcess.trajectory (fun (z : X × X) ζ => (step z.1 ζ, T z.2))
        h (start, start) ξ).1 -
        (HeavyTailedProductProcess.trajectory (fun (z : X × X) ζ => (step z.1 ζ, T z.2))
          h (start, start) ξ).2‖ ^ p
  change Integrable C R ∧ (∫ ξ, C ξ ∂R) ≤ 192 * η ^ p * v at hcouple
  dsimp [C] at hcouple
  simp_rw [coupled_trajectory_fst, coupled_trajectory_snd] at hcouple
  have hout := trajectory_reply_moment Q R
    (OracleTemplate.StochasticGeneralized.infinitePi_iid Q) hs h start (T^[h] start)
    hBm hL.le hp hp2 (fun x => hdl x _) (fun x => (hB x).1)
    (fun x => (hB x).2.2.1) (fun x => (hB x).2.1) (fun x => (hB x).2.2.2)
    hcouple.1 hcouple.2
  have hconst : L ^ p * (192 * η ^ p * v) + 6 * v ≤ 324 * V / (batch : ℝ) ^ (p - 1) := by
    have he : L * η = (1 / 4 : ℝ) := by dsimp [η]; field_simp
    have hpw : L ^ p * η ^ p ≤ (1 / 4 : ℝ) := by
      rw [← Real.mul_rpow hL.le hη, he]
      exact Real.rpow_le_self_of_le_one (by norm_num) (by norm_num) hp
    have hh := mul_le_mul_of_nonneg_right hpw hv
    calc
      _ ≤ 54 * v := by nlinarith
      _ = _ := by dsimp [v]; ring
  have ht : Measurable (fun ξ : ℕ → Fin batch → Ω =>
      HeavyTailedProductProcess.trajectory step h start ξ) :=
    (HeavyTailedProductProcess.trajectory_measurable hs h).comp
      (measurable_const.prodMk measurable_id)
  have he : Measurable (fun ξ : ℕ → Fin batch → Ω =>
      ‖B (HeavyTailedProductProcess.trajectory step h start ξ) (ξ h) - dual (T^[h] start)‖ ^ p) :=
    ((hBm.comp (ht.prodMk (measurable_pi_apply h))).sub measurable_const).norm.pow_const p
  have hblocks := OracleTemplate.FiniteVariance.infinite_block_law pnoise P
    hIID.independent hIID.marginal batch
  refine ⟨hblocks.integrable_comp_of_integrable hout.1, ?_⟩
  have heq := integral_map_of_stronglyMeasurable (μ := P) hblocks.measurable he.stronglyMeasurable
  rw [hblocks.map_eq] at heq
  exact heq.symm.trans_le (hout.2.trans hconst)

lemma iid_stream_shift {Ω : Type*} [MeasurableSpace Ω]
    {pnoise : Measure Ω} {P : Measure (ℕ → Ω)}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P) (offset : ℕ) :
    MeasurePreserving (fun ξ k => ξ (offset + k)) P P := by
  have hshift : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ (offset + k)) pnoise P :=
    ⟨fun k => hIID.measurable (offset + k),
      hIID.independent.precomp (fun _ _ h => Nat.add_left_cancel h),
      fun k => hIID.marginal (offset + k)⟩
  have he : P = Measure.infinitePi (fun _ : ℕ => pnoise) := by
    have hh := hIID.stream_law.map_eq
    change P.map id = _ at hh
    simpa only [Measure.map_id] using hh
  simpa only [← he] using hshift.stream_law

lemma offset_reply_mean {Ω Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {pnoise : Measure Ω} (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P) (family : ℕ → (ℕ → Ω) → Y)
    (hf : ∀ k, Measurable (family k)) (hi : ∀ k, Integrable (family k) P)
    (J baseOffset : ℕ) (fineOffset coarseOffset : Fin (J + 1) → ℕ) :
    let R := fun z : Fin (J + 1) × (ℕ → Ω) =>
      reply (family 0 (fun k => z.2 (baseOffset + k)))
        (fun j => family (j.val + 1) (fun k => z.2 (fineOffset j + k)))
        (fun j => family j.val (fun k => z.2 (coarseOffset j + k))) z.1
    Integrable R ((levelLaw J : Measure _).prod P) ∧
      (∫ z, R z ∂(levelLaw J : Measure _).prod P) = ∫ ξ, family (J + 1) ξ ∂P := by
  intro R
  have hshift (k n : ℕ) :
      Integrable (fun ξ => family k (fun i => ξ (n + i))) P ∧
        (∫ ξ, family k (fun i => ξ (n + i)) ∂P) = ∫ ξ, family k ξ ∂P := by
    have hs := iid_stream_shift hIID n
    refine ⟨hs.integrable_comp_of_integrable (hi k), ?_⟩
    have he := integral_map_of_stronglyMeasurable (μ := P) hs.measurable (hf k).stronglyMeasurable
    rw [hs.map_eq] at he
    exact he.symm
  apply HeavyTailSaddleMultilevel.random_reply_mean P
    (base := fun ξ => family 0 (fun k => ξ (baseOffset + k)))
    (fine := fun j ξ => family (j.val + 1) (fun k => ξ (fineOffset j + k)))
    (coarse := fun j ξ => family j.val (fun k => ξ (coarseOffset j + k)))
    ((hf 0).comp (iid_stream_shift hIID baseOffset).measurable)
    (measurable_from_prod_countable_right (fun j =>
      (hf (j.val + 1)).comp (iid_stream_shift hIID (fineOffset j)).measurable))
    (measurable_from_prod_countable_right (fun j =>
      (hf j.val).comp (iid_stream_shift hIID (coarseOffset j)).measurable))
    (hshift 0 baseOffset).1 (fun j => (hshift (j.val + 1) (fineOffset j)).1)
    (fun j => (hshift j.val (coarseOffset j)).1)
    (fun k : Fin (J + 2) => ∫ ξ, family k.val ξ ∂P)
    (hshift 0 baseOffset).2 (fun j => (hshift (j.val + 1) (fineOffset j)).2)
    (fun j => (hshift j.val (coarseOffset j)).2)

lemma eval_algorithm_plan {Q R U : Type} (A : Algorithm Q R U)
    (raw : ℕ → Q → R) (k call : ℕ) (s : A.State) :
    evalAt raw (algorithmPlan A k s) call =
      A.output (advance (fun i z => A.update z (raw i (A.query z).2)) k call s) := by
  induction k generalizing call s with
  | zero => rfl
  | succ k ih => exact ih (call + 1) _

lemma eval_estimator_plan (raw : ℕ → E × F → E × F) (h : ℕ) {J : ℕ}
    (j : Fin (J + 1)) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (call : ℕ) :
    evalAt raw (estimatorPlan h j η start dual correction) call =
      evalAt raw (fastPlan h 0 η start dual correction) call + (levelWeight J j)⁻¹ •
        (evalAt raw (fastPlan h (j.val + 1) η start dual correction) (call + levelCalls h 0) -
          evalAt raw (fastPlan h j.val η start dual correction)
            (call + levelCalls h 0 + levelCalls h (j.val + 1))) := by
  simp only [estimatorPlan, StochasticEnvelopeExecution.evalAt_castPlan, evalAt_bind, evalAt_map]

lemma eval_sum_estimator_plan (raw : ℕ → E × F → E × F) (h : ℕ) {J : ℕ}
    (levels : ℕ → Fin (J + 1)) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (n call : ℕ) :
    evalAt raw (sumEstimatorPlan h levels η start dual correction n) call =
      ∑ i ∈ Finset.range n,
        evalAt raw (estimatorPlan h (levels i) η start dual correction)
          (call + batchCalls h levels i) := by
  induction n with
  | zero => simp [sumEstimatorPlan, evalAt]
  | succ n ih =>
    simp only [sumEstimatorPlan, StochasticEnvelopeExecution.evalAt_castPlan,
      evalAt_bind, evalAt_map, ih, Finset.sum_range_succ]

lemma eval_clipped_batch_plan {X Y : Type} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (raw : ℕ → X × Y → X × Y) (h n : ℕ) {J : ℕ}
    (levels : ℕ → Fin (J + 1)) (η C : ℝ) (start : X) (dual : Y)
    (correction : X × Y → X × Y) (call : ℕ) :
    evalAt raw (clippedBatchPlan h n levels η C start dual correction) call =
      OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        evalAt raw (estimatorPlan h (levels i) η start dual correction)
          (call + batchCalls h levels i)) := by
  rw [clippedBatchPlan, evalAt_map, eval_sum_estimator_plan]

lemma eval_primal_replicas_plan (raw : ℕ → E × F → E × F) (h n : ℕ) (hn : 0 < n)
    (η : ℝ) (start : E) (dual : F) (correction : E × F → E × F) (M call : ℕ) :
    evalAt raw (primalReplicasPlan h n hn η start dual correction M) call =
      fun i : Fin M => evalAt raw (primalPlan h n hn η start dual correction)
        (call + h * n * i.val) := by
  exact StochasticEnvelopeExecution.evalAt_collectPlans raw M
    (fun _ => primalPlan h n hn η start dual correction) call

lemma eval_refresh_plan {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (raw : ℕ → X × Y → X × Y) (h n M : ℕ) (hn : 0 < n) (η R : ℝ)
    (start : X) (dual : Y) (correction : X × Y → X × Y) (call : ℕ) :
    evalAt raw (refreshPlan h n M hn η R start dual correction) call =
      OracleTemplate.RobustGradient.pilotCenter (R / 8)
        (fun i : Fin M => evalAt raw (primalPlan h n hn η start dual correction)
          (call + h * n * i.val)) := by
  rw [refreshPlan, evalAt_map, eval_primal_replicas_plan]

lemma eval_primal_plan_corrected {E F Ω : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [MeasurableSpace Ω]
    (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h n : ℕ) (hn : 0 < n) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (call : ℕ) :
    let a := fun x ω => (g (x, dual) ω + correction (x, dual)).1
    let step := fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i))
    evalAt (fun j x => g x (ξ j)) (primalPlan h n hn η start dual correction) call =
      LongTails.Proofs.HeavyTailedProductProcess.trajectory step h start
        (fun k (i : Fin n) => ξ (call + (k * n + i.val))) := by
  intro a step
  let ζ := fun j => ξ (call + j)
  let P : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.dirac ζ, inferInstance⟩
  let O : Oracle (E × F) (E × F) :=
    { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => g z ω }
  let A := primalLevel n hn η start dual correction
  have hh := execute_primal_level_corrected P g ζ h n hn η start dual correction
  dsimp only at hh
  erw [execute_advance_of_answer O A (h * n) () ζ
    (fun k q => g q.2 (ζ k)) (by intros; rfl)] at hh
  have he := LongTails.Proofs.StochasticEnvelopeExecution.evalAt_shift (fun j x => g x (ξ j)) (primalPlan h n hn η start dual correction) call 0
  simp only [Nat.add_zero] at he
  rw [← he, primalPlan, eval_algorithm_plan]
  exact hh
lemma eval_refresh_plan_corrected {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [MeasurableSpace Ω]
    (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h n M : ℕ) (hn : 0 < n) (η R : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (call : ℕ) :
    let a := fun x ω => (g (x, dual) ω + correction (x, dual)).1
    let step := fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i))
    evalAt (fun j x => g x (ξ j)) (refreshPlan h n M hn η R start dual correction) call =
      OracleTemplate.RobustGradient.pilotCenter (R / 8) (fun i : Fin M =>
        LongTails.Proofs.HeavyTailedProductProcess.trajectory step h start
          (fun k (j : Fin n) => ξ (call + h * n * i.val + (k * n + j.val)))) := by
  intro a step
  rw [eval_refresh_plan]
  congr 1
  funext i
  exact eval_primal_plan_corrected g ξ h n hn η start dual correction _

lemma parameter_trajectory_measurable {A E Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace E] [MeasurableSpace Ω]
    {step : A → E → Ω → E}
    (hs : Measurable (fun w : (A × E) × Ω => step w.1.1 w.1.2 w.2)) (n : ℕ) :
    Measurable (fun w : A × (E × (ℕ → Ω)) =>
      HeavyTailedProductProcess.trajectory (step w.1) n w.2.1 w.2.2) := by
  induction n with
  | zero => exact measurable_snd.fst
  | succ n ih =>
      simp_rw [HeavyTailedProductProcess.trajectory_succ_last]
      exact hs.comp ((measurable_fst.prodMk ih).prodMk
        ((measurable_pi_apply n).comp measurable_snd.snd))

lemma batched_endpoint_measurable {A E Ω : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {oracle : A → E → Ω → E}
    (ho : Measurable (fun w : (A × E) × Ω => oracle w.1.1 w.1.2 w.2))
    {start : A → E} (hx : Measurable start) (η : ℝ) (h n : ℕ) :
    Measurable (fun w : A × (ℕ → Ω) =>
      HeavyTailedProductProcess.trajectory
        (fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i, oracle w.1 x (ζ i)))
        h (start w.1) (fun k (i : Fin n) => w.2 (k * n + i.val))) := by
  have hs : Measurable (fun w : (A × E) × (Fin n → Ω) =>
      w.1.2 - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, oracle w.1.1 w.1.2 (w.2 i))) := by
    apply Measurable.sub measurable_fst.snd
    apply Measurable.const_smul
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i hi
    exact ho.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have ht := parameter_trajectory_measurable
    (step := fun a x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i, oracle a x (ζ i))) hs h
  exact ht.comp (measurable_fst.prodMk ((hx.comp measurable_fst).prodMk (by fun_prop)))
lemma batched_reply_measurable {A E F Ω : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {oracle : A → E → Ω → E} {dual : A → E → Ω → F}
    (ho : Measurable (fun w : (A × E) × Ω => oracle w.1.1 w.1.2 w.2))
    (hd : Measurable (fun w : (A × E) × Ω => dual w.1.1 w.1.2 w.2))
    {start : A → E} (hx : Measurable start) (η : ℝ) (h n : ℕ) :
    Measurable (fun w : A × (ℕ → Ω) =>
      let endpoint := HeavyTailedProductProcess.trajectory
        (fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i, oracle w.1 x (ζ i)))
        h (start w.1) (fun k (i : Fin n) => w.2 (k * n + i.val))
      (n : ℝ)⁻¹ • ∑ i : Fin n, dual w.1 endpoint (w.2 (h * n + i.val))) := by
  have ht := batched_endpoint_measurable (oracle := oracle) ho hx η h n
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i hi
  exact hd.comp ((measurable_fst.prodMk ht).prodMk
    ((measurable_pi_apply (h * n + i.val)).comp measurable_snd))

lemma eval_fast_plan_corrected {E F Ω : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [MeasurableSpace Ω]
    (g : E × F → Ω → E × F) (ξ : ℕ → Ω)
    (h level : ℕ) (η : ℝ) (start : E) (dual : F)
    (correction : E × F → E × F) (call : ℕ) :
    let n := 2 ^ level
    let a := fun x ω => (g (x, dual) ω + correction (x, dual)).1
    let b := fun x ω => -(g (x, dual) ω + correction (x, dual)).2
    let step := fun x (ζ : Fin n → Ω) => x - η • ((n : ℝ)⁻¹ • ∑ i : Fin n, a x (ζ i))
    let endpoint := LongTails.Proofs.HeavyTailedProductProcess.trajectory step h start
      (fun k (i : Fin n) => ξ (call + (k * n + i.val)))
    evalAt (fun j x => g x (ξ j)) (fastPlan h level η start dual correction) call =
      (n : ℝ)⁻¹ • ∑ i : Fin n, b endpoint (ξ (call + (h * n + i.val))) := by
  intro n a b step endpoint
  have hn : 0 < n := by dsimp [n]; positivity
  let ζ := fun j => ξ (call + j)
  let P : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.dirac ζ, inferInstance⟩
  let O : Oracle (E × F) (E × F) :=
    { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => g z ω }
  let A := fastLevel h n hn η start dual correction
  have hh := execute_fast_level_corrected P g ζ h n hn η start dual correction
  dsimp only at hh
  erw [execute_advance_of_answer O A ((h + 1) * n) () ζ
    (fun k q => g q.2 (ζ k)) (by intros; rfl)] at hh
  have he := LongTails.Proofs.StochasticEnvelopeExecution.evalAt_shift
    (fun j x => g x (ξ j)) (fastPlan h level η start dual correction) call 0
  simp only [Nat.add_zero] at he
  rw [← he, fastPlan, eval_algorithm_plan]
  exact hh
lemma fast_plan_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h level : ℕ) (η : ℝ) (call : ℕ) :
    Measurable (fun w : A × (ℕ → Ω) =>
      evalAt (fun j x => g x (w.2 j))
        (fastPlan h level η (start w.1) (dual w.1) (correction w.1)) call) := by
  let c := fun a x ω => g (x, dual a) ω + correction a (x, dual a)
  have hcm : Measurable (fun w : (A × E) × Ω => c w.1.1 w.1.2 w.2) := by
    apply Measurable.add
    · exact hg.comp ((measurable_fst.snd.prodMk (hv.comp measurable_fst.fst)).prodMk measurable_snd)
    · exact hc.comp (measurable_fst.fst.prodMk
        (measurable_fst.snd.prodMk (hv.comp measurable_fst.fst)))
  have ht := batched_reply_measurable
    (oracle := fun a x ω => (c a x ω).1) (dual := fun a x ω => -(c a x ω).2)
    hcm.fst hcm.snd.neg hx η h (2 ^ level)
  have hs : Measurable (fun w : A × (ℕ → Ω) =>
      (w.1, fun j => w.2 (call + j))) := by fun_prop
  convert ht.comp hs using 1
  funext w
  exact eval_fast_plan_corrected g w.2 h level η (start w.1) (dual w.1) (correction w.1) call
lemma estimator_plan_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h : ℕ) {J : ℕ} (j : Fin (J + 1)) (η : ℝ) (call : ℕ) :
    Measurable (fun w : A × (ℕ → Ω) =>
      evalAt (fun k x => g x (w.2 k))
        (estimatorPlan h j η (start w.1) (dual w.1) (correction w.1)) call) := by
  have hb := fast_plan_measurable hg hx hv hc h 0 η call
  have hf := fast_plan_measurable hg hx hv hc h (j.val + 1) η (call + levelCalls h 0)
  have hco := fast_plan_measurable hg hx hv hc h j.val η
    (call + levelCalls h 0 + levelCalls h (j.val + 1))
  convert hb.add ((hf.sub hco).const_smul (levelWeight J j)⁻¹) using 1
  funext w
  exact eval_estimator_plan (fun k x => g x (w.2 k)) h j η
    (start w.1) (dual w.1) (correction w.1) call

lemma clipped_batch_plan_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h n : ℕ) {J : ℕ} (levels : ℕ → Fin (J + 1)) (η C : ℝ) (call : ℕ) :
    Measurable (fun w : A × (ℕ → Ω) =>
      evalAt (fun k x => g x (w.2 k))
        (clippedBatchPlan h n levels η C (start w.1) (dual w.1) (correction w.1)) call) := by
  simp_rw [eval_clipped_batch_plan]
  apply (OracleTemplate.measurable_clip (E := F) C).comp
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i hi
  exact estimator_plan_measurable hg hx hv hc h (levels i) η (call + batchCalls h levels i)


open StochasticEnvelopeExecution LongTails.Algorithms.StochasticEnvelopeProgram

lemma collected_substitution_law {S Ω Q R C D : Type}
    [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSpace R]
    (P : Measure S) (p : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    (cost : ℕ → S → ℕ) (hc : ∀ j, Measurable (cost j))
    (child : (j : ℕ) → (s : S) → Q → QueryPlan C D R (cost j s))
    (g : C → Ω → D)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) =>
      evalAt (fun i x => g x (w.2.2 i)) (child j w.2.1 w.1) 0)) (n : ℕ) (q : Q) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => fun i : Fin n =>
        evalAt (fun j x => g x (w.2 j)) (child i (w.1 i) q)
          (slotCalls (fun j => cost j (w.1 j)) i 0))
      (fun w : ℕ → S × (ℕ → Ω) => fun i : Fin n =>
        evalAt (fun j x => g x ((w i).2 j)) (child i (w i).1 q) 0)
      ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.infinitePi fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  let plan := fun q : Q => LongTails.Algorithms.StochasticEnvelopeProgram.collectPlans n (fun _ => QueryPlan.ask q (fun r : R => .done r))
  have hp : PlanFamily.MeasurableFamily (1 * n) plan := by
    apply PlanFamily.collect
    intro i
    exact PlanFamily.ask measurable_id (PlanFamily.done measurable_snd)
  have hd := PlanFamily.substituted_family_identDistrib P p cost hc child g hr hp q
  have hdep {α : ℕ → Type} (f : (j : ℕ) → α j) {i j : ℕ} (hij : i = j) : HEq (f i) (f j) := by
    cases hij
    rfl
  convert hd using 1
  · funext w
    have he := evalAt_substitutePlan (fun j x => g x (w.2 j))
      (fun j => cost j (w.1 j)) (fun j => child j (w.1 j)) (plan q) 0 0
    simp only [slotCalls, Nat.zero_add] at he
    rw [he]
    simp [plan, evalAt_collectPlans, evalAt]
    funext i
    congr 1 <;> try simp
    exact hdep (fun j => child j (w.1 j) q) (by omega)
  · funext w
    simp [plan, evalAt_collectPlans, evalAt]
    funext i
    congr 1 <;> try simp
    exact hdep (fun j => child j (w j).1 q) (by omega)
lemma iid_response_vector_law {Z R : Type} [MeasurableSpace Z] [MeasurableSpace R]
    (P : Measure Z) [IsProbabilityMeasure P] {n : ℕ} (response : Fin n → Z → R)
    (hr : ∀ i, Measurable (response i)) :
    ProbabilityTheory.IdentDistrib
      (fun w : ℕ → Z => fun i : Fin n => response i (w i))
      (fun w : Fin n → Z => fun i => response i (w i))
      (Measure.infinitePi fun _ : ℕ => P) (Measure.pi fun _ : Fin n => P) := by
  have hIID := OracleTemplate.StochasticGeneralized.infinitePi_iid P
  have hi := hIID.independent.precomp (g := fun i : Fin n => i.val) Fin.val_injective
  have hp : (Measure.infinitePi fun _ : ℕ => P).map (fun w : ℕ → Z => fun i : Fin n => w i) =
      Measure.pi (fun _ : Fin n => P) := by
    simpa only [hIID.marginal] using hi.map_fun_eq_pi_map
      (fun i : Fin n => (hIID.measurable i.val).aemeasurable)
  have hd : ProbabilityTheory.IdentDistrib
      (fun w : ℕ → Z => fun i : Fin n => w i) (id : (Fin n → Z) → (Fin n → Z))
      (Measure.infinitePi fun _ : ℕ => P) (Measure.pi fun _ : Fin n => P) :=
    ⟨(show Measurable (fun w : ℕ → Z => fun i : Fin n => w i) by fun_prop).aemeasurable,
      measurable_id.aemeasurable, by simpa using hp⟩
  have hm : Measurable (fun w : Fin n → Z => fun i => response i (w i)) :=
    Measurable.of_eval (fun i => (hr i).comp (measurable_pi_apply i))
  exact hd.comp hm
lemma collected_substitution_finite_law {S Ω Q R C D : Type}
    [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSpace R]
    (P : Measure S) (p : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    (cost : ℕ → S → ℕ) (hc : ∀ j, Measurable (cost j))
    (child : (j : ℕ) → (s : S) → Q → QueryPlan C D R (cost j s))
    (g : C → Ω → D)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) =>
      evalAt (fun i x => g x (w.2.2 i)) (child j w.2.1 w.1) 0)) (n : ℕ) (q : Q) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => fun i : Fin n =>
        evalAt (fun j x => g x (w.2 j)) (child i (w.1 i) q)
          (slotCalls (fun j => cost j (w.1 j)) i 0))
      (fun w : Fin n → S × (ℕ → Ω) => fun i : Fin n =>
        evalAt (fun j x => g x ((w i).2 j)) (child i (w i).1 q) 0)
      ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.pi fun _ : Fin n => P.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  have hr' (i : Fin n) : Measurable (fun w : S × (ℕ → Ω) =>
      evalAt (fun j x => g x (w.2 j)) (child i w.1 q) 0) :=
    (hr i).comp (measurable_const.prodMk measurable_id)
  exact (collected_substitution_law P p cost hc child g hr n q).trans
    (iid_response_vector_law (P.prod (Measure.infinitePi fun _ : ℕ => p))
      (fun i (w : S × (ℕ → Ω)) => evalAt (fun j x => g x (w.2 j)) (child i w.1 q) 0) hr')

lemma estimator_batch_law {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h J n : ℕ) (η : ℝ) (query : A) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → Fin (J + 1)) × (ℕ → Ω) => fun i : Fin n =>
        evalAt (fun k x => g x (w.2 k))
          (estimatorPlan h (w.1 i) η (start query) (dual query) (correction query))
          (batchCalls h w.1 i))
      (fun w : Fin n → Fin (J + 1) × (ℕ → Ω) => fun i =>
        evalAt (fun k x => g x ((w i).2 k))
          (estimatorPlan h (w i).1 η (start query) (dual query) (correction query)) 0)
      ((Measure.infinitePi fun _ : ℕ => (levelLaw J : Measure _)).prod
        (Measure.infinitePi fun _ : ℕ => p))
      (Measure.pi fun _ : Fin n => (levelLaw J : Measure _).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
  have hm : Measurable (fun w : Fin (J + 1) × (A × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (estimatorPlan h w.1 η (start w.2.1) (dual w.2.1) (correction w.2.1)) 0) :=
    measurable_from_prod_countable_right
      (fun j => estimator_plan_measurable hg hx hv hc h j η 0)
  have hr : Measurable (fun w : A × (Fin (J + 1) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (estimatorPlan h w.2.1 η (start w.1) (dual w.1) (correction w.1)) 0) :=
    hm.comp (by fun_prop : Measurable (fun w : A × (Fin (J + 1) × (ℕ → Ω)) =>
      (w.2.1, (w.1, w.2.2))))
  have hh := collected_substitution_finite_law (levelLaw J : Measure _) p
    (fun _ j => replyCalls h j) (fun _ => measurable_of_finite _)
    (fun _ j q => estimatorPlan h j η (start q) (dual q) (correction q)) g (fun _ => hr) n query
  simpa only [slotCalls_sum, Nat.zero_add, batchCalls] using hh

lemma clipped_batch_law {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h J n : ℕ) (η C : ℝ) (query : A) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → Fin (J + 1)) × (ℕ → Ω) =>
        evalAt (fun k x => g x (w.2 k))
          (clippedBatchPlan h n w.1 η C (start query) (dual query) (correction query)) 0)
      (fun w : Fin n → Fin (J + 1) × (ℕ → Ω) =>
        OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i : Fin n,
          evalAt (fun k x => g x ((w i).2 k))
            (estimatorPlan h (w i).1 η (start query) (dual query) (correction query)) 0))
      ((Measure.infinitePi fun _ : ℕ => (levelLaw J : Measure _)).prod
        (Measure.infinitePi fun _ : ℕ => p))
      (Measure.pi fun _ : Fin n => (levelLaw J : Measure _).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
  have hm : Measurable (fun v : Fin n → F => OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i, v i)) := by
    apply (OracleTemplate.measurable_clip (E := F) C).comp
    apply Measurable.const_smul
    exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hd := (estimator_batch_law p hg hx hv hc h J n η query).comp hm
  convert hd using 1
  · funext w
    rw [eval_clipped_batch_plan]
    simp only [Function.comp_def, Nat.zero_add]
    congr 2
    exact (Fin.sum_univ_eq_sum_range (fun i => evalAt (fun k x => g x (w.2 k))
      (estimatorPlan h (w.1 i) η (start query) (dual query) (correction query))
      (batchCalls h w.1 i)) n).symm
  · rfl


lemma offset_dyadic_reply_moments {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (pnoise : Measure Ω)
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P) (family : ℕ → (ℕ → Ω) → E)
    (hf : ∀ k, Measurable (family k)) (θ : E) {p B : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hB : 0 ≤ B)
    (hi : ∀ k, Integrable (fun ξ => ‖family k ξ - θ‖ ^ p) P)
    (hbound : ∀ k, (∫ ξ, ‖family k ξ - θ‖ ^ p ∂P) ≤ B / ((2 : ℝ) ^ k) ^ (p - 1))
    (J baseOffset : ℕ) (fineOffset coarseOffset : Fin (J + 1) → ℕ) :
    let Q := (levelLaw J : Measure _).prod P
    let R := fun z : Fin (J + 1) × (ℕ → Ω) =>
      reply (family 0 (fun k => z.2 (baseOffset + k)))
        (fun j => family (j.val + 1) (fun k => z.2 (fineOffset j + k)))
        (fun j => family j.val (fun k => z.2 (coarseOffset j + k))) z.1
    Integrable R Q ∧ Integrable (fun z => ‖R z - θ‖ ^ p) Q ∧
      (∫ z, ‖R z - θ‖ ^ p ∂Q) ≤ 18 * (J + 1) * B ∧
      Integrable (fun z => ‖R z - ∫ w, R w ∂Q‖ ^ p) Q ∧
      (∫ z, ‖R z - ∫ w, R w ∂Q‖ ^ p ∂Q) ≤ 72 * (J + 1) * B := by
  intro Q R
  have hshift (k offset : ℕ) :
      Integrable (fun ξ => ‖family k (fun j => ξ (offset + j)) - θ‖ ^ p) P ∧
      (∫ ξ, ‖family k (fun j => ξ (offset + j)) - θ‖ ^ p ∂P) ≤
        B / ((2 : ℝ) ^ k) ^ (p - 1) := by
    have hs := iid_stream_shift hIID offset
    have hm : Measurable (fun ξ => ‖family k ξ - θ‖ ^ p) :=
      ((hf k).sub measurable_const).norm.pow_const p
    have he := integral_map_of_stronglyMeasurable (μ := P) hs.measurable hm.stronglyMeasurable
    rw [hs.map_eq] at he
    exact ⟨hs.integrable_comp_of_integrable (hi k), he.symm.trans_le (hbound k)⟩
  apply HeavyTailSaddleMultilevel.dyadic_reply_moments P
    (base := fun ξ => family 0 (fun k => ξ (baseOffset + k)))
    (fine := fun j ξ => family (j.val + 1) (fun k => ξ (fineOffset j + k)))
    (coarse := fun j ξ => family j.val (fun k => ξ (coarseOffset j + k))) θ
    ((hf 0).comp (iid_stream_shift hIID baseOffset).measurable)
    (measurable_from_prod_countable_right (fun j : Fin (J + 1) =>
      (hf (j.val + 1)).comp (iid_stream_shift hIID (fineOffset j)).measurable))
    (measurable_from_prod_countable_right (fun j : Fin (J + 1) =>
      (hf j.val).comp (iid_stream_shift hIID (coarseOffset j)).measurable)) hp hp2 hB
    (hshift 0 baseOffset).1 (by simpa using (hshift 0 baseOffset).2)
    (fun j => (hshift (j.val + 1) (fineOffset j)).1)
    (fun j => (hshift j.val (coarseOffset j)).1)
    (fun j => ?_) (fun j => (hshift j.val (coarseOffset j)).2)
  apply (hshift (j.val + 1) (fineOffset j)).2.trans
  gcongr
  · norm_num
  · linarith

lemma batch_calls_prefix_congr (h n : ℕ) {J : ℕ} (v w : ℕ → Fin (J + 1))
    (heq : ∀ j < n, v j = w j) : batchCalls h v n = batchCalls h w n := by
  unfold batchCalls
  apply Finset.sum_congr rfl
  intro j hj
  rw [heq j (Finset.mem_range.mp hj)]

lemma clipped_batch_prefix_congr {E F : Type} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (raw : ℕ → E × F → E × F)
    (h n : ℕ) {J : ℕ} (v w : ℕ → Fin (J + 1))
    (η C : ℝ) (start : E) (dual : F) (correction : E × F → E × F) (call : ℕ)
    (heq : ∀ j < n, v j = w j) :
    evalAt raw (clippedBatchPlan h n v η C start dual correction) call =
      evalAt raw (clippedBatchPlan h n w η C start dual correction) call := by
  rw [eval_clipped_batch_plan, eval_clipped_batch_plan]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq i (Finset.mem_range.mp hi), batch_calls_prefix_congr h i v w
    (fun j hj => heq j (by have := Finset.mem_range.mp hi; omega))]

lemma extended_clipped_batch_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h n J : ℕ) (η C : ℝ) (call : ℕ) :
    Measurable (fun w : (Fin n → Fin (J + 1)) × (A × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (clippedBatchPlan h n (extendLevels w.1) η C (start w.2.1) (dual w.2.1)
          (correction w.2.1)) call) :=
  measurable_from_prod_countable_right
    (fun v => clipped_batch_plan_measurable hg hx hv hc h n (extendLevels v) η C call)
lemma finite_seed_prefix_law {S Ω R : Type} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace R] (P : Measure S) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n : ℕ)
    {F : (ℕ → S) × Ω → R} {f : (Fin n → S) × Ω → R} (hf : Measurable f)
    (heq : ∀ w, F w = f ((fun i : Fin n => w.1 i), w.2)) :
    ProbabilityTheory.IdentDistrib F f
      ((Measure.infinitePi fun _ : ℕ => P).prod Q) ((Measure.pi fun _ : Fin n => P).prod Q) := by
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid P
  have hi := hiid.independent.precomp (g := fun i : Fin n => i.val) Fin.val_injective
  have hp : MeasurePreserving (fun w : ℕ → S => fun i : Fin n => w i)
      (Measure.infinitePi fun _ : ℕ => P) (Measure.pi fun _ : Fin n => P) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [hiid.marginal] using hi.map_fun_eq_pi_map
      (fun i : Fin n => (hiid.measurable i.val).aemeasurable)
  have hprod := hp.prod (MeasurePreserving.id Q)
  have hd : ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × Ω => ((fun i : Fin n => w.1 i), w.2))
      (id : ((Fin n → S) × Ω) → ((Fin n → S) × Ω))
      ((Measure.infinitePi fun _ : ℕ => P).prod Q) ((Measure.pi fun _ : Fin n => P).prod Q) :=
    ⟨hprod.measurable.aemeasurable, measurable_id.aemeasurable, by
      rw [Measure.map_id]
      convert hprod.map_eq using 1
      congr 1⟩
  convert hd.comp hf using 1
  · exact funext heq
  · rfl

lemma finite_clipped_batch_law {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {start : A → E} {dual : A → F} {correction : A → E × F → E × F}
    (hx : Measurable start) (hv : Measurable dual)
    (hc : Measurable (Function.uncurry correction)) (h J n : ℕ) (η C : ℝ) (query : A) :
    ProbabilityTheory.IdentDistrib
      (fun w : (Fin n → Fin (J + 1)) × (ℕ → Ω) =>
        evalAt (fun k x => g x (w.2 k))
          (clippedBatchPlan h n (extendLevels w.1) η C
            (start query) (dual query) (correction query)) 0)
      (fun w : Fin n → Fin (J + 1) × (ℕ → Ω) =>
        OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i : Fin n,
          evalAt (fun k x => g x ((w i).2 k))
            (estimatorPlan h (w i).1 η (start query) (dual query) (correction query)) 0))
      ((Measure.pi fun _ : Fin n => (levelLaw J : Measure _)).prod
        (Measure.infinitePi fun _ : ℕ => p))
      (Measure.pi fun _ : Fin n => (levelLaw J : Measure _).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
  have hm := (extended_clipped_batch_measurable hg hx hv hc h n J η C 0).comp
    (show Measurable (fun w : (Fin n → Fin (J + 1)) × (ℕ → Ω) =>
      (w.1, (query, w.2))) by fun_prop)
  have hp := finite_seed_prefix_law (levelLaw J : Measure _)
    (Measure.infinitePi fun _ : ℕ => p) n
    (F := fun w => evalAt (fun k x => g x (w.2 k))
      (clippedBatchPlan h n w.1 η C (start query) (dual query) (correction query)) 0)
    hm (fun w => ?_)
  · exact hp.symm.trans (clipped_batch_law p hg hx hv hc h J n η C query)
  · apply clipped_batch_prefix_congr
    intro j hj
    simp [extendLevels, hj]


lemma offset_reply_properties {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (pnoise : Measure Ω)
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P) (family : ℕ → (ℕ → Ω) → E)
    (hf : ∀ k, Measurable (family k)) (θ : E) {p B : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hB : 0 ≤ B)
    (hi : ∀ k, Integrable (fun ξ => ‖family k ξ - θ‖ ^ p) P)
    (hbound : ∀ k, (∫ ξ, ‖family k ξ - θ‖ ^ p ∂P) ≤ B / ((2 : ℝ) ^ k) ^ (p - 1))
    (J baseOffset : ℕ) (fineOffset coarseOffset : Fin (J + 1) → ℕ) :
    let Q := (levelLaw J : Measure _).prod P
    let R := fun z : Fin (J + 1) × (ℕ → Ω) =>
      reply (family 0 (fun k => z.2 (baseOffset + k)))
        (fun j => family (j.val + 1) (fun k => z.2 (fineOffset j + k)))
        (fun j => family j.val (fun k => z.2 (coarseOffset j + k))) z.1
    Integrable R Q ∧
      ‖(∫ z, R z ∂Q) - θ‖ ≤ (B / ((2 : ℝ) ^ (J + 1)) ^ (p - 1)) ^ (1 / p) ∧
      Integrable (fun z => ‖R z - ∫ w, R w ∂Q‖ ^ p) Q ∧
      (∫ z, ‖R z - ∫ w, R w ∂Q‖ ^ p ∂Q) ≤ 72 * (J + 1) * B := by
  intro Q R
  have hfamily (k : ℕ) := HeavyTailSaddleMultilevel.moment_mean_bound P
    (hf k).aestronglyMeasurable θ hp (hi k) (hbound k)
  have hm := offset_reply_mean P hIID family hf (fun k => (hfamily k).1)
    J baseOffset fineOffset coarseOffset
  have hv := offset_dyadic_reply_moments pnoise P hIID family hf θ hp hp2 hB hi hbound
    J baseOffset fineOffset coarseOffset
  refine ⟨hm.1, ?_, hv.2.2.2⟩
  rw [hm.2]
  exact (hfamily (J + 1)).2

lemma actual_reply_properties {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) pnoise P)
    (g : E × F → Ω → E × F) (correction : E × F → E × F) (v : F)
    {field : E → E} {dual : E → F} {a : E → Ω → E} {b : E → Ω → F}
    (hga : ∀ x ω, (g (x, v) ω + correction (x, v)).1 = a x ω)
    (hgb : ∀ x ω, -(g (x, v) ω + correction (x, v)).2 = b x ω)
    (hf : Measurable field) (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field x - field y, x - y⟫)
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ x y, ‖dual x - dual y‖ ≤ L * ‖x - y‖)
    (hai : ∀ x, Integrable (a x) pnoise) (hbi : ∀ x, Integrable (b x) pnoise)
    (hap : ∀ x, Integrable (fun ω => ‖a x ω - field x‖ ^ p) pnoise)
    (hbp : ∀ x, Integrable (fun ω => ‖b x ω - dual x‖ ^ p) pnoise)
    (ham : ∀ x, ∫ ω, a x ω ∂pnoise = field x)
    (hbm : ∀ x, ∫ ω, b x ω ∂pnoise = dual x)
    (haV : ∀ x, (∫ ω, ‖a x ω - field x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ x, (∫ ω, ‖b x ω - dual x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (h J : ℕ) (start : E) :
    let θ := dual ((fun x => x - (1 / (4 * L)) • field x)^[h] start)
    let Q := (levelLaw J : Measure (Fin (J + 1))).prod P
    let R := fun z : Fin (J + 1) × (ℕ → Ω) =>
      evalAt (fun k x => g x (z.2 k)) (estimatorPlan h z.1 (1 / (4 * L)) start v correction) 0
    Integrable R Q ∧
      ‖(∫ z, R z ∂Q) - θ‖ ≤
        (324 * σ ^ p / ((2 : ℝ) ^ (J + 1)) ^ (p - 1)) ^ (1 / p) ∧
      Integrable (fun z => ‖R z - ∫ w, R w ∂Q‖ ^ p) Q ∧
      (∫ z, ‖R z - ∫ w, R w ∂Q‖ ^ p ∂Q) ≤ 23328 * (J + 1) * σ ^ p := by
  intro θ Q R
  let family := fun k (ξ : ℕ → Ω) =>
    let n := 2 ^ k
    let step := fun x (ζ : Fin n → Ω) => x - (1 / (4 * L)) • ((n : ℝ)⁻¹ • ∑ i, a x (ζ i))
    let u := HeavyTailedProductProcess.trajectory step h start (fun j (i : Fin n) => ξ (j * n + i.val))
    (n : ℝ)⁻¹ • ∑ i : Fin n, b u (ξ (h * n + i.val))
  have hfamily (k : ℕ) : Integrable (fun ξ => ‖family k ξ - θ‖ ^ p) P ∧
      (∫ ξ, ‖family k ξ - θ‖ ^ p ∂P) ≤ 324 * σ ^ p / ((2 : ℝ) ^ k) ^ (p - 1) := by
    have hh := fast_reply_moment pnoise P hIID hf ha hb hL hp.le hp2
      (Real.rpow_nonneg hσ p) hm hl hdl hai hbi hap hbp ham hbm haV hbV (2 ^ k) (by positivity) h start
    simpa only [family, θ, Nat.cast_pow, Nat.cast_ofNat] using hh
  have hfm (k : ℕ) : Measurable (family k) := by
    have ht := batched_reply_measurable (A := Unit)
      (oracle := fun _ => a) (dual := fun _ => b) (start := fun _ => start)
      (ha.comp (measurable_fst.snd.prodMk measurable_snd))
      (hb.comp (measurable_fst.snd.prodMk measurable_snd)) measurable_const (1 / (4 * L)) h (2 ^ k)
    exact ht.comp ((measurable_const (a := ())).prodMk measurable_id)
  have heval (k call : ℕ) (ξ : ℕ → Ω) :
      evalAt (fun j x => g x (ξ j)) (fastPlan h k (1 / (4 * L)) start v correction) call =
        family k (fun j => ξ (call + j)) := by
    have hh := eval_fast_plan_corrected g ξ h k (1 / (4 * L)) start v correction call
    dsimp only at hh
    simp_rw [hga, hgb] at hh
    exact hh
  let Rideal := fun z : Fin (J + 1) × (ℕ → Ω) =>
    reply (family 0 (fun k => z.2 (0 + k)))
      (fun j => family (j.val + 1) (fun k => z.2 (levelCalls h 0 + k)))
      (fun j => family j.val (fun k => z.2 (levelCalls h 0 + levelCalls h (j.val + 1) + k))) z.1
  have heq : R = Rideal := by
    funext z
    dsimp only [R, Rideal, reply]
    rw [eval_estimator_plan]
    simp only [heval, Nat.zero_add]
  have hh := offset_reply_properties pnoise P hIID family hfm θ hp hp2
    (show 0 ≤ 324 * σ ^ p by positivity) (fun k => (hfamily k).1) (fun k => (hfamily k).2)
    J 0 (fun _ => levelCalls h 0) (fun j => levelCalls h 0 + levelCalls h (j.val + 1))
  change Integrable Rideal Q ∧
    ‖(∫ z, Rideal z ∂Q) - θ‖ ≤ (324 * σ ^ p / ((2 : ℝ) ^ (J + 1)) ^ (p - 1)) ^ (1 / p) ∧
    Integrable (fun z => ‖Rideal z - ∫ w, Rideal w ∂Q‖ ^ p) Q ∧
    (∫ z, ‖Rideal z - ∫ w, Rideal w ∂Q‖ ^ p ∂Q) ≤ 72 * (J + 1) * (324 * σ ^ p) at hh
  rw [← heq] at hh
  refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
  convert hh.2.2.2 using 1; ring
lemma tuned_kernel_properties {E F Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    (g : E × F → Ω → E × F) (correction : E × F → E × F) (v : F)
    {field : E → E} {dual : E → F} {a : E → Ω → E} {b : E → Ω → F}
    (hg : Measurable (Function.uncurry g)) (hc : Measurable correction)
    (hga : ∀ x ω, (g (x, v) ω + correction (x, v)).1 = a x ω)
    (hgb : ∀ x ω, -(g (x, v) ω + correction (x, v)).2 = b x ω)
    (hf : Measurable field) (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {L p σ : ℝ}
    (hL : 0 < L) (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪field x - field y, x - y⟫)
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hdl : ∀ x y, ‖dual x - dual y‖ ≤ L * ‖x - y‖)
    (hai : ∀ x, Integrable (a x) pnoise) (hbi : ∀ x, Integrable (b x) pnoise)
    (hap : ∀ x, Integrable (fun ω => ‖a x ω - field x‖ ^ p) pnoise)
    (hbp : ∀ x, Integrable (fun ω => ‖b x ω - dual x‖ ^ p) pnoise)
    (ham : ∀ x, ∫ ω, a x ω ∂pnoise = field x)
    (hbm : ∀ x, ∫ ω, b x ω ∂pnoise = dual x)
    (haV : ∀ x, (∫ ω, ‖a x ω - field x‖ ^ p ∂pnoise) ≤ σ ^ p)
    (hbV : ∀ x, (∫ ω, ‖b x ω - dual x‖ ^ p ∂pnoise) ≤ σ ^ p)
    {m H B : ℝ} (hmp : 0 < m) (hmH : m ≤ H) (hB : 0 < B)
    (start u : E) (hu : field u = 0)
    (href : m * ‖start - u‖ ^ 2 ≤ 16 * B)
    (hgrad : ‖dual u‖ ≤ 9 * Real.sqrt (H * B)) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    let S := (Measure.pi fun _ : Fin n => (levelLaw J : Measure _)).prod
      (Measure.infinitePi fun _ : ℕ => pnoise)
    let Y := fun w : (Fin n → Fin (J + 1)) × (ℕ → Ω) =>
      evalAt (fun k x => g x (w.2 k))
        (tunedKernelPlan p σ L m H B (extendLevels w.1) start v correction) 0
    let error := fun w => Y w - dual u
    Integrable error S ∧ Integrable (fun w => ‖error w‖ ^ 2) S ∧
      (∀ w, ‖error w‖ ≤ 48 * Real.sqrt (H * B)) ∧
      ‖∫ w, error w ∂S‖ ≤ Real.sqrt (m * B) / 1024 ∧
      (∫ w, ‖error w‖ ^ 2 ∂S) ≤ Real.sqrt (m * B) * Real.sqrt (H * B) / 512 := by
  intro J n S Y error
  let P := Measure.infinitePi fun _ : ℕ => pnoise
  let Q := (levelLaw J : Measure (Fin (J + 1))).prod P
  let h := kernelHorizon L m
  let X := fun z : Fin (J + 1) × (ℕ → Ω) =>
    evalAt (fun k x => g x (z.2 k)) (estimatorPlan h z.1 (1 / (4 * L)) start v correction) 0
  let mean := ∫ z, X z ∂Q
  have hr := actual_reply_properties pnoise P
    (OracleTemplate.StochasticGeneralized.infinitePi_iid pnoise)
    g correction v hga hgb hf ha hb hL hp hp2 hσ hm hl hdl hai hbi hap hbp ham hbm haV hbV h J start
  change Integrable X Q ∧ _ ∧ Integrable (fun z => ‖X z - mean‖ ^ p) Q ∧ _ at hr
  have hmean : ‖mean - dual u‖ ≤ Real.sqrt (m * B) / 4096 := by
    apply HeavyTailSaddleMultilevel.kernel_bias_bound hp hσ hmp hB (norm_nonneg _) href
      mean (dual ((fun x => x - (1 / (4 * L)) • field x)^[h] start)) (dual u)
    · exact HeavyTailSaddleGeometry.fast_orbit_dual_bias hL hm hl hdl u start hu h
    · exact hr.2.1
  have hX : Measurable X := by
    apply measurable_from_prod_countable_right
    intro j
    exact (estimator_plan_measurable (A := Unit) hg
      (start := fun _ => start) (dual := fun _ => v) (correction := fun _ => correction)
      measurable_const measurable_const (hc.comp measurable_snd) h j (1 / (4 * L)) 0).comp
      ((measurable_const (a := ())).prodMk measurable_id)
  have hD := finite_clipped_batch_law (A := Unit) pnoise hg
    (start := fun _ => start) (dual := fun _ => v) (correction := fun _ => correction)
    measurable_const measurable_const (hc.comp measurable_snd) h J n (1 / (4 * L))
    (32 * Real.sqrt (H * B)) ()
  have hY : ∀ w, ‖Y w‖ ≤ 32 * Real.sqrt (H * B) := by
    intro w
    dsimp only [Y, tunedKernelPlan]
    rw [eval_clipped_batch_plan]
    exact OracleTemplate.norm_clip_le (by positivity) _
  exact HeavyTailSaddleMultilevel.kernel_error_bounds Q S hX hr.1 mean (dual u) rfl
    hp hp2 hσ hmp hmH hB hgrad hmean J hr.2.2.1 hr.2.2.2 hY hD

lemma eval_epoch_plan {E F Ω : Type} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E × F → Ω → E × F)
    (p σ Lfast m H B a : ℝ)
    (seeds : ℕ → Fin (kernelBatch p σ m H B (kernelDepth p σ m B)) → Fin (kernelDepth p σ m B + 1))
    (ref : E) (correction : E × F → E × F) (N : ℕ) (state : F × F)
    (ξ : ℕ → Ω) (offset : ℕ) :
    evalAt (fun k x => g x (ξ k)) (epochPlan p σ Lfast m H B a seeds ref correction N state) offset =
      (cursorRun
        (fun _ levels => batchCalls (kernelHorizon Lfast m) (extendLevels levels)
          (kernelBatch p σ m H B (kernelDepth p σ m B)))
        (fun _ levels v ζ => evalAt (fun k x => g x (ζ k))
          (tunedKernelPlan p σ Lfast m H B (extendLevels levels) ref v correction) 0)
        (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedQuery a)
        (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedUpdate a m)
        seeds ξ N 0 0 offset state).1 := by
  exact StochasticEnvelopeExecution.evalAt_substituted_statePlan
    (fun _ levels => batchCalls (kernelHorizon Lfast m) (extendLevels levels)
      (kernelBatch p σ m H B (kernelDepth p σ m B)))
    (fun _ levels v => tunedKernelPlan p σ Lfast m H B (extendLevels levels) ref v correction)
    g (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedQuery a)
    (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedUpdate a m)
    seeds ξ N 0 offset state

lemma epoch_plan_law {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    (pnoise : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ Lfast m H B a : ℝ) (ref : E) {correction : E × F → E × F}
    (hc : Measurable correction) (N : ℕ) (state : F × F) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    let S := MeasureTheory.Measure.pi fun _ : Fin n => (levelLaw J : MeasureTheory.Measure _)
    let step := fun (_ : ℕ) (s : F × F) (w : (Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
      OracleTemplate.TemporalDiscrepancy.acceleratedUpdate a m s
        (evalAt (fun k x => g x (w.2 k))
          (tunedKernelPlan p σ Lfast m H B (extendLevels w.1) ref
            (OracleTemplate.TemporalDiscrepancy.acceleratedQuery a s) correction) 0)
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω) =>
        evalAt (fun k x => g x (w.2 k)) (epochPlan p σ Lfast m H B a w.1 ref correction N state) 0)
      (LongTails.Proofs.StochasticEnvelopeFreshness.idealRun step N 0 state)
      ((MeasureTheory.Measure.infinitePi fun _ : ℕ => S).prod
        (MeasureTheory.Measure.infinitePi fun _ : ℕ => pnoise))
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => S.prod
        (MeasureTheory.Measure.infinitePi fun _ : ℕ => pnoise)) := by
  intro J n S step
  apply StochasticEnvelopeExecution.substituted_statePlan_identDistrib S pnoise
    (fun _ levels => batchCalls (kernelHorizon Lfast m) (extendLevels levels) n)
    (fun _ => measurable_of_countable _)
    (fun _ levels v => tunedKernelPlan p σ Lfast m H B (extendLevels levels) ref v correction)
    g (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedQuery a)
    (fun _ => OracleTemplate.TemporalDiscrepancy.acceleratedUpdate a m)
  · intro j
    have hh := extended_clipped_batch_measurable (A := F) hg
      (start := fun _ => ref) (dual := id) (correction := fun _ => correction)
      measurable_const measurable_id (hc.comp measurable_snd)
      (kernelHorizon Lfast m) n J (1 / (4 * Lfast)) (32 * Real.sqrt (H * B)) 0
    exact hh.comp (show Measurable (fun w : F × ((Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
      (w.2.1, (w.1, w.2.2))) by fun_prop)
  · intro j
    unfold OracleTemplate.TemporalDiscrepancy.acceleratedQuery
    fun_prop
  · intro j
    unfold Function.uncurry OracleTemplate.TemporalDiscrepancy.acceleratedUpdate
      OracleTemplate.TemporalDiscrepancy.acceleratedQuery
    fun_prop

open StochasticEnvelopeFreshness
open OracleTemplate.TemporalDiscrepancy

lemma parameter_freshRun_measurable {A U S Ω : Type*} [MeasurableSpace A]
    [MeasurableSpace U] [MeasurableSpace S] [MeasurableSpace Ω]
    {cost : ℕ → S → ℕ} (hc : ∀ k, Measurable (cost k))
    {step : A → ℕ → U → S × (ℕ → Ω) → U}
    (hs : ∀ k, Measurable (fun w : (A × U) × (S × (ℕ → Ω)) => step w.1.1 k w.1.2 w.2))
    (N call : ℕ) :
    Measurable (fun w : (A × U) × ((ℕ → S) × (ℕ → Ω)) =>
      freshRun cost (step w.1.1) N call w.1.2 w.2) := by
  induction N generalizing call with
  | zero => exact measurable_fst.snd
  | succ N ih =>
    have hh : Measurable (fun w : (A × U) × ((ℕ → S) × (ℕ → Ω)) => (w.2.1 0, w.2.2)) := by fun_prop
    have ht : Measurable (fun w : (A × U) × ((ℕ → S) × (ℕ → Ω)) =>
        ((fun j => w.2.1 (j + 1)), fun j => w.2.2 (cost call (w.2.1 0) + j))) :=
      (by fun_prop : Measurable (fun w : (A × U) × ((ℕ → S) × (ℕ → Ω)) => fun j => w.2.1 (j + 1))).prodMk
        ((measurable_seed_shift (hc call)).comp hh)
    exact (ih (call + 1)).comp
      ((measurable_fst.fst.prodMk ((hs call).comp (measurable_fst.prodMk hh))).prodMk ht)

lemma epoch_plan_measurable {A E F Ω : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    {ref : A → E} {initial : A → F × F} {correction : A → E × F → E × F}
    (hr : Measurable ref) (hi : Measurable initial) (hc : Measurable (Function.uncurry correction))
    (p σ L m H B a : ℝ) (N : ℕ) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    Measurable (fun w : A × ((ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (epochPlan p σ L m H B a w.2.1 (ref w.1) (correction w.1) N (initial w.1)) 0) := by
  intro J n
  let cost := fun (_ : ℕ) (levels : Fin n → Fin (J + 1)) =>
    batchCalls (kernelHorizon L m) (extendLevels levels) n
  let step := fun (v : A) (_ : ℕ) (s : F × F) (w : (Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
    acceleratedUpdate a m s (evalAt (fun k x => g x (w.2 k))
      (tunedKernelPlan p σ L m H B (extendLevels w.1) (ref v) (acceleratedQuery a s) (correction v)) 0)
  have hs (k : ℕ) : Measurable (fun w : (A × (F × F)) × ((Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
      step w.1.1 k w.1.2 w.2) := by
    have hh := extended_clipped_batch_measurable (A := A × (F × F)) hg
      (start := fun v => ref v.1) (dual := fun v => acceleratedQuery a v.2)
      (correction := fun v => correction v.1)
      (hr.comp measurable_fst) (by unfold acceleratedQuery; fun_prop)
      (hc.comp (measurable_fst.fst.prodMk measurable_snd))
      (kernelHorizon L m) n J (1 / (4 * L)) (32 * Real.sqrt (H * B)) 0
    have hk := hh.comp (show Measurable
      (fun w : (A × (F × F)) × ((Fin n → Fin (J + 1)) × (ℕ → Ω)) =>
        (w.2.1, (w.1, w.2.2))) by fun_prop)
    have hu : Measurable (fun w : (F × F) × F => acceleratedUpdate a m w.1 w.2) := by
      unfold acceleratedUpdate acceleratedQuery
      fun_prop
    exact hu.comp (measurable_fst.snd.prodMk hk)
  have hh := parameter_freshRun_measurable (cost := cost) (fun _ => measurable_of_countable _) hs N 0
  have ht := hh.comp (show Measurable
    (fun w : A × ((ℕ → Fin n → Fin (J + 1)) × (ℕ → Ω)) => ((w.1, initial w.1), w.2)) by fun_prop)
  convert ht using 1
  funext w
  rw [eval_epoch_plan, StochasticEnvelopeExecution.cursorRun_freshRun]
  simp only [Nat.zero_add]
  rfl

lemma epoch_calls_measurable (p σ L m H B : ℝ) (N slot : ℕ) :
    let J := kernelDepth p σ m B
    let n := kernelBatch p σ m H B J
    Measurable (fun seeds : ℕ → Fin n → Fin (J + 1) =>
      slotCalls (fun j => batchCalls (kernelHorizon L m) (extendLevels (seeds j)) n) N slot) := by
  intro J n
  induction N generalizing slot with
  | zero => exact measurable_const
  | succ N ih =>
    exact (ih (slot + 1)).add
      ((measurable_of_countable (f := fun levels : Fin n → Fin (J + 1) =>
        batchCalls (kernelHorizon L m) (extendLevels levels) n)).comp (measurable_pi_apply slot))

lemma eval_halving_plan {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (raw : ℕ → E × F → E × F)
    (p σ L m H B δ : ℝ)
    (seeds : ℕ → Fin (kernelBatch p σ m H B (kernelDepth p σ m B)) → Fin (kernelDepth p σ m B + 1))
    (ref : E) (state : F × F) (correction : E × F → E × F) (call : ℕ) :
    let N := epochSteps m H (δ / 2)
    let cost := slotCalls (fun j => batchCalls (kernelHorizon L m) (extendLevels (seeds j))
      (kernelBatch p σ m H B (kernelDepth p σ m B))) N 0
    let v := evalAt raw (epochPlan p σ L m H B (epochMomentum m H (δ / 2)) seeds ref correction N state) call
    evalAt raw (halvingPlan p σ L m H B δ seeds ref state correction) call =
      (evalAt raw (tunedRefreshPlan p σ L (Real.sqrt (B / m)) (δ / 2) ref v.1 correction) (call + cost), v.1) := by
  intro N cost v
  dsimp only [halvingPlan, halvingCalls]
  rw [evalAt_bind, evalAt_map]

lemma halving_profile_coordinate_law (batch depth : ℕ → ℕ) (j : ℕ) :
    MeasurePreserving (fun s : HalvingProfile batch depth => s j)
      (halvingProfileLaw batch depth : Measure _)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (batch j) =>
        (levelLaw (depth j) : Measure (Fin (depth j + 1)))) := by
  refine ⟨measurable_pi_apply j, ?_⟩
  exact Measure.infinitePi_map_eval _ j

set_option maxHeartbeats 800000 in
lemma eval_refinement_plan {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E × F → Ω → E × F)
    (p σ L m H B δ : ℝ) (K : ℕ)
    (seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B))
    (state : E × F) (correction : E × F → E × F) (ξ : ℕ → Ω) (offset : ℕ) :
    evalAt (fun k x => g x (ξ k)) (refinementPlan p σ L m H B δ K seeds state correction) offset =
      (cursorRun
        (fun j (seed : HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) => halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (seed j))
        (fun j (seed : HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) (z : E × F) (ζ : ℕ → Ω) => evalAt (fun k x => g x (ζ k))
          (halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (seed j) z.1 (z.2, z.2) correction) 0)
        (fun _ z => z) (fun _ _ z => z) seeds ξ K 0 0 offset state).1 := by
  exact StochasticEnvelopeExecution.evalAt_substituted_statePlan
    (fun j (seed : HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) => halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (seed j))
    (fun j (seed : HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) (z : E × F) => halvingPlan p σ L m H (refinementEnvelope B j) (δ / (K + 1)) (seed j) z.1 (z.2, z.2) correction)
    g (fun _ z => z) (fun _ _ z => z) seeds ξ K 0 offset state

lemma epoch_work_exp_moment (h J n N : ℕ) {M : ℝ} (hM : 0 < M)
    (hmax : (h+1 : ℝ) * (1+3*(2 : ℝ)^J) ≤ M) :
    let Q := Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J+1)))
    let R := Measure.infinitePi fun _ : ℕ => Q
    let W := fun seeds : ℕ → Fin n → Fin (J+1) =>
      (slotCalls (fun j => batchCalls h (extendLevels (seeds j)) n) N 0 : ℝ) / M
    Integrable (fun seeds => Real.exp (W seeds)) R ∧
    (∫ seeds, Real.exp (W seeds) ∂R) ≤ Real.exp (2 * N * n * ((h+1)*(1+3*(J+1))) / M) := by
  intro Q R W
  have hh := HeavyTailSaddleMultilevel.batch_work_exp_moment h J n hM hmax
  have hh' : (∫ v, Real.exp ((batchCalls h (extendLevels v) n : ℝ) / M) ∂Q) ≤
      Real.exp (2 * ((n : ℝ) * ((h+1)*(1+3*(J+1))) / M)) := by
    convert hh.2 using 1
    ring
  have hp := HeavyTailSaddleMultilevel.prefix_exp_sum_moment Q
    (fun _ v => (batchCalls h (extendLevels v) n : ℝ) / M)
    (fun _ => (n : ℝ) * ((h+1)*(1+3*(J+1))) / M)
    N (fun _ _ => hh.1) (fun _ _ => hh')
  have hw (seeds : ℕ → Fin n → Fin (J+1)) :
      (∑ j ∈ Finset.range N, (batchCalls h (extendLevels (seeds j)) n : ℝ) / M) = W seeds := by
    simp only [W, StochasticEnvelopeExecution.slotCalls_sum, Nat.zero_add, Nat.cast_sum,
      Finset.sum_div]
  simpa only [hw, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_div_assoc, mul_assoc] using hp
lemma profile_epoch_work_exp_moment (batch depth : ℕ → ℕ) (j h N : ℕ)
    {M : ℝ} (hM : 0 < M) (hmax : (h+1 : ℝ) * (1+3*(2 : ℝ)^(depth j)) ≤ M) :
    let Q := (halvingProfileLaw batch depth : Measure (HalvingProfile batch depth))
    let W := fun seeds : HalvingProfile batch depth =>
      (slotCalls (fun k => batchCalls h (extendLevels (seeds j k)) (batch j)) N 0 : ℝ) / M
    Integrable (fun seeds => Real.exp (W seeds)) Q ∧
    (∫ seeds, Real.exp (W seeds) ∂Q) ≤
      Real.exp (2 * N * (batch j) * ((h+1)*(1+3*(depth j+1))) / M) := by
  intro Q W
  have hh := epoch_work_exp_moment h (depth j) (batch j) N hM hmax
  have hp := halving_profile_coordinate_law batch depth j
  exact ⟨hp.integrable_comp_of_integrable hh.1,
    (hp.hasLaw.integral_comp hh.1.aestronglyMeasurable).trans_le hh.2⟩

lemma profile_work_exp_moment (batch depth horizon count : ℕ → ℕ) (K : ℕ)
    {M : ℝ} (hM : 0 < M)
    (hmax : ∀ j < K, (horizon j+1 : ℝ) * (1+3*(2 : ℝ)^(depth j)) ≤ M) :
    let Q := (halvingProfileLaw batch depth : Measure (HalvingProfile batch depth))
    let R := Measure.infinitePi fun _ : ℕ => Q
    let W := fun seeds : ℕ → HalvingProfile batch depth =>
      (∑ j ∈ Finset.range K,
        (slotCalls (fun k => batchCalls (horizon j) (extendLevels (seeds j j k)) (batch j))
          (count j) 0 : ℝ)) / M
    let C := ∑ j ∈ Finset.range K,
      (count j : ℝ) * (batch j) * ((horizon j+1)*(1+3*(depth j+1)))
    Integrable (fun seeds => Real.exp (W seeds)) R ∧
    (∫ seeds, Real.exp (W seeds) ∂R) ≤ Real.exp (2 * C / M) := by
  intro Q R W C
  let cost := fun j (seed : HalvingProfile batch depth) =>
    (slotCalls (fun k => batchCalls (horizon j) (extendLevels (seed j k)) (batch j)) (count j) 0 : ℝ) / M
  let mean := fun j => (count j : ℝ) * (batch j) * ((horizon j+1)*(1+3*(depth j+1))) / M
  have hi (j : ℕ) (hj : j < K) : Integrable (fun seed => Real.exp (cost j seed)) Q :=
    (profile_epoch_work_exp_moment batch depth j (horizon j) (count j) hM (hmax j hj)).1
  have hm (j : ℕ) (hj : j < K) : (∫ seed, Real.exp (cost j seed) ∂Q) ≤ Real.exp (2 * mean j) := by
    have hh := (profile_epoch_work_exp_moment batch depth j (horizon j) (count j) hM (hmax j hj)).2
    convert hh using 1
    dsimp [mean]
    ring
  have hh := HeavyTailSaddleMultilevel.prefix_exp_sum_moment Q cost mean K hi hm
  have hw (seeds : ℕ → HalvingProfile batch depth) :
      (∑ j ∈ Finset.range K, cost j (seeds j)) = W seeds := by
    simp only [cost, W, Finset.sum_div]
  have hmean : (∑ j ∈ Finset.range K, mean j) = C / M := by
    simp only [mean, C, Finset.sum_div]
  simpa only [hw, hmean, mul_div_assoc] using hh


lemma refinement_calls_split (p σ L m H B δ : ℝ) (K : ℕ)
    (seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)) :
    (refinementCalls p σ L m H B δ K seeds : ℝ) =
      (∑ j ∈ Finset.range K, (256 : ℝ) * refreshBatch p σ L (Real.sqrt (refinementEnvelope B j / m)) *
        refreshRepetitions (δ / (K+1) / 2)) +
      ∑ j ∈ Finset.range K,
        (slotCalls (fun k => batchCalls (kernelHorizon L m) (extendLevels (seeds j j k))
          (refinementBatch p σ m H B j)) (epochSteps m H (δ / (K+1) / 2)) 0 : ℝ) := by
  let cost := fun j => halvingCalls p σ L m H (refinementEnvelope B j) (δ / (K+1)) (seeds j j)
  change (slotCalls cost K 0 : ℝ) = _
  have he := StochasticEnvelopeExecution.slotCalls_sum cost K 0
  simp only [Nat.zero_add] at he
  rw [he, Nat.cast_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [cost]
  simp only [halvingCalls, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    refinementBatch, refinementDepth]

lemma refinement_work_tail (p σ L m H B δ : ℝ) (K : ℕ) {M : ℝ} (hM : 0 < M)
    (hmax : ∀ j < K, (kernelHorizon L m+1 : ℝ) * (1+3*(2 : ℝ)^(refinementDepth p σ m B j)) ≤ M)
    (t : ℝ) :
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) :
      Measure (HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)))
    let D := ∑ j ∈ Finset.range K,
      (256 : ℝ) * refreshBatch p σ L (Real.sqrt (refinementEnvelope B j / m)) * refreshRepetitions (δ / (K+1) / 2)
    let C := ∑ j ∈ Finset.range K,
      (epochSteps m H (δ / (K+1) / 2) : ℝ) * refinementBatch p σ m H B j *
        ((kernelHorizon L m+1)*(1+3*(refinementDepth p σ m B j+1)))
    (Measure.infinitePi fun _ : ℕ => Q)
      {seeds | D + 2 * C + M * t < (refinementCalls p σ L m H B δ K seeds : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  intro Q D C
  let W := fun seeds : ℕ → HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B) =>
    ∑ j ∈ Finset.range K,
      (slotCalls (fun k => batchCalls (kernelHorizon L m) (extendLevels (seeds j j k))
        (refinementBatch p σ m H B j)) (epochSteps m H (δ / (K+1) / 2)) 0 : ℝ)
  have hh := profile_work_exp_moment (refinementBatch p σ m H B) (refinementDepth p σ m B)
    (fun _ => kernelHorizon L m) (fun _ => epochSteps m H (δ / (K+1) / 2)) K hM hmax
  have ht := HeavyTailSaddleMultilevel.exponential_work_tail (Measure.infinitePi fun _ : ℕ => Q)
    W hM hh.1 hh.2 t
  have he (seeds) : (refinementCalls p σ L m H B δ K seeds : ℝ) = D + W seeds :=
    refinement_calls_split p σ L m H B δ K seeds
  refine (measure_mono ?_).trans ht
  intro seeds hs
  change D + 2 * C + M * t < (refinementCalls p σ L m H B δ K seeds : ℝ) at hs
  rw [he] at hs
  change 2 * C + M * t < W seeds
  linarith

open OracleTemplate LongTails.Algorithms.QueryLayers
lemma evalAt_transport {Q R U : Type} (reply : ℕ → Q → R) {n k : ℕ}
    (h : n=k) (plan : QueryPlan Q R U n) (call : ℕ) :
    evalAt reply (cast (congrArg (QueryPlan Q R U) h) plan) call = evalAt reply plan call := by
  cases h
  rfl
lemma evalAt_padding {Q R U : Type} (reply : ℕ → Q → R) (q0 : Q) (u0 : U) (n call : ℕ) :
    evalAt reply (paddingPlan q0 u0 n) call = u0 := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih => exact ih (call+1)
lemma evalAt_capped_plan {Q R U : Type} (reply : ℕ → Q → R) (q0 : Q) (u0 : U)
    (cap : ℕ) {k : ℕ} (plan : QueryPlan Q R U k) (call : ℕ) :
    evalAt reply (cappedPlan q0 u0 cap plan) call =
      if k ≤ cap then evalAt reply plan call else u0 := by
  by_cases h : k ≤ cap
  · simp only [cappedPlan, dite_eq_left h, ite_eq_left h]
    rw [evalAt_transport reply (Nat.sub_add_cancel h)]
    unfold paddedPlan
    rw [evalAt_bind, evalAt_padding]
  · simp only [cappedPlan, dite_eq_right h, ite_eq_right h]
    exact evalAt_padding reply q0 u0 cap call

lemma capped_plan_output_measurable {W Q R U : Type} [MeasurableSpace W] [MeasurableSpace U]
    (k : W → ℕ) (plan : (w : W) → QueryPlan Q R U (k w))
    (reply : W → ℕ → Q → R) (q0 : W → Q) (u0 : W → U) (cap call : ℕ)
    (hk : Measurable k) (hu : Measurable u0)
    (hp : Measurable (fun w => evalAt (reply w) (plan w) call)) :
    Measurable (fun w => evalAt (reply w) (cappedPlan (q0 w) (u0 w) cap (plan w)) call) := by
  simp_rw [evalAt_capped_plan]
  exact Measurable.ite (measurableSet_le hk measurable_const) hp hu

lemma capped_plan_failure_bound {W Q R U : Type} [MeasurableSpace W]
    (P : Measure W) (k : W → ℕ) (plan : (w : W) → QueryPlan Q R U (k w))
    (reply : W → ℕ → Q → R) (q0 : W → Q) (u0 : W → U) (cap call : ℕ)
    (bad : Set U) {α β : ENNReal}
    (hbad : P {w | evalAt (reply w) (plan w) call ∈ bad} ≤ α)
    (hcost : P {w | cap < k w} ≤ β) :
    P {w | evalAt (reply w) (cappedPlan (q0 w) (u0 w) cap (plan w)) call ∈ bad} ≤ α+β := by
  have hs : {w | evalAt (reply w) (cappedPlan (q0 w) (u0 w) cap (plan w)) call ∈ bad} ⊆
      {w | evalAt (reply w) (plan w) call ∈ bad} ∪ {w | cap < k w} := by
    intro w hw
    by_cases hk : k w ≤ cap
    · left
      simpa only [Set.mem_ofPred_eq, evalAt_capped_plan, ite_eq_left hk] using hw
    · exact Or.inr (Nat.lt_of_not_ge hk)
  exact (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add hbad hcost))

lemma refinement_max_reply_pos (p σ L m B : ℝ) (K : ℕ) :
    0 < refinementMaxReply p σ L m B K := by unfold refinementMaxReply; omega
lemma refinement_reply_le_max (p σ L m B : ℝ) (K j : ℕ) (hj : j < K) :
    (kernelHorizon L m+1 : ℝ)*(1+3*(2 : ℝ)^(refinementDepth p σ m B j)) ≤
      refinementMaxReply p σ L m B K := by
  have hh := Finset.le_sup (f := fun j => (kernelHorizon L m+1)*(1+3*2^(refinementDepth p σ m B j)))
    (Finset.mem_range.mpr hj)
  have hb : (kernelHorizon L m+1)*(1+3*2^(refinementDepth p σ m B j)) ≤
      refinementMaxReply p σ L m B K := hh.trans (Nat.le_add_left _ _)
  exact_mod_cast hb
lemma refinement_cap_threshold (p σ L m H B δ η : ℝ) (K : ℕ) :
    (refinementFixedCalls p σ L m B δ K : ℝ) + 2*refinementMeanCalls p σ L m H B δ K +
      (refinementMaxReply p σ L m B K : ℝ)*Real.log (1/η) ≤ refinementCap p σ L m H B δ η K := by
  unfold refinementCap
  push_cast
  have hh := Nat.le_ceil ((refinementMaxReply p σ L m B K : ℝ)*Real.log (1/η))
  linarith only [hh]
lemma refinement_overflow_probability (p σ L m H B δ η : ℝ) (hη : 0 < η) (K : ℕ) :
    let Q := (halvingProfileLaw (refinementBatch p σ m H B) (refinementDepth p σ m B) :
      Measure (HalvingProfile (refinementBatch p σ m H B) (refinementDepth p σ m B)))
    (Measure.infinitePi fun _ : ℕ => Q)
      {seeds | refinementCap p σ L m H B δ η K < refinementCalls p σ L m H B δ K seeds}
      ≤ ENNReal.ofReal η := by
  intro Q
  have hM : (0 : ℝ) < refinementMaxReply p σ L m B K := by
    exact_mod_cast refinement_max_reply_pos p σ L m B K
  have hh := refinement_work_tail p σ L m H B δ K hM
    (refinement_reply_le_max p σ L m B K) (Real.log (1/η))
  have ht : (Measure.infinitePi fun _ : ℕ => Q)
      {seeds | (refinementFixedCalls p σ L m B δ K : ℝ) + 2*refinementMeanCalls p σ L m H B δ K +
        (refinementMaxReply p σ L m B K : ℝ)*Real.log (1/η) <
          (refinementCalls p σ L m H B δ K seeds : ℝ)} ≤ ENNReal.ofReal (Real.exp (-Real.log (1/η))) := by
    simpa only [refinementFixedCalls, refinementMeanCalls, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hh
  have he : Real.exp (-Real.log (1/η)) = η := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    simp
  rw [he] at ht
  refine (measure_mono ?_).trans ht
  intro seeds hs
  have hc : (refinementCap p σ L m H B δ η K : ℝ) < refinementCalls p σ L m H B δ K seeds := by
    exact_mod_cast hs
  exact (refinement_cap_threshold p σ L m H B δ η K).trans_lt hc


lemma capped_plan_product_failure {S W Q R U : Type} [MeasurableSpace S] [MeasurableSpace W]
    (P : Measure S) (V : Measure W) [IsProbabilityMeasure V]
    (k : S → ℕ) (hk : Measurable k) (plan : (s : S) → QueryPlan Q R U (k s))
    (reply : W → ℕ → Q → R) (q0 : Q) (u0 : U) (cap call : ℕ)
    (bad : Set U) {α β : ENNReal}
    (hbad : (P.prod V) {w | evalAt (reply w.2) (plan w.1) call ∈ bad} ≤ α)
    (hcost : P {s | cap < k s} ≤ β) :
    (P.prod V) {w | evalAt (reply w.2) (cappedPlan q0 u0 cap (plan w.1)) call ∈ bad} ≤ α+β := by
  apply capped_plan_failure_bound (P.prod V) (fun w => k w.1) (fun w => plan w.1)
    (fun w => reply w.2) (fun _ => q0) (fun _ => u0) cap call bad hbad
  have hs : MeasurableSet {s | cap < k s} := measurableSet_lt measurable_const hk
  have he := (measurePreserving_fst (μ := P) (ν := V)).measure_preimage hs.nullMeasurableSet
  exact he.le.trans hcost

end LongTails.Proofs.HeavyTailSaddleExecution
