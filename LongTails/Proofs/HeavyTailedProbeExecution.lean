import LongTails.Proofs.HeavyTailedProbeGeometry
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.HeavyTailedSpectralEnergy

namespace LongTails.Proofs.HeavyTailedProbeExecution

open LongTails.Algorithms.HeavyTailedEnergyProbe
open LongTails.Setups.HeavyTailedHessianVector
open OracleTemplate
open MeasureTheory
open scoped RealInnerProductSpace

lemma indexed_run {d : ℕ} (shift η : ℝ)
    (response : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℕ) (s : State d) (n : ℕ) (hn : s.index = n) :
    ((fun sc : State d × ℕ =>
      (step shift η sc.1 (response sc.2 sc.1.vector), sc.2 + 1))^[K] (s, n)).1 =
      run shift η response K s := by
  induction K generalizing s n with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply]
      change ((fun sc : State d × ℕ =>
        (step shift η sc.1 (response sc.2 sc.1.vector), sc.2 + 1))^[K]
        (step shift η s (response n s.vector), n + 1)).1 = _
      rw [ih _ _ (by simp only [step, hn])]
      unfold run
      rw [Function.iterate_succ_apply, hn]

lemma run_succ {d : ℕ} (shift η : ℝ)
    (response : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℕ) (s : State d) :
    run shift η response (K + 1) s =
      step shift η (run shift η response K s)
        (response (run shift η response K s).index (run shift η response K s).vector) := by
  exact Function.iterate_succ_apply' _ _ _

lemma run_metadata {d : ℕ} (shift η : ℝ)
    (response : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℕ) (s : State d) :
    (run shift η response K s).index = s.index + K ∧
      (run shift η response K s).target = s.target ∧
      (run shift η response K s).fallback = s.fallback := by
  induction K with
  | zero => simp [run]
  | succ K ih =>
      rw [run_succ]
      simp only [step, ih.1, ih.2.1, ih.2.2, Nat.add_assoc, and_self]

lemma run_selected {d : ℕ} (shift η : ℝ)
    (response : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℕ) (s : State d) (hi : s.index = 0) (ht : s.target < K) :
    (run shift η response K s).selected = (run shift η response s.target s).vector := by
  induction K with
  | zero => omega
  | succ K ih =>
      rw [run_succ]
      have hmeta := run_metadata shift η response K s
      change (if (run shift η response K s).index = (run shift η response K s).target
        then (run shift η response K s).vector else (run shift η response K s).selected) = _
      rw [hmeta.1, hmeta.2.1, hi, zero_add]
      by_cases heq : K = s.target
      · simp only [heq, ite_true]
      · rw [ite_eq_right heq]
        exact ih (by omega)

lemma run_vector_eq_normalizedPath {d : ℕ} (shift η : ℝ)
    (H : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (K : ℕ) (s : State d) (hi : s.index = 0) :
    (run shift η (fun k v => H k v) K s).vector =
      HeavyTailedProbeGeometry.normalizedPath
        (fun k => (1 + η * shift) • ContinuousLinearMap.id ℝ _ - η • H k)
        s.fallback s.vector K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [run_succ]
      have hmeta := run_metadata shift η (fun k v => H k v) K s
      simp only [step, HeavyTailedProbeGeometry.normalizedPath, hmeta.1, hmeta.2.2,
        hi, zero_add, ih, sub_apply, smul_apply,
        ContinuousLinearMap.id_apply]

lemma execute_probe (p : Params) (x : Space p) (shift η : ℝ) (T K : ℕ)
    (O : Oracle (Space p × Option (Space p)) (Space p))
    (seed : (algorithm p x shift η T).Seed) (ξ : (k : ℕ) → O.Seed k)
    (reply : ℕ → (Space p × Option (Space p)) → Space p)
    (h : ∀ history query, O.answer history query (ξ history.length) = reply history.length query.2) :
    execute O (algorithm p x shift η T) (fun _ => K) seed ξ =
      (run shift η (fun k v => reply k (x, some v)) K (initialState seed.1 seed.2.val)).selected := by
  rw [execute_indexed_of_answer O (algorithm p x shift η T) K seed ξ
    (fun k q => reply k q.2) h]
  change (((fun sc : State p.d × ℕ =>
    (step shift η sc.1 (reply sc.2 (x, some sc.1.vector)), sc.2 + 1))^[K]
      (initialState seed.1 seed.2.val, 0)).1).selected = _
  rw [indexed_run shift η (fun k v => reply k (x, some v)) K _ 0 rfl]

lemma execute_probe_selected (p : Params) (x : Space p) (shift η : ℝ) (T : ℕ)
    (hT : 0 < T) (O : Oracle (Space p × Option (Space p)) (Space p))
    (seed : (algorithm p x shift η T).Seed) (ξ : (k : ℕ) → O.Seed k)
    (H : ℕ → Space p →L[ℝ] Space p)
    (reply : ℕ → (Space p × Option (Space p)) → Space p)
    (h : ∀ history query, O.answer history query (ξ history.length) = reply history.length query.2)
    (hH : ∀ k v, reply k (x, some v) = H k v) :
    execute O (algorithm p x shift η T) (fun _ => T) seed ξ =
      HeavyTailedProbeGeometry.normalizedPath
        (fun k => (1 + η * shift) • ContinuousLinearMap.id ℝ _ - η • H k)
        (initialVector seed.1) (initialVector seed.1) seed.2.val := by
  rw [execute_probe p x shift η T T O seed ξ reply h]
  simp only [hH]
  have ht : seed.2.val < T := by
    have hh := seed.2.isLt
    simpa only [max_eq_right (show 1 ≤ T by omega)] using hh
  rw [run_selected shift η (fun k v => H k v) T _ rfl ht,
    run_vector_eq_normalizedPath shift η H _ _ rfl]
  rfl

lemma coordinate_iid_law {Ω : Type*} [MeasurableSpace Ω]
    {P0 : Measure Ω} {P : Measure (ℕ → Ω)}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P0 P) : P = Measure.infinitePi (fun _ : ℕ => P0) := by
  have hh := h.stream_law.map_eq
  change Measure.map id P = _ at hh
  simpa only [Measure.map_id] using hh

lemma swap_second_third_preserving {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) (Q : Measure B) (R : Measure C)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    MeasurePreserving (fun z : (A × B) × C => ((z.1.1, z.2), z.1.2))
      ((P.prod Q).prod R) ((P.prod R).prod Q) := by
  have h1 := measurePreserving_prodAssoc P Q R
  have h2 := (MeasurePreserving.id P).prod (Measure.measurePreserving_swap (μ := Q) (ν := R))
  have h3 := (measurePreserving_prodAssoc P R Q).symm MeasurableEquiv.prodAssoc
  convert h3.comp (h2.comp h1) using 1
  funext z
  rfl

lemma shifted_step_identity {d : ℕ} (shift η : ℝ)
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ContinuousLinearMap.id ℝ _ + η • (shift • ContinuousLinearMap.id ℝ _ - H) =
      (1 + η * shift) • ContinuousLinearMap.id ℝ _ - η • H := by
  ext v
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply, smul_sub,
    smul_smul, add_smul, one_smul, add_sub_assoc]

lemma fixed_hessian_execution (p : Params) (x : Space p) (shift η : ℝ) (T : ℕ) (hT : 0 < T)
    (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (P : ProbabilityMeasure (ℕ → p.Ω))
    (seed : (Fin p.d → Bool) × Fin (max 1 T)) (ξ : ℕ → p.Ω) :
    let O : Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, y, v) ω => match v with | none => g y ω | some w => H y ω w }
    execute O (algorithm p x shift η T) (fun _ => T) seed ξ =
      HeavyTailedSpectralEnergy.initialPath
        (fun ω => shift • ContinuousLinearMap.id ℝ _ - H x ω) η (seed.1, ξ) seed.2.val := by
  intro O
  have hh := execute_probe_selected p x shift η T hT O seed ξ (fun k => H x (ξ k))
    (fun k q => match q.2 with | none => g q.1 (ξ k) | some v => H q.1 (ξ k) v)
    (by intro history query; rfl) (by intro k v; rfl)
  simpa only [HeavyTailedSpectralEnergy.initialPath, shifted_step_identity] using hh

lemma probe_execution_probability (p : Params) (x : Space p) (shift η : ℝ)
    (T : ℕ) [NeZero (max 1 T)] (hT : 0 < T)
    (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (H x)) (P : ProbabilityMeasure (ℕ → p.Ω))
    (S : Set (Space p)) (hS : MeasurableSet S) :
    let O : Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, y, v) ω => match v with | none => g y ω | some w => H y ω w }
    (((algorithm p x shift η T).law : Measure _).prod (P : Measure _)).real
      {z | execute O (algorithm p x shift η T) (fun _ => T) z.1 z.2 ∈ S} =
      (((PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod (P : Measure _)).prod
        (PMF.uniformOfFintype (Fin (max 1 T))).toMeasure).real
      {z | HeavyTailedSpectralEnergy.initialPath
        (fun ω => shift • ContinuousLinearMap.id ℝ _ - H x ω) η z.1 z.2.val ∈ S} := by
  intro O
  let B := fun ω => shift • ContinuousLinearMap.id ℝ (Space p) - H x ω
  have hB : Measurable B := measurable_const.sub hH
  have hp : Measurable (fun z : ((Fin p.d → Bool) × (ℕ → p.Ω)) × Fin (max 1 T) =>
      HeavyTailedSpectralEnergy.initialPath B η z.1 z.2.val) :=
    measurable_from_prod_countable_left
      (fun i => HeavyTailedSpectralEnergy.initialPath_measurable B hB η i.val)
  have hpres := swap_second_third_preserving
    (PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure
    (PMF.uniformOfFintype (Fin (max 1 T))).toMeasure (P : Measure (ℕ → p.Ω))
  have heq := hpres.measureReal_preimage (hS.preimage hp).nullMeasurableSet
  refine Eq.trans ?_ heq
  congr 1
  ext z
  change execute O (algorithm p x shift η T) (fun _ => T) z.1 z.2 ∈ S ↔
    HeavyTailedSpectralEnergy.initialPath B η (z.1.1, z.2) z.1.2.val ∈ S
  rw [fixed_hessian_execution p x shift η T hT g H P z.1 z.2]


lemma actual_energy_probability (p : Params) (hd : 0 < p.d)
    (x : Space p) (shift η ell γ q : ℝ) (T : ℕ) (hT : 0 < T)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (Hmean : Space p →L[ℝ] Space p) (hH : Measurable (H x))
    (P0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure p.Ω) (P : Measure (ℕ → p.Ω)))
    (hη : 0 < η) (hpq : p.p.HolderConjugate q) (hp2 : p.p ≤ 2)
    (hell : 0 ≤ ell) (hηell : η * ell ≤ 1) (hγ : 0 < γ) (hσ : 0 ≤ p.σh)
    (hpos : ∀ v, 0 ≤ ⟪v, (shift • ContinuousLinearMap.id ℝ (Space p) - Hmean) v⟫)
    (hnorm : ‖shift • ContinuousLinearMap.id ℝ (Space p) - Hmean‖ ≤ ell)
    (hi : ∀ v, Integrable (fun ω => H x ω v) (P0 : Measure p.Ω))
    (hm : ∀ v, (∫ ω, H x ω v ∂(P0 : Measure p.Ω)) = Hmean v)
    (hpi : ∀ v, Integrable (fun ω => ‖H x ω v - Hmean v‖ ^ p.p) (P0 : Measure p.Ω))
    (hb : ∀ v, (∫ ω, ‖H x ω v - Hmean v‖ ^ p.p ∂(P0 : Measure p.Ω)) ≤
      p.σh ^ p.p * ‖v‖ ^ p.p)
    (u : Space p) (hu : (shift • ContinuousLinearMap.id ℝ (Space p) - Hmean) u = ell • u)
    (hunit : ‖u‖ = 1)
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤ η * T * γ)
    (hsmall : ((1 + η * ell) ^ p.p + 6 * η ^ p.p * p.σh ^ p.p) ^ T ≤
      (2 * (1 + η * ell) ^ T) ^ p.p)
    (hnoise : T * (η ^ p.p * p.σh ^ p.p) ≤ (1 / 4 : ℝ) ^ q / 256) :
    let O : Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, y, v) ω => match v with | none => g y ω | some w => H y ω w }
    (1 / 4 : ℝ) ^ q / 64 ≤
      (((algorithm p x shift η T).law : Measure _).prod (P : Measure (ℕ → p.Ω))).real
      {z | let v := execute O (algorithm p x shift η T) (fun _ => T) z.1 z.2
        ell - ⟪v, (shift • ContinuousLinearMap.id ℝ (Space p) - Hmean) v⟫ ≤ γ} := by
  intro O
  let A := shift • ContinuousLinearMap.id ℝ (Space p) - Hmean
  let B := fun ω => shift • ContinuousLinearMap.id ℝ (Space p) - H x ω
  have hB : Measurable B := measurable_const.sub hH
  have hshift (v : Space p) := HeavyTailedSpectralMoments.shifted_oracle_moments
    Hmean (H x) v shift p.p p.σh (hi v) (hm v) (hpi v) (hb v)
  let : NeZero T := ⟨Nat.ne_zero_of_lt hT⟩
  let : NeZero (max 1 T) := ⟨by omega⟩
  have he := HeavyTailedSpectralEnergy.spectral_energy_probability
    (P0 : Measure p.Ω) hd A B hB hη hpq hp2 hell hηell hγ hσ hpos hnorm
    (fun v => (hshift v).1) (fun v => (hshift v).2.1)
    (fun v => (hshift v).2.2.1) (fun v => (hshift v).2.2.2)
    hu hunit (max 1 T)
    (by simpa only [max_eq_right (show 1 ≤ T from hT)] using htune)
    (by simpa only [max_eq_right (show 1 ≤ T from hT)] using hsmall)
    (by simpa only [max_eq_right (show 1 ≤ T from hT)] using hnoise)
  let S := {v : Space p | ell - ⟪v, A v⟫ ≤ γ}
  have hS : MeasurableSet S := measurableSet_le
    (measurable_const.sub (measurable_id.inner A.continuous.measurable)) measurable_const
  have heq := probe_execution_probability p x shift η T hT g H hH P S hS
  change (1 / 4 : ℝ) ^ q / 64 ≤ _ at he
  change (1 / 4 : ℝ) ^ q / 64 ≤
    (((algorithm p x shift η T).law : Measure _).prod (P : Measure (ℕ → p.Ω))).real
      {z | execute O (algorithm p x shift η T) (fun _ => T) z.1 z.2 ∈ S}
  rw [heq, coordinate_iid_law hIID]
  simpa only [S, A, B, Set.mem_ofPred_eq] using he

end LongTails.Proofs.HeavyTailedProbeExecution
