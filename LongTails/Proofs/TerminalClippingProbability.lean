import LongTails.Proofs.TerminalClippingAccuracy
import LongTails.Proofs.TerminalClippingExecution
import LongTails.Proofs.FixedBatchConfidenceProbability

open MeasureTheory
open scoped RealInnerProductSpace
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

def completeSamples {Ω : Type*} {T : ℕ} (hT : 0 < T) (ξ : Fin T → Ω) (t : ℕ) : Ω :=
  if ht : t < T then ξ ⟨t, ht⟩ else ξ ⟨0, hT⟩

lemma completeSamples_fin {Ω : Type*} {T : ℕ} (hT : 0 < T) (ξ : Fin T → Ω) (i : Fin T) :
    completeSamples hT ξ i = ξ i := by simp [completeSamples, i.isLt]

lemma finite_trajectory {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (hT : 0 < q.T) (ξ : Fin q.T → Ω) {k : ℕ} (hk : k ≤ q.T) :
    iterateSamples (transition q g projection) k (0, q.x0, 0) (fun i => ξ (Fin.castLE hk i)) =
      trajectory q g projection (completeSamples hT ξ) k := by
  rw [← iterate_eq_trajectory]
  congr 1
  funext i
  exact (completeSamples_fin hT ξ (Fin.castLE hk i)).symm

lemma finite_accumulated_sum {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (increment : (ℕ × (Vector q.d × Vector q.d)) → Ω → ℝ)
    (hT : 0 < q.T) (ξ : Fin q.T → Ω) :
    (iterateSamples (accumulatingTransition (transition q g projection) increment) q.T
      ((0, q.x0, 0), 0) ξ).2 =
      ∑ t ∈ Finset.range q.T,
        increment (trajectory q g projection (completeSamples hT ξ) t) (completeSamples hT ξ t) := by
  have hh := accumulated_along (transition q g projection) increment
    (trajectory q g projection (completeSamples hT ξ)) (completeSamples hT ξ)
    (fun _ => rfl) q.T 0
  have he : (fun i : Fin q.T => completeSamples hT ξ i) = ξ := funext (completeSamples_fin hT ξ)
  rw [he] at hh
  simpa only [trajectory, zero_add] using congrArg Prod.snd hh

lemma finite_accuracy {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure Ω) (hg : Measurable (Function.uncurry g)) (hpm : Measurable projection)
    (hB : 0 < q.B) (hG : 0 < q.G) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} (hX : MeasurableSet X) {f : Vector q.d → ℝ} (hf : ConvexOn ℝ X f)
    (hx0 : q.x0 ∈ X) (hpX : ∀ y, projection y ∈ X)
    (hp : ∀ y, ∀ v ∈ X, ⟪y - projection y, v - projection y⟫ ≤ 0)
    (hsub : ∀ x ∈ X, ∀ y ∈ X, f x - f y ≤ ⟪∫ ω, g x ω ∂(P : Measure Ω), x - y⟫)
    (hgi : ∀ x ∈ X, Integrable (g x) (P : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (P : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(P : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    {u : Vector q.d} (hu : u ∈ X) (hmin : ∀ x ∈ X, f u ≤ f x) {D : ℝ} (hD : 0 < D)
    (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D) :
    (Measure.pi fun _ : Fin q.T => (P : Measure Ω))
      {ξ | 16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T <
        f (iterateSamples (transition q g projection) q.T (0, q.x0, 0) ξ).2.1 - f u} ≤
      ENNReal.ofReal q.δ := by
  let advance := transition q g projection
  let good := radiusGood q X u D
  let initial : ℕ × (Vector q.d × Vector q.d) := (0, q.x0, 0)
  let Q := Real.log (8 / q.δ)
  let μ := Measure.pi fun _ : Fin q.T => (P : Measure Ω)
  let R : Set (Fin q.T → Ω) := {ξ | ¬good (iterateSamples (stopUnless good advance) q.T initial ξ)}
  let M : Set (Fin q.T → Ω) := {ξ | good (iterateSamples (stopUnless good advance) q.T initial ξ) ∧
    Q < (iterateSamples (accumulatingTransition advance (martingaleIncrement q g P u D)) q.T (initial, 0) ξ).2}
  let S : Set (Fin q.T → Ω) := {ξ | good (iterateSamples (stopUnless good advance) q.T initial ξ) ∧
    Q < (iterateSamples (accumulatingTransition advance (squareIncrement q g D)) q.T (initial, 0) ξ).2}
  let e := ENNReal.ofReal (Real.exp (-Q))
  have hgood := radiusGood_measurable q hX u D
  have ha := transition_measurable q hg hpm
  have hproj (y : Vector q.d) : ‖projection y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := projection_distance (hp y u hu)
  have hstepR := radius_transition_mgf q g projection P hg hpm hB hG hδ hδ1 hT
    hmin (fun x hx => hsub x hx u hu) hgi hmi hm hproj hD hstart hGD
  have hR : μ R ≤ e := by
    apply (measure_mono ?_).trans (stopped_radius_tail q g projection P hg hpm hδ hδ1 hT hX u hD hstart hstepR)
    intro ξ hξ
    have hi := stopped_radius_invariant q g projection hB hδ hδ1 hx0 hpX hD.le hstart q.T ξ
    change 16 * D < ‖(iterateSamples (stopUnless good advance) q.T initial ξ).2.1 - u‖ ^ 2
    apply lt_of_not_ge
    intro hh
    exact hξ ⟨hi, hh⟩
  have hstepM (s : ℕ × (Vector q.d × Vector q.d)) (hs : good s) :
      Integrable (fun ω => Real.exp (martingaleIncrement q g P u D s ω)) (P : Measure Ω) ∧
      (∫ ω, Real.exp (martingaleIncrement q g P u D s ω) ∂(P : Measure Ω)) ≤ 1 := by
    have hh := clippedSample_centered_mgf q g P hg hB hG hδ hδ1 hT hD hstart hGD hmi hm s hs
    exact compensated_mgf hh.1 hh.2
  have hM : μ M ≤ e := by
    simpa only [zero_add] using accumulated_exponential_tail hgood ha
      (martingaleIncrement_measurable q hg P u D) P hstepM q.T initial 0 Q
  have hstepS (s : ℕ × (Vector q.d × Vector q.d)) (hs : good s) :
      Integrable (fun ω => Real.exp (squareIncrement q g D s ω)) (P : Measure Ω) ∧
      (∫ ω, Real.exp (squareIncrement q g D s ω) ∂(P : Measure Ω)) ≤ 1 := by
    have hh := squared_clip_mgf q g P hg hB hG hδ hδ1 hT hD hstart hGD hmi hm s hs
    exact compensated_mgf hh.1 hh.2
  have hS : μ S ≤ e := by
    simpa only [zero_add] using accumulated_exponential_tail hgood ha
      (squareIncrement_measurable q hg D) P hstepS q.T initial 0 Q
  have hcontain : {ξ : Fin q.T → Ω | 16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T <
      f (iterateSamples advance q.T initial ξ).2.1 - f u} ⊆ R ∪ M ∪ S := by
    intro ξ hbad
    by_cases hr : good (iterateSamples (stopUnless good advance) q.T initial ξ)
    · by_cases hm' : Q < (iterateSamples (accumulatingTransition advance (martingaleIncrement q g P u D)) q.T (initial, 0) ξ).2
      · exact Or.inl (Or.inr ⟨hr, hm'⟩)
      · by_cases hs' : Q < (iterateSamples (accumulatingTransition advance (squareIncrement q g D)) q.T (initial, 0) ξ).2
        · exact Or.inr ⟨hr, hs'⟩
        · exfalso
          have hradius (t : ℕ) (ht : t ≤ q.T) :
              ‖(trajectory q g projection (completeSamples hT ξ) t).2.1 - u‖ ^ 2 ≤ 16 * D := by
            rw [← finite_trajectory q g projection hT ξ ht]
            exact stopped_radius_coupling q g projection hB hδ hδ1 hx0 hpX hD.le hstart q.T ξ hr.2 t ht
          have hmSum : (∑ t ∈ Finset.range q.T,
              martingaleIncrement q g P u D (trajectory q g projection (completeSamples hT ξ) t)
                (completeSamples hT ξ t)) ≤ Q := by
            rw [← finite_accumulated_sum q g projection (martingaleIncrement q g P u D) hT ξ]
            exact le_of_not_gt hm'
          have hsSum : (∑ t ∈ Finset.range q.T,
              squareIncrement q g D (trajectory q g projection (completeSamples hT ξ) t)
                (completeSamples hT ξ t)) ≤ Q := by
            rw [← finite_accumulated_sum q g projection (squareIncrement q g D) hT ξ]
            exact le_of_not_gt hs'
          have hh := trajectory_accuracy_on_events q g projection P (completeSamples hT ξ) hg
            hB hG hδ hδ1 hT hf hx0 hpX hp hsub hgi hmi hm hu hD hstart hGD hradius hmSum hsSum
          have he : iterateSamples advance q.T initial ξ = trajectory q g projection (completeSamples hT ξ) q.T := by
            simpa only [Fin.castLE_refl] using finite_trajectory q g projection hT ξ (le_refl q.T)
          change 16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T < f (iterateSamples advance q.T initial ξ).2.1 - f u at hbad
          rw [he] at hbad
          exact (not_lt_of_ge hh) hbad
    · exact Or.inl (Or.inl hr)
  have htotal : μ (R ∪ M ∪ S) ≤ e + e + e :=
    ((measure_union_le (R ∪ M) S).trans (add_le_add (measure_union_le R M) le_rfl)).trans
      (add_le_add (add_le_add hR hM) hS)
  apply ((measure_mono hcontain).trans htotal).trans
  have he : Real.exp (-Q) = q.δ / 8 := by
    dsimp [Q]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 8 / q.δ)]
    field_simp
  dsimp [e]
  rw [he, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma iid_accuracy {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ν : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (ν : Measure Ω) (P : Measure (ℕ → Ω)))
    (hg : Measurable (Function.uncurry g)) (hpm : Measurable projection)
    (hB : 0 < q.B) (hG : 0 < q.G) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} (hX : MeasurableSet X) {f : Vector q.d → ℝ}
    (hf : ConvexOn ℝ X f) (hfm : Measurable f)
    (hx0 : q.x0 ∈ X) (hpX : ∀ y, projection y ∈ X)
    (hp : ∀ y, ∀ v ∈ X, ⟪y - projection y, v - projection y⟫ ≤ 0)
    (hsub : ∀ x ∈ X, ∀ y ∈ X, f x - f y ≤ ⟪∫ ω, g x ω ∂(ν : Measure Ω), x - y⟫)
    (hgi : ∀ x ∈ X, Integrable (g x) (ν : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (ν : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(ν : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    {u : Vector q.d} (hu : u ∈ X) (hmin : ∀ x ∈ X, f u ≤ f x) {D : ℝ} (hD : 0 < D)
    (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D) :
    (P : Measure (ℕ → Ω)) {ξ | 16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T <
      f (terminal q g projection ξ) - f u} ≤ ENNReal.ofReal q.δ := by
  let A : Set (Fin q.T → Ω) := {ξ | 16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T <
    f (iterateSamples (transition q g projection) q.T (0, q.x0, 0) ξ).2.1 - f u}
  let Φ := fun ξ : ℕ → Ω => fun i : Fin q.T => ξ (2 * i.val)
  have hΦ : MeasurePreserving Φ (P : Measure (ℕ → Ω)) (Measure.pi fun _ : Fin q.T => (ν : Measure Ω)) := by
    simpa only [Nat.zero_add] using FixedBatchConfidence.iid_finite_block_law (even_samples_iid hIID) 0 q.T
  have hi : Measurable (fun ξ : Fin q.T → Ω =>
      (iterateSamples (transition q g projection) q.T (0, q.x0, 0) ξ).2.1) :=
    ((GapStrongGrowth.iterateSamples_measurable (transition_measurable q hg hpm) q.T).comp
      (measurable_const.prodMk measurable_id)).snd.fst
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((hfm.comp hi).sub_const (f u))
  have houtput (ξ : ℕ → Ω) : terminal q g projection ξ =
      (iterateSamples (transition q g projection) q.T (0, q.x0, 0) (Φ ξ)).2.1 :=
    run_eq_iterateSamples q g projection q.T 0 q.x0 0 ξ
  have hevent : {ξ : ℕ → Ω | 16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T <
      f (terminal q g projection ξ) - f u} = Φ ⁻¹' A := by
    ext ξ
    change (_ < f (terminal q g projection ξ) - f u) ↔ _
    rw [houtput]
    rfl
  rw [hevent, hΦ.measure_preimage hA.nullMeasurableSet]
  exact finite_accuracy q g projection ν hg hpm hB hG hδ hδ1 hT hX hf hx0 hpX hp hsub hgi hmi hm hu hmin hD hstart hGD

end OracleTemplate.TerminalClipping
