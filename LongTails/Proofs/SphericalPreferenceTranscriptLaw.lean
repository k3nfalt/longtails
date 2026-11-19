import LongTails.Proofs.SphericalPreferenceTranscript
import LongTails.Proofs.MultiplicativeRobustSampling
import LongTails.Proofs.ScentExecution

open MeasureTheory Metric Set Filter
open scoped BigOperators

namespace LongTails.Proofs.SphericalPreferenceTranscriptLaw

open LongTails.Proofs.SphericalPreferenceTranscript LongTails.Proofs.SphericalPreferenceHypercube
open LongTails.Setups.SphericalRandomUtility OracleTemplate

variable {S Ω : Type} [MeasurableSpace Ω]

def observed (s : S) (step : S → Bool → S) (test : S → Ω → Bool) :
    (k : ℕ) → (Fin k → Ω) → Words k
  | 0,_ => ()
  | k+1,a =>
    let w := observed s step test k (fun i => a i.castSucc)
    (w,test (state s step k w) (a (Fin.last k)))

omit [MeasurableSpace Ω] in
lemma event_identity (s : S) (step : S → Bool → S) (test : S → Ω → Bool) (k : ℕ) (w : Words k) (b : Bool) :
    {a | observed s step test (k+1) a = (w,b)} =
    (fun a : Fin (k+1) → Ω => ((fun i : Fin k => a i.castSucc),a (Fin.last k))) ⁻¹'
      ({a | observed s step test k a = w} ×ˢ {z | test (state s step k w) z=b}) := by
  ext a
  let v := observed s step test k (fun i => a i.castSucc)
  change ((v,test (state s step k v) (a (Fin.last k))) : Words k × Bool) = (w,b) ↔
    v = w ∧ test (state s step k w) (a (Fin.last k)) = b
  rw [Prod.mk.injEq]
  constructor <;> rintro ⟨h,hb⟩ <;> exact ⟨h,by simpa only [h] using hb⟩

lemma event_measurable (s : S) (step : S → Bool → S) (test : S → Ω → Bool)
    (ht : ∀ x, Measurable (test x)) (k : ℕ) (w : Words k) :
    MeasurableSet {a | observed s step test k a = w} := by
  induction k with
  | zero =>
    change MeasurableSet {a : Fin 0 → Ω | () = w}
    cases w
    simp
  | succ k ih =>
    obtain ⟨w,b⟩ := w
    rw [event_identity]
    exact (show Measurable (fun a : Fin (k+1) → Ω => ((fun i : Fin k => a i.castSucc),a (Fin.last k))) by fun_prop)
      ((ih w).prod ((ht (state s step k w)) (measurableSet_singleton b)))

lemma bool_weight (P : Measure Ω) [IsProbabilityMeasure P] (t : Ω → Bool) (hm : Measurable t) (b : Bool) :
    P.real {z | t z=b} = factor (P.real {z | t z=true}) b := by
  cases b
  · have he : {z | t z=false} = {z | t z=true}ᶜ := by ext z; cases h : t z <;> simp [h]
    rw [he,measureReal_compl (show MeasurableSet {z | t z=true} from hm (measurableSet_singleton true)),probReal_univ]
    rfl
  · rfl

lemma event_probability (P : Measure Ω) [IsProbabilityMeasure P]
    (s : S) (step : S → Bool → S) (test : S → Ω → Bool) (ht : ∀ x, Measurable (test x))
    (k : ℕ) (w : Words k) :
    (Measure.pi fun _ : Fin k => P).real {a | observed s step test k a=w} =
      weight s step (fun x => P.real {z | test x z=true}) k w := by
  induction k with
  | zero =>
    cases w
    change (Measure.pi fun _ : Fin 0 => P).real {a : Fin 0 → Ω | (() : Unit) = ()} = 1
    simp
  | succ k ih =>
    obtain ⟨w,b⟩ := w
    have hl := OracleTemplate.MultiplicativeRobustEstimator.split_last_measurePreserving (P := P) k
    have hm : MeasurableSet ({a | observed s step test k a = w} ×ˢ {z | test (state s step k w) z = b}) :=
      (event_measurable s step test ht k w).prod ((ht (state s step k w)) (measurableSet_singleton b))
    rw [event_identity,measureReal_def,← Measure.map_apply (μ := Measure.pi (fun _ : Fin (k+1) => P)) hl.measurable hm,hl.map_eq,Measure.prod_prod,
      ENNReal.toReal_mul]
    exact congrArg₂ (·*·) (ih w) (bool_weight P _ (ht _) b)

lemma finite_loss (P : Measure Ω) [IsProbabilityMeasure P]
    (s : S) (step : S → Bool → S) (test : S → Ω → Bool) (ht : ∀ x, Measurable (test x))
    (k : ℕ) (L : Words k → ℝ) :
    let law := Measure.pi fun _ : Fin k => P
    Measurable (fun a => L (observed s step test k a)) ∧
      (∫ a, L (observed s step test k a) ∂law) =
        ∑ w, weight s step (fun x => P.real {z | test x z=true}) k w * L w := by
  classical
  let law := Measure.pi fun _ : Fin k => P
  let F := fun (w : Words k) => {a | observed s step test k a=w}.indicator (fun _ => L w)
  have hF (w) : Measurable (F w) := measurable_const.indicator (event_measurable _ _ _ ht _ _)
  have he (a : Fin k → Ω) : L (observed s step test k a) = ∑ w, F w a := by
    simp [F,Set.indicator_apply,Finset.sum_ite_eq]
  simp_rw [he]
  refine ⟨Finset.measurable_sum _ (fun i _ => hF i), ?_⟩
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro w _
    rw [show (∫ a, F w a ∂law) = law.real {a | observed s step test k a=w} * L w by
      simpa [F,smul_eq_mul] using integral_indicator_const (μ := law) (L w) (event_measurable _ _ _ ht k w),
      event_probability]
    exact ht
  · intro w _
    exact (integrable_const (L w)).indicator (event_measurable _ _ _ ht _ _)

omit [MeasurableSpace Ω] in
lemma state_observed (s : S) (step : S → Bool → S) (test : S → Ω → Bool) (z : ℕ → Ω) (k : ℕ) :
    StochasticGradient.advance (fun i x => step x (test x (z i))) k 0 s =
      state s step k (observed s step test k (fun i => z i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Scent.advance_succ_last,ih]
    simp [state,observed]

end LongTails.Proofs.SphericalPreferenceTranscriptLaw
