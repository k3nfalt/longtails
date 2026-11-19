import LongTails.Proofs.MultilevelStream
import LongTails.Proofs.MultilevelPath

namespace LongTails.Proofs.MultilevelMartingale

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport (Bits)
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Algorithms.MultilevelWorkerSchedule
open MultilevelPath MultilevelPacketMoments MultilevelStream MultilevelTransportState MultilevelDraws
open scoped MultilevelStream

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p}
    {μ : Fin p.n → ProbabilityMeasure p.Ω} {f : Point p → ℝ} {a : ℝ}

noncomputable def noise (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (k m : ℕ) (b : ℕ → Bits) : Point p :=
  ∑ r ∈ Finset.range m, weight p k r •
    (readValue p (b r) - meanValue p g μ ((script p).worker r) (payload (script p) b r))

lemma noise_prefix (k m : ℕ) (b : ℕ → Bits) :
    noise p g μ k m (extend (priorBits b m)) = noise p g μ k m b := by
  apply Finset.sum_congr rfl
  intro r hr
  have h := Finset.mem_range.mp hr
  have he := payload_agree (script p) r _ b (fun j hj => extend_eq b m j (hj.trans h))
  simp only [extend_eq b m r h, he]

noncomputable def history (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (z : ℕ → Column p) : ℕ → Bits :=
  row (script p) g (columns (script p) z)

lemma measurable_history (H : Data p f g μ a) (j : ℕ) : Measurable (fun z => history p g z j) :=
  (row_measurable H j).comp (columns_preserving _ μ).measurable

noncomputable def innovation (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (k r : ℕ) (b : Fin r → Bits) (z : Column p) : Point p :=
  let bs := payload (script p) (extend b) r
  let i := (script p).worker r
  weight p k r • (readValue p (emit p g i bs (z i)) - meanValue p g μ i bs)

lemma centered_row (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i) (k r : ℕ) (hr : r < (table p).length)
    (b : Fin r → Bits) :
    let W := innovation p g μ k r b
    let Q := columnLaw μ
    Integrable W Q ∧ (∫ z, W z ∂Q) = 0 ∧ Integrable (fun z => ‖W z‖^2) Q ∧
      (∫ z, ‖W z‖^2 ∂Q) ≤ weight p k r^2 * (4*units p (entry p r).1*precision p^2) := by
  intro W Q
  let i := (script p).worker r
  let bs := payload (script p) (extend b) r
  let Y := fun x => readValue p (emit p g i bs x)
  let m := meanValue p g μ i bs
  have hP : MeasurePreserving (fun z : Column p => z i) Q (μ i : Measure _) :=
    measurePreserving_eval (μ := fun i : Fin p.n => (μ i : Measure p.Ω)) i
  obtain ⟨hY,_,hY2,hv⟩ := conditional_moments H hh r hr (extend b)
  have hZ : Integrable (fun x => Y x-m) (μ i : Measure _) := hY.sub (integrable_const _)
  have hZi := hP.integrable_comp_of_integrable hZ
  have hZ2 := hP.integrable_comp_of_integrable hY2
  have hZi' : Integrable (fun z : Column p => Y (z i)-m) Q := hZi
  have hZ2' : Integrable (fun z : Column p => ‖Y (z i)-m‖^2) Q := hZ2
  have law : HasLaw (fun z : Column p => z i) (μ i : Measure _) Q := ⟨hP.measurable.aemeasurable,hP.map_eq⟩
  have hm : (∫ z, Y (z i)-m ∂Q) = 0 := by
    have heq := law.integral_comp (f := fun x => Y x - m) hZ.aestronglyMeasurable
    simp only [Function.comp_apply] at heq
    rw [heq,integral_sub (f := Y) hY (integrable_const _)]
    simp [Y,m,meanValue,i]
  have hn (z : Column p) : ‖W z‖^2 = weight p k r ^ 2 * ‖Y (z i)-m‖^2 := by
    change ‖weight p k r • (Y (z i)-m)‖^2 = _
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  refine ⟨hZi'.smul (weight p k r), ?_, ?_, ?_⟩
  · change (∫ z, weight p k r • (Y (z i)-m) ∂Q) = 0
    rw [integral_smul,hm,smul_zero]
  · simp_rw [hn]; exact hZ2'.const_mul _
  · simp_rw [hn]
    have heq := law.integral_comp (f := fun x => ‖Y x-m‖^2) hY2.aestronglyMeasurable
    simp only [Function.comp_apply] at heq
    rw [integral_const_mul,heq]
    exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)

lemma measurable_innovation (H : Data p f g μ a) (k r : ℕ) :
    Measurable (Function.uncurry (innovation p g μ k r)) := by
  apply measurable_from_prod_countable_right
  intro b
  let i := (script p).worker r
  let bs := payload (script p) (extend b) r
  have hp : Measurable (fun z : Column p => (bs,z i)) := measurable_const.prodMk (measurable_pi_apply i)
  have he := (measurable_emit H i).comp hp
  change Measurable (fun z : Column p => emit p g i bs (z i)) at he
  exact (((measurable_of_countable (readValue p)).comp he).sub_const (meanValue p g μ i bs)).const_smul (weight p k r)

lemma noise_energy (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i) (k m : ℕ) (hm : m ≤ (table p).length) :
    let P := timeline μ
    let U := fun z => noise p g μ k m (history p g z)
    Integrable (fun z => ‖U z‖^2) P ∧
      (∫ z, ‖U z‖^2 ∂P) ≤ ∑ j ∈ Finset.range m, weight p k j^2 * (4*units p (entry p j).1*precision p^2) := by
  induction m with
  | zero => simp [noise]
  | succ m ih =>
    obtain ⟨hi,hb⟩ := ih (Nat.le_of_succ_le hm)
    let S := fun z => priorBits (history p g z) m
    let U := fun b : Fin m → Bits => noise p g μ k m (extend b)
    let W := innovation p g μ k m
    let C := weight p k m^2 * (4*units p (entry p m).1*precision p^2)
    have hS : Measurable S := Measurable.of_eval (fun j => measurable_history H j)
    have hdep : ∀ x y : ℕ → Column p, (∀ j < m, x j = y j) → S x = S y := by
      intro x y hxy
      funext j
      exact row_past _ _ _ _ _ (fun i hi => by unfold columns; rw [hxy i (hi.trans_lt j.isLt)])
    have hU (z) : U (S z) = noise p g μ k m (history p g z) := noise_prefix _ _ _
    have hUi : Integrable (fun z => ‖U (S z)‖^2) (timeline μ) := by simpa only [hU] using hi
    have hiid := OracleTemplate.NormalizedStorm.fresh_step_sq (columnLaw μ) m S hS hdep U
      (measurable_of_countable _) W (measurable_innovation H k m)
      (fun b => (centered_row H hh k m hm b).1) (fun b => (centered_row H hh k m hm b).2.1)
      (fun b => (centered_row H hh k m hm b).2.2.1) (fun _ => C)
      (fun b => (centered_row H hh k m hm b).2.2.2) (integrable_const _) hUi 1
    have hu' (z) : U (S z) + W (S z) (z m) = noise p g μ k (m+1) (history p g z) := by
      rw [hU]
      unfold noise W innovation
      rw [Finset.sum_range_succ]
      congr 2
      have hbs := payload_agree (script p) m _ (history p g z) (extend_eq _ m)
      dsimp only [S]
      rw [hbs]
      have he := row_eq (script p) g (columns (script p) z) m
      change history p g z m = emit p g _ (payload (script p) (history p g z) m) ((z m) _) at he
      rw [he]
    simp only [one_smul,one_pow,one_mul,integral_const,probReal_univ] at hiid
    simp_rw [hu'] at hiid
    simp only [hU] at hiid
    refine ⟨hiid.1,?_⟩
    rw [Finset.sum_range_succ]
    exact hiid.2.trans (add_le_add_left hb _)

end LongTails.Proofs.MultilevelMartingale
