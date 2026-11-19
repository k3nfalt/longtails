import LongTails.Proofs.MultilevelPacketMoments
import LongTails.Proofs.DistributedCompressionMoments

namespace LongTails.Proofs.MultilevelStream

open MeasureTheory
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport (Bits Script)
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Algorithms.DistributedQuantization (receive message)
open MultilevelDraws MultilevelPacketMoments MultilevelTransportState MultilevelTimetable MultilevelInformation

scoped instance : MeasurableSpace Bits := ⊤
scoped instance : DiscreteMeasurableSpace Bits := ⟨fun _ => trivial⟩

def extend {m : ℕ} (xs : Fin m → Bits) (j : ℕ) : Bits := if h : j < m then xs ⟨j,h⟩ else []

def priorBits (xs : ℕ → Bits) (m : ℕ) : Fin m → Bits := fun j => xs j

lemma extend_eq (xs : ℕ → Bits) (m j : ℕ) (hj : j < m) : extend (priorBits xs m) j = xs j := by
  simp [priorBits,extend,hj]

lemma payload_agree {p : Params} (t : Script p) (k : ℕ) (x y : ℕ → Bits) (h : ∀ j < k, x j = y j) :
    payload t x k = payload t y k := by
  unfold payload
  apply congrArg
  funext j
  by_cases hj : j < k ∧ t.finish j ≤ t.start k <;> simp_all

lemma measurable_code (p : Params) (ds : ℝ) :
    Measurable (message p.d (width p) ds) := by
  apply (measurable_of_countable LongTails.Algorithms.DistributedQuantization.encode).comp
  apply Measurable.of_eval
  intro i
  let M := 2^width p - 1
  let cap := fun n : ℕ => (⟨min n M, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩ : Fin (2^width p))
  have hcap : Measurable cap := measurable_of_countable _
  have hx : Measurable fun x : Point p => x i := (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)
  exact hcap.comp (Nat.measurable_floor.comp ((hx.div_const ds).add_const ((M:ℝ)/2)))

noncomputable def emit (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (i : Fin p.n) (bs : Bits) (z : p.Ω) : Bits :=
  let q := decode p bs
  encode p bs (g i q.1 z,g i q.2 z)

noncomputable def readValue (p : Params) : Bits → Point p :=
  receive p.d (width p) (valueSpacing p)

noncomputable def meanValue (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (i : Fin p.n) (bs : Bits) :=
  ∫ z, readValue p (emit p g i bs z) ∂(μ i : Measure _)

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p}
    {μ : Fin p.n → ProbabilityMeasure p.Ω} {f : Point p → ℝ} {a : ℝ}

lemma measurable_emit (H : Data p f g μ a) (i : Fin p.n) :
    Measurable (Function.uncurry (emit p g i)) := by
  apply measurable_from_prod_countable_right
  intro bs
  have hm (x : Point p) : Measurable (g i x) := (H.oracle i).measurable.comp (measurable_const.prodMk measurable_id)
  unfold Function.uncurry emit encode
  apply (measurable_code _ _).comp
  apply (OracleTemplate.measurable_clip _).comp
  by_cases hs : bs.head? = some true
  · simpa [hs] using hm (decode p bs).1
  · simp only [hs,ite_false]
    exact (hm (decode p bs).1).sub (hm (decode p bs).2)

lemma row_measurable (H : Data p f g μ a) (k : ℕ) :
    Measurable (fun draw => row (script p) g draw k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    let pre := fun draw => priorBits (row (script p) g draw) k
    have hpre : Measurable pre := Measurable.of_eval (fun j => ih j j.isLt)
    let bs := fun (v : Fin k → Bits) => payload (script p) (extend v) k
    have hp (d : ℕ → p.Ω) : bs (pre d) = payload (script p) (row (script p) g d) k :=
      payload_agree _ _ _ _ (extend_eq _ _)
    have hmeas := (measurable_emit H ((script p).worker k)).comp
      (((measurable_of_countable bs).comp hpre).prodMk (measurable_pi_apply k))
    convert hmeas using 1
    funext d
    rw [row_eq]
    simp only [Function.comp_apply,Function.uncurry,hp]
    rfl

lemma read_packet (b : ℕ → Bits) (job : Job) (i : Fin p.n) (z : p.Ω) :
    readValue p (emit p g i (queryBits p b job) z) =
      clippedGrid p (target p b job (fun x => g i x z)) := by
  unfold emit
  rw [decoded_pair]
  unfold readValue encode clippedGrid target
  rw [flag]
  cases h : snapshot p job <;> simp

lemma payload_contains (hh : ∀ i, 0 < p.h i) (b : ℕ → Bits) (r : ℕ) (hr : r < (table p).length) :
    payload (script p) b r = queryBits p b (entry p r).1 := data_at_send p hh b r hr

lemma conditional_moments (H : Data p f g μ a) (hh : ∀ i, 0 < p.h i)
    (r : ℕ) (hr : r < (table p).length) (b : ℕ → Bits) :
    let i := (script p).worker r
    let bs := payload (script p) b r
    let Y := fun z => readValue p (emit p g i bs z)
    let u := target p b (entry p r).1 (gradient f)
    let m := meanValue p g μ i bs
    Integrable Y (μ i : Measure _) ∧
      ‖m-u‖ ≤ 2*precision p/(height p+1 : ℕ) ∧
      Integrable (fun z => ‖Y z-m‖^2) (μ i : Measure _) ∧
      (∫ z, ‖Y z-m‖^2 ∂(μ i : Measure _)) ≤ 4*units p (entry p r).1 * precision p^2 := by
  have hj := (mem_table.mp (show entry p r ∈ table p by rw [entry_at p hr]; exact List.getElem_mem ..)).1
  dsimp only
  rw [payload_contains hh b r hr]
  unfold meanValue
  simp_rw [read_packet]
  exact H.digital b _ hj _

end LongTails.Proofs.MultilevelStream
