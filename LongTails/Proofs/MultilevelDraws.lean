import LongTails.Proofs.MultilevelInformation
import LongTails.Proofs.DistributedSampling
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultilevelDraws

open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState

variable {p : Params}

abbrev Column (p : Params) := Fin p.n → p.Ω

noncomputable def columnLaw (μ : Fin p.n → ProbabilityMeasure p.Ω) : Measure (Column p) :=
  Measure.pi fun i => (μ i : Measure _)

instance (μ : Fin p.n → ProbabilityMeasure p.Ω) : IsProbabilityMeasure (columnLaw μ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

noncomputable def timeline (μ : Fin p.n → ProbabilityMeasure p.Ω) : Measure (ℕ → Column p) :=
  Measure.infinitePi fun _ => columnLaw μ

instance (μ : Fin p.n → ProbabilityMeasure p.Ω) : IsProbabilityMeasure (timeline μ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))

def actual (t : Script p) (xs : Samples p) (k : ℕ) : p.Ω := xs (t.worker k) (ordinal t k)
def columns (t : Script p) (xs : ℕ → Column p) (k : ℕ) : p.Ω := xs k (t.worker k)

lemma ordinal_strict (t : Script p) {j k : ℕ} (hj : j < k) (hw : t.worker j = t.worker k) :
    ordinal t j < ordinal t k := by
  have hc : count t (t.worker k) (j+1) ≤ count t (t.worker k) k :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hj))
  rw [count_succ, hw] at hc
  unfold ordinal
  rw [hw]
  simpa [count] using hc

lemma coordinate_injective (t : Script p) : Function.Injective (fun k => (t.worker k, ordinal t k)) := by
  intro a b he
  rw [Prod.mk.injEq] at he
  rcases lt_trichotomy a b with h | h | h
  · exact ((ordinal_strict t h he.1).ne he.2).elim
  · exact h
  · exact ((ordinal_strict t h he.1.symm).ne he.2.symm).elim

lemma actual_preserving (t : Script p) (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P) :
    MeasurePreserving (actual t) P (Measure.infinitePi fun k => (μ (t.worker k) : Measure _)) := by
  have h := (DistributedSampling.independent_coordinates p P μ hw hIID).precomp (coordinate_injective t)
  have hm (k : ℕ) : Measurable (fun s : Samples p => actual t s k) := (hIID _).measurable _
  refine ⟨Measurable.of_eval hm, ?_⟩
  change P.map (fun s k => s (t.worker k) (ordinal t k)) = _
  simpa only [Function.comp_apply, actual, (hIID _).marginal] using h.map_fun_eq_infinitePi_map hm

lemma columns_preserving (t : Script p) (μ : Fin p.n → ProbabilityMeasure p.Ω) :
    MeasurePreserving (columns t) (timeline μ) (Measure.infinitePi fun k => (μ (t.worker k) : Measure _)) := by
  have mm (k : ℕ) : MeasurePreserving (fun (s : ℕ → Column p) => columns t s k) (timeline μ)
      (μ (t.worker k) : Measure _) := by
    have h₁ : MeasurePreserving (fun (s : ℕ → Column p) => s k) (timeline μ) (columnLaw μ) :=
      ⟨measurable_pi_apply k, Measure.infinitePi_map_eval _ k⟩
    have h₂ : MeasurePreserving (fun x : Column p => x (t.worker k)) (columnLaw μ) (μ (t.worker k) : Measure _) :=
      measurePreserving_eval (μ := fun i : Fin p.n => (μ i : Measure p.Ω)) (t.worker k)
    exact h₂.comp h₁
  have h : iIndepFun (fun k (s : ℕ → Column p) => columns t s k) (timeline μ) :=
    iIndepFun_infinitePi (X := fun k (v : Column p) => v (t.worker k)) (fun k => measurable_pi_apply _)
  exact ⟨Measurable.of_eval fun k => (mm k).measurable,
    by simpa only [(mm _).map_eq] using h.map_fun_eq_infinitePi_map (fun k => (mm k).measurable)⟩

noncomputable def row (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p) (draw : ℕ → p.Ω)
    (k : ℕ) : Bits :=
  let bs := t.request k (fun j => if _h : j < k ∧ t.finish j ≤ t.start k then row t g draw j else [])
  let i := t.worker k
  let q := t.decode bs
  t.encode bs (g i q.1 (draw k), g i q.2 (draw k))
termination_by k

lemma row_eq (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p) (draw : ℕ → p.Ω) (k : ℕ) :
    let bs := payload t (row t g draw) k
    let q := t.decode bs
    let i := t.worker k
    row t g draw k = t.encode bs (g i q.1 (draw k), g i q.2 (draw k)) := by
  dsimp only
  conv_lhs => unfold row
  rfl

lemma reply_row (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p) (xs : Samples p) (k : ℕ) :
    reply t g xs k = row t g (actual t xs) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hb : payload t (reply t g xs) k = payload t (row t g (actual t xs)) k := by
      unfold payload
      apply congrArg
      funext j
      by_cases h : j < k ∧ t.finish j ≤ t.start k <;> simp [h,ih]
    rw [reply_eq, row_eq t g (actual t xs) k, hb]
    rfl

lemma row_past (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p)
    (x y : ℕ → p.Ω) (k : ℕ) (h : ∀ j ≤ k, x j = y j) :
    row t g x k = row t g y k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hb : payload t (row t g x) k = payload t (row t g y) k := by
      unfold payload
      apply congrArg
      funext j
      by_cases he : j < k ∧ t.finish j ≤ t.start k
      · simp [he, ih j he.1 (fun l hl => h l (hl.trans he.1.le))]
      · simp [he]
    rw [row_eq t g x k, row_eq t g y k, hb,h k le_rfl]

end LongTails.Proofs.MultilevelDraws
