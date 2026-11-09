import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.GapStrongGrowthIteration
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.FullRangeLaw

open OracleTemplate.StochasticGeneralized
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

variable {Ω : Type} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

def shift (n : ℕ) (ξ : ℕ → Ω) : ℕ → Ω := fun i => ξ (n + i)

lemma split_lintegral (n : ℕ) {X : Type} [MeasurableSpace X] (A : (ℕ → Ω) → X) (hA : Measurable A)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i < n, ξ i = ξ' i) → A ξ = A ξ')
    (H : X × (ℕ → Ω) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ξ, H (A ξ, shift n ξ) ∂Measure.infinitePi (fun _ : ℕ => p) =
      ∫⁻ ξ, ∫⁻ ξ', H (A ξ, ξ') ∂Measure.infinitePi (fun _ : ℕ => p)
        ∂Measure.infinitePi (fun _ : ℕ => p) := by
  obtain ⟨ω0⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure p
  let μ := Measure.infinitePi fun _ : ℕ => p
  let tail0 : ℕ → Ω := fun _ => ω0
  let e := splitStream (Ω := Ω) n
  let At : (Fin n → Ω) → X := fun w => A (e.symm (w, tail0))
  have hAt : Measurable At := hA.comp (e.symm.measurable.comp (by fun_prop))
  have hagree (ξ : ℕ → Ω) : A ξ = At (fun i => ξ i) := by
    apply hdep
    intro i hi
    change ξ i = (if h : i < n then (fun j : Fin n => ξ j) ⟨i, h⟩ else tail0 (i - n))
    rw [dite_eq_left hi]
  have hs := splitStream_preserving p n
  have hpre := prefix_preserving p n
  have hF : Measurable (fun w : (Fin n → Ω) × (ℕ → Ω) => H (At w.1, w.2)) :=
    hH.comp ((hAt.comp measurable_fst).prodMk measurable_snd)
  have hl : ∫⁻ ξ, H (A ξ, shift n ξ) ∂μ =
      ∫⁻ w, H (At w.1, w.2) ∂(Measure.pi fun _ : Fin n => p).prod μ := by
    have := hs.lintegral_comp hF
    rw [← this]
    refine lintegral_congr fun ξ => ?_
    rw [hagree ξ]
    rfl
  rw [hl, lintegral_prod _ hF.aemeasurable]
  have hG : Measurable (fun w : Fin n → Ω => ∫⁻ ξ', H (At w, ξ') ∂μ) := hF.lintegral_prod_right'
  have := hpre.lintegral_comp hG
  rw [← this]
  refine lintegral_congr fun ξ => ?_
  rw [hagree ξ]

lemma shift_measurable (n : ℕ) : Measurable (shift (Ω := Ω) n) := by
  unfold shift
  fun_prop

section Run

variable {S : Type} [MeasurableSpace S] (adv : S → ℕ → (ℕ → Ω) → S) (c : ℕ → ℕ)

def run : List ℕ → S → (ℕ → Ω) → S
  | [], s, _ => s
  | l :: t, s, ξ => run t (adv s l ξ) (shift (c l) ξ)

def costOf : List ℕ → ℕ
  | [] => 0
  | l :: t => c l + costOf t

variable (hadv : ∀ l, Measurable (fun w : S × (ℕ → Ω) => adv w.1 l w.2))
  (hdep : ∀ s l (ξ ξ' : ℕ → Ω), (∀ i < c l, ξ i = ξ' i) → adv s l ξ = adv s l ξ')

include hadv in
lemma run_measurable (ls : List ℕ) : Measurable (fun w : S × (ℕ → Ω) => run adv c ls w.1 w.2) := by
  induction ls with
  | nil => exact measurable_fst
  | cons l t ih =>
      have hs : Measurable (shift (Ω := Ω) (c l)) := shift_measurable (c l)
      exact ih.comp ((hadv l).prodMk (hs.comp measurable_snd))

omit [MeasurableSpace Ω] [MeasurableSpace S] in
include hdep in
lemma run_dep (ls : List ℕ) (s : S) (ξ ξ' : ℕ → Ω) (h : ∀ i < costOf c ls, ξ i = ξ' i) :
    run adv c ls s ξ = run adv c ls s ξ' := by
  induction ls generalizing s ξ ξ' with
  | nil => rfl
  | cons l t ih =>
      simp only [run]
      rw [hdep s l ξ ξ' (fun i hi => h i (by simp only [costOf]; omega))]
      apply ih
      intro i hi
      exact h (c l + i) (by simp only [costOf]; omega)

include hadv hdep in
lemma tail_lintegral (ls : List ℕ) (s : S) (Ψ : S × (ℕ → Ω) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ ξ, Ψ (run adv c ls s ξ, shift (costOf c ls) ξ) ∂Measure.infinitePi (fun _ : ℕ => p) =
      ∫⁻ ξ, ∫⁻ ξ', Ψ (run adv c ls s ξ, ξ') ∂Measure.infinitePi (fun _ : ℕ => p)
        ∂Measure.infinitePi (fun _ : ℕ => p) :=
  split_lintegral p (costOf c ls) (run adv c ls s)
    ((run_measurable adv c hadv ls).comp measurable_prodMk_left)
    (run_dep adv c hdep ls s) Ψ hΨ


variable {top : ℕ} (ν : Measure (Fin (top + 1))) [IsProbabilityMeasure ν]

noncomputable def advTheta (s : S) (θ : Fin (top + 1) × (ℕ → Ω)) : S := adv s (θ.1 : ℕ) θ.2

include hadv in
omit [IsProbabilityMeasure p] in
lemma advTheta_measurable : Measurable (Function.uncurry (advTheta (top := top) adv)) := by
  have hall : Measurable (fun w : Fin (top + 1) × (S × (ℕ → Ω)) => adv w.2.1 (w.1 : ℕ) w.2.2) :=
    measurable_from_prod_countable_right fun l => hadv (l : ℕ)
  exact hall.comp (show Measurable (fun w : S × (Fin (top + 1) × (ℕ → Ω)) =>
    (w.2.1, (w.1, w.2.2))) from by fun_prop)

include hadv hdep in
lemma level_lintegral (K : ℕ) (s : S) (Φ : S → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ ℓ, ∫⁻ ξ, Φ (run adv c (List.ofFn fun i => ((ℓ i : Fin (top + 1)) : ℕ)) s ξ)
        ∂Measure.infinitePi (fun _ : ℕ => p) ∂Measure.pi (fun _ : Fin K => ν) =
      ∫⁻ θ, Φ (iterateSamples (advTheta (top := top) adv) K s θ)
        ∂Measure.pi (fun _ : Fin K => ν.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  let μ := Measure.infinitePi fun _ : ℕ => p
  induction K generalizing s with
  | zero =>
      have h1 : ∀ ℓ : Fin 0 → Fin (top + 1), ∫⁻ ξ, Φ (run adv c
          (List.ofFn fun i => ((ℓ i : Fin (top + 1)) : ℕ)) s ξ) ∂μ = Φ s := by
        intro ℓ
        simp [run]
      rw [lintegral_congr h1]
      change ∫⁻ _, Φ s ∂_ = ∫⁻ _, Φ s ∂_
      simp
  | succ K ih =>
      let W : S → ℝ≥0∞ := fun s' => ∫⁻ θ, Φ (iterateSamples (advTheta (top := top) adv) K s' θ)
        ∂Measure.pi (fun _ : Fin K => ν.prod μ)
      have hit := OracleTemplate.GapStrongGrowth.iterateSamples_measurable
        (advTheta_measurable (top := top) adv hadv) K
      have hW : Measurable W := (hΦ.comp hit).lintegral_prod_right'
      have hnext (l : Fin (top + 1)) (ℓ' : Fin K → Fin (top + 1)) :
          ∫⁻ ξ, Φ (run adv c (List.ofFn fun i => ((ℓ' i : Fin (top + 1)) : ℕ))
            (adv s (l : ℕ) ξ) (shift (c (l : ℕ)) ξ)) ∂μ =
          ∫⁻ ξ, ∫⁻ ξ', Φ (run adv c (List.ofFn fun i => ((ℓ' i : Fin (top + 1)) : ℕ))
            (adv s (l : ℕ) ξ) ξ') ∂μ ∂μ :=
        split_lintegral p (c (l : ℕ)) (adv s (l : ℕ))
          ((hadv (l : ℕ)).comp measurable_prodMk_left) (hdep s (l : ℕ))
          (fun w => Φ (run adv c (List.ofFn fun i => ((ℓ' i : Fin (top + 1)) : ℕ)) w.1 w.2))
          (hΦ.comp (run_measurable adv c hadv _))
      have hpL := measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => ν) 0
      have hpR := measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => ν.prod μ) 0
      let Gl : Fin (top + 1) × (Fin K → Fin (top + 1)) → ℝ≥0∞ := fun w =>
        ∫⁻ ξ, Φ (run adv c (List.ofFn fun i => ((w.2 i : Fin (top + 1)) : ℕ))
            (adv s (w.1 : ℕ) ξ) (shift (c (w.1 : ℕ)) ξ)) ∂μ
      have hGl : Measurable Gl := Measurable.of_discrete
      have hLeft : ∫⁻ ℓ, ∫⁻ ξ, Φ (run adv c (List.ofFn fun i => ((ℓ i : Fin (top + 1)) : ℕ)) s ξ) ∂μ
          ∂Measure.pi (fun _ : Fin (K + 1) => ν) =
          ∫⁻ w, Gl w ∂ν.prod (Measure.pi fun _ : Fin K => ν) := by
        rw [← hpL.lintegral_comp hGl]
        refine lintegral_congr fun ℓ => ?_
        simp only [List.ofFn_succ, run]
        rfl
      have hslice (l : Fin (top + 1)) :
          ∫⁻ ℓ', Gl (l, ℓ') ∂Measure.pi (fun _ : Fin K => ν) =
            ∫⁻ ξ, W (adv s (l : ℕ) ξ) ∂μ := by
        simp only [Gl, hnext]
        have hjoint : Measurable (fun w : (Fin K → Fin (top + 1)) × (ℕ → Ω) =>
            ∫⁻ ξ', Φ (run adv c (List.ofFn fun i => ((w.1 i : Fin (top + 1)) : ℕ))
              (adv s (l : ℕ) w.2) ξ') ∂μ) := by
          apply measurable_from_prod_countable_right
          intro ℓ'
          have h1 : Measurable (fun w : S × (ℕ → Ω) =>
              Φ (run adv c (List.ofFn fun i => ((ℓ' i : Fin (top + 1)) : ℕ)) w.1 w.2)) :=
            hΦ.comp (run_measurable adv c hadv _)
          exact h1.lintegral_prod_right'.comp ((hadv (l : ℕ)).comp measurable_prodMk_left)
        rw [lintegral_lintegral_swap (μ := Measure.pi fun _ : Fin K => ν) (ν := μ)
          (f := fun (ℓ' : Fin K → Fin (top + 1)) (ξ : ℕ → Ω) =>
          ∫⁻ ξ', Φ (run adv c (List.ofFn fun i => ((ℓ' i : Fin (top + 1)) : ℕ))
            (adv s (l : ℕ) ξ) ξ') ∂μ) hjoint.aemeasurable]
        refine lintegral_congr fun ξ => ?_
        exact ih (adv s (l : ℕ) ξ)
      have hadvT := advTheta_measurable (top := top) adv hadv
      have hWθ : Measurable (fun θ : Fin (top + 1) × (ℕ → Ω) => W (advTheta adv s θ)) :=
        hW.comp (hadvT.comp measurable_prodMk_left)
      have hRight : ∫⁻ θ, Φ (iterateSamples (advTheta (top := top) adv) (K + 1) s θ)
          ∂Measure.pi (fun _ : Fin (K + 1) => ν.prod μ) =
          ∫⁻ θ, W (advTheta adv s θ) ∂ν.prod μ := by
        let Gr : (Fin (top + 1) × (ℕ → Ω)) × (Fin K → Fin (top + 1) × (ℕ → Ω)) → ℝ≥0∞ := fun w =>
          Φ (iterateSamples (advTheta (top := top) adv) K (advTheta adv s w.1) w.2)
        have hGr : Measurable Gr := hΦ.comp (hit.comp
          ((hadvT.comp ((measurable_const.prodMk measurable_fst))).prodMk measurable_snd))
        rw [show (∫⁻ θ, Φ (iterateSamples (advTheta (top := top) adv) (K + 1) s θ)
            ∂Measure.pi (fun _ : Fin (K + 1) => ν.prod μ)) =
            ∫⁻ θ, Gr (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) =>
              Fin (top + 1) × (ℕ → Ω)) 0 θ) ∂Measure.pi (fun _ : Fin (K + 1) => ν.prod μ) from rfl,
          hpR.lintegral_comp hGr, lintegral_prod _ hGr.aemeasurable]
      rw [hLeft, hRight, lintegral_prod _ hGl.aemeasurable, lintegral_prod _ hWθ.aemeasurable]
      refine lintegral_congr fun l => ?_
      exact hslice l

end Run

end LongTails.Proofs.FullRangeLaw
