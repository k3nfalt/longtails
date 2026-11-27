import LongTails.Proofs.SlidingLowerSim
import LongTails.Proofs.SlidingLowerCoins

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.SlidingLowerExposure

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingLowerSim SlidingLowerCoins QuasarCoinLaw

variable {d k : ℕ} {S : Type*}

def coinReveal (i : Fin 2) (b : Bool) : ℕ := if i = 1 ∧ b = true then 1 else 0

lemma active_dep (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (budget : Fin 2 → ℕ) (i : Fin 2) (t : ℕ) :
    ∀ β β' : ℕ → Bool, (∀ s < t, β s = β' s) →
      active H rv pr π β budget i t = active H rv pr π β' budget i t := by
  intro β β' h
  unfold active
  rw [simSeq_coin_dep H rv pr π β β' budget t h]

lemma active_bounds (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (i : Fin 2) (t : ℕ) :
    0 ≤ active H rv pr π β budget i t ∧ active H rv pr π β budget i t ≤ 1 := by
  unfold active
  split_ifs <;> norm_num

lemma exposure_coin (H : Run S d)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) :
    ((simSeq H coinReveal pr π β budget N).exposure : ℝ) =
      ∑ t ∈ Finset.range N,
        active H coinReveal pr π β budget 1 t * (if β t then (1 : ℝ) else 0) := by
  rw [exposure_eq]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fin.sum_univ_two]
  cases β t <;> simp [coinReveal]

lemma exposure_measurable (H : Run S d) (rv : Fin 2 → Bool → ℕ)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (budget : Fin 2 → ℕ) (N : ℕ) :
    Measurable (fun β : ℕ → Bool => ((simSeq H rv pr π β budget N).exposure : ℝ)) :=
  measurable_of_dep N _ (fun β β' h => by rw [simSeq_coin_dep H rv pr π β β' budget N h])

lemma exposure_integral_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (H : Run S d)
    (pr : (Fin (k + 1) ↪ Fin d) → ℕ → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (budget : Fin 2 → ℕ) (N : ℕ) :
    Integrable (fun β : ℕ → Bool => ((simSeq H coinReveal pr π β budget N).exposure : ℝ))
        (coinPath p hp hp1 : Measure (ℕ → Bool)) ∧
      (∫ β, ((simSeq H coinReveal pr π β budget N).exposure : ℝ)
        ∂(coinPath p hp hp1 : Measure (ℕ → Bool))) ≤ p * budget 1 := by
  let P := (coinPath p hp hp1 : Measure (ℕ → Bool))
  have ha (t : ℕ) : Integrable (fun β => active H coinReveal pr π β budget 1 t) P := by
    apply Integrable.of_bound (measurable_of_dep t _ (active_dep H coinReveal pr π budget 1 t)).aestronglyMeasurable 1
    filter_upwards [] with β
    have := active_bounds H coinReveal pr π β budget 1 t
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  have hb (t : ℕ) : Integrable (fun β : ℕ → Bool =>
      active H coinReveal pr π β budget 1 t * (if β t then (1 : ℝ) else 0)) P := by
    apply Integrable.of_bound ((measurable_of_dep (t + 1) _ (fun β β' h => by
      rw [active_dep H coinReveal pr π budget 1 t β β' (fun s hs => h s (by omega)),
        h t (by omega)])).aestronglyMeasurable) 1
    filter_upwards [] with β
    have := active_bounds H coinReveal pr π β budget 1 t
    cases β t <;> simp [abs_of_nonneg this.1, this.2]
  have he : (fun β : ℕ → Bool => ((simSeq H coinReveal pr π β budget N).exposure : ℝ)) =
      fun β => ∑ t ∈ Finset.range N,
        active H coinReveal pr π β budget 1 t * (if β t then (1 : ℝ) else 0) := by
    funext β
    exact exposure_coin H pr π β budget N
  rw [he]
  refine ⟨integrable_finsetSum _ (fun t _ => hb t), ?_⟩
  rw [integral_finsetSum _ (fun t _ => hb t)]
  have hs : ∀ t ∈ Finset.range N,
      (∫ β, active H coinReveal pr π β budget 1 t * (if β t then (1 : ℝ) else 0) ∂P) =
        p * ∫ β, active H coinReveal pr π β budget 1 t ∂P := fun t _ =>
    adapted_coin_integral hp hp1 t _ (active_dep H coinReveal pr π budget 1 t)
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, ← integral_finsetSum _ (fun t _ => ha t)]
  apply mul_le_mul_of_nonneg_left _ hp
  have hle : (∫ β, ∑ t ∈ Finset.range N, active H coinReveal pr π β budget 1 t ∂P) ≤
      ∫ _β, (budget 1 : ℝ) ∂P :=
    integral_mono (integrable_finsetSum _ (fun t _ => ha t)) (integrable_const _)
      (fun β => active_sum_le H coinReveal pr π β budget 1 N)
  have hP : IsProbabilityMeasure P := inferInstance
  simpa [integral_const, probReal_univ] using hle

end LongTails.Proofs.SlidingLowerExposure
