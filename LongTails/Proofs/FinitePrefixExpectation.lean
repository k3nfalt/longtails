import LongTails.Proofs.FinitePrefixSimulation
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Classical
open scoped BigOperators

namespace LongTails.Proofs.FinitePrefixExpectation

open FinitePrefixSimulation FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound

variable {d k : ℕ} {S : Type*}

lemma average_loss (B θ D gap : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (hD : 0 < D) (hgap : 0 ≤ gap)
    (hDs : D + (k + 1 : ℕ) ≤ d) (hsize : 2 * (k + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2) ≤ D)
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (reply : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (loss : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hp : ∀ π ρ r x, (∀ i, i.val ≤ r → π i = ρ i) → partialReply π r x = partialReply ρ r x)
    (heq : ∀ π r x, r < k → (‖x‖ < B → ∀ i, r ≤ i.val → |x (π i)| ≤ θ) → partialReply π r x = reply π x)
    (hn : ∀ π x, 0 ≤ loss π x)
    (hnear : ∀ π x, |x (π (Fin.last k))| ≤ θ → gap ≤ loss π x)
    (hfar : ∀ π x, B ≤ ‖x‖ → gap ≤ loss π x)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) :
    gap * Fintype.card (CoordinateWords d k) ≤
      2 * ∑ w : CoordinateWords d k, loss (coordinateEmbedding w)
        (output ((fun s => update s (reply (coordinateEmbedding w) (query s)))^[k] initial)) := by
  let observe := observation partialReply query output update initial
  let isBad := fun w : CoordinateWords d k => bad B θ observe (coordinateEmbedding w)
  have hb := bad_sum_bound B θ D hB hθ hD.le hDs observe
    (observation_prefix partialReply hp query output update initial)
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords d k) := Nat.cast_nonneg _
  have hs := mul_le_mul_of_nonneg_right hsize hcard
  have hb' : 2 * (∑ w : CoordinateWords d k, if isBad w then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords d k) := by
    change D * (∑ w : CoordinateWords d k, if isBad w then (1 : ℝ) else 0) ≤ _ at hb
    nlinarith only [hb, hs, hD]
  apply SmoothConvexFiniteAveraging.finite_good_average isBad _ gap hgap
    (fun w => hn (coordinateEmbedding w) _)
    (fun w hw => good_loss B θ gap partialReply reply loss heq hnear hfar
      (coordinateEmbedding w) query output update initial hw) hb'

lemma exists_failure {Ω : Type*} [MeasurableSpace Ω]
    (B θ D gap ε : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (hD : 0 < D) (hgap : 0 ≤ gap)
    (hDs : D + (k + 1 : ℕ) ≤ d) (hsize : 2 * (k + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2) ≤ D)
    (hε : 2 * ε < gap)
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (reply : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (loss : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hp : ∀ π ρ r x, (∀ i, i.val ≤ r → π i = ρ i) → partialReply π r x = partialReply ρ r x)
    (heq : ∀ π r x, r < k → (‖x‖ < B → ∀ i, r ≤ i.val → |x (π i)| ≤ θ) → partialReply π r x = reply π x)
    (hn : ∀ π x, 0 ≤ loss π x)
    (hnear : ∀ π x, |x (π (Fin.last k))| ≤ θ → gap ≤ loss π x)
    (hfar : ∀ π x, B ≤ ‖x‖ → gap ≤ loss π x)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (k + 1) ↪ Fin d,
      let l := fun ω => loss π (output ((fun s => update s (reply π (query s)))^[k] (initial ω)))
      ¬ (Integrable l (P : Measure Ω) ∧ (∫ ω, l ω ∂(P : Measure Ω)) ≤ ε) := by
  by_contra h
  push Not at h
  let l := fun (w : CoordinateWords d k) (ω : Ω) => loss (coordinateEmbedding w)
    (output ((fun s => update s (reply (coordinateEmbedding w) (query s)))^[k] (initial ω)))
  have hi (w : CoordinateWords d k) : Integrable (l w) (P : Measure Ω) := (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d k) : (∫ ω, l w ω ∂(P : Measure Ω)) ≤ ε := (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, l w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hv := integral_mono (integrable_const (gap * Fintype.card (CoordinateWords d k)))
    (hs.const_mul 2) (fun ω => average_loss B θ D gap hB hθ hD hgap hDs hsize
      partialReply reply loss hp heq hn hnear hfar query output update (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hv
  have hb : (∑ w : CoordinateWords d k, ∫ ω, l w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d k) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d k, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : k + 1 ≤ d := by
    have hh : ((k + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d k) := by
    exact_mod_cast coordinateWords_card_pos d k hd
  have hstrict := mul_lt_mul_of_pos_right hε hc
  change _ ≤ 2 * ∑ w : CoordinateWords d k, ∫ ω, l w ω ∂(P : Measure Ω) at hv
  nlinarith only [hv, hb, hstrict]

end LongTails.Proofs.FinitePrefixExpectation
