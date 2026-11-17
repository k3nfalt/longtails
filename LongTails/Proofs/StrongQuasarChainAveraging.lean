import LongTails.Proofs.StrongQuasarChainHard
import LongTails.Proofs.SmoothConvexFiniteAveraging
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators
open Classical

namespace LongTails.Proofs.StrongQuasarChainAveraging

open LongTails.Proofs.StrongQuasarChainObjective LongTails.Proofs.StrongQuasarChainHard
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.SmoothConvexFiniteAveraging
open LongTails.Proofs.FiniteSumNondualLowerHiding LongTails.Proofs.FiniteSumNondualLowerExposure
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound
open LongTails.Proofs.SmoothConvexFiniteWall (wall)

noncomputable def simState (S : Shape) (R : ℝ) {d : ℕ} {St : Type*} (π : Fin (S.k + 1) ↪ Fin d)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState S R π query update initial t
    update s (partialField S R π t (query s))

lemma simState_prefix (S : Shape) (R : ℝ) {d : ℕ} {St : Type*} (π ρ : Fin (S.k + 1) ↪ Fin d)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (t : ℕ) (h : ∀ j : Fin (S.k + 1), j.val < t → π j = ρ j) :
    simState S R π query update initial t = simState S R ρ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => h j (by omega))
    simp only [simState, he]
    rw [partialField_prefix S R π ρ t (fun j hj => h j (by omega))]

lemma simState_coupling {S : Shape} (V : S.Valid) (R : ℝ) (hR : 0 < R) {d : ℕ} {St : Type*}
    (π : Fin (S.k + 1) ↪ Fin d) (hxs : ‖xstar S π‖ ≤ R)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (T : ℕ)
    (hgood : ∀ t < T, let x := query (simState S R π query update initial t)
      ‖x‖ < 3 * R → ∀ p : Fin (S.k + 1), t ≤ p.val → |x (π p)| ≤ S.ρ / 2) :
    simState S R π query update initial T =
      (fun s => update s (hardField S R π (query s)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (fun t ht => hgood t (by omega))
    rw [simState, V.partialField_eq π hR hxs T _ (hgood T (by omega)), he,
      Function.iterate_succ_apply']

noncomputable def obs (S : Shape) (R : ℝ) (b : ℕ) {d : ℕ} {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (t : Fin (b + 1)) (π : Fin (S.k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  let s := simState S R π query update initial t.val
  if t.val < b then query s else output s

lemma obs_prefix (S : Shape) (R : ℝ) (b : ℕ) {d : ℕ} {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (t : Fin (b + 1)) (π ρ : Fin (S.k + 1) ↪ Fin d)
    (h : ∀ j : Fin (S.k + 1), j.val < t.val → π j = ρ j) :
    obs S R b query output update initial t π = obs S R b query output update initial t ρ := by
  unfold obs
  rw [simState_prefix S R π ρ query update initial t.val h]

def chainBad (S : Shape) (R : ℝ) (b : ℕ) {d : ℕ} {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (π : Fin (S.k + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (b + 1), 0 < hits (largeSet (3 * R) (S.ρ / 2)
    (obs S R b query output update initial t π)) ((List.ofFn π).drop t.val)

lemma good_small (S : Shape) (R : ℝ) (b : ℕ) {d : ℕ} {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (π : Fin (S.k + 1) ↪ Fin d)
    (hgood : ¬ chainBad S R b query output update initial π)
    (t : Fin (b + 1)) (j : Fin (S.k + 1)) (hj : t.val ≤ j.val)
    (ht : ‖obs S R b query output update initial t π‖ ≤ 3 * R) :
    |obs S R b query output update initial t π (π j)| ≤ S.ρ / 2 := by
  apply not_largeSet_small _ _ _ ht
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ j hj h⟩

noncomputable def tailGap (S : Shape) (b : ℕ) : ℝ :=
  S.μ * StrongQuasarChainScalar.bump 0 / 17 *
    ∑ p ∈ (Finset.univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val), S.scale p ^ 2

lemma good_gap {S : Shape} (V : S.Valid) (R : ℝ) (hR : 0 < R) (b : ℕ)
    (htail : tailGap S b ≤ 14 * R ^ 2) {d : ℕ} {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (π : Fin (S.k + 1) ↪ Fin d) (hxs : ‖xstar S π‖ ≤ R)
    (hgood : ¬ chainBad S R b query output update initial π) :
    tailGap S b ≤ hard S R π
      (output ((fun s => update s (hardField S R π (query s)))^[b] initial)) := by
  have he := simState_coupling V R hR π hxs query update initial b
    (fun t ht hx j hj => by
      have h := good_small S R b query output update initial π hgood ⟨t, by omega⟩ j hj
        (by simpa only [obs, ht, ↓reduceIte] using hx.le)
      simpa only [obs, ht, ↓reduceIte] using h)
  rw [← he]
  set x := output (simState S R π query update initial b)
  by_cases hx : ‖x‖ ≤ 3 * R
  · apply V.hard_gap π hR b x
    intro p hp
    have h := good_small S R b query output update initial π hgood (Fin.last b) p
      (by simpa using hp) (by simpa only [obs, Fin.val_last, lt_self_iff_false, ↓reduceIte] using hx)
    simpa only [obs, Fin.val_last, lt_self_iff_false, ↓reduceIte] using h
  · push Not at hx
    refine le_trans ?_ (wall_le_hard S π hR x)
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * R) hx.le 2
    unfold wall
    nlinarith

lemma chain_bad_count {S : Shape} (R : ℝ) (hR : 0 ≤ R) (b : ℕ) (hb : b ≤ S.k) (D : ℝ)
    (hρ : 0 < S.ρ) (hD : 0 ≤ D) {d : ℕ} (hDs : D + (S.k + 1 : ℕ) ≤ d) {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) :
    D * (∑ w : CoordinateWords d S.k, if chainBad S R b query output update initial
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (b + 1 : ℕ) * (S.k + 1 : ℕ) * ((3 * R) ^ 2 / (S.ρ / 2) ^ 2) *
        Fintype.card (CoordinateWords d S.k) := by
  let bad := fun π : Fin (S.k + 1) ↪ Fin d => chainBad S R b query output update initial π
  have he (w : CoordinateWords d S.k) : bad (coordinateEmbedding w) ↔
      ∃ t : Fin (b + 1), ∃ π : Fin (S.k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (3 * R) (S.ρ / 2)
          (obs S R b query output update initial t π)) (w.val.drop t.val) := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using ht⟩
    · rintro ⟨t, π, hπ, ht⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro j
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) j
      exact ⟨t, by simpa only [hp, ← coordinateEmbedding_labels w] using ht⟩
  let P := fun w : List (Fin d) => ∃ t : Fin (b + 1), ∃ π : Fin (S.k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (3 * R) (S.ρ / 2)
      (obs S R b query output update initial t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d S.k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (S.k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d S.k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := S.k + 1) (3 * R) (S.ρ / 2) D
    (by positivity) (by positivity) hD hDs (fun t : Fin (b + 1) => t.val)
    (fun t => by have := t.isLt; omega) (obs S R b query output update initial)
    (obs_prefix S R b query output update initial)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 4
  ext w
  simp only [Finset.mem_filter, P]

lemma chain_average {S : Shape} (V : S.Valid) (R : ℝ) (hR : 0 < R) (b : ℕ) (hb : b ≤ S.k)
    (htail : tailGap S b ≤ 14 * R ^ 2) (D : ℝ) (hD : 0 < D) {d : ℕ}
    (hDs : D + (S.k + 1 : ℕ) ≤ d)
    (hsize : 2 * ((b + 1 : ℕ) * (S.k + 1 : ℕ) * ((3 * R) ^ 2 / (S.ρ / 2) ^ 2)) ≤ D)
    (hxs : ∀ π : Fin (S.k + 1) ↪ Fin d, ‖xstar S π‖ ≤ R) {St : Type*}
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) :
    tailGap S b * Fintype.card (CoordinateWords d S.k) ≤
      2 * ∑ w : CoordinateWords d S.k, hard S R (coordinateEmbedding w)
        (output ((fun s => update s (hardField S R (coordinateEmbedding w) (query s)))^[b]
          initial)) := by
  let bad := fun w : CoordinateWords d S.k =>
    chainBad S R b query output update initial (coordinateEmbedding w)
  have hb' := chain_bad_count R hR.le b hb D V.hρ0 hD.le hDs query output update initial
  have hcount : 2 * (∑ w, if bad w then (1 : ℝ) else 0) ≤ Fintype.card (CoordinateWords d S.k) := by
    have hc0 : (0 : ℝ) ≤ Fintype.card (CoordinateWords d S.k) := Nat.cast_nonneg _
    have hs := mul_le_mul_of_nonneg_right hsize hc0
    have hsum0 : 0 ≤ ∑ w, if bad w then (1 : ℝ) else 0 :=
      Finset.sum_nonneg (fun w _ => by split_ifs <;> norm_num)
    nlinarith
  have htail0 : 0 ≤ tailGap S b := by
    unfold tailGap
    have := V.hμ0
    have := StrongQuasarChainScalar.bump_zero_lower
    have : 0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val),
      S.scale p ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
    positivity
  exact finite_good_average bad _ _ htail0
    (fun w => V.hard_nonneg (coordinateEmbedding w) hR _)
    (fun w hw => good_gap V R hR b htail query output update initial (coordinateEmbedding w)
      (hxs _) hw) hcount

lemma chain_failure {S : Shape} (V : S.Valid) (R : ℝ) (hR : 0 < R) (b : ℕ) (hb : b ≤ S.k)
    (htail : tailGap S b ≤ 14 * R ^ 2) (D ε : ℝ) (hD : 0 < D) {d : ℕ}
    (hDs : D + (S.k + 1 : ℕ) ≤ d)
    (hsize : 2 * ((b + 1 : ℕ) * (S.k + 1 : ℕ) * ((3 * R) ^ 2 / (S.ρ / 2) ^ 2)) ≤ D)
    (hxs : ∀ π : Fin (S.k + 1) ↪ Fin d, ‖xstar S π‖ ≤ R) (hε : 2 * ε < tailGap S b)
    {St Ω : Type*} [MeasurableSpace Ω]
    (query output : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : Ω → St) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (S.k + 1) ↪ Fin d,
      let loss := fun ω => hard S R π
        (output ((fun s => update s (hardField S R π (query s)))^[b] (initial ω)))
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  by_contra h
  push Not at h
  let loss := fun (w : CoordinateWords d S.k) (ω : Ω) =>
    hard S R (coordinateEmbedding w)
      (output ((fun s => update s (hardField S R (coordinateEmbedding w) (query s)))^[b]
        (initial ω)))
  have hi (w : CoordinateWords d S.k) : Integrable (loss w) (P : Measure Ω) :=
    (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d S.k) : (∫ ω, loss w ω ∂(P : Measure Ω)) ≤ ε :=
    (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, loss w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hp := integral_mono (integrable_const
    (tailGap S b * Fintype.card (CoordinateWords d S.k)))
    (hs.const_mul 2) (fun ω => chain_average V R hR b hb htail D hD hDs hsize hxs
      query output update (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hp
  have hb2 : (∑ w : CoordinateWords d S.k, ∫ ω, loss w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d S.k) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d S.k, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : S.k + 1 ≤ d := by
    have hh : ((S.k + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d S.k) := by
    exact_mod_cast coordinateWords_card_pos d S.k hd
  have hstrict := mul_lt_mul_of_pos_right hε hc
  change _ ≤ 2 * ∑ w : CoordinateWords d S.k, ∫ ω, loss w ω ∂(P : Measure Ω) at hp
  nlinarith only [hp, hb2, hstrict]

end LongTails.Proofs.StrongQuasarChainAveraging
