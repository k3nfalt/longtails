import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SharpChainHiding

open SmoothConvexFiniteHiding
open FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure FiniteSumNondualLowerAveraging

variable {d k : ℕ} {S R : Type*}

noncomputable def simState (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (π : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S)
    (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let s := simState part π query update initial t
    update s (part π t (query s))

lemma simState_prefix (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hpart : ∀ π ρ : Fin (k + 1) ↪ Fin d, ∀ t, (∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) →
      part π t = part ρ t)
    (π ρ : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S)
    (initial : S) (t : ℕ) (h : ∀ j : Fin (k + 1), j.val < t → π j = ρ j) :
    simState part π query update initial t = simState part ρ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => h j (by omega))
    simp only [simState, he]
    rw [hpart π ρ t (fun j hj => h j (by omega))]

lemma simState_coupling (B θ : ℝ) (full : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → R)
    (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hfull : ∀ π t u, t < k → (‖u‖ ≤ B → ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) →
      full π u = part π t u)
    (π : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S)
    (initial : S) (T : ℕ) (hT : T ≤ k)
    (hgood : ∀ t < T, ‖query (simState part π query update initial t)‖ ≤ B →
      ∀ j : Fin (k + 1), t ≤ j.val → |query (simState part π query update initial t) (π j)| ≤ θ) :
    simState part π query update initial T = (fun s => update s (full π (query s)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (by omega) (fun t ht => hgood t (by omega))
    rw [simState, ← hfull π T _ (by omega) (hgood T (by omega)), he, Function.iterate_succ_apply']

noncomputable def observation (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  let s := simState part π query update initial t.val
  if t.val < k then query s else output s

lemma observation_prefix (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hpart : ∀ π ρ : Fin (k + 1) ↪ Fin d, ∀ t, (∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) →
      part π t = part ρ t)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S) (initial : S)
    (t : Fin (k + 1)) (π ρ : Fin (k + 1) ↪ Fin d)
    (h : ∀ j : Fin (k + 1), j.val < t.val → π j = ρ j) :
    observation part query output update initial t π =
      observation part query output update initial t ρ := by
  unfold observation
  rw [simState_prefix part hpart π ρ query update initial t.val h]

def coordinateBad (B θ : ℝ) (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (k + 1), 0 < hits
    (largeSet B θ (observation part query output update initial t π)) ((List.ofFn π).drop t.val)

lemma good_observation_small (B θ : ℝ)
    (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) (hgood : ¬ coordinateBad B θ part query output update initial π)
    (t j : Fin (k + 1)) (hj : t.val ≤ j.val)
    (hB : ‖observation part query output update initial t π‖ ≤ B) :
    |observation part query output update initial t π (π j)| ≤ θ := by
  apply not_largeSet_small _ _ _ hB
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ j hj h⟩

lemma good_output (B θ : ℝ) (full : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → R)
    (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hfull : ∀ π t u, t < k → (‖u‖ ≤ B → ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) →
      full π u = part π t u)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) (hgood : ¬ coordinateBad B θ part query output update initial π) :
    ‖output ((fun s => update s (full π (query s)))^[k] initial)‖ ≤ B →
      |output ((fun s => update s (full π (query s)))^[k] initial) (π (Fin.last k))| ≤ θ := by
  have he := simState_coupling B θ full part hfull π query update initial k le_rfl
    (fun t ht hB j hj => by
      have h := good_observation_small B θ part query output update initial π hgood
        ⟨t, by omega⟩ j hj (by simpa only [observation, ht, ↓reduceIte] using hB)
      simpa only [observation, ht, ↓reduceIte] using h)
  rw [← he]
  intro hB
  have h := good_observation_small B θ part query output update initial π hgood
    (Fin.last k) (Fin.last k) le_rfl
    (by simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using hB)
  simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using h

lemma bad_sum_bound (B θ D : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (hD : 0 ≤ D)
    (hDs : D + (k + 1 : ℕ) ≤ d)
    (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hpart : ∀ π ρ : Fin (k + 1) ↪ Fin d, ∀ t, (∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) →
      part π t = part ρ t)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S) (initial : S) :
    D * (∑ w : CoordinateWords d k, if coordinateBad B θ part query output update initial
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (k + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2) * Fintype.card (CoordinateWords d k) := by
  let bad := fun π : Fin (k + 1) ↪ Fin d => coordinateBad B θ part query output update initial π
  have he (w : CoordinateWords d k) : bad (coordinateEmbedding w) ↔
      ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet B θ
          (observation part query output update initial t π)) (w.val.drop t.val) := by
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
  let P := fun w : List (Fin d) => ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet B θ
      (observation part query output update initial t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) B θ D
    hB hθ hD hDs (fun t : Fin (k + 1) => t.val)
    (fun t => t.isLt.le) (observation part query output update initial)
    (observation_prefix part hpart query output update initial)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe, pow_two, mul_assoc] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma execution_average (B θ D ε : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (hD : 0 < D)
    (hDs : D + (k + 1 : ℕ) ≤ d) (hsize : 4 * ((k + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2)) ≤ D)
    (hε : 0 ≤ ε)
    (full : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → R)
    (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hpart : ∀ π ρ : Fin (k + 1) ↪ Fin d, ∀ t, (∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) →
      part π t = part ρ t)
    (hfull : ∀ π t u, t < k → (‖u‖ ≤ B → ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) →
      full π u = part π t u)
    (loss : (Fin (k + 1) ↪ Fin d) → S → ℝ) (hnn : ∀ π s, 0 ≤ loss π s)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S)
    (hloss : ∀ π s, (‖output s‖ ≤ B → |output s (π (Fin.last k))| ≤ θ) → 2 * ε ≤ loss π s)
    (initial : S) :
    3 * ε * Fintype.card (CoordinateWords d k) ≤
      2 * ∑ w : CoordinateWords d k, loss (coordinateEmbedding w)
        ((fun s => update s (full (coordinateEmbedding w) (query s)))^[k] initial) := by
  let bad := fun w : CoordinateWords d k =>
    coordinateBad B θ part query output update initial (coordinateEmbedding w)
  let nb : ℝ := ∑ w, if bad w then (1 : ℝ) else 0
  have hb := bad_sum_bound B θ D hB hθ hD.le hDs part hpart query output update initial
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords d k) := Nat.cast_nonneg _
  have hnb : 4 * nb ≤ Fintype.card (CoordinateWords d k) := by
    have h1 : D * (4 * nb) ≤ D * Fintype.card (CoordinateWords d k) := by
      have h2 := mul_le_mul_of_nonneg_right hsize hcard
      change D * nb ≤ _ at hb
      nlinarith
    exact le_of_mul_le_mul_left h1 hD
  have hl (w : CoordinateWords d k) : 2 * ε * (1 - if bad w then (1 : ℝ) else 0) ≤
      loss (coordinateEmbedding w)
        ((fun s => update s (full (coordinateEmbedding w) (query s)))^[k] initial) := by
    by_cases hw : bad w
    · simp only [hw, ↓reduceIte, sub_self, mul_zero]
      exact hnn _ _
    · simp only [hw, ↓reduceIte, sub_zero, mul_one]
      exact hloss _ _ (good_output B θ full part hfull query output update initial _ hw)
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords d k))) =>
    hl w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  change 2 * ε * (Fintype.card (CoordinateWords d k) - nb) ≤ _ at hs
  nlinarith [mul_le_mul_of_nonneg_left hnb hε]

lemma exists_failure {Ω : Type*} [MeasurableSpace Ω] (B θ D ε : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d) (hsize : 4 * ((k + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2)) ≤ D)
    (hε : 0 < ε)
    (full : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → R)
    (part : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → R)
    (hpart : ∀ π ρ : Fin (k + 1) ↪ Fin d, ∀ t, (∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) →
      part π t = part ρ t)
    (hfull : ∀ π t u, t < k → (‖u‖ ≤ B → ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) →
      full π u = part π t u)
    (loss : (Fin (k + 1) ↪ Fin d) → S → ℝ) (hnn : ∀ π s, 0 ≤ loss π s)
    (query output : S → EuclideanSpace ℝ (Fin d)) (update : S → R → S)
    (hloss : ∀ π s, (‖output s‖ ≤ B → |output s (π (Fin.last k))| ≤ θ) → 2 * ε ≤ loss π s)
    (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (k + 1) ↪ Fin d,
      ¬ (Integrable (fun ω => loss π ((fun s => update s (full π (query s)))^[k] (initial ω)))
          (P : Measure Ω) ∧
        (∫ ω, loss π ((fun s => update s (full π (query s)))^[k] (initial ω)) ∂(P : Measure Ω))
          ≤ ε) := by
  by_contra h
  push Not at h
  let L := fun (w : CoordinateWords d k) (ω : Ω) =>
    loss (coordinateEmbedding w)
      ((fun s => update s (full (coordinateEmbedding w) (query s)))^[k] (initial ω))
  have hi (w : CoordinateWords d k) : Integrable (L w) (P : Measure Ω) :=
    (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d k) : (∫ ω, L w ω ∂(P : Measure Ω)) ≤ ε :=
    (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, L w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hp := integral_mono (integrable_const
    (3 * ε * Fintype.card (CoordinateWords d k)))
    (hs.const_mul 2) (fun ω => execution_average B θ D ε hB hθ hD hDs hsize hε.le full part
      hpart hfull loss hnn query output update hloss (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hp
  have hb : (∑ w : CoordinateWords d k, ∫ ω, L w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d k) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d k, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : k + 1 ≤ d := by
    have hh : ((k + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d k) := by
    exact_mod_cast FiniteSumNondualLowerBound.coordinateWords_card_pos d k hd
  change _ ≤ 2 * ∑ w : CoordinateWords d k, ∫ ω, L w ω ∂(P : Measure Ω) at hp
  nlinarith [mul_pos hε hc]

end LongTails.Proofs.SharpChainHiding
