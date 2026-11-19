import LongTails.Proofs.SecondOrderMintyInstance
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.SmoothConvexFiniteAveraging
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SecondOrderMintyHiding

open SecondOrderMintyChain SecondOrderMintyInstance LocalizedMonotoneRadial
open SmoothConvexFiniteHiding FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound

abbrev Query (d : ℕ) := Space d ⊕ Space d
abbrev Reply (d : ℕ) := Space d × (Space d →L[ℝ] Space d)

def point {d : ℕ} (q : Query d) : Space d := Sum.elim id id q

noncomputable def reply {d n : ℕ} (κ r b : ℝ) (π : Fin (n + 1) ↪ Fin d) (q : Query d) :
    Reply d :=
  Sum.elim (fun x => (field κ r b π x, 0)) (fun x => (0, jacobian κ r b π x)) q

noncomputable def partialReply {d n : ℕ} (κ r b : ℝ) (k : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (q : Query d) : Reply d :=
  Sum.elim (fun x => (partialChain κ r k π (radial b x) + κ • (x - radial b x), 0))
    (fun x => (0, (partialJacobian κ r k π (radial b x)).comp (radialJacobian b x) +
      κ • (ContinuousLinearMap.id ℝ (Space d) - radialJacobian b x))) q

lemma partialReply_prefix {d n k : ℕ} (κ r b : ℝ) (π τ : Fin (n + 1) ↪ Fin d) (q : Query d)
    (h : ∀ i : Fin (n + 1), i.val < k + 1 → π i = τ i) :
    partialReply κ r b k π q = partialReply κ r b k τ q := by
  cases q with
  | inl x => simp only [partialReply, Sum.elim_inl, partialChain_prefix κ r π τ _ h]
  | inr x => simp only [partialReply, Sum.elim_inr, partialJacobian_prefix κ r π τ _ h]

lemma reply_eq_partial {d n k : ℕ} (κ r b : ℝ) (hr : 0 < r) (π : Fin (n + 1) ↪ Fin d)
    (q : Query d) (hx : ∀ i : Fin (n + 1), k ≤ i.val → |radial b (point q) (π i)| ≤ r / 4) :
    reply κ r b π q = partialReply κ r b k π q := by
  cases q with
  | inl x =>
    simp only [point, Sum.elim_inl, id] at hx
    simp only [reply, partialReply, Sum.elim_inl, field, chain_eq_partial κ r hr π _ hx]
  | inr x =>
    simp only [point, Sum.elim_inr, id] at hx
    simp only [reply, partialReply, Sum.elim_inr, jacobian, jacobian_eq_partial κ r hr π _ hx]

noncomputable def simulatedState {d n : ℕ} {S : Type*} (κ r b : ℝ)
    (π : Fin (n + 1) ↪ Fin d) (query : S → Query d)
    (update : S → Reply d → S) (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let s := simulatedState κ r b π query update initial t
    update s (partialReply κ r b t π (query s))

lemma simulatedState_prefix {d n : ℕ} {S : Type*} (κ r b : ℝ)
    (π τ : Fin (n + 1) ↪ Fin d) (query : S → Query d)
    (update : S → Reply d → S) (initial : S) (t : ℕ)
    (h : ∀ i : Fin (n + 1), i.val < t → π i = τ i) :
    simulatedState κ r b π query update initial t =
      simulatedState κ r b τ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun i hi => h i (by omega))
    simp only [simulatedState, he]
    rw [partialReply_prefix κ r b π τ _ h]

lemma simulatedState_coupling {d n : ℕ} {S : Type*} (κ r b : ℝ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (query : S → Query d)
    (update : S → Reply d → S) (initial : S) (T : ℕ)
    (hgood : ∀ t < T, ∀ i : Fin (n + 1), t ≤ i.val →
      |radial b (point (query (simulatedState κ r b π query update initial t))) (π i)| ≤ r / 4) :
    simulatedState κ r b π query update initial T =
      (fun s => update s (reply κ r b π (query s)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (fun t ht => hgood t (by omega))
    rw [simulatedState, ← reply_eq_partial κ r b hr π _ (hgood T (by omega)),
      he, Function.iterate_succ_apply']

noncomputable def observation {d n k : ℕ} {S : Type*} (κ r b : ℝ)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  let s := simulatedState κ r b π query update initial t.val
  if t.val < k then radial b (point (query s)) else radial b (output s)

lemma observation_prefix {d n k : ℕ} {S : Type*} (κ r b : ℝ)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S)
    (t : Fin (k + 1)) (π τ : Fin (n + 1) ↪ Fin d)
    (h : ∀ i : Fin (n + 1), i.val < t.val → π i = τ i) :
    observation κ r b query output update initial t π =
      observation κ r b query output update initial t τ := by
  unfold observation
  rw [simulatedState_prefix κ r b π τ query update initial t.val h]

def coordinateBad {d n k : ℕ} {S : Type*} (κ r b B : ℝ)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S)
    (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (k + 1), 0 < hits
    (largeSet B (r / 4) (observation κ r b query output update initial t π))
    ((List.ofFn π).drop t.val)

lemma observation_norm {d n k : ℕ} {S : Type*} (κ r b : ℝ) (hb : 0 < b)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (n + 1) ↪ Fin d) :
    ‖observation κ r b query output update initial t π‖ ≤ 3 * b / 2 := by
  unfold observation
  split_ifs
  · exact radial_bounded b hb _
  · exact radial_bounded b hb _

lemma good_observation_small {d n k : ℕ} {S : Type*} (κ r b : ℝ) (hb : 0 < b)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S)
    (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad (k := k) κ r b (3 * b / 2) query output update initial π)
    (t : Fin (k + 1)) (i : Fin (n + 1)) (hi : t.val ≤ i.val) :
    |observation κ r b query output update initial t π (π i)| ≤ r / 4 := by
  apply not_largeSet_small _ _ _ (observation_norm κ r b hb query output update initial t π)
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ i hi h⟩

lemma good_execution_residual {d n k : ℕ} {S : Type*} (κ r b R : ℝ)
    (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b) (hR : 0 ≤ R) (hbR : 8 * R ≤ b) (hk : k ≤ n)
    (hnr : (n + 1) * r ^ 2 ≤ R ^ 2)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S)
    (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad (k := k) κ r b (3 * b / 2) query output update initial π) :
    3 / 10 * (κ * r) ≤ ‖field κ r b π
      (output ((fun s => update s (reply κ r b π (query s)))^[k] initial))‖ := by
  have he := simulatedState_coupling κ r b hr π query update initial k
    (fun t ht i hi => by
      have h := good_observation_small κ r b hb query output update initial π hgood
        (⟨t, by omega⟩ : Fin (k + 1)) i hi
      simpa only [observation, ht, ↓reduceIte] using h)
  rw [← he]
  have h := good_observation_small κ r b hb query output update initial π hgood
    (Fin.last k) (Fin.last n) hk
  simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
  exact field_floor κ r b R hκ hr hb hR hbR π hnr _ (Fin.last n)
    (by linarith [(abs_le.mp h).2, hr])

lemma bad_sum_bound {d n k : ℕ} {S : Type*} (κ r b D : ℝ)
    (hb : 0 < b) (hr : 0 < r) (hk : k ≤ n) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (query : S → Query d) (output : S → Space d)
    (update : S → Reply d → S) (initial : S) :
    D * (∑ w : CoordinateWords d n, if coordinateBad (k := k) κ r b (3 * b / 2) query output
      update initial (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (k + 1 : ℕ) * (n + 1 : ℕ) * ((3 * b / 2) ^ 2 / (r / 4) ^ 2) *
        Fintype.card (CoordinateWords d n) := by
  classical
  let bad := fun π : Fin (n + 1) ↪ Fin d =>
    coordinateBad (k := k) κ r b (3 * b / 2) query output update initial π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ t : Fin (k + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (3 * b / 2) (r / 4)
          (observation κ r b query output update initial t π)) (w.val.drop t.val) := by
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
  let P := fun w : List (Fin d) => ∃ t : Fin (k + 1), ∃ π : Fin (n + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (3 * b / 2) (r / 4)
      (observation κ r b query output update initial t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) (3 * b / 2) (r / 4) D
    (by positivity) (by positivity) hD hDs (fun t : Fin (k + 1) => t.val)
    (fun t => by have := t.isLt; omega) (observation κ r b query output update initial)
    (observation_prefix κ r b query output update initial)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe, pow_two, mul_assoc] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma execution_average_residual {d n k : ℕ} {S : Type*} (κ r b R D : ℝ)
    (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b) (hR : 0 ≤ R) (hbR : 8 * R ≤ b) (hk : k ≤ n)
    (hnr : (n + 1) * r ^ 2 ≤ R ^ 2)
    (hD : 0 < D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (hsize : 2 * (k + 1 : ℕ) * (n + 1 : ℕ) * ((3 * b / 2) ^ 2 / (r / 4) ^ 2) ≤ D)
    (query : S → Query d) (output : S → Space d) (update : S → Reply d → S) (initial : S) :
    (3 / 10 * (κ * r)) * Fintype.card (CoordinateWords d n) ≤
      2 * ∑ w : CoordinateWords d n, ‖field κ r b (coordinateEmbedding w)
        (output ((fun s => update s (reply κ r b (coordinateEmbedding w) (query s)))^[k]
          initial))‖ := by
  classical
  let bad := fun w : CoordinateWords d n =>
    coordinateBad (k := k) κ r b (3 * b / 2) query output update initial (coordinateEmbedding w)
  have hb' := bad_sum_bound κ r b D hb hr hk hD.le hDs query output update initial
  have hhalf : 2 * (∑ w, if bad w then (1 : ℝ) else 0) ≤ Fintype.card (CoordinateWords d n) := by
    have hs := mul_le_mul_of_nonneg_right hsize
      (Nat.cast_nonneg (Fintype.card (CoordinateWords d n)) : (0 : ℝ) ≤ _)
    nlinarith
  exact SmoothConvexFiniteAveraging.finite_good_average bad _ _ (by positivity)
    (fun _ => norm_nonneg _)
    (fun w hw => good_execution_residual κ r b R hκ hr hb hR hbR hk hnr
      query output update initial (coordinateEmbedding w) hw) hhalf

lemma exists_failure {d n k : ℕ} {S Ω : Type*} [MeasurableSpace Ω]
    (κ r b R D ε : ℝ)
    (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b) (hR : 0 ≤ R) (hbR : 8 * R ≤ b) (hk : k ≤ n)
    (hnr : (n + 1) * r ^ 2 ≤ R ^ 2)
    (hD : 0 < D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (hsize : 2 * (k + 1 : ℕ) * (n + 1 : ℕ) * ((3 * b / 2) ^ 2 / (r / 4) ^ 2) ≤ D)
    (hε : 2 * ε < 3 / 10 * (κ * r))
    (query : S → Query d) (output : S → Space d)
    (update : S → Reply d → S) (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (n + 1) ↪ Fin d,
      let loss := fun ω => ‖field κ r b π
        (output ((fun s => update s (reply κ r b π (query s)))^[k] (initial ω)))‖
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  classical
  by_contra h
  push Not at h
  let loss := fun (w : CoordinateWords d n) (ω : Ω) =>
    ‖field κ r b (coordinateEmbedding w)
      (output ((fun s => update s (reply κ r b (coordinateEmbedding w) (query s)))^[k]
        (initial ω)))‖
  have hi (w : CoordinateWords d n) : Integrable (loss w) (P : Measure Ω) :=
    (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d n) : (∫ ω, loss w ω ∂(P : Measure Ω)) ≤ ε :=
    (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, loss w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hp := integral_mono (integrable_const
    ((3 / 10 * (κ * r)) * Fintype.card (CoordinateWords d n)))
    (hs.const_mul 2) (fun ω => execution_average_residual κ r b R D hκ hr hb hR hbR hk hnr
      hD hDs hsize query output update (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hp
  have hb2 : (∑ w : CoordinateWords d n, ∫ ω, loss w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d n) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d n, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : n + 1 ≤ d := by
    have hh : ((n + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d n) := by
    exact_mod_cast coordinateWords_card_pos d n hd
  have hstrict := mul_lt_mul_of_pos_right hε hc
  change _ ≤ 2 * ∑ w : CoordinateWords d n, ∫ ω, loss w ω ∂(P : Measure Ω) at hp
  nlinarith only [hp, hb2, hstrict]

end LongTails.Proofs.SecondOrderMintyHiding
