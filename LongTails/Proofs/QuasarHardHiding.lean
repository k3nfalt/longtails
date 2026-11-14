import LongTails.Proofs.QuasarHardInstance
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical
open scoped BigOperators

namespace LongTails.Proofs.QuasarHardHiding

open QuasarHardInstance SmoothConvexFiniteHiding FiniteSumNondualLowerHiding
open FiniteSumNondualLowerExposure FiniteSumNondualLowerAveraging

variable {d k : ℕ} {S : Type*}

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure HardData (d : ℕ) where
  L : ℝ
  a : ℝ
  η : ℝ
  μ : ℝ
  ρ : ℝ
  x0 : Point d
  proj : Point d → Point d

noncomputable def reply (H : HardData d) (π : Fin (k + 1) ↪ Fin d) (q : Fin 2 × Point d) :
    Point d :=
  if q.1 = 0 then (if ‖q.2 - H.x0‖ ≤ H.ρ then hardField H.L H.a H.η H.μ π (q.2 - H.x0) else 0)
  else H.proj q.2

noncomputable def partialReply (H : HardData d) (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (q : Fin 2 × Point d) : Point d :=
  if q.1 = 0 then
    (if ‖q.2 - H.x0‖ ≤ H.ρ then partialHardField H.L H.a H.η H.μ π r (q.2 - H.x0) else 0)
  else H.proj q.2

noncomputable def simState (H : HardData d) (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (update : S → Point d → S) (init : S) : ℕ → S
  | 0 => init
  | t + 1 =>
    let s := simState H π query update init t
    update s (partialReply H π t (query s))

lemma simState_prefix (H : HardData d) (π π' : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (update : S → Point d → S) (init : S) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val < t → π j = π' j) :
    simState H π query update init t = simState H π' query update init t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => h j (by omega))
    simp only [simState, he]
    unfold partialReply
    rw [partialHardField_prefix H.L H.a H.η H.μ π π' t (fun j hj => h j (by omega))]

noncomputable def observation (H : HardData d) (K : ℕ) (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S)
    (j : Fin (K + 1) × Bool) : Point d :=
  let s := simState H π query update init j.1.val
  if j.2 then (query s).2 - H.x0 else output s - H.x0

lemma observation_prefix (H : HardData d) (K : ℕ) (π π' : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S)
    (j : Fin (K + 1) × Bool) (h : ∀ z : Fin (k + 1), z.val < j.1.val → π z = π' z) :
    observation H K π query output update init j = observation H K π' query output update init j := by
  unfold observation
  rw [simState_prefix H π π' query update init j.1.val h]

def isBad (H : HardData d) (K : ℕ) (θ : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S) :
    Prop :=
  ∃ j : Fin (K + 1) × Bool, 0 < hits
    (largeSet H.ρ θ (observation H K π query output update init j)) ((List.ofFn π).drop j.1.val)

lemma good_query_small (H : HardData d) (K : ℕ) (θ : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S)
    (hgood : ¬ isBad H K θ π query output update init) (t : ℕ) (ht : t ≤ K)
    (hx : ‖(query (simState H π query update init t)).2 - H.x0‖ ≤ H.ρ)
    (i : Fin (k + 1)) (hi : t ≤ i.val) :
    |((query (simState H π query update init t)).2 - H.x0) (π i)| ≤ θ := by
  apply not_largeSet_small H.ρ θ _ hx
  intro hm
  apply hgood
  refine ⟨(⟨t, by omega⟩, true), ?_⟩
  apply hits_drop_positive π t _ i hi
  simpa [observation] using hm

lemma good_output_small (H : HardData d) (K : ℕ) (θ : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S)
    (hgood : ¬ isBad H K θ π query output update init) (t : ℕ) (ht : t ≤ K)
    (hx : ‖output (simState H π query update init t) - H.x0‖ ≤ H.ρ)
    (i : Fin (k + 1)) (hi : t ≤ i.val) :
    |(output (simState H π query update init t) - H.x0) (π i)| ≤ θ := by
  apply not_largeSet_small H.ρ θ _ hx
  intro hm
  apply hgood
  refine ⟨(⟨t, by omega⟩, false), ?_⟩
  apply hits_drop_positive π t _ i hi
  simpa [observation] using hm

lemma simState_coupling (H : HardData d) (K : ℕ) (θ : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S)
    (ha : 0 < H.a) (hη : 0 ≤ H.η) (hη1 : H.η ≤ 1 / 5) (hθ : θ ≤ H.a * H.η / 4)
    (hgood : ¬ isBad H K θ π query output update init) (t : ℕ) (ht : t ≤ K) :
    simState H π query update init t =
      (fun s => update s (reply H π (query s)))^[t] init := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ← ih (by omega)]
    simp only [simState]
    congr 1
    unfold partialReply reply
    split_ifs with h0 h1
    · apply partialHardField_eq H.L H.a H.η H.μ ha hη hη1 π t
      intro j hj
      exact (good_query_small H K θ π query output update init hgood t (by omega) h1 j hj).trans hθ
    · rfl
    · rfl

lemma bad_count (H : HardData d) (K : ℕ) (θ D : ℝ) (hρ : 0 ≤ H.ρ) (hθ : 0 < θ) (hD : 0 ≤ D)
    (hDs : D + (k + 1 : ℕ) ≤ d) (hK : K ≤ k + 1)
    (query : S → Fin 2 × Point d) (output : S → Point d) (update : S → Point d → S) (init : S) :
    D * (∑ w : CoordinateWords d k,
      if isBad H K θ (coordinateEmbedding w) query output update init then (1 : ℝ) else 0) ≤
      (2 * ((K : ℝ) + 1)) * (k + 1 : ℕ) * (H.ρ ^ 2 / θ ^ 2) *
        Fintype.card (CoordinateWords d k) := by
  have he (w : CoordinateWords d k) :
      isBad H K θ (coordinateEmbedding w) query output update init ↔
      ∃ j : Fin (K + 1) × Bool, ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet H.ρ θ (observation H K π query output update init j))
          (w.val.drop j.1.val) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro i
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) i
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (K + 1) × Bool, ∃ π : Fin (k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet H.ρ θ
      (observation H K π query output update init j)) (w.drop j.1.val)
  have hs : (∑ w : CoordinateWords d k,
      if isBad H K θ (coordinateEmbedding w) query output update init then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) H.ρ θ D hρ hθ hD hDs
    (fun j : Fin (K + 1) × Bool => j.1.val) (fun j => by have := j.1.isLt; omega)
    (fun j π => observation H K π query output update init j)
    (fun j π ρ' hπ => observation_prefix H K π ρ' query output update init j hπ)
  have hJ : (Fintype.card (Fin (K + 1) × Bool) : ℝ) = 2 * ((K : ℝ) + 1) := by
    simp [Fintype.card_prod]; ring
  rw [hJ] at h
  simp only [CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1

end LongTails.Proofs.QuasarHardHiding
