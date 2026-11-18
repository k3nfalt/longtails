import LongTails.Proofs.MarkovFrontierOccupancy
import LongTails.Proofs.AbcHardExecution
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovFrontierSimulation

open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask
open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution (simReply simReply_prefix simReply_outside reply_outside)
open MarkovFrontierProgress

abbrev Color := Option (Fin 2)

def parity (m : ℕ) : Fin 2 := ⟨m % 2, Nat.mod_lt _ (by decide)⟩

def gate (m : ℕ) (c : Color) : ℝ := if c = some (parity m) then 0 else 2

variable {d n : ℕ}

noncomputable def response (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 x : Space d) (c : Color) : Space d :=
  reply S (fun _ => q) π x0 x (gate (stage (sel π (toUnit S x0 x))) c)

noncomputable def partialResponse (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (r : ℕ) (x0 x : Space d) (c : Color) : Space d :=
  simReply S (fun _ => q) π r x0 x (gate (stageUpTo r (sel π (toUnit S x0 x))) c)

lemma partialResponse_prefix (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d)
    (r : ℕ) (x0 x : Space d) (c : Color)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) :
    partialResponse S q π r x0 x c = partialResponse S q ρ r x0 x c := by
  have hs : ∀ i : Fin (n + 1), i.val < r →
      sel π (toUnit S x0 x) i = sel ρ (toUnit S x0 x) i := by
    intro i hi
    rw [sel_apply, sel_apply, h i hi]
  unfold partialResponse
  rw [stageUpTo_congr r _ _ hs, simReply_prefix S _ π ρ r x0 x _ h]

lemma response_eq_partial (S : Scale) (q : ℝ) (hq : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d) (c : Color)
    (h : ‖toUnit S x0 x‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), r ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4) :
    response S q π x0 x c = partialResponse S q π (advance r c) x0 x c := by
  let w := toUnit S x0 x
  by_cases hw : 2 * radius n ≤ ‖w‖
  · exact (reply_outside S _ π x0 x _ hw).trans (simReply_outside S _ π _ x0 x _ hw).symm
  have hs := h (le_of_not_ge hw)
  have hr := (advance_bounds r c).1
  have hs' : ∀ i : Fin (n + 1), advance r c ≤ i.val → |sel π w i| ≤ 1 / 4 :=
    fun i hi => hs i (hr.trans hi)
  have he := stageUpTo_eq (advance r c) (sel π w) hs'
  have hm : stage (sel π w) ≤ r := by
    rw [← stageUpTo_eq r _ hs]
    exact stageUpTo_le _ _
  unfold response partialResponse simReply reply
  dsimp only [w] at he hm hs' ⊢
  rw [he]
  split_ifs with hlt
  · rw [objGrad, visibleGrad_eq π _ w (fun i hi => small_of_stage _ i hi)]
  · have heq : stage (sel π (toUnit S x0 x)) = r := by omega
    have hc : c ≠ some (parity r) := by
      intro hc
      have ha : advance r c = r + 1 := ite_eq_left hc
      omega
    rw [heq]
    simp [gate, hc, coin, show ¬ (2 : ℝ) ≤ q by linarith]

variable {St : Type*}

noncomputable def simulated (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) (query : St → Space d) (update : St → Space d → St)
    (initial : St) (colors : ℕ → Color) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simulated S q π x0 query update initial colors t
    update s (partialResponse S q π (level colors (t + 1)) x0 (query s) (colors t))

lemma simulated_prefix (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) (query : St → Space d) (update : St → Space d → St)
    (initial : St) (colors : ℕ → Color) (t : ℕ)
    (h : ∀ i : Fin (n + 1), i.val < level colors t → π i = ρ i) :
    simulated S q π x0 query update initial colors t =
      simulated S q ρ x0 query update initial colors t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm : level colors t ≤ level colors (t + 1) := (advance_bounds _ _).1
    simp only [simulated]
    rw [ih (fun i hi => h i (hi.trans_le hm)), partialResponse_prefix S q π ρ _ _ _ _ h]

noncomputable def actual (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) (query : St → Space d) (update : St → Space d → St)
    (initial : St) (colors : ℕ → Color) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := actual S q π x0 query update initial colors t
    update s (response S q π x0 (query s) (colors t))

lemma coupling (S : Scale) (q : ℝ) (hq : q ≤ 1) (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) (query : St → Space d) (update : St → Space d → St)
    (initial : St) (colors : ℕ → Color) (N : ℕ)
    (hs : ∀ t < N, let w := toUnit S x0 (query (simulated S q π x0 query update initial colors t))
      ‖w‖ ≤ 2 * radius n → ∀ i : Fin (n + 1), level colors t ≤ i.val → |sel π w i| ≤ 1 / 4) :
    actual S q π x0 query update initial colors N = simulated S q π x0 query update initial colors N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [actual, simulated]
    rw [ih (fun t ht => hs t (by omega))]
    rw [response_eq_partial S q hq π (level colors N) x0 _ _ (hs N (by omega))]
    rfl

end LongTails.Proofs.MarkovFrontierSimulation

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovFrontierHiding

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask
open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.MarkovFrontierSimulation LongTails.Proofs.MarkovFrontierProgress
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging

variable {d n : ℕ} {St : Type*}

noncomputable def observation (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → Color) (N : ℕ) (j : Fin (N + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  if j.val < N then
    toUnit S x0 (query (simulated S q π x0 query update initial ω j.val))
  else toUnit S x0 (output (simulated S q π x0 query update initial ω j.val))

lemma observation_prefix (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → Color) (N : ℕ) (j : Fin (N + 1)) (π ρ : Fin (n + 1) ↪ Fin d)
    (h : ∀ k : Fin (n + 1), k.val < level ω j.val → π k = ρ k) :
    observation S q x0 query output update initial ω N j π =
      observation S q x0 query output update initial ω N j ρ := by
  unfold observation
  rw [simulated_prefix S q π ρ x0 query update initial ω j.val h]

def coordinateBad (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → Color) (N : ℕ) (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits
    (largeSet (2 * radius n) (1 / 4)
      (observation S q x0 query output update initial ω N j π))
    ((List.ofFn π).drop (level ω j.val))

lemma good_small (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → Color) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S q x0 query output update initial ω N π)
    (j : Fin (N + 1))
    (hj : ‖observation S q x0 query output update initial ω N j π‖ ≤ 2 * radius n)
    (i : Fin (n + 1)) (hi : level ω j.val ≤ i.val) :
    |sel π (observation S q x0 query output update initial ω N j π) i| ≤ 1 / 4 := by
  rw [sel_apply]
  apply not_largeSet_small _ _ _ hj
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ i hi h⟩

lemma bad_sum_bound (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → Color) (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (hlev : level ω N ≤ n + 1) :
    D * (∑ w : CoordinateWords d n, if coordinateBad S q x0 query output update initial ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (n + 1 : ℕ) * ((2 * radius n) ^ 2 / (1 / 4) ^ 2) *
        Fintype.card (CoordinateWords d n) := by
  let bad := fun π : Fin (n + 1) ↪ Fin d =>
    coordinateBad S q x0 query output update initial ω N π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (2 * radius n) (1 / 4)
          (observation S q x0 query output update initial ω N j π))
          (w.val.drop (level ω j.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro k
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) k
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (2 * radius n) (1 / 4)
      (observation S q x0 query output update initial ω N j π))
      (w.drop (level ω j.val))
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) (2 * radius n) (1 / 4) D
    (by have := radius_pos n; positivity) (by norm_num) hD hDs
    (fun j : Fin (N + 1) => level ω j.val) (fun j => (level_mono ω (show j.val ≤ N by omega)).trans hlev)
    (observation S q x0 query output update initial ω N)
    (observation_prefix S q x0 query output update initial ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma good_gradient (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → Color) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S q x0 query output update initial ω N π)
    (hlev : level ω N < n + 1)
    (hq : q ≤ 1) :
    S.a / S.lam / 20 ≤
      ‖objGrad S π x0 (output (actual S q π x0 query update initial ω N))‖ := by
  have hhit : ∀ t < N,
      let x := query (simulated S q π x0 query update initial ω t)
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), level ω t ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4 := by
    intro t ht x hx i hi
    have h := good_small S q x0 query output update initial ω N π hgood ⟨t, by omega⟩
    simp only [observation, ht, ↓reduceIte] at h
    exact h hx i hi
  rw [coupling S q hq π x0 query update initial ω N hhit]
  have hpos : 0 ≤ S.a / S.lam := by have := S.ha; have := S.hlam; positivity
  rw [objGrad, norm_smul, Real.norm_of_nonneg hpos]
  set w := toUnit S x0 (output (simulated S q π x0 query update initial ω N))
  have hR := radius_pos n
  by_cases hw : 2 * radius n < ‖w‖
  · rw [hardGrad_outside π w hw.le, wallGrad_norm]
    have : 4 ≤ 2 * ‖w‖ / radius n := by rw [le_div_iff₀ hR]; linarith
    nlinarith
  · push Not at hw
    have h := good_small S q x0 query output update initial ω N π hgood (Fin.last N)
    simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    have hl := h hw (Fin.last n) (by simp; omega)
    have hg := hardGrad_lower π w (lt_of_le_of_lt hl (by norm_num))
    nlinarith

end LongTails.Proofs.MarkovFrontierHiding
