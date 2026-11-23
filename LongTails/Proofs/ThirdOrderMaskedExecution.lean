import LongTails.Proofs.ThirdOrderMaskedOracle
import LongTails.Proofs.AbcHardExecution
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ThirdOrderMaskedExecution

open Classical
open LongTails.Proofs.ThirdOrderMaskedOracle
open LongTails.Proofs.RelativeHessianLocalized (radius radius_pos)
open LongTails.Proofs.RelativeHessianArctan (coefficient)
open LongTails.Proofs.AbcHardOracle (coin Scale toUnit)
open LongTails.Proofs.AbcHardExecution (coinCount coinCount_mono)
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging

variable {d n : ℕ} {St : Type*}

noncomputable def lvl (n : ℕ) (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℕ := min (n + 1) (coinCount q ω t + 1)

lemma lvl_mono (n : ℕ) (q : ℝ) (ω : ℕ → ℝ) {s t : ℕ} (h : s ≤ t) : lvl n q ω s ≤ lvl n q ω t :=
  min_le_min le_rfl (Nat.succ_le_succ (coinCount_mono q ω h))

lemma lvl_le (n : ℕ) (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) : lvl n q ω t ≤ n + 1 := min_le_left _ _

lemma lvl_pos (n : ℕ) (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) : 1 ≤ lvl n q ω t := by
  unfold lvl
  omega

noncomputable def simReply (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (r : ℕ)
    (x0 x : Space d) (ω : ℝ) : Space d :=
  knownPart S π (stageUpTo r π (toUnit S x0 x)) x0 x +
    if stageUpTo r π (toUnit S x0 x) < r then
      coin q ω • (fullPart S π (stageUpTo r π (toUnit S x0 x)) x0 x -
        knownPart S π (stageUpTo r π (toUnit S x0 x)) x0 x)
    else 0

lemma simReply_prefix (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (hr : 1 ≤ r)
    (x0 x : Space d) (ω : ℝ) (h : ∀ k : Fin (n + 1), k.val < r → π k = ρ k) :
    simReply S q π r x0 x ω = simReply S q ρ r x0 x ω := by
  have hst := stageUpTo_congr r π ρ (toUnit S x0 x) h
  have hle := stageUpTo_le r ρ (toUnit S x0 x)
  have hk : knownPart S π (stageUpTo r π (toUnit S x0 x)) x0 x =
      knownPart S ρ (stageUpTo r ρ (toUnit S x0 x)) x0 x := by
    rw [hst, knownPart, knownPart, partGrad_prefix π ρ _ _ (fun k hk => h k (by omega))]
  unfold simReply
  rw [hk, hst]
  split_ifs with hlt
  · rw [fullPart, fullPart, partGrad_prefix π ρ _ _ (fun k hk => h k (by omega))]
  · rfl

noncomputable def simState (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState S q π x0 query update initial ω t
    update s (simReply S q π (lvl n q ω (t + 1)) x0 (query s) (ω t))

noncomputable def trueState (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := trueState S q π x0 query update initial ω t
    update s (reply S q π x0 (query s) (ω t))

lemma simState_prefix (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (t : ℕ) (h : ∀ k : Fin (n + 1), k.val < lvl n q ω t → π k = ρ k) :
    simState S q π x0 query update initial ω t = simState S q ρ x0 query update initial ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := lvl_mono n q ω (Nat.le_add_right t 1)
    have he := ih (fun k hk => h k (by omega))
    simp only [simState]
    rw [he, simReply_prefix S q π ρ _ (lvl_pos n q ω (t + 1)) x0 _ _ h]

lemma reply_eq_simReply (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℕ → ℝ) (t : ℕ)
    (hhit : ‖toUnit S x0 x‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), lvl n q ω t ≤ i.val → |toUnit S x0 x (π i)| ≤ 1 / 20) :
    reply S q π x0 x (ω t) = simReply S q π (lvl n q ω (t + 1)) x0 x (ω t) := by
  set w := toUnit S x0 x with hw_def
  by_cases hw : 2 * radius n ≤ ‖w‖
  · simp only [reply, simReply, knownPart, fullPart, objGrad, ← hw_def, partGrad_outside π _ w hw,
      hardGrad_outside π w hw, sub_self, smul_zero, ite_self, add_zero]
  · push Not at hw
    have hsm := hhit hw.le
    have hmono := lvl_mono n q ω (Nat.le_add_right t 1)
    have hsm' : ∀ i : Fin (n + 1), lvl n q ω (t + 1) ≤ i.val → |w (π i)| ≤ 1 / 20 :=
      fun i hi => hsm i (by omega)
    have hst : stageUpTo (lvl n q ω (t + 1)) π w = stage π w := stageUpTo_eq _ _ _ hsm'
    have hstage : stage π w ≤ lvl n q ω t := by
      rw [← stageUpTo_eq _ _ _ hsm]; exact stageUpTo_le _ _ _
    unfold simReply reply
    rw [← hw_def, hst]
    by_cases hlt : stage π w < lvl n q ω (t + 1)
    · rw [ite_eq_left hlt, objGrad_eq_full]
    · rw [ite_eq_right hlt, add_zero]
      have heq : stage π w = lvl n q ω t := by omega
      by_cases hfull : n + 1 ≤ stage π w
      · have hs : stage π w = n + 1 := le_antisymm (stage_le π w) hfull
        have h1 : hardGrad π w = partGrad π n w :=
          hardGrad_eq_part π n w (fun _ i hi hi' => absurd hi' (by omega))
        rw [objGrad, knownPart, ← hw_def, hs, Nat.add_sub_cancel, h1, sub_self, smul_zero, add_zero]
      · have hlev : lvl n q ω (t + 1) = lvl n q ω t := by omega
        have hcount : ¬ ω t ≤ q := by
          intro hc
          have h1 : lvl n q ω (t + 1) = min (n + 1) (coinCount q ω t + 1 + 1) := by
            simp [lvl, coinCount, hc]
          have h2 : lvl n q ω t = min (n + 1) (coinCount q ω t + 1) := rfl
          omega
        have hc0 : coin q (ω t) = 0 := by
          unfold coin
          rw [ite_eq_right hcount]
        rw [hc0, zero_smul, add_zero]

lemma coupling (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N,
      let x := query (simState S q π x0 query update initial ω t)
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), lvl n q ω t ≤ i.val → |toUnit S x0 x (π i)| ≤ 1 / 20) :
    simState S q π x0 query update initial ω N = trueState S q π x0 query update initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hhit t (by omega))
    simp only [simState, trueState]
    rw [← he, reply_eq_simReply S q π x0 _ ω N (hhit N (by omega))]

noncomputable def observation (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  if j.val < N then
    toUnit S x0 (query (simState S q π x0 query update initial ω j.val))
  else toUnit S x0 (output (simState S q π x0 query update initial ω j.val))

lemma observation_prefix (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1)) (π ρ : Fin (n + 1) ↪ Fin d)
    (h : ∀ k : Fin (n + 1), k.val < lvl n q ω j.val → π k = ρ k) :
    observation S q x0 query output update initial ω N j π =
      observation S q x0 query output update initial ω N j ρ := by
  unfold observation
  rw [simState_prefix S q π ρ x0 query update initial ω j.val h]

def coordinateBad (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits
    (largeSet (2 * radius n) (1 / 20)
      (observation S q x0 query output update initial ω N j π))
    ((List.ofFn π).drop (lvl n q ω j.val))

lemma good_small (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S q x0 query output update initial ω N π)
    (j : Fin (N + 1))
    (hj : ‖observation S q x0 query output update initial ω N j π‖ ≤ 2 * radius n)
    (i : Fin (n + 1)) (hi : lvl n q ω j.val ≤ i.val) :
    |observation S q x0 query output update initial ω N j π (π i)| ≤ 1 / 20 := by
  apply not_largeSet_small _ _ _ hj
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ i hi h⟩

lemma bad_sum_bound (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d) :
    D * (∑ w : CoordinateWords d n, if coordinateBad S q x0 query output update initial ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (n + 1 : ℕ) * ((2 * radius n) ^ 2 / (1 / 20) ^ 2) *
        Fintype.card (CoordinateWords d n) := by
  let bad := fun π : Fin (n + 1) ↪ Fin d =>
    coordinateBad S q x0 query output update initial ω N π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (2 * radius n) (1 / 20)
          (observation S q x0 query output update initial ω N j π))
          (w.val.drop (lvl n q ω j.val)) := by
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
    List.ofFn π = w ∧ 0 < hits (largeSet (2 * radius n) (1 / 20)
      (observation S q x0 query output update initial ω N j π))
      (w.drop (lvl n q ω j.val))
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) (2 * radius n) (1 / 20) D
    (by have := radius_pos n; positivity) (by norm_num) hD hDs
    (fun j : Fin (N + 1) => lvl n q ω j.val) (fun j => lvl_le n q ω j.val)
    (observation S q x0 query output update initial ω N)
    (observation_prefix S q x0 query output update initial ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma good_gradient (S : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S q x0 query output update initial ω N π)
    (hlev : lvl n q ω N < n + 1) :
    7 / 10 * (S.a / S.lam) ≤
      ‖objGrad S π x0 (output (trueState S q π x0 query update initial ω N))‖ := by
  have hhit : ∀ t < N,
      let x := query (simState S q π x0 query update initial ω t)
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), lvl n q ω t ≤ i.val → |toUnit S x0 x (π i)| ≤ 1 / 20 := by
    intro t ht x hx i hi
    have h := good_small S q x0 query output update initial ω N π hgood ⟨t, by omega⟩
    simp only [observation, ht, ↓reduceIte] at h
    exact h hx i hi
  rw [← coupling S q π x0 query update initial ω N hhit]
  have hpos : 0 ≤ S.a / S.lam := by have := S.ha; have := S.hlam; positivity
  rw [objGrad, norm_smul, Real.norm_of_nonneg hpos, mul_comm]
  apply mul_le_mul_of_nonneg_left _ hpos
  apply hardGrad_lower
  intro hw
  have h := good_small S q x0 query output update initial ω N π hgood (Fin.last N)
  simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
  exact h hw (Fin.last n) (by simp; omega)

end LongTails.Proofs.ThirdOrderMaskedExecution
