import LongTails.Proofs.FiniteSumNondualLowerSimulation
import LongTails.Proofs.FiniteSumNondualLowerSearch
import Mathlib.Data.List.GetD

namespace LongTails.Proofs.FiniteSumNondualLowerPolicy

open FiniteSumNondualLowerSimulation FiniteSumNondualLowerSearch
open FiniteSumNondualLowerComponents

variable {S : Type*} {n : ℕ}

def policy (query : S → Fin n) (step : S → Bool → S) (s : S) (h : List Bool) : Fin n :=
  query (h.foldl step s)

def searchRun (query : S → Fin n) (step : S → Bool → S) : ℕ → S → List (Fin n) → ℕ
  | 0, _, _ => 0
  | _ + 1, _, [] => 0
  | T + 1, s, a :: w => if query s = a then
      1 + searchRun query step T (step s true) w
    else searchRun query step T (step s false) (a :: w)

lemma searchRun_eq (query : S → Fin n) (step : S → Bool → S)
    (T : ℕ) (s : S) (w : List (Fin n)) :
    searchRun query step T s w = discoveries n T (policy query step s) w := by
  induction T generalizing s w with
  | zero => rfl
  | succ T ih =>
    cases w with
    | nil => rfl
    | cons a w =>
      simp only [searchRun, discoveries, policy, List.foldl_nil]
      by_cases h : query s = a <;> simp only [h, ↓reduceIte, ih, List.foldl_cons] <;> rfl

def wordAdvance (query : S → Fin n) (step : S → Bool → S)
    (state : S × List (Fin n)) : S × List (Fin n) :=
  match state.2 with
  | [] => (step state.1 false, [])
  | a :: w => if query state.1 = a then (step state.1 true, w)
      else (step state.1 false, a :: w)

lemma wordAdvance_count (query : S → Fin n) (step : S → Bool → S)
    (T : ℕ) (s : S) (w : List (Fin n)) :
    ((wordAdvance query step)^[T] (s, w)).2.length + searchRun query step T s w = w.length := by
  induction T generalizing s w with
  | zero => simp [searchRun]
  | succ T ih =>
    rw [Function.iterate_succ_apply]
    cases w with
    | nil =>
      have hi := ih (step s false) []
      have hz : ((wordAdvance query step)^[T] (step s false, [])).2.length = 0 := by
        simp only [List.length_nil] at hi
        omega
      simpa only [wordAdvance, searchRun, Nat.add_zero, List.length_nil] using hz
    | cons a w =>
      by_cases h : query s = a
      · simp only [wordAdvance, h, ↓reduceIte, searchRun, List.length_cons]
        have hi := ih (step s true) w
        omega
      · simpa [wordAdvance, searchRun, h] using ih (step s false) (a :: w)

lemma wordAdvance_discoveries (query : S → Fin n) (step : S → Bool → S)
    (T : ℕ) (s : S) (w : List (Fin n)) :
    ((wordAdvance query step)^[T] (s, w)).2.length +
      discoveries n T (policy query step s) w = w.length := by
  simpa only [searchRun_eq] using wordAdvance_count query step T s w

def Remaining {k n : ℕ} (owner : Fin (k + 1) → Fin n) (r : ℕ) (w : List (Fin n)) : Prop :=
  w.length + r = k ∧ ∀ j (hj : j < w.length) (z : Fin (k + 1)),
    z.val = r + j + 1 → w[j] = owner z

lemma remaining_initial {k n : ℕ} (owner : Fin (k + 1) → Fin n) :
    Remaining owner 0 (List.ofFn (fun j : Fin k => owner j.succ)) := by
  constructor
  · simp
  · intro j hj z hz
    have hjk : j < k := by simpa using hj
    have he : z = (⟨j, hjk⟩ : Fin k).succ := Fin.ext (by simpa using hz)
    simp [he]

lemma remaining_tail {k n : ℕ} (owner : Fin (k + 1) → Fin n) (r : ℕ)
    (a : Fin n) (w : List (Fin n)) (h : Remaining owner r (a :: w)) :
    Remaining owner (r + 1) w := by
  constructor
  · have := h.1; simp only [List.length_cons] at this; omega
  · intro j hj z hz
    have he := h.2 (j + 1) (by simpa using hj) z (by omega)
    simpa using he

lemma remaining_head {k n : ℕ} (owner : Fin (k + 1) → Fin n) (r : ℕ)
    (a : Fin n) (w : List (Fin n)) (h : Remaining owner r (a :: w))
    (j : Fin k) (hj : j.val = r) : a = owner j.succ := by
  exact h.2 0 (by simp) j.succ (by simp [hj])

noncomputable def learnedStep {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S)
    (state : S × ℕ × (Fin (k + 1) → Fin n)) (hit : Bool) :
    S × ℕ × (Fin (k + 1) → Fin n) :=
  let q := query state.1
  let r := state.2.1
  let info := if h : r < k ∧ hit = true then
    (r + 1, Function.update state.2.2 ⟨r + 1, by omega⟩ q.1) else (r, state.2.2)
  (update state.1 (partialGradient L δ a π info.2 q.1 info.1 q.2), info)

lemma learnedStep_correct {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S)
    (s : S) (r : ℕ) (known owner : Fin (k + 1) → Fin n)
    (hk : ∀ j : Fin (k + 1), j.val ≤ r → known j = owner j)
    (hit : Bool) (hh : hit = decide (∃ j : Fin k, j.val = r ∧ owner j.succ = (query s).1)) :
    let next := learnedStep L δ a π query update (s, r, known) hit
    next.2.1 = revealedStep owner (query s).1 r ∧
      (∀ j : Fin (k + 1), j.val ≤ next.2.1 → next.2.2 j = owner j) ∧
      next.1 = update s (partialGradient L δ a π owner (query s).1 next.2.1 (query s).2) := by
  subst hit
  by_cases hr : r < k
  · let j : Fin k := ⟨r, hr⟩
    have hex : (∃ j : Fin k, j.val = r ∧ owner j.succ = (query s).1) ↔
        owner j.succ = (query s).1 := by
      constructor
      · rintro ⟨i, hi, ho⟩
        have he : i = j := Fin.ext hi
        simpa [he] using ho
      · intro ho; exact ⟨j, rfl, ho⟩
    by_cases ho : owner j.succ = (query s).1
    · have he : (⟨r + 1, by omega⟩ : Fin (k + 1)) = j.succ := rfl
      have hp : ∀ z : Fin (k + 1), z.val ≤ r + 1 →
          Function.update known j.succ (query s).1 z = owner z := by
        intro z hz
        by_cases hez : z = j.succ
        · subst z; simp [ho]
        · rw [Function.update_of_ne hez]
          apply hk
          have hn : z.val ≠ r + 1 := by intro hz; exact hez (Fin.ext hz)
          omega
      simp only [learnedStep, hex, ho, decide_true, hr, and_self, ↓reduceDIte,
        revealedStep, he, ↓reduceIte]
      refine ⟨True.intro, hp, ?_⟩
      congr 1
      exact partialGradient_prefix L δ a π π _ owner _ _ _ (fun _ _ => rfl) hp
    · have he : (⟨r + 1, by omega⟩ : Fin (k + 1)) = j.succ := rfl
      simp only [learnedStep, hex, ho, decide_false, Bool.false_eq_true, and_false,
        ↓reduceDIte, revealedStep, hr, he, ↓reduceIte]
      refine ⟨True.intro, hk, ?_⟩
      congr 1
      exact partialGradient_prefix L δ a π π known owner _ _ _ (fun _ _ => rfl) hk
  · have hex : ¬ ∃ j : Fin k, j.val = r ∧ owner j.succ = (query s).1 := by
      rintro ⟨j, hj, _⟩
      have := j.isLt
      omega
    simp only [learnedStep, hr, false_and, ↓reduceDIte, revealedStep]
    refine ⟨True.intro, hk, ?_⟩
    congr 1
    exact partialGradient_prefix L δ a π π known owner _ _ _ (fun _ _ => rfl) hk

lemma wordAdvance_learned {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S)
    (state : S × ℕ × (Fin (k + 1) → Fin n)) (w : List (Fin n))
    (hw : Remaining owner state.2.1 w) :
    let q := fun st : S × ℕ × (Fin (k + 1) → Fin n) => (query st.1).1
    let step := learnedStep L δ a π query update
    let next := wordAdvance q step (state, w)
    next.1 = step state (decide (∃ j : Fin k,
      j.val = state.2.1 ∧ owner j.succ = (query state.1).1)) ∧
      Remaining owner next.1.2.1 next.2 := by
  rcases state with ⟨s, r, known⟩
  cases w with
  | nil =>
    have hr : r = k := by simpa [Remaining] using hw.1
    have hn : ¬ ∃ j : Fin k, j.val = r ∧ owner j.succ = (query s).1 := by
      rintro ⟨j, hj, _⟩
      have := j.isLt
      omega
    simp only [wordAdvance, hn, decide_false]
    refine ⟨True.intro, ?_⟩
    simpa only [learnedStep, hr, lt_self_iff_false, false_and, ↓reduceDIte] using hw
  | cons b w =>
    have hr : r < k := by have := hw.1; simp only [List.length_cons] at this; omega
    let j : Fin k := ⟨r, hr⟩
    have hb : b = owner j.succ := remaining_head owner r b w hw j rfl
    have hh : (∃ j : Fin k, j.val = r ∧ owner j.succ = (query s).1) ↔
        (query s).1 = b := by
      constructor
      · rintro ⟨i, hi, ho⟩
        have he : i = j := Fin.ext hi
        simpa [he, ← hb] using ho.symm
      · intro h; exact ⟨j, rfl, hb.symm.trans h.symm⟩
    by_cases h : (query s).1 = b
    · have hhb : ∃ i : Fin k, i.val = r ∧ owner i.succ = b := ⟨j, rfl, hb.symm⟩
      simp only [wordAdvance, h, ↓reduceIte, hhb, decide_true]
      refine ⟨True.intro, ?_⟩
      simpa only [learnedStep, hr, and_self, ↓reduceDIte] using remaining_tail owner r b w hw
    · simp only [wordAdvance, hh, h, ↓reduceIte, decide_false]
      refine ⟨True.intro, ?_⟩
      simpa only [learnedStep, Bool.false_eq_true, and_false, ↓reduceDIte] using hw

noncomputable def learnedRun {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (anchor : Fin n) :
    ℕ → S × ℕ × (Fin (k + 1) → Fin n)
  | 0 => (initial, 0, fun _ => anchor)
  | T + 1 =>
    let state := learnedRun L δ a π owner query update initial anchor T
    learnedStep L δ a π query update state
      (decide (∃ j : Fin k, j.val = state.2.1 ∧ owner j.succ = (query state.1).1))

lemma learnedRun_correct {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (anchor : Fin n)
    (hanchor : owner 0 = anchor) (T : ℕ) :
    let state := learnedRun L δ a π owner query update initial anchor T
    let sim := simulatedState L δ a π owner query update initial T
    state.1 = sim.1 ∧ state.2.1 = sim.2 ∧
      ∀ j : Fin (k + 1), j.val ≤ state.2.1 → state.2.2 j = owner j := by
  induction T with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro j hj
    have he : j = 0 := Fin.ext (by simpa [learnedRun] using hj)
    simpa [he, learnedRun] using hanchor.symm
  | succ T ih =>
    dsimp only at ih ⊢
    let state := learnedRun L δ a π owner query update initial anchor T
    have hc := learnedStep_correct L δ a π query update state.1 state.2.1 state.2.2
      owner ih.2.2 _ rfl
    change _ ∧ _ ∧ _ at hc
    change (learnedStep L δ a π query update state _).1 = _ ∧ _ ∧ _
    refine ⟨?_, ?_, hc.2.1⟩
    · rw [hc.2.2, hc.1]
      simp only [state, ih.1, ih.2.1, simulatedState]
    · rw [learnedRun, hc.1]
      simp only [state, ih.1, ih.2.1, simulatedState]

lemma wordRun_learned {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (anchor : Fin n) (T : ℕ) :
    let q := fun st : S × ℕ × (Fin (k + 1) → Fin n) => (query st.1).1
    let step := learnedStep L δ a π query update
    let run := (wordAdvance q step)^[T]
      ((initial, 0, fun _ => anchor), List.ofFn (fun j : Fin k => owner j.succ))
    run.1 = learnedRun L δ a π owner query update initial anchor T ∧
      Remaining owner run.1.2.1 run.2 := by
  dsimp only
  induction T with
  | zero => exact ⟨rfl, remaining_initial owner⟩
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    have hc := wordAdvance_learned L δ a π owner query update _ _ ih.2
    refine ⟨?_, hc.2⟩
    rw [hc.1, ih.1]
    rfl

lemma simulated_discoveries {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (anchor : Fin n)
    (hanchor : owner 0 = anchor) (T : ℕ) :
    (simulatedState L δ a π owner query update initial T).2 =
      discoveries n T (policy (fun st : S × ℕ × (Fin (k + 1) → Fin n) => (query st.1).1)
        (learnedStep L δ a π query update) (initial, 0, fun _ => anchor))
        (List.ofFn (fun j : Fin k => owner j.succ)) := by
  have hr := wordRun_learned L δ a π owner query update initial anchor T
  have hc := wordAdvance_discoveries
    (fun st : S × ℕ × (Fin (k + 1) → Fin n) => (query st.1).1)
    (learnedStep L δ a π query update) T (initial, 0, fun _ => anchor)
    (List.ofFn (fun j : Fin k => owner j.succ))
  have hs := (learnedRun_correct L δ a π owner query update initial anchor hanchor T).2.1
  have hl := hr.2.1
  rw [hr.1, hs] at hl
  simp only [List.length_ofFn] at hc
  omega

def wordOwner {k n : ℕ} (anchor : Fin n) (w : List (Fin n)) (j : Fin (k + 1)) : Fin n :=
  if j.val = 0 then anchor else w.getD (j.val - 1) anchor

lemma wordOwner_zero {k n : ℕ} (anchor : Fin n) (w : List (Fin n)) :
    wordOwner (k := k) anchor w 0 = anchor := by simp [wordOwner]

lemma wordOwner_labels {k n : ℕ} (anchor : Fin n) (w : List (Fin n)) (hw : w.length = k) :
    List.ofFn (fun j : Fin k => wordOwner anchor w j.succ) = w := by
  apply List.ext_getElem
  · simpa using hw.symm
  · intro j hj hwj
    simp only [List.getElem_ofFn, wordOwner, Fin.val_succ, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    exact List.getD_eq_getElem w anchor hwj

lemma simulated_completion_fraction {d k n : ℕ} (L δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (anchor : Fin n)
    (T : ℕ) (hn : 0 < n) (hk : 0 < k) (hT : 8 * T ≤ n * k) :
    4 * (((words n k).filter (fun w => k ≤
      (simulatedState L δ a π (wordOwner anchor w) query update initial T).2)).card : ℝ) ≤
        (n : ℝ) ^ k := by
  classical
  let q := policy (fun st : S × ℕ × (Fin (k + 1) → Fin n) => (query st.1).1)
    (learnedStep L δ a π query update) (initial, 0, fun _ => anchor)
  have he : (words n k).filter (fun w => k ≤
      (simulatedState L δ a π (wordOwner anchor w) query update initial T).2) =
      (words n k).filter (fun w => k ≤ discoveries n T q w) := by
    apply Finset.filter_congr
    intro w hw
    rw [simulated_discoveries L δ a π (wordOwner anchor w) query update initial anchor
      (wordOwner_zero anchor w) T, wordOwner_labels anchor w ((mem_words n k w).mp hw)]
  rw [he]
  exact completion_fraction n T k q hn hk hT

end LongTails.Proofs.FiniteSumNondualLowerPolicy
