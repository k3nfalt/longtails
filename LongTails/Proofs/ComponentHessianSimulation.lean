import LongTails.Proofs.ComponentHessianTranscript
import LongTails.Proofs.SmoothConvexFiniteHiding

namespace LongTails.Proofs.ComponentHessianSimulation

open ComponentHessianFamily ComponentHessianTranscript RelativeHessianOracle
open FiniteSumNondualLowerPolicy FiniteSumNondualLowerSearch
open FiniteSumNondualLowerHiding SmoothConvexFiniteHiding

structure Policy (d n : ℕ) (S : Type*) where
  initial : S
  query : S → Fin n × EuclideanSpace ℝ (Fin d)
  update : S → Reply (EuclideanSpace ℝ (Fin d)) → S
  output : S → EuclideanSpace ℝ (Fin d)

variable {d k n : ℕ} {S : Type*}

abbrev Record (S : Type*) (n : ℕ) := (S × List (Fin n)) × List (Fin n)

namespace Policy

variable (P : Policy d n S)

def component (s : S × List (Fin n)) : Fin n := (P.query s.1).1

noncomputable def step (π : Fin (k + 1) ↪ Fin d) (s : S × List (Fin n)) (hit : Bool) :
    S × List (Fin n) :=
  let q := P.query s.1
  let known := if hit then s.2 ++ [q.1] else s.2
  (P.update s.1 (jet (part π (indices k known q.1) n) q.2), known)

noncomputable def simulate (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n)) (t : ℕ) :
    Record S n :=
  (wordAdvance P.component (P.step π))^[t] ((P.initial, [anchor]), w)

def restAfter (rest : List (Fin n)) (i : Fin n) : List (Fin n) :=
  if rest.head? = some i then rest.tail else rest

lemma append_after (known rest : List (Fin n)) (i : Fin n) :
    nextKnown known rest i ++ restAfter rest i = known ++ rest := by
  cases rest with
  | nil => simp [nextKnown, restAfter]
  | cons j w =>
    by_cases h : j = i <;> simp [nextKnown, restAfter, h]

lemma sim_succ (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n)) (t : ℕ) :
    P.simulate π anchor w (t + 1) =
      let g := P.simulate π anchor w t
      let q := P.query g.1.1
      let known := nextKnown g.1.2 g.2 q.1
      ((P.update g.1.1 (jet (part π (indices k known q.1) n) q.2), known), restAfter g.2 q.1) := by
  unfold simulate
  rw [Function.iterate_succ_apply']
  generalize (wordAdvance P.component (P.step π))^[t] ((P.initial, [anchor]), w) = g
  rcases g with ⟨⟨s, known⟩, rest⟩
  cases rest with
  | nil => rfl
  | cons j w =>
    by_cases h : (P.query s).1 = j
    · simp [wordAdvance, component, step, nextKnown, restAfter, h]
    · simp [wordAdvance, component, step, nextKnown, restAfter, h, Ne.symm h]

lemma preserved (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n)) (t : ℕ) :
    (P.simulate π anchor w t).1.2 ++ (P.simulate π anchor w t).2 = anchor :: w := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [sim_succ, append_after] using ih

lemma prefix_length_le (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n))
    (t : ℕ) : (P.simulate π anchor w t).1.2.length ≤ w.length + 1 := by
  have h := congrArg List.length (P.preserved π anchor w t)
  simp only [List.length_append, List.length_cons] at h
  omega

set_option maxHeartbeats 2500000 in
lemma agreed (π ρ : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n)) (t : ℕ)
    (hp : ∀ j : Fin (k + 1), j.val < (P.simulate π anchor w t).1.2.length → π j = ρ j) :
    P.simulate π anchor w t = P.simulate ρ anchor w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [P.sim_succ] at hp
    dsimp only at hp
    have hle (known rest : List (Fin n)) (i : Fin n) :
        known.length ≤ (nextKnown known rest i).length := by
      unfold nextKnown
      split <;> simp
    have hh := ih (fun j hj => hp j (hj.trans_le (hle _ _ _)))
    rw [P.sim_succ, P.sim_succ, ← hh]
    dsimp only
    rw [part_prefix π ρ _ _ hp]

noncomputable def actual (π : Fin (k + 1) ↪ Fin d) (full : List (Fin n)) (t : ℕ) : S :=
  (fun s => let q := P.query s
            P.update s (jet (part π (indices k full q.1) n) q.2))^[t] P.initial

noncomputable def observation (T : ℕ) (j : Fin (T + 1)) (g : Record S n) :
    EuclideanSpace ℝ (Fin d) := if j.val < T then (P.query g.1.1).2 else P.output g.1.1

noncomputable def exposure (anchor : Fin n) (w : List (Fin n)) (T : ℕ)
    (j : Fin (T + 1)) (π : Fin (k + 1) ↪ Fin d) : ℕ × Finset (Fin d) :=
  let g := P.simulate π anchor w j.val
  (g.1.2.length, largeSet (2 * radius n (k + 1 : ℕ)) (1 / 80) (P.observation T j g))

def bad (anchor : Fin n) (w : List (Fin n)) (T : ℕ) (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (T + 1), 0 < hits (P.exposure anchor w T j π).2 ((List.ofFn π).drop (P.exposure anchor w T j π).1)

lemma small_of_good (anchor : Fin n) (w : List (Fin n)) (T : ℕ) (π : Fin (k + 1) ↪ Fin d)
    (hg : ¬ P.bad anchor w T π) (j : Fin (T + 1))
    (hx : ‖P.observation T j (P.simulate π anchor w j.val)‖ ≤ 2 * radius n (k + 1 : ℕ))
    (z : Fin (k + 1)) (hz : (P.simulate π anchor w j.val).1.2.length ≤ z.val) :
    |P.observation T j (P.simulate π anchor w j.val) (π z)| ≤ 1 / 80 := by
  apply not_largeSet_small _ _ _ hx
  intro hmem
  apply hg
  refine ⟨j, ?_⟩
  exact FiniteSumNondualLowerExposure.hits_drop_positive π _ _ z hz hmem

lemma coupled (hn : 0 < n) (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n))
    (T : ℕ) (hg : ¬ P.bad anchor w T π) (t : ℕ) (ht : t ≤ T) :
    P.actual π (anchor :: w) t = (P.simulate π anchor w t).1.1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold actual
    rw [Function.iterate_succ_apply']
    change P.update (P.actual π (anchor :: w) t)
      (jet (part π (indices k (anchor :: w) (P.query (P.actual π (anchor :: w) t)).1) n)
        (P.query (P.actual π (anchor :: w) t)).2) = _
    rw [ih (by omega), P.sim_succ]
    dsimp only
    let g := P.simulate π anchor w t
    let q := P.query g.1.1
    have eq := P.preserved π anchor w t
    change g.1.2 ++ g.2 = anchor :: w at eq
    change P.update g.1.1 (jet (part π (indices k (anchor :: w) q.1) n) q.2) = _
    apply congrArg (P.update g.1.1)
    change jet (part π (indices k (anchor :: w) q.1) n) q.2 =
      jet (part π (indices k (nextKnown g.1.2 g.2 q.1) q.1) n) q.2
    rw [← eq]
    apply Eq.symm
    apply transcript_jet π hn g.1.2.length _ _ (next_missing g.1.2 g.2 q.1).1
      (next_missing g.1.2 g.2 q.1).2
    intro hx z hz
    let j : Fin (T + 1) := ⟨t, by omega⟩
    have ho : P.observation T j g = q.2 := by
      unfold observation
      exact ite_eq_left (by dsimp [j]; omega)
    have h := P.small_of_good anchor w T π hg j (by
      change ‖P.observation T j g‖ ≤ _
      rwa [ho]) z hz
    change |P.observation T j g (π z)| ≤ _ at h
    rw [ho] at h
    linarith

end Policy

end LongTails.Proofs.ComponentHessianSimulation
