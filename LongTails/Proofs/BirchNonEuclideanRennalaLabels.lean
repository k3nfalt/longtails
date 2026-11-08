import LongTails.Proofs.BirchNonEuclideanRennalaScheduling
import LongTails.Proofs.BirchNonEuclideanEventLabels

namespace LongTails.Proofs.BirchNonEuclideanRennalaLabels

open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
open LongTails.Proofs.BirchNonEuclideanEventLabels (labelIndex labelIndex_injective)

def normalLabels {m : ℕ} (s : State m) : List (Label m) := s.accepted ++ s.stale ++ s.drained

lemma reply_serial {m : ℕ} (K B : ℕ) (s : State m) (w : Fin m) :
    (step K B s (.reply w)).serial = Function.update s.serial w (s.serial w + 1) := by
  unfold step
  split_ifs <;> rfl

lemma reply_ready {m : ℕ} (K B : ℕ) (s : State m) (w : Fin m) :
    (step K B s (.reply w)).ready = s.ready.erase w := by
  unfold step
  split_ifs <;> rfl

lemma reply_queries {m : ℕ} (K B : ℕ) (s : State m) (w : Fin m) :
    (step K B s (.reply w)).queries = s.queries := by
  unfold step
  split_ifs <;> rfl

lemma reply_normal_mem {m : ℕ} (K B : ℕ) (s : State m) (w : Fin m) (q : Label m) :
    q ∈ normalLabels (step K B s (.reply w)) ↔ q ∈ normalLabels s ∨ q = (w, s.serial w) := by
  simp only [normalLabels, step]
  split_ifs <;> simp only [List.mem_append, List.mem_singleton] <;> tauto

def QueryPast {m : ℕ} (s : State m) : Prop :=
  ∀ w c, (w, c) ∈ s.queries → c < s.serial w ∨ c = s.serial w ∧ w ∈ s.ready

def SerialCoverage {m : ℕ} (s : State m) : Prop :=
  ∀ w c, c < s.serial w → (w, c) ∈ normalLabels s

lemma step_queryPast {m : ℕ} (K B : ℕ) (s : State m) (e : Event m) (hs : QueryPast s) :
    QueryPast (step K B s e) := by
  cases e with
  | query v =>
      intro w c hmem
      change (w, c) ∈ s.queries ++ [(v, s.serial v)] at hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · have hp := hs w c hold
        change c < s.serial w ∨ c = s.serial w ∧ w ∈ insert v s.ready
        rcases hp with hp | ⟨hc, hr⟩
        · exact Or.inl hp
        · exact Or.inr ⟨hc, Finset.mem_insert_of_mem hr⟩
      · have heq := List.mem_singleton.mp hnew
        cases heq
        exact Or.inr ⟨rfl, Finset.mem_insert_self _ _⟩
  | reply v =>
      intro w c hmem
      rw [reply_queries] at hmem
      have hp := hs w c hmem
      rw [reply_serial, reply_ready]
      by_cases hw : w = v
      · subst w
        rw [Function.update_self]
        left
        rcases hp with hp | ⟨hp, _⟩ <;> omega
      · rw [Function.update_of_ne hw]
        rcases hp with hp | ⟨hc, hr⟩
        · exact Or.inl hp
        · exact Or.inr ⟨hc, Finset.mem_erase.mpr ⟨hw, hr⟩⟩

lemma step_serialCoverage {m : ℕ} (K B : ℕ) (s : State m) (e : Event m) (hs : SerialCoverage s) :
    SerialCoverage (step K B s e) := by
  cases e with
  | query v => exact hs
  | reply v =>
      intro w c hc
      rw [reply_serial] at hc
      rw [reply_normal_mem]
      by_cases hw : w = v
      · subst w
        rw [Function.update_self] at hc
        by_cases hold : c < s.serial v
        · exact Or.inl (hs v c hold)
        · right
          congr 1
          omega
      · rw [Function.update_of_ne hw] at hc
        exact Or.inl (hs w c hc)

lemma step_queries_nodup {m : ℕ} (K B : ℕ) (s : State m) (e : Event m)
    (hp : QueryPast s) (hn : s.queries.Nodup) (he : e.Enabled s) :
    (step K B s e).queries.Nodup := by
  cases e with
  | query w =>
      have hf : (w, s.serial w) ∉ s.queries := by
        intro hm
        have hh := hp w _ hm
        rcases hh with hh | ⟨_, hr⟩
        · omega
        · exact he.2 hr
      change (s.queries ++ [(w, s.serial w)]).Nodup
      refine List.nodup_append.mpr ⟨hn, by simp, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst b
      exact hf (hab ▸ ha)
  | reply w => simpa only [reply_queries] using hn

lemma run_label_invariant {m : ℕ} (K B : ℕ) (events : List (Event m)) (he : LegalFrom K B {} events) :
    QueryPast (run K B events) ∧ SerialCoverage (run K B events) ∧ (run K B events).queries.Nodup := by
  have hi : QueryPast ({} : State m) ∧ SerialCoverage ({} : State m) ∧ ([] : List (Label m)).Nodup := by
    refine ⟨?_, ?_, List.nodup_nil⟩
    · intro w c hh
      cases hh
    · intro w c hh
      change c < 0 at hh
      omega
  exact legalFrom_invariant K B (fun s => QueryPast s ∧ SerialCoverage s ∧ s.queries.Nodup)
    (fun s e hs he => ⟨step_queryPast K B s e hs.1, step_serialCoverage K B s e hs.2.1,
      step_queries_nodup K B s e hs.1 hs.2.2 he⟩) {} events hi he

lemma completeTrace_ready {m : ℕ} (K B : ℕ) (events : List (Event m))
    (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) : (run K B events).ready = ∅ := by
  have hi := run_invariant K B events hK hB he.1
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hx := hi.ready_live hw
  simp [he.2.2] at hx

lemma completeTrace_labels_perm {m : ℕ} (K B : ℕ) (events : List (Event m))
    (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    (run K B events).queries.Perm (normalLabels (run K B events)) := by
  have hl := run_label_invariant K B events he.1
  have hr := completeTrace_ready K B events hK hB he
  have hsub : (run K B events).queries ⊆ normalLabels (run K B events) := by
    rintro ⟨w, c⟩ hq
    have hp := hl.1 w c hq
    rcases hp with hp | ⟨_, hp⟩
    · exact hl.2.1 w c hp
    · simp [hr] at hp
  apply (hl.2.2.subperm hsub).perm_of_length_le
  have hb := (run_invariant K B events hK hB he.1).query_balance
  simp only [normalLabels, List.length_append]
  rw [hr, Finset.card_empty, Nat.add_zero] at hb
  omega

lemma completeTrace_iid {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {samples : ℕ → Ξ → Ω} {mu : MeasureTheory.Measure Ω} {P : MeasureTheory.Measure Ξ}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID samples mu P)
    {m : ℕ} (K B : ℕ) (events : List (Event m)) (hK : 0 < K) (hB : 0 < B)
    (he : CompleteTrace K B events) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun i => samples (labelIndex (completeTrace_labels_perm K B events hK hB he) i)) mu P := by
  exact LongTails.Proofs.BirchNonEuclideanExecution.iid_reindex h_samples _ (labelIndex_injective _)

end LongTails.Proofs.BirchNonEuclideanRennalaLabels
