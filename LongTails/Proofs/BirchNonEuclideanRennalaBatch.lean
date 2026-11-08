import LongTails.Proofs.BirchNonEuclideanRennalaRecords

namespace LongTails.Proofs.BirchNonEuclideanRennalaBatch

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaRecords
open LongTails.Proofs.BirchNonEuclideanRennalaLabels (reply_ready)

structure BatchShape {m : ℕ} (B : ℕ) (pub : State m) (regs : Registers m) : Prop where
  length : regs.terms.length = pub.batch
  coefficients : ∀ term ∈ regs.terms, term.1 = .constant (1 / (B : ℝ))
  distinct : (regs.terms.map Prod.snd).Nodup
  pending_distinct : Set.InjOn regs.reply (↑pub.ready : Set (Fin m))
  pending_disjoint : ∀ w ∈ pub.ready, regs.reply w ∉ regs.terms.map Prod.snd

lemma batchShape_initial (m B : ℕ) : BatchShape B ({} : State m) ({} : Registers m) := by
  constructor <;> simp [Set.InjOn]

lemma batchShape_query {m : ℕ} (K B : ℕ) (w : Fin m) (pub : State m) (regs : Registers m)
    (s : CodeState) (t : Tuning) (hv : CodeValid (m + 1) t s) (ho : Owned t pub regs s)
    (hb : BatchShape B pub regs) :
    let z := eventCode K B (.query w) (pub, regs) s
    BatchShape B z.1.1 z.1.2 := by
  have hbound := codeValid_register_bound (m + 1) t s hv
  have hterm : ∀ q ∈ regs.terms.map Prod.snd, q < s.next := by
    intro q hq
    obtain ⟨term, ht, rfl⟩ := List.mem_map.mp hq
    exact hbound.2 0 _ (ho.terms term ht)
  have hreply : ∀ v ∈ pub.ready, regs.reply v < s.next := fun v hv => hbound.2 _ _ (ho.reply v hv)
  dsimp only
  refine {
    length := hb.length
    coefficients := hb.coefficients
    distinct := hb.distinct
    pending_distinct := ?_
    pending_disjoint := ?_ }
  · intro v hv z hz he
    change v ∈ insert w pub.ready at hv
    change z ∈ insert w pub.ready at hz
    change Function.update regs.reply w s.next v = Function.update regs.reply w s.next z at he
    by_cases hvw : v = w
    · subst v
      by_cases hzw : z = w
      · exact hzw.symm
      · have hzold := (Finset.mem_insert.mp hz).resolve_left hzw
        rw [Function.update_self, Function.update_of_ne hzw] at he
        have := hreply z hzold
        omega
    · have hvold := (Finset.mem_insert.mp hv).resolve_left hvw
      by_cases hzw : z = w
      · subst z
        rw [Function.update_self, Function.update_of_ne hvw] at he
        have := hreply v hvold
        omega
      · rw [Function.update_of_ne hvw, Function.update_of_ne hzw] at he
        exact hb.pending_distinct hvold ((Finset.mem_insert.mp hz).resolve_left hzw) he
  · intro v hv hmem
    change v ∈ insert w pub.ready at hv
    change Function.update regs.reply w s.next v ∈ regs.terms.map Prod.snd at hmem
    by_cases hvw : v = w
    · subst v
      rw [Function.update_self] at hmem
      have := hterm _ hmem
      omega
    · rw [Function.update_of_ne hvw] at hmem
      exact hb.pending_disjoint v ((Finset.mem_insert.mp hv).resolve_left hvw) hmem

lemma batchShape_reply {m : ℕ} (K B : ℕ) (w : Fin m) (pub : State m) (regs : Registers m)
    (s : CodeState) (hb : BatchShape B pub regs) (hw : w ∈ pub.ready) :
    BatchShape B (step K B pub (.reply w)) (replyCode K B w pub regs s).1 := by
  have hnodup : ((regs.terms ++ [(Coefficient.constant (1 / (B : ℝ)), regs.reply w)]).map Prod.snd).Nodup := by
    simp only [List.map_append, List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨hb.distinct, by simp, ?_⟩
    intro a ha b hbm hab
    have hbq : a = regs.reply w := hab.trans (List.mem_singleton.mp hbm)
    exact hb.pending_disjoint w hw (hbq ▸ ha)
  have hcoeff : ∀ term ∈ regs.terms ++ [(Coefficient.constant (1 / (B : ℝ)), regs.reply w)],
      term.1 = .constant (1 / (B : ℝ)) := by
    intro term ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hb.coefficients term ht
    · rw [List.mem_singleton.mp ht]
  refine { length := ?_, coefficients := ?_, distinct := ?_, pending_distinct := ?_, pending_disjoint := ?_ }
  · rw [replyCode_terms]
    have hl := hb.length
    by_cases ha : pub.round < K <;> by_cases hf : fresh pub w <;> by_cases hc : commits B pub w <;>
      simp [step, ha, hf, hc, hl]
  · rw [replyCode_terms]
    split_ifs <;> first | exact hcoeff | exact hb.coefficients | simp
  · rw [replyCode_terms]
    split_ifs <;> first | exact hnodup | exact hb.distinct | simp
  · intro v hv z hz he
    rw [reply_ready] at hv hz
    rw [replyCode_reply] at he
    exact hb.pending_distinct (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hz).2 he
  · intro v hv
    rw [reply_ready] at hv
    rw [replyCode_reply, replyCode_terms]
    have hdis := hb.pending_disjoint v (Finset.mem_erase.mp hv).2
    have hneq : regs.reply v ≠ regs.reply w := by
      intro he
      exact (Finset.mem_erase.mp hv).1 (hb.pending_distinct (Finset.mem_erase.mp hv).2 hw he)
    split_ifs <;> simp_all only [List.map_nil, List.not_mem_nil, List.map_append, List.map_singleton,
      List.mem_append, List.mem_singleton, not_or, not_false_eq_true, and_self]

lemma eventCode_batchShape {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m)
    (s : CodeState) (t : Tuning) (hv : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s)
    (hb : BatchShape B state.1 state.2) (he : e.Enabled state.1) :
    let z := eventCode K B e state s
    BatchShape B z.1.1 z.1.2 := by
  cases e with
  | query w => exact batchShape_query K B w state.1 state.2 s t hv ho hb
  | reply w => exact batchShape_reply K B w state.1 state.2 s hb he.2

lemma loop_batchShape {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState)
    (hv : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s)
    (hb : BatchShape B state.1 state.2) (he : LegalFrom K B state.1 events) :
    let z := (forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s
    BatchShape B z.1.1 z.1.2 := by
  induction events generalizing state s with
  | nil => exact hb
  | cons e rest ih =>
      have hv' := eventCode_valid K B t ht e state s hv ho he.1
      have hb' := eventCode_batchShape K B e state s t hv ho hb he.1
      have hr : LegalFrom K B (eventCode K B e state s).1.1 rest := by
        rw [eventCode_public]
        exact he.2
      rw [state_forIn_cons]
      exact ih _ _ hv'.1 hv'.2.2 hb' hr

lemma eventsStateCode_batchShape {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid)
    (events : List (Event m)) (he : LegalFrom K B {} events) :
    let z := eventsStateCode K B events {}
    BatchShape B z.1.1 z.1.2 := by
  have hi := initialCode_valid m t
  rw [eventsStateCode_run]
  apply loop_batchShape K B t ht events _ _ hi.1 hi.2 _ he
  rw [initialCode_run]
  exact batchShape_initial m B

end LongTails.Proofs.BirchNonEuclideanRennalaBatch
