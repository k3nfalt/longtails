import LongTails.Proofs.BirchNonEuclideanRennalaMean

namespace LongTails.Proofs.BirchNonEuclideanRennalaHistory

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaRecords
open LongTails.Proofs.BirchNonEuclideanRennalaAnchor
open LongTails.Proofs.BirchNonEuclideanRennalaMean
open LongTails.Proofs.BirchNonEuclideanShared (termSum termSum_extends)
open LongTails.Proofs.BirchNonEuclideanRennalaCosts (initialCode_run)

structure History {m : ℕ} (η : ℝ) (B k : ℕ) (regs : Registers m) (s : CodeState) : Prop where
  initial : regs.points 0 = 0
  units : (codeSymbolic (canonicalTuning η B) s).units = ∅
  queries_linear : ∀ q ∈ (codeSymbolic (canonicalTuning η B) s).queries,
    ((codeSymbolic (canonicalTuning η B) s).queryPoints q).1 = 0
  main_linear : ∀ j ≤ k, ((codeSymbolic (canonicalTuning η B) s).points (regs.points j)).1 = 0
  sharps : (codeSymbolic (canonicalTuning η B) s).sharps = (Finset.range k).image regs.sharps
  owners : ∀ j < k, regs.owner (regs.sharps j) = j
  chain : ∀ j < k, (codeSymbolic (canonicalTuning η B) s).points (regs.points (j + 1)) =
    (codeSymbolic (canonicalTuning η B) s).points (regs.points j) +
      η • ((0, Finsupp.single (regs.sharps j) 1) : LinearValue)
  means : ∀ j < k, Nonempty (MeanWitness (canonicalTuning η B) s B (regs.sharps j) (regs.points j))

lemma History.sharp_mem {m : ℕ} {η : ℝ} {B k : ℕ} {regs : Registers m} {s : CodeState}
    (hh : History η B k regs s) (j : ℕ) (hj : j < k) :
    regs.sharps j ∈ (codeSymbolic (canonicalTuning η B) s).sharps := by
  rw [hh.sharps]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

lemma History.quiet {m : ℕ} {η : ℝ} {B k : ℕ} {regs regs' : Registers m} {s s' : CodeState}
    (hh : History η B k regs s) (n : ℕ)
    (hs : codeSymbolic (canonicalTuning η B) s' =
      { codeSymbolic (canonicalTuning η B) s with next := n })
    (hp : regs'.points = regs.points) (hd : regs'.sharps = regs.sharps) (ho : regs'.owner = regs.owner) :
    History η B k regs' s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hp] using hh.initial
  · simpa only [hs] using hh.units
  · simpa only [hs] using hh.queries_linear
  · simpa only [hs, hp] using hh.main_linear
  · simpa only [hs, hd] using hh.sharps
  · simpa only [hd, ho] using hh.owners
  · simpa only [hs, hp, hd] using hh.chain
  · intro j hj
    obtain ⟨hw⟩ := hh.means j hj
    refine ⟨⟨hw.queries, hw.card, ?_, ?_, ?_⟩⟩
    · simpa only [hs] using hw.included
    · simpa only [hs, hp] using hw.points
    · simpa only [hs, hd] using hw.input

lemma launches_symbolic {m : ℕ} (ws : List (Fin m)) (s : CodeState) (t : Tuning) :
    codeSymbolic t ((forIn ws () (fun w _ => ForInStep.yield <$> launchCode (w.val + 1)) :
      StateM CodeState Unit) s).2 = { codeSymbolic t s with next := (codeSymbolic t s).next + ws.length } := by
  induction ws generalizing s with
  | nil => simp [state_pure_apply]
  | cons w rest ih =>
      rw [state_forIn_cons, ih]
      simp only [launchCode, state_bind_apply, state_pure_apply, codeSymbolic_emit,
        InstructionTemplate.instantiate, symbolicPerform, List.length_cons]
      congr 1
      omega

lemma initialCode_symbolic (m : ℕ) (t : Tuning) :
    codeSymbolic t (initialCode m {}).2 = { ({} : SymbolicMemory) with next := 1 + m } := by
  rw [initialCode_run]
  dsimp only
  rw [launches_symbolic, List.length_finRange]
  rfl

lemma initialCode_history (m B : ℕ) (η : ℝ) :
    History η B 0 (initialCode m {}).1 (initialCode m {}).2 := by
  have hs := initialCode_symbolic m (canonicalTuning η B)
  have hr : (initialCode m {}).1 = ({} : Registers m) := by rw [initialCode_run]
  constructor <;> simp [hs, hr]

lemma History.extend {m : ℕ} {η : ℝ} {B k : ℕ} {regs regs' : Registers m} {s s' : CodeState}
    (hh : History η B k regs s) (he : CodeExtends s s')
    (hp : ∀ j ≤ k, regs'.points j = regs.points j)
    (hd : ∀ j < k, regs'.sharps j = regs.sharps j)
    (ho : ∀ j < k, regs'.owner (regs.sharps j) = regs.owner (regs.sharps j))
    (hb : ∀ j ≤ k, regs.points j < (codeSymbolic (canonicalTuning η B) s).next)
    (hsh : (codeSymbolic (canonicalTuning η B) s').sharps = (codeSymbolic (canonicalTuning η B) s).sharps)
    (hu : (codeSymbolic (canonicalTuning η B) s').units = (codeSymbolic (canonicalTuning η B) s).units)
    (hq : ∀ q ∈ (codeSymbolic (canonicalTuning η B) s').queries,
      ((codeSymbolic (canonicalTuning η B) s').queryPoints q).1 = 0) : History η B k regs' s' := by
  have hm : ∀ j ≤ k, (codeSymbolic (canonicalTuning η B) s').points (regs'.points j) =
      (codeSymbolic (canonicalTuning η B) s).points (regs.points j) := by
    intro j hj
    rw [hp j hj]
    exact (codeExtends_symbolic _ s s' he _ (hb j hj)).1
  refine ⟨(hp 0 (Nat.zero_le k)).trans hh.initial, hu.trans hh.units, hq,
    fun j hj => by rw [hm j hj]; exact hh.main_linear j hj, ?_, ?_, ?_, ?_⟩
  · rw [hsh, hh.sharps]
    apply Finset.image_congr
    intro j hj
    exact (hd j (Finset.mem_range.mp hj)).symm
  · intro j hj
    rw [hd j hj, ho j hj, hh.owners j hj]
  · intro j hj
    rw [hm (j + 1) (by omega), hm j hj.le, hd j hj, hh.chain j hj]
  · intro j hj
    obtain ⟨hw⟩ := hh.means j hj
    rw [hd j hj, hp j hj.le]
    exact ⟨hw.mono he ((codeSymbolic_beforeNext _ s).2 _
      (Finset.mem_union_left _ (hh.sharp_mem j hj))) (hb j hj.le)⟩

lemma commitCode_history {m : ℕ} (η : ℝ) (B k : ℕ) (regs : Registers m) (s : CodeState)
    (terms : List (Coefficient × ℕ)) (hv : CodeValid (m + 1) (canonicalTuning η B) s)
    (hb : ∀ j ≤ k, regs.points j ∈ (codeLayout (canonicalTuning η B) s).points 0)
    (hh : History η B k regs s) (hl : terms.length = B)
    (hc : ∀ term ∈ terms, term.1 = .constant (1 / (B : ℝ)))
    (hdup : (terms.map Prod.snd).Nodup)
    (hr : ∀ term ∈ terms, RawRecord (canonicalTuning η B) s term.2 (regs.points k)) :
    let z := commitCode k terms regs s
    History η B (k + 1) z.1 z.2 := by
  let t := canonicalTuning η B
  let z := commitCode k terms regs s
  have hn := codeValid_symbolic_next (m + 1) t s hv
  have hbound := codeValid_register_bound (m + 1) t s hv
  have hpbound : ∀ j ≤ k, regs.points j < (codeSymbolic t s).next := by
    intro j hj
    rw [← hn]
    exact hbound.1 _ _ (hb j hj)
  have he := commitCode_extends k terms regs s
  have hs := commitCode_symbolic k terms regs s η B hn
  have hz := (commitCode_registers k terms regs s).1
  change z.1 = _ at hz
  have hp : ∀ j ≤ k, z.1.points j = regs.points j := by
    intro j hj
    simp only [hz, Function.update_of_ne (by omega : j ≠ k + 1)]
  have hd : ∀ j < k, z.1.sharps j = regs.sharps j := by
    intro j hj
    simp only [hz, Function.update_of_ne (by omega : j ≠ k)]
  have hdbound : ∀ j < k, regs.sharps j < (codeSymbolic t s).next := by
    intro j hj
    exact (codeSymbolic_beforeNext t s).2 _ (Finset.mem_union_left _ (hh.sharp_mem j hj))
  have ho : ∀ j < k, z.1.owner (regs.sharps j) = regs.owner (regs.sharps j) := by
    intro j hj
    have hne : regs.sharps j ≠ s.next + 1 := by have := hdbound j hj; omega
    simp only [hz, Function.update_of_ne hne]
  have hm : ∀ j ≤ k, (codeSymbolic t z.2).points (z.1.points j) =
      (codeSymbolic t s).points (regs.points j) := by
    intro j hj
    rw [hp j hj]
    exact (codeExtends_symbolic t s z.2 he _ (hpbound j hj)).1
  have hlast : z.1.points (k + 1) = s.next + 2 := by simp only [hz, Function.update_self]
  have hsharp : z.1.sharps k = s.next + 1 := by simp only [hz, Function.update_self]
  have hnew : (codeSymbolic t z.2).points (z.1.points (k + 1)) =
      (codeSymbolic t s).points (regs.points k) + η • ((0, Finsupp.single (z.1.sharps k) 1) : LinearValue) := by
    rw [hlast, hsharp]
    exact hs.1
  refine {
    initial := (hp 0 (Nat.zero_le k)).trans hh.initial
    units := hs.2.2.2.2.trans hh.units
    queries_linear := ?_
    main_linear := ?_
    sharps := ?_
    owners := ?_
    chain := ?_
    means := ?_ }
  · intro q hq
    rw [hs.2.2.1] at hq
    rw [(codeExtends_symbolic t s z.2 he q ((codeSymbolic_beforeNext t s).1 q hq)).2.2.1]
    exact hh.queries_linear q hq
  · intro j hj
    by_cases h : j = k + 1
    · subst j
      rw [hnew]
      simp only [Prod.fst_add, LongTails.Proofs.BirchNonEuclideanDelta.linearValue_fst_smul,
        smul_zero, add_zero]
      exact hh.main_linear k le_rfl
    · rw [hm j (by omega)]
      exact hh.main_linear j (by omega)
  · rw [hs.2.2.2.1, hh.sharps, Finset.range_add_one, Finset.image_insert, hsharp]
    congr 1
    apply Finset.image_congr
    intro j hj
    exact (hd j (Finset.mem_range.mp hj)).symm
  · intro j hj
    by_cases h : j = k
    · subst j
      rw [hsharp, hz]
      exact Function.update_self _ _ _
    · have hjk : j < k := by omega
      rw [hd j hjk, ho j hjk, hh.owners j hjk]
  · intro j hj
    by_cases h : j = k
    · subst j
      rw [hnew, hm k le_rfl]
    · have hjk : j < k := by omega
      rw [hm (j + 1) (by omega), hm j hjk.le, hd j hjk, hh.chain j hjk]
  · intro j hj
    by_cases h : j = k
    · subst j
      have hraw : ∀ term ∈ terms, RawRecord t z.2 term.2 (regs.points k) := by
        intro term ht
        exact (hr term ht).mono he ((codeSymbolic_beforeNext t s).1 _ (hr term ht).query) (hpbound k le_rfl)
      have hsum : termSum t z.2 terms = termSum t s terms :=
        termSum_extends t s z.2 terms he hn (fun term ht => by
          rw [hn]; exact (codeSymbolic_beforeNext t s).1 _ (hr term ht).query)
      rw [hsharp, hp k le_rfl]
      exact ⟨meanWitnessOfTerms t z.2 B (s.next + 1) (regs.points k) terms hl hc hdup hraw
        (hs.2.1.trans hsum.symm)⟩
    · have hjk : j < k := by omega
      obtain ⟨hw⟩ := hh.means j hjk
      rw [hd j hjk, hp j hjk.le]
      exact ⟨hw.mono he (hdbound j hjk) (hpbound j hjk.le)⟩

end LongTails.Proofs.BirchNonEuclideanRennalaHistory
