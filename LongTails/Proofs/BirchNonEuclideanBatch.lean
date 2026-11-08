import LongTails.Proofs.BirchNonEuclideanDelta

namespace LongTails.Proofs.BirchNonEuclideanBatch

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_fst_smul linearValue_snd_smul
  linearValue_fst_sum linearValue_snd_sum coefficientMass coefficientMass_single
  codeSymbolic_sharp_mass weighted_single_sum_le)

noncomputable def collectedPrefix (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) :
    List (Coefficient × ℕ) × CodeState :=
  (forIn (List.range n) []
    (fun h terms => ForInStep.yield <$> collectedStep worker round x B h terms) :
      StateM CodeState (List (Coefficient × ℕ))) s

lemma collectedPrefix_zero (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) :
    collectedPrefix worker round x B 0 s = ([], s) := rfl

lemma collectedPrefix_succ (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) :
    collectedPrefix worker round x B (n + 1) s =
      let z := collectedPrefix worker round x B n s
      collectedStep worker round x B n z.1 z.2 := state_forIn_range_succ _ n [] s

lemma collectedPrefix_next (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) :
    (collectedPrefix worker round x B n s).2.next = s.next + 3 * n := by
  induction n with
  | zero => simp [collectedPrefix_zero]
  | succ n ih =>
      rw [collectedPrefix_succ]
      change (collectedPrefix worker round x B n s).2.next + 1 + 1 + 1 = _
      rw [ih, Nat.mul_add]
      omega

lemma collectedPrefix_terms (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) :
    (collectedPrefix worker round x B n s).1 =
      (List.range n).map (fun j => (Coefficient.constant (1 / (B : ℝ)), s.next + 3 * j + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [collectedPrefix_succ]
      change (collectedPrefix worker round x B n s).1 ++
        [(.constant (1 / (B : ℝ)), (collectedPrefix worker round x B n s).2.next + 1)] = _
      rw [ih, collectedPrefix_next, List.range_succ, List.map_append]
      rfl

lemma collectedPrefix_symbolic_step (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) (t : Tuning) :
    codeSymbolic t (collectedPrefix worker round x B (n + 1) s).2 =
      let old := codeSymbolic t (collectedPrefix worker round x B n s).2
      { old with
        next := old.next + 3
        vectors := Function.update old.vectors (old.next + 1) (Finsupp.single (old.next + 1) 1, 0)
        queryPoints := Function.update old.queryPoints (old.next + 1) (old.points x)
        queries := insert (old.next + 1) old.queries } := by
  rw [collectedPrefix_succ]
  simp only [collectedStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
    InstructionTemplate.instantiate, symbolicPerform, symbolicStore]

lemma collectedPrefix_aligned (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    (collectedPrefix worker round x B n s).2.next = (codeSymbolic t (collectedPrefix worker round x B n s).2).next := by
  induction n with
  | zero => exact hn
  | succ n ih =>
      rw [collectedPrefix_next, collectedPrefix_symbolic_step]
      dsimp only
      rw [← ih, collectedPrefix_next, Nat.mul_add]
      omega

lemma collectedPrefix_points (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) (t : Tuning) :
    (codeSymbolic t (collectedPrefix worker round x B n s).2).points = (codeSymbolic t s).points := by
  induction n with
  | zero => rfl
  | succ n ih => rw [collectedPrefix_symbolic_step]; exact ih

lemma collectedPrefix_records (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let new := codeSymbolic t (collectedPrefix worker round x B n s).2
    ∀ j < n, new.vectors (s.next + 3 * j + 1) = (Finsupp.single (s.next + 3 * j + 1) 1, 0) ∧
      new.queryPoints (s.next + 3 * j + 1) = (codeSymbolic t s).points x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have he := (collectedPrefix_aligned worker round x B n s t hn).symm.trans
        (collectedPrefix_next worker round x B n s)
      dsimp only
      intro j hj
      rw [collectedPrefix_symbolic_step]
      by_cases hjn : j = n
      · subst j
        simp [he, collectedPrefix_points]
      · have hjn' : j < n := by omega
        have hne : s.next + 3 * j + 1 ≠ s.next + 3 * n + 1 := by omega
        simpa only [he, Function.update_of_ne hne] using ih j hjn'

lemma collectedPrefix_sets (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let new := codeSymbolic t (collectedPrefix worker round x B n s).2
    new.queries = (codeSymbolic t s).queries ∪ (Finset.range n).image (fun j => s.next + 3 * j + 1) ∧
      new.sharps = (codeSymbolic t s).sharps ∧ new.units = (codeSymbolic t s).units := by
  induction n with
  | zero => simp [collectedPrefix_zero]
  | succ n ih =>
      have he := (collectedPrefix_aligned worker round x B n s t hn).symm.trans
        (collectedPrefix_next worker round x B n s)
      dsimp only
      rw [collectedPrefix_symbolic_step]
      simp [he, Finset.range_add_one, Finset.union_insert, ih.1, ih.2.1, ih.2.2]

lemma collectedBatch_prefix (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) :
    (collectedBatch worker round x B).run s =
      let z := collectedPrefix worker round x B B s
      emit (.mix 0 z.1) z.2 := rfl

lemma collectedBatch_register (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) :
    ((collectedBatch worker round x B).run s).1 = s.next + 3 * B := by
  rw [collectedBatch_prefix]
  exact collectedPrefix_next worker round x B B s

lemma collectedBatch_next (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) :
    ((collectedBatch worker round x B).run s).2.next = s.next + 3 * B + 1 := by
  rw [collectedBatch_prefix]
  change (collectedPrefix worker round x B B s).2.next + 1 = _
  rw [collectedPrefix_next]

lemma collectedBatch_symbolic (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let z := (collectedBatch worker round x B).run s
    (codeSymbolic t z.2).vectors z.1 =
      (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, ((Finsupp.single (s.next + 3 * j + 1) 1, 0) : LinearValue) := by
  rw [collectedBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  have ha := collectedPrefix_aligned worker round x B B s t hn
  simp only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, emit_apply, ha,
    Function.update_self]
  rw [collectedPrefix_terms]
  simp only [List.map_map, Function.comp_def, Coefficient.eval]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(collectedPrefix_records worker round x B B s t hn j (Finset.mem_range.mp hj)).1]

lemma buildExtends_collectedStep (worker : ℕ → ℕ) (round x B h : ℕ) (terms : List (Coefficient × ℕ)) :
    BuildExtends (collectedStep worker round x B h terms) := by
  unfold collectedStep
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro a
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro q
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro b
  exact buildExtends_pure _

lemma collectedPrefix_extends (worker : ℕ → ℕ) (round x B n : ℕ) (s : CodeState) :
    CodeExtends s (collectedPrefix worker round x B n s).2 := by
  induction n with
  | zero => exact codeExtends_refl s
  | succ n ih =>
      rw [collectedPrefix_succ]
      exact codeExtends_trans s _ _ ih (buildExtends_collectedStep worker round x B n _ _)

lemma buildExtends_collectedBatch (worker : ℕ → ℕ) (round x B : ℕ) :
    BuildExtends (collectedBatch worker round x B) := by
  intro s
  rw [show collectedBatch worker round x B s = (collectedBatch worker round x B).run s from rfl,
    collectedBatch_prefix]
  exact codeExtends_trans s _ _ (collectedPrefix_extends worker round x B B s) (codeExtends_emit _ _)

lemma buildExtends_batchStep (worker : ℕ → ℕ) (B k : ℕ) (points : ℕ → ℕ) :
    BuildExtends (batchStep worker B k points) := by
  unfold batchStep
  apply buildExtends_bind _ _ (buildExtends_collectedBatch worker k (points k) B)
  intro g
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro d
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro x
  exact buildExtends_pure _

lemma collectedBatch_aligned (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    ((collectedBatch worker round x B).run s).2.next =
      (codeSymbolic t ((collectedBatch worker round x B).run s).2).next := by
  rw [collectedBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  exact congrArg (fun n => n + 1) (collectedPrefix_aligned worker round x B B s t hn)

lemma collectedBatch_points (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) (t : Tuning) :
    (codeSymbolic t ((collectedBatch worker round x B).run s).2).points = (codeSymbolic t s).points := by
  rw [collectedBatch_prefix, codeSymbolic_emit]
  exact collectedPrefix_points worker round x B B s t

lemma collectedBatch_records (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) (j : ℕ) (hj : j < B) :
    (codeSymbolic t ((collectedBatch worker round x B).run s).2).queryPoints (s.next + 3 * j + 1) =
      (codeSymbolic t s).points x := by
  rw [collectedBatch_prefix, codeSymbolic_emit]
  exact (collectedPrefix_records worker round x B B s t hn j hj).2

lemma collectedBatch_sets (worker : ℕ → ℕ) (round x B : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let new := codeSymbolic t ((collectedBatch worker round x B).run s).2
    new.queries = (codeSymbolic t s).queries ∪ (Finset.range B).image (fun j => s.next + 3 * j + 1) ∧
      new.sharps = (codeSymbolic t s).sharps ∧ new.units = (codeSymbolic t s).units := by
  rw [collectedBatch_prefix, codeSymbolic_emit]
  exact collectedPrefix_sets worker round x B B s t hn

lemma batchStep_registers (worker : ℕ → ℕ) (B k : ℕ) (points : ℕ → ℕ) (s : CodeState) :
    (batchStep worker B k points s).1 = Function.update points (k + 1) (s.next + 3 * B + 2) ∧
      (batchStep worker B k points s).2.next = s.next + 3 * B + 3 := by
  simp only [batchStep, state_bind_apply, state_pure_apply, emit_apply]
  rw [show (collectedBatch worker k (points k) B s).2.next = s.next + 3 * B + 1 from
    collectedBatch_next worker k (points k) B s]
  constructor <;> congr 2

lemma batchStep_symbolic (worker : ℕ → ℕ) (B k : ℕ) (points : ℕ → ℕ) (s : CodeState)
    (η : ℝ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (batchStep worker B k points s).2
    new.points (s.next + 3 * B + 2) = (codeSymbolic t s).points (points k) +
      η • ((0, Finsupp.single (s.next + 3 * B + 1) 1) : LinearValue) ∧
    new.sharpInputs (s.next + 3 * B + 1) =
      (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, ((Finsupp.single (s.next + 3 * j + 1) 1, 0) : LinearValue) ∧
    new.queries = (codeSymbolic t s).queries ∪ (Finset.range B).image (fun j => s.next + 3 * j + 1) ∧
    new.sharps = insert (s.next + 3 * B + 1) (codeSymbolic t s).sharps ∧
    new.units = (codeSymbolic t s).units := by
  let t := canonicalTuning η B
  let z := (collectedBatch worker k (points k) B).run s
  have ha : z.2.next = (codeSymbolic t z.2).next := collectedBatch_aligned worker k (points k) B s t hn
  have hnext : z.2.next = s.next + 3 * B + 1 := collectedBatch_next worker k (points k) B s
  have he : (codeSymbolic t z.2).next = s.next + 3 * B + 1 := ha.symm.trans hnext
  have hv := collectedBatch_symbolic worker k (points k) B s t hn
  have hp := collectedBatch_points worker k (points k) B s t
  have hs := collectedBatch_sets worker k (points k) B s t hn
  have hm : codeSymbolic t (batchStep worker B k points s).2 =
      symbolicPerform (symbolicPerform (codeSymbolic t z.2) (.sharp 0 z.1))
        (.move 0 (points k) z.2.next η) := by
    simp only [batchStep, state_bind_apply, state_pure_apply]
    rw [codeSymbolic_emit, codeSymbolic_emit]
    rfl
  dsimp only
  rw [hm]
  simp only [symbolicPerform, symbolicStore, hnext, he,
    show s.next + 3 * B + 1 + 1 = s.next + 3 * B + 2 by omega,
    Function.update_self]
  exact ⟨by rw [hp], hv, hs.1, congrArg (insert (s.next + 3 * B + 1)) hs.2.1, hs.2.2⟩

lemma batchStep_query_record (worker : ℕ → ℕ) (B k : ℕ) (points : ℕ → ℕ) (s : CodeState)
    (t : Tuning) (hn : s.next = (codeSymbolic t s).next) (j : ℕ) (hj : j < B) :
    (codeSymbolic t (batchStep worker B k points s).2).queryPoints (s.next + 3 * j + 1) =
      (codeSymbolic t s).points (points k) := by
  simp only [batchStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
    InstructionTemplate.instantiate, symbolicPerform, symbolicStore]
  exact collectedBatch_records worker k (points k) B s t hn j hj

noncomputable def iteratePrefix (worker : ℕ → ℕ) (K B : ℕ) : (ℕ → ℕ) × CodeState :=
  (batchCode worker K B).run {}

lemma iteratePrefix_zero (worker : ℕ → ℕ) (B : ℕ) : iteratePrefix worker 0 B = ((fun _ => 0), {}) := rfl

lemma iteratePrefix_succ (worker : ℕ → ℕ) (K B : ℕ) :
    iteratePrefix worker (K + 1) B =
      let z := iteratePrefix worker K B
      batchStep worker B K z.1 z.2 :=
  state_forIn_range_succ (batchStep worker B) K (fun _ : ℕ => 0) ({} : CodeState)

lemma iteratePrefix_next (worker : ℕ → ℕ) (K B : ℕ) :
    (iteratePrefix worker K B).2.next = 1 + K * (3 * B + 3) := by
  induction K with
  | zero => simp [iteratePrefix_zero]
  | succ K ih =>
      rw [iteratePrefix_succ]
      dsimp only
      rw [(batchStep_registers worker B K _ _).2, ih, Nat.add_mul]
      omega

def mainIndex (B k : ℕ) : ℕ := k * (3 * B + 3)

def sharpIndex (B k : ℕ) : ℕ := k * (3 * B + 3) + 3 * B + 2

def queryIndex (B k h : ℕ) : ℕ := k * (3 * B + 3) + 3 * h + 2

lemma iteratePrefix_registers (worker : ℕ → ℕ) (K B : ℕ) :
    ∀ j ≤ K, (iteratePrefix worker K B).1 j = mainIndex B j := by
  induction K with
  | zero =>
      intro j hj
      have : j = 0 := by omega
      subst j
      simp [iteratePrefix_zero, mainIndex]
  | succ K ih =>
      rw [iteratePrefix_succ]
      dsimp only
      rw [(batchStep_registers worker B K _ _).1]
      intro j hj
      by_cases he : j = K + 1
      · subst j
        rw [Function.update_self, iteratePrefix_next]
        simp only [mainIndex, Nat.add_mul, Nat.one_mul]
        omega
      · rw [Function.update_of_ne he]
        exact ih j (by omega)

lemma iteratePrefix_aligned (worker : ℕ → ℕ) (K B : ℕ) (t : Tuning) :
    (iteratePrefix worker K B).2.next = (codeSymbolic t (iteratePrefix worker K B).2).next := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [iteratePrefix_succ]
      dsimp only
      simp only [batchStep, state_bind_apply, state_pure_apply]
      rw [codeSymbolic_emit, codeSymbolic_emit]
      exact congrArg (fun n => n + 1 + 1)
        (collectedBatch_aligned worker K ((iteratePrefix worker K B).1 K) B (iteratePrefix worker K B).2 t ih)

lemma iteratePrefix_extends (worker : ℕ → ℕ) (K B j : ℕ) (hj : j ≤ K) :
    CodeExtends (iteratePrefix worker j B).2 (iteratePrefix worker K B).2 := by
  induction K with
  | zero =>
      have : j = 0 := by omega
      subst j
      exact codeExtends_refl _
  | succ K ih =>
      by_cases h : j ≤ K
      · rw [iteratePrefix_succ]
        exact codeExtends_trans _ _ _ (ih h) (buildExtends_batchStep worker B K _ _)
      · have : j = K + 1 := by omega
        subst j
        exact codeExtends_refl _

lemma iteratePrefix_old (worker : ℕ → ℕ) (K B j : ℕ) (t : Tuning) (hj : j ≤ K) :
    (codeSymbolic t (iteratePrefix worker K B).2).points (mainIndex B j) =
      (codeSymbolic t (iteratePrefix worker j B).2).points (mainIndex B j) := by
  have hn : mainIndex B j < (codeSymbolic t (iteratePrefix worker j B).2).next := by
    rw [← iteratePrefix_aligned, iteratePrefix_next]
    dsimp [mainIndex]
    omega
  exact (codeExtends_symbolic t _ _ (iteratePrefix_extends worker K B j hj) _ hn).1

noncomputable def mainValue (worker : ℕ → ℕ) (B : ℕ) (η : ℝ) (k : ℕ) : LinearValue :=
  (codeSymbolic (canonicalTuning η B) (iteratePrefix worker k B).2).points (mainIndex B k)

lemma mainValue_zero (worker : ℕ → ℕ) (B : ℕ) (η : ℝ) : mainValue worker B η 0 = 0 := rfl

lemma mainValue_succ (worker : ℕ → ℕ) (B : ℕ) (η : ℝ) (k : ℕ) :
    mainValue worker B η (k + 1) = mainValue worker B η k +
      η • ((0, Finsupp.single (sharpIndex B k) 1) : LinearValue) := by
  have hh := (batchStep_symbolic worker B k (iteratePrefix worker k B).1 (iteratePrefix worker k B).2 η
    (iteratePrefix_aligned worker k B _)).1
  have he : (iteratePrefix worker k B).2.next + 3 * B + 2 = mainIndex B (k + 1) := by
    rw [iteratePrefix_next]
    dsimp [mainIndex]
    rw [Nat.add_mul]
    omega
  have hs : (iteratePrefix worker k B).2.next + 3 * B + 1 = sharpIndex B k := by
    rw [iteratePrefix_next]
    dsimp [sharpIndex]
    omega
  rw [he, hs, iteratePrefix_registers worker k B k le_rfl] at hh
  simpa only [mainValue, iteratePrefix_succ] using hh

lemma mainValue_raw (worker : ℕ → ℕ) (B : ℕ) (η : ℝ) (k : ℕ) :
    (mainValue worker B η k).1 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [mainValue_succ, Prod.fst_add, linearValue_fst_smul, smul_zero, add_zero, ih]

def querySet (B K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion (fun k => (Finset.range B).image (queryIndex B k))

def sharpSet (B K : ℕ) : Finset ℕ := (Finset.range K).image (sharpIndex B)

lemma iteratePrefix_sets (worker : ℕ → ℕ) (K B : ℕ) (η : ℝ) :
    let m := codeSymbolic (canonicalTuning η B) (iteratePrefix worker K B).2
    m.queries = querySet B K ∧ m.sharps = sharpSet B K ∧ m.units = ∅ := by
  induction K with
  | zero => simp [iteratePrefix_zero, codeSymbolic, codeInstructions, querySet, sharpSet]
  | succ K ih =>
      have hh := (batchStep_symbolic worker B K (iteratePrefix worker K B).1 (iteratePrefix worker K B).2 η
        (iteratePrefix_aligned worker K B _)).2.2
      have hq : (fun j => (iteratePrefix worker K B).2.next + 3 * j + 1) = queryIndex B K := by
        funext j
        rw [iteratePrefix_next]
        dsimp [queryIndex]
        omega
      have hs : (iteratePrefix worker K B).2.next + 3 * B + 1 = sharpIndex B K := by
        rw [iteratePrefix_next]
        dsimp [sharpIndex]
        omega
      rw [hq, hs, ih.1, ih.2.1, ih.2.2] at hh
      simpa only [iteratePrefix_succ, querySet, sharpSet, Finset.range_add_one, Finset.biUnion_insert,
        Finset.image_insert, Finset.union_comm] using hh

lemma iteratePrefix_records (worker : ℕ → ℕ) (K B k h : ℕ) (η : ℝ) (hk : k < K) (hh : h < B) :
    let m := codeSymbolic (canonicalTuning η B) (iteratePrefix worker K B).2
    m.queryPoints (queryIndex B k h) = mainValue worker B η k ∧
    m.sharpInputs (sharpIndex B k) =
      (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, ((Finsupp.single (queryIndex B k j) 1, 0) : LinearValue) := by
  let t := canonicalTuning η B
  have ha := iteratePrefix_aligned worker k B t
  have hq := batchStep_query_record worker B k (iteratePrefix worker k B).1 (iteratePrefix worker k B).2 t ha h hh
  have hs := (batchStep_symbolic worker B k (iteratePrefix worker k B).1 (iteratePrefix worker k B).2 η ha).2.1
  have hqi (j : ℕ) : (iteratePrefix worker k B).2.next + 3 * j + 1 = queryIndex B k j := by
    rw [iteratePrefix_next]
    dsimp [queryIndex]
    omega
  have hsi : (iteratePrefix worker k B).2.next + 3 * B + 1 = sharpIndex B k := by
    rw [iteratePrefix_next]
    dsimp [sharpIndex]
    omega
  rw [hqi, iteratePrefix_registers worker k B k le_rfl] at hq
  rw [hsi] at hs
  simp only [hqi] at hs
  have hqn : queryIndex B k h < (codeSymbolic t (iteratePrefix worker (k + 1) B).2).next := by
    rw [← iteratePrefix_aligned, iteratePrefix_next]
    dsimp [queryIndex]
    rw [Nat.add_mul]
    omega
  have hsn : sharpIndex B k < (codeSymbolic t (iteratePrefix worker (k + 1) B).2).next := by
    rw [← iteratePrefix_aligned, iteratePrefix_next]
    dsimp [sharpIndex]
    rw [Nat.add_mul]
    omega
  have he := iteratePrefix_extends worker K B (k + 1) (by omega)
  refine ⟨(codeExtends_symbolic t _ _ he _ hqn).2.2.1.trans ?_,
    (codeExtends_symbolic t _ _ he _ hsn).2.2.2.trans ?_⟩
  · simpa only [iteratePrefix_succ, mainValue] using hq
  · simpa only [iteratePrefix_succ] using hs

end LongTails.Proofs.BirchNonEuclideanBatch
