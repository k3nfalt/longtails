import LongTails.Proofs.BirchNonEuclideanCoefficients

namespace LongTails.Proofs.BirchNonEuclideanDelta

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients

lemma localMomentum_next (w x m H round : ℕ) (s : CodeState) :
    ((localMomentum w x m H round).run s).2.next = s.next + 4 * H :=
  localPrefix_next w H round H (x, m) s

lemma deltaStep_registers (H k : ℕ) (dispatch worker : ℕ → ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) :
    (deltaStep H dispatch worker k state s).1 =
      (Function.update state.1 (k + 1) (s.next + 4 * H + 6),
        Function.update state.2 (k + 1) (s.next + 4 * H + 7)) ∧
      (deltaStep H dispatch worker k state s).2.next = s.next + 4 * H + 8 := by
  simp only [deltaStep, state_bind_apply, state_pure_apply, emit_apply]
  have hn := localMomentum_next (worker k) (state.1 (dispatch k)) (state.2 (dispatch k)) H k
    { instructions := s.instructions ++ [.sendPoint 0 (worker k) (state.1 (dispatch k)),
        .sendVector 0 (worker k) (state.2 (dispatch k))], next := s.next + 1 + 1 }
  simp only [StateT.run, List.append_assoc, List.singleton_append] at hn ⊢
  rw [hn]
  constructor
  · congr 2 <;> omega
  · omega

noncomputable def deltaPrefix (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    ((ℕ → ℕ) × (ℕ → ℕ)) × CodeState :=
  let init := (localBatch 0 0 B).run {}
  (forIn (List.range K) ((fun _ => 0), (fun _ => init.1))
    (fun k state => ForInStep.yield <$> deltaStep H dispatch worker k state) :
      StateM CodeState ((ℕ → ℕ) × (ℕ → ℕ))) init.2

lemma deltaPrefix_zero (H : ℕ) (dispatch worker : ℕ → ℕ) (B : ℕ) :
    deltaPrefix H dispatch worker 0 B =
      let init := (localBatch 0 0 B).run {}
      (((fun _ => 0), (fun _ => init.1)), init.2) := rfl

lemma deltaPrefix_succ (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    deltaPrefix H dispatch worker (K + 1) B =
      let z := deltaPrefix H dispatch worker K B
      deltaStep H dispatch worker K z.1 z.2 :=
  state_forIn_range_succ _ K _ _

lemma deltaCode_prefix (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    (deltaCode H dispatch worker K B).run {} =
      ((deltaPrefix H dispatch worker K B).1.1, (deltaPrefix H dispatch worker K B).2) := rfl

lemma deltaPrefix_next (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    (deltaPrefix H dispatch worker K B).2.next = B + 2 + K * (4 * H + 8) := by
  induction K with
  | zero =>
      rw [deltaPrefix_zero]
      dsimp only
      rw [localBatch_next]
      simp
      omega
  | succ K ih =>
      rw [deltaPrefix_succ]
      dsimp only
      rw [(deltaStep_registers H K dispatch worker _ _).2, ih]
      rw [Nat.add_mul]
      omega

def mainIndex (H B k : ℕ) : ℕ := if k = 0 then 0 else B + k * (4 * H + 8)

def momentumIndex (H B k : ℕ) : ℕ := B + k * (4 * H + 8) + 1

def queryIndex (H B k h : ℕ) : ℕ := B + 4 + k * (4 * H + 8) + 4 * h

def sharpIndex (H B k h : ℕ) : ℕ := queryIndex H B k h + 2

lemma deltaPrefix_registers (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    (∀ j ≤ K, (deltaPrefix H dispatch worker K B).1.1 j = mainIndex H B j) ∧
      ∀ j ≤ K, (deltaPrefix H dispatch worker K B).1.2 j = momentumIndex H B j := by
  induction K with
  | zero =>
      constructor
      · intro j hj
        have : j = 0 := by omega
        subst j
        rfl
      · intro j hj
        have : j = 0 := by omega
        subst j
        rw [deltaPrefix_zero]
        dsimp only
        rw [localBatch_register]
        simp [momentumIndex, Nat.add_comm]
  | succ K ih =>
      rw [deltaPrefix_succ]
      dsimp only
      rw [(deltaStep_registers H K dispatch worker _ _).1]
      dsimp only
      constructor
      · intro j hj
        by_cases hjk : j = K + 1
        · subst j
          rw [Function.update_self, deltaPrefix_next]
          simp [mainIndex, Nat.add_mul]
          omega
        · rw [Function.update_of_ne hjk]
          exact ih.1 j (by omega)
      · intro j hj
        by_cases hjk : j = K + 1
        · subst j
          rw [Function.update_self, deltaPrefix_next]
          dsimp [momentumIndex]
          rw [Nat.add_mul]
          omega
        · rw [Function.update_of_ne hjk]
          exact ih.2 j (by omega)

lemma deltaPrefix_valid (workers H K B : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) :
    let z := deltaPrefix H dispatch worker K B
    CodeValid workers t z.2 ∧
      (∀ j, z.1.1 j ∈ (codeLayout t z.2).points 0) ∧
      ∀ j, z.1.2 j ∈ (codeLayout t z.2).vectors 0 := by
  have hx : 0 ∈ (codeLayout t {}).points 0 := by simp [codeLayout, codeInstructions, finalLayout]
  have hi := localBatch_valid workers t 0 0 B {} (codeValid_initial workers t) hw0 hx
  let init := (localBatch 0 0 B).run {}
  let Inv := fun (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) => CodeValid workers t s ∧
    (∀ j, state.1 j ∈ (codeLayout t s).points 0) ∧ ∀ j, state.2 j ∈ (codeLayout t s).vectors 0
  apply state_forIn_invariant (deltaStep H dispatch worker) (List.range K) Inv
  · intro k _ state s h
    have hc := deltaStep_valid workers H k dispatch worker t ht state s h.1 (hw k) h.2.1 h.2.2
    exact ⟨hc.1, hc.2.2⟩
  · exact ⟨hi.1, (fun _ => (hi.2.1 0).1 hx), fun _ => hi.2.2⟩

lemma buildExtends_deltaStep (H k : ℕ) (dispatch worker : ℕ → ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) : BuildExtends (deltaStep H dispatch worker k state) := by
  unfold deltaStep
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_localMomentum _ _ _ _ _)
  intro packet
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dx
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dm
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro x
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro m
  exact buildExtends_pure _

lemma deltaPrefix_extends_succ (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    CodeExtends (deltaPrefix H dispatch worker K B).2 (deltaPrefix H dispatch worker (K + 1) B).2 := by
  rw [deltaPrefix_succ]
  exact buildExtends_deltaStep H K dispatch worker _ _

lemma deltaPrefix_extends (H : ℕ) (dispatch worker : ℕ → ℕ) (K B j : ℕ) (hj : j ≤ K) :
    CodeExtends (deltaPrefix H dispatch worker j B).2 (deltaPrefix H dispatch worker K B).2 := by
  induction K with
  | zero =>
      have : j = 0 := by omega
      subst j
      exact codeExtends_refl _
  | succ K ih =>
      by_cases h : j ≤ K
      · exact codeExtends_trans _ _ _ (ih h) (deltaPrefix_extends_succ H dispatch worker K B)
      · have : j = K + 1 := by omega
        subst j
        exact codeExtends_refl _

lemma mainIndex_lt (H B j K : ℕ) (hj : j ≤ K) :
    mainIndex H B j < B + 2 + K * (4 * H + 8) := by
  have hm := Nat.mul_le_mul_right (4 * H + 8) hj
  simp only [mainIndex]
  split_ifs <;> omega

lemma momentumIndex_lt (H B j K : ℕ) (hj : j ≤ K) :
    momentumIndex H B j < B + 2 + K * (4 * H + 8) := by
  have hm := Nat.mul_le_mul_right (4 * H + 8) hj
  dsimp [momentumIndex]
  omega

lemma deltaPrefix_old (workers H K B j : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hj : j ≤ K) :
    (codeSymbolic t (deltaPrefix H dispatch worker K B).2).points (mainIndex H B j) =
      (codeSymbolic t (deltaPrefix H dispatch worker j B).2).points (mainIndex H B j) ∧
    (codeSymbolic t (deltaPrefix H dispatch worker K B).2).vectors (momentumIndex H B j) =
      (codeSymbolic t (deltaPrefix H dispatch worker j B).2).vectors (momentumIndex H B j) := by
  have hv := (deltaPrefix_valid workers H j B dispatch worker t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have hx : mainIndex H B j < (codeSymbolic t (deltaPrefix H dispatch worker j B).2).next := by
    rw [← hn, deltaPrefix_next]
    exact mainIndex_lt H B j j le_rfl
  have hm : momentumIndex H B j < (codeSymbolic t (deltaPrefix H dispatch worker j B).2).next := by
    rw [← hn, deltaPrefix_next]
    exact momentumIndex_lt H B j j le_rfl
  have he := deltaPrefix_extends H dispatch worker K B j hj
  exact ⟨(codeExtends_symbolic t _ _ he _ hx).1, (codeExtends_symbolic t _ _ he _ hm).2.1⟩

noncomputable def mainValue (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (k : ℕ) : LinearValue :=
  (codeSymbolic t (deltaPrefix H dispatch worker k B).2).points (mainIndex H B k)

noncomputable def bufferValue (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (k : ℕ) : LinearValue :=
  (codeSymbolic t (deltaPrefix H dispatch worker k B).2).vectors (momentumIndex H B k)

lemma delta_recurrences (workers H K B : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hs : dispatch K ≤ K) :
    mainValue H B dispatch worker (canonicalTuning η B) (K + 1) =
      mainValue H B dispatch worker (canonicalTuning η B) K +
        (1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
          ((0, Finsupp.single (sharpIndex H B K h) 1) : LinearValue) ∧
    bufferValue H B dispatch worker (canonicalTuning η B) (K + 1) =
      bufferValue H B dispatch worker (canonicalTuning η B) K +
        (localRaw (1 / (B : ℝ)) (queryIndex H B K 0)
          (bufferValue H B dispatch worker (canonicalTuning η B) (dispatch K)) H -
          bufferValue H B dispatch worker (canonicalTuning η B) (dispatch K)) := by
  let t := canonicalTuning η B
  let z := deltaPrefix H dispatch worker K B
  have hv := deltaPrefix_valid workers H K B dispatch worker t ht hw0 hw
  have hn := codeValid_symbolic_next workers t z.2 hv.1
  have hb := codeValid_register_bound workers t z.2 hv.1
  have hr := deltaStep_symbolic H K dispatch worker z.1 z.2 η B hn
    (fun j => hb.2 0 _ (hv.2.2 j)) (fun j => hb.1 0 _ (hv.2.1 j))
  have hregs := deltaPrefix_registers H dispatch worker K B
  have hnextregs := deltaPrefix_registers H dispatch worker (K + 1) B
  have hsrc := deltaPrefix_old workers H K B (dispatch K) dispatch worker t ht hw0 hw hs
  have hxn : (deltaStep H dispatch worker K z.1 z.2).1.1 (K + 1) = mainIndex H B (K + 1) := by
    simpa only [deltaPrefix_succ] using hnextregs.1 (K + 1) le_rfl
  have hmn : (deltaStep H dispatch worker K z.1 z.2).1.2 (K + 1) = momentumIndex H B (K + 1) := by
    simpa only [deltaPrefix_succ] using hnextregs.2 (K + 1) le_rfl
  dsimp only at hr
  rw [hxn, hmn, hregs.1 K le_rfl, hregs.2 K le_rfl, hregs.2 (dispatch K) hs,
    hsrc.2] at hr
  constructor
  · change (codeSymbolic t (deltaPrefix H dispatch worker (K + 1) B).2).points _ = _
    rw [deltaPrefix_succ, hr.1]
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    congr 2
    rw [show z.2.next = B + 2 + K * (4 * H + 8) from deltaPrefix_next H dispatch worker K B]
    dsimp [sharpIndex, queryIndex]
    omega
  · change (codeSymbolic t (deltaPrefix H dispatch worker (K + 1) B).2).vectors _ = _
    rw [deltaPrefix_succ, hr.2]
    congr 2
    congr 1
    rw [show z.2.next = B + 2 + K * (4 * H + 8) from deltaPrefix_next H dispatch worker K B]
    simp [queryIndex]
    omega

lemma mainValue_zero (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) :
    mainValue H B dispatch worker t 0 = 0 := by
  dsimp only [mainValue]
  rw [deltaPrefix_zero]
  dsimp only
  rw [localBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  change (codeSymbolic t (batchPrefix 0 0 B B {}).2).points 0 = 0
  rw [batchPrefix_points]
  rfl

lemma bufferValue_zero (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) :
    bufferValue H B dispatch worker t 0 =
      (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, ((Finsupp.single (1 + j) 1, 0) : LinearValue) := by
  have hh := localBatch_symbolic 0 0 B {} t rfl
  have hm := localBatch_register 0 0 B {}
  dsimp only [bufferValue]
  rw [deltaPrefix_zero]
  dsimp only
  rw [show momentumIndex H B 0 = ((localBatch 0 0 B).run {}).1 by rw [hm]; simp [momentumIndex, Nat.add_comm]]
  exact hh

noncomputable def coefficientMass : (ℕ →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ => (1 : ℝ))

lemma coefficientMass_single (q : ℕ) (c : ℝ) :
    coefficientMass (Finsupp.single q c) = c := by
  simp [coefficientMass]

lemma linearValue_fst_smul (a : ℝ) (v : LinearValue) : (a • v).1 = a • v.1 := rfl

lemma linearValue_snd_smul (a : ℝ) (v : LinearValue) : (a • v).2 = a • v.2 := rfl

lemma linearValue_fst_sum {ι : Type*} (s : Finset ι) (f : ι → LinearValue) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  map_sum (LinearMap.fst ℝ (ℕ →₀ ℝ) (ℕ →₀ ℝ)) f s

lemma linearValue_snd_sum {ι : Type*} (s : Finset ι) (f : ι → LinearValue) :
    (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 :=
  map_sum (LinearMap.snd ℝ (ℕ →₀ ℝ) (ℕ →₀ ℝ)) f s

lemma localRaw_mass (α : ℝ) (first : ℕ) (v : LinearValue) (n : ℕ)
    (hv : coefficientMass v.1 = 1) : coefficientMass (localRaw α first v n).1 = 1 := by
  induction n with
  | zero => exact hv
  | succ n ih =>
      simp only [localRaw, Prod.fst_add, linearValue_fst_smul, map_add, map_smul,
        coefficientMass_single, ih, smul_eq_mul]
      ring

lemma buffer_mass_direction (workers H B : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hB : 0 < B) :
    ∀ k, coefficientMass (bufferValue H B dispatch worker (canonicalTuning η B) k).1 = 1 ∧
      (bufferValue H B dispatch worker (canonicalTuning η B) k).2 = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          rw [bufferValue_zero]
          constructor
          · simp only [linearValue_fst_smul, linearValue_fst_sum, map_smul, map_sum, coefficientMass_single]
            simp [smul_eq_mul, ne_of_gt hB]
          · simp only [linearValue_snd_smul, linearValue_snd_sum, Finset.sum_const_zero, smul_zero]
      | succ k =>
          rw [(delta_recurrences workers H k B dispatch worker η ht hw0 hw (hsource k)).2]
          have hk := ih k (by omega)
          have hs := ih (dispatch k) (by have := hsource k; omega)
          constructor
          · simp only [Prod.fst_add, Prod.fst_sub, map_add, map_sub, hk.1, hs.1,
              localRaw_mass _ _ _ _ hs.1]
            ring
          · simp only [Prod.snd_add, Prod.snd_sub, localRaw_direction, hk.2, hs.2, smul_zero,
              sub_self, add_zero]

noncomputable def packetCoefficient (H B k q : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, (1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (H - 1 - h)) *
    Finsupp.single (queryIndex H B k h) (1 : ℝ) q

lemma buffer_coefficient_recurrence (workers H K B : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hs : dispatch K ≤ K) (q : ℕ) :
    (bufferValue H B dispatch worker (canonicalTuning η B) (K + 1)).1 q =
      (bufferValue H B dispatch worker (canonicalTuning η B) K).1 q -
        (1 - (1 - 1 / (B : ℝ)) ^ H) *
          (bufferValue H B dispatch worker (canonicalTuning η B) (dispatch K)).1 q +
        packetCoefficient H B K q := by
  rw [(delta_recurrences workers H K B dispatch worker η ht hw0 hw hs).2, localRaw_closed]
  simp only [Prod.fst_add, Prod.fst_sub, linearValue_fst_smul, linearValue_fst_sum,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
  have he : ∑ j ∈ Finset.range H, (1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (H - 1 - j)) *
      Finsupp.single (queryIndex H B K 0 + 4 * j) (1 : ℝ) q = packetCoefficient H B K q := by
    apply Finset.sum_congr rfl
    intro j _
    simp [queryIndex, Nat.add_assoc]
  rw [he]
  ring

lemma packetCoefficient_nonneg (H B k q : ℕ) (hB : 0 < B) : 0 ≤ packetCoefficient H B k q := by
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  apply Finset.sum_nonneg
  intro h _
  apply mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

lemma buffer_coefficients_nonnegative (workers H B R : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (q : ℕ) :
    ∀ k, 0 ≤ (bufferValue H B dispatch worker (canonicalTuning η B) k).1 q ∧
      (bufferValue H B dispatch worker (canonicalTuning η B) k).1 q ≤
        (bufferValue H B dispatch worker (canonicalTuning η B) 0).1 q +
          ∑ j ∈ Finset.range k, packetCoefficient H B j q := by
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hl0 : 0 ≤ 1 - (1 - 1 / (B : ℝ)) ^ H := by
    have hp : (1 - 1 / (B : ℝ)) ^ H ≤ 1 :=
      pow_le_one₀ (by linarith : 0 ≤ 1 - 1 / (B : ℝ)) (by linarith : 1 - 1 / (B : ℝ) ≤ 1)
    linarith
  have hi : 0 ≤ (bufferValue H B dispatch worker (canonicalTuning η B) 0).1 q := by
    rw [bufferValue_zero]
    simp only [linearValue_fst_smul, linearValue_fst_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
    apply mul_nonneg hα0
    apply Finset.sum_nonneg
    intro j _
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  have hh := LongTails.Proofs.BirchDelayedCoefficients.delayed_forcing_nonnegative
    (fun k => (bufferValue H B dispatch worker (canonicalTuning η B) k).1 q)
    (fun k => packetCoefficient H B k q) dispatch (1 - (1 - 1 / (B : ℝ)) ^ H) R
    hl0 hlam hdelay hi hsource (fun k => packetCoefficient_nonneg H B k q hB)
    (fun k => buffer_coefficient_recurrence workers H k B dispatch worker η ht hw0 hw (hsource k).1 q)
  exact fun k => ⟨(hh k).1, (hh k).2.2⟩

lemma queryIndex_injective (H B k h l j : ℕ) (hh : h < H) (hj : j < H)
    (he : queryIndex H B k h = queryIndex H B l j) : k = l ∧ h = j := by
  have hk : k = l := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hkl | hlk
    · have hm := Nat.mul_le_mul_right (4 * H + 8) (show k + 1 ≤ l by omega)
      rw [Nat.add_mul] at hm
      dsimp [queryIndex] at he
      omega
    · have hm := Nat.mul_le_mul_right (4 * H + 8) (show l + 1 ≤ k by omega)
      rw [Nat.add_mul] at hm
      dsimp [queryIndex] at he
      omega
  subst l
  exact ⟨rfl, by dsimp [queryIndex] at he; omega⟩

lemma weighted_single_sum_le {ι : Type*} (s : Finset ι) (index : ι → ℕ)
    (c : ι → ℝ) (a : ℝ) (q : ℕ) (ha : 0 ≤ a)
    (hinj : Set.InjOn index (↑s : Set ι)) (hc : ∀ i ∈ s, c i ≤ a) :
    (∑ i ∈ s, c i * Finsupp.single (index i) (1 : ℝ) q) ≤ a := by
  classical
  by_cases he : ∃ i ∈ s, index i = q
  · obtain ⟨i, hi, he⟩ := he
    rw [Finset.sum_eq_single i]
    · simpa [he] using hc i hi
    · intro j hj hji
      have hne : index j ≠ q := by
        intro heq
        exact hji (hinj hj hi (heq.trans he.symm))
      simp [hne]
    · exact fun h => False.elim (h hi)
  · have hz : ∀ i ∈ s, index i ≠ q := by simpa only [not_exists, not_and] using he
    have heq : (∑ i ∈ s, c i * Finsupp.single (index i) (1 : ℝ) q) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hz i hi]
    rw [heq]
    exact ha

lemma packetCoefficient_sum_le (H B K q : ℕ) (hB : 0 < B) :
    (∑ k ∈ Finset.range K, packetCoefficient H B k q) ≤ 1 / (B : ℝ) := by
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hh := weighted_single_sum_le ((Finset.range K) ×ˢ (Finset.range H))
    (fun z => queryIndex H B z.1 z.2)
    (fun z => 1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (H - 1 - z.2)) (1 / (B : ℝ)) q hα0
    (by
      intro x hx y hy he
      have hh := queryIndex_injective H B x.1 x.2 y.1 y.2
        (Finset.mem_range.mp (Finset.mem_product.mp hx).2)
        (Finset.mem_range.mp (Finset.mem_product.mp hy).2) he
      exact Prod.ext hh.1 hh.2)
    (by
      intro z _
      have hp : (1 - 1 / (B : ℝ)) ^ (H - 1 - z.2) ≤ 1 :=
        pow_le_one₀ (by linarith) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hp hα0])
  simpa only [Finset.sum_product, packetCoefficient] using hh

lemma packetCoefficient_old_zero (H B k q : ℕ) (hq : q ≤ B) : packetCoefficient H B k q = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  have hn : queryIndex H B k h ≠ q := by dsimp [queryIndex]; omega
  simp [hn]

lemma buffer_initial_coefficient (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (q : ℕ) :
    (bufferValue H B dispatch worker t 0).1 q =
      ∑ j ∈ Finset.range B, (1 / (B : ℝ)) * Finsupp.single (1 + j) (1 : ℝ) q := by
  rw [bufferValue_zero]
  simp only [linearValue_fst_smul, linearValue_fst_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, smul_eq_mul, Finset.mul_sum]

lemma buffer_initial_coefficient_le (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (q : ℕ) :
    (bufferValue H B dispatch worker t 0).1 q ≤ 1 / (B : ℝ) := by
  rw [buffer_initial_coefficient]
  exact weighted_single_sum_le (Finset.range B) (fun j => 1 + j) (fun _ => 1 / (B : ℝ))
    (1 / (B : ℝ)) q (by positivity) (by intro x _ y _ h; dsimp only at h; omega) (by intro _ _; rfl)

lemma buffer_initial_coefficient_fresh (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (q : ℕ)
    (hq : B < q) : (bufferValue H B dispatch worker t 0).1 q = 0 := by
  rw [buffer_initial_coefficient]
  apply Finset.sum_eq_zero
  intro j hj
  have hn : 1 + j ≠ q := by have := Finset.mem_range.mp hj; omega
  simp [hn]

lemma buffer_coefficient_bounds (workers H B R : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (q k : ℕ) :
    0 ≤ (bufferValue H B dispatch worker (canonicalTuning η B) k).1 q ∧
      (bufferValue H B dispatch worker (canonicalTuning η B) k).1 q ≤ 1 / (B : ℝ) := by
  have hh := buffer_coefficients_nonnegative workers H B R dispatch worker η ht hw0 hw hsource hB hlam hdelay q k
  refine ⟨hh.1, hh.2.trans ?_⟩
  by_cases hq : q ≤ B
  · simpa only [packetCoefficient_old_zero H B _ q hq, Finset.sum_const_zero, add_zero]
      using buffer_initial_coefficient_le H B dispatch worker (canonicalTuning η B) q
  · rw [buffer_initial_coefficient_fresh H B dispatch worker (canonicalTuning η B) q (by omega), zero_add]
    exact packetCoefficient_sum_le H B k q hB

lemma localRaw_future_zero (α : ℝ) (first : ℕ) (v : LinearValue)
    (hv : ∀ q, first ≤ q → v.1 q = 0) (n q : ℕ) (hq : first + 4 * n ≤ q) :
    (localRaw α first v n).1 q = 0 := by
  induction n with
  | zero => exact hv q (by omega)
  | succ n ih =>
      have hn : first + 4 * n ≠ q := by omega
      have hi := ih (by omega)
      simp only [localRaw, Prod.fst_add, linearValue_fst_smul, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul, hi, mul_zero, add_zero]
      simp [hn]

lemma localRaw_coefficient_bounds (α : ℝ) (first : ℕ) (v : LinearValue)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hv : ∀ q, 0 ≤ v.1 q ∧ v.1 q ≤ α)
    (hf : ∀ q, first ≤ q → v.1 q = 0) (n q : ℕ) :
    0 ≤ (localRaw α first v n).1 q ∧ (localRaw α first v n).1 q ≤ α := by
  induction n with
  | zero => exact hv q
  | succ n ih =>
      simp only [localRaw, Prod.fst_add, linearValue_fst_smul, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul]
      by_cases he : first + 4 * n = q
      · rw [localRaw_future_zero α first v hf n q (by omega)]
        simp [he, hα]
      · simp only [Finsupp.single_apply, ite_eq_right he, mul_zero, zero_add]
        constructor
        · exact mul_nonneg (by linarith) ih.1
        · have hh := mul_le_mul_of_nonneg_left ih.2 (by linarith : 0 ≤ 1 - α)
          nlinarith [sq_nonneg α]

lemma source_buffer_future_zero (workers H B k : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning)
    (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hs : dispatch k ≤ k) :
    ∀ q, queryIndex H B k 0 ≤ q → (bufferValue H B dispatch worker t (dispatch k)).1 q = 0 := by
  intro q hq
  have hv := (deltaPrefix_valid workers H (dispatch k) B dispatch worker t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have hm := Nat.mul_le_mul_right (4 * H + 8) hs
  have hnext : (codeSymbolic t (deltaPrefix H dispatch worker (dispatch k) B).2).next ≤ q := by
    rw [← hn, deltaPrefix_next]
    dsimp [queryIndex] at hq
    omega
  exact (codeSymbolic_causal _ t (momentumIndex H B (dispatch k)) q hnext).2.2.1

lemma local_buffer_coefficient_bounds (workers H B R k n : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (q : ℕ) :
    let v := localRaw (1 / (B : ℝ)) (queryIndex H B k 0)
      (bufferValue H B dispatch worker (canonicalTuning η B) (dispatch k)) n
    0 ≤ v.1 q ∧ v.1 q ≤ 1 / (B : ℝ) := by
  apply localRaw_coefficient_bounds
  · positivity
  · exact (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  · intro q
    exact buffer_coefficient_bounds workers H B R dispatch worker η ht hw0 hw hsource hB hlam hdelay q (dispatch k)
  · exact source_buffer_future_zero workers H B k dispatch worker _ ht hw0 hw (hsource k).1

lemma deltaStep_records (H k h : ℕ) (dispatch worker : ℕ → ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) (η : ℝ) (B : ℕ)
    (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hm : state.2 (dispatch k) < s.next) (hh : h < H) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (deltaStep H dispatch worker k state s).2
    let old := codeSymbolic t s
    new.queryPoints (s.next + 2 + 4 * h) =
      localPath (1 / (H : ℝ) * η) (s.next + 2) (old.points (state.1 (dispatch k))) h ∧
    new.sharpInputs (s.next + 2 + 4 * h + 2) =
      localRaw (1 / (B : ℝ)) (s.next + 2) (old.vectors (state.2 (dispatch k))) (h + 1) := by
  let t := canonicalTuning η B
  let w := worker k
  let src := dispatch k
  let s1 := (emit (.sendPoint 0 w (state.1 src)) s).2
  let s2 := (emit (.sendVector 0 w (state.2 src)) s1).2
  let packet := (localMomentum w (state.1 src) (state.2 src) H k).run s2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : codeSymbolic t s2 = { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
    simp [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, Nat.add_assoc]
  have ha2 : s2.next = (codeSymbolic t s2).next := by rw [hs2n, hs2, hn]
  have hm2 : state.2 src < s2.next := by rw [hs2n]; dsimp only [src]; omega
  have hr := localPrefix_records w H k H (state.1 src, state.2 src) s2 η B ha2 hm2 h hh
  have hr' : (codeSymbolic t packet.2).queryPoints (s.next + 2 + 4 * h) =
      localPath (1 / (H : ℝ) * η) (s.next + 2) ((codeSymbolic t s).points (state.1 src)) h ∧
      (codeSymbolic t packet.2).sharpInputs (s.next + 2 + 4 * h + 2) =
      localRaw (1 / (B : ℝ)) (s.next + 2) ((codeSymbolic t s).vectors (state.2 src)) (h + 1) := by
    have hp : (codeSymbolic t packet.2).queryPoints (s2.next + 4 * h) =
        localPath (1 / (H : ℝ) * η) s2.next ((codeSymbolic t s2).points (state.1 src)) h ∧
        (codeSymbolic t packet.2).sharpInputs (s2.next + 4 * h + 2) =
        localRaw (1 / (B : ℝ)) s2.next ((codeSymbolic t s2).vectors (state.2 src)) (h + 1) := by
      simpa only [packet, localMomentum_prefix] using hr
    rw [hs2n, hs2] at hp
    exact hp
  convert hr' using 1 <;>
    simp only [deltaStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
      InstructionTemplate.instantiate, symbolicPerform, symbolicStore, packet, s2, s1, w, src,
      t, StateT.run]

lemma deltaStep_sets (H k : ℕ) (dispatch worker : ℕ → ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) (hm : state.2 (dispatch k) < s.next) :
    let new := codeSymbolic t (deltaStep H dispatch worker k state s).2
    let old := codeSymbolic t s
    new.queries = old.queries ∪ (Finset.range H).image (fun h => s.next + 2 + 4 * h) ∧
      new.sharps = old.sharps ∪ (Finset.range H).image (fun h => s.next + 2 + 4 * h + 2) ∧
      new.units = old.units := by
  let w := worker k
  let src := dispatch k
  let s1 := (emit (.sendPoint 0 w (state.1 src)) s).2
  let s2 := (emit (.sendVector 0 w (state.2 src)) s1).2
  let packet := (localMomentum w (state.1 src) (state.2 src) H k).run s2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : codeSymbolic t s2 = { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
    simp [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, Nat.add_assoc]
  have ha2 : s2.next = (codeSymbolic t s2).next := by rw [hs2n, hs2, hn]
  have hm2 : state.2 src < s2.next := by rw [hs2n]; dsimp only [src]; omega
  have hr := localPrefix_sets w H k H (state.1 src, state.2 src) s2 t ha2 hm2
  have hr' : (codeSymbolic t packet.2).queries = (codeSymbolic t s).queries ∪
      (Finset.range H).image (fun h => s.next + 2 + 4 * h) ∧
      (codeSymbolic t packet.2).sharps = (codeSymbolic t s).sharps ∪
      (Finset.range H).image (fun h => s.next + 2 + 4 * h + 2) ∧
      (codeSymbolic t packet.2).units = (codeSymbolic t s).units := by
    simpa only [packet, localMomentum_prefix, hs2n, hs2] using hr
  convert hr' using 1 <;>
    simp only [deltaStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
      InstructionTemplate.instantiate, symbolicPerform, symbolicStore, packet, s2, s1, w, src,
      StateT.run]

def packetQueries (H B k : ℕ) : Finset ℕ := (Finset.range H).image (queryIndex H B k)

def packetSharps (H B k : ℕ) : Finset ℕ := (Finset.range H).image (sharpIndex H B k)

def querySet (H B K : ℕ) : Finset ℕ :=
  (Finset.range B).image (fun j => 1 + j) ∪ (Finset.range K).biUnion (packetQueries H B)

def sharpSet (H B K : ℕ) : Finset ℕ := (Finset.range K).biUnion (packetSharps H B)

lemma querySet_succ (H B K : ℕ) : querySet H B (K + 1) = querySet H B K ∪ packetQueries H B K := by
  simp [querySet, Finset.range_add_one, Finset.union_assoc, Finset.union_comm]

lemma sharpSet_succ (H B K : ℕ) : sharpSet H B (K + 1) = sharpSet H B K ∪ packetSharps H B K := by
  simp [sharpSet, Finset.range_add_one, Finset.union_comm]

lemma deltaPrefix_sets (workers H K B : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) :
    let m := codeSymbolic t (deltaPrefix H dispatch worker K B).2
    m.queries = querySet H B K ∧ m.sharps = sharpSet H B K ∧ m.units = ∅ := by
  induction K with
  | zero =>
      rw [deltaPrefix_zero]
      dsimp only
      rw [localBatch_prefix]
      dsimp only
      rw [codeSymbolic_emit]
      have hh := batchPrefix_sets 0 0 B B {} t rfl
      simpa only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, querySet, sharpSet,
        Finset.range_zero, Finset.biUnion_empty, Finset.union_empty, codeSymbolic, codeInstructions,
        List.map_nil, List.foldl_nil, Finset.empty_union] using hh
  | succ K ih =>
      let z := deltaPrefix H dispatch worker K B
      have hv := deltaPrefix_valid workers H K B dispatch worker t ht hw0 hw
      have hn := codeValid_symbolic_next workers t z.2 hv.1
      have hb := codeValid_register_bound workers t z.2 hv.1
      have hh := deltaStep_sets H K dispatch worker z.1 z.2 t hn (hb.2 0 _ (hv.2.2 _))
      have hq : (fun h => z.2.next + 2 + 4 * h) = queryIndex H B K := by
        funext h
        rw [show z.2.next = B + 2 + K * (4 * H + 8) from deltaPrefix_next H dispatch worker K B]
        dsimp [queryIndex]
        omega
      have he : (fun h => z.2.next + 2 + 4 * h + 2) = sharpIndex H B K := by
        funext h
        change (fun h => z.2.next + 2 + 4 * h) h + 2 = _
        rw [hq]
        rfl
      dsimp only at hh
      rw [hq, he] at hh
      rw [deltaPrefix_succ, querySet_succ, sharpSet_succ]
      exact ⟨hh.1.trans (congrArg (fun s => s ∪ packetQueries H B K) ih.1),
        hh.2.1.trans (congrArg (fun s => s ∪ packetSharps H B K) ih.2.1), hh.2.2.trans ih.2.2⟩

lemma deltaPrefix_new_records (workers H k B h : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hs : dispatch k ≤ k) (hh : h < H) :
    let t := canonicalTuning η B
    let m := codeSymbolic t (deltaPrefix H dispatch worker (k + 1) B).2
    m.queryPoints (queryIndex H B k h) = localPath (1 / (H : ℝ) * η) (queryIndex H B k 0)
      (mainValue H B dispatch worker t (dispatch k)) h ∧
    m.sharpInputs (sharpIndex H B k h) = localRaw (1 / (B : ℝ)) (queryIndex H B k 0)
      (bufferValue H B dispatch worker t (dispatch k)) (h + 1) := by
  let t := canonicalTuning η B
  let z := deltaPrefix H dispatch worker k B
  have hv := deltaPrefix_valid workers H k B dispatch worker t ht hw0 hw
  have hn := codeValid_symbolic_next workers t z.2 hv.1
  have hb := codeValid_register_bound workers t z.2 hv.1
  have hr := deltaStep_records H k h dispatch worker z.1 z.2 η B hn (hb.2 0 _ (hv.2.2 _)) hh
  have hregs := deltaPrefix_registers H dispatch worker k B
  have hsrc := deltaPrefix_old workers H k B (dispatch k) dispatch worker t ht hw0 hw hs
  have hnq : z.2.next + 2 = queryIndex H B k 0 := by
    rw [show z.2.next = B + 2 + k * (4 * H + 8) from deltaPrefix_next H dispatch worker k B]
    dsimp [queryIndex]
    omega
  have hq : z.2.next + 2 + 4 * h = queryIndex H B k h := by rw [hnq]; simp [queryIndex, Nat.add_assoc]
  have he : z.2.next + 2 + 4 * h + 2 = sharpIndex H B k h := by rw [hq]; rfl
  dsimp only at hr
  rw [hregs.1 (dispatch k) hs, hregs.2 (dispatch k) hs, hsrc.1, hsrc.2, he, hq, hnq] at hr
  simpa only [mainValue, bufferValue, deltaPrefix_succ, z, t] using hr

lemma deltaPrefix_records (workers H K B k h : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hs : dispatch k ≤ k) (hk : k < K) (hh : h < H) :
    let t := canonicalTuning η B
    let m := codeSymbolic t (deltaPrefix H dispatch worker K B).2
    m.queryPoints (queryIndex H B k h) = localPath (1 / (H : ℝ) * η) (queryIndex H B k 0)
      (mainValue H B dispatch worker t (dispatch k)) h ∧
    m.sharpInputs (sharpIndex H B k h) = localRaw (1 / (B : ℝ)) (queryIndex H B k 0)
      (bufferValue H B dispatch worker t (dispatch k)) (h + 1) := by
  let t := canonicalTuning η B
  have hv := (deltaPrefix_valid workers H (k + 1) B dispatch worker t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have he := deltaPrefix_extends H dispatch worker K B (k + 1) (by omega)
  have hq : queryIndex H B k h < (codeSymbolic t (deltaPrefix H dispatch worker (k + 1) B).2).next := by
    rw [← hn, deltaPrefix_next]
    dsimp [queryIndex]
    rw [Nat.add_mul]
    omega
  have hs' : sharpIndex H B k h < (codeSymbolic t (deltaPrefix H dispatch worker (k + 1) B).2).next := by
    rw [← hn, deltaPrefix_next]
    dsimp [sharpIndex, queryIndex]
    rw [Nat.add_mul]
    omega
  have hqr := (codeExtends_symbolic t _ _ he _ hq).2.2.1
  have hsr := (codeExtends_symbolic t _ _ he _ hs').2.2.2
  have hr := deltaPrefix_new_records workers H k B h dispatch worker η ht hw0 hw hs hh
  exact ⟨hqr.trans hr.1, hsr.trans hr.2⟩

lemma codeSymbolic_sharp_mass (s : CodeState) (t : Tuning) (e : ℕ) :
    coefficientMass ((codeSymbolic t s).sharpInputs e).1 =
      ∑ q ∈ (codeSymbolic t s).queries, ((codeSymbolic t s).sharpInputs e).1 q := by
  let a : Program := {
    instructions := codeInstructions t s
    outputWorker := 0
    outputCount := 0
    outputPoint := fun _ => 0 }
  have hsup := (LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_maps_supported a).sharpInputs e
  have hs : ((codeSymbolic t s).sharpInputs e).1 ∈
      Finsupp.supported ℝ ℝ ((codeSymbolic t s).queries : Set ℕ) := hsup.1
  simpa only [coefficientMass, smul_eq_mul, mul_one] using
    (Finsupp.linearCombination_apply_of_mem_supported (R := ℝ) (v := fun _ => (1 : ℝ)) hs)

lemma deltaPrefix_estimators (workers H K B R : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) :
    let t := canonicalTuning η B
    let m := codeSymbolic t (deltaPrefix H dispatch worker K B).2
    ∀ e ∈ m.sharps, (m.sharpInputs e).2 = 0 ∧
      (∑ q ∈ m.queries, (m.sharpInputs e).1 q) = 1 ∧
      (∑ q ∈ m.queries, (m.sharpInputs e).1 q ^ 2) ≤ 1 / (B : ℝ) := by
  intro t m e he
  have hsets := deltaPrefix_sets workers H K B dispatch worker t ht hw0 hw
  rw [hsets.2.1] at he
  obtain ⟨k, hk, h, hh, rfl⟩ := by
    simpa only [sharpSet, packetSharps, Finset.mem_biUnion, Finset.mem_image] using he
  have hk' := Finset.mem_range.mp hk
  have hh' := Finset.mem_range.mp hh
  have hr := (deltaPrefix_records workers H K B k h dispatch worker η ht hw0 hw (hsource k).1 hk' hh').2
  have hb := buffer_mass_direction workers H B dispatch worker η ht hw0 hw (fun k => (hsource k).1) hB (dispatch k)
  have hm : coefficientMass (m.sharpInputs (sharpIndex H B k h)).1 = 1 := by
    rw [hr]
    exact localRaw_mass _ _ _ _ hb.1
  have hmass : (∑ q ∈ m.queries, (m.sharpInputs (sharpIndex H B k h)).1 q) = 1 := by
    rw [← codeSymbolic_sharp_mass]
    exact hm
  refine ⟨?_, hmass, ?_⟩
  · rw [hr, localRaw_direction, hb.2, smul_zero]
  · apply LongTails.Proofs.BirchDelayedCoefficients.coefficient_square_sum_le m.queries _ _ ?_ ?_ hmass
    · intro q _
      rw [hr]
      exact (local_buffer_coefficient_bounds workers H B R k (h + 1) dispatch worker η ht hw0 hw hsource hB hlam hdelay q).1
    · intro q _
      rw [hr]
      exact (local_buffer_coefficient_bounds workers H B R k (h + 1) dispatch worker η ht hw0 hw hsource hB hlam hdelay q).2

lemma mainValue_closed (workers H B K : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) :
    mainValue H B dispatch worker (canonicalTuning η B) K =
      (1 / (H : ℝ) * η) • ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (sharpIndex H B k h) 1) : LinearValue) := by
  induction K with
  | zero => simp [mainValue_zero]
  | succ K ih =>
      rw [(delta_recurrences workers H K B dispatch worker η ht hw0 hw (hsource K)).1,
        ih, Finset.sum_range_succ, smul_add]

lemma mainValue_raw (workers H B K : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) :
    (mainValue H B dispatch worker (canonicalTuning η B) K).1 = 0 := by
  rw [mainValue_closed workers H B K dispatch worker η ht hw0 hw hsource]
  simp only [linearValue_fst_smul, linearValue_fst_sum, Finset.sum_const_zero, smul_zero]

lemma deltaPrefix_initial_records (workers H K B j : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) (hj : j < B) :
    (codeSymbolic t (deltaPrefix H dispatch worker K B).2).queryPoints (1 + j) = 0 := by
  have hz : (codeSymbolic t (deltaPrefix H dispatch worker 0 B).2).queryPoints (1 + j) = 0 := by
    rw [deltaPrefix_zero]
    dsimp only
    rw [localBatch_prefix]
    dsimp only
    rw [codeSymbolic_emit]
    have hr := (batchPrefix_records 0 0 B B {} t rfl j hj).2
    simpa only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, codeSymbolic,
      codeInstructions, List.map_nil, List.foldl_nil] using hr
  have hv := (deltaPrefix_valid workers H 0 B dispatch worker t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have hjn : 1 + j < (codeSymbolic t (deltaPrefix H dispatch worker 0 B).2).next := by
    rw [← hn, deltaPrefix_next]
    omega
  exact (codeExtends_symbolic t _ _ (deltaPrefix_extends H dispatch worker K B 0 (Nat.zero_le K)) _ hjn).2.2.1.trans hz

lemma deltaPrefix_query_linear (workers H K B : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) :
    let t := canonicalTuning η B
    let m := codeSymbolic t (deltaPrefix H dispatch worker K B).2
    ∀ q ∈ m.queries, (m.queryPoints q).1 = 0 := by
  intro t m q hq
  have hs := (deltaPrefix_sets workers H K B dispatch worker t ht hw0 hw).1
  rw [hs] at hq
  rcases Finset.mem_union.mp hq with hi | hi
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [deltaPrefix_initial_records workers H K B j dispatch worker t ht hw0 hw (Finset.mem_range.mp hj)]
    rfl
  · obtain ⟨k, hk, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, packetQueries, Finset.mem_image] using hi
    rw [(deltaPrefix_records workers H K B k h dispatch worker η ht hw0 hw (hsource k)
      (Finset.mem_range.mp hk) (Finset.mem_range.mp hh)).1, localPath_raw]
    exact mainValue_raw workers H B (dispatch k) dispatch worker η ht hw0 hw hsource

end LongTails.Proofs.BirchNonEuclideanDelta
