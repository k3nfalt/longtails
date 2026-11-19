import LongTails.Proofs.BlockLowerInstance

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.BlockLowerBound

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution LongTails.Proofs.AbcHardCounting
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcLowerAssembly LongTails.Proofs.FiniteSumNondualLowerAveraging
open LongTails.Proofs.FiniteSumNondualLowerBound LongTails.Proofs.BlockEmbedding
open LongTails.Proofs.BlockLowerInstance LongTails.Proofs.AbcLowerBound
open LongTails.Setups.BlockHeterogeneousNonconvex (blockProj)

variable {q : QParams} {a : Alloc q.B} {N : ℕ}

noncomputable def compState (hav : AllocValid q a N)
    (A : Algorithm (Space q.d) (Space q.d) (Space q.d)) (w : ∀ j, Word q a j) (seed : A.Seed)
    (ω : ℕ → ℝ) : ℕ → A.State
  | 0 => A.initial seed
  | t + 1 => A.update (compState hav A w seed ω t)
      (hardG hav w (A.query (compState hav A w seed ω t)).2 (ω t))

lemma comp_iterate (hav : AllocValid q a N) (A : Algorithm (Space q.d) (Space q.d) (Space q.d))
    (w : ∀ j, Word q a j) (seed : A.Seed) (ω : ℕ → ℝ) (M : ℕ) :
    ((fun sc : A.State × ℕ => (A.update sc.1 (hardG hav w (A.query sc.1).2 (ω sc.2)), sc.2 + 1))^[M]
      (A.initial seed, 0)) = (compState hav A w seed ω M, M) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_comp (hav : AllocValid q a N) (A : Algorithm (Space q.d) (Space q.d) (Space q.d))
    (w : ∀ j, Word q a j) (M : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardO hav w) A (fun _ => M) seed ω = A.output (compState hav A w seed ω M) := by
  rw [execute_indexed_of_answer (hardO hav w) A M seed ω
    (fun t query => hardG hav w query.2 (ω t)) (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (comp_iterate hav A w seed ω M)

noncomputable def othersG (hav : AllocValid q a N) (j : Fin q.B)
    (b : ∀ k : {k // k ≠ j}, Word q a k.1) (x : Space q.d) (u : ℝ) : Space q.d :=
  ∑ k : {k // k ≠ j}, extend q.blk k.1 (reply (sc hav k.1) (rate q a k.1)
    (coordinateEmbedding (b k)) (restrict q.blk k.1 q.x0) (restrict q.blk k.1 x) u)

lemma split_self (j : Fin q.B) (c : Word q a j) (b : ∀ k : {k // k ≠ j}, Word q a k.1) :
    (Equiv.piSplitAt j (Word q a)).symm (c, b) j = c := by
  have h := congrArg Prod.fst ((Equiv.piSplitAt j (Word q a)).apply_symm_apply (c, b))
  simpa only [Equiv.piSplitAt_apply] using h

lemma split_ne (j : Fin q.B) (c : Word q a j) (b : ∀ k : {k // k ≠ j}, Word q a k.1)
    (k : {k // k ≠ j}) : (Equiv.piSplitAt j (Word q a)).symm (c, b) k.1 = b k := by
  have h := congrArg (fun p => p.2 k) ((Equiv.piSplitAt j (Word q a)).apply_symm_apply (c, b))
  simpa only [Equiv.piSplitAt_apply] using h

lemma hardG_split (hav : AllocValid q a N) (j : Fin q.B) (c : Word q a j)
    (b : ∀ k : {k // k ≠ j}, Word q a k.1) (x : Space q.d) (u : ℝ) :
    hardG hav ((Equiv.piSplitAt j (Word q a)).symm (c, b)) x u =
      extend q.blk j (reply (sc hav j) (rate q a j) (coordinateEmbedding c)
        (restrict q.blk j q.x0) (restrict q.blk j x) u) + othersG hav j b x u := by
  unfold hardG othersG
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j, split_self]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [split_ne]

noncomputable def blockUpdate (hav : AllocValid q a N)
    (A : Algorithm (Space q.d) (Space q.d) (Space q.d)) (j : Fin q.B)
    (b : ∀ k : {k // k ≠ j}, Word q a k.1) (ω : ℕ → ℝ) (s : A.State × ℕ)
    (r : Space (blockSize q.blk j)) : A.State × ℕ :=
  (A.update s.1 (extend q.blk j r + othersG hav j b (A.query s.1).2 (ω s.2)), s.2 + 1)

lemma trueState_split (hav : AllocValid q a N) (A : Algorithm (Space q.d) (Space q.d) (Space q.d))
    (j : Fin q.B) (c : Word q a j) (b : ∀ k : {k // k ≠ j}, Word q a k.1) (seed : A.Seed)
    (ω : ℕ → ℝ) (t : ℕ) :
    trueState (sc hav j) (rate q a j) (coordinateEmbedding c) (restrict q.blk j q.x0)
      (fun s : A.State × ℕ => restrict q.blk j (A.query s.1).2) (blockUpdate hav A j b ω)
      (A.initial seed, 0) ω t =
      (compState hav A ((Equiv.piSplitAt j (Word q a)).symm (c, b)) seed ω t, t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [trueState]
    rw [ih]
    simp only [blockUpdate, compState, Prod.mk.injEq, and_true]
    rw [hardG_split]

theorem exists_failure (hav : AllocValid q a N) (hε : 0 < q.ε)
    (A : Algorithm (Space q.d) (Space q.d) (Space q.d)) :
    ∃ w : ∀ j, Word q a j, ¬ QSpec.successful q (hardF hav w)
        (fun z : A.Seed × ((k : ℕ) → (hardO hav w).Seed k) =>
          execute (hardO hav w) A (fun _ => N) z.1 z.2)
        ⟨(A.law : Measure _).prod ((hardO hav w).law : Measure _), inferInstance⟩ := by
  by_contra hcon
  push Not at hcon
  let W := ∀ j, Word q a j
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let phi : Fin q.B → W → A.Seed × (ℕ → ℝ) → ℝ := fun j w z =>
    ‖objGrad (sc hav j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
      (restrict q.blk j (A.output (compState hav A w z.1 z.2 N)))‖
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z => ∑ j, phi j w z
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) => ∑ j, ‖blockProj q.blk j
      (gradient (hardF hav w) (execute (hardO hav w) A (fun _ => N) z.1 z.2))‖) = loss w := by
    funext z
    simp only [loss, phi]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hardF_gradient, execute_comp, norm_blockProj_hardGrad]
  have hi (w : W) : Integrable (loss w) P := by
    have h := (hcon w).2.1
    rw [← hloss w]
    exact h
  have hle (w : W) : ∫ z, loss w z ∂P ≤ q.ε := by
    have h := (hcon w).2.2
    rw [← hloss w]
    exact h
  have hdim (j : Fin q.B) : chainDim (blockParams q a j) + 1 ≤ blockSize q.blk j := by
    have hv := hav.valid j
    have hn1 := chainDim_succ (blockParams q a j) hv
    have h := dimension_room (blockParams q a j) hv N (hav.budget j)
    have hT : ((chainDim (blockParams q a j) + 1 : ℕ) : ℝ) ≤ (blockParams q a j).d := by
      rw [hn1]
      nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength (blockParams q a j)) :
        (0 : ℝ) ≤ chainLength (blockParams q a j)) 3, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast hT
  have hcardj (j : Fin q.B) : 0 < Fintype.card (Word q a j) :=
    coordinateWords_card_pos _ _ (hdim j)
  have hcard : (0 : ℝ) < Fintype.card W := by
    have : 0 < Fintype.card W := by
      rw [Fintype.card_pi]
      exact Finset.prod_pos (fun j _ => hcardj j)
    exact_mod_cast this
  let good : Fin q.B → A.Seed × (ℕ → ℝ) → ℝ := fun j z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) |
      coinCount (revealBar (blockParams q a j)) z.2 N ≤ chainDim (blockParams q a j) / 2} 1 z
  have hblock (j : Fin q.B) (z : A.Seed × (ℕ → ℝ)) :
      3 * a.ε j * (7 / 8) * Fintype.card W * good j z ≤ ∑ w, phi j w z := by
    by_cases hz : coinCount (revealBar (blockParams q a j)) z.2 N ≤
        chainDim (blockParams q a j) / 2
    · have hg : good j z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hsum : ∑ w, phi j w z = ∑ b : (∀ k : {k // k ≠ j}, Word q a k.1),
          ∑ c : Word q a j, phi j ((Equiv.piSplitAt j (Word q a)).symm (c, b)) z := by
        rw [← Equiv.sum_comp (Equiv.piSplitAt j (Word q a)).symm, Fintype.sum_prod_type, Finset.sum_comm]
      have hb (b : ∀ k : {k // k ≠ j}, Word q a k.1) :
          3 * a.ε j * (7 / 8) * Fintype.card (Word q a j) ≤
            ∑ c : Word q a j, phi j ((Equiv.piSplitAt j (Word q a)).symm (c, b)) z := by
        have h := block_sum_bound (blockParams q a j) (hav.valid j) N (hav.budget j)
          (fun s : A.State × ℕ => restrict q.blk j (A.query s.1).2)
          (fun s : A.State × ℕ => restrict q.blk j (A.output s.1))
          (blockUpdate hav A j b z.2) (A.initial z.1, 0) z.2 hz
        refine le_of_le_of_eq h (Finset.sum_congr rfl (fun c _ => ?_))
        simp only [phi]
        rw [trueState_split, split_self]
      have hcardW : (Fintype.card W : ℝ) = Fintype.card (Word q a j) *
          Fintype.card (∀ k : {k // k ≠ j}, Word q a k.1) := by
        rw [Fintype.card_congr (Equiv.piSplitAt j (Word q a)), Fintype.card_prod, Nat.cast_mul]
      rw [hsum, hcardW]
      calc 3 * a.ε j * (7 / 8) * (↑(Fintype.card (Word q a j)) *
            ↑(Fintype.card (∀ k : {k // k ≠ j}, Word q a k.1)))
          = ∑ _b : (∀ k : {k // k ≠ j}, Word q a k.1),
              3 * a.ε j * (7 / 8) * Fintype.card (Word q a j) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun b _ => hb b)
    · have hg : good j z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      ∑ j, 3 * a.ε j * (7 / 8) * Fintype.card W * good j z ≤ ∑ w, loss w z := by
    simp only [loss]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun j _ => hblock j z)
  have hsetmeas (j : Fin q.B) : MeasurableSet {ω : ℕ → ℝ |
      coinCount (revealBar (blockParams q a j)) ω N ≤ chainDim (blockParams q a j) / 2} := by
    have h := (coinCount_measurable (revealBar (blockParams q a j)) N)
      (measurableSet_Iic (a := (((chainDim (blockParams q a j) / 2 : ℕ)) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas (j : Fin q.B) : MeasurableSet {z : A.Seed × (ℕ → ℝ) |
      coinCount (revealBar (blockParams q a j)) z.2 N ≤ chainDim (blockParams q a j) / 2} :=
    measurable_snd (hsetmeas j)
  have hgood_int (j : Fin q.B) : ∫ z, good j z ∂P = stream.real {ω |
      coinCount (revealBar (blockParams q a j)) ω N ≤ chainDim (blockParams q a j) / 2} := by
    rw [integral_indicator_one (hgoodmeas j)]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) |
        coinCount (revealBar (blockParams q a j)) z.2 N ≤ chainDim (blockParams q a j) / 2} =
        Prod.snd ⁻¹' {ω | coinCount (revealBar (blockParams q a j)) ω N ≤
          chainDim (blockParams q a j) / 2} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd (hsetmeas j), hm]
    rfl
  have hint_good (j : Fin q.B) :
      Integrable (fun z => 3 * a.ε j * (7 / 8) * Fintype.card W * good j z) P :=
    ((integrable_const (1 : ℝ)).indicator (hgoodmeas j)).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hmono := integral_mono (integrable_finsetSum Finset.univ (fun j _ => hint_good j))
    hint_sum hpt
  rw [integral_finsetSum Finset.univ (fun j _ => hint_good j),
    integral_finsetSum Finset.univ (fun w _ => hi w)] at hmono
  have hlower : ∑ j, 3 * a.ε j * (7 / 8) * Fintype.card W * (7 / 8) ≤
      ∑ j, ∫ z, 3 * a.ε j * (7 / 8) * Fintype.card W * good j z ∂P := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [integral_const_mul, hgood_int]
    have hfrac := good_count_fraction (blockParams q a j) (hav.valid j) N (hav.budget j)
    have hεj : 0 < a.ε j := (hav.valid j).2.2.2.2.1
    exact mul_le_mul_of_nonneg_left hfrac
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεj.le) (by norm_num)) hcard.le)
  have hupper : (∑ w : W, ∫ z, loss w z ∂P) ≤ Fintype.card W * q.ε := by
    calc _ ≤ ∑ _w : W, q.ε := Finset.sum_le_sum (fun w _ => hle w)
      _ = _ := by simp
  have hacc := hav.acc
  have hsumε : ∑ j, 3 * a.ε j * (7 / 8) * Fintype.card W * (7 / 8) =
      (147 / 64) * Fintype.card W * ∑ j, a.ε j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsumε] at hlower
  have h1 : (147 / 64) * Fintype.card W * ∑ j, a.ε j ≤ Fintype.card W * q.ε := by linarith
  have h2 : (147 / 128) * Fintype.card W * q.ε ≤ (147 / 64) * Fintype.card W * ∑ j, a.ε j := by
    have := mul_le_mul_of_nonneg_left hacc
      (mul_nonneg (by norm_num) hcard.le : (0 : ℝ) ≤ (147 / 128) * Fintype.card W)
    nlinarith
  nlinarith [mul_pos hcard hε]

end LongTails.Proofs.BlockLowerBound
