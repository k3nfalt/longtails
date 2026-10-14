import LongTails.Algorithms.ScalarNoisySearch
import LongTails.Proofs.ScalarNoisySearch
import LongTails.Proofs.ScalarEstimatorLaw
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

open MeasureTheory Classical

namespace OracleTemplate.ScalarNoisySearch

def nodeEquiv : Node ≃ ((ℝ × ℝ × ℕ) ⊕ (ℝ × ℕ × ℕ)) where
  toFun
    | .interval lo hi d => .inl (lo, hi, d)
    | .candidate x d k => .inr (x, d, k)
  invFun
    | .inl (lo, hi, d) => .interval lo hi d
    | .inr (x, d, k) => .candidate x d k
  left_inv n := by cases n <;> rfl
  right_inv n := by rcases n with ⟨x, y, d⟩ | ⟨x, d, k⟩ <;> rfl

instance : MeasurableSpace Node := MeasurableSpace.comap nodeEquiv inferInstance

set_option backward.isDefEq.respectTransparency false in
def nodeMeasurableEquiv : Node ≃ᵐ ((ℝ × ℝ × ℕ) ⊕ (ℝ × ℕ × ℕ)) where
  toEquiv := nodeEquiv
  measurable_toFun := comap_measurable nodeEquiv
  measurable_invFun := by
    change Measurable[(inferInstance : MeasurableSpace ((ℝ × ℝ × ℕ) ⊕ (ℝ × ℕ × ℕ))),
      MeasurableSpace.comap nodeEquiv (inferInstance : MeasurableSpace ((ℝ × ℝ × ℕ) ⊕ (ℝ × ℕ × ℕ)))] nodeEquiv.symm
    apply measurable_comap_iff.mpr
    convert (measurable_id : Measurable (id : ((ℝ × ℝ × ℕ) ⊕ (ℝ × ℕ × ℕ)) → _)) using 1
    exact nodeEquiv.self_comp_symm

lemma measurable_node_cases {Z : Type*} [MeasurableSpace Z] (f : Node → Z)
    (hi : Measurable (fun x : ℝ × ℝ × ℕ => f (.interval x.1 x.2.1 x.2.2)))
    (hc : Measurable (fun x : ℝ × ℕ × ℕ => f (.candidate x.1 x.2.1 x.2.2))) :
    Measurable f := by
  apply nodeMeasurableEquiv.symm.measurable_comp_iff.mp
  exact measurable_fun_sum hi hc

lemma measurable_interval : Measurable (fun x : ℝ × ℝ × ℕ => Node.interval x.1 x.2.1 x.2.2) :=
  nodeMeasurableEquiv.symm.measurable.comp measurable_inl

lemma measurable_candidate : Measurable (fun x : ℝ × ℕ × ℕ => Node.candidate x.1 x.2.1 x.2.2) :=
  nodeMeasurableEquiv.symm.measurable.comp measurable_inr

lemma measurable_queries (i : Fin 3) : Measurable (fun n => queries n i) := by
  apply measurable_node_cases
  · change Measurable (fun x : ℝ × ℝ × ℕ => if i = 0 then x.1 else if i = 1 then x.2.1 else (x.1 + x.2.1) / 2)
    split_ifs <;> fun_prop
  · exact measurable_fst

instance : MeasurableSpace (List Node) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

set_option backward.isDefEq.respectTransparency false in
def pathMeasurableEquiv : List Node ≃ᵐ Σ n, Fin n → Node where
  toEquiv := List.equivSigmaTuple
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    change Measurable[(inferInstance : MeasurableSpace (Σ n, Fin n → Node)),
      MeasurableSpace.comap List.equivSigmaTuple (inferInstance : MeasurableSpace (Σ n, Fin n → Node))]
      List.equivSigmaTuple.symm
    apply measurable_comap_iff.mpr
    convert (measurable_id : Measurable (id : (Σ n, Fin n → Node) → _)) using 1
    exact List.equivSigmaTuple.self_comp_symm

lemma measurable_sigma_source {α : Type*} {β : α → Type*} [∀ i, MeasurableSpace (β i)]
    {Z : Type*} [MeasurableSpace Z] (f : (Σ i, β i) → Z)
    (h : ∀ i, Measurable (fun x => f ⟨i, x⟩)) : Measurable f := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap f inferInstance ≤ ⨅ i, MeasurableSpace.map (Sigma.mk i) inferInstance
  apply le_iInf
  intro i
  apply (MeasurableSpace.gc_comap_map _ _ _).mp
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, inferInstance] using (h i).comap_le

lemma measurable_path_cases {Z : Type*} [MeasurableSpace Z] (f : List Node → Z)
    (h : ∀ n, Measurable (fun x : Fin n → Node => f (List.ofFn x))) : Measurable f := by
  apply pathMeasurableEquiv.symm.measurable_comp_iff.mp
  exact measurable_sigma_source _ h

lemma measurable_headD (fallback : Node) : Measurable (fun path : List Node => path.headD fallback) := by
  apply measurable_path_cases
  intro n
  cases n with
  | zero => simp
  | succ n => simpa only [List.ofFn_succ, List.headD_cons] using (measurable_pi_apply (0 : Fin (n + 1)))

lemma measurable_sigma_mk {α : Type*} {β : α → Type*} [∀ i, MeasurableSpace (β i)]
    (i : α) : Measurable (Sigma.mk i : β i → Σ j, β j) := by
  apply measurable_iff_le_map.mpr
  exact iInf_le _ i

lemma measurable_ofFn (n : ℕ) : Measurable (List.ofFn : (Fin n → Node) → List Node) :=
  pathMeasurableEquiv.symm.measurable.comp (measurable_sigma_mk n)

lemma measurable_retreat : Measurable retreat := by
  apply measurable_path_cases
  intro n
  cases n with
  | zero => simp [retreat]
  | succ n =>
    cases n with
    | zero =>
      convert measurable_ofFn 1 using 1
      funext x
      simp [retreat, List.ofFn_succ]
    | succ n =>
      have ht : Measurable (fun x : Fin (n + 2) → Node => fun i : Fin (n + 1) => x i.succ) :=
        measurable_pi_iff.mpr (fun i => measurable_pi_apply i.succ)
      have hm := (measurable_ofFn (n + 1)).comp ht
      simpa only [Function.comp_def, List.ofFn_succ, retreat] using hm

lemma measurable_recordedPoint (fallback : ℝ) : Measurable (recordedPoint fallback) := by
  let value : Node → ℝ
    | .interval _ _ _ => fallback
    | .candidate x _ _ => x
  have hv : Measurable value := measurable_node_cases value measurable_const measurable_fst
  have hm := hv.comp (measurable_headD (.interval 0 0 0))
  convert hm using 1
  funext path
  cases path with
  | nil => rfl
  | cons n rest => cases n <;> rfl

lemma measurable_length : Measurable (List.length : List Node → ℕ) := by
  apply measurable_path_cases
  intro n
  simpa only [List.length_ofFn] using
    (measurable_const : Measurable (fun _ : Fin n → Node => n))

lemma measurable_getD (i : ℕ) (fallback : Node) :
    Measurable (fun path : List Node => path[i]?.getD fallback) := by
  apply measurable_path_cases
  intro n
  by_cases hi : i < n
  · have hfun : (fun x : Fin n → Node => (List.ofFn x)[i]?.getD fallback) =
        fun x => x ⟨i, hi⟩ := by
      funext x
      rw [List.getElem?_eq_getElem (by simpa using hi)]
      simp
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun x : Fin n → Node => (List.ofFn x)[i]?.getD fallback) = fun _ => fallback := by
      funext x
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      rfl
    rw [hfun]
    exact measurable_const

lemma measurable_nat_selection {Z U : Type*} [MeasurableSpace Z] [MeasurableSpace U]
    (f : Z → U) (index : Z → ℕ) (hi : Measurable index) (family : ℕ → Z → U)
    (hf : ∀ n, Measurable (family n)) (he : ∀ z, f z = family (index z) z) : Measurable f := by
  intro A hA
  have hset : f ⁻¹' A = ⋃ n : ℕ, {z | index z = n} ∩ (family n ⁻¹' A) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨index z, rfl, (he z) ▸ hz⟩
    · rintro ⟨n, hn, hz⟩
      rw [he z, hn]
      exact hz
  rw [hset]
  exact MeasurableSet.iUnion (fun n => (hi (measurableSet_singleton n)).inter ((hf n) hA))

lemma measurable_cons : Measurable (fun w : Node × List Node => w.1 :: w.2) := by
  let family : ℕ → Node × List Node → List Node := fun n w =>
    List.ofFn (Fin.cons w.1 (fun i : Fin n => w.2[i.val]?.getD (.interval 0 0 0)))
  apply measurable_nat_selection _ (fun w : Node × List Node => w.2.length)
    (measurable_length.comp measurable_snd) family
  · intro n
    apply (measurable_ofFn (n + 1)).comp
    apply measurable_pi_iff.mpr
    intro i
    cases i using Fin.cases with
    | zero => exact measurable_fst
    | succ i => exact (measurable_getD i.val (.interval 0 0 0)).comp measurable_snd
  · intro w
    dsimp only [family]
    rw [List.ofFn_succ]
    congr 1
    have he : (fun i : Fin w.2.length => w.2[i.val]?.getD (.interval 0 0 0)) = w.2.get := by
      funext i
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    rw [he]
    simp only [Fin.cons_succ, List.ofFn_get]

lemma measurable_node_prod_cases {Z U : Type*} [MeasurableSpace Z] [MeasurableSpace U]
    (f : Node × Z → U)
    (hi : Measurable (fun x : (ℝ × ℝ × ℕ) × Z => f (.interval x.1.1 x.1.2.1 x.1.2.2, x.2)))
    (hc : Measurable (fun x : (ℝ × ℕ × ℕ) × Z => f (.candidate x.1.1 x.1.2.1 x.1.2.2, x.2))) :
    Measurable f := by
  apply (nodeMeasurableEquiv.symm.prodCongr (MeasurableEquiv.refl Z)).measurable_comp_iff.mp
  apply (MeasurableEquiv.sumProdDistrib (ℝ × ℝ × ℕ) (ℝ × ℕ × ℕ) Z).symm.measurable_comp_iff.mp
  exact measurable_fun_sum hi hc

@[fun_prop]
lemma measurable_interval_mk {Z : Type*} [MeasurableSpace Z] {lo hi : Z → ℝ} {d : Z → ℕ}
    (hlo : Measurable lo) (hhi : Measurable hi) (hd : Measurable d) :
    Measurable (fun z => Node.interval (lo z) (hi z) (d z)) :=
  measurable_interval.comp (hlo.prodMk (hhi.prodMk hd))

@[fun_prop]
lemma measurable_candidate_mk {Z : Type*} [MeasurableSpace Z] {x : Z → ℝ} {d k : Z → ℕ}
    (hx : Measurable x) (hd : Measurable d) (hk : Measurable k) :
    Measurable (fun z => Node.candidate (x z) (d z) (k z)) :=
  measurable_candidate.comp (hx.prodMk (hd.prodMk hk))

@[fun_prop]
lemma measurable_path_cons {Z : Type*} [MeasurableSpace Z] {head : Z → Node} {tail : Z → List Node}
    (hh : Measurable head) (ht : Measurable tail) : Measurable (fun z => head z :: tail z) :=
  measurable_cons.comp (hh.prodMk ht)

lemma measurable_advance (ε : ℝ) (D ℓ : ℕ) :
    Measurable (fun w : (Fin 3 → ℝ) × List Node => advance ε D ℓ w.1 w.2) := by
  let F : Node × ((Fin 3 → ℝ) × List Node) → List Node := fun w =>
    match w.1 with
    | .interval lo hi d =>
      if |w.2.1 0| ≤ ε / 4 then .candidate lo d 0 :: w.2.2
      else if |w.2.1 1| ≤ ε / 4 then .candidate hi d 0 :: w.2.2
      else if |w.2.1 2| ≤ ε / 4 then .candidate ((lo + hi) / 2) d 0 :: w.2.2
      else if w.2.1 0 < 0 ∧ 0 < w.2.1 1 ∧ d < D then
        if w.2.1 2 < 0 then .interval ((lo + hi) / 2) hi (d + 1) :: w.2.2
        else .interval lo ((lo + hi) / 2) (d + 1) :: w.2.2
      else retreat w.2.2
    | .candidate x d k =>
      if ℓ ≤ k then w.2.2
      else if |w.2.1 0| ≤ ε / 2 then .candidate x d (k + 1) :: w.2.2
      else retreat w.2.2
  have hF : Measurable F := by
    apply measurable_node_prod_cases
    · dsimp only [F]
      have hr : Measurable (fun w : (ℝ × ℝ × ℕ) × ((Fin 3 → ℝ) × List Node) => retreat w.2.2) :=
        measurable_retreat.comp measurable_snd.snd
      refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) ?_
      refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) ?_
      refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) ?_
      have hcond : MeasurableSet {w : (ℝ × ℝ × ℕ) × ((Fin 3 → ℝ) × List Node) |
          w.2.1 0 < 0 ∧ 0 < w.2.1 1 ∧ w.1.2.2 < D} := by
        exact (measurableSet_lt
          (f := fun w : (ℝ × ℝ × ℕ) × ((Fin 3 → ℝ) × List Node) => w.2.1 0)
          (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const).inter
          ((measurableSet_lt (f := fun _ => (0 : ℝ))
            (g := fun w : (ℝ × ℝ × ℕ) × ((Fin 3 → ℝ) × List Node) => w.2.1 1)
            measurable_const (by fun_prop)).inter
            (measurableSet_lt
              (f := fun w : (ℝ × ℝ × ℕ) × ((Fin 3 → ℝ) × List Node) => w.1.2.2)
              (g := fun _ => D) (by fun_prop) measurable_const))
      refine Measurable.ite hcond ?_ hr
      exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)
    · dsimp only [F]
      have hr : Measurable (fun w : (ℝ × ℕ × ℕ) × ((Fin 3 → ℝ) × List Node) => retreat w.2.2) :=
        measurable_retreat.comp measurable_snd.snd
      refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by fun_prop) ?_
      exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) hr
  have hm := hF.comp (((measurable_headD (.interval 0 0 0)).comp measurable_snd).prodMk measurable_id)
  have hempty : MeasurableSet {w : (Fin 3 → ℝ) × List Node | w.2.length = 0} :=
    (measurable_length.comp measurable_snd) (measurableSet_singleton 0)
  have hall : Measurable (fun w : (Fin 3 → ℝ) × List Node =>
      if w.2.length = 0 then ([] : List Node) else F (w.2.headD (.interval 0 0 0), w)) :=
    Measurable.ite hempty measurable_const hm
  convert hall using 1
  funext w
  rcases w with ⟨reply, path⟩
  cases path with
  | nil => simp [advance]
  | cons n rest => cases n <;> simp only [List.length_cons, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, List.headD_cons, F, advance]

lemma measurable_trace {Z : Type*} [MeasurableSpace Z] (ε : ℝ) (D ℓ : ℕ)
    (replies : ℕ → Z → List Node → Fin 3 → ℝ)
    (hr : ∀ t, Measurable (fun w : Z × List Node => replies t w.1 w.2))
    (initial : Z → List Node) (hi : Measurable initial) (n : ℕ) :
    Measurable (fun z => trace ε D ℓ (fun t path => replies t z path) (initial z) n) := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    exact (measurable_advance ε D ℓ).comp (((hr n).comp (measurable_id.prodMk ih)).prodMk ih)

lemma measurable_trace_output {Z : Type*} [MeasurableSpace Z] (ε : ℝ) (D ℓ : ℕ)
    (replies : ℕ → Z → List Node → Fin 3 → ℝ)
    (hr : ∀ t, Measurable (fun w : Z × List Node => replies t w.1 w.2))
    (initial : Z → List Node) (hi : Measurable initial) (fallback : ℝ) (n : ℕ) :
    Measurable (fun z => recordedPoint fallback
      (trace ε D ℓ (fun t path => replies t z path) (initial z) n)) :=
  (measurable_recordedPoint fallback).comp (measurable_trace ε D ℓ replies hr initial hi n)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
lemma measurable_walkReplies {Z : Type*} [MeasurableSpace Z]
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (σ p ε x0 s : ℝ) (call t : ℕ) :
    Measurable (fun w : Z × List Node =>
      ScalarSearchExecution.walkReplies (fun j x => g j w.1 x) σ p ε x0 s call t w.2) := by
  let c := ScalarHeavyTailEstimator.calls σ p (ε / 96) 6
  let start := call + 3 * c * t
  have he (i : Fin 3) (offset : ℕ) : Measurable (fun w : Z × List Node =>
      s * ScalarHeavyTailEstimator.estimate σ p (ε / 96) 6
        (fun j => g (start + offset + j) w.1
          (x0 + s * queries (w.2.headD (.interval 0 0 0)) i))) := by
    have hpoint : Measurable (fun w : Z × List Node =>
        x0 + s * queries (w.2.headD (.interval 0 0 0)) i) := by
      have hq := (measurable_queries i).comp
        ((measurable_headD (.interval 0 0 0)).comp (measurable_snd : Measurable (Prod.snd : Z × List Node → List Node)))
      exact measurable_const.add (measurable_const.mul hq)
    have hstream : Measurable (fun w : Z × List Node => fun j : ℕ =>
        g (start + offset + j) w.1 (x0 + s * queries (w.2.headD (.interval 0 0 0)) i)) :=
      measurable_pi_iff.mpr (fun j => (hg _).comp (measurable_fst.prodMk hpoint))
    have hest : Measurable (fun ξ : ℕ → ℝ => ScalarHeavyTailEstimator.estimate σ p (ε / 96) 6 ξ) :=
      ScalarHeavyTailEstimator.measurable_estimate (X := fun x : ℝ => x) measurable_id σ p (ε / 96) 6
    have hcomp := hest.comp hstream
    exact hcomp.const_mul s
  apply measurable_pi_iff.mpr
  intro i
  simpa only [ScalarSearchExecution.walkReplies, ScalarSearchExecution.triplePlan_evalOracle_apply,
    start, c] using he i (c * i.val)

lemma measurable_walk_records {Z : Type*} [MeasurableSpace Z]
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (σ p ε x0 s : ℝ) (D call n : ℕ) (initial : Z → List Node) (hi : Measurable initial) :
    Measurable (fun z => recordedPoint 0
      (trace ε D (2 * D)
        (ScalarSearchExecution.walkReplies (fun j x => g j z x) σ p ε x0 s call)
        (initial z) n)) :=
  measurable_trace_output ε D (2 * D) _
    (fun t => measurable_walkReplies g hg σ p ε x0 s call t) initial hi 0 n

lemma measurable_prefix_trace {Ω : Type*} [MeasurableSpace Ω]
    {oracle : ℝ → Ω → ℝ} (ho : Measurable (Function.uncurry oracle))
    (σ p ε x0 s : ℝ) (D call n cut : ℕ) (path : List Node) :
    Measurable (fun ξ : Fin cut → Ω => trace ε D (2 * D)
      (ScalarSearchExecution.walkReplies
        (fun j x => if h : j < cut then oracle x (ξ ⟨j, h⟩) else 0)
        σ p ε x0 s call) path n) := by
  have hg (j : ℕ) : Measurable (fun w : (Fin cut → Ω) × ℝ =>
      if h : j < cut then oracle w.2 (w.1 ⟨j, h⟩) else 0) := by
    split_ifs with hj
    · exact ho.comp (measurable_snd.prodMk ((measurable_pi_apply (⟨j, hj⟩ : Fin cut)).comp measurable_fst))
    · exact measurable_const
  exact measurable_trace ε D (2 * D) _
    (fun t => measurable_walkReplies
      (fun j (ξ : Fin cut → Ω) x => if h : j < cut then oracle x (ξ ⟨j, h⟩) else 0)
      hg σ p ε x0 s call t) (fun _ => path) measurable_const n

lemma measurable_prefix_query {Ω : Type*} [MeasurableSpace Ω]
    {oracle : ℝ → Ω → ℝ} (ho : Measurable (Function.uncurry oracle))
    (σ p ε x0 s : ℝ) (D call n cut : ℕ) (path : List Node) (i : Fin 3) :
    Measurable (fun ξ : Fin cut → Ω => x0 + s * queries
      ((trace ε D (2 * D) (ScalarSearchExecution.walkReplies
        (fun j x => if h : j < cut then oracle x (ξ ⟨j, h⟩) else 0)
        σ p ε x0 s call) path n).headD (.interval 0 0 0)) i) := by
  exact measurable_const.add (measurable_const.mul ((measurable_queries i).comp
    ((measurable_headD (.interval 0 0 0)).comp
      (measurable_prefix_trace ho σ p ε x0 s D call n cut path))))

lemma measurable_walk_error {Ω : Type*} [MeasurableSpace Ω]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    (σ p ε x0 s : ℝ) (D call t : ℕ) (path : List Node) (i : Fin 3) :
    Measurable (fun ξ : ℕ → Ω =>
      let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
      let state := trace ε D (2 * D) replies path t
      replies t state i - s * μ (x0 + s * queries (state.headD (.interval 0 0 0)) i)) := by
  let g : ℕ → (ℕ → Ω) → ℝ → ℝ := fun j ξ x => oracle x (ξ j)
  have hg (j : ℕ) : Measurable (Function.uncurry (g j)) :=
    ho.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hstate := measurable_trace ε D (2 * D)
    (fun j ξ => ScalarSearchExecution.walkReplies (fun k x => g k ξ x) σ p ε x0 s call j)
    (fun j => measurable_walkReplies g hg σ p ε x0 s call j) (fun _ => path) measurable_const t
  have hvalue := (measurable_pi_apply i).comp
    ((measurable_walkReplies g hg σ p ε x0 s call t).comp (measurable_id.prodMk hstate))
  have hpoint := (measurable_queries i).comp ((measurable_headD (.interval 0 0 0)).comp hstate)
  have hx := (measurable_const (a := x0)).add ((measurable_const (a := s)).mul hpoint)
  exact hvalue.sub ((measurable_const (a := s)).mul (hμ.comp hx))

lemma measurable_badStep (g : ℝ → ℝ) (hg : Measurable g) (ε : ℝ) :
    Measurable (fun w : (Fin 3 → ℝ) × List Node => badStep g ε w.1 w.2) := by
  have hRel : MeasurableSet {w : (Fin 3 → ℝ) × List Node |
      Reliable g ε (w.2.headD (.interval 0 0 0)) w.1} := by
    simp only [Reliable, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (continuous_abs.measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).sub
        (hg.comp ((measurable_queries i).comp ((measurable_headD (.interval 0 0 0)).comp measurable_snd)))))
      measurable_const
  have hempty : MeasurableSet {w : (Fin 3 → ℝ) × List Node | w.2.length = 0} :=
    (measurable_length.comp measurable_snd) (measurableSet_singleton 0)
  have h : Measurable (fun w : (Fin 3 → ℝ) × List Node =>
      if w.2.length = 0 then (0 : ℕ) else
        if Reliable g ε (w.2.headD (.interval 0 0 0)) w.1 then 0 else 1) :=
    Measurable.ite hempty measurable_const (Measurable.ite hRel measurable_const measurable_const)
  convert h using 1
  funext w
  rcases w with ⟨reply, path⟩
  cases path <;> simp [badStep]

lemma measurable_walk_bad_count {Ω : Type*} [MeasurableSpace Ω]
    {oracle : ℝ → Ω → ℝ} {μ : ℝ → ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hμ : Measurable μ)
    (σ p ε x0 s : ℝ) (D call N : ℕ) (path : List Node) :
    Measurable (fun ξ : ℕ → Ω =>
      let replies := ScalarSearchExecution.walkReplies (fun j x => oracle x (ξ j)) σ p ε x0 s call
      ∑ t : Fin N, (badStep (fun x => s * μ (x0 + s * x)) ε
        (replies t (trace ε D (2 * D) replies path t))
        (trace ε D (2 * D) replies path t) : ℝ)) := by
  let g : ℕ → (ℕ → Ω) → ℝ → ℝ := fun j ξ x => oracle x (ξ j)
  have hg (j : ℕ) : Measurable (Function.uncurry (g j)) :=
    ho.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hmean : Measurable (fun x => s * μ (x0 + s * x)) := by fun_prop
  apply Finset.measurable_sum
  intro t ht
  have hstate := measurable_trace ε D (2 * D)
    (fun j ξ => ScalarSearchExecution.walkReplies (fun k x => g k ξ x) σ p ε x0 s call j)
    (fun j => measurable_walkReplies g hg σ p ε x0 s call j) (fun _ => path) measurable_const t
  have hvalue := (measurable_walkReplies g hg σ p ε x0 s call t).comp (measurable_id.prodMk hstate)
  have hn := (measurable_badStep _ hmean ε).comp (hvalue.prodMk hstate)
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn

lemma measurable_rootAttempt {Ω : Type*} [MeasurableSpace Ω]
    {oracle : ℝ → Ω → ℝ} (ho : Measurable (Function.uncurry oracle))
    (σ p ε x0 s endpoint : ℝ) (D call : ℕ) :
    Measurable (fun w : Fin (16 * D) × (ℕ → Ω) =>
      ScalarSearchExecution.evalOracle (fun j x => oracle x (w.2 j))
        (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s endpoint D w.1.val) call) := by
  let g : ℕ → (ℕ → Ω) → ℝ → ℝ := fun j ξ x => oracle x (ξ j)
  have hg (j : ℕ) : Measurable (Function.uncurry (g j)) :=
    ho.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  let point : Fin (16 * D) × (ℕ → Ω) → ℝ := fun w => x0 + s * recordedPoint 0
    (trace ε D (2 * D) (ScalarSearchExecution.walkReplies
      (fun j x => oracle x (w.2 j)) σ p ε x0 s call) [.interval 0 endpoint 0] w.1.val)
  have hrecord : Measurable (fun w : Fin (16 * D) × (ℕ → Ω) => recordedPoint 0
      (trace ε D (2 * D) (ScalarSearchExecution.walkReplies
        (fun j x => oracle x (w.2 j)) σ p ε x0 s call) [.interval 0 endpoint 0] w.1.val)) := by
    apply measurable_nat_selection _ (fun w => w.1.val) (by fun_prop)
      (fun t w => recordedPoint 0 (trace ε D (2 * D) (ScalarSearchExecution.walkReplies
        (fun j x => oracle x (w.2 j)) σ p ε x0 s call) [.interval 0 endpoint 0] t))
    · intro t
      exact (measurable_walk_records g hg σ p ε x0 s D call t
        (fun _ => [.interval 0 endpoint 0]) measurable_const).comp measurable_snd
    · intro w
      rfl
  have hx : Measurable point := measurable_const.add (measurable_const.mul hrecord)
  have hstream : Measurable (fun w : Fin (16 * D) × (ℕ → Ω) => fun j : ℕ =>
      oracle (point w) (w.2 (call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * (16 * D) + j))) := by
    apply measurable_pi_iff.mpr
    intro j
    exact ho.comp (hx.prodMk ((measurable_pi_apply _).comp measurable_snd))
  have he : Measurable (fun ξ : ℕ → ℝ => ScalarHeavyTailEstimator.estimate σ p (ε / 48) 6 ξ) :=
    ScalarHeavyTailEstimator.measurable_estimate (X := fun x : ℝ => x) measurable_id σ p (ε / 48) 6
  simpa only [ScalarSearchExecution.rootAttemptPlan_evalOracle, point, Function.comp_def] using hx.prodMk (he.comp hstream)

lemma measurable_rootAttempt_variable {Z : Type*} [MeasurableSpace Z]
    (g : ℕ → Z → ℝ → ℝ) (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (σ p ε x0 s : ℝ) (D call : ℕ) (endpoint : Z → ℝ) (hend : Measurable endpoint)
    (time : Z → Fin (16 * D)) (htime : Measurable time) :
    Measurable (fun z => ScalarSearchExecution.evalOracle (fun j x => g j z x)
      (ScalarSearchPlans.rootAttemptPlan σ p ε x0 s (endpoint z) D (time z).val) call) := by
  let initial : Z → List Node := fun z => [.interval 0 (endpoint z) 0]
  have hinit : Measurable initial := measurable_cons.comp
    ((measurable_interval.comp (measurable_const.prodMk (hend.prodMk measurable_const))).prodMk measurable_const)
  let point : Z → ℝ := fun z => x0 + s * recordedPoint 0
    (trace ε D (2 * D) (ScalarSearchExecution.walkReplies
      (fun j x => g j z x) σ p ε x0 s call) (initial z) (time z).val)
  have hindex : Measurable (fun z => (time z).val) :=
    (measurable_of_countable (fun i : Fin (16 * D) => i.val)).comp htime
  have hrecord : Measurable (fun z => recordedPoint 0
      (trace ε D (2 * D) (ScalarSearchExecution.walkReplies
        (fun j x => g j z x) σ p ε x0 s call) (initial z) (time z).val)) := by
    apply measurable_nat_selection _ (fun z => (time z).val) hindex
      (fun t z => recordedPoint 0 (trace ε D (2 * D) (ScalarSearchExecution.walkReplies
        (fun j x => g j z x) σ p ε x0 s call) (initial z) t))
    · intro t
      exact measurable_walk_records g hg σ p ε x0 s D call t initial hinit
    · intro z
      rfl
  have hx : Measurable point := measurable_const.add (measurable_const.mul hrecord)
  have hstream : Measurable (fun z => fun j : ℕ =>
      g (call + 3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * (16 * D) + j) z (point z)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (hg _).comp (measurable_id.prodMk hx)
  have he : Measurable (fun ξ : ℕ → ℝ => ScalarHeavyTailEstimator.estimate σ p (ε / 48) 6 ξ) :=
    ScalarHeavyTailEstimator.measurable_estimate (X := fun x : ℝ => x) measurable_id σ p (ε / 48) 6
  simpa only [ScalarSearchExecution.rootAttemptPlan_evalOracle, point, initial, Function.comp_def] using
    hx.prodMk (he.comp hstream)

end OracleTemplate.ScalarNoisySearch
