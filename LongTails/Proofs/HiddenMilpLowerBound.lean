import LongTails.Setups.HiddenMixedIntegerLinear
import LongTails.Proofs.Execution
import Mathlib.Data.Fintype.Powerset

namespace OracleTemplate.HiddenMixedIntegerLinear

open LongTails.Setups LongTails.Setups.HiddenMixedIntegerLinear Matrix
open LongTails.Setups.BoundedMixedIntegerLinear
  (objective toPoint MixedFeasible RelaxationFeasible RowFeasible InBox SolvesRelaxation
    IsRelaxationOracle SolvesMixed)

def cutVal {p : ℕ} (v : Finset (Fin p)) (x : Fin p → ℝ) : ℝ :=
  ∑ k, if k ∈ v then x k else -x k

lemma cutVal_le {p : ℕ} (v : Finset (Fin p)) (x : Fin p → ℝ) (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (δ : ℝ) (k0 : Fin p) (h : (k0 ∈ v ∧ x k0 ≤ 1 - δ) ∨ (k0 ∉ v ∧ δ ≤ x k0)) :
    cutVal v x ≤ v.card - δ := by
  classical
  have hs : ∑ k, ((if k ∈ v then (1 : ℝ) else 0) - if k = k0 then δ else 0) = v.card - δ := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.sum_ite_eq' Finset.univ k0]
    simp
  rw [← hs]
  unfold cutVal
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = k0
  · subst hk
    rcases h with ⟨hv, hle⟩ | ⟨hv, hle⟩
    · simp [hv]; linarith
    · simp [hv]; linarith
  · simp only [hk, ite_false, sub_zero]
    split_ifs
    · exact (hx k).2
    · linarith [(hx k).1]

lemma cutVal_add_sum {p : ℕ} (v : Finset (Fin p)) (x : Fin p → ℝ) (hx : ∀ k ∈ v, x k = 1) :
    cutVal v x + ∑ k, x k = 2 * v.card := by
  classical
  unfold cutVal
  rw [← Finset.sum_add_distrib]
  have : ∀ k, ((if k ∈ v then x k else -x k) + x k) = if k ∈ v then (2 : ℝ) else 0 := by
    intro k
    by_cases hk : k ∈ v
    · simp [hk, hx k hk]; norm_num
    · simp [hk]
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

def indicator {p : ℕ} (F : Finset (Fin p)) : Fin p → ℝ := fun k => if k ∈ F then 1 else 0

lemma cutVal_indicator_self {p : ℕ} (F : Finset (Fin p)) : cutVal F (indicator F) = F.card := by
  classical
  unfold cutVal indicator
  have : ∀ k, (if k ∈ F then (if k ∈ F then (1 : ℝ) else 0) else -(if k ∈ F then 1 else 0)) =
      if k ∈ F then 1 else 0 := by
    intro k; by_cases hk : k ∈ F <;> simp [hk]
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

abbrev CutIndex (p r : ℕ) := {v : Finset (Fin p) // v.card ≤ r}

noncomputable def cutEquiv (p r : ℕ) : CutIndex p r ≃ Fin (Fintype.card (CutIndex p r)) :=
  Fintype.equivFin _

abbrev hardPublic (p : ℕ) : Public := ⟨p, 0, fun _ => 1, fun i => i.elim0, fun _ => 0, fun _ => 1⟩

noncomputable def hardA (p r : ℕ) (w : Finset (Fin p)) :
    Matrix (Fin (Fintype.card (CutIndex p r))) (Fin p) ℝ := fun i k => open Classical in
  if ((cutEquiv p r).symm i).1 = w then 0 else if k ∈ ((cutEquiv p r).symm i).1 then 1 else -1

noncomputable def hardB (p r : ℕ) (w : Finset (Fin p)) :
    Fin (Fintype.card (CutIndex p r)) → ℝ := fun i => open Classical in
  if ((cutEquiv p r).symm i).1 = w then 1 else (((cutEquiv p r).symm i).1.card : ℝ) - 1 / 2

noncomputable abbrev hardInstance (p r : ℕ) (w : Finset (Fin p)) : Params where
  toPublic := hardPublic p
  m := Fintype.card (CutIndex p r)
  A := hardA p r w
  G := fun _ j => j.elim0
  b := hardB p r w
  lam := 0

lemma row_value (p r : ℕ) (w : Finset (Fin p)) (x : (Fin p → ℝ) × (Fin 0 → ℝ))
    (i : Fin (Fintype.card (CutIndex p r))) :
    ((hardInstance p r w).A *ᵥ x.1 + (hardInstance p r w).G *ᵥ x.2) i =
      open Classical in if ((cutEquiv p r).symm i).1 = w then 0
        else cutVal ((cutEquiv p r).symm i).1 x.1 := by
  classical
  have hG : (hardInstance p r w).G *ᵥ x.2 = 0 := by
    funext i
    simp only [mulVec, dotProduct, Pi.zero_apply]
    exact Finset.sum_of_isEmpty _
  rw [hG, add_zero]
  change ∑ k, hardA p r w i k * x.1 k = _
  unfold hardA cutVal
  split_ifs with h
  · simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring

lemma rowFeasible_iff (p r : ℕ) (w : Finset (Fin p)) (x : (Fin p → ℝ) × (Fin 0 → ℝ)) :
    RowFeasible (data (hardInstance p r w)) x ↔
      ∀ v : Finset (Fin p), v.card ≤ r → v ≠ w → cutVal v x.1 ≤ v.card - 1 / 2 := by
  classical
  constructor
  · intro h v hv hvw
    have := h ((cutEquiv p r) ⟨v, hv⟩)
    rw [row_value] at this
    simp only [Equiv.symm_apply_apply, hvw, ite_false] at this
    simpa [hardB, hvw] using this
  · intro h i
    rw [row_value]
    by_cases hi : ((cutEquiv p r).symm i).1 = w
    · simp only [hi, ite_true]
      simp [hardB, hi]
    · simp only [hi, ite_false]
      have := h _ ((cutEquiv p r).symm i).2 hi
      change _ ≤ hardB p r w i
      simpa [hardB, hi] using this

def BoxNE {p : ℕ} (β : (Fin p → ℤ) × (Fin p → ℤ)) : Prop :=
  ∀ k, β.1 k ≤ 1 ∧ 0 ≤ β.2 k ∧ β.1 k ≤ β.2 k

noncomputable def ones {p : ℕ} (β : (Fin p → ℤ) × (Fin p → ℤ)) : Finset (Fin p) :=
  open Classical in Finset.univ.filter fun k => 1 ≤ β.1 k

def Free {p : ℕ} (β : (Fin p → ℤ) × (Fin p → ℤ)) (k : Fin p) : Prop := β.1 k ≤ 0 ∧ 1 ≤ β.2 k

noncomputable def halfPoint {p : ℕ} (F : Finset (Fin p)) (u : Fin p) : Fin p → ℝ := fun k =>
  open Classical in if k ∈ F then 1 else if k = u then 1 / 2 else 0

def emptyY : Fin 0 → ℝ := fun i => i.elim0

noncomputable def canonAnswer (p r : ℕ) (β : Box (hardPublic p)) : Option (Point (hardPublic p)) :=
  open Classical in
  if ¬ BoxNE β then none
  else if r < (ones β).card then some (indicator (ones β), emptyY)
  else if h : ∃ k, Free β k then some (halfPoint (ones β) h.choose, emptyY)
  else none

noncomputable def hardAnswer (p r : ℕ) (w : Finset (Fin p)) (β : Box (hardPublic p)) :
    Option (Point (hardPublic p)) :=
  open Classical in
  if BoxNE β ∧ ones β = w then some (indicator w, emptyY) else canonAnswer p r β

noncomputable def hardOracle (p r : ℕ) (w : Finset (Fin p)) :
    Oracle (Box (hardPublic p)) (Option (Point (hardPublic p))) where
  answer _ query _ := hardAnswer p r w query.2

lemma hard_objective (p r : ℕ) (w : Finset (Fin p)) (x : (Fin p → ℝ) × (Fin 0 → ℝ)) :
    objective (data (hardInstance p r w)) x = ∑ k, x.1 k := by
  simp [objective, dotProduct]

lemma indicator_bounds {p : ℕ} (F : Finset (Fin p)) (k : Fin p) :
    0 ≤ indicator F k ∧ indicator F k ≤ 1 := by
  unfold indicator; split_ifs <;> norm_num

lemma halfPoint_bounds {p : ℕ} (F : Finset (Fin p)) (u k : Fin p) :
    0 ≤ halfPoint F u k ∧ halfPoint F u k ≤ 1 := by
  unfold halfPoint; split_ifs <;> norm_num

lemma exists_symmDiff {p : ℕ} {v w : Finset (Fin p)} (h : v ≠ w) :
    ∃ k0, (k0 ∈ v ∧ k0 ∉ w) ∨ (k0 ∉ v ∧ k0 ∈ w) := by
  by_contra hc
  push Not at hc
  exact h (Finset.ext fun k => ⟨fun hk => (hc k).1 hk,
    fun hw => by_contra fun hk => (hc k).2 hk hw⟩)

lemma cutVal_indicator_ne {p : ℕ} {v F : Finset (Fin p)} (h : v ≠ F) :
    cutVal v (indicator F) ≤ v.card - 1 / 2 := by
  classical
  obtain ⟨k0, hk⟩ := exists_symmDiff h
  have := cutVal_le v (indicator F) (indicator_bounds F) 1 k0 (by
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by simp [indicator, h2]⟩
    · exact Or.inr ⟨h1, by simp [indicator, h2]⟩)
  linarith

lemma cutVal_halfPoint {p : ℕ} (v F : Finset (Fin p)) {u : Fin p} (hu : u ∉ F) :
    cutVal v (halfPoint F u) ≤ v.card - 1 / 2 := by
  classical
  have hval : halfPoint F u u = 1 / 2 := by simp [halfPoint, hu]
  apply cutVal_le v _ (halfPoint_bounds F u) (1 / 2) u
  by_cases huv : u ∈ v
  · exact Or.inl ⟨huv, by rw [hval]; norm_num⟩
  · exact Or.inr ⟨huv, by rw [hval]⟩

lemma not_relaxation_of_not_ne {p r : ℕ} {w : Finset (Fin p)} {β : Box (hardPublic p)}
    (hβ : ¬ BoxNE β) (x : (Fin p → ℝ) × (Fin 0 → ℝ)) :
    ¬ RelaxationFeasible (data (hardInstance p r w)) β x := by
  rintro ⟨_, hroot, hbox⟩
  apply hβ
  intro k
  have h1 := hroot k
  have h2 := hbox k
  simp only [Int.cast_zero, Int.cast_one] at h1
  refine ⟨?_, ?_, ?_⟩
  · have : (β.1 k : ℝ) ≤ 1 := h2.1.trans h1.2
    exact_mod_cast this
  · have : (0 : ℝ) ≤ β.2 k := h1.1.trans h2.2
    exact_mod_cast this
  · have : (β.1 k : ℝ) ≤ β.2 k := h2.1.trans h2.2
    exact_mod_cast this

lemma relaxation_eq_one {p r : ℕ} {w : Finset (Fin p)} {β : Box (hardPublic p)}
    {x : (Fin p → ℝ) × (Fin 0 → ℝ)} (hx : RelaxationFeasible (data (hardInstance p r w)) β x)
    {k : Fin p} (hk : k ∈ ones β) : x.1 k = 1 := by
  classical
  have h1 := hx.2.1 k
  have h2 := hx.2.2 k
  simp only [Int.cast_zero, Int.cast_one] at h1
  have hk' : (1 : ℝ) ≤ β.1 k := by
    have := (Finset.mem_filter.1 hk).2
    exact_mod_cast this
  linarith [h2.1]

lemma relaxation_eq_zero {p r : ℕ} {w : Finset (Fin p)} {β : Box (hardPublic p)}
    {x : (Fin p → ℝ) × (Fin 0 → ℝ)} (hx : RelaxationFeasible (data (hardInstance p r w)) β x)
    {k : Fin p} (hk : k ∉ ones β) (hf : ¬ Free β k) : x.1 k = 0 := by
  classical
  have h1 := hx.2.1 k
  have h2 := hx.2.2 k
  simp only [Int.cast_zero, Int.cast_one] at h1
  have hlo : β.1 k ≤ 0 := by
    by_contra h
    exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩)
  have hhi : β.2 k ≤ 0 := by
    by_contra h
    exact hf ⟨hlo, by omega⟩
  have : (β.2 k : ℝ) ≤ 0 := by exact_mod_cast hhi
  linarith [h2.2]

lemma indicator_inBox {p r : ℕ} {w : Finset (Fin p)} {β : Box (hardPublic p)} (hβ : BoxNE β) :
    InBox (data (hardInstance p r w)) β (indicator (ones β)) := by
  classical
  intro k
  have h := hβ k
  by_cases hk : 1 ≤ β.1 k
  · have hm : k ∈ ones β := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
    simp only [indicator, hm, ite_true]
    constructor
    · exact_mod_cast h.1
    · have : (1 : ℤ) ≤ β.2 k := hk.trans h.2.2
      exact_mod_cast this
  · have hm : k ∉ ones β := fun hm => hk (Finset.mem_filter.1 hm).2
    simp only [indicator, hm, ite_false]
    constructor
    · have : β.1 k ≤ 0 := by omega
      exact_mod_cast this
    · exact_mod_cast h.2.1

lemma sum_indicator {p : ℕ} (F : Finset (Fin p)) : ∑ k, indicator F k = F.card := by
  classical
  unfold indicator
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma sum_halfPoint {p : ℕ} (F : Finset (Fin p)) {u : Fin p} (hu : u ∉ F) :
    ∑ k, halfPoint F u k = F.card + 1 / 2 := by
  classical
  have : ∀ k, halfPoint F u k = indicator F k + if k = u then 1 / 2 else 0 := by
    intro k
    unfold halfPoint indicator
    by_cases hk : k ∈ F
    · have : k ≠ u := fun h => hu (h ▸ hk)
      simp [hk, this]
    · simp [hk]
  simp only [this, Finset.sum_add_distrib, sum_indicator, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

lemma root_inBox {p r : ℕ} {w : Finset (Fin p)} {z : Fin p → ℝ} (hz : ∀ k, 0 ≤ z k ∧ z k ≤ 1) :
    InBox (data (hardInstance p r w)) ((hardInstance p r w).lo, (hardInstance p r w).hi) z := by
  intro k
  simpa using hz k

lemma root_bounds {p r : ℕ} {w : Finset (Fin p)} {β : Box (hardPublic p)}
    {x : (Fin p → ℝ) × (Fin 0 → ℝ)} (hx : RelaxationFeasible (data (hardInstance p r w)) β x)
    (k : Fin p) : 0 ≤ x.1 k ∧ x.1 k ≤ 1 := by
  simpa using hx.2.1 k

lemma sum_ge_card {p r : ℕ} {w : Finset (Fin p)} {β : Box (hardPublic p)}
    {x : (Fin p → ℝ) × (Fin 0 → ℝ)} (hx : RelaxationFeasible (data (hardInstance p r w)) β x) :
    ((ones β).card : ℝ) ≤ ∑ k, x.1 k := by
  classical
  rw [← sum_indicator]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ ones β
  · simp [indicator, hk, relaxation_eq_one hx hk]
  · simp only [indicator, hk, ite_false]
    exact (root_bounds hx k).1

lemma hardOracle_admissible (p r : ℕ) (w : Finset (Fin p)) :
    IsRelaxationOracle (data (hardInstance p r w)) (hardOracle p r w) := by
  classical
  intro _ query _
  change SolvesRelaxation (data (hardInstance p r w)) query.2 (hardAnswer p r w query.2)
  set β := query.2
  unfold hardAnswer
  by_cases hA : BoxNE β ∧ ones β = w
  · rw [ite_eq_left hA]
    refine ⟨⟨(rowFeasible_iff p r w _).2 fun v _ hvw => cutVal_indicator_ne hvw,
      root_inBox (indicator_bounds w), hA.2 ▸ indicator_inBox hA.1⟩, fun x hx => ?_⟩
    rw [hard_objective, hard_objective]
    have := sum_ge_card hx
    rw [hA.2] at this
    simpa [sum_indicator] using this
  rw [ite_eq_right hA]
  unfold canonAnswer
  by_cases hne : BoxNE β
  swap
  · rw [ite_eq_left hne]
    exact fun x => not_relaxation_of_not_ne hne x
  rw [ite_eq_right (not_not.2 hne)]
  have hw' : ones β ≠ w := fun h => hA ⟨hne, h⟩
  by_cases hc : r < (ones β).card
  · rw [ite_eq_left hc]
    refine ⟨⟨(rowFeasible_iff p r w _).2 fun v hv _ => cutVal_indicator_ne ?_,
      root_inBox (indicator_bounds _), indicator_inBox hne⟩, fun x hx => ?_⟩
    · rintro rfl; omega
    · rw [hard_objective, hard_objective]
      simpa [sum_indicator] using sum_ge_card hx
  rw [ite_eq_right hc]
  by_cases hf : ∃ k, Free β k
  · rw [dite_eq_left hf]
    set u := hf.choose
    have hfu : Free β u := hf.choose_spec
    have hu : u ∉ ones β := fun h => by
      have := (Finset.mem_filter.1 h).2
      have := hfu.1
      omega
    refine ⟨⟨(rowFeasible_iff p r w _).2 fun v _ _ => cutVal_halfPoint v _ hu,
      root_inBox (halfPoint_bounds _ _), fun k => ?_⟩, fun x hx => ?_⟩
    · have h := hne k
      unfold halfPoint
      by_cases hk : k ∈ ones β
      · have h1 : 1 ≤ β.1 k := (Finset.mem_filter.1 hk).2
        simp only [hk, ite_true]
        constructor
        · exact_mod_cast h.1
        · have : (1 : ℤ) ≤ β.2 k := h1.trans h.2.2
          exact_mod_cast this
      · simp only [hk, ite_false]
        by_cases hku : k = u
        · subst hku
          simp only [ite_true]
          have h1 : (β.1 u : ℝ) ≤ 0 := by exact_mod_cast hfu.1
          have h2 : (1 : ℝ) ≤ β.2 u := by exact_mod_cast hfu.2
          constructor <;> linarith
        · simp only [hku, ite_false]
          have h1 : β.1 k ≤ 0 := by
            by_contra h'
            exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩)
          constructor
          · exact_mod_cast h1
          · exact_mod_cast h.2.1
    · rw [hard_objective, hard_objective]
      change ∑ k, halfPoint (ones β) u k ≤ _
      rw [sum_halfPoint _ hu]
      have hrow := (rowFeasible_iff p r w x).1 hx.1 (ones β) (by omega) hw'
      have hadd := cutVal_add_sum (ones β) x.1 fun k hk => relaxation_eq_one hx hk
      linarith
  · rw [dite_eq_right hf]
    intro x hx
    push Not at hf
    have hx1 : x.1 = indicator (ones β) := by
      funext k
      unfold indicator
      by_cases hk : k ∈ ones β
      · simp only [hk, ite_true]; exact relaxation_eq_one hx hk
      · simp only [hk, ite_false]
        exact relaxation_eq_zero hx hk (hf k)
    have hrow := (rowFeasible_iff p r w x).1 hx.1 (ones β) (by omega) hw'
    rw [hx1, cutVal_indicator_self] at hrow
    linarith

lemma hardInstance_valid (p r : ℕ) (w : Finset (Fin p)) : spec.valid (hardInstance p r w) := by
  refine Or.inl ⟨fun _ => le_refl _, ?_⟩
  funext i
  exact i.elim0

def wPoint {p : ℕ} (w : Finset (Fin p)) : Solution (hardPublic p) :=
  open Classical in (fun k => if k ∈ w then 1 else 0, emptyY)

lemma toPoint_wPoint {p r : ℕ} (w : Finset (Fin p)) :
    toPoint (data (hardInstance p r w)) (wPoint w) = (indicator w, emptyY) := by
  classical
  simp only [toPoint, wPoint, Prod.mk.injEq, and_true]
  funext k
  unfold indicator
  split_ifs <;> simp

lemma wPoint_feasible (p r : ℕ) (w : Finset (Fin p)) :
    MixedFeasible (data (hardInstance p r w)) (wPoint w) := by
  classical
  refine ⟨?_, fun k => ?_⟩
  · rw [toPoint_wPoint]
    exact (rowFeasible_iff p r w _).2 fun v _ hvw => cutVal_indicator_ne hvw
  · simp only [wPoint]
    split_ifs <;> simp

lemma solves_unique (p r : ℕ) (w : Finset (Fin p)) (hw : w.card = r)
    {o : Option (Solution (hardPublic p))} (h : SolvesMixed (data (hardInstance p r w)) o) :
    ∃ x, o = some x ∧ ∀ k, (x.1 k = 1 ↔ k ∈ w) := by
  classical
  cases o with
  | none => exact absurd (wPoint_feasible p r w) (h _)
  | some x =>
    refine ⟨x, rfl, ?_⟩
    obtain ⟨hx, hopt⟩ := h
    set S := Finset.univ.filter fun k => x.1 k = 1
    have hcast : (toPoint (data (hardInstance p r w)) x).1 = indicator S := by
      funext k
      have hb := hx.2 k
      simp only at hb
      unfold indicator toPoint
      by_cases hk : x.1 k = 1
      · simp [S, hk]
      · have : x.1 k = 0 := by omega
        simp [S, this]
    have hle := hopt _ (wPoint_feasible p r w)
    rw [hard_objective, hard_objective, hcast, toPoint_wPoint, sum_indicator] at hle
    simp only [sum_indicator] at hle
    have hS : (S.card : ℝ) ≤ r := by rw [← hw]; exact hle
    have hSr : S.card ≤ r := by exact_mod_cast hS
    by_cases hSw : S = w
    · intro k
      rw [← hSw]
      simp [S]
    · have hrow := (rowFeasible_iff p r w _).1 hx.1 S hSr hSw
      rw [hcast, cutVal_indicator_self] at hrow
      linarith

lemma iterate_eq_of_agree {α : Type*} (f g : α → α) (x0 : α) (B : ℕ)
    (h : ∀ i < B, f (g^[i] x0) = g (g^[i] x0)) : f^[B] x0 = g^[B] x0 := by
  induction B with
  | zero => rfl
  | succ B ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun i hi => h i (by omega)]
    exact h B (by omega)

lemma hard_lower_bound (p r B : ℕ) (hB : B + 2 ≤ p.choose r)
    (A : Algorithm (Box (hardPublic p)) (Option (Point (hardPublic p)))
      (Option (Solution (hardPublic p)))) (seed : A.Seed) :
    ∃ w : Finset (Fin p), w.card = r ∧
      ¬ SolvesMixed (data (hardInstance p r w))
        (execute (hardOracle p r w) A (fun _ => B) seed (fun _ => ())) := by
  classical
  let g : A.State × ℕ → A.State × ℕ := fun sc =>
    (A.update sc.1 (canonAnswer p r (A.query sc.1).2), sc.2 + 1)
  let x0 : A.State × ℕ := (A.initial seed, 0)
  let hits : Finset (Finset (Fin p)) :=
    (Finset.range B).image fun i => ones (A.query (g^[i] x0).1).2
  let W := Finset.powersetCard r (Finset.univ : Finset (Fin p))
  have hW : W.card = p.choose r := by simp [W, Finset.card_powersetCard]
  have hcard : 1 < (W \ hits).card := by
    have h1 : hits.card ≤ B := (Finset.card_image_le).trans (by simp)
    have h2 := Finset.le_card_sdiff hits W
    omega
  have hexec : ∀ w ∈ W \ hits,
      execute (hardOracle p r w) A (fun _ => B) seed (fun _ => ()) = A.output (g^[B] x0).1 := by
    intro w hw
    rw [execute_indexed_of_answer (hardOracle p r w) A B seed (fun _ => ())
      (fun _ q => hardAnswer p r w q.2) (fun _ _ => rfl)]
    congr 2
    apply iterate_eq_of_agree
    intro i hi
    have hans : hardAnswer p r w (A.query (g^[i] x0).1).2 =
        canonAnswer p r (A.query (g^[i] x0).1).2 := by
      unfold hardAnswer
      rw [ite_eq_right]
      rintro ⟨_, heq⟩
      exact (Finset.mem_sdiff.1 hw).2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, heq⟩)
    simp only [g]
    rw [hans]
  obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 hcard
  by_contra hcon
  push Not at hcon
  have hc1 := (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1 hw1).1).2
  have hc2 := (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1 hw2).1).2
  have s1 := hcon w1 hc1
  have s2 := hcon w2 hc2
  rw [hexec w1 hw1] at s1
  rw [hexec w2 hw2] at s2
  obtain ⟨x1, hx1, hk1⟩ := solves_unique p r w1 hc1 s1
  obtain ⟨x2, hx2, hk2⟩ := solves_unique p r w2 hc2 s2
  rw [hx1] at hx2
  cases hx2
  exact hne (Finset.ext fun k => (hk1 k).symm.trans (hk2 k))

lemma not_convergence_hard (p r B : ℕ) (hB : B + 2 ≤ p.choose r)
    (budget : spec.Params → Fin spec.numOracles → ℕ)
    (hbud : ∀ w : Finset (Fin p), w.card = r → budget (hardInstance p r w) = fun _ => B) :
    ¬ Convergence spec budget := by
  rintro ⟨make, hsucc, -⟩
  let A := make (hardPublic p)
  let seed : A.Seed := Classical.choice A.law.nonempty
  obtain ⟨w, hw, hfail⟩ := hard_lower_bound p r B hB A seed
  have h := hsucc (hardInstance p r w) (hardInstance_valid p r w) () (hardOracle p r w)
    (hardOracle_admissible p r w) (seed, fun _ => ())
  rw [hbud w hw] at h
  exact hfail h

lemma goodPoints_hard_card (p r : ℕ) (w : Finset (Fin p)) (hw : w.card = r) :
    (goodPoints (hardInstance p r w)).card ≤
      ((Finset.univ : Finset (Finset (Fin p))).filter fun S => S.card ≤ r).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun z => Finset.univ.filter fun k => z k = 1)
    (fun z hz => ?_) (fun z hz z' hz' heq => ?_)
  · have hz' := Finset.mem_filter.1 (Finset.mem_coe.1 hz)
    have hbox := Fintype.mem_piFinset.1 hz'.1
    have hle := hz'.2 _ (wPoint_feasible p r w)
    rw [hard_objective, toPoint_wPoint, sum_indicator, hw] at hle
    have hsum : lagrangian (hardInstance p r w) (fun j => (z j : ℝ)) =
        ((Finset.univ.filter fun k => z k = 1).card : ℝ) := by
      have hz01 : ∀ k, (z k : ℝ) = indicator (Finset.univ.filter fun k => z k = 1) k := by
        intro k
        have : (0 : ℤ) ≤ z k ∧ z k ≤ 1 := Finset.mem_Icc.1 (hbox k)
        unfold indicator
        by_cases hk : z k = 1
        · simp [hk]
        · have : z k = 0 := by omega
          simp [this]
      simp only [lagrangian, zero_vecMul, add_zero, zero_dotProduct, sub_zero]
      rw [← sum_indicator]
      simp only [dotProduct, one_mul, hz01]
    rw [hsum] at hle
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact_mod_cast hle
  · have hb := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).1
    have hb' := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hz')).1
    funext k
    have h1 : (0 : ℤ) ≤ z k ∧ z k ≤ 1 := Finset.mem_Icc.1 (hb k)
    have h2 : (0 : ℤ) ≤ z' k ∧ z' k ≤ 1 := Finset.mem_Icc.1 (hb' k)
    have := congrArg (fun S : Finset (Fin p) => k ∈ S) heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    omega

end OracleTemplate.HiddenMixedIntegerLinear
