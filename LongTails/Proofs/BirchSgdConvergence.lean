import LongTails.Setups.BirchSgd
import LongTails.Proofs.RingmasterStochastic
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.RennalaConvergence
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BirchSgd

open OracleTemplate LongTails.Setups.BirchSgd
open OracleTemplate.Rennala (Point Instance)

theorem foldHist_stable {α : Type} (T : Tree) (init : α) (step : ℕ → α → α) (k j : ℕ)
    (hj : j ≤ k) : T.foldHist init step k j = T.fold init step j := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have h' : j ≤ k := Nat.lt_succ_iff.mp h
      change (if j ≤ k then T.foldHist init step k j
        else step k (T.foldHist init step k (T.base k))) = _
      rw [ite_eq_left h', ih h']
    · obtain rfl : j = k + 1 := le_antisymm hj h
      rfl

theorem fold_succ {α : Type} (T : Tree) (init : α) (step : ℕ → α → α) (j : ℕ)
    (hb : T.base j ≤ j) :
    T.fold init step (j + 1) = step j (T.fold init step (T.base j)) := by
  change (if j + 1 ≤ j then T.foldHist init step j (j + 1)
    else step j (T.foldHist init step j (T.base j))) = _
  rw [ite_eq_right (Nat.not_succ_le_self j), foldHist_stable T init step j (T.base j) hb]

theorem repr_succ (T : Tree) (j : ℕ) (hb : T.base j ≤ j) :
    T.repr (j + 1) = T.grad j ::ₘ T.repr (T.base j) := by
  exact fold_succ T 0 (fun k M => T.grad k ::ₘ M) j hb

theorem depth_succ (T : Tree) (j : ℕ) (hb : T.base j ≤ j) :
    T.depth (j + 1) = T.depth (T.base j) + 1 := by
  exact fold_succ T 0 (fun _ n => n + 1) j hb

theorem ancestors_succ (T : Tree) (j : ℕ) (hb : T.base j ≤ j) :
    T.ancestors (j + 1) = insert (j + 1) (T.ancestors (T.base j)) := by
  exact fold_succ T {0} (fun k s => insert (k + 1) s) j hb

theorem zero_mem_ancestors (T : Tree) (hT : T.WellFormed) (y : ℕ) : 0 ∈ T.ancestors y := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rcases y with _ | j
    · exact Finset.mem_singleton_self 0
    · rw [ancestors_succ T j (hT j).1]
      exact Finset.mem_insert_of_mem (ih _ (Nat.lt_succ_of_le (hT j).1))

theorem ancestor_repr (T : Tree) (hT : T.WellFormed) (y : ℕ) :
    ∀ a ∈ T.ancestors y, T.depth a ≤ T.depth y ∧
      ∃ C : Multiset ℕ, T.repr y = T.repr a + C ∧ C.card = T.depth y - T.depth a := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro a ha
    rcases y with _ | j
    · have : a = 0 := Finset.mem_singleton.mp ha
      subst this
      exact ⟨le_rfl, 0, by simp, by simp⟩
    · have hb := (hT j).1
      rw [ancestors_succ T j hb] at ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact ⟨le_rfl, 0, by simp, by simp⟩
      · obtain ⟨hd, C, hC, hcard⟩ := ih (T.base j) (Nat.lt_succ_of_le hb) a ha'
        refine ⟨?_, T.grad j ::ₘ C, ?_, ?_⟩
        · rw [depth_succ T j hb]
          omega
        · rw [repr_succ T j hb, hC, Multiset.add_cons]
        · rw [Multiset.card_cons, hcard, depth_succ T j hb]
          omega

theorem realize_stable {d : ℕ} {Ω : Type} (T : Tree) (hT : T.WellFormed) (gamma : ℝ)
    (x0 : Point d) (g : Point d → Ω → Point d) (η : ℕ → Ω) (k : ℕ) :
    (∀ j ≤ k, (T.realize gamma x0 g η k).nodes j = T.vertex gamma x0 g η j) ∧
      ∀ c < k, (T.realize gamma x0 g η k).replies c = T.reply gamma x0 g η c := by
  induction k with
  | zero =>
    refine ⟨fun j hj => ?_, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rfl
  | succ k ih =>
    have hrk : g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k) =
        T.reply gamma x0 g η k := by
      rw [ih.1 _ (hT k).2.1]
      rfl
    refine ⟨fun j hj => ?_, fun c hc => ?_⟩
    · rcases Nat.lt_or_ge j (k + 1) with h | h
      · have hne : j ≠ k + 1 := Nat.ne_of_lt h
        change (if j = k + 1 then _ else (T.realize gamma x0 g η k).nodes j) = _
        rw [ite_eq_right hne, ih.1 j (Nat.lt_succ_iff.mp h)]
      · obtain rfl : j = k + 1 := le_antisymm hj h
        rfl
    · change (if c = k then g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k)
        else (T.realize gamma x0 g η k).replies c) = _
      by_cases hck : c = k
      · rw [ite_eq_left hck, hrk, hck]
      · rw [ite_eq_right hck, ih.2 c (by omega)]

theorem vertex_zero {d : ℕ} {Ω : Type} (T : Tree) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (η : ℕ → Ω) : T.vertex gamma x0 g η 0 = x0 := by
  exact rfl

theorem vertex_succ {d : ℕ} {Ω : Type} (T : Tree) (hT : T.WellFormed) (gamma : ℝ)
    (x0 : Point d) (g : Point d → Ω → Point d) (η : ℕ → Ω) (j : ℕ) :
    T.vertex gamma x0 g η (j + 1) =
      T.vertex gamma x0 g η (T.base j) - gamma • T.reply gamma x0 g η (T.grad j) := by
  have hs := realize_stable T hT gamma x0 g η j
  have hrk : g ((T.realize gamma x0 g η j).nodes (T.point j)) (η j) =
      T.reply gamma x0 g η j := by
    rw [hs.1 _ (hT j).2.1]
    rfl
  change (if j + 1 = j + 1 then (T.realize gamma x0 g η j).nodes (T.base j) - gamma •
      (if T.grad j = j then g ((T.realize gamma x0 g η j).nodes (T.point j)) (η j)
        else (T.realize gamma x0 g η j).replies (T.grad j))
    else (T.realize gamma x0 g η j).nodes (j + 1)) = _
  rw [ite_eq_left rfl, hs.1 _ (hT j).1]
  by_cases hg : T.grad j = j
  · rw [ite_eq_left hg, hrk, hg]
  · rw [ite_eq_right hg, hs.2 _ (lt_of_le_of_ne (hT j).2.2 hg)]

theorem vertex_eq_repr {d : ℕ} {Ω : Type} (T : Tree) (hT : T.WellFormed) (gamma : ℝ)
    (x0 : Point d) (g : Point d → Ω → Point d) (η : ℕ → Ω) (j : ℕ) :
    T.vertex gamma x0 g η j =
      x0 - gamma • ((T.repr j).map (T.reply gamma x0 g η)).sum := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · change x0 = x0 - gamma • ((0 : Multiset ℕ).map (T.reply gamma x0 g η)).sum
      simp
    · have hb := (hT j).1
      rw [vertex_succ T hT gamma x0 g η j, ih _ (Nat.lt_succ_of_le hb), repr_succ T j hb,
        Multiset.map_cons, Multiset.sum_cons, smul_add]
      module

theorem branch_succ (T : Tree) (m : ℕ → ℕ) (hm : T.IsMainBranch m) (k : ℕ) :
    m (k + 1) = (m (k + 1) - 1) + 1 := by
  exact (Nat.succ_pred_eq_of_pos (hm.2 k).1).symm

theorem branch_repr_succ (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (k : ℕ) : T.repr (m (k + 1)) = T.auxSample m k ::ₘ T.repr (m k) := by
  have h := repr_succ T (m (k + 1) - 1) (hT _).1
  rw [← branch_succ T m hm k, (hm.2 k).2] at h
  exact h

theorem branch_depth (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (k : ℕ) : T.depth (m k) = k := by
  induction k with
  | zero => rw [hm.1]; rfl
  | succ k ih =>
    have h := depth_succ T (m (k + 1) - 1) (hT _).1
    rw [← branch_succ T m hm k, (hm.2 k).2, ih] at h
    exact h

theorem branch_ancestors (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (k : ℕ) : T.ancestors (m k) = (Finset.range (k + 1)).image m := by
  induction k with
  | zero =>
    rw [Finset.range_one, Finset.image_singleton, hm.1]
    rfl
  | succ k ih =>
    have h := ancestors_succ T (m (k + 1) - 1) (hT _).1
    rw [← branch_succ T m hm k, (hm.2 k).2, ih] at h
    rw [h, Finset.range_add_one (n := k + 1), Finset.image_insert]

theorem branch_vertex_succ {d : ℕ} {Ω : Type} (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ)
    (hm : T.IsMainBranch m) (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d)
    (η : ℕ → Ω) (k : ℕ) :
    T.vertex gamma x0 g η (m (k + 1)) = T.vertex gamma x0 g η (m k) -
      gamma • g (T.vertex gamma x0 g η (T.auxNode m k)) (η (T.auxSample m k)) := by
  have h := vertex_succ T hT gamma x0 g η (m (k + 1) - 1)
  rw [← branch_succ T m hm k, (hm.2 k).2] at h
  exact h

theorem branch_repr_Ico (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (p k : ℕ) (hpk : p ≤ k) :
    T.repr (m k) = T.repr (m p) + (Finset.Ico p k).val.map (T.auxSample m) := by
  induction k, hpk using Nat.le_induction with
  | base => simp
  | succ k hpk ih =>
    rw [branch_repr_succ T hT m hm k, ih, Nat.Ico_succ_right_eq_insert_Ico hpk,
      Finset.insert_val_of_notMem (by simp), Multiset.map_cons, Multiset.add_cons]

theorem le_map_exists {α β : Type} (f : α → β) (s : Multiset α) :
    ∀ M : Multiset β, M ≤ s.map f → ∃ t ≤ s, M = t.map f := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    intro M hM
    refine ⟨0, le_rfl, ?_⟩
    simpa using hM
  | cons a s ih =>
    intro M hM
    rw [Multiset.map_cons] at hM
    by_cases ha : f a ∈ M
    · obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem ha
      obtain ⟨t, ht, rfl⟩ := ih M' ((Multiset.cons_le_cons_iff _).mp hM)
      exact ⟨a ::ₘ t, (Multiset.cons_le_cons_iff _).mpr ht, by rw [Multiset.map_cons]⟩
    · obtain ⟨t, ht, rfl⟩ := ih M ((Multiset.le_cons_of_notMem ha).mp hM)
      exact ⟨t, ht.trans (Multiset.le_cons_self s a), rfl⟩

theorem tree_gap {d : ℕ} {Ω : Type} (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ)
    (hm : T.IsMainBranch m) (R : ℝ)
    (h2 : ∀ k, T.repr (T.auxNode m k) ≤ T.repr (m k))
    (h3 : ∀ k, (T.dist (m k) (T.auxNode m k) : ℝ) ≤ R)
    (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d) (k : ℕ) :
    ∃ p ≤ k, ((k : ℝ) - p ≤ R) ∧ ∃ I ⊆ Finset.Ico p k, ∀ η : ℕ → Ω,
      T.vertex gamma x0 g η (T.auxNode m k) = T.vertex gamma x0 g η (m k) +
        gamma • ∑ i ∈ I, g (T.vertex gamma x0 g η (T.auxNode m i)) (η (T.auxSample m i)) := by
  classical
  set z := T.auxNode m k with hz
  set S := T.ancestors (m k) ∩ T.ancestors z with hS
  have hne : S.Nonempty := ⟨0, Finset.mem_inter.mpr
    ⟨zero_mem_ancestors T hT _, zero_mem_ancestors T hT _⟩⟩
  obtain ⟨a, haS, hsup⟩ := Finset.exists_mem_eq_sup S hne T.depth
  have haS' := Finset.mem_inter.mp haS
  have hak := haS'.1
  rw [branch_ancestors T hT m hm k, Finset.mem_image] at hak
  obtain ⟨p, hp, rfl⟩ := hak
  have hpk : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have hdp : T.depth (m p) = p := branch_depth T hT m hm p
  refine ⟨p, hpk, ?_, ?_⟩
  · have hdist : k - p ≤ T.dist (m k) z := by
      change k - p ≤ max (T.depth (m k) - S.sup T.depth) (T.depth z - S.sup T.depth)
      rw [hsup, hdp, branch_depth T hT m hm k]
      exact le_max_left _ _
    have h := h3 k
    rw [← hz] at h
    have hcast : (k : ℝ) - p = ((k - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpk]
    rw [hcast]
    exact le_trans (by exact_mod_cast hdist) h
  · obtain ⟨-, C, hC, -⟩ := ancestor_repr T hT z (m p) haS'.2
    have hB := branch_repr_Ico T hT m hm p k hpk
    set B := (Finset.Ico p k).val.map (T.auxSample m) with hBdef
    have hCB : C ≤ B := by
      have h := h2 k
      rw [← hz, hC, hB] at h
      exact (add_le_add_iff_left _).mp h
    obtain ⟨t, ht, htB⟩ := le_map_exists (T.auxSample m) (Finset.Ico p k).val (B - C)
      (tsub_le_self.trans le_rfl)
    have hnd : t.Nodup := Multiset.nodup_of_le ht (Finset.Ico p k).nodup
    refine ⟨⟨t, hnd⟩, fun i hi => Multiset.mem_of_le ht hi, fun η => ?_⟩
    have hsplit : B = C + (B - C) := (add_tsub_cancel_of_le hCB).symm
    rw [vertex_eq_repr T hT gamma x0 g η z, vertex_eq_repr T hT gamma x0 g η (m k), hC, hB,
      hsplit, htB]
    have hsum : ∑ i ∈ (⟨t, hnd⟩ : Finset ℕ),
        g (T.vertex gamma x0 g η (T.auxNode m i)) (η (T.auxSample m i)) =
        ((t.map (T.auxSample m)).map (T.reply gamma x0 g η)).sum := by
      rw [Finset.sum_mk, Multiset.map_map]
      rfl
    rw [hsum]
    simp only [Multiset.map_add, Multiset.sum_add, smul_add]
    module

theorem indep_comp {Ξ Ω β : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ξ) [IsProbabilityMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ξ → β) (Y : Ξ → Ω) (hW : Measurable W) (hY : Measurable Y)
    (hind : IndepFun W Y P) (hlaw : P.map Y = μ)
    (Φ : β → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hint : ∀ w, Integrable (Φ w) μ)
    (hint2 : Integrable (fun ω => ∫ b, ‖Φ (W ω) b‖ ∂μ) P) :
    Integrable (fun ω => Φ (W ω) (Y ω)) P ∧
      ∫ ω, Φ (W ω) (Y ω) ∂P = ∫ ω, ∫ b, Φ (W ω) b ∂μ ∂P := by
  have hjoint : P.map (fun ω => (W ω, Y ω)) = (P.map W).prod μ := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hY.aemeasurable).mp hind
  have hWY : Measurable (fun ω => (W ω, Y ω)) := hW.prodMk hY
  have hnm : StronglyMeasurable (fun w => ∫ b, ‖Φ w b‖ ∂μ) :=
    hΦ.norm.stronglyMeasurable.integral_prod_right' (f := fun z => ‖Function.uncurry Φ z‖)
  have hm : StronglyMeasurable (fun w => ∫ b, Φ w b ∂μ) :=
    hΦ.stronglyMeasurable.integral_prod_right' (f := Function.uncurry Φ)
  have hprod : Integrable (Function.uncurry Φ) ((P.map W).prod μ) := by
    rw [integrable_prod_iff hΦ.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun w => hint w), ?_⟩
    exact (integrable_map_measure hnm.aestronglyMeasurable hW.aemeasurable).mpr hint2
  have hcomp : Integrable (fun ω => Φ (W ω) (Y ω)) P := by
    have h := (integrable_map_measure (μ := P) (f := fun ω => (W ω, Y ω))
      (g := Function.uncurry Φ) (by rw [hjoint]; exact hΦ.aestronglyMeasurable)
      hWY.aemeasurable).mp (by rw [hjoint]; exact hprod)
    exact h
  refine ⟨hcomp, ?_⟩
  have h1 : ∫ ω, Φ (W ω) (Y ω) ∂P = ∫ z, Function.uncurry Φ z ∂(P.map (fun ω => (W ω, Y ω))) :=
    (integral_map hWY.aemeasurable (by rw [hjoint]; exact hΦ.aestronglyMeasurable)).symm
  rw [h1, hjoint, integral_prod _ hprod]
  exact integral_map hW.aemeasurable hm.aestronglyMeasurable

theorem indep_bound {Ξ Ω β : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ξ) [IsProbabilityMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ξ → β) (Y : Ξ → Ω) (hW : Measurable W) (hY : Measurable Y)
    (hind : IndepFun W Y P) (hlaw : P.map Y = μ)
    (Φ : β → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ)) (hnn : ∀ w b, 0 ≤ Φ w b)
    (hint : ∀ w, Integrable (Φ w) μ) (B : Ξ → ℝ) (hB : Integrable B P)
    (hle : ∀ ω, (∫ b, Φ (W ω) b ∂μ) ≤ B ω) :
    Integrable (fun ω => Φ (W ω) (Y ω)) P ∧ (∫ ω, Φ (W ω) (Y ω) ∂P) ≤ ∫ ω, B ω ∂P := by
  have hm : StronglyMeasurable (fun w => ∫ b, Φ w b ∂μ) :=
    hΦ.stronglyMeasurable.integral_prod_right' (f := Function.uncurry Φ)
  have hnorm (w : β) : (∫ b, ‖Φ w b‖ ∂μ) = ∫ b, Φ w b ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun b => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (hnn w b)])
  have hinner : Integrable (fun ω => ∫ b, Φ (W ω) b ∂μ) P := by
    apply hB.mono' (hm.comp_measurable hW).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      show |∫ b, Φ (W ω) b ∂μ| ≤ B ω
      rw [abs_of_nonneg (integral_nonneg (fun b => hnn _ b))]
      exact hle ω)
  have hint2 : Integrable (fun ω => ∫ b, ‖Φ (W ω) b‖ ∂μ) P := by
    simp only [hnorm]
    exact hinner
  obtain ⟨hI, heq⟩ := indep_comp P μ W Y hW hY hind hlaw Φ hΦ hint hint2
  refine ⟨hI, ?_⟩
  rw [heq]
  exact integral_mono hinner hB hle

theorem realize_measurable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (gamma : ℝ)
    (x0 : Point d) (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    (∀ j, Measurable (fun η : ℕ → Ω => (T.realize gamma x0 g η k).nodes j)) ∧
      ∀ c, Measurable (fun η : ℕ → Ω => (T.realize gamma x0 g η k).replies c) := by
  induction k with
  | zero => exact ⟨fun _ => measurable_const, fun _ => measurable_const⟩
  | succ k ih =>
    have hr : Measurable (fun η : ℕ → Ω =>
        g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k)) :=
      hg.comp ((ih.1 _).prodMk (measurable_pi_apply k))
    refine ⟨fun j => ?_, fun c => ?_⟩
    · change Measurable (fun η : ℕ → Ω => if j = k + 1 then
        (T.realize gamma x0 g η k).nodes (T.base k) - gamma •
          (if T.grad k = k then g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k)
            else (T.realize gamma x0 g η k).replies (T.grad k))
        else (T.realize gamma x0 g η k).nodes j)
      by_cases hj : j = k + 1
      · simp only [ite_eq_left hj]
        by_cases hgk : T.grad k = k
        · simp only [ite_eq_left hgk]
          exact (ih.1 _).sub (hr.const_smul gamma)
        · simp only [ite_eq_right hgk]
          exact (ih.1 _).sub ((ih.2 _).const_smul gamma)
      · simp only [ite_eq_right hj]
        exact ih.1 j
    · change Measurable (fun η : ℕ → Ω => if c = k then
        g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k)
        else (T.realize gamma x0 g η k).replies c)
      by_cases hc : c = k
      · simp only [ite_eq_left hc]
        exact hr
      · simp only [ite_eq_right hc]
        exact ih.2 c

theorem vertex_measurable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (gamma : ℝ)
    (x0 : Point d) (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun η : ℕ → Ω => T.vertex gamma x0 g η j) := by
  exact (realize_measurable T gamma x0 g hg j).1 j

theorem aux_zero {d : ℕ} {Ω : Type} (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ)
    (hm : T.IsMainBranch m) (R : ℝ) (h2 : ReprContained T m) (h3 : DistanceBounded T m R)
    (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d) (η : ℕ → Ω) :
    T.vertex gamma x0 g η (m 0) = x0 ∧ T.vertex gamma x0 g η (T.auxNode m 0) = x0 := by
  have hx : T.vertex gamma x0 g η (m 0) = x0 := by
    rw [hm.1]
    rfl
  refine ⟨hx, ?_⟩
  obtain ⟨p, hp, -, I, hI, hZ⟩ := tree_gap (Ω := Ω) T hT m hm R h2 h3 gamma x0 g 0
  have hp0 : p = 0 := Nat.le_zero.mp hp
  have hIe : I = ∅ := by
    rw [hp0, Finset.Ico_self] at hI
    exact Finset.subset_empty.mp hI
  rw [hZ η, hIe, Finset.sum_empty, smul_zero, add_zero, hx]

theorem past_X {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (hT : T.WellFormed)
    (m : ℕ → ℕ) (hm : T.IsMainBranch m) (R : ℝ) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d)
    (k i : ℕ) (hi : i ≤ k) :
    ∃ F : (Fin k → Point d × Point d × Ω) → Point d, Measurable F ∧ ∀ η : ℕ → Ω,
      T.vertex gamma x0 g η (m i) = F (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val))) := by
  rcases i with _ | i
  · exact ⟨fun _ => x0, measurable_const,
      fun η => (aux_zero T hT m hm R h2 h3 gamma x0 g η).1⟩
  · exact ⟨fun t => (t ⟨i, by omega⟩).1, (measurable_pi_apply _).fst, fun _ => rfl⟩

theorem past_Z {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (hT : T.WellFormed)
    (m : ℕ → ℕ) (hm : T.IsMainBranch m) (R : ℝ) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d)
    (k i : ℕ) (hi : i ≤ k) :
    ∃ F : (Fin k → Point d × Point d × Ω) → Point d, Measurable F ∧ ∀ η : ℕ → Ω,
      T.vertex gamma x0 g η (T.auxNode m i) = F (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val))) := by
  rcases i with _ | i
  · exact ⟨fun _ => x0, measurable_const,
      fun η => (aux_zero T hT m hm R h2 h3 gamma x0 g η).2⟩
  · exact ⟨fun t => (t ⟨i, by omega⟩).2.1, (measurable_pi_apply _).snd.fst, fun _ => rfl⟩

theorem past_sample {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (m : ℕ → ℕ)
    (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d) (k i : ℕ) (hi : i < k) :
    ∃ F : (Fin k → Point d × Point d × Ω) → Ω, Measurable F ∧ ∀ η : ℕ → Ω,
      η (T.auxSample m i) = F (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val))) := by
  exact ⟨fun t => (t ⟨i, hi⟩).2.2, (measurable_pi_apply _).snd.snd, fun _ => rfl⟩

theorem past_measurable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (m : ℕ → ℕ)
    (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g))
    (k : ℕ) :
    Measurable (fun η : ℕ → Ω => fun l : Fin k =>
      (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
        η (T.auxSample m l.val))) := by
  refine Measurable.of_eval (fun l => ?_)
  exact (vertex_measurable T gamma x0 g hg _).prodMk
    ((vertex_measurable T gamma x0 g hg _).prodMk (measurable_pi_apply _))

theorem norm_sum_sq {d : ℕ} (s : Finset ℕ) (F : ℕ → Point d) :
    ‖∑ i ∈ s, F i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖F i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, F i‖ ≤ ∑ i ∈ s, ‖F i‖ := norm_sum_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact h2.trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖F i‖))

theorem norm_add_sq_two {d : ℕ} (x y : Point d) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hn : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem indep_sample {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {β : Type} [MeasurableSpace β]
    (T : Tree) (m : ℕ → ℕ) (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d)
    (P : Measure (ℕ → Ω)) (h1 : SampleIndependent T m gamma x0 g P) (k : ℕ)
    (F : (Fin k → Point d × Point d × Ω) → β) (hF : Measurable F) :
    IndepFun (fun η : ℕ → Ω => F (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val))))
      (fun η : ℕ → Ω => η (T.auxSample m k)) P := by
  exact (h1 k).symm.comp hF measurable_id

theorem moments_step {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ) (L σ R : ℝ)
    (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d) (gamma : ℝ) (x0 : Point d)
    (hsmooth : SmoothObjective f L)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (h1 : SampleIndependent T m gamma x0 g (P : Measure (ℕ → Ω))) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (k : ℕ)
    (hX : Integrable (fun η => ‖T.vertex gamma x0 g η (m k)‖ ^ 2) (P : Measure (ℕ → Ω)))
    (hG : ∀ i < k, Integrable (fun η => ‖g (T.vertex gamma x0 g η (T.auxNode m i))
      (η (T.auxSample m i))‖ ^ 2) (P : Measure (ℕ → Ω))) :
    Integrable (fun η => ‖T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
      Integrable (fun η => ‖g (T.vertex gamma x0 g η (T.auxNode m k))
        (η (T.auxSample m k))‖ ^ 2) (P : Measure (ℕ → Ω)) := by
  have hgm := hg.measurable
  have hsm := OracleTemplate.Rennala.smooth_growth f L hsmooth.1 hsmooth.2
  obtain ⟨p, -, -, I, hI, hZ⟩ := tree_gap (Ω := Ω) T hT m hm R h2 h3 gamma x0 g k
  have hZm := vertex_measurable T gamma x0 g hgm (T.auxNode m k)
  have hZ2 : Integrable (fun η => ‖T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2)
      (P : Measure (ℕ → Ω)) := by
    have hsum : Integrable (fun η => ∑ i ∈ I, ‖g (T.vertex gamma x0 g η (T.auxNode m i))
        (η (T.auxSample m i))‖ ^ 2) (P : Measure (ℕ → Ω)) :=
      integrable_finsetSum _ (fun i hi => hG i (Finset.mem_Ico.mp (hI hi)).2)
    apply ((hX.const_mul 2).add (hsum.const_mul (2 * gamma ^ 2 * I.card))).mono'
      (hZm.norm.pow_const 2).aestronglyMeasurable
    refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hZ η]
    have h1' := norm_add_sq_two (T.vertex gamma x0 g η (m k))
      (gamma • ∑ i ∈ I, g (T.vertex gamma x0 g η (T.auxNode m i)) (η (T.auxSample m i)))
    have h2' := norm_sum_sq I (fun i => g (T.vertex gamma x0 g η (T.auxNode m i))
      (η (T.auxSample m i)))
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1'
    have hg2 : 0 ≤ gamma ^ 2 := sq_nonneg gamma
    have := mul_le_mul_of_nonneg_left h2' hg2
    change _ ≤ 2 * ‖T.vertex gamma x0 g η (m k)‖ ^ 2 + 2 * gamma ^ 2 * (I.card : ℝ) *
      ∑ i ∈ I, ‖g (T.vertex gamma x0 g η (T.auxNode m i)) (η (T.auxSample m i))‖ ^ 2
    nlinarith
  refine ⟨hZ2, ?_⟩
  obtain ⟨F, hF, hFz⟩ := past_Z T hT m hm R h2 h3 gamma x0 g k k le_rfl
  have hPm := past_measurable T m gamma x0 g hgm k
  set W : (ℕ → Ω) → Point d := fun η => F (fun l : Fin k =>
    (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
      η (T.auxSample m l.val))) with hWdef
  have hWm : Measurable W := hF.comp hPm
  have hind := indep_sample T m gamma x0 g (P : Measure (ℕ → Ω)) h1 k F hF
  let Φ : Point d → Ω → ℝ := fun z b => ‖g z b‖ ^ 2
  have hΦ : Measurable (Function.uncurry Φ) := hgm.norm.pow_const 2
  have hB : Integrable (fun η => σ ^ 2 + (2 * ‖gradient f 0‖ ^ 2 +
      2 * L ^ 2 * ‖W η‖ ^ 2)) (P : Measure (ℕ → Ω)) := by
    have hWZ : (fun η => ‖W η‖ ^ 2) = fun η => ‖T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2 :=
      funext (fun η => by rw [hFz η])
    have hW2 : Integrable (fun η => ‖W η‖ ^ 2) (P : Measure (ℕ → Ω)) := by
      rw [hWZ]; exact hZ2
    exact (integrable_const _).add ((integrable_const _).add (hW2.const_mul _))
  have hle : ∀ η, (∫ b, Φ (W η) b ∂(μ : Measure Ω)) ≤ σ ^ 2 + (2 * ‖gradient f 0‖ ^ 2 +
      2 * L ^ 2 * ‖W η‖ ^ 2) := by
    intro η
    have h1' := (OracleTemplate.RingmasterAsgd.oracle_moments f g μ σ hg (W η)).2
    have h2' := hsm.2.2 (W η)
    change (∫ b, ‖g (W η) b‖ ^ 2 ∂(μ : Measure Ω)) ≤ _
    linarith
  obtain ⟨hGi, -⟩ := indep_bound (P : Measure (ℕ → Ω)) (μ : Measure Ω) W
    (fun η : ℕ → Ω => η (T.auxSample m k)) hWm (measurable_pi_apply _) hind
    (hlaw _) Φ hΦ (fun _ _ => sq_nonneg _)
    (fun z => (OracleTemplate.RingmasterAsgd.oracle_moments f g μ σ hg z).1) _ hB hle
  have hfun : (fun η : ℕ → Ω => ‖g (T.vertex gamma x0 g η (T.auxNode m k))
      (η (T.auxSample m k))‖ ^ 2) = fun η => Φ (W η) (η (T.auxSample m k)) :=
    funext (fun η => by rw [hFz η])
  rw [hfun]
  exact hGi

theorem moments {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ) (L σ R : ℝ)
    (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d) (gamma : ℝ) (x0 : Point d)
    (hsmooth : SmoothObjective f L)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (h1 : SampleIndependent T m gamma x0 g (P : Measure (ℕ → Ω))) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (k : ℕ) :
    Integrable (fun η => ‖T.vertex gamma x0 g η (m k)‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
    Integrable (fun η => ‖T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
      Integrable (fun η => ‖g (T.vertex gamma x0 g η (T.auxNode m k))
        (η (T.auxSample m k))‖ ^ 2) (P : Measure (ℕ → Ω)) := by
  have hgm := hg.measurable
  have key : ∀ k, Integrable (fun η => ‖T.vertex gamma x0 g η (m k)‖ ^ 2)
      (P : Measure (ℕ → Ω)) ∧ ∀ i < k, Integrable (fun η => ‖g (T.vertex gamma x0 g η
        (T.auxNode m i)) (η (T.auxSample m i))‖ ^ 2) (P : Measure (ℕ → Ω)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      have hfun : (fun η : ℕ → Ω => ‖T.vertex gamma x0 g η (m 0)‖ ^ 2) = fun _ => ‖x0‖ ^ 2 :=
        funext (fun η => by rw [(aux_zero T hT m hm R h2 h3 gamma x0 g η).1])
      rw [hfun]
      exact integrable_const _
    | succ k ih =>
      have hstep := moments_step f L σ R T hT m hm μ P g gamma x0 hsmooth hg hlaw h1 h2 h3 k
        ih.1 ih.2
      refine ⟨?_, fun i hi => ?_⟩
      · apply ((ih.1.const_mul 2).add (hstep.2.const_mul (2 * gamma ^ 2))).mono'
          ((vertex_measurable T gamma x0 g hgm _).norm.pow_const 2).aestronglyMeasurable
        refine Filter.Eventually.of_forall (fun η => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          branch_vertex_succ T hT m hm gamma x0 g η k, sub_eq_add_neg]
        have h := norm_add_sq_two (T.vertex gamma x0 g η (m k))
          (-(gamma • g (T.vertex gamma x0 g η (T.auxNode m k)) (η (T.auxSample m k))))
        rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
        change _ ≤ 2 * ‖T.vertex gamma x0 g η (m k)‖ ^ 2 + 2 * gamma ^ 2 *
          ‖g (T.vertex gamma x0 g η (T.auxNode m k)) (η (T.auxSample m k))‖ ^ 2
        linarith
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ih.2 i hi'
        · exact hstep.2
  have hk := key k
  have hstep := moments_step f L σ R T hT m hm μ P g gamma x0 hsmooth hg hlaw h1 h2 h3 k
    hk.1 hk.2
  exact ⟨hk.1, hstep.1, hstep.2⟩

theorem indep_integral {Ξ Ω β : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    [MeasurableSpace β] (P : Measure Ξ) [IsProbabilityMeasure P] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ξ → β) (Y : Ξ → Ω) (hW : Measurable W) (hY : Measurable Y)
    (hind : IndepFun W Y P) (hlaw : P.map Y = μ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : β → Ω → E) (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hcomp : Integrable (fun ω => Φ (W ω) (Y ω)) P) :
    Integrable (fun ω => ∫ b, Φ (W ω) b ∂μ) P ∧
      ∫ ω, Φ (W ω) (Y ω) ∂P = ∫ ω, ∫ b, Φ (W ω) b ∂μ ∂P := by
  have hjoint : P.map (fun ω => (W ω, Y ω)) = (P.map W).prod μ := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hY.aemeasurable).mp hind
  have hWY : Measurable (fun ω => (W ω, Y ω)) := hW.prodMk hY
  have hm : StronglyMeasurable (fun w => ∫ b, Φ w b ∂μ) :=
    hΦ.integral_prod_right' (f := Function.uncurry Φ)
  have hprod : Integrable (Function.uncurry Φ) ((P.map W).prod μ) := by
    rw [← hjoint]
    exact (integrable_map_measure (by rw [hjoint]; exact hΦ.aestronglyMeasurable)
      hWY.aemeasurable).mpr hcomp
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable hW.aemeasurable).mp
    hprod.integral_prod_left, ?_⟩
  have h1 : ∫ ω, Φ (W ω) (Y ω) ∂P = ∫ z, Function.uncurry Φ z ∂(P.map (fun ω => (W ω, Y ω))) :=
    (integral_map hWY.aemeasurable (by rw [hjoint]; exact hΦ.aestronglyMeasurable)).symm
  rw [h1, hjoint, integral_prod _ hprod]
  exact integral_map hW.aemeasurable hm.aestronglyMeasurable

theorem descent_point {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (g : Point d → Ω → Point d) (μ : MeasureTheory.ProbabilityMeasure Ω) (L σ gamma : ℝ)
    (hL : 0 < L) (hsmooth : SmoothObjective f L)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hgamma0 : 0 ≤ gamma) (x y : Point d) :
    Integrable (fun b => f (x - gamma • g y b)) (μ : Measure Ω) ∧
      (∫ b, f (x - gamma • g y b) ∂(μ : Measure Ω)) ≤ f x - gamma / 2 * ‖gradient f x‖ ^ 2 -
        gamma / 2 * (1 - L * gamma) * ‖gradient f y‖ ^ 2 + gamma * L ^ 2 / 2 * ‖x - y‖ ^ 2 +
        gamma ^ 2 * L / 2 * σ ^ 2 := by
  have hsm := OracleTemplate.Rennala.smooth_growth f L hsmooth.1 hsmooth.2
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hsmooth.1 x).hasFDerivAt.continuousAt)
  have hgm : Measurable (g y) := hg.measurable.of_uncurry_left
  have hG := hg.integrable y
  obtain ⟨hG2, hG2le⟩ := OracleTemplate.RingmasterAsgd.oracle_moments f g μ σ hg y
  have hzm : Measurable (fun b => x - gamma • g y b) := measurable_const.sub (hgm.const_smul gamma)
  have hup (b : Ω) : f (x - gamma • g y b) ≤ f x - gamma * (inner ℝ (gradient f x) (g y b)) +
      L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2 := by
    have h := hsm.1 x (x - gamma • g y b)
    have he : x - gamma • g y b - x = -(gamma • g y b) := sub_sub_cancel_left _ _
    rw [he, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs] at h
    linarith
  have hupi : Integrable (fun b => f x - gamma * (inner ℝ (gradient f x) (g y b)) +
      L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2) (μ : Measure Ω) :=
    ((integrable_const _).sub ((Integrable.const_inner (gradient f x) hG).const_mul gamma)).add
      (hG2.const_mul _)
  have hint : Integrable (fun b => f (x - gamma • g y b)) (μ : Measure Ω) := by
    have hzn : Integrable (fun b => ‖x - gamma • g y b‖) (μ : Measure Ω) :=
      ((integrable_const x).sub (hG.smul gamma)).norm
    have hz2 : Integrable (fun b => 2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖g y b‖ ^ 2) (μ : Measure Ω) :=
      (integrable_const _).add (hG2.const_mul _)
    apply (((integrable_const |f 0|).add (hzn.const_mul ‖gradient f 0‖)).add
      (hz2.const_mul (L / 2))).mono' (hfc.measurable.comp hzm).aestronglyMeasurable
    refine Filter.Eventually.of_forall (fun b => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hsm.2.1 (x - gamma • g y b)
    have h2 : ‖x - gamma • g y b‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖g y b‖ ^ 2 := by
      have h := norm_add_sq_two x (-(gamma • g y b))
      rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
      rw [sub_eq_add_neg]
      linarith
    have hL2 : 0 ≤ L / 2 := by linarith
    have := mul_le_mul_of_nonneg_left h2 hL2
    change |f (x - gamma • g y b)| ≤ |f 0| + ‖gradient f 0‖ * ‖x - gamma • g y b‖ +
      L / 2 * (2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖g y b‖ ^ 2)
    linarith
  refine ⟨hint, ?_⟩
  have hmono := integral_mono hint hupi hup
  have hI1 : Integrable (fun b => gamma * (inner ℝ (gradient f x) (g y b))) (μ : Measure Ω) :=
    (Integrable.const_inner (gradient f x) hG).const_mul gamma
  have hI2 : Integrable (fun b => f x - gamma * (inner ℝ (gradient f x) (g y b)))
      (μ : Measure Ω) := (integrable_const _).sub hI1
  have hI3 : Integrable (fun b => L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2) (μ : Measure Ω) :=
    hG2.const_mul _
  have hval : (∫ b, (f x - gamma * (inner ℝ (gradient f x) (g y b)) +
      L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2) ∂(μ : Measure Ω)) =
      f x - gamma * (inner ℝ (gradient f x) (gradient f y)) +
        L / 2 * gamma ^ 2 * ∫ b, ‖g y b‖ ^ 2 ∂(μ : Measure Ω) := by
    rw [integral_add hI2 hI3, integral_sub (integrable_const _) hI1, integral_const_mul,
      integral_const_mul, integral_inner hG, hg.unbiased y]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hval] at hmono
  have hip : (inner ℝ (gradient f x) (gradient f y)) = (‖gradient f x‖ ^ 2 +
      ‖gradient f y‖ ^ 2 - ‖gradient f x - gradient f y‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]
    ring
  have hl2 : ‖gradient f x - gradient f y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (hsmooth.2 x y) 2
    rw [mul_pow] at this
    exact this
  have hA := mul_le_mul_of_nonneg_left hl2 hgamma0
  have hC := mul_le_mul_of_nonneg_left hG2le
    (mul_nonneg (by linarith : (0 : ℝ) ≤ L / 2) (sq_nonneg gamma))
  rw [hip] at hmono
  nlinarith

theorem growth_integrable {d : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (f : Point d → ℝ) (L : ℝ)
    (hL : 0 < L) (hsmooth : SmoothObjective f L) (P : Measure Ξ) [IsProbabilityMeasure P]
    (Y : Ξ → Point d) (hY : Measurable Y) (hY2 : Integrable (fun ω => ‖Y ω‖ ^ 2) P) :
    Integrable (fun ω => f (Y ω)) P ∧ Integrable (fun ω => ‖gradient f (Y ω)‖ ^ 2) P := by
  have hsm := OracleTemplate.Rennala.smooth_growth f L hsmooth.1 hsmooth.2
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hsmooth.2 :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hsmooth.1 x).hasFDerivAt.continuousAt)
  have hYn : Integrable (fun ω => ‖Y ω‖) P :=
    (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      ((memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr hY2)).norm
  refine ⟨?_, ?_⟩
  · apply (((integrable_const |f 0|).add (hYn.const_mul ‖gradient f 0‖)).add
      (hY2.const_mul (L / 2))).mono' (hfc.measurable.comp hY).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]
      exact hsm.2.1 _)
  · apply ((integrable_const (2 * ‖gradient f 0‖ ^ 2)).add
      (hY2.const_mul (2 * L ^ 2))).mono'
        ((hgc.measurable.comp hY).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsm.2.2 _)

theorem sub_sq_integrable {d : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (P : Measure Ξ)
    (Y Y' : Ξ → Point d) (hY : Measurable Y) (hY' : Measurable Y')
    (hY2 : Integrable (fun ω => ‖Y ω‖ ^ 2) P) (hY2' : Integrable (fun ω => ‖Y' ω‖ ^ 2) P) :
    Integrable (fun ω => ‖Y ω - Y' ω‖ ^ 2) P := by
  apply ((hY2.const_mul 2).add (hY2'.const_mul 2)).mono'
    ((hY.sub hY').norm.pow_const 2).aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := norm_add_sq_two (Y ω) (-Y' ω)
  rw [norm_neg, ← sub_eq_add_neg] at h
  exact h

theorem past_family {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (hT : T.WellFormed)
    (m : ℕ → ℕ) (hm : T.IsMainBranch m) (R : ℝ) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d)
    (k : ℕ) :
    ∃ FX FZ : ℕ → (Fin k → Point d × Point d × Ω) → Point d,
      (∀ i, Measurable (FX i)) ∧ (∀ i, Measurable (FZ i)) ∧
      (∀ i ≤ k, ∀ η : ℕ → Ω, T.vertex gamma x0 g η (m i) = FX i (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val)))) ∧
      ∀ i ≤ k, ∀ η : ℕ → Ω, T.vertex gamma x0 g η (T.auxNode m i) = FZ i (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val))) := by
  classical
  have hX : ∀ i, ∃ F : (Fin k → Point d × Point d × Ω) → Point d, Measurable F ∧
      (i ≤ k → ∀ η : ℕ → Ω, T.vertex gamma x0 g η (m i) = F (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val)))) := by
    intro i
    by_cases hi : i ≤ k
    · obtain ⟨F, hF, hFe⟩ := past_X T hT m hm R h2 h3 gamma x0 g k i hi
      exact ⟨F, hF, fun _ => hFe⟩
    · exact ⟨fun _ => x0, measurable_const, fun h => absurd h hi⟩
  have hZ : ∀ i, ∃ F : (Fin k → Point d × Point d × Ω) → Point d, Measurable F ∧
      (i ≤ k → ∀ η : ℕ → Ω, T.vertex gamma x0 g η (T.auxNode m i) = F (fun l : Fin k =>
        (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
          η (T.auxSample m l.val)))) := by
    intro i
    by_cases hi : i ≤ k
    · obtain ⟨F, hF, hFe⟩ := past_Z T hT m hm R h2 h3 gamma x0 g k i hi
      exact ⟨F, hF, fun _ => hFe⟩
    · exact ⟨fun _ => x0, measurable_const, fun h => absurd h hi⟩
  choose FX hFX hFXe using hX
  choose FZ hFZ hFZe using hZ
  exact ⟨FX, FZ, hFX, hFZ, fun i hi => hFXe i hi, fun i hi => hFZe i hi⟩

theorem expected_step {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ) (L σ R : ℝ)
    (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d) (gamma : ℝ) (x0 : Point d) (hL : 0 < L)
    (hgamma0 : 0 ≤ gamma) (hsmooth : SmoothObjective f L)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (h1 : SampleIndependent T m gamma x0 g (P : Measure (ℕ → Ω))) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (k : ℕ) :
    (∫ η, f (T.vertex gamma x0 g η (m (k + 1))) ∂(P : Measure (ℕ → Ω))) ≤
      (∫ η, f (T.vertex gamma x0 g η (m k)) ∂(P : Measure (ℕ → Ω))) -
      gamma / 2 * (∫ η, ‖gradient f (T.vertex gamma x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) -
      gamma / 2 * (1 - L * gamma) *
        (∫ η, ‖gradient f (T.vertex gamma x0 g η (T.auxNode m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) +
      gamma * L ^ 2 / 2 * (∫ η, ‖T.vertex gamma x0 g η (m k) -
        T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) +
      gamma ^ 2 * L / 2 * σ ^ 2 := by
  have hgm := hg.measurable
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hsmooth.1 x).hasFDerivAt.continuousAt)
  obtain ⟨FX, FZ, hFX, hFZ, hFXe, hFZe⟩ := past_family T hT m hm R h2 h3 gamma x0 g k
  have hPm := past_measurable T m gamma x0 g hgm k
  set Pk : (ℕ → Ω) → (Fin k → Point d × Point d × Ω) := fun η => fun l : Fin k =>
    (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
      η (T.auxSample m l.val)) with hPkdef
  set W : (ℕ → Ω) → Point d × Point d := fun η => (FX k (Pk η), FZ k (Pk η)) with hWdef
  have hWm : Measurable W := ((hFX k).comp hPm).prodMk ((hFZ k).comp hPm)
  have hind := indep_sample T m gamma x0 g (P : Measure (ℕ → Ω)) h1 k
    (fun t => (FX k t, FZ k t)) ((hFX k).prodMk (hFZ k))
  have hW1 (η : ℕ → Ω) : (W η).1 = T.vertex gamma x0 g η (m k) := (hFXe k le_rfl η).symm
  have hW2 (η : ℕ → Ω) : (W η).2 = T.vertex gamma x0 g η (T.auxNode m k) :=
    (hFZe k le_rfl η).symm
  let Φ : Point d × Point d → Ω → ℝ := fun w b => f (w.1 - gamma • g w.2 b)
  have hΦ : StronglyMeasurable (Function.uncurry Φ) :=
    (hfc.measurable.comp (measurable_fst.fst.sub
      ((hgm.comp (measurable_fst.snd.prodMk measurable_snd)).const_smul gamma))).stronglyMeasurable
  have hΦW (η : ℕ → Ω) : Φ (W η) (η (T.auxSample m k)) =
      f (T.vertex gamma x0 g η (m (k + 1))) := by
    change f ((W η).1 - gamma • g (W η).2 (η (T.auxSample m k))) = _
    rw [hW1, hW2, branch_vertex_succ T hT m hm gamma x0 g η k]
  have hmo := moments f L σ R T hT m hm μ P g gamma x0 hsmooth hg hlaw h1 h2 h3
  have hXm := vertex_measurable T gamma x0 g hgm
  obtain ⟨hfX1, -⟩ := growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _)
    (hmo (k + 1)).1
  obtain ⟨hfX, hgX⟩ := growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _)
    (hmo k).1
  obtain ⟨-, hgZ⟩ := growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _)
    (hmo k).2.1
  have hXZ := sub_sq_integrable (P : Measure (ℕ → Ω)) _ _ (hXm (m k)) (hXm (T.auxNode m k))
    (hmo k).1 (hmo k).2.1
  have hcomp : Integrable (fun η => Φ (W η) (η (T.auxSample m k))) (P : Measure (ℕ → Ω)) := by
    simp only [hΦW]
    exact hfX1
  obtain ⟨hinner, heq⟩ := indep_integral (P : Measure (ℕ → Ω)) (μ : Measure Ω) W
    (fun η => η (T.auxSample m k)) hWm (measurable_pi_apply _) hind (hlaw _) Φ hΦ hcomp
  have hlhs : (∫ η, f (T.vertex gamma x0 g η (m (k + 1))) ∂(P : Measure (ℕ → Ω))) =
      ∫ η, Φ (W η) (η (T.auxSample m k)) ∂(P : Measure (ℕ → Ω)) := by
    simp only [hΦW]
  set RHS : (ℕ → Ω) → ℝ := fun η => f (T.vertex gamma x0 g η (m k)) -
      gamma / 2 * ‖gradient f (T.vertex gamma x0 g η (m k))‖ ^ 2 -
      gamma / 2 * (1 - L * gamma) * ‖gradient f (T.vertex gamma x0 g η (T.auxNode m k))‖ ^ 2 +
      gamma * L ^ 2 / 2 * ‖T.vertex gamma x0 g η (m k) -
        T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2 +
      gamma ^ 2 * L / 2 * σ ^ 2 with hRHS
  have hle : ∀ η, (∫ b, Φ (W η) b ∂(μ : Measure Ω)) ≤ RHS η := by
    intro η
    have h := (descent_point f g μ L σ gamma hL hsmooth hg hgamma0 (W η).1 (W η).2).2
    change (∫ b, f ((W η).1 - gamma • g (W η).2 b) ∂(μ : Measure Ω)) ≤ RHS η
    rw [hW1, hW2] at h ⊢
    exact h
  have iA : Integrable (fun η => f (T.vertex gamma x0 g η (m k))) (P : Measure (ℕ → Ω)) := hfX
  have iB : Integrable (fun η => gamma / 2 * ‖gradient f (T.vertex gamma x0 g η (m k))‖ ^ 2)
      (P : Measure (ℕ → Ω)) := hgX.const_mul _
  have iC : Integrable (fun η => gamma / 2 * (1 - L * gamma) *
      ‖gradient f (T.vertex gamma x0 g η (T.auxNode m k))‖ ^ 2) (P : Measure (ℕ → Ω)) :=
    hgZ.const_mul _
  have iD : Integrable (fun η => gamma * L ^ 2 / 2 * ‖T.vertex gamma x0 g η (m k) -
      T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) := hXZ.const_mul _
  have iAB : Integrable (fun η => f (T.vertex gamma x0 g η (m k)) -
      gamma / 2 * ‖gradient f (T.vertex gamma x0 g η (m k))‖ ^ 2) (P : Measure (ℕ → Ω)) :=
    iA.sub iB
  have iABC : Integrable (fun η => f (T.vertex gamma x0 g η (m k)) -
      gamma / 2 * ‖gradient f (T.vertex gamma x0 g η (m k))‖ ^ 2 -
      gamma / 2 * (1 - L * gamma) * ‖gradient f (T.vertex gamma x0 g η (T.auxNode m k))‖ ^ 2)
      (P : Measure (ℕ → Ω)) := iAB.sub iC
  have iABCD : Integrable (fun η => f (T.vertex gamma x0 g η (m k)) -
      gamma / 2 * ‖gradient f (T.vertex gamma x0 g η (m k))‖ ^ 2 -
      gamma / 2 * (1 - L * gamma) * ‖gradient f (T.vertex gamma x0 g η (T.auxNode m k))‖ ^ 2 +
      gamma * L ^ 2 / 2 * ‖T.vertex gamma x0 g η (m k) -
        T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) := iABC.add iD
  have hRi : Integrable RHS (P : Measure (ℕ → Ω)) := iABCD.add (integrable_const _)
  rw [hlhs, heq]
  refine (integral_mono hinner hRi hle).trans (le_of_eq ?_)
  rw [hRHS, integral_add iABCD (integrable_const _), integral_add iABC iD, integral_sub iAB iC,
    integral_sub iA iB, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]

theorem noise_sum {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ) (L σ R : ℝ)
    (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d) (gamma : ℝ) (x0 : Point d) (hL : 0 < L)
    (hsmooth : SmoothObjective f L)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (h1 : SampleIndependent T m gamma x0 g (P : Measure (ℕ → Ω))) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (s : Finset ℕ) :
    Integrable (fun η => ‖∑ i ∈ s, (g (T.vertex gamma x0 g η (T.auxNode m i))
      (η (T.auxSample m i)) - gradient f (T.vertex gamma x0 g η (T.auxNode m i)))‖ ^ 2)
      (P : Measure (ℕ → Ω)) ∧
    (∫ η, ‖∑ i ∈ s, (g (T.vertex gamma x0 g η (T.auxNode m i))
      (η (T.auxSample m i)) - gradient f (T.vertex gamma x0 g η (T.auxNode m i)))‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) ≤ s.card * σ ^ 2 := by
  classical
  have hgm := hg.measurable
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hsmooth.2 :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hXm := vertex_measurable T gamma x0 g hgm
  have hmo := moments f L σ R T hT m hm μ P g gamma x0 hsmooth hg hlaw h1 h2 h3
  set e : ℕ → (ℕ → Ω) → Point d := fun i η => g (T.vertex gamma x0 g η (T.auxNode m i))
    (η (T.auxSample m i)) - gradient f (T.vertex gamma x0 g η (T.auxNode m i)) with he
  have hem : ∀ i, Measurable (e i) := fun i =>
    (hgm.comp ((hXm _).prodMk (measurable_pi_apply _))).sub (hgc.measurable.comp (hXm _))
  have he2 : ∀ i, Integrable (fun η => ‖e i η‖ ^ 2) (P : Measure (ℕ → Ω)) := by
    intro i
    obtain ⟨-, hgZ⟩ := growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _)
      (hmo i).2.1
    apply (((hmo i).2.2.const_mul 2).add (hgZ.const_mul 2)).mono'
      ((hem i).norm.pow_const 2).aestronglyMeasurable
    refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_add_sq_two (g (T.vertex gamma x0 g η (T.auxNode m i)) (η (T.auxSample m i)))
      (-gradient f (T.vertex gamma x0 g η (T.auxNode m i)))
    rw [norm_neg, ← sub_eq_add_neg] at h
    exact h
  induction s using Finset.induction_on_max with
  | empty =>
    simp only [Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, integral_zero, Finset.card_empty, Nat.cast_zero, zero_mul, le_refl, and_true]
    exact integrable_zero _ _ _
  | insert j s hlt ih =>
    have hj : j ∉ s := fun h => lt_irrefl j (hlt j h)
    obtain ⟨FX, FZ, -, hFZ, -, hFZe⟩ := past_family T hT m hm R h2 h3 gamma x0 g j
    have hPm := past_measurable T m gamma x0 g hgm j
    set Pk : (ℕ → Ω) → (Fin j → Point d × Point d × Ω) := fun η => fun l : Fin j =>
      (T.vertex gamma x0 g η (m (l.val + 1)), T.vertex gamma x0 g η (T.auxNode m (l.val + 1)),
        η (T.auxSample m l.val)) with hPkdef
    let G : (Fin j → Point d × Point d × Ω) → Point d := fun t =>
      ∑ i ∈ s.attach, (g (FZ i.1 t) (t ⟨i.1, hlt i.1 i.2⟩).2.2 - gradient f (FZ i.1 t))
    have hGm : Measurable G := by
      refine Finset.measurable_sum _ (fun i _ => ?_)
      exact (hgm.comp ((hFZ i.1).prodMk (measurable_pi_apply _).snd.snd)).sub
        (hgc.measurable.comp (hFZ i.1))
    have hGe : ∀ η, ∑ i ∈ s, e i η = G (Pk η) := by
      intro η
      change _ = ∑ i ∈ s.attach, (g (FZ i.1 (Pk η)) (Pk η ⟨i.1, hlt i.1 i.2⟩).2.2 -
        gradient f (FZ i.1 (Pk η)))
      rw [← Finset.sum_attach s (fun i => e i η)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change g (T.vertex gamma x0 g η (T.auxNode m i.1)) (η (T.auxSample m i.1)) -
        gradient f (T.vertex gamma x0 g η (T.auxNode m i.1)) = _
      rw [hFZe i.1 (hlt i.1 i.2).le η]
    set W : (ℕ → Ω) → Point d × Point d := fun η => (G (Pk η), FZ j (Pk η)) with hWdef
    have hWm : Measurable W := (hGm.comp hPm).prodMk ((hFZ j).comp hPm)
    have hind := indep_sample T m gamma x0 g (P : Measure (ℕ → Ω)) h1 j
      (fun t => (G t, FZ j t)) (hGm.prodMk (hFZ j))
    have hZj (η : ℕ → Ω) : FZ j (Pk η) = T.vertex gamma x0 g η (T.auxNode m j) :=
      (hFZe j le_rfl η).symm
    let Φ : Point d × Point d → Ω → ℝ := fun w b => inner ℝ w.1 (g w.2 b - gradient f w.2)
    have hΦ : StronglyMeasurable (Function.uncurry Φ) :=
      (measurable_fst.fst.inner ((hgm.comp (measurable_fst.snd.prodMk measurable_snd)).sub
        (hgc.measurable.comp measurable_fst.snd))).stronglyMeasurable
    have hΦW (η : ℕ → Ω) : Φ (W η) (η (T.auxSample m j)) =
        inner ℝ (∑ i ∈ s, e i η) (e j η) := by
      change inner ℝ (G (Pk η)) (g (FZ j (Pk η)) (η (T.auxSample m j)) -
        gradient f (FZ j (Pk η))) = _
      rw [hZj, ← hGe]
    have hSm : Measurable (fun η => ∑ i ∈ s, e i η) := Finset.measurable_sum _ (fun i _ => hem i)
    have hcross : Integrable (fun η => inner ℝ (∑ i ∈ s, e i η) (e j η)) (P : Measure (ℕ → Ω)) := by
      apply ((ih.1.add (he2 j)).const_mul (1 / 2)).mono' (hSm.inner (hem j)).aestronglyMeasurable
      refine Filter.Eventually.of_forall (fun η => ?_)
      rw [Real.norm_eq_abs]
      have h1' := abs_real_inner_le_norm (∑ i ∈ s, e i η) (e j η)
      have h2' := sq_nonneg (‖∑ i ∈ s, e i η‖ - ‖e j η‖)
      change _ ≤ 1 / 2 * (‖∑ i ∈ s, e i η‖ ^ 2 + ‖e j η‖ ^ 2)
      nlinarith
    have hcomp : Integrable (fun η => Φ (W η) (η (T.auxSample m j))) (P : Measure (ℕ → Ω)) := by
      simp only [hΦW]
      exact hcross
    obtain ⟨-, heq⟩ := indep_integral (P : Measure (ℕ → Ω)) (μ : Measure Ω) W
      (fun η => η (T.auxSample m j)) hWm (measurable_pi_apply _) hind (hlaw _) Φ hΦ hcomp
    have hzero : ∀ η, (∫ b, Φ (W η) b ∂(μ : Measure Ω)) = 0 := by
      intro η
      change (∫ b, inner ℝ (W η).1 (g (W η).2 b - gradient f (W η).2) ∂(μ : Measure Ω)) = 0
      have hI : Integrable (fun b => g (W η).2 b - gradient f (W η).2) (μ : Measure Ω) :=
        (hg.integrable _).sub (integrable_const _)
      rw [integral_inner hI, integral_sub (hg.integrable _) (integrable_const _), hg.unbiased,
        integral_const]
      simp
    have hcross0 : (∫ η, inner ℝ (∑ i ∈ s, e i η) (e j η) ∂(P : Measure (ℕ → Ω))) = 0 := by
      have h := heq
      simp only [hΦW, hzero, integral_zero] at h
      exact h
    have hvar : (∫ η, ‖e j η‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ σ ^ 2 := by
      let Ψ : Point d → Ω → ℝ := fun z b => ‖g z b - gradient f z‖ ^ 2
      have hΨ : Measurable (Function.uncurry Ψ) :=
        ((hgm.sub (hgc.measurable.comp measurable_fst)).norm.pow_const 2)
      obtain ⟨-, hb⟩ := indep_bound (P : Measure (ℕ → Ω)) (μ : Measure Ω)
        (fun η => FZ j (Pk η)) (fun η => η (T.auxSample m j)) ((hFZ j).comp hPm)
        (measurable_pi_apply _)
        (indep_sample T m gamma x0 g (P : Measure (ℕ → Ω)) h1 j (FZ j) (hFZ j)) (hlaw _) Ψ hΨ
        (fun _ _ => sq_nonneg _) (fun z => hg.variance_integrable z) (fun _ => σ ^ 2)
        (integrable_const _) (fun η => hg.variance _)
      have hfun : (fun η => Ψ (FZ j (Pk η)) (η (T.auxSample m j))) = fun η => ‖e j η‖ ^ 2 :=
        funext (fun η => by
          change ‖g (FZ j (Pk η)) (η (T.auxSample m j)) - gradient f (FZ j (Pk η))‖ ^ 2 = _
          rw [hZj])
      rw [hfun] at hb
      simpa using hb
    have hsum : ∀ η, ‖∑ i ∈ insert j s, e i η‖ ^ 2 = ‖e j η‖ ^ 2 +
        2 * inner ℝ (∑ i ∈ s, e i η) (e j η) + ‖∑ i ∈ s, e i η‖ ^ 2 := by
      intro η
      rw [Finset.sum_insert hj, norm_add_sq_real, real_inner_comm]
    have i1 : Integrable (fun η => ‖e j η‖ ^ 2 + 2 * inner ℝ (∑ i ∈ s, e i η) (e j η))
        (P : Measure (ℕ → Ω)) := (he2 j).add (hcross.const_mul 2)
    have i2 : Integrable (fun η => ‖e j η‖ ^ 2 + 2 * inner ℝ (∑ i ∈ s, e i η) (e j η) +
        ‖∑ i ∈ s, e i η‖ ^ 2) (P : Measure (ℕ → Ω)) := i1.add ih.1
    have hfun : (fun η => ‖∑ i ∈ insert j s, e i η‖ ^ 2) = fun η => ‖e j η‖ ^ 2 +
        2 * inner ℝ (∑ i ∈ s, e i η) (e j η) + ‖∑ i ∈ s, e i η‖ ^ 2 := funext hsum
    change Integrable (fun η => ‖∑ i ∈ insert j s, e i η‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
      (∫ η, ‖∑ i ∈ insert j s, e i η‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ _
    rw [hfun]
    refine ⟨i2, ?_⟩
    rw [integral_add i1 ih.1, integral_add (he2 j) (hcross.const_mul 2), integral_const_mul,
      hcross0, Finset.card_insert_of_notMem hj]
    have := ih.2
    push_cast
    nlinarith

theorem delay_bound {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ) (L σ R : ℝ)
    (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d) (gamma : ℝ) (x0 : Point d) (hL : 0 < L)
    (hsmooth : SmoothObjective f L)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (h1 : SampleIndependent T m gamma x0 g (P : Measure (ℕ → Ω))) (h2 : ReprContained T m)
    (h3 : DistanceBounded T m R) (k : ℕ) :
    ∃ p ≤ k, ((k : ℝ) - p ≤ R) ∧ ∃ I ⊆ Finset.Ico p k,
      (∫ η, ‖T.vertex gamma x0 g η (m k) - T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2
        ∂(P : Measure (ℕ → Ω))) ≤ 2 * gamma ^ 2 * I.card * ((∑ i ∈ I,
          ∫ η, ‖gradient f (T.vertex gamma x0 g η (T.auxNode m i))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) +
          σ ^ 2) := by
  have hgm := hg.measurable
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hsmooth.2 :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hXm := vertex_measurable T gamma x0 g hgm
  have hmo := moments f L σ R T hT m hm μ P g gamma x0 hsmooth hg hlaw h1 h2 h3
  obtain ⟨p, hp, hpR, I, hI, hZ⟩ := tree_gap (Ω := Ω) T hT m hm R h2 h3 gamma x0 g k
  refine ⟨p, hp, hpR, I, hI, ?_⟩
  set v : ℕ → (ℕ → Ω) → Point d := fun i η => gradient f (T.vertex gamma x0 g η (T.auxNode m i))
    with hv
  set e : ℕ → (ℕ → Ω) → Point d := fun i η => g (T.vertex gamma x0 g η (T.auxNode m i))
    (η (T.auxSample m i)) - gradient f (T.vertex gamma x0 g η (T.auxNode m i)) with he
  have hv2 : ∀ i, Integrable (fun η => ‖v i η‖ ^ 2) (P : Measure (ℕ → Ω)) := fun i =>
    (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo i).2.1).2
  obtain ⟨hn2, hnle⟩ := noise_sum f L σ R T hT m hm μ P g gamma x0 hL hsmooth hg hlaw h1 h2 h3 I
  have hpt : ∀ η, ‖T.vertex gamma x0 g η (m k) - T.vertex gamma x0 g η (T.auxNode m k)‖ ^ 2 ≤
      2 * gamma ^ 2 * I.card * ∑ i ∈ I, ‖v i η‖ ^ 2 +
        2 * gamma ^ 2 * ‖∑ i ∈ I, e i η‖ ^ 2 := by
    intro η
    have hdiff : T.vertex gamma x0 g η (m k) - T.vertex gamma x0 g η (T.auxNode m k) =
        -(gamma • ((∑ i ∈ I, v i η) + ∑ i ∈ I, e i η)) := by
      rw [hZ η, ← Finset.sum_add_distrib]
      have : ∀ i, v i η + e i η =
          g (T.vertex gamma x0 g η (T.auxNode m i)) (η (T.auxSample m i)) := by
        intro i
        change gradient f _ + (g _ _ - gradient f _) = _
        module
      simp only [this]
      module
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1' := norm_add_sq_two (∑ i ∈ I, v i η) (∑ i ∈ I, e i η)
    have h2' := norm_sum_sq I (fun i => v i η)
    have hg2 : 0 ≤ gamma ^ 2 := sq_nonneg gamma
    nlinarith [mul_le_mul_of_nonneg_left h1' hg2, mul_le_mul_of_nonneg_left h2' hg2]
  have iV : Integrable (fun η => 2 * gamma ^ 2 * I.card * ∑ i ∈ I, ‖v i η‖ ^ 2)
      (P : Measure (ℕ → Ω)) := (integrable_finsetSum _ (fun i _ => hv2 i)).const_mul _
  have iE : Integrable (fun η => 2 * gamma ^ 2 * ‖∑ i ∈ I, e i η‖ ^ 2) (P : Measure (ℕ → Ω)) :=
    hn2.const_mul _
  have hXZ := sub_sq_integrable (P : Measure (ℕ → Ω)) _ _ (hXm (m k)) (hXm (T.auxNode m k))
    (hmo k).1 (hmo k).2.1
  have iVE : Integrable (fun η => 2 * gamma ^ 2 * I.card * ∑ i ∈ I, ‖v i η‖ ^ 2 +
      2 * gamma ^ 2 * ‖∑ i ∈ I, e i η‖ ^ 2) (P : Measure (ℕ → Ω)) := iV.add iE
  refine (integral_mono hXZ iVE hpt).trans ?_
  rw [integral_add iV iE, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hv2 i)]
  have hc : (0 : ℝ) ≤ 2 * gamma ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hnle hc
  change 2 * gamma ^ 2 * I.card * ∑ i ∈ I, ∫ η, ‖v i η‖ ^ 2 ∂(P : Measure (ℕ → Ω)) +
      2 * gamma ^ 2 * ∫ η, ‖∑ i ∈ I, e i η‖ ^ 2 ∂(P : Measure (ℕ → Ω)) ≤ _
  nlinarith

theorem stepSize_facts (L σ ε R : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hR : 0 ≤ R) :
    0 < stepSize L σ ε R ∧ L * stepSize L σ ε R ≤ 1 / 2 ∧
      L * stepSize L σ ε R * R ≤ 1 / 2 ∧ L * stepSize L σ ε R * σ ^ 2 ≤ ε / 4 ∧
      (L * stepSize L σ ε R = 1 / 2 ∨ L * stepSize L σ ε R * R = 1 / 2 ∨
        L * stepSize L σ ε R * σ ^ 2 = ε / 4) := by
  set a : ℝ := 1 / (2 * L) with ha
  set bR : ℝ := if R = 0 then 1 / (2 * L) else 1 / (2 * R * L) with hbR
  set bS : ℝ := if σ = 0 then 1 / (2 * L) else ε / (4 * σ ^ 2 * L) with hbS
  have hγ : stepSize L σ ε R = min a (min bR bS) := rfl
  have ha0 : 0 < a := by positivity
  have hLa : L * a = 1 / 2 := by rw [ha]; field_simp
  have hbR0 : 0 < bR := by
    rw [hbR]; split_ifs with h
    · positivity
    · have : 0 < R := lt_of_le_of_ne hR (Ne.symm h)
      positivity
  have hbS0 : 0 < bS := by
    rw [hbS]; split_ifs with h
    · positivity
    · have : 0 < σ := lt_of_le_of_ne hσ (Ne.symm h)
      positivity
  have hγ0 : 0 < stepSize L σ ε R := by
    rw [hγ]; exact lt_min ha0 (lt_min hbR0 hbS0)
  have hγa : stepSize L σ ε R ≤ a := by rw [hγ]; exact min_le_left _ _
  have hγR : stepSize L σ ε R ≤ bR := by
    rw [hγ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hγS : stepSize L σ ε R ≤ bS := by
    rw [hγ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have h1 : L * stepSize L σ ε R ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hγa hL.le
    linarith
  have h2 : L * stepSize L σ ε R * R ≤ 1 / 2 := by
    by_cases hR0 : R = 0
    · rw [hR0, mul_zero]; norm_num
    · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      have hb : bR = 1 / (2 * R * L) := by rw [hbR, ite_eq_right hR0]
      have := mul_le_mul_of_nonneg_left hγR (by positivity : (0 : ℝ) ≤ L * R)
      rw [hb] at this
      have he : L * R * (1 / (2 * R * L)) = 1 / 2 := by field_simp
      nlinarith
  have h3 : L * stepSize L σ ε R * σ ^ 2 ≤ ε / 4 := by
    by_cases hσ0 : σ = 0
    · rw [hσ0]; norm_num; linarith
    · have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
      have hb : bS = ε / (4 * σ ^ 2 * L) := by rw [hbS, ite_eq_right hσ0]
      have := mul_le_mul_of_nonneg_left hγS (by positivity : (0 : ℝ) ≤ L * σ ^ 2)
      rw [hb] at this
      have he : L * σ ^ 2 * (ε / (4 * σ ^ 2 * L)) = ε / 4 := by field_simp
      nlinarith
  refine ⟨hγ0, h1, h2, h3, ?_⟩
  rcases min_choice a (min bR bS) with hm | hm
  · left; rw [hγ, hm, hLa]
  · rcases min_choice bR bS with hm' | hm'
    · by_cases hR0 : R = 0
      · left; rw [hγ, hm, hm', hbR, ite_eq_left hR0, ← ha, hLa]
      · right; left
        rw [hγ, hm, hm', hbR, ite_eq_right hR0]
        field_simp
    · by_cases hσ0 : σ = 0
      · left; rw [hγ, hm, hm', hbS, ite_eq_left hσ0, ← ha, hLa]
      · right; right
        rw [hγ, hm, hm', hbS, ite_eq_right hσ0]
        field_simp

theorem window_sum (K : ℕ) (R : ℝ) (hR : 0 ≤ R) (p : ℕ → ℕ) (I : ℕ → Finset ℕ)
    (hI : ∀ k, I k ⊆ Finset.Ico (p k) k) (hp : ∀ k : ℕ, (k : ℝ) - (p k : ℝ) ≤ R)
    (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ∑ k ∈ Finset.range K, ∑ i ∈ I k, b i ≤ R * ∑ i ∈ Finset.range K, b i := by
  classical
  have h1 : ∀ k ∈ Finset.range K, ∑ i ∈ I k, b i =
      ∑ i ∈ Finset.range K, if i ∈ I k then b i else 0 := by
    intro k hk
    rw [Finset.sum_ite_mem]
    congr 1
    ext i
    constructor
    · intro hi
      have := Finset.mem_Ico.mp (hI k hi)
      exact Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hk; omega), hi⟩
    · intro hi
      exact (Finset.mem_inter.mp hi).2
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hb i)
  have hsub : (Finset.range K).filter (fun k => i ∈ I k) ⊆ Finset.Ioc i (i + ⌊R⌋₊) := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have hik := Finset.mem_Ico.mp (hI k hk')
    refine Finset.mem_Ioc.mpr ⟨hik.2, ?_⟩
    have hpk := hp k
    have hkR : ((k - i : ℕ) : ℝ) ≤ R := by
      rw [Nat.cast_sub hik.2.le]
      have : (p k : ℝ) ≤ i := by exact_mod_cast hik.1
      linarith
    have := Nat.le_floor hkR
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hR' : ((i + ⌊R⌋₊ - i : ℕ) : ℝ) ≤ R := by
    rw [Nat.add_sub_cancel_left]
    exact Nat.floor_le hR
  exact (by exact_mod_cast hcard : (((Finset.range K).filter (fun k => i ∈ I k)).card : ℝ) ≤
    ((i + ⌊R⌋₊ - i : ℕ) : ℝ)).trans hR'

theorem poly_case (l r q : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) (hcase : l = 1 / 2 ∨ r = 1 / 2 ∨ q = 1 / 4) :
    (1 + r) * (1 + 2 * r) + (2 * r + 2 * l + 4 * q) * ((1 + r) * (1 + 2 * r) * q * (1 + 2 * r) +
      2 * (1 - l - 2 * r ^ 2) * q * (1 + r)) ≤
      (2 * r + 2 * l + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) := by
  rcases hcase with rfl | rfl | rfl
  · nlinarith [mul_nonneg hr0 hq0, mul_nonneg (mul_nonneg hr0 hr0) hq0,
      mul_nonneg (mul_nonneg hr0 hr0) (mul_nonneg hr0 hq0),
      mul_nonneg hq0 (by linarith : (0:ℝ) ≤ 1/4 - q),
      mul_nonneg hr0 (by linarith : (0:ℝ) ≤ 1/2 - r),
      mul_nonneg (mul_nonneg hr0 hq0) (by linarith : (0:ℝ) ≤ 1/2 - r),
      mul_nonneg (mul_nonneg hr0 hr0) (by linarith : (0:ℝ) ≤ 1/2 - r)]
  · nlinarith [mul_nonneg hl0 hq0, mul_nonneg hq0 (by linarith : (0:ℝ) ≤ 1/4 - q),
      mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1/2 - l),
      mul_nonneg (mul_nonneg hl0 hq0) (by linarith : (0:ℝ) ≤ 1/2 - l),
      mul_nonneg (mul_nonneg hl0 hq0) (by linarith : (0:ℝ) ≤ 1/4 - q)]
  · nlinarith [mul_nonneg hl0 hr0, mul_nonneg (mul_nonneg hr0 hr0) hl0,
      mul_nonneg (mul_nonneg hr0 hr0) hr0, mul_nonneg hr0 (by linarith : (0:ℝ) ≤ 1/2 - r),
      mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1/2 - l),
      mul_nonneg (mul_nonneg hr0 hr0) (by linarith : (0:ℝ) ≤ 1/2 - r),
      mul_nonneg (mul_nonneg hl0 hr0) (by linarith : (0:ℝ) ≤ 1/2 - r),
      mul_nonneg (mul_nonneg hr0 hr0) (mul_nonneg hr0 hr0)]

theorem final_combination (A B Y Kε l r q : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2) (hr0 : 0 ≤ r)
    (hr : r ≤ 1 / 2) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (hcase : l = 1 / 2 ∨ r = 1 / 2 ∨ q = 1 / 4) (hK : 0 ≤ Kε)
    (hA : A + (1 - l - 2 * r ^ 2) * B ≤ Y + Kε * q * (1 + 2 * r))
    (hA3 : A ≤ (1 + r) * (1 + 2 * r) * B + 2 * (1 + r) * Kε * q)
    (hY : Y * (2 * r + 2 * l + 4 * q) ≤ Kε) : A ≤ Kε := by
  have hP0 : 0 < (1 + r) * (1 + 2 * r) := by positivity
  have hβ0 : 0 ≤ 1 - l - 2 * r ^ 2 := by nlinarith
  have hs1 : 1 ≤ 2 * r + 2 * l + 4 * q := by
    rcases hcase with h | h | h <;> rw [h] <;> linarith
  have hH := poly_case l r q hl0 hl hr0 hr hq0 hq hcase
  have h1 : ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) * A ≤
      (1 + r) * (1 + 2 * r) * Y + Kε * ((1 + r) * (1 + 2 * r) * q * (1 + 2 * r) +
        2 * (1 - l - 2 * r ^ 2) * q * (1 + r)) := by
    have e1 := mul_le_mul_of_nonneg_left hA hP0.le
    have e2 := mul_le_mul_of_nonneg_left hA3 hβ0
    linarith
  have h2 := mul_le_mul_of_nonneg_left hY hP0.le
  have e1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * r + 2 * l + 4 * q)
  have e2 := mul_le_mul_of_nonneg_left hH hK
  have hpos : 0 < (2 * r + 2 * l + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) := by
    positivity
  have h3 : (2 * r + 2 * l + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) * A ≤
      (2 * r + 2 * l + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) * Kε := by
    linarith
  exact le_of_mul_le_mul_left h3 hpos

theorem young_split {d : ℕ} (ρ L : ℝ) (hρ : 0 ≤ ρ) (u v x y : Point d)
    (hlip : ‖u - v‖ ≤ L * ‖x - y‖) :
    ρ * ‖u‖ ^ 2 ≤ ρ * (1 + ρ) * ‖v‖ ^ 2 + (1 + ρ) * L ^ 2 * ‖x - y‖ ^ 2 := by
  have hn : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
  have hw2 : ‖u - v‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hlip 2
    rwa [mul_pow] at this
  have hu2 : ‖u‖ ^ 2 ≤ (‖v‖ + ‖u - v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hy := sq_nonneg (ρ * ‖v‖ - ‖u - v‖)
  have h1 := mul_le_mul_of_nonneg_left hu2 hρ
  have h2 := mul_le_mul_of_nonneg_left hw2 (by linarith : (0 : ℝ) ≤ 1 + ρ)
  nlinarith

theorem assembly (K : ℕ) (L σ ε R γ Δ : ℝ) (hL : 0 < L) (hε : 0 < ε) (hR : 0 ≤ R)
    (hγ0 : 0 < γ) (hlam1 : L * γ ≤ 1 / 2) (hrho1 : L * γ * R ≤ 1 / 2)
    (hq : L * γ * σ ^ 2 ≤ ε / 4)
    (hcase : L * γ = 1 / 2 ∨ L * γ * R = 1 / 2 ∨ L * γ * σ ^ 2 = ε / 4)
    (a b D F : ℕ → ℝ) (p : ℕ → ℕ) (I : ℕ → Finset ℕ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hstep : ∀ k, F (k + 1) ≤ F k - γ / 2 * a k - γ / 2 * (1 - L * γ) * b k +
      γ * L ^ 2 / 2 * D k + γ ^ 2 * L / 2 * σ ^ 2)
    (hFK : F 0 - F K ≤ Δ)
    (hI : ∀ k, I k ⊆ Finset.Ico (p k) k) (hpk : ∀ k, p k ≤ k)
    (hpR : ∀ k : ℕ, (k : ℝ) - (p k : ℝ) ≤ R)
    (hDk : ∀ k, D k ≤ 2 * γ ^ 2 * (I k).card * ((∑ i ∈ I k, b i) + σ ^ 2))
    (hyoung : ∀ k, L * γ * R * a k ≤ L * γ * R * (1 + L * γ * R) * b k +
      (1 + L * γ * R) * L ^ 2 * D k)
    (hzero : R = 0 → ∀ k, a k = b k)
    (hK : 4 * (R + 1) * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2 ≤ K) :
    ∑ k ∈ Finset.range K, a k ≤ K * ε := by
  have hcard : ∀ k, ((I k).card : ℝ) ≤ R := by
    intro k
    have h := Finset.card_le_card (hI k)
    rw [Nat.card_Ico] at h
    have h' : ((I k).card : ℝ) ≤ ((k - p k : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (hpk k)] at h'
    linarith [hpR k]
  have hDk' : ∀ k, D k ≤ 2 * γ ^ 2 * R * ((∑ i ∈ I k, b i) + σ ^ 2) := by
    intro k
    refine (hDk k).trans ?_
    have hnn : 0 ≤ (∑ i ∈ I k, b i) + σ ^ 2 :=
      add_nonneg (Finset.sum_nonneg (fun i _ => hb0 i)) (sq_nonneg σ)
    have h1 := mul_le_mul_of_nonneg_right (hcard k) hnn
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2)
    linarith
  have hwin := window_sum K R hR p I hI hpR b hb0
  set A := ∑ k ∈ Finset.range K, a k with hAdef
  set B := ∑ k ∈ Finset.range K, b k with hBdef
  set Ds := ∑ k ∈ Finset.range K, D k with hDsdef
  have hE1 : γ / 2 * A + γ / 2 * (1 - L * γ) * B ≤ Δ + γ * L ^ 2 / 2 * Ds +
      K * (γ ^ 2 * L / 2 * σ ^ 2) := by
    have hs : ∀ k ∈ Finset.range K, F (k + 1) - F k ≤ -(γ / 2) * a k +
        (-(γ / 2 * (1 - L * γ))) * b k + γ * L ^ 2 / 2 * D k + γ ^ 2 * L / 2 * σ ^ 2 :=
      fun k _ => by linarith [hstep k]
    have hsum := Finset.sum_le_sum hs
    rw [Finset.sum_range_sub] at hsum
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum
    linarith
  have hE2 : Ds ≤ 2 * γ ^ 2 * R * (R * B + K * σ ^ 2) := by
    have hs : ∀ k ∈ Finset.range K, D k ≤ 2 * γ ^ 2 * R * ((∑ i ∈ I k, b i) + σ ^ 2) :=
      fun k _ => hDk' k
    have hsum := Finset.sum_le_sum hs
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum
    have h2 := mul_le_mul_of_nonneg_left hwin (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2 * R)
    nlinarith
  have hq0 : 0 ≤ L * γ * σ ^ 2 / ε := by positivity
  have hq' : L * γ * σ ^ 2 / ε ≤ 1 / 4 := by rw [div_le_iff₀ hε]; linarith
  have hqε : K * ε * (L * γ * σ ^ 2 / ε) = K * (L * γ * σ ^ 2) := by field_simp
  have hcase' : L * γ = 1 / 2 ∨ L * γ * R = 1 / 2 ∨ L * γ * σ ^ 2 / ε = 1 / 4 := by
    rcases hcase with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; rw [h]; field_simp
  have hE3 : A ≤ (1 + L * γ * R) * (1 + 2 * (L * γ * R)) * B +
      2 * (1 + L * γ * R) * (K * ε) * (L * γ * σ ^ 2 / ε) := by
    rw [mul_assoc (2 * (1 + L * γ * R)) (K * ε), hqε]
    by_cases hR0 : R = 0
    · have hAB : A = B := Finset.sum_congr rfl (fun k _ => hzero hR0 k)
      rw [hR0, hAB]
      have : 0 ≤ (K : ℝ) * (L * γ * σ ^ 2) := by positivity
      nlinarith
    · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      have hρp : 0 < L * γ * R := by positivity
      have hs : ∀ k ∈ Finset.range K, L * γ * R * a k ≤
          L * γ * R * (1 + L * γ * R) * b k + (1 + L * γ * R) * L ^ 2 * D k :=
        fun k _ => hyoung k
      have hsum := Finset.sum_le_sum hs
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        at hsum
      have hE2' := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ (1 + L * γ * R) * L ^ 2)
      have hkey : L * γ * R * A ≤ L * γ * R * ((1 + L * γ * R) * (1 + 2 * (L * γ * R)) * B +
          2 * (1 + L * γ * R) * (K * (L * γ * σ ^ 2))) := by
        have e1 : (1 + L * γ * R) * L ^ 2 * (2 * γ ^ 2 * R * (R * B + K * σ ^ 2)) =
            L * γ * R * (2 * (1 + L * γ * R) * (L * γ * R) * B +
              2 * (1 + L * γ * R) * (K * (L * γ * σ ^ 2))) := by ring
        nlinarith
      exact le_of_mul_le_mul_left hkey hρp
  have hA1 : A + (1 - L * γ - 2 * (L * γ * R) ^ 2) * B ≤
      2 * Δ / γ + K * ε * (L * γ * σ ^ 2 / ε) * (1 + 2 * (L * γ * R)) := by
    rw [hqε]
    have hE2' := mul_le_mul_of_nonneg_left hE2 (by positivity : (0 : ℝ) ≤ γ * L ^ 2 / 2)
    have e1 : γ * L ^ 2 / 2 * (2 * γ ^ 2 * R * (R * B + K * σ ^ 2)) =
        γ / 2 * (2 * (L * γ * R) ^ 2 * B + 2 * (L * γ * R) * (K * (L * γ * σ ^ 2))) := by ring
    have e2 : γ / 2 * (2 * Δ / γ) = Δ := by field_simp
    have e3 : K * (γ ^ 2 * L / 2 * σ ^ 2) = γ / 2 * (K * (L * γ * σ ^ 2)) := by ring
    have hmain : γ / 2 * (A + (1 - L * γ - 2 * (L * γ * R) ^ 2) * B) ≤
        γ / 2 * (2 * Δ / γ + K * (L * γ * σ ^ 2) * (1 + 2 * (L * γ * R))) := by
      rw [mul_add (γ / 2) (2 * Δ / γ), e2]
      nlinarith
    exact le_of_mul_le_mul_left hmain (by positivity)
  have hY : 2 * Δ / γ * (2 * (L * γ * R) + 2 * (L * γ) + 4 * (L * γ * σ ^ 2 / ε)) ≤ K * ε := by
    have e : 2 * Δ / γ * (2 * (L * γ * R) + 2 * (L * γ) + 4 * (L * γ * σ ^ 2 / ε)) =
        ε * (4 * (R + 1) * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2) := by
      field_simp
      ring
    rw [e, mul_comm (K : ℝ) ε]
    exact mul_le_mul_of_nonneg_left hK hε.le
  exact final_combination A B (2 * Δ / γ) (K * ε) (L * γ) (L * γ * R) (L * γ * σ ^ 2 / ε)
    (by positivity) hlam1 (by positivity) hrho1 hq0 hq' hcase' (by positivity) hA1 hE3 hY

theorem main_theorem {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (L σ ε R lower : ℝ) (x0 : Point d) (T : Tree) (m : ℕ → ℕ)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hsmooth : SmoothObjective f L) (hlower : LowerBounded f lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (hT : T.WellFormed) (hm : T.IsMainBranch m)
    (h1 : SampleIndependent T m (stepSize L σ ε R) x0 g (P : Measure (ℕ → Ω)))
    (h2 : ReprContained T m) (h3 : DistanceBounded T m R) (K : ℕ)
    (hK : 4 * (R + 1) * L * (f x0 - lower) / ε + 8 * σ ^ 2 * L * (f x0 - lower) / ε ^ 2 ≤ K) :
    (∀ k, Integrable (fun η => ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (m k))‖ ^ 2)
      (P : Measure (ℕ → Ω))) ∧
    1 / (K : ℝ) * ∑ k ∈ Finset.range K,
      ∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω)) ≤
      ε := by
  classical
  obtain ⟨hγ0, hlam1, hrho1, hq, hcase⟩ := stepSize_facts L σ ε R hL hσ hε hR
  have hgm := hg.measurable
  have hXm := vertex_measurable T (stepSize L σ ε R) x0 g hgm
  have hmo := moments f L σ R T hT m hm μ P g (stepSize L σ ε R) x0 hsmooth hg hlaw h1 h2 h3
  have hgX : ∀ k, Integrable (fun η => ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (m k))‖ ^ 2)
      (P : Measure (ℕ → Ω)) := fun k =>
    (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo k).1).2
  refine ⟨hgX, ?_⟩
  have hgZ : ∀ k, Integrable (fun η =>
      ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k))‖ ^ 2)
      (P : Measure (ℕ → Ω)) := fun k =>
    (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo k).2.1).2
  have hXZ : ∀ k, Integrable (fun η => ‖T.vertex (stepSize L σ ε R) x0 g η (m k) -
      T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) :=
    fun k => sub_sq_integrable (P : Measure (ℕ → Ω)) _ _ (hXm _) (hXm _) (hmo k).1 (hmo k).2.1
  choose p hpk hpR I hI hDb using fun k =>
    delay_bound f L σ R T hT m hm μ P g (stepSize L σ ε R) x0 hL hsmooth hg hlaw h1 h2 h3 k
  have hFK : (∫ η, f (T.vertex (stepSize L σ ε R) x0 g η (m 0)) ∂(P : Measure (ℕ → Ω))) -
      (∫ η, f (T.vertex (stepSize L σ ε R) x0 g η (m K)) ∂(P : Measure (ℕ → Ω))) ≤
      f x0 - lower := by
    have hfun : (fun η : ℕ → Ω => f (T.vertex (stepSize L σ ε R) x0 g η (m 0))) =
        fun _ => f x0 :=
      funext (fun η => by rw [(aux_zero T hT m hm R h2 h3 (stepSize L σ ε R) x0 g η).1])
    have hfi := (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo K).1).1
    have hlow := integral_mono (integrable_const lower) hfi (fun η => hlower _)
    rw [hfun, integral_const]
    rw [integral_const] at hlow
    simp only [probReal_univ, smul_eq_mul, one_mul] at hlow ⊢
    linarith
  have hyoung : ∀ k, L * stepSize L σ ε R * R *
      (∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      L * stepSize L σ ε R * R * (1 + L * stepSize L σ ε R * R) *
        (∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k))‖ ^ 2
          ∂(P : Measure (ℕ → Ω))) +
      (1 + L * stepSize L σ ε R * R) * L ^ 2 *
        (∫ η, ‖T.vertex (stepSize L σ ε R) x0 g η (m k) -
          T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) := by
    intro k
    have hρ0 : 0 ≤ L * stepSize L σ ε R * R := by positivity
    have i0 := (hgX k).const_mul (L * stepSize L σ ε R * R)
    have i1 := (hgZ k).const_mul (L * stepSize L σ ε R * R * (1 + L * stepSize L σ ε R * R))
    have i2 := (hXZ k).const_mul ((1 + L * stepSize L σ ε R * R) * L ^ 2)
    have i12 : Integrable (fun η => L * stepSize L σ ε R * R * (1 + L * stepSize L σ ε R * R) *
        ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k))‖ ^ 2 +
        (1 + L * stepSize L σ ε R * R) * L ^ 2 * ‖T.vertex (stepSize L σ ε R) x0 g η (m k) -
          T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) :=
      i1.add i2
    have hmono := integral_mono i0 i12 (fun η => young_split _ L hρ0 _ _ _ _
      (hsmooth.2 (T.vertex (stepSize L σ ε R) x0 g η (m k))
        (T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k))))
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul] at hmono
    exact hmono
  have hzero : R = 0 → ∀ k,
      (∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) =
      ∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k))‖ ^ 2
        ∂(P : Measure (ℕ → Ω)) := by
    intro hR0 k
    obtain ⟨p', hp', hpR', I', hI', hZ'⟩ :=
      tree_gap (Ω := Ω) T hT m hm R h2 h3 (stepSize L σ ε R) x0 g k
    have hpk' : p' = k := by
      rw [hR0] at hpR'
      have : (k : ℝ) ≤ p' := by linarith
      have : k ≤ p' := by exact_mod_cast this
      omega
    have hIe : I' = ∅ := by
      rw [hpk', Finset.Ico_self] at hI'
      exact Finset.subset_empty.mp hI'
    congr 1
    funext η
    rw [hZ' η, hIe, Finset.sum_empty, smul_zero, add_zero]
  have hA := assembly K L σ ε R (stepSize L σ ε R) (f x0 - lower) hL hε hR hγ0 hlam1 hrho1 hq
    hcase
    (fun k => ∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (m k))‖ ^ 2
      ∂(P : Measure (ℕ → Ω)))
    (fun k => ∫ η, ‖gradient f (T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k))‖ ^ 2
      ∂(P : Measure (ℕ → Ω)))
    (fun k => ∫ η, ‖T.vertex (stepSize L σ ε R) x0 g η (m k) -
      T.vertex (stepSize L σ ε R) x0 g η (T.auxNode m k)‖ ^ 2 ∂(P : Measure (ℕ → Ω)))
    (fun k => ∫ η, f (T.vertex (stepSize L σ ε R) x0 g η (m k)) ∂(P : Measure (ℕ → Ω)))
    p I (fun k => integral_nonneg (fun _ => sq_nonneg _))
    (fun k => expected_step f L σ R T hT m hm μ P g (stepSize L σ ε R) x0 hL hγ0.le hsmooth hg
      hlaw h1 h2 h3 k)
    hFK hI hpk hpR hDb hyoung hzero hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKp
  · subst hK0
    simp only [Nat.cast_zero, div_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
    exact hε.le
  · have hKr : (0 : ℝ) < K := by exact_mod_cast hKp
    rw [one_div, inv_mul_le_iff₀ hKr]
    exact hA

theorem branch_mono (T : Tree) (hT : T.WellFormed) (m : ℕ → ℕ) (hm : T.IsMainBranch m)
    (i j : ℕ) (hij : i ≤ j) : m i ≤ m j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have h1 := (hm.2 j).1
    have h2 := (hT (m (j + 1) - 1)).1
    rw [(hm.2 j).2] at h2
    omega

theorem advance_birch (q : Public) {Ω : Type} (g : Point q.d → Ω → Point q.d)
    (η : ℕ → Ω) (n c : ℕ) (s : State q.d) (hc : s.count = c)
    (hh : s.hist = q.tree.realize q.gamma q.x0 g η c) :
    StochasticGradient.advance (fun k s => (birch q).update s (g ((birch q).query s).2 (η k)))
      n c s = ⟨c + n, q.tree.realize q.gamma q.x0 g η (c + n), s.chosen⟩ := by
  induction n generalizing c s with
  | zero =>
    obtain ⟨count, hist, chosen⟩ := s
    change count = c at hc
    change hist = _ at hh
    subst hc hh
    rfl
  | succ n ih =>
    have hstep : (birch q).update s (g ((birch q).query s).2 (η c)) =
        ⟨c + 1, q.tree.realize q.gamma q.x0 g η (c + 1), s.chosen⟩ := by
      change (⟨s.count + 1, s.hist.step q.tree q.gamma s.count
        (g (s.hist.nodes (q.tree.point s.count)) (η c)), s.chosen⟩ : State q.d) = _
      rw [hc, hh]
      rfl
    change StochasticGradient.advance _ n (c + 1)
      ((birch q).update s (g ((birch q).query s).2 (η c))) = _
    rw [hstep, ih (c + 1) _ rfl rfl, Nat.add_right_comm, Nat.add_assoc]

theorem execute_birch (q : Public) (hT : q.tree.WellFormed) (hm : q.tree.IsMainBranch q.branch)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point q.d → Ω → Point q.d) (i : Fin (q.K + 1)) (η : ℕ → Ω) :
    execute (gradientOracle P g) (birch q) (fun _ => q.branch q.K) i η =
      q.tree.vertex q.gamma q.x0 g η (q.branch i.val) := by
  erw [StochasticGradient.execute_advance]
  have hadv := advance_birch q g η (q.branch q.K) 0 ((birch q).initial i) rfl rfl
  change ((birch q).output (StochasticGradient.advance (fun k s => (birch q).update s
    (g ((birch q).query s).2 (η k))) (q.branch q.K) 0 ((birch q).initial i))) = _
  rw [hadv]
  change (q.tree.realize q.gamma q.x0 g η (0 + q.branch q.K)).nodes (q.branch i.val) = _
  rw [Nat.zero_add]
  exact (realize_stable q.tree hT q.gamma q.x0 g η _).1 _
    (branch_mono q.tree hT q.branch hm _ _ (Nat.lt_succ_iff.mp i.isLt))

theorem birch_success (p : Params) (hp : spec.valid p) (I : Instance p.d)
    (O : Oracle (Point p.d) (Point p.d)) (hO : spec.admissible p I O) :
    spec.successful p I
      (fun z : (birch (publicInput p)).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (birch (publicInput p)) (fun _ => p.branch (horizon p.L p.σ p.ε p.Δ p.R))
          z.1 z.2)
      ⟨((birch (publicInput p)).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  obtain ⟨hL, hσ, hε, hΔ, hR, hT, hm, h2, h3⟩ := hp
  obtain ⟨hsm, hlow, hgap, Ω, mΩ, μ, P, g, hlaw, hgs, hind, rfl⟩ := hO
  let := mΩ
  set q := publicInput p with hq
  set K := horizon p.L p.σ p.ε p.Δ p.R with hKdef
  have hbound : 4 * (p.R + 1) * p.L * (I.f p.x0 - I.lower) / p.ε +
      8 * p.σ ^ 2 * p.L * (I.f p.x0 - I.lower) / p.ε ^ 2 ≤ ((K + 1 : ℕ) : ℝ) := by
    have hmono : 4 * (p.R + 1) * p.L * (I.f p.x0 - I.lower) / p.ε +
        8 * p.σ ^ 2 * p.L * (I.f p.x0 - I.lower) / p.ε ^ 2 ≤
        4 * (p.R + 1) * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 := by
      have h1 : 0 ≤ 4 * (p.R + 1) * p.L / p.ε := by positivity
      have h2' : 0 ≤ 8 * p.σ ^ 2 * p.L / p.ε ^ 2 := by positivity
      have e1 : ∀ x : ℝ, 4 * (p.R + 1) * p.L * x / p.ε + 8 * p.σ ^ 2 * p.L * x / p.ε ^ 2 =
          (4 * (p.R + 1) * p.L / p.ε + 8 * p.σ ^ 2 * p.L / p.ε ^ 2) * x := by
        intro x; ring
      rw [e1, e1]
      exact mul_le_mul_of_nonneg_left hgap (add_nonneg h1 h2')
    have hceil := Nat.le_ceil (4 * (p.R + 1) * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ /
      p.ε ^ 2)
    push_cast
    change _ ≤ ((⌈4 * (p.R + 1) * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊ : ℕ) :
      ℝ) + 1
    linarith
  obtain ⟨hint, hacc⟩ := main_theorem I.f p.L p.σ p.ε p.R I.lower p.x0 p.tree p.branch μ P g
    hL hσ hε hR hsm hlow hgs hlaw hT hm hind h2 h3 (K + 1) hbound
  let x : Fin (K + 1) → (ℕ → Ω) → Point p.d := fun j η =>
    p.tree.vertex (stepSize p.L p.σ p.ε p.R) p.x0 g η (p.branch j.val)
  have hxm (j : Fin (K + 1)) : Measurable (x j) :=
    vertex_measurable p.tree _ p.x0 g hgs.measurable _
  have hxi (j : Fin (K + 1)) : Integrable (fun η => ‖gradient I.f (x j η)‖ ^ 2)
      (P : Measure (ℕ → Ω)) := hint j.val
  have ha : (1 / ((K + 1 : ℕ) : ℝ)) * ∑ j : Fin (K + 1),
      (∫ η, ‖gradient I.f (x j η)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
    have hs := Fin.sum_univ_eq_sum_range (fun k => ∫ η, ‖gradient I.f
      (p.tree.vertex (stepSize p.L p.σ p.ε p.R) p.x0 g η (p.branch k))‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) (K + 1)
    show (1 / ((K + 1 : ℕ) : ℝ)) * ∑ j : Fin (K + 1), (fun k => ∫ η, ‖gradient I.f
      (p.tree.vertex (stepSize p.L p.σ p.ε p.R) p.x0 g η (p.branch k))‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) (j : ℕ) ≤ p.ε
    rw [hs]
    exact hacc
  have hu := OracleTemplate.Rennala.uniform_prefix_accuracy P I.f K x p.ε hxm hxi ha
  have hfun : (fun z : Fin (K + 1) × (ℕ → Ω) =>
      execute (gradientOracle P g) (birch q) (fun _ => p.branch K) z.1 z.2) =
      fun z => x z.1 z.2 := by
    funext z
    exact execute_birch q hT hm P g z.1 z.2
  change spec.successful p I
    (fun z : Fin (K + 1) × (ℕ → Ω) =>
      execute (gradientOracle P g) (birch q) (fun _ => p.branch K) z.1 z.2)
    ⟨((PMF.uniformOfFintype (Fin (K + 1))).toMeasure).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  rw [hfun]
  exact ⟨hu.1, hu.2.1, hu.2.2.2⟩

end OracleTemplate.BirchSgd
