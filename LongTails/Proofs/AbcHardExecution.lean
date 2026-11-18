import LongTails.Proofs.AbcHardSimulation

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardExecution

open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask
open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation

variable {d n : ℕ} {St : Type*}

noncomputable def coinCount (qbar : ℝ) (ω : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => coinCount qbar ω t + if ω t ≤ qbar then 1 else 0

noncomputable def level (n : ℕ) (qbar : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℕ := min (n + 1) (coinCount qbar ω t)

lemma coinCount_mono (qbar : ℝ) (ω : ℕ → ℝ) {s t : ℕ} (h : s ≤ t) :
    coinCount qbar ω s ≤ coinCount qbar ω t := by
  induction t with
  | zero => simp [Nat.le_zero.mp h]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hs | hs
    · exact (ih (by omega)).trans (by simp [coinCount])
    · rw [show s = t + 1 by omega]

lemma level_mono (n : ℕ) (qbar : ℝ) (ω : ℕ → ℝ) {s t : ℕ} (h : s ≤ t) :
    level n qbar ω s ≤ level n qbar ω t :=
  min_le_min le_rfl (coinCount_mono qbar ω h)

lemma level_le (n : ℕ) (qbar : ℝ) (ω : ℕ → ℝ) (t : ℕ) : level n qbar ω t ≤ n + 1 :=
  min_le_left _ _

lemma level_succ_of_gt (n : ℕ) (qbar : ℝ) (ω : ℕ → ℝ) (t : ℕ) (h : qbar < ω t) :
    level n qbar ω (t + 1) = level n qbar ω t := by
  simp [level, coinCount, not_le.mpr h]

noncomputable def simReply (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (r : ℕ)
    (x0 x : Space d) (ω : ℝ) : Space d :=
  knownPart S π (stageUpTo r (sel π (toUnit S x0 x))) x0 x +
    if stageUpTo r (sel π (toUnit S x0 x)) < r then
      coin (qf (stageUpTo r (sel π (toUnit S x0 x)))) ω •
        ((S.a / S.lam) • visibleGrad π (stageUpTo r (sel π (toUnit S x0 x)) + 1) (toUnit S x0 x) -
          knownPart S π (stageUpTo r (sel π (toUnit S x0 x))) x0 x)
    else 0

lemma simReply_prefix (S : Scale) (qf : ℕ → ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ)
    (x0 x : Space d) (ω : ℝ) (h : ∀ k : Fin (n + 1), k.val < r → π k = ρ k) :
    simReply S qf π r x0 x ω = simReply S qf ρ r x0 x ω := by
  have hs : ∀ i : Fin (n + 1), i.val < r → sel π (toUnit S x0 x) i = sel ρ (toUnit S x0 x) i := by
    intro i hi; rw [sel_apply, sel_apply, h i hi]
  have hst := stageUpTo_congr r _ _ hs
  have hle := stageUpTo_le r (sel ρ (toUnit S x0 x))
  have hk : knownPart S π (stageUpTo r (sel π (toUnit S x0 x))) x0 x =
      knownPart S ρ (stageUpTo r (sel ρ (toUnit S x0 x))) x0 x := by
    rw [hst, knownPart, knownPart, knownGrad_prefix π ρ _ _ (fun k hk => h k (by omega))]
  unfold simReply
  rw [hk, hst]
  split_ifs with hlt
  · rw [visibleGrad_prefix π ρ _ _ (fun k hk => h k (by omega))]
  · rfl

noncomputable def simState (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState S qf π x0 query update initial qbar ω t
    update s (simReply S qf π (level n qbar ω (t + 1)) x0 (query s) (ω t))

noncomputable def trueState (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := trueState S qf π x0 query update initial ω t
    update s (reply S qf π x0 (query s) (ω t))

lemma simState_prefix (S : Scale) (qf : ℕ → ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (t : ℕ) (h : ∀ k : Fin (n + 1), k.val < level n qbar ω t → π k = ρ k) :
    simState S qf π x0 query update initial qbar ω t =
      simState S qf ρ x0 query update initial qbar ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := level_mono n qbar ω (Nat.le_add_right t 1)
    have he := ih (fun k hk => h k (by omega))
    simp only [simState]
    rw [he, simReply_prefix S qf π ρ _ x0 _ _ h]

lemma reply_outside (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℝ) (hw : 2 * radius n ≤ ‖toUnit S x0 x‖) :
    reply S qf π x0 x ω = (S.a / S.lam) • wallGrad n (toUnit S x0 x) := by
  simp only [reply, knownPart, objGrad, knownGrad_outside π _ _ hw, hardGrad_outside π _ hw,
    sub_self, smul_zero, add_zero]

lemma simReply_outside (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (r : ℕ)
    (x0 x : Space d) (ω : ℝ) (hw : 2 * radius n ≤ ‖toUnit S x0 x‖) :
    simReply S qf π r x0 x ω = (S.a / S.lam) • wallGrad n (toUnit S x0 x) := by
  simp only [simReply, knownPart, knownGrad_outside π _ _ hw, visibleGrad_outside π _ _ hw,
    sub_self, smul_zero, ite_self, add_zero]

lemma reply_eq_simReply (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (qbar : ℝ) (ω : ℕ → ℝ) (t : ℕ)
    (hhit : ‖toUnit S x0 x‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), level n qbar ω t ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4)
    (hq : ∀ m, m ≤ level n qbar ω t → qf m ≤ qbar) :
    reply S qf π x0 x (ω t) = simReply S qf π (level n qbar ω (t + 1)) x0 x (ω t) := by
  set w := toUnit S x0 x
  by_cases hw : 2 * radius n ≤ ‖w‖
  · rw [reply_outside S qf π x0 x _ hw, simReply_outside S qf π _ x0 x _ hw]
  · push Not at hw
    have hsm := hhit hw.le
    have hmono := level_mono n qbar ω (Nat.le_add_right t 1)
    have hsm' : ∀ i : Fin (n + 1), level n qbar ω (t + 1) ≤ i.val → |sel π w i| ≤ 1 / 4 :=
      fun i hi => hsm i (by omega)
    have hst : stageUpTo (level n qbar ω (t + 1)) (sel π w) = stage (sel π w) :=
      stageUpTo_eq _ _ hsm'
    have hstage : stage (sel π w) ≤ level n qbar ω t := by
      rw [← stageUpTo_eq _ _ hsm]; exact stageUpTo_le _ _
    unfold simReply reply
    rw [hst]
    by_cases hlt : stage (sel π w) < level n qbar ω (t + 1)
    · rw [ite_eq_left hlt, objGrad, visibleGrad_eq π _ w (fun i hi => small_of_stage _ i hi)]
    · rw [ite_eq_right hlt, add_zero]
      have heq : stage (sel π w) = level n qbar ω t := by omega
      by_cases hfull : n + 1 ≤ stage (sel π w)
      · rw [objGrad, knownPart, knownGrad_full π _ w hfull, sub_self, smul_zero, add_zero]
      · have hlev : level n qbar ω (t + 1) = level n qbar ω t := by omega
        have hcount : ¬ ω t ≤ qbar := by
          intro hc
          have h1 : level n qbar ω (t + 1) = min (n + 1) (coinCount qbar ω t + 1) := by
            simp [level, coinCount, hc]
          have h2 : level n qbar ω t = min (n + 1) (coinCount qbar ω t) := rfl
          omega
        have hc0 : coin (qf (stage (sel π w))) (ω t) = 0 := by
          unfold coin
          rw [ite_eq_right]
          intro hle
          exact hcount (hle.trans (hq _ hstage))
        rw [hc0, zero_smul, add_zero]

lemma coupling (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N,
      let x := query (simState S qf π x0 query update initial qbar ω t)
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), level n qbar ω t ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4)
    (hq : ∀ m, m ≤ level n qbar ω N → qf m ≤ qbar) :
    simState S qf π x0 query update initial qbar ω N =
      trueState S qf π x0 query update initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hmono := level_mono n qbar ω (Nat.le_add_right N 1)
    have he := ih (fun t ht => hhit t (by omega)) (fun m hm => hq m (by omega))
    simp only [simState, trueState]
    rw [← he, reply_eq_simReply S qf π x0 _ qbar ω N (hhit N (by omega))
      (fun m hm => hq m (by omega))]

end LongTails.Proofs.AbcHardExecution
