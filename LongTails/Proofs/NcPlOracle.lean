import LongTails.Proofs.NcPlMoreau
import LongTails.Proofs.NcPlTrunc
import LongTails.Proofs.AbcHardOracle

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlOracle

open Classical
open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc LongTails.Proofs.NcPlSchedule
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlCut
open LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlLipschitz LongTails.Proofs.NcPlPL
open LongTails.Proofs.NcPlMoreau LongTails.Proofs.NcPlTrunc
open LongTails.Proofs.AbcChain (Chain)
open LongTails.Proofs.AbcHardFunction (Space sel sel_apply sel_norm adjoint_norm adjoint_congr)
open LongTails.Proofs.MintyChainGeometry (ball ball_norm_le ball_lipschitz ball_of_le)
open LongTails.Proofs.AbcHardOracle (coin unif coin_integral coin_sq_integral coin_integrable
  setOf_le_measurable)

section TruncChain

variable {k : ℕ}

noncomputable def trC (s : ℕ) (c : Chain k) : Chain k :=
  WithLp.toLp 2 (fun p : Fin (k + 1) => if p.val < s then c p else 0)

lemma trC_apply (s : ℕ) (c : Chain k) (p : Fin (k + 1)) :
    trC s c p = if p.val < s then c p else 0 := rfl

lemma seq_trC (s : ℕ) (c : Chain k) : seq (trC s c) = tr s (seq c) := by
  funext p
  unfold tr
  by_cases hp : p < k + 1
  · rw [seq_lt _ hp, seq_lt _ hp, trC_apply]
  · rw [seq_of_ge _ (by omega), seq_of_ge _ (by omega), ite_self]

lemma trC_full (c : Chain k) : trC (k + 1) c = c := by
  ext p
  rw [trC_apply, ite_eq_left p.isLt]

lemma trC_sub_sq (s : ℕ) (c c' : Chain k) (p : Fin (k + 1)) :
    (trC s c' p - trC s c p) ^ 2 ≤ (c' p - c p) ^ 2 := by
  rw [trC_apply, trC_apply]
  split_ifs
  · exact le_rfl
  · rw [sub_zero]
    nlinarith [sq_nonneg (c' p - c p)]

lemma trC_sub_norm (s : ℕ) (c c' : Chain k) : ‖trC s c' - trC s c‖ ≤ ‖c' - c‖ := by
  apply norm_le_of_sq_le _ (norm_nonneg _)
  rw [norm_sub_sq_eq]
  exact Finset.sum_le_sum fun p _ => trC_sub_sq s c c' p

lemma trC_succ_sub_sq (s : ℕ) (b : Chain k) : ‖trC (s + 1) b - trC s b‖ ^ 2 ≤ seq b s ^ 2 := by
  rw [← sum_seq_sq, seq_trC, seq_trC]
  exact tr_succ_sub (seq b) s (k + 1)

end TruncChain

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

noncomputable def vecA (a b : Chain G.k) (c : ℝ) : Chain G.k :=
  WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) (seq b) c p)

noncomputable def vecB (a b : Chain G.k) : Chain G.k :=
  WithLp.toLp 2 (fun p : Fin (G.k + 1) => gB G.n G.r (seq a) (seq b) p)

lemma vecA_lip_sq (a a' b b' : Chain G.k) {c c' : ℝ} (hc : |c'| ≤ 1) :
    ‖vecA G a' b' c' - vecA G a b c‖ ^ 2 ≤
      2 ^ 33 * (‖a' - a‖ ^ 2 + ‖b' - b‖ ^ 2) + 2 ^ 15 * ((G.m : ℝ) + 1) * (c' - c) ^ 2 := by
  have h := gA_lip (m := G.m) G.scales (c := c) (c' := c') hc (seq a) (seq a') (seq b) (seq b')
  rw [← G.hk, sum_seq_sq, sum_seq_sq, Finset.sum_range] at h
  rw [norm_sub_sq_eq]
  exact h

lemma vecB_lip_sq (a a' b b' : Chain G.k) :
    ‖vecB G a' b' - vecB G a b‖ ^ 2 ≤ 2 ^ 25 * (‖a' - a‖ ^ 2 + ‖b' - b‖ ^ 2) := by
  have h := gB_lip (m := G.m) G.scales (seq a) (seq a') (seq b) (seq b')
  rw [← G.hk, sum_seq_sq, sum_seq_sq, Finset.sum_range] at h
  rw [norm_sub_sq_eq]
  exact h

noncomputable def gxOf (x : Space d) (A : Chain G.k) : Space d :=
  (1 / 16 : ℝ) • x + cutv G.Bx x • (sel π).adjoint A + ⟪A, sel π x⟫ • cutGrad G.Bx x

noncomputable def gyOf (y : Space d) (B : Chain G.k) (R : ℝ) : Space d :=
  baseGrad (lamOf G.n) G.ρ y + cutv G.By y • (sel π).adjoint B + R • cutGrad G.By y

noncomputable def yhat (y : Space d) : Chain G.k := sel π (ball (2 * G.By) y)

noncomputable def AK (s : ℕ) (x y : Space d) : Chain G.k :=
  trC s (vecA G (trC s (chA G π x)) (trC s (yhat G π y)) (cutv G.By y))

noncomputable def BK (s : ℕ) (x y : Space d) : Chain G.k :=
  trC s (vecB G (trC s (chA G π x)) (trC s (yhat G π y)))

noncomputable def RK (s : ℕ) (x y : Space d) : ℝ :=
  rF G.m G.n G.r (seq (trC s (chA G π x))) (seq (trC s (yhat G π y)))

noncomputable def knownGx (s : ℕ) (x y : Space d) : Space d := gxOf G π x (AK G π s x y)

noncomputable def knownGy (s : ℕ) (x y : Space d) : Space d :=
  gyOf G π y (BK G π s x y) (RK G π s x y)

lemma hardGx_ball (x y : Space d) :
    hardGx G π x y = gxOf G π x (vecA G (chA G π x) (yhat G π y) (cutv G.By y)) := by
  rcases le_or_gt ‖y‖ (2 * G.By) with h | h
  · unfold yhat
    rw [ball_of_le _ _ h]
    rfl
  · have hv : vA G π x y = vecA G (chA G π x) (yhat G π y) (cutv G.By y) := by
      unfold vA vecA
      rw [cutv_of_ge G.hBy h.le]
      congr 1
      funext p
      unfold gA gAu
      rw [zero_mul, zero_mul]
    unfold hardGx gxOf
    rw [hv]

lemma hardGy_ball (x y : Space d) :
    hardGy G π x y = gyOf G π y (vecB G (chA G π x) (yhat G π y))
      (rF G.m G.n G.r (seq (chA G π x)) (seq (yhat G π y))) := by
  rcases le_or_gt ‖y‖ (2 * G.By) with h | h
  · unfold yhat
    rw [ball_of_le _ _ h]
    rfl
  · unfold hardGy gyOf
    rw [cutv_of_ge G.hBy h.le, cutGrad_of_ge G.hBy h.le]
    simp only [zero_smul, smul_zero]

lemma known_full_x (x y : Space d) : knownGx G π (G.k + 1) x y = hardGx G π x y := by
  rw [hardGx_ball]
  unfold knownGx AK
  rw [trC_full, trC_full, trC_full]

lemma known_full_y (x y : Space d) : knownGy G π (G.k + 1) x y = hardGy G π x y := by
  rw [hardGy_ball]
  unfold knownGy BK RK
  rw [trC_full, trC_full, trC_full]

noncomputable def obsVec (x y : Space d) : Space d :=
  WithLp.toLp 2 (fun j => max |ball (2 * G.Bx) x j| |ball (2 * G.By) y j|)

lemma obsVec_norm (x y : Space d) : ‖obsVec G x y‖ ≤ 2 * G.Bx + 2 * G.By := by
  have hx := ball_norm_le (2 * G.Bx) (by have := G.hBx; positivity) x
  have hy := ball_norm_le (2 * G.By) (by have := G.hBy; positivity) y
  have h0 : 0 ≤ ‖ball (2 * G.Bx) x‖ + ‖ball (2 * G.By) y‖ := by positivity
  refine le_trans (norm_le_of_sq_le _ h0 ?_) (add_le_add hx hy)
  have e : ∀ j ∈ (Finset.univ : Finset (Fin d)), obsVec G x y j ^ 2 ≤
      ball (2 * G.Bx) x j ^ 2 + ball (2 * G.By) y j ^ 2 := by
    intro j _
    change (max |ball (2 * G.Bx) x j| |ball (2 * G.By) y j|) ^ 2 ≤ _
    rcases max_cases |ball (2 * G.Bx) x j| |ball (2 * G.By) y j| with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, sq_abs]
      nlinarith [sq_nonneg (ball (2 * G.By) y j)]
    · rw [h, sq_abs]
      nlinarith [sq_nonneg (ball (2 * G.Bx) x j)]
  refine (Finset.sum_le_sum e).trans ?_
  rw [Finset.sum_add_distrib, ← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  nlinarith [norm_nonneg (ball (2 * G.Bx) x), norm_nonneg (ball (2 * G.By) y)]

def big (θ : ℝ) (x y : Space d) (j : Fin d) : Prop := θ < |obsVec G x y j|

lemma small_of_not_big {θ : ℝ} {x y : Space d} {j : Fin d} (h : ¬ big G θ x y j) :
    |ball (2 * G.Bx) x j| ≤ θ ∧ |ball (2 * G.By) y j| ≤ θ := by
  unfold big at h
  have h1 : obsVec G x y j = max |ball (2 * G.Bx) x j| |ball (2 * G.By) y j| := rfl
  have h0 : 0 ≤ obsVec G x y j := by
    rw [h1]
    exact le_max_of_le_left (abs_nonneg _)
  rw [abs_of_nonneg h0, h1] at h
  have h2 := not_lt.mp h
  exact ⟨(le_max_left _ _).trans h2, (le_max_right _ _).trans h2⟩

noncomputable def stage (θ : ℝ) (x y : Space d) : ℕ :=
  Finset.univ.sup (fun p : Fin (G.k + 1) => if big G θ x y (π p) then p.val + 1 else 0)

noncomputable def stageUpTo (θ : ℝ) (lev : ℕ) (x y : Space d) : ℕ :=
  Finset.univ.sup
    (fun p : Fin (G.k + 1) => if p.val < lev ∧ big G θ x y (π p) then p.val + 1 else 0)

lemma not_big_of_stage (θ : ℝ) (x y : Space d) (p : Fin (G.k + 1))
    (hp : stage G π θ x y ≤ p.val) : ¬ big G θ x y (π p) := by
  intro h
  have hle : (if big G θ x y (π p) then p.val + 1 else 0) ≤ stage G π θ x y :=
    Finset.le_sup (f := fun p : Fin (G.k + 1) => if big G θ x y (π p) then p.val + 1 else 0)
      (Finset.mem_univ p)
  rw [ite_eq_left h] at hle
  omega

lemma stage_le (θ : ℝ) (x y : Space d) : stage G π θ x y ≤ G.k + 1 := by
  apply Finset.sup_le
  intro p _
  split_ifs <;> omega

lemma stageUpTo_le (θ : ℝ) (lev : ℕ) (x y : Space d) : stageUpTo G π θ lev x y ≤ lev := by
  apply Finset.sup_le
  intro p _
  split_ifs with h <;> omega

lemma stageUpTo_eq (θ : ℝ) (lev : ℕ) (x y : Space d)
    (h : ∀ p : Fin (G.k + 1), lev ≤ p.val → ¬ big G θ x y (π p)) :
    stageUpTo G π θ lev x y = stage G π θ x y := by
  unfold stageUpTo stage
  congr 1
  funext p
  by_cases hp : p.val < lev
  · simp only [hp, true_and]
  · have := h p (by omega)
    simp only [hp, false_and, ↓reduceIte, this]

lemma stageUpTo_congr (ρ' : Fin (G.k + 1) ↪ Fin d) (θ : ℝ) (lev : ℕ) (x y : Space d)
    (h : ∀ p : Fin (G.k + 1), p.val < lev → π p = ρ' p) :
    stageUpTo G π θ lev x y = stageUpTo G ρ' θ lev x y := by
  unfold stageUpTo
  congr 1
  funext p
  by_cases hp : p.val < lev
  · rw [h p hp]
  · simp only [hp, false_and, ↓reduceIte]

section Prefix

variable (ρ' : Fin (G.k + 1) ↪ Fin d)

lemma trC_chA_prefix (s : ℕ) (x : Space d) (h : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p) :
    trC s (chA G π x) = trC s (chA G ρ' x) := by
  ext p
  rw [trC_apply, trC_apply]
  by_cases hp : p.val < s
  · rw [ite_eq_left hp, ite_eq_left hp]
    change cutv G.Bx x * x (π p) = cutv G.Bx x * x (ρ' p)
    rw [h p hp]
  · rw [ite_eq_right hp, ite_eq_right hp]

lemma trC_yhat_prefix (s : ℕ) (y : Space d) (h : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p) :
    trC s (yhat G π y) = trC s (yhat G ρ' y) := by
  ext p
  rw [trC_apply, trC_apply]
  by_cases hp : p.val < s
  · rw [ite_eq_left hp, ite_eq_left hp]
    change ball (2 * G.By) y (π p) = ball (2 * G.By) y (ρ' p)
    rw [h p hp]
  · rw [ite_eq_right hp, ite_eq_right hp]

lemma adjoint_trC_prefix (s : ℕ) (V : Chain G.k)
    (h : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p) :
    (sel π).adjoint (trC s V) = (sel ρ').adjoint (trC s V) :=
  adjoint_congr π ρ' (trC s V) s (fun p hp => by rw [trC_apply, ite_eq_right (by omega)]) h

lemma gxOf_prefix (s : ℕ) (x : Space d) (V : Chain G.k)
    (h : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p) :
    gxOf G π x (trC s V) = gxOf G ρ' x (trC s V) := by
  have hadj := adjoint_trC_prefix G π ρ' s V h
  unfold gxOf
  rw [← ContinuousLinearMap.adjoint_inner_left (sel π) x (trC s V),
    ← ContinuousLinearMap.adjoint_inner_left (sel ρ') x (trC s V), hadj]

lemma gyOf_prefix (s : ℕ) (y : Space d) (V : Chain G.k) (R : ℝ)
    (h : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p) :
    gyOf G π y (trC s V) R = gyOf G ρ' y (trC s V) R := by
  unfold gyOf
  rw [adjoint_trC_prefix G π ρ' s V h]

lemma knownGx_prefix (s t : ℕ) (hst : s ≤ t) (x y : Space d)
    (h : ∀ p : Fin (G.k + 1), p.val < t → π p = ρ' p) :
    knownGx G π s x y = knownGx G ρ' s x y := by
  have hs : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p := fun p hp => h p (by omega)
  unfold knownGx AK
  rw [trC_chA_prefix G π ρ' s x hs, trC_yhat_prefix G π ρ' s y hs]
  exact gxOf_prefix G π ρ' s x _ hs

lemma knownGy_prefix (s t : ℕ) (hst : s ≤ t) (x y : Space d)
    (h : ∀ p : Fin (G.k + 1), p.val < t → π p = ρ' p) :
    knownGy G π s x y = knownGy G ρ' s x y := by
  have hs : ∀ p : Fin (G.k + 1), p.val < s → π p = ρ' p := fun p hp => h p (by omega)
  unfold knownGy BK RK
  rw [trC_chA_prefix G π ρ' s x hs, trC_yhat_prefix G π ρ' s y hs]
  exact gyOf_prefix G π ρ' s y _ _ hs

end Prefix

section Exact

variable {θ : ℝ}

lemma seq_chA_small (hθ2 : θ ≤ 1 / 2) (s : ℕ) (x y : Space d)
    (hs : ∀ p : Fin (G.k + 1), s ≤ p.val → ¬ big G θ x y (π p)) :
    ∀ p, s ≤ p → |seq (chA G π x) p| ≤ 1 / 2 := by
  intro p hp
  by_cases hk : p < G.k + 1
  · rw [seq_lt _ hk, chA_eq_ball]
    change |cutv G.Bx x * ball (2 * G.Bx) x (π ⟨p, hk⟩)| ≤ 1 / 2
    rw [abs_mul]
    have h1 := (small_of_not_big G (hs ⟨p, hk⟩ hp)).1
    have h2 := cutv_abs G.Bx x
    have h3 := abs_nonneg (cutv G.Bx x)
    have h4 := abs_nonneg (ball (2 * G.Bx) x (π ⟨p, hk⟩))
    nlinarith
  · rw [seq_of_ge _ (by omega), abs_zero]
    norm_num

lemma seq_yhat_small (hθ0 : 0 ≤ θ) (s : ℕ) (x y : Space d)
    (hs : ∀ p : Fin (G.k + 1), s ≤ p.val → ¬ big G θ x y (π p)) :
    ∀ p, s ≤ p → |seq (yhat G π y) p| ≤ θ := by
  intro p hp
  by_cases hk : p < G.k + 1
  · rw [seq_lt _ hk]
    exact (small_of_not_big G (hs ⟨p, hk⟩ hp)).2
  · rw [seq_of_ge _ (by omega), abs_zero]
    exact hθ0

theorem known_exact (hθ0 : 0 ≤ θ) (hθρ : θ ≤ G.ρ) (hθ2 : θ ≤ 1 / 2) (s : ℕ) (x y : Space d)
    (hs : ∀ p : Fin (G.k + 1), s ≤ p.val → ¬ big G θ x y (π p)) :
    knownGx G π (s + 1) x y = hardGx G π x y ∧ knownGy G π (s + 1) x y = hardGy G π x y := by
  have ha := seq_chA_small G π hθ2 s x y hs
  have hb := seq_yhat_small G π hθ0 s x y hs
  have hA : AK G π (s + 1) x y = vecA G (chA G π x) (yhat G π y) (cutv G.By y) := by
    ext p
    change (if p.val < s + 1 then gA G.m G.n G.r (seq (trC (s + 1) (chA G π x)))
      (seq (trC (s + 1) (yhat G π y))) (cutv G.By y) p else 0) =
      gA G.m G.n G.r (seq (chA G π x)) (seq (yhat G π y)) (cutv G.By y) p
    rw [seq_trC, seq_trC]
    exact gA_trunc hθρ G.scales.hρ G.scales.ge _ _ _ s ha hb p
  have hB : BK G π (s + 1) x y = vecB G (chA G π x) (yhat G π y) := by
    ext p
    change (if p.val < s + 1 then gB G.n G.r (seq (trC (s + 1) (chA G π x)))
      (seq (trC (s + 1) (yhat G π y))) p else 0) =
      gB G.n G.r (seq (chA G π x)) (seq (yhat G π y)) p
    rw [seq_trC, seq_trC]
    exact gB_trunc hθρ G.scales.hρ G.scales.ge _ _ s ha hb p
  have hR : RK G π (s + 1) x y = rF G.m G.n G.r (seq (chA G π x)) (seq (yhat G π y)) := by
    unfold RK
    rw [seq_trC, seq_trC]
    exact rF_trunc hθρ G.scales.hρ G.scales.ge _ _ s ha hb
  constructor
  · rw [hardGx_ball]
    unfold knownGx
    rw [hA]
  · rw [hardGy_ball]
    unfold knownGy
    rw [hB, hR]

end Exact

def masked (s : ℕ) : Prop := s % (G.n + 2) ≠ G.n + 1 ∧ 2 * (s % (G.n + 2)) ≤ G.n

noncomputable def qOf (q : ℝ) (s : ℕ) : ℝ := if masked G s then q else 1

lemma qOf_pos {q : ℝ} (hq : 0 < q) (s : ℕ) : 0 < qOf G q s := by
  unfold qOf
  split_ifs
  · exact hq
  · exact one_pos

lemma qOf_le {q : ℝ} (hq : q ≤ 1) (s : ℕ) : qOf G q s ≤ 1 := by
  unfold qOf
  split_ifs
  · exact hq
  · exact le_rfl

noncomputable def replyX (θ q : ℝ) (x y : Space d) (ω : ℝ) : Space d :=
  knownGx G π (stage G π θ x y) x y + coin (qOf G q (stage G π θ x y)) ω •
    (hardGx G π x y - knownGx G π (stage G π θ x y) x y)

noncomputable def replyY (θ q : ℝ) (x y : Space d) (ω : ℝ) : Space d :=
  knownGy G π (stage G π θ x y) x y + coin (qOf G q (stage G π θ x y)) ω •
    (hardGy G π x y - knownGy G π (stage G π θ x y) x y)

noncomputable def simX (θ q : ℝ) (lev : ℕ) (x y : Space d) (ω : ℝ) : Space d :=
  knownGx G π (stageUpTo G π θ lev x y) x y +
    if stageUpTo G π θ lev x y < lev then
      coin (qOf G q (stageUpTo G π θ lev x y)) ω •
        (knownGx G π (stageUpTo G π θ lev x y + 1) x y -
          knownGx G π (stageUpTo G π θ lev x y) x y)
    else 0

noncomputable def simY (θ q : ℝ) (lev : ℕ) (x y : Space d) (ω : ℝ) : Space d :=
  knownGy G π (stageUpTo G π θ lev x y) x y +
    if stageUpTo G π θ lev x y < lev then
      coin (qOf G q (stageUpTo G π θ lev x y)) ω •
        (knownGy G π (stageUpTo G π θ lev x y + 1) x y -
          knownGy G π (stageUpTo G π θ lev x y) x y)
    else 0

lemma sim_prefix (ρ' : Fin (G.k + 1) ↪ Fin d) (θ q : ℝ) (lev : ℕ) (x y : Space d) (ω : ℝ)
    (h : ∀ p : Fin (G.k + 1), p.val < lev → π p = ρ' p) :
    simX G π θ q lev x y ω = simX G ρ' θ q lev x y ω ∧
      simY G π θ q lev x y ω = simY G ρ' θ q lev x y ω := by
  have hs := stageUpTo_congr G π ρ' θ lev x y h
  have hle := stageUpTo_le G ρ' θ lev x y
  unfold simX simY
  rw [hs, knownGx_prefix G π ρ' _ lev hle x y h, knownGy_prefix G π ρ' _ lev hle x y h]
  constructor
  · split_ifs with hlt
    · rw [knownGx_prefix G π ρ' _ lev (by omega) x y h]
    · rfl
  · split_ifs with hlt
    · rw [knownGy_prefix G π ρ' _ lev (by omega) x y h]
    · rfl

theorem reply_eq_sim {θ q : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ G.ρ) (hθ2 : θ ≤ 1 / 2)
    (x y : Space d) (lev lev' : ℕ) (hm : lev ≤ lev') (ω : ℝ)
    (hsmall : ∀ p : Fin (G.k + 1), lev ≤ p.val → ¬ big G θ x y (π p))
    (hcoin : lev' = lev → G.k + 1 ≤ lev ∨ (masked G lev ∧ q < ω)) :
    replyX G π θ q x y ω = simX G π θ q lev' x y ω ∧
      replyY G π θ q x y ω = simY G π θ q lev' x y ω := by
  have hst : stageUpTo G π θ lev' x y = stage G π θ x y :=
    stageUpTo_eq G π θ lev' x y (fun p hp => hsmall p (by omega))
  have hst2 : stageUpTo G π θ lev x y = stage G π θ x y := stageUpTo_eq G π θ lev x y hsmall
  have hle : stage G π θ x y ≤ lev := by
    rw [← hst2]
    exact stageUpTo_le G π θ lev x y
  have hex := known_exact G π hθ0 hθρ hθ2 (stage G π θ x y) x y
    (fun p hp => not_big_of_stage G π θ x y p hp)
  unfold replyX replyY simX simY
  rw [hst]
  by_cases hlt : stage G π θ x y < lev'
  · rw [ite_eq_left hlt, ite_eq_left hlt, hex.1, hex.2]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hlt, ite_eq_right hlt, add_zero, add_zero]
    have heq : lev' = lev := by omega
    have hsl : stage G π θ x y = lev := by omega
    rcases hcoin heq with hK | ⟨hmask, hq⟩
    · have hsK : stage G π θ x y = G.k + 1 := by
        have := stage_le G π θ x y
        omega
      rw [hsK, known_full_x, known_full_y]
      refine ⟨?_, ?_⟩ <;> simp only [sub_self, smul_zero, add_zero]
    · have hc : coin (qOf G q (stage G π θ x y)) ω = 0 := by
        rw [hsl]
        unfold qOf coin
        rw [ite_eq_left hmask, ite_eq_right (not_le.mpr hq)]
      rw [hc]
      refine ⟨?_, ?_⟩ <;> simp only [zero_smul, add_zero]

end LongTails.Proofs.NcPlOracle
