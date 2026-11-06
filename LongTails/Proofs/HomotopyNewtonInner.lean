import LongTails.Proofs.HomotopyNewtonSchedule
import LongTails.Proofs.TikhonovHomotopy

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HomotopyNewtonInner

open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP
open LongTails.Proofs.HomotopyNewtonSchedule
open LongTails.Proofs.MonotoneTensorBounds
open LongTails.Proofs.StiffNewtonStage
open LongTails.Proofs.TikhonovHomotopy

noncomputable section

variable {p : Params} (F : p.E → p.E)

def gval (k : ℕ) (z Fz : p.E) : ℝ :=
  ‖step p k • F (center p k z Fz) + center p k z Fz - anchor p k z‖

def innerSeq (k : ℕ) (z Fz : p.E) (j : ℕ) : ℕ → p.E
  | 0 => center p k z Fz
  | i + 1 =>
      newton F (stepParam p k (gval F k z Fz) j i)
        (target p k z Fz (stepParam p k (gval F k z Fz) j i)) (innerSeq k z Fz j i)

def attemptPoint (k : ℕ) (z Fz : p.E) (j : ℕ) : p.E :=
  innerSeq F k z Fz j (programLength p k (gval F k z Fz) j)

def acc (k : ℕ) (z Fz : p.E) (j : ℕ) : Prop :=
  ‖step p k • F (attemptPoint F k z Fz j) + attemptPoint F k z Fz j - anchor p k z‖ ≤
    ‖attemptPoint F k z Fz j - center p k z Fz‖ / 2

lemma target_step (hp : Valid p) (k : ℕ) (z Fz : p.E) :
    target p k z Fz (step p k) = anchor p k z := by
  unfold target; rw [div_self (step_pos hp k).ne', one_smul]; abel

lemma target_form (k : ℕ) (z Fz : p.E) (b : ℝ) :
    target p k z Fz b = center p k z Fz + (b / step p k) • (anchor p k z - center p k z Fz) := rfl

variable {F}

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.resid_unique (h : Regular F p.L) {b : ℝ} (hb : 0 < b) {v z1 z2 : p.E}
    (h1 : resid F b v z1 = 0) (h2 : resid F b v z2 = 0) : z1 = z2 := by
  have hm := h.mono z1 z2
  have heq : b • (F z1 - F z2) + (z1 - z2) = 0 := by
    have : resid F b v z1 - resid F b v z2 = b • (F z1 - F z2) + (z1 - z2) := by
      simp only [resid, smul_sub]; abel
    rw [← this, h1, h2, sub_zero]
  have hin : ‖z1 - z2‖ ^ 2 + b * ⟪F z1 - F z2, z1 - z2⟫ = 0 := by
    have := congrArg (fun u => ⟪u, z1 - z2⟫) heq
    simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      inner_zero_left] at this
    linarith
  have : ‖z1 - z2‖ ^ 2 = 0 := by nlinarith [mul_nonneg hb.le hm, sq_nonneg ‖z1 - z2‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this))

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.strong_resolvent (h : Regular F p.L) {a : ℝ} (ha : 0 < a) (y zs : p.E) :
    ‖y - zs‖ ≤ ‖(a • F y + y) - (a • F zs + zs)‖ := by
  have hm := h.mono y zs
  have hinner : ‖y - zs‖ ^ 2 ≤ ⟪(a • F y + y) - (a • F zs + zs), y - zs⟫ := by
    have : (a • F y + y) - (a • F zs + zs) = a • (F y - F zs) + (y - zs) := by
      simp only [smul_sub]; abel
    rw [this, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg ha.le hm]
  have h2 := real_inner_le_norm ((a • F y + y) - (a • F zs + zs)) (y - zs)
  rcases eq_or_lt_of_le (norm_nonneg (y - zs)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

lemma newton_block [FiniteDimensional ℝ p.E] (h : Regular F p.L) {b Q : ℝ} (hb : 0 ≤ b)
    {v zs : p.E} (hzs : resid F b v zs = 0) (hsmall : 169 * b * p.L * (12 * Q ^ 2) ≤ 1)
    (seq : ℕ → p.E) (N : ℕ) (hseq : ∀ n < N, seq (n + 1) = newton F b v (seq n))
    (h0 : nq F b zs (seq 0 - zs) ≤ 12 * Q ^ 2) :
    ∀ n ≤ N, nq F b zs (seq n - zs) ≤ 12 * Q ^ 2 / 4 ^ n
  | 0, _ => by simpa using h0
  | n + 1, hn => by
    have ih := newton_block h hb hzs hsmall seq N hseq h0 n (by omega)
    have hL := h.nonneg
    have hpow : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have hle : nq F b zs (seq n - zs) ≤ 12 * Q ^ 2 := by
      refine ih.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg Q]
    have hc : 169 * b * p.L * nq F b zs (seq n - zs) ≤ 1 :=
      le_trans (by gcongr) hsmall
    rw [hseq n (by omega)]
    refine (h.newton_quarter hb hzs hc).trans ?_
    rw [pow_succ]
    have : nq F b zs (seq n - zs) / 4 ≤ 12 * Q ^ 2 / 4 ^ n / 4 := by gcongr
    calc _ ≤ 12 * Q ^ 2 / 4 ^ n / 4 := this
      _ = 12 * Q ^ 2 / (4 ^ n * 4) := by field_simp

def stageTarget (k : ℕ) (z Fz : p.E) (g : ℝ) (j i : ℕ) : p.E := by
  classical
  exact if hz : ∃ y, resid F (stageParam p k g j i)
      (target p k z Fz (stageParam p k g j i)) y = 0 then Classical.choose hz else 0

lemma stageTarget_spec [FiniteDimensional ℝ p.E] (h : Regular F p.L) (hp : Valid p) (k : ℕ)
    (z Fz : p.E) {g : ℝ} (hg : 0 < g) (j i : ℕ) :
    resid F (stageParam p k g j i) (target p k z Fz (stageParam p k g j i))
      (stageTarget (F := F) k z Fz g j i) = 0 := by
  classical
  have hz := h.zero_exists (stageParam_pos hp k hg j i)
    (target p k z Fz (stageParam p k g j i))
  simp only [stageTarget, hz, ↓reduceDIte]
  exact Classical.choose_spec hz

lemma innerSeq_stage (k : ℕ) (z Fz : p.E) (j i r : ℕ) (hr : r < 3)
    (hi : i < stages p k (gval F k z Fz) j + 1) :
    innerSeq F k z Fz j (3 * i + r + 1) =
      newton F (stageParam p k (gval F k z Fz) j i)
        (target p k z Fz (stageParam p k (gval F k z Fz) j i))
        (innerSeq F k z Fz j (3 * i + r)) := by
  have hlt : 3 * i + r < 3 * (stages p k (gval F k z Fz) j + 1) := by omega
  have hdiv : (3 * i + r) / 3 = i := by omega
  simp only [innerSeq, stepParam, hlt, ↓reduceIte, hdiv]

lemma innerSeq_tail (k : ℕ) (z Fz : p.E) (j n : ℕ) :
    innerSeq F k z Fz j (3 * (stages p k (gval F k z Fz) j + 1) + n + 1) =
      newton F (step p k) (target p k z Fz (step p k))
        (innerSeq F k z Fz j (3 * (stages p k (gval F k z Fz) j + 1) + n)) := by
  have hlt : ¬ (3 * (stages p k (gval F k z Fz) j + 1) + n <
      3 * (stages p k (gval F k z Fz) j + 1)) := by omega
  simp only [innerSeq, stepParam, hlt, ↓reduceIte]

lemma pow_four_extra (n : ℕ) : (2 : ℝ) ^ (Nat.log2 n + 5) ≥ 16 * (n + 1) := by
  have h := Nat.lt_log2_self (n := n)
  have h' : (n : ℝ) + 1 ≤ 2 ^ (Nat.log2 n + 1) := by exact_mod_cast Nat.succ_le_of_lt h
  rw [show Nat.log2 n + 5 = (Nat.log2 n + 1) + 4 by ring, pow_add]
  nlinarith

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.bracket (h : Regular F p.L) (hp : Valid p) (k : ℕ) (z Fz : p.E) {zs : p.E}
    (hzs : resid F (step p k) (anchor p k z) zs = 0)
    (hball : ∀ y ∈ Metric.closedBall zs ‖zs - center p k z Fz‖, ‖fderiv ℝ F y‖ ≤ stiff p) :
    ‖zs - center p k z Fz‖ ≤ gval F k z Fz ∧
      gval F k z Fz ≤ (1 + step p k * stiff p) * ‖zs - center p k z Fz‖ := by
  set a := step p k
  set c := center p k z Fz
  have ha := step_pos hp k
  have hw : a • F zs + zs = anchor p k z := by
    simp only [resid, sub_eq_zero] at hzs; exact hzs
  have hgform : gval F k z Fz = ‖(a • F c + c) - (a • F zs + zs)‖ := by
    unfold gval; rw [hw]
  constructor
  · rw [hgform, norm_sub_rev zs c]; exact h.strong_resolvent ha c zs
  · rw [hgform]
    have hc : c ∈ Metric.closedBall zs ‖zs - c‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    have hz : zs ∈ Metric.closedBall zs ‖zs - c‖ := Metric.mem_closedBall_self (norm_nonneg _)
    have hl := h.lipschitz_on_ball hball hc hz
    have : (a • F c + c) - (a • F zs + zs) = a • (F c - F zs) + (c - zs) := by
      simp only [smul_sub]; abel
    rw [this]
    calc ‖a • (F c - F zs) + (c - zs)‖ ≤ a * ‖F c - F zs‖ + ‖c - zs‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * (stiff p * ‖c - zs‖) + ‖c - zs‖ := by gcongr
      _ = (1 + a * stiff p) * ‖zs - c‖ := by rw [norm_sub_rev]; ring

set_option maxHeartbeats 1000000 in
theorem attempt_success [FiniteDimensional ℝ p.E] (h : Regular F p.L) (hp : Valid p) (k : ℕ)
    (z Fz : p.E) {zs : p.E} (hzs : resid F (step p k) (anchor p k z) zs = 0)
    (hg : 0 < gval F k z Fz) {j : ℕ}
    (hlo : ‖zs - center p k z Fz‖ ≤ guess p k (gval F k z Fz) j)
    (hhi : guess p k (gval F k z Fz) j ≤ 2 * ‖zs - center p k z Fz‖)
    (hball : ∀ y ∈ Metric.closedBall zs ‖zs - center p k z Fz‖, ‖fderiv ℝ F y‖ ≤ stiff p) :
    acc F k z Fz j := by
  set a := step p k with ha_def
  set w := anchor p k z
  set c := center p k z Fz
  set g := gval F k z Fz
  set R := ‖zs - c‖
  set ρ := guess p k g j
  set η := ratio p k g j
  set M := stages p k g j
  set Q := η * ρ
  set bs := fun i => stageParam p k g j i
  set zt := fun i => stageTarget (F := F) k z Fz g j i
  have ha := step_pos hp k
  have hL := hp.L
  have hη := ratio_pos hp k hg j
  have hη1 : η ≤ 1 := ratio_le_one k g j
  have hρ := guess_pos hp k hg j
  have hQ0 : 0 ≤ Q := by positivity
  have hQρ : Q ≤ ρ := by
    have := mul_le_mul_of_nonneg_right hη1 hρ.le; simpa [Q] using this
  have hsmall : 2500 * a * p.L * Q ^ 2 ≤ 1 := by
    have hm := ratio_mul hp k hg j
    have hs : Real.sqrt (a * p.L) ^ 2 = a * p.L := Real.sq_sqrt (by positivity)
    have hpos : 0 ≤ η * (50 * Real.sqrt (a * p.L) * ρ) := by positivity
    have := pow_le_one₀ hpos hm (n := 2)
    calc 2500 * a * p.L * Q ^ 2 = (η * (50 * Real.sqrt (a * p.L) * ρ)) ^ 2 := by
          rw [show (η * (50 * Real.sqrt (a * p.L) * ρ)) ^ 2 =
            2500 * Real.sqrt (a * p.L) ^ 2 * (η * ρ) ^ 2 by ring, hs]
          have hQdef : Q = η * ρ := rfl
          rw [hQdef]; ring
      _ ≤ 1 := this
  have hwz : a • F zs + zs = w := by simp only [resid, sub_eq_zero] at hzs; exact hzs
  have htarget : ∀ b, target p k z Fz b = c + (b / a) • (w - c) := fun b => rfl
  have hfull : c + (a / a) • (w - c) = w := by rw [div_self ha.ne', one_smul]; abel
  have hzs' : resid F a (c + (a / a) • (w - c)) zs = 0 := by rw [hfull]; exact hzs
  have hbs_pos : ∀ i, 0 < bs i := fun i => stageParam_pos hp k hg j i
  have hbs_le : ∀ i, bs i ≤ a := fun i => stageParam_le k g j i
  have hzt : ∀ i, resid F (bs i) (c + (bs i / a) • (w - c)) (zt i) = 0 := fun i => by
    have := stageTarget_spec (F := F) h hp k z Fz hg j i
    rwa [htarget] at this
  have hpath : ∀ i, ‖zt i - c‖ ≤ R := fun i =>
    path_mono h.mono (hbs_pos i) (hbs_le i) (hzt i) hzs'
  have hR_ρ : R ≤ ρ := hlo
  have hstep : ∀ i, ‖zt (i + 1) - zt i‖ ≤ Q ∧
      nq F (bs (i + 1)) (zt (i + 1)) (zt (i + 1) - zt i) ≤ 5 * Q ^ 2 := by
    intro i
    have hb1 := hbs_pos i
    have hmono := stageParam_mono hp k hg j i
    have hsucc := stageParam_succ_le hp k hg j i
    have heq := path_step (F := F) (hbs_pos (i + 1)) (hzt i) (hzt (i + 1))
    have hfrac : 0 ≤ 1 - bs i / bs (i + 1) ∧ 1 - bs i / bs (i + 1) ≤ η := by
      have hb2 := hbs_pos (i + 1)
      constructor
      · rw [sub_nonneg, div_le_one hb2]; exact hmono
      · have : bs i / bs (i + 1) ≥ 1 - η := by
          rw [ge_iff_le, le_div_iff₀ hb2]; nlinarith
        linarith
    have hq : ‖(1 - bs i / bs (i + 1)) • (zt (i + 1) - c)‖ ≤ Q := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfrac.1]
      calc (1 - bs i / bs (i + 1)) * ‖zt (i + 1) - c‖ ≤ η * R :=
            mul_le_mul hfrac.2 (hpath (i + 1)) (norm_nonneg _) hη.le
        _ ≤ η * ρ := by gcongr
    have h2b : bs (i + 1) ≤ 2 * bs i := by nlinarith
    have hsm : 22 * bs (i + 1) * p.L * Q ^ 2 ≤ 1 := by
      nlinarith [hbs_le (i + 1), mul_nonneg hL.le (sq_nonneg Q)]
    exact h.step_bound hb1 hmono h2b heq hq hsm
  have hfirst : nq F (bs 0) (zt 0) (c - zt 0) ≤ 5 * Q ^ 2 := by
    have heq := first_step (F := F) ha (hzt 0)
    have hb0 : bs 0 = start p k g j := stageParam_zero k g j
    have hq : ‖-((bs 0 / a) • (a • F c + c - w))‖ ≤ Q := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (hbs_pos 0) ha)]
      have := start_scaled hp k hg j
      rw [← hb0] at this
      exact this
    have hsm : 22 * bs 0 * p.L * Q ^ 2 ≤ 1 := by
      nlinarith [hbs_le 0, mul_nonneg hL.le (sq_nonneg Q)]
    have := (h.step_bound (hbs_pos 0) le_rfl (by linarith [hbs_pos 0]) heq hq hsm).2
    rwa [show c - zt 0 = -(zt 0 - c) by abel, nq_neg]
  have hsm169 : ∀ i, 169 * bs i * p.L * (12 * Q ^ 2) ≤ 1 := fun i => by
    nlinarith [hbs_le i, mul_nonneg hL.le (sq_nonneg Q)]
  have hblock : ∀ i, i < M + 1 →
      nq F (bs i) (zt i) (innerSeq F k z Fz j (3 * i) - zt i) ≤ 12 * Q ^ 2 →
      nq F (bs i) (zt i) (innerSeq F k z Fz j (3 * i + 3) - zt i) ≤ 12 * Q ^ 2 / 4 ^ 3 := by
    intro i hi h0
    have := newton_block h (hbs_pos i).le (hzt i) (hsm169 i)
      (fun n => innerSeq F k z Fz j (3 * i + n)) 3
      (fun n hn => by
        have := innerSeq_stage (F := F) k z Fz j i n hn hi
        simpa [htarget, add_assoc] using this) h0 3 le_rfl
    simpa using this
  have hinv : ∀ i, i ≤ M →
      nq F (bs i) (zt i) (innerSeq F k z Fz j (3 * i) - zt i) ≤ 12 * Q ^ 2 := by
    intro i
    induction i with
    | zero => intro _; simpa [innerSeq] using hfirst.trans (by nlinarith [sq_nonneg Q])
    | succ i ih =>
      intro hi
      have hprev := hblock i (by omega) (ih (by omega))
      obtain ⟨hd, hnq⟩ := hstep i
      set u := innerSeq F k z Fz j (3 * i + 3) - zt i
      have hsplit : innerSeq F k z Fz j (3 * (i + 1)) - zt (i + 1) = u + (zt i - zt (i + 1)) := by
        simp only [u, show 3 * (i + 1) = 3 * i + 3 by ring]; abel
      rw [hsplit]
      have hb' := (hbs_pos (i + 1)).le
      refine (h.nq_add_le hb' _ _ _).trans ?_
      have hcmp : 6 * bs (i + 1) * p.L * ‖zt (i + 1) - zt i‖ ^ 2 ≤ 1 := by
        have : ‖zt (i + 1) - zt i‖ ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
        nlinarith [hbs_le (i + 1), mul_nonneg hL.le (sq_nonneg Q),
          mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 6 * bs (i + 1) * p.L)]
      have hu1 := (h.compare hb' (zt i) (zt (i + 1)) u hcmp).1
      have hmono := stageParam_mono hp k hg j i
      have hsucc := stageParam_succ_le hp k hg j i
      have hu2 := (h.nq_mono hmono (by nlinarith) (zt i) u).2
      have hneg : nq F (bs (i + 1)) (zt (i + 1)) (zt i - zt (i + 1)) ≤ 5 * Q ^ 2 := by
        rw [show zt i - zt (i + 1) = -(zt (i + 1) - zt i) by abel, nq_neg]; exact hnq
      norm_num at hprev
      nlinarith
  have hlast : bs M = a := stageParam_last hp k hg j
  have hztM : zt M = zs := by
    have h1 := hzt M
    rw [hlast] at h1
    exact h.resid_unique ha h1 hzs'
  have hend := hblock M (by omega) (hinv M le_rfl)
  rw [hlast, hztM] at hend
  set Kc := extra p k
  have htail := newton_block h ha.le hzs' (Q := Q / 8)
    (by nlinarith [mul_nonneg hL.le (sq_nonneg Q)])
    (fun n => innerSeq F k z Fz j (3 * (M + 1) + n)) Kc
    (fun n _ => innerSeq_tail (F := F) k z Fz j n)
    (by simp only [add_zero]; rw [show 3 * (M + 1) = 3 * M + 3 by ring]; nlinarith [hend])
    Kc le_rfl
  have hy : attemptPoint F k z Fz j = innerSeq F k z Fz j (3 * (M + 1) + Kc) := rfl
  set y := attemptPoint F k z Fz j
  rw [← hy] at htail
  have hδ2 : ‖y - zs‖ ^ 2 ≤ 12 * (Q / 8) ^ 2 / 4 ^ Kc :=
    (h.nq_ge ha.le zs (y - zs)).trans htail
  have hK := pow_four_extra (⌈a * stiff p⌉₊ + 2)
  have hceil : a * stiff p ≤ (⌈a * stiff p⌉₊ : ℝ) := Nat.le_ceil _
  have hKc : (2 : ℝ) ^ Kc ≥ 16 * (a * stiff p + 3) := by
    have : (2 : ℝ) ^ Kc = 2 ^ (Nat.log2 (⌈a * stiff p⌉₊ + 2) + 5) := rfl
    rw [this]; push_cast at hK; linarith
  have hs0 := stiff_nonneg hp
  have hR0 : 0 < R := by
    have hb := (h.bracket hp k z Fz hzs hball).2
    have hd := one_le_denom hp k
    by_contra hR
    have h1 : R ≤ 0 := not_lt.mp hR
    have h2 : (1 + a * stiff p) * R ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h1
    linarith
  have h4 : (4 : ℝ) ^ Kc = (2 ^ Kc) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hδ : ‖y - zs‖ ≤ R / (16 * (a * stiff p + 3)) := by
    have hpos2 : (0 : ℝ) < 2 ^ Kc := by positivity
    have hQ2R : Q ≤ 2 * R := hQρ.trans hhi
    have hsq : ‖y - zs‖ ^ 2 ≤ (R / (16 * (a * stiff p + 3))) ^ 2 := by
      refine hδ2.trans ?_
      rw [h4, div_le_iff₀ (by positivity)]
      have hden : 0 < 16 * (a * stiff p + 3) := by positivity
      have hpw : (16 * (a * stiff p + 3)) ^ 2 ≤ (2 ^ Kc) ^ 2 :=
        pow_le_pow_left₀ hden.le hKc 2
      have e : (R / (16 * (a * stiff p + 3))) ^ 2 * (16 * (a * stiff p + 3)) ^ 2 = R ^ 2 := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hden.ne')]
      have hQ2 := pow_le_pow_left₀ hQ0 hQ2R 2
      calc 12 * (Q / 8) ^ 2 ≤ R ^ 2 := by nlinarith
        _ = (R / (16 * (a * stiff p + 3))) ^ 2 * (16 * (a * stiff p + 3)) ^ 2 := e.symm
        _ ≤ (R / (16 * (a * stiff p + 3))) ^ 2 * (2 ^ Kc) ^ 2 :=
            mul_le_mul_of_nonneg_left hpw (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq
  have hyball : y ∈ Metric.closedBall zs R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine hδ.trans (div_le_self hR0.le (by nlinarith))
  have hzball : zs ∈ Metric.closedBall zs R := Metric.mem_closedBall_self (norm_nonneg _)
  have hlip := h.lipschitz_on_ball hball hyball hzball
  have hres : ‖a • F y + y - w‖ ≤ (1 + a * stiff p) * ‖y - zs‖ := by
    rw [← hwz]
    have : a • F y + y - (a • F zs + zs) = a • (F y - F zs) + (y - zs) := by
      simp only [smul_sub]; abel
    rw [this]
    calc ‖a • (F y - F zs) + (y - zs)‖ ≤ a * ‖F y - F zs‖ + ‖y - zs‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * (stiff p * ‖y - zs‖) + ‖y - zs‖ := by gcongr
      _ = (1 + a * stiff p) * ‖y - zs‖ := by ring
  have hyc : R - ‖y - zs‖ ≤ ‖y - c‖ := by
    have := norm_sub_norm_le (zs - c) (zs - y)
    rw [show zs - c - (zs - y) = y - c by abel, norm_sub_rev zs y] at this
    linarith
  unfold acc
  change ‖a • F y + y - w‖ ≤ ‖y - c‖ / 2
  have hfin : (1 + a * stiff p) * ‖y - zs‖ ≤ (R - ‖y - zs‖) / 2 := by
    have hden : 0 < 16 * (a * stiff p + 3) := by positivity
    have hm := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 3 / 2 + a * stiff p)
    have : (3 / 2 + a * stiff p) * (R / (16 * (a * stiff p + 3))) ≤ R / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
      nlinarith [mul_nonneg (mul_nonneg ha.le hs0) hR0.le]
    linarith
  linarith

end

end LongTails.Proofs.HomotopyNewtonInner
