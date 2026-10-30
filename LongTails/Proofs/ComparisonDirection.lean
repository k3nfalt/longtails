import LongTails.Algorithms.ComparisonOrth
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace OracleTemplate.ComparisonOrth

open QueryPlan

noncomputable def cmp {n : ℕ} (f : Pt n → ℝ) (q : Pt n × Pt n) : Bool := decide (f q.1 ≤ f q.2)

lemma eval_iteratePlan {Q R U : Type} (g : Q → R) (c : ℕ) (m : ℕ)
    (step : U → QueryPlan Q R U c) (u : U) :
    eval g (iteratePlan c m step u) = (fun v => eval g (step v))^[m] u := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih =>
      simp only [iteratePlan, eval_bind, ih, Function.iterate_succ_apply]

lemma eval_comparePlan {n : ℕ} (g : Pt n × Pt n → Bool) (x y : Pt n) :
    eval g (comparePlan x y) = g (x, y) := rfl

lemma nrm_sub_le {n : ℕ} (a b : Pt n) (hb : b ≠ 0) :
    ‖nrm a - nrm b‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  rw [le_div_iff₀ hbpos]
  by_cases ha : a = 0
  · subst ha
    simp only [nrm, norm_zero, inv_zero, zero_smul, zero_sub, norm_neg, norm_smul,
      norm_inv, norm_norm]
    rw [inv_mul_cancel₀ hbpos.ne']
    nlinarith
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hsm : ‖b‖ • (nrm a - nrm b) = (‖b‖ / ‖a‖) • a - b := by
    simp only [nrm, smul_sub, smul_smul]
    rw [mul_inv_cancel₀ hbpos.ne', one_smul, div_eq_mul_inv]
  have h1 : ‖nrm a - nrm b‖ * ‖b‖ = ‖(‖b‖ / ‖a‖) • a - b‖ := by
    rw [← hsm, norm_smul, Real.norm_of_nonneg (norm_nonneg _), mul_comm]
  rw [h1]
  calc ‖(‖b‖ / ‖a‖) • a - b‖ ≤ ‖(‖b‖ / ‖a‖) • a - a‖ + ‖a - b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |‖b‖ - ‖a‖| + ‖a - b‖ := by
        congr 1
        rw [show (‖b‖ / ‖a‖) • a - a = ((‖b‖ - ‖a‖) / ‖a‖) • a by
          rw [sub_div, div_self hapos.ne', sub_smul, one_smul]]
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hapos, div_mul_cancel₀ _ hapos.ne']
    _ ≤ ‖a - b‖ + ‖a - b‖ := by
        gcongr
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le a b
    _ = 2 * ‖a - b‖ := by ring

section Probe

variable {n : ℕ} {f : Pt n → ℝ} {L : ℝ}

lemma probe_true (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x z : Pt n} {h : ℝ} (hh : 0 < h) (hle : f (x - h • z) ≤ f (x + h • z)) :
    -(L * h * ‖z‖ ^ 2 / 4) ≤ ⟪gradient f x, z⟫ := by
  have hup := Gradient.smooth_upper_bound hg hlip x (x + h • z)
  have hlo := Gradient.convex_support hc hg x (x - h • z)
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hh] at hup
  rw [show x - h • z - x = -(h • z) by abel, inner_neg_right, inner_smul_right] at hlo
  have : 2 * h * ⟪gradient f x, z⟫ ≥ -(L / 2 * (h * ‖z‖) ^ 2) := by linarith
  have h4 : 0 < 2 * h := by linarith
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_left hcon h4
  nlinarith

lemma probe_false (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x z : Pt n} {h : ℝ} (hh : 0 < h) (hlt : ¬ f (x - h • z) ≤ f (x + h • z)) :
    ⟪gradient f x, z⟫ ≤ L * h * ‖z‖ ^ 2 / 4 := by
  push Not at hlt
  have := probe_true (z := -z) hc hg hlip hh (by
    rw [smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]; exact hlt.le)
  rw [inner_neg_right, norm_neg] at this
  linarith

end Probe

lemma norm_unitVec_le (n i : ℕ) : ‖unitVec n i‖ ≤ 1 := by
  unfold unitVec
  split_ifs
  · simp
  · simp

lemma inner_unitVec {n : ℕ} (g : Pt n) (i : ℕ) :
    ⟪g, unitVec n i⟫ = if hi : i < n then g ⟨i, hi⟩ else 0 := by
  unfold unitVec
  split_ifs <;> simp [EuclideanSpace.inner_single_right]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

lemma eval_probePlan {n : ℕ} (f : Pt n → ℝ) (x : Pt n) (h : ℝ) (z : Pt n) :
    eval (cmp f) (probePlan x h z) = decide (f (x - h • z) ≤ f (x + h • z)) := rfl

lemma eval_signPlan {n : ℕ} (f : Pt n → ℝ) (x : Pt n) (h : ℝ) :
    eval (cmp f) (signPlan x h) =
      List.ofFn (fun i : Fin n => decide (f (x - h • unitVec n i) ≤ f (x + h • unitVec n i))) := by
  simp only [signPlan, eval_traverse, eval_probePlan]

lemma listSign_signPlan {n : ℕ} (f : Pt n → ℝ) (x : Pt n) (h : ℝ) (i : ℕ) :
    listSign (eval (cmp f) (signPlan x h)) i =
      if i < n then sgn (decide (f (x - h • unitVec n i) ≤ f (x + h • unitVec n i))) else 1 := by
  rw [eval_signPlan, listSign, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> simp [sgn]

section Direction

variable {n : ℕ} {f : Pt n → ℝ} {L : ℝ}
  (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
  (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
include hc hg hlip

lemma probe_dir {x z : Pt n} {h : ℝ} (hh : 0 < h) (hL : 0 ≤ L) {B : ℝ} (hz : ‖z‖ ≤ B) :
    (f (x - h • z) ≤ f (x + h • z) → -(L * h * B ^ 2 / 4) ≤ ⟪gradient f x, z⟫) ∧
      (¬ f (x - h • z) ≤ f (x + h • z) → ⟪gradient f x, z⟫ ≤ L * h * B ^ 2 / 4) := by
  have hB : ‖z‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hm : L * h * ‖z‖ ^ 2 / 4 ≤ L * h * B ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_left hB (mul_nonneg hL hh.le)
    linarith
  constructor
  · intro hle
    have := probe_true hc hg hlip hh hle
    linarith
  · intro hlt
    have := probe_false hc hg hlip hh hlt
    linarith

lemma sign_good (x : Pt n) {h : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (i : ℕ) :
    |⟪gradient f x, unitVec n i⟫| - L * h / 2 ≤
      listSign (eval (cmp f) (signPlan x h)) i * ⟪gradient f x, unitVec n i⟫ := by
  have hLh : 0 ≤ L * h := mul_nonneg hL hh.le
  rw [listSign_signPlan]
  split_ifs with hi
  · have hp := probe_dir hc hg hlip (x := x) hh hL (norm_unitVec_le n i)
    set γ := ⟪gradient f x, unitVec n i⟫
    by_cases hb : f (x - h • unitVec n i) ≤ f (x + h • unitVec n i)
    · simp only [hb, decide_true, sgn, ite_true, one_mul]
      have := hp.1 hb
      rcases le_or_gt 0 γ with h0 | h0
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_of_neg h0]; linarith
    · simp only [hb, decide_false, sgn, Bool.false_eq_true, ite_false, neg_one_mul]
      have := hp.2 hb
      rcases le_or_gt 0 γ with h0 | h0
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_of_neg h0]; linarith
  · have : unitVec n i = 0 := by simp [unitVec, hi]
    rw [this, inner_zero_right]
    simp only [abs_zero, mul_zero]
    linarith

lemma champion_spec (x : Pt n) {h : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (hn : 1 ≤ n) :
    let Ls := eval (cmp f) (signPlan x h)
    let c := (eval (cmp f) (championPlan x h Ls)).1
    c < n ∧ ∀ i < n, listSign Ls i * ⟪gradient f x, unitVec n i⟫ ≤
      listSign Ls c * ⟪gradient f x, unitVec n c⟫ + n * (L * h) := by
  intro Ls c
  set S := fun i => listSign Ls i
  set γ := fun i => ⟪gradient f x, unitVec n i⟫
  have hstep : ∀ st : ℕ × ℕ, eval (cmp f) (championStep x h Ls st) =
      if f (x - h • (listSign Ls st.2 • unitVec n st.2 - listSign Ls st.1 • unitVec n st.1)) ≤
          f (x + h • (listSign Ls st.2 • unitVec n st.2 - listSign Ls st.1 • unitVec n st.1))
      then (st.2, st.2 + 1) else (st.1, st.2 + 1) := by
    intro st
    simp only [championStep, eval_map, eval_probePlan]
    by_cases hb : f (x - h • (listSign Ls st.2 • unitVec n st.2 - listSign Ls st.1 • unitVec n st.1)) ≤
          f (x + h • (listSign Ls st.2 • unitVec n st.2 - listSign Ls st.1 • unitVec n st.1))
    · simp [hb]
    · simp [hb]
  have hznorm : ∀ i j : ℕ, ‖S i • unitVec n i - S j • unitVec n j‖ ≤ 2 := by
    intro i j
    calc ‖S i • unitVec n i - S j • unitVec n j‖
        ≤ ‖S i • unitVec n i‖ + ‖S j • unitVec n j‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs]
            simp only [S, listSign, abs_sgn, one_mul]; exact norm_unitVec_le n i
          · rw [norm_smul, Real.norm_eq_abs]
            simp only [S, listSign, abs_sgn, one_mul]; exact norm_unitVec_le n j
      _ = 2 := by norm_num
  have hinner : ∀ i j : ℕ, ⟪gradient f x, S i • unitVec n i - S j • unitVec n j⟫ =
      S i * γ i - S j * γ j := by
    intro i j
    simp only [inner_sub_right, inner_smul_right, γ]
  have key : ∀ k, ((fun st => eval (cmp f) (championStep x h Ls st))^[k] (0, 0)).2 = k ∧
      (((fun st => eval (cmp f) (championStep x h Ls st))^[k] (0, 0)).1 = 0 ∨
        ((fun st => eval (cmp f) (championStep x h Ls st))^[k] (0, 0)).1 < k) ∧
      ∀ i < k, S i * γ i ≤
        S ((fun st => eval (cmp f) (championStep x h Ls st))^[k] (0, 0)).1 *
          γ ((fun st => eval (cmp f) (championStep x h Ls st))^[k] (0, 0)).1 + k * (L * h) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        obtain ⟨h2, h1, h3⟩ := ih
        set st := (fun st => eval (cmp f) (championStep x h Ls st))^[k] (0, 0)
        rw [hstep st]
        have hp := probe_dir hc hg hlip (x := x) hh hL (hznorm st.2 st.1)
        rw [hinner, h2] at hp
        have hLh : 0 ≤ L * h := mul_nonneg hL hh.le
        split_ifs with hb
        · have := hp.1 (by rw [← h2]; exact hb)
          refine ⟨by simp [h2], Or.inr (by simp [h2]), ?_⟩
          intro i hi
          dsimp only
          rw [h2]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · have := h3 i hi
            push_cast
            nlinarith
          · subst hi
            push_cast
            nlinarith
        · have := hp.2 (by rw [← h2]; exact hb)
          refine ⟨by simp [h2], h1.imp_right (fun h => Nat.lt_succ_of_lt h), ?_⟩
          intro i hi
          dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · have := h3 i hi
            push_cast
            nlinarith
          · subst hi
            push_cast
            nlinarith
  have hres : eval (cmp f) (championPlan x h Ls) =
      (fun st => eval (cmp f) (championStep x h Ls st))^[n] (0, 0) := by
    simp only [championPlan, eval_iteratePlan]
  obtain ⟨-, hc1, hc2⟩ := key n
  refine ⟨?_, ?_⟩
  · show (eval (cmp f) (championPlan x h Ls)).1 < n
    rw [hres]
    rcases hc1 with h0 | h0
    · rw [h0]; omega
    · exact h0
  · intro i hi
    have := hc2 i hi
    simp only [c, hres]
    exact this

end Direction

lemma bisect_spec {w β : ℝ} (D : ℝ → Bool) (B : ℝ × ℝ → ℝ × ℝ)
    (hB : ∀ I : ℝ × ℝ, B I = if D ((I.1 + I.2) / 2) = true then ((I.1 + I.2) / 2, I.2)
      else (I.1, (I.1 + I.2) / 2))
    (hβ : 0 ≤ β) (hw : |w| ≤ 2)
    (hD : ∀ t, -2 ≤ t → t ≤ 2 → (D t = true → t - β ≤ w) ∧ (D t = false → w ≤ t + β))
    (m : ℕ) :
    |((B^[m] (-2, 2)).1 + (B^[m] (-2, 2)).2) / 2 - w| ≤ 2 / 2 ^ m + β := by
  have key : ∀ k, -2 ≤ (B^[k] (-2, 2)).1 ∧ (B^[k] (-2, 2)).1 ≤ (B^[k] (-2, 2)).2 ∧
      (B^[k] (-2, 2)).2 ≤ 2 ∧ (B^[k] (-2, 2)).2 - (B^[k] (-2, 2)).1 = 4 / 2 ^ k ∧
      (B^[k] (-2, 2)).1 - β ≤ w ∧ w ≤ (B^[k] (-2, 2)).2 + β := by
    intro k
    induction k with
    | zero =>
        simp only [Function.iterate_zero, id_eq, pow_zero]
        rw [abs_le] at hw
        refine ⟨le_rfl, by norm_num, le_rfl, by norm_num, by linarith, by linarith⟩
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
        set I := B^[k] (-2, 2)
        have ht1 : -2 ≤ (I.1 + I.2) / 2 := by linarith
        have ht2 : (I.1 + I.2) / 2 ≤ 2 := by linarith
        have hD' := hD _ ht1 ht2
        have hpow : (4 : ℝ) / 2 ^ (k + 1) = (4 / 2 ^ k) / 2 := by
          rw [pow_succ]; field_simp
        rw [hB]
        cases hDt : D ((I.1 + I.2) / 2)
        · simp only [Bool.false_eq_true, ite_false]
          have := hD'.2 hDt
          refine ⟨h1, by linarith, by linarith, by rw [hpow]; linarith, h5, this⟩
        · simp only [ite_true]
          have := hD'.1 hDt
          refine ⟨ht1, by linarith, h3, by rw [hpow]; linarith, this, h6⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := key m
  have h7 : (4 : ℝ) / 2 ^ m = 2 * (2 / 2 ^ m) := by ring
  rw [abs_le]
  constructor <;> linarith

lemma exists_big_coord {n : ℕ} (hn : 1 ≤ n) (g : Pt n) :
    ∃ i < n, ‖g‖ / Real.sqrt n ≤ |⟪g, unitVec n i⟫| := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ _i : Fin n, ‖g‖ ^ 2 / n ≤ ∑ i : Fin n, (g i) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ hnpos.ne', EuclideanSpace.real_norm_sq_eq]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨i.1, i.2, ?_⟩
  rw [inner_unitVec, dite_eq_left_of_eq_true (eq_true i.2)]
  have h1 : Real.sqrt (‖g‖ ^ 2 / n) ≤ Real.sqrt ((g i) ^ 2) := Real.sqrt_le_sqrt hi
  rwa [Real.sqrt_div' _ hnpos.le, Real.sqrt_sq (norm_nonneg g), Real.sqrt_sq_eq_abs] at h1

section Accuracy

variable {n : ℕ} {f : Pt n → ℝ} {L : ℝ}
  (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
  (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
include hc hg hlip

theorem dir_accuracy (x : Pt n) {h : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (hn : 1 ≤ n) (m : ℕ)
    (hg0 : 0 < ‖gradient f x‖)
    (hbig : 2 * (n + 1) * (L * h) * Real.sqrt n ≤ ‖gradient f x‖) :
    ‖eval (cmp f) (dirPlan x h m) - nrm (gradient f x)‖ ≤
      2 * Real.sqrt n * (2 / 2 ^ m + 9 * (L * h) * Real.sqrt n / (2 * ‖gradient f x‖)) := by
  set g := gradient f x with hgdef
  set Ls := eval (cmp f) (signPlan x h) with hLs
  obtain ⟨hcn, hcmax⟩ := champion_spec hc hg hlip x hh hL hn
  set c := (eval (cmp f) (championPlan x h Ls)).1 with hcdef
  set σ := listSign Ls c with hσ
  set γ := fun i => ⟪g, unitVec n i⟫ with hγ
  set a := σ * γ c with ha
  have hLh : 0 ≤ L * h := mul_nonneg hL hh.le
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hσ1 : |σ| = 1 := by simp only [hσ, listSign, abs_sgn]
  have hσσ : σ * σ = 1 := by simp only [hσ, listSign, sgn_mul_self]
  have hsign := fun i => sign_good hc hg hlip x hh hL i
  obtain ⟨i0, hi0, hbig0⟩ := exists_big_coord hn g
  have hsmall : (n + 1) * (L * h) ≤ ‖g‖ / (2 * Real.sqrt n) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have ha_lb : ‖g‖ / (2 * Real.sqrt n) ≤ a := by
    have h1 := hcmax i0 hi0
    have h2 := hsign i0
    have h3 : ‖g‖ / Real.sqrt n = 2 * (‖g‖ / (2 * Real.sqrt n)) := by field_simp
    nlinarith
  have ha_pos : 0 < a := lt_of_lt_of_le (by positivity) ha_lb
  have hγ_le : ∀ i, |γ i| ≤ 2 * a := by
    intro i
    by_cases hi : i < n
    · have h1 := hcmax i hi
      have h2 := hsign i
      nlinarith
    · have : γ i = 0 := by simp only [hγ, inner_unitVec, dite_eq_right_iff.mpr (fun h => absurd h hi)]
      rw [this, abs_zero]; linarith
  set β := 9 * (L * h) / (4 * a) with hβ
  have hβ0 : 0 ≤ β := by positivity
  set mid := fun i : ℕ => eval (cmp f) (ratioPlan x h σ c i m) with hmid
  have hmid_err : ∀ i, |mid i - σ * γ i / a| ≤ 2 / 2 ^ m + β := by
    intro i
    have hw : |σ * γ i / a| ≤ 2 := by
      rw [abs_div, abs_mul, hσ1, one_mul, abs_of_pos ha_pos, div_le_iff₀ ha_pos]
      exact hγ_le i
    have hD : ∀ t : ℝ, -2 ≤ t → t ≤ 2 →
        (decide (f (x - h • (σ • (unitVec n i - t • unitVec n c))) ≤
            f (x + h • (σ • (unitVec n i - t • unitVec n c)))) = true →
          t - β ≤ σ * γ i / a) ∧
        (decide (f (x - h • (σ • (unitVec n i - t • unitVec n c))) ≤
            f (x + h • (σ • (unitVec n i - t • unitVec n c)))) = false →
          σ * γ i / a ≤ t + β) := by
      intro t ht1 ht2
      have hz : ‖σ • (unitVec n i - t • unitVec n c)‖ ≤ 3 := by
        rw [norm_smul, Real.norm_eq_abs, hσ1, one_mul]
        calc ‖unitVec n i - t • unitVec n c‖ ≤ ‖unitVec n i‖ + ‖t • unitVec n c‖ :=
              norm_sub_le _ _
          _ ≤ 1 + 2 * 1 := by
              gcongr
              · exact norm_unitVec_le n i
              · rw [norm_smul, Real.norm_eq_abs]
                exact mul_le_mul (abs_le.mpr ⟨by linarith, ht2⟩) (norm_unitVec_le n c)
                  (norm_nonneg _) (by norm_num)
          _ = 3 := by norm_num
      have hp := probe_dir hc hg hlip (x := x) hh hL hz
      have hin : ⟪g, σ • (unitVec n i - t • unitVec n c)⟫ = σ * γ i - t * a := by
        simp only [inner_smul_right, inner_sub_right, hγ, ha]; ring
      rw [hin] at hp
      have e1 : σ * γ i / a - t = (σ * γ i - t * a) / a := by field_simp
      have e2 : β = 9 * (L * h) / 4 / a := by rw [hβ]; ring
      constructor
      · intro hb
        have := hp.1 (of_decide_eq_true hb)
        have : -(9 * (L * h) / 4) / a ≤ (σ * γ i - t * a) / a :=
          div_le_div_of_nonneg_right (by linarith) ha_pos.le
        rw [neg_div] at this
        linarith
      · intro hb
        have := hp.2 (of_decide_eq_false hb)
        have : (σ * γ i - t * a) / a ≤ 9 * (L * h) / 4 / a :=
          div_le_div_of_nonneg_right (by linarith) ha_pos.le
        linarith
    have hev : mid i = (((fun I => eval (cmp f) (bisectStep x h σ c i I))^[m] (-2, 2)).1 +
        ((fun I => eval (cmp f) (bisectStep x h σ c i I))^[m] (-2, 2)).2) / 2 := by
      simp only [hmid, ratioPlan, eval_map, eval_iteratePlan]
    rw [hev]
    refine bisect_spec (fun t => decide (f (x - h • (σ • (unitVec n i - t • unitVec n c))) ≤
      f (x + h • (σ • (unitVec n i - t • unitVec n c))))) _ ?_ hβ0 hw hD m
    intro I
    simp only [bisectStep, eval_map, eval_probePlan]
    rfl
  set what := listVec n (List.ofFn (fun i : Fin n => mid i)) with hwhat
  set wvec := (σ / a) • g with hwvec
  have hcoord : ∀ j : Fin n, what j - wvec j = mid j - σ * γ j / a := by
    intro j
    simp only [hwhat, listVec, PiLp.toLp_apply, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, j.2, ↓reduceDIte, Option.getD_some, hwvec, PiLp.smul_apply,
      smul_eq_mul, hγ, inner_unitVec, Fin.eta]
    ring
  have hdiff : ‖what - wvec‖ ≤ Real.sqrt n * (2 / 2 ^ m + β) := by
    have hsq2 : ‖what - wvec‖ ^ 2 ≤ n * (2 / 2 ^ m + β) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ j : Fin n, ((what - wvec) j) ^ 2 ≤ ∑ _j : Fin n, (2 / 2 ^ m + β) ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            rw [PiLp.sub_apply, hcoord j, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hmid_err j) 2
        _ = n * (2 / 2 ^ m + β) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpos : 0 ≤ Real.sqrt n * (2 / 2 ^ m + β) := by positivity
    calc ‖what - wvec‖ = Real.sqrt (‖what - wvec‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (n * (2 / 2 ^ m + β) ^ 2) := Real.sqrt_le_sqrt hsq2
      _ = Real.sqrt n * (2 / 2 ^ m + β) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hwvec_norm : 1 ≤ ‖wvec‖ := by
    have := PiLp.norm_apply_le wvec ⟨c, hcn⟩
    simp only [hwvec, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs] at this
    have hgc : g ⟨c, hcn⟩ = γ c := by simp only [hγ, inner_unitVec, hcn, ↓reduceDIte]
    rw [hgc, show σ / a * γ c = a / a by rw [ha]; ring, div_self ha_pos.ne', abs_one] at this
    exact this
  have hwvec0 : wvec ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwvec_norm; linarith
  have hnrm : σ • nrm wvec = nrm g := by
    simp only [nrm, hwvec, norm_smul, Real.norm_eq_abs, abs_div, hσ1, abs_of_pos ha_pos,
      smul_smul]
    congr 1
    field_simp
    nlinarith [hσσ]
  have hevdir : eval (cmp f) (dirPlan x h m) = σ • nrm what := by
    simp only [dirPlan, eval_bind, eval_map, eval_traverse]
    rfl
  rw [hevdir, ← hnrm, ← smul_sub, norm_smul, Real.norm_eq_abs, hσ1, one_mul]
  calc ‖nrm what - nrm wvec‖ ≤ 2 * ‖what - wvec‖ / ‖wvec‖ := nrm_sub_le _ _ hwvec0
    _ ≤ 2 * ‖what - wvec‖ := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg (what - wvec)]
    _ ≤ 2 * (Real.sqrt n * (2 / 2 ^ m + β)) := by linarith
    _ ≤ 2 * Real.sqrt n * (2 / 2 ^ m + 9 * (L * h) * Real.sqrt n / (2 * ‖g‖)) := by
        rw [mul_assoc]
        gcongr
        rw [hβ, div_le_div_iff₀ (by positivity) (by positivity)]
        have := ha_lb
        rw [div_le_iff₀ (by positivity)] at this
        nlinarith

end Accuracy

end OracleTemplate.ComparisonOrth
