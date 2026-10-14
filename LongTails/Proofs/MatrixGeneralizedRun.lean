import LongTails.Proofs.MatrixGeneralizedStep
import LongTails.Proofs.QueryPlan

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

noncomputable def stepAll (p : Params) (f : Point p.d → ℝ) (k : ℕ)
    (st : Point p.d × Point p.d × Point p.d) (s : Fin p.d → Bool) :
    Point p.d × Point p.d × Point p.d :=
  (xnext p f k (extrapolate p k st.1 st.2.1) s, znext p f k (extrapolate p k st.1 st.2.1) st.2.1 s,
    extrapolate p k st.2.2 st.2.1)

noncomputable def traj (p : Params) (f : Point p.d → ℝ) : (n : ℕ) → ℕ →
    Point p.d × Point p.d × Point p.d → (Fin n → Fin p.d → Bool) → Point p.d × Point p.d × Point p.d
  | 0, _, st, _ => st
  | n + 1, k, st, seeds => traj p f n (k + 1) (stepAll p f k st (seeds 0)) (fun j => seeds j.succ)

noncomputable def badInd (p : Params) (f : Point p.d → ℝ) (H : Point p.d →L[ℝ] Point p.d)
    (xstar : Point p.d) : (n : ℕ) → ℕ → Point p.d × Point p.d × Point p.d →
    (Fin n → Fin p.d → Bool) → ℝ
  | 0, k, st, _ => if 4 * p.R ^ 2 < potential p f H xstar k st.1 st.2.1 st.2.2 then 1 else 0
  | n + 1, k, st, seeds =>
      if 4 * p.R ^ 2 < potential p f H xstar k st.1 st.2.1 st.2.2 then 1
      else badInd p f H xstar n (k + 1) (stepAll p f k st (seeds 0)) (fun j => seeds j.succ)

noncomputable def errSum (p : Params) (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, 9 * p.R ^ 2 / (32 * 2 ^ (k + j))

section

variable {p : Params} {f : Point p.d → ℝ} {H : Point p.d →L[ℝ] Point p.d} {xstar : Point p.d}
  (I : Inst p f H xstar)
include I

lemma potential_nonneg (k : ℕ) (st : Point p.d × Point p.d × Point p.d) :
    0 ≤ potential p f H xstar k st.1 st.2.1 st.2.2 := by
  have hv := I.valid
  have hA := sched_pos hv k
  have hf0 : 0 ≤ f st.1 - f xstar := by
    have := I.min (Set.mem_univ st.1); simp only [Set.mem_ofPred_eq] at this; linarith
  unfold potential
  have := lagWeight_pos hv hA
  positivity

omit I in
lemma badInd_nonneg (n k : ℕ) (st : Point p.d × Point p.d × Point p.d)
    (seeds : Fin n → Fin p.d → Bool) : 0 ≤ badInd p f H xstar n k st seeds := by
  induction n generalizing k st with
  | zero => simp only [badInd]; split_ifs <;> norm_num
  | succ n ih => simp only [badInd]; split_ifs
                 · norm_num
                 · exact ih _ _ _

omit I in
lemma badInd_cases (n k : ℕ) (st : Point p.d × Point p.d × Point p.d)
    (seeds : Fin n → Fin p.d → Bool) :
    badInd p f H xstar n k st seeds = 0 ∨ badInd p f H xstar n k st seeds = 1 := by
  induction n generalizing k st with
  | zero => simp only [badInd]; split_ifs <;> simp
  | succ n ih =>
    simp only [badInd]
    split_ifs
    · right; rfl
    · exact ih _ _ _

lemma ville (n : ℕ) : ∀ (k : ℕ) (st : Point p.d × Point p.d × Point p.d),
    ‖st.2.2 - xstar‖ ≤ Real.sqrt 8 * p.R →
    (𝔼 seeds : Fin n → Fin p.d → Bool, badInd p f H xstar n k st seeds) ≤
      (potential p f H xstar k st.1 st.2.1 st.2.2 + errSum p k n) / (4 * p.R ^ 2) := by
  have hv := I.valid
  have hR := hv.R_pos
  have hR4 : 0 < 4 * p.R ^ 2 := by positivity
  have herr0 : ∀ k n, 0 ≤ errSum p k n := fun k n =>
    Finset.sum_nonneg fun j _ => by positivity
  induction n with
  | zero =>
    intro k st _
    simp only [badInd, Fintype.expect_const, errSum, Finset.range_zero, Finset.sum_empty, add_zero]
    split_ifs with h
    · rw [le_div_iff₀ hR4]; linarith
    · exact div_nonneg (potential_nonneg I k st) hR4.le
  | succ n ih =>
    intro k st hpt
    by_cases h : 4 * p.R ^ 2 < potential p f H xstar k st.1 st.2.1 st.2.2
    · have : ∀ seeds : Fin (n + 1) → Fin p.d → Bool, badInd p f H xstar (n + 1) k st seeds = 1 := by
        intro seeds; simp only [badInd]; rw [ite_eq_left h]
      simp only [this, Fintype.expect_const]
      rw [le_div_iff₀ hR4]
      have := herr0 k (n + 1)
      linarith
    · have hrec : ∀ seeds : Fin (n + 1) → Fin p.d → Bool, badInd p f H xstar (n + 1) k st seeds =
          badInd p f H xstar n (k + 1) (stepAll p f k st (seeds 0)) (fun j => seeds j.succ) := by
        intro seeds; simp only [badInd]; rw [ite_eq_right h]
      simp only [hrec]
      rw [NonconvexFiniteSum.expect_function_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hΨ : potential p f H xstar k st.1 st.2.1 st.2.2 ≤ 4 * p.R ^ 2 := not_lt.mp h
      obtain ⟨hghost, hstep⟩ := main_step I k st.1 st.2.1 st.2.2 hΨ hpt
      have h1 : ∀ s : Fin p.d → Bool,
          (𝔼 tail : Fin n → Fin p.d → Bool,
            badInd p f H xstar n (k + 1) (stepAll p f k st s) tail) ≤
          (potential p f H xstar (k + 1) (stepAll p f k st s).1 (stepAll p f k st s).2.1
            (stepAll p f k st s).2.2 + errSum p (k + 1) n) / (4 * p.R ^ 2) :=
        fun s => ih (k + 1) (stepAll p f k st s) hghost
      have h2 := Finset.expect_le_expect (s := Finset.univ) (fun s _ => h1 s)
      rw [← Finset.expect_div, Finset.expect_add_distrib, Fintype.expect_const] at h2
      have h3 : (𝔼 s : Fin p.d → Bool, potential p f H xstar (k + 1) (stepAll p f k st s).1
          (stepAll p f k st s).2.1 (stepAll p f k st s).2.2) ≤
          potential p f H xstar k st.1 st.2.1 st.2.2 + 9 * p.R ^ 2 / (32 * 2 ^ k) := hstep
      have hsum : 9 * p.R ^ 2 / (32 * 2 ^ k) + errSum p (k + 1) n = errSum p k (n + 1) := by
        unfold errSum
        rw [Finset.sum_range_succ']
        simp only [add_zero, Nat.add_succ, Nat.succ_add]
        ring_nf
      refine h2.trans ?_
      apply div_le_div_of_nonneg_right _ hR4.le
      linarith

lemma good_final (n : ℕ) : ∀ (k : ℕ) (st : Point p.d × Point p.d × Point p.d)
    (seeds : Fin n → Fin p.d → Bool), ‖st.2.2 - xstar‖ ≤ Real.sqrt 8 * p.R →
    badInd p f H xstar n k st seeds = 0 →
    potential p f H xstar (k + n) (traj p f n k st seeds).1 (traj p f n k st seeds).2.1
      (traj p f n k st seeds).2.2 ≤ 4 * p.R ^ 2 := by
  induction n with
  | zero =>
    intro k st seeds _ hb
    simp only [badInd] at hb
    split_ifs at hb with h
    · norm_num at hb
    · simpa [traj] using not_lt.mp h
  | succ n ih =>
    intro k st seeds hpt hb
    simp only [badInd] at hb
    split_ifs at hb with h
    · norm_num at hb
    · have hΨ := not_lt.mp h
      obtain ⟨hghost, _⟩ := main_step I k st.1 st.2.1 st.2.2 hΨ hpt
      have := ih (k + 1) (stepAll p f k st (seeds 0)) (fun j => seeds j.succ) hghost hb
      simp only [traj]
      rwa [show k + (n + 1) = k + 1 + n by ring]

lemma errSum_le (n : ℕ) : errSum p 0 n ≤ 9 * p.R ^ 2 / 16 := by
  have hR := (I.valid).R_pos
  unfold errSum
  have e : ∀ j ∈ Finset.range n, 9 * p.R ^ 2 / (32 * 2 ^ (0 + j)) =
      9 * p.R ^ 2 / 32 * (1 / 2) ^ j := by
    intro j _; rw [zero_add, one_div_pow]; field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have hg : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ 2 := by
    have := geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num) n
    rw [this]
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    have e2 : ((1 / 2 : ℝ) ^ n - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2) ^ n := by ring
    rw [e2]; linarith
  have : 0 ≤ 9 * p.R ^ 2 / 32 := by positivity
  nlinarith

lemma initial_potential :
    potential p f H xstar 0 p.x0 p.x0 p.x0 ≤ p.R ^ 2 := by
  have hv := I.valid
  have hR := hv.R_pos
  have hΔ := hv.Δ_pos
  unfold potential
  simp only [sub_self]
  have hh : hnorm H 0 = 0 := by simp [hnorm]
  rw [hh]
  have h1 : sched p 0 * (f p.x0 - f xstar) ≤ p.R ^ 2 / 2 := by
    have e : sched p 0 = p.R ^ 2 / (2 * p.Δ) := rfl
    rw [e]
    have hf0 : 0 ≤ f p.x0 - f xstar := by
      have := I.min (Set.mem_univ p.x0); simp only [Set.mem_ofPred_eq] at this; linarith
    calc p.R ^ 2 / (2 * p.Δ) * (f p.x0 - f xstar) ≤ p.R ^ 2 / (2 * p.Δ) * p.Δ :=
          mul_le_mul_of_nonneg_left I.gap (by positivity)
      _ = p.R ^ 2 / 2 := by field_simp
  have h2 : ‖p.x0 - xstar‖ ^ 2 / 2 ≤ p.R ^ 2 / 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) I.start 2
    linarith
  have : (0 : ℝ) ^ 2 = 0 := by norm_num
  nlinarith

lemma run_fail_prob :
    (𝔼 seeds : Fin (iterations p) → Fin p.d → Bool,
      if p.ε < f (traj p f (iterations p) 0 (p.x0, p.x0, p.x0) seeds).1 - f xstar then (1 : ℝ) else 0)
      ≤ 1 / 2 := by
  have hv := I.valid
  have hR := hv.R_pos
  have hε := hv.ε_pos
  set K := iterations p
  have hpt0 : ‖(p.x0, p.x0, p.x0).2.2 - xstar‖ ≤ Real.sqrt 8 * p.R := by
    have h8 : 1 ≤ Real.sqrt 8 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    calc ‖p.x0 - xstar‖ ≤ p.R := I.start
      _ ≤ Real.sqrt 8 * p.R := le_mul_of_one_le_left hR.le h8
  have hpoint : ∀ seeds : Fin K → Fin p.d → Bool,
      (if p.ε < f (traj p f K 0 (p.x0, p.x0, p.x0) seeds).1 - f xstar then (1 : ℝ) else 0) ≤
        badInd p f H xstar K 0 (p.x0, p.x0, p.x0) seeds := by
    intro seeds
    split_ifs with hfail
    · by_contra hb
      rw [not_le] at hb
      have hb0 : badInd p f H xstar K 0 (p.x0, p.x0, p.x0) seeds = 0 := by
        have h01 := badInd_cases (f := f) (H := H) (xstar := xstar) K 0 (p.x0, p.x0, p.x0) seeds
        rcases h01 with h | h
        · exact h
        · rw [h] at hb; norm_num at hb
      have hfin := good_final I K 0 (p.x0, p.x0, p.x0) seeds hpt0 hb0
      rw [zero_add] at hfin
      set xK := (traj p f K 0 (p.x0, p.x0, p.x0) seeds)
      have hA := sched_pos hv K
      have hf0 : 0 ≤ f xK.1 - f xstar := by
        have := I.min (Set.mem_univ xK.1); simp only [Set.mem_ofPred_eq] at this; linarith
      have hzpart : 0 ≤ ‖xK.2.1 - xstar‖ ^ 2 / 2 := by positivity
      have hlpart : 0 ≤ lagWeight p (sched p K) * hnorm H (xK.1 - xK.2.2) ^ 2 :=
        mul_nonneg (lagWeight_pos hv hA).le (sq_nonneg _)
      unfold potential at hfin
      have h1 : sched p K * (f xK.1 - f xstar) ≤ 4 * p.R ^ 2 := by linarith
      have hgrow := sched_iterations hv
      have h2 : f xK.1 - f xstar ≤ p.ε := by
        have h3 : sched p K * (f xK.1 - f xstar) ≤ sched p K * p.ε := by
          calc sched p K * (f xK.1 - f xstar) ≤ 4 * p.R ^ 2 := h1
            _ = 4 * p.R ^ 2 / p.ε * p.ε := by field_simp
            _ ≤ sched p K * p.ε := mul_le_mul_of_nonneg_right hgrow hε.le
        exact le_of_mul_le_mul_left h3 hA
      linarith
    · exact badInd_nonneg K 0 _ seeds
  have h := Finset.expect_le_expect (s := Finset.univ) (fun seeds _ => hpoint seeds)
  have hv2 := ville I K 0 (p.x0, p.x0, p.x0) hpt0
  have hinit := initial_potential I
  have herr := errSum_le I K
  refine h.trans (hv2.trans ?_)
  rw [div_le_iff₀ (by positivity)]
  simp only
  have := sq_nonneg p.R
  linarith

end

end OracleTemplate.MatrixGeneralizedZO
