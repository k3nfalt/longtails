import LongTails.Proofs.CyclicLogisticSignal

open scoped RealInnerProductSpace
open LongTails.Proofs.CyclicLogisticGroups
open LongTails.Proofs.CyclicLogisticDynamics
open LongTails.Proofs.CyclicLogisticSignal
open LongTails.Proofs.BilinearLogisticDescent (loss)

namespace LongTails.Proofs.CyclicLogisticTrajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

noncomputable def initial : Point E :=
  let b : CyclicLogisticGroups.Group E := WithLp.toLp 2 ((Real.sqrt 2)⁻¹, (0 : E))
  WithLp.toLp 2 (b, b)

noncomputable def path (z r : Fin n → E) (η : ℝ) : ℕ → Point E
  | 0 => initial
  | k + 1 => update z r η (path z r η k)

structure Stable (z r : Fin n → E) (η : ℝ) (s : Point E) (k : ℕ) : Prop where
  risk_le : risk z r s ≤ 1
  energy : ‖s‖ ^ 2 + 2 * η * risk z r s ≤ 2 + 4 * η * k
  strong : |imbalance s.fst - 1 / 2| + 2 * η * risk z r s ≤ 2 * η
  weak : |imbalance s.snd - 1 / 2| + 2 * η * risk z r s ≤ 2 * η
  positive : 0 < s.snd.fst
  member : s.fst.snd ∈ Submodule.span ℝ (Set.range z)

lemma initial_stable (z r : Fin n → E) (hn : 0 < n) {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 8) :
    Stable z r η initial 0 := by
  have hF : risk z r initial = Real.log 2 := by
    norm_num [risk, scores, margin, value, initial, loss, Nat.ne_of_gt hn]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI : imbalance (initial (E := E)).fst = 1 / 2 := by
    simp [imbalance, initial]
  have hE : ‖(initial : Point E)‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, group_norm, group_norm]
    simp [initial, hs]
    ring
  constructor
  · linarith
  · rw [hF, hE]; push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlog hη]
  · rw [hI, hF]; simp only [sub_self, abs_zero, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hlog hη]
  · change |imbalance (initial (E := E)).fst - 1 / 2| + _ ≤ _
    rw [hI, hF]; simp only [sub_self, abs_zero, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hlog hη]
  · change 0 < (Real.sqrt 2)⁻¹; positivity
  · exact Submodule.zero_mem _

lemma path_stable (z r : Fin n → E) (hn : 0 < n) {η μ ρ H : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 8) (hμ : 0 ≤ μ) (hμ' : μ ≤ 1) (hρ : 0 < ρ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ μ)
    (hopp : ∀ v ∈ Submodule.span ℝ (Set.range z), ∃ i, ⟪z i, v⟫ ≤ -ρ * ‖v‖)
    (hsmall : η * (1 + (1 + (2 * n + μ * H) / ρ + μ ^ 2 * H)) ≤ 1 / 8)
    (k : ℕ) (hk : 2 + 4 * η * k ≤ H) : Stable z r η (path z r η k) k := by
  induction k with
  | zero => exact initial_stable z r hn hη hη'
  | succ k ih =>
    push_cast at hk
    specialize ih (by linarith)
    let s := path z r η k
    let s' := update z r η s
    let v := velocity z r s
    change Stable z r η s k at ih
    change Stable z r η s' (k + 1)
    have hF := risk_nonneg z r s
    have hF' := risk_nonneg z r s'
    have hprod := mul_nonneg hη hF
    have hE : ‖s‖ ^ 2 ≤ H := by linarith [ih.energy]
    have hI₁ := ih.strong
    have hI₂ := ih.weak
    have hb₁ : |imbalance s.fst| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp (show |imbalance s.fst - 1 / 2| ≤ 1 / 4 by
        linarith)).1, (abs_le.mp (show |imbalance s.fst - 1 / 2| ≤ 1 / 4 by linarith)).2]
    have hb₂ : 1 / 4 ≤ imbalance s.snd := by linarith [neg_le_abs (imbalance s.snd - 1 / 2)]
    have hN := nuisance_bound z r s hμ hr hρ
      (hopp _ (Submodule.smul_mem _ _ ih.member)) ih.risk_le hn hb₁
    have hwE : ‖s.snd‖ ^ 2 ≤ H := by
      rw [WithLp.prod_norm_sq_eq_of_L2] at hE
      linarith [sq_nonneg ‖s.fst‖]
    have hM : ‖s.fst‖ ^ 2 + μ ^ 2 * ‖s.snd‖ ^ 2 ≤ 1 + (2 * n + μ * H) / ρ + μ ^ 2 * H := by
      have hmono : (2 * n + μ * ‖s‖ ^ 2) / ρ ≤ (2 * n + μ * H) / ρ := by gcongr
      linarith [mul_le_mul_of_nonneg_left hwE (sq_nonneg μ)]
    have hd := risk_descent hn z r s hη (by linarith) hμ' hz hr hM hsmall
    change risk z r s' ≤ risk z r s - η / 2 * ‖v‖ ^ 2 at hd
    have hdrop := mul_le_mul_of_nonneg_left hd hη
    have hwork := balance_bounds z r s η
    have he := energy_update hn z r s hη
    change ‖s'‖ ^ 2 ≤ ‖s‖ ^ 2 + 4 * η + η ^ 2 * ‖v‖ ^ 2 at he
    have hb {x y : ℝ} (hold : |x - 1 / 2| + 2 * η * risk z r s ≤ 2 * η)
        (hchange : |y - x| ≤ η ^ 2 * ‖v‖ ^ 2) :
        |y - 1 / 2| + 2 * η * risk z r s' ≤ 2 * η := by
      have htri := abs_add_le (y - x) (x - 1 / 2)
      rw [sub_add_sub_cancel] at htri
      linarith
    constructor
    · linarith [ih.risk_le, mul_nonneg hη (sq_nonneg ‖v‖)]
    · push_cast; linarith [ih.energy]
    · exact hb ih.strong hwork.1
    · exact hb ih.weak hwork.2
    · exact filter_positive z r s hn hr hμ' hη (by linarith) ih.positive (by linarith)
    · change s.fst.snd + η • (s.fst.fst • mean (scores z r s) z) ∈ _
      exact Submodule.add_mem _ ih.member (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (mean_in_span _ _)))

lemma hits_separator (z r : Fin n → E) (hn : 0 < n) {η μ κ ρ H : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 8) (hμ : 0 < μ) (hμ' : μ ≤ 1) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hz : ∀ i, ‖z i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ μ)
    (hopp : ∀ v ∈ Submodule.span ℝ (Set.range z), ∃ i, ⟪z i, v⟫ ≤ -ρ * ‖v‖)
    (u : E) (hu : ‖u‖ = 1) (hsep : ∀ i, μ * κ ≤ ⟪r i, u⟫)
    (hsmall : η * (1 + (1 + (2 * n + μ * H) / ρ + μ ^ 2 * H)) ≤ 1 / 8)
    (K : ℕ) (hK : 2 + 4 * η * K ≤ H)
    (hpow : 2 + Real.sqrt H ≤ (1 + η * (μ * κ) / (8 * n)) ^ K) :
    ∃ k ≤ K, ∀ i, 0 < scores z r (path z r η k) i := by
  by_contra! hfail
  have stable (k : ℕ) (hk : k ≤ K) := path_stable z r hn hη.le hη' hμ.le hμ' hρ hz hr
    hopp hsmall k (le_trans (by gcongr) hK)
  let b := 1 + η * (μ * κ) / (8 * n)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have grow (k : ℕ) (hk : k ≤ K) :
      b ^ k ≤ 1 + ⟪(path z r η k).snd.snd, u⟫ := by
    induction k with
    | zero => simp [path, initial]
    | succ k ih =>
      have hk' := Nat.le_of_succ_le hk
      have st := stable k hk'
      have hf := mul_nonneg hη.le (risk_nonneg z r (path z r η k))
      have hbis : 1 / 4 ≤ imbalance (path z r η k).snd := by
        linarith [st.weak, neg_le_abs (imbalance (path z r η k).snd - 1 / 2)]
      rw [pow_succ']
      exact (mul_le_mul_of_nonneg_left (ih hk') hb).trans (signal_growth z r _ u hn hu
        (mul_pos hμ hκ) hη.le hsep (hfail k hk') st.positive hbis)
  let s := path z r η K
  have st := stable K le_rfl
  have henergy : ‖s‖ ^ 2 ≤ H := by
    linarith [st.energy, mul_nonneg hη.le (risk_nonneg z r s)]
  have hs : ‖s.snd.snd‖ ≤ Real.sqrt H := by
    apply Real.le_sqrt_of_sq_le
    rw [WithLp.prod_norm_sq_eq_of_L2, group_norm s.snd] at henergy
    linarith [sq_nonneg ‖s.fst‖, sq_nonneg s.snd.fst]
  have hy := abs_real_inner_le_norm s.snd.snd u
  rw [hu, mul_one] at hy
  have hg : b ^ K ≤ 1 + ⟪s.snd.snd, u⟫ := grow K le_rfl
  change 2 + Real.sqrt H ≤ b ^ K at hpow
  linarith [le_abs_self ⟪s.snd.snd, u⟫]

end LongTails.Proofs.CyclicLogisticTrajectory
