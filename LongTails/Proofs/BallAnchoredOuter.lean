import LongTails.Proofs.BallAnchoredTrial
import LongTails.Proofs.LazyAnchoredLyapunov

open scoped RealInnerProductSpace

namespace LongTails.Proofs.BallAnchoredOuter

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.HessianStableNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredTrial
open LongTails.Proofs.LazyAnchoredLyapunov

noncomputable section

lemma descent_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x0 z z1 g g1 r : E) (a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (hz1 : z1 - x0 = (A / (A + a)) • (z - x0) - a • g1 + r)
    (hmono : A = 0 ∨ 0 ≤ ⟪g1 - g, z1 - z⟫) :
    potential x0 (A + a) z1 g1 ≤ potential x0 A z g +
      (A + a) ^ 2 / (2 * a ^ 2) *
        (‖r‖ ^ 2 - ‖z1 - (((a / (A + a)) • x0 + (A / (A + a)) • z) -
          (a * A / (A + a)) • g)‖ ^ 2) := by
  have hA1 : A + a ≠ 0 := by positivity
  have hβ : a / (A + a) = 1 - A / (A + a) := by field_simp; ring
  have hγ : a * A / (A + a) = a * (A / (A + a)) := by ring
  have hz : z1 = x0 + ((A / (A + a)) • (z - x0) - a • g1 + r) := by rw [← hz1]; abel
  have hd : z1 - (((a / (A + a)) • x0 + (A / (A + a)) • z) - (a * A / (A + a)) • g) =
      -(a • g1) + r + (a * A / (A + a)) • g := by
    rw [hβ, hγ, hz]
    module
  have hz1z : z1 - z = -((a / (A + a)) • (z - x0)) - a • g1 + r := by
    rw [hβ, hz]
    module
  have key := potential_identity a A ha hA (z - x0) g g1 r
  rw [← hz1z] at key
  have hterm : 0 ≤ A * (A + a) / a * ⟪g1 - g, z1 - z⟫ := by
    rcases hmono with h0 | hm
    · rw [h0]; simp
    · have hc : 0 ≤ A * (A + a) / a := by positivity
      exact mul_nonneg hc hm
  unfold potential
  rw [hd, hz1]
  linarith

variable {p : Public} {F : p.E → p.E} {S : p.E →L[ℝ] p.E}

def decrement (p : Public) : ℝ := 15 * radius p ^ 2 / 288

structure Inv (p : Public) (F : p.E → p.E) (xs : p.E) (Λ : ℝ) (k : ℕ) (A : ℝ) (z g : p.E) :
    Prop where
  ok : OuterOK p xs Λ A z g
  dist : ‖z - xs‖ ≤ p.D + radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1))
  grad : A = 0 ∨ g = F z
  zeroA : A = 0 → z = p.x0 ∧ g = 0
  pot : potential p.x0 A z g ≤ 0

lemma inv_initial (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} (hR : Region p F xs Λ) :
    Inv p F xs Λ 0 0 p.x0 0 := by
  refine ⟨⟨le_rfl, ?_, by rw [zero_mul]; linarith [hreg.D_pos], ?_⟩, ?_, Or.inl rfl,
    fun _ => ⟨rfl, rfl⟩, ?_⟩
  · have := hR.x0_dist; have := radius_pos hreg; linarith
  · simp only [norm_zero]
    unfold rho; have := radius_pos hreg; have := hreg.D_pos
    have := hR.Λ_nonneg; positivity
  · simp only [Nat.cast_zero, zero_div, mul_zero, add_zero]; exact hR.x0_dist
  · simp [potential]

lemma dist_step (hreg : Regular p F S) {k : ℕ} {x : ℝ}
    (hx : x ≤ p.D + radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) + tolerance p k) :
    x ≤ p.D + radius p / 6 * (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) := by
  have hr := radius_pos hreg
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < k + 2 := by positivity
  have e : radius p / 6 * (((k : ℝ) + 1) / ((k : ℝ) + 2)) -
      radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) =
        radius p / (6 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    field_simp
    ring
  have ht : tolerance p k ≤ radius p / (6 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    unfold tolerance
    apply div_le_div_of_nonneg_left hr.le (by positivity)
    nlinarith
  have key : radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) + tolerance p k ≤
      radius p / 6 * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := by linarith
  push_cast
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
  linarith

lemma w_dist_k (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} {k : ℕ} {A : ℝ} {z g : p.E}
    (hR : Region p F xs Λ) (hI : Inv p F xs Λ k A z g) {a : ℝ} (ha : 0 < a) :
    ‖wOf p A z a - xs‖ ≤ p.D + radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) := by
  have hA := hI.ok.A_nonneg
  have hAa : 0 < A + a := by linarith
  set b := p.D + radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1))
  have hb : p.D ≤ b := by
    have : 0 ≤ radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) := by
      have := radius_pos hreg; positivity
    exact le_add_of_nonneg_right this
  have e : wOf p A z a - xs = (a / (A + a)) • (p.x0 - xs) + (A / (A + a)) • (z - xs) := by
    unfold wOf
    have : a / (A + a) + A / (A + a) = 1 := by rw [← add_div, add_comm a A, div_self hAa.ne']
    rw [smul_sub, smul_sub]
    calc _ = (a / (A + a)) • p.x0 + (A / (A + a)) • z - (a / (A + a) + A / (A + a)) • xs := by
          rw [this, one_smul]
      _ = _ := by rw [add_smul]; abel
  rw [e]
  have h1 : 0 ≤ a / (A + a) := by positivity
  have h2 : 0 ≤ A / (A + a) := by positivity
  calc _ ≤ ‖(a / (A + a)) • (p.x0 - xs)‖ + ‖(A / (A + a)) • (z - xs)‖ := norm_add_le _ _
    _ = a / (A + a) * ‖p.x0 - xs‖ + A / (A + a) * ‖z - xs‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
        abs_of_nonneg h2]
    _ ≤ a / (A + a) * b + A / (A + a) * b := by
      gcongr
      · exact hR.x0_dist.trans hb
      · exact hI.dist
    _ = b := by rw [← add_mul, ← add_div, add_comm a A, div_self hAa.ne', one_mul]

lemma final_dist (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} {k : ℕ} {A : ℝ} {z g : p.E}
    (hR : Region p F xs Λ) (hI : Inv p F xs Λ k A z g) {a : ℝ} (ha : 0 < a)
    (hφ : phi hreg A z g a ha < radius p) :
    ‖finalPoint F k A z g a - xs‖ ≤
      p.D + radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) + tolerance p k := by
  have h1 := resolvent_dist hreg hR.zero ha (resolvent_zero hreg A z g ha hφ)
  have h2 := final_close' hreg k A z g ha
  have h3 := w_dist_k hreg hR hI ha
  calc ‖finalPoint F k A z g a - xs‖
      = ‖(finalPoint F k A z g a - ballSol hreg A z g a ha) +
          (ballSol hreg A z g a ha - xs)‖ := by congr 1; abel
    _ ≤ ‖finalPoint F k A z g a - ballSol hreg A z g a ha‖ + ‖ballSol hreg A z g a ha - xs‖ :=
      norm_add_le _ _
    _ ≤ _ := by linarith

lemma accept_potential (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} {k : ℕ} {A : ℝ} {z g : p.E}
    (hI : Inv p F xs Λ k A z g) {a : ℝ} (ha : 0 < a)
    (hφ : phi hreg A z g a ha < radius p)
    (hd : radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    potential p.x0 (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) ≤
      potential p.x0 A z g - ((A + a) / a) ^ 2 * decrement p := by
  have hA := hI.ok.A_nonneg
  have hAa : 0 < A + a := by linarith
  set z1 := finalPoint F k A z g a
  set r := a • F z1 + z1 - wOf p A z a with hr
  have hz1 : z1 - p.x0 = (A / (A + a)) • (z - p.x0) - a • F z1 + r := by
    have hβ : a / (A + a) = 1 - A / (A + a) := by field_simp; ring
    rw [hr]; unfold wOf; rw [hβ]; module
  have hmono : A = 0 ∨ 0 ≤ ⟪F z1 - g, z1 - z⟫ := by
    rcases hI.grad with h | h
    · exact Or.inl h
    · right; rw [h]; exact monotone_F hreg z1 z
  have hdes := descent_zero p.x0 z z1 g (F z1) r a A ha hA hz1 hmono
  have hres := final_residual hreg k A z g ha hφ
  have htol := tolerance_le hreg k
  have hrad := radius_pos hreg
  have hc : z1 - (((a / (A + a)) • p.x0 + (A / (A + a)) • z) - (a * A / (A + a)) • g) =
      z1 - cOf p A z g a := rfl
  rw [hc] at hdes
  have hr0 : ‖r‖ ≤ radius p / 12 := hres.trans htol
  have hr2 : ‖r‖ ^ 2 ≤ (radius p / 12) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hr0 2
  have hd2 : (radius p / 3) ^ 2 ≤ ‖z1 - cOf p A z g a‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  have hq : (A + a) ^ 2 / (2 * a ^ 2) * (‖r‖ ^ 2 - ‖z1 - cOf p A z g a‖ ^ 2) ≤
      -(((A + a) / a) ^ 2 * decrement p) := by
    have ha0 : a ≠ 0 := ha.ne'
    have hcoef : 0 ≤ (A + a) ^ 2 / (2 * a ^ 2) := by positivity
    have h1 : ‖r‖ ^ 2 - ‖z1 - cOf p A z g a‖ ^ 2 ≤ -(15 * radius p ^ 2 / 144) := by
      nlinarith
    calc (A + a) ^ 2 / (2 * a ^ 2) * (‖r‖ ^ 2 - ‖z1 - cOf p A z g a‖ ^ 2)
        ≤ (A + a) ^ 2 / (2 * a ^ 2) * (-(15 * radius p ^ 2 / 144)) :=
          mul_le_mul_of_nonneg_left h1 hcoef
      _ = _ := by unfold decrement; field_simp; ring
  linarith

lemma accept_inv (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} {k : ℕ} {A : ℝ} {z g : p.E}
    (hR : Region p F xs Λ) (hI : Inv p F xs Λ k A z g) {a : ℝ} (ha : 0 < a)
    (hφ : phi hreg A z g a ha < radius p)
    (hd : radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    Inv p F xs Λ (k + 1) (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) := by
  have hA := hI.ok.A_nonneg
  have hAa : 0 < A + a := by linarith
  have hpot := accept_potential hreg hI ha hφ hd
  have hdec : 0 ≤ ((A + a) / a) ^ 2 * decrement p := by
    unfold decrement; positivity
  have hpot0 : potential p.x0 (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) ≤ 0 := by
    linarith [hI.pot]
  have hdist := dist_step hreg (final_dist hreg hR hI ha hφ)
  have hr := radius_pos hreg
  have hfrac : ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hz : ‖finalPoint F k A z g a - xs‖ ≤ p.D + radius p / 6 := by
    have : radius p / 6 * (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) ≤ radius p / 6 := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ radius p / 6)
      linarith
    linarith
  have hzr : ‖finalPoint F k A z g a - xs‖ ≤ rho p := by
    unfold rho; have := hreg.D_pos; linarith
  have hmono : 0 ≤ ⟪F (finalPoint F k A z g a), finalPoint F k A z g a - xs⟫ := by
    have := monotone_F hreg (finalPoint F k A z g a) xs
    rwa [hR.zero, sub_zero] at this
  refine ⟨⟨hAa.le, hz, ?_, ?_⟩, hdist, Or.inr rfl, fun h => absurd h hAa.ne', hpot0⟩
  · have := residual_bound p.x0 xs _ _ (A + a) p.D hAa hR.x0_dist hmono hpot0
    rw [le_div_iff₀ hAa] at this
    linarith
  · exact (region_norm hreg hR hzr).trans (mul_le_mul_of_nonneg_left hzr hR.Λ_nonneg)

lemma finished_accuracy (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} {k : ℕ} {A : ℝ} {z g : p.E}
    (hR : Region p F xs Λ) (hI : Inv p F xs Λ k A z g) (hA : stepMax p ≤ A) (hA0 : 0 < A) :
    ‖g‖ ≤ p.ε := by
  have hg : g = F z := by
    rcases hI.grad with h | h
    · exact absurd h hA0.ne'
    · exact h
  have hmono : 0 ≤ ⟪g, z - xs⟫ := by
    have := monotone_F hreg z xs
    rwa [hR.zero, sub_zero, ← hg] at this
  have h := residual_bound p.x0 xs z g A p.D hA0 hR.x0_dist hmono hI.pot
  have hε := hreg.ε_pos
  have hr := radius_pos hreg
  have hsm : stepMax p = (2 * p.D + radius p) / p.ε := rfl
  have h2 : 2 * p.D / A ≤ 2 * p.D / stepMax p :=
    div_le_div_of_nonneg_left (by have := hreg.D_pos; positivity)
      (by rw [hsm]; have := hreg.D_pos; positivity) hA
  have h3 : 2 * p.D / stepMax p ≤ p.ε := by
    rw [hsm, div_div_eq_mul_div, div_le_iff₀ (by have := hreg.D_pos; positivity)]
    nlinarith
  linarith

lemma terminal_accuracy (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} {k : ℕ} {A : ℝ} {z g : p.E}
    (hR : Region p F xs Λ) (hI : Inv p F xs Λ k A z g) (ha : 0 < stepMax p)
    (hφ : phi hreg A z g (stepMax p) ha < radius p) :
    ‖F (finalPoint F k A z g (stepMax p))‖ ≤ p.ε := by
  have hr := radius_pos hreg
  have hε := hreg.ε_pos
  have hD := hreg.D_pos
  set a := stepMax p with hadef
  set z1 := finalPoint F k A z g a
  have hres : ‖a • F z1 + z1 - wOf p A z a‖ ≤ tolerance p k := final_residual hreg k A z g ha hφ
  have htol := tolerance_le hreg k
  have hfd : ‖z1 - xs‖ ≤ p.D + radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) + tolerance p k :=
    final_dist hreg hR hI ha hφ
  have hw := w_dist_k hreg hR hI ha
  have hfrac : ((k : ℝ) / ((k : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hb : radius p / 6 * ((k : ℝ) / ((k : ℝ) + 1)) ≤ radius p / 6 := by
    have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ radius p / 6)
    linarith
  have hzw : ‖z1 - wOf p A z a‖ ≤ ‖z1 - xs‖ + ‖wOf p A z a - xs‖ := by
    calc ‖z1 - wOf p A z a‖ = ‖(z1 - xs) - (wOf p A z a - xs)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hFa : a * ‖F z1‖ ≤ 2 * p.D + radius p := by
    have e : (a • F z1 + z1 - wOf p A z a) - (z1 - wOf p A z a) = a • F z1 := by abel
    have : ‖a • F z1‖ ≤ ‖a • F z1 + z1 - wOf p A z a‖ + ‖z1 - wOf p A z a‖ := by
      have h := norm_sub_le (a • F z1 + z1 - wOf p A z a) (z1 - wOf p A z a)
      rwa [e] at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at this
    linarith
  have hae : a * p.ε = 2 * p.D + radius p := by
    show stepMax p * p.ε = _
    unfold stepMax
    exact div_mul_cancel₀ _ hε.ne'
  have : a * ‖F z1‖ ≤ a * p.ε := by linarith
  exact le_of_mul_le_mul_left this ha

structure Growth (n : ℕ) (A A1 Q : ℝ) : Prop where
  A1_pos : 0 < A1
  A1_le : A1 ≤ A
  Q_nonneg : 0 ≤ Q
  sums : ∃ S1 S2 : ℝ, 0 ≤ S1 ∧ 0 ≤ S2 ∧ (n : ℝ) ^ 2 ≤ S1 * S2 ∧ S2 ^ 2 ≤ n * Q ∧
    S1 ≤ Real.log (A / A1)

lemma growth_zero {A1 : ℝ} (h : 0 < A1) : Growth 0 A1 A1 0 :=
  ⟨h, le_rfl, le_rfl, ⟨0, 0, le_rfl, le_rfl, by simp, by simp, by simp [div_self h.ne']⟩⟩

lemma growth_step {n : ℕ} {A A1 Q a : ℝ} (hG : Growth n A A1 Q) (ha : 0 < a) :
    Growth (n + 1) (A + a) A1 (Q + ((A + a) / a) ^ 2) := by
  obtain ⟨hA1, hA1A, hQ, S1, S2, h1, h2, h3, h4, h5⟩ := hG
  have hA : 0 < A := lt_of_lt_of_le hA1 hA1A
  have hAa : 0 < A + a := by linarith
  set q := (A + a) / a with hqdef
  have hq : 0 < q := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS1q : 0 ≤ S1 * q + S2 / q := add_nonneg (mul_nonneg h1 hq.le) (div_nonneg h2 hq.le)
  refine ⟨hA1, by linarith, add_nonneg hQ (sq_nonneg _), S1 + 1 / q, S2 + q,
    add_nonneg h1 (one_div_nonneg.mpr hq.le), add_nonneg h2 hq.le, ?_, ?_, ?_⟩
  · have hq0 : q ≠ 0 := hq.ne'
    have hxy : (S1 * q) * (S2 / q) = S1 * S2 := by
      rw [mul_assoc, mul_div_assoc', mul_comm q S2, mul_div_assoc, div_self hq0, mul_one]
    have hX : 2 * (n : ℝ) ≤ S1 * q + S2 / q := by
      have hsq : (2 * (n : ℝ)) ^ 2 ≤ (S1 * q + S2 / q) ^ 2 := by
        nlinarith [sq_nonneg (S1 * q - S2 / q)]
      exact (pow_le_pow_iff_left₀ (by positivity) hS1q two_ne_zero).mp hsq
    have hqq : 1 / q * q = 1 := one_div_mul_cancel hq0
    have e : (S1 + 1 / q) * (S2 + q) = S1 * S2 + (S1 * q + S2 / q) + 1 := by
      linear_combination hqq
    rw [e]; push_cast; nlinarith
  · have hY : 2 * q * S2 ≤ Q + n * q ^ 2 := by
      have hsq : (2 * q * S2) ^ 2 ≤ (Q + n * q ^ 2) ^ 2 := by
        have : (2 * q * S2) ^ 2 = 4 * q ^ 2 * S2 ^ 2 := by ring
        rw [this]
        nlinarith [sq_nonneg (Q - n * q ^ 2), mul_le_mul_of_nonneg_left h4
          (by positivity : (0 : ℝ) ≤ 4 * q ^ 2)]
      exact (pow_le_pow_iff_left₀ (mul_nonneg (mul_nonneg (by norm_num) hq.le) h2)
        (add_nonneg hQ (mul_nonneg hn (sq_nonneg q))) two_ne_zero).mp hsq
    push_cast
    nlinarith
  · have hl : Real.log ((A + a) / A1) = Real.log (A / A1) + Real.log ((A + a) / A) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      rw [div_mul_div_comm, mul_comm A (A + a), mul_div_mul_right _ _ hA.ne']
    have hlog := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < (A + a) / A)
    have e : 1 - ((A + a) / A)⁻¹ = 1 / q := by
      rw [inv_div, hqdef, one_div_div, eq_div_iff hAa.ne', sub_mul, div_mul_cancel₀ _ hAa.ne']
      ring
    rw [hl]
    linarith

lemma growth_bound {n : ℕ} {A A1 Q amax : ℝ} (hG : Growth n A A1 Q) (hA : A ≤ amax) :
    (n : ℝ) ^ 3 ≤ Real.log (amax / A1) ^ 2 * Q := by
  obtain ⟨hA1, hA1A, hQ, S1, S2, h1, h2, h3, h4, h5⟩ := hG
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : S1 ≤ Real.log (amax / A1) := by
    have hm : 0 < A := lt_of_lt_of_le hA1 hA1A
    refine h5.trans (Real.log_le_log (div_pos hm hA1) ?_)
    exact div_le_div_of_nonneg_right hA hA1.le
  have hS1 : S1 ^ 2 ≤ Real.log (amax / A1) ^ 2 := pow_le_pow_left₀ h1 hlog 2
  have h6 : (n : ℝ) ^ 4 ≤ S1 ^ 2 * (n * Q) := by
    have := pow_le_pow_left₀ (by positivity) h3 2
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg S1)]
  rcases eq_or_lt_of_le hn with h0 | h0
  · calc (n : ℝ) ^ 3 = 0 := by rw [← h0]; norm_num
      _ ≤ _ := mul_nonneg (sq_nonneg _) hQ
  · have h7 : (n : ℝ) ^ 3 ≤ S1 ^ 2 * Q := by
      have : (n : ℝ) * (n : ℝ) ^ 3 ≤ (n : ℝ) * (S1 ^ 2 * Q) := by nlinarith
      exact le_of_mul_le_mul_left this h0
    nlinarith [mul_le_mul_of_nonneg_right hS1 hQ]

end

end LongTails.Proofs.BallAnchoredOuter
