import LongTails.Proofs.WeaklyConvexSilverBasic
import LongTails.Proofs.WeaklyConvexSilverCertificate

open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeaklyConvexSilverJoin

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace
open LongTails.Proofs.WeaklyConvexSilverBasic
open LongTails.Proofs.WeaklyConvexSilverCertificate

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma sq_add_le_two (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

omit [InnerProductSpace ℝ E] in
lemma sq_add_le_three (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

omit [InnerProductSpace ℝ E] in
lemma sq_add_le_young (a b : E) {l : ℝ} (hl : 0 < l) :
    ‖a + b‖ ^ 2 ≤ (1 + l) * ‖a‖ ^ 2 + (1 + 1 / l) * ‖b‖ ^ 2 := by
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  have h3 : 2 * ‖a‖ * ‖b‖ ≤ l * ‖a‖ ^ 2 + 1 / l * ‖b‖ ^ 2 := by
    have e : l * ‖a‖ ^ 2 + 1 / l * ‖b‖ ^ 2 - 2 * ‖a‖ * ‖b‖ =
        1 / l * (l * ‖a‖ - ‖b‖) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg (le_of_lt (one_div_pos.mpr hl)) (sq_nonneg (l * ‖a‖ - ‖b‖))]
  nlinarith

lemma anchor_defect (f : E → ℝ) (g : E → E) (e y : E) :
    defect (f e) (f y) e y (g e) (g y) =
      -2 * (f y - (f e - ‖g e‖ ^ 2 / 2)) + 2 * ⟪g y, y - (e - g e)⟫ - ‖g y‖ ^ 2 := by
  simp only [defect, norm_sub_sq_real, inner_sub_right, real_inner_comm (g e) (g y)]
  ring

lemma nodes_join_cases (g : E → E) (hs : List ℝ) (μ : ℝ) (x w : E)
    (hw : w ∈ nodes g (hs ++ [μ] ++ hs) x) :
    w ∈ nodes g hs x ∨ w ∈ nodes g hs (run g hs x - μ • g (run g hs x)) := by
  rcases (nodes_append g (hs ++ [μ]) hs x w).1 hw with h | h
  · rcases (nodes_append g hs [μ] x w).1 h with h' | h'
    · exact Or.inl h'
    · simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl
      · exact Or.inl (run_mem_nodes g hs x)
      · exact Or.inr (start_mem_nodes g hs _)
  · right
    simpa only [run_append, run] using h

def BlockBound (f : E → ℝ) (g : E → E) (ρ : ℝ) (k : ℕ) (n q A : ℝ) : Prop :=
  ∀ (x e : E) (R2 η : ℝ), 0 ≤ η → ‖x - (e - g e)‖ ^ 2 ≤ R2 →
    -(1 / 10) * (steps k).sum * ‖g (run g (steps k) x)‖ ^ 2 - η ≤
      f (run g (steps k) x) - (f e - ‖g e‖ ^ 2 / 2) →
    (∀ w ∈ nodes g (steps k) x,
      ‖w - (e - g e)‖ ^ 2 ≤ n * (R2 + 2 * ((steps k).sum + 1) * η) ∧
      ‖g w‖ ^ 2 ≤ q * (R2 + 2 * ((steps k).sum + 1) * η)) ∧
    -(ρ * A * (R2 + 2 * ((steps k).sum + 1) * η)) ≤ primitive f g (steps k) x

lemma level_facts (k : ℕ) (hk : 1 ≤ k) :
    let S := (steps k).sum
    let μ := (ratio - 2) * (S + 1) + 1
    ratio ≤ S + 1 ∧ 1 ≤ S ∧ μ ≤ 3 / 2 * S ∧ 0 ≤ μ - 1 ∧
      (μ - 1) ^ 2 = (S + 1) ^ 2 * (ratio - 2) ^ 2 := by
  intro S μ
  have hb := ratio_bounds
  have hS : S = ratio ^ k - 1 := steps_sum k
  have hp : ratio ≤ ratio ^ k := by
    calc ratio = ratio ^ 1 := (pow_one _).symm
      _ ≤ ratio ^ k := pow_le_pow_right₀ (by linarith) hk
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · show (ratio - 2) * (S + 1) + 1 ≤ 3 / 2 * S
    nlinarith
  · show 0 ≤ (ratio - 2) * (S + 1) + 1 - 1
    nlinarith
  · show ((ratio - 2) * (S + 1) + 1 - 1) ^ 2 = (S + 1) ^ 2 * (ratio - 2) ^ 2
    ring

lemma num_ratio_sq : (ratio - 2) ^ 2 ≤ 1716 / 10000 := by
  have hb := ratio_bounds
  have h0 : 0 ≤ ratio - 2 := by linarith [hb.1]
  have h1 : ratio - 2 ≤ 414214 / 1000000 := by linarith [hb.2]
  have h2 := pow_le_pow_left₀ h0 h1 2
  have h3 : ((414214 : ℝ) / 1000000) ^ 2 ≤ 1716 / 10000 := by norm_num
  linarith

lemma num_scaled {S e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 200) :
    (S + 1) ^ 2 * (ratio - 2) ^ 2 * (1 + e) ≤ (S + 1) ^ 2 * (1716 / 10000) * (1 + 1 / 200) := by
  apply mul_le_mul _ (by linarith) (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left num_ratio_sq (sq_nonneg _)

lemma num_C1 {S e : ℝ} (hS : 1 ≤ S) (he0 : 0 ≤ e) (he : e ≤ 1 / 200) :
    (S + 1) ^ 2 * (ratio - 2) ^ 2 * (1 + e) ≤ S + S ^ 2 / 5 := by
  have h := num_scaled (S := S) he0 he
  nlinarith [sq_nonneg S]

lemma num_C4 {S e : ℝ} (hS : 14142 / 10000 ≤ S) (he0 : 0 ≤ e) (he : e ≤ 1 / 200) :
    (S + 1) ^ 2 * (ratio - 2) ^ 2 * (1 + e) ≤ 7 / 20 * (S * (S + 1) - S ^ 2 / 5) := by
  have h := num_scaled (S := S) he0 he
  have hSS : 14142 / 10000 * S ≤ S * S := mul_le_mul_of_nonneg_right hS (by linarith)
  nlinarith

lemma num_C3 {S : ℝ} (hS : 14142 / 10000 ≤ S) :
    S * (S + 1) + ((ratio - 2) * (S + 1) + 1) - ((ratio - 2) * (S + 1) + 1) ^ 2 -
      (S + ((ratio - 2) * (S + 1) + 1)) * S / 5 ≥ 0 := by
  have hb := ratio_bounds
  have hsq := ratio_square
  have ha : (ratio - 2) ^ 2 = 1 - 2 * (ratio - 2) := by linear_combination hsq
  have hq : (ratio - 2) ^ 2 * (S + 1) ^ 2 = (1 - 2 * (ratio - 2)) * (S + 1) ^ 2 := by rw [ha]
  have hS0 : 0 ≤ S := by linarith
  have h1 : 414213 / 1000000 * S ^ 2 ≤ (ratio - 2) * S ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hb.1]) (sq_nonneg S)
  have h2 : 414213 / 1000000 * S ≤ (ratio - 2) * S :=
    mul_le_mul_of_nonneg_right (by linarith [hb.1]) hS0
  have hSS : 14142 / 10000 * S ≤ S * S := mul_le_mul_of_nonneg_right hS hS0
  nlinarith

lemma num_sq_five {S : ℝ} (hr : ratio ≤ S + 1) : 29 / 5 ≤ (S + 1) ^ 2 := by
  have hb := ratio_bounds
  have h := pow_le_pow_left₀ (by linarith [hb.1] : (0:ℝ) ≤ ratio) hr 2
  have hsq := ratio_square
  linarith [hb.1]

set_option maxHeartbeats 4000000 in
lemma join_scalar {S μ ρ A Y X R2 η ZL Gy Gz PC ZC θ2 cL cR cRy cc cz cIC : ℝ}
    (hS1 : 1 ≤ S) (hμ : μ ≤ 3 / 2 * S) (hμ1 : 1 ≤ μ) (hr : ratio ≤ S + 1)
    (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hY : 0 ≤ Y) (hX : 0 ≤ X) (hη : 0 ≤ η) (hR2 : 0 ≤ R2)
    (hGy : 0 ≤ Gy) (hGz : 0 ≤ Gz) (hZC : 0 ≤ ZC)
    (hε : ρ * (A + 3 * S * (1 + Y)) ≤ 1 / 200)
    (hZL : ZL = R2 + 2 * (S + 1) * (η + ρ * (A + 3 * S * (1 + Y)) * X / (2 * S)))
    (hGy' : (μ - 1) ^ 2 * Gy ≤ 7 / 20 * ZL)
    (hGz' : (S + 1) ^ 2 * Gz ≤ X * (1 + ρ * A + ρ * S * Y))
    (hPC : PC ≤ R2 + 2 * (S + μ) * (η + ρ * (A + 3 * S * (1 + Y)) * X / (2 * S)) +
      ρ * (A + S * Y) * ZL + μ * ρ * Y * ZL)
    (hZC' : ZC * (1 - 3 * S * ρ) ≤ PC + 2 * S * η + ρ * A * X + 3 * S * ρ * Gz +
      3 * S * ρ * Y * X)
    (hF1 : X ≤ θ2 * R2 + cL * (ρ * (A + S * Y) * ZL) +
      cR * (ρ * A * X + 3 * S * ρ * (ZC + Gz + Y * X)) +
      cRy * (ρ * A * X + S * ρ * (3 * ((μ - 1) ^ 2 * Gy + X + Y * X))) +
      cc * S * (ρ * Y * ZL) + cz * S * (ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy))) + cIC * S * η)
    (_hcL : 0 ≤ cL) (hcL' : cL ≤ 3 / 5) (_hcR : 0 ≤ cR) (hcR' : cR ≤ 1 / 5)
    (_hcRy : 0 ≤ cRy) (hcRy' : cRy ≤ 34 / 25) (_hcc : 0 ≤ cc) (hcc' : cc ≤ 7 / 50)
    (_hcz : 0 ≤ cz) (hcz' : cz ≤ 31 / 50) (hθ : 0 ≤ θ2) (hθ' : θ2 ≤ 3 / 5)
    (_hcIC : 0 ≤ cIC) (hcIC' : cIC * S ≤ 2 * θ2 * (2 * S + μ + 1)) :
    X ≤ (θ2 + 3 / 200) * (R2 + 2 * (2 * S + μ + 1) * η) ∧
      ZL ≤ (1 + 13 / 2000) * (R2 + 2 * (2 * S + μ + 1) * η) ∧
      ZC ≤ 41 / 40 * (R2 + 2 * (2 * S + μ + 1) * η) ∧
      Gz ≤ 1 / 5 * X := by
  set Z := R2 + 2 * (2 * S + μ + 1) * η with hZ
  have hb := ratio_bounds
  have hS0 : 0 < S := by linarith
  have hYS : 0 ≤ S * Y := mul_nonneg hS0.le hY
  have e1 : ρ * A ≤ 1 / 200 := by linarith [mul_nonneg hρ (mul_nonneg hS0.le (by linarith : (0:ℝ) ≤ 1 + Y))]
  have e2 : 3 * S * ρ ≤ 1 / 200 := by linarith [mul_nonneg hρ hA, mul_nonneg hρ (mul_nonneg hS0.le hY)]
  have e3 : ρ * A + 3 * S * ρ * Y ≤ 1 / 200 := by linarith [mul_nonneg hρ hS0.le]
  have e4 : ρ * (A + S * Y) ≤ 1 / 200 := by linarith [mul_nonneg hρ hS0.le, mul_nonneg hρ hYS]
  have e5 : μ * ρ * Y ≤ 1 / 400 := by
    have h1 : S * ρ * Y ≤ 1 / 600 := by linarith [mul_nonneg hρ hA, mul_nonneg hρ hS0.le]
    have h2 : μ * ρ * Y ≤ 3 / 2 * S * ρ * Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hρ) hY
    linarith
  have hSY : S * ρ * Y ≤ 1 / 600 := by linarith [mul_nonneg hρ hA, mul_nonneg hρ hS0.le]
  have hSρ : S * ρ ≤ 1 / 600 := by linarith
  set ε := ρ * (A + 3 * S * (1 + Y)) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hΔ : 2 * (S + 1) * (ρ * (A + 3 * S * (1 + Y)) * X / (2 * S)) ≤ 2 / 200 * X := by
    rw [← hεdef]
    have : 2 * (S + 1) * (ε * X / (2 * S)) = (S + 1) / S * (ε * X) := by
      field_simp
    rw [this]
    have h1 : (S + 1) / S ≤ 2 := by rw [div_le_iff₀ hS0]; linarith
    have h2 : ε * X ≤ 1 / 200 * X := mul_le_mul_of_nonneg_right hε hX
    calc (S + 1) / S * (ε * X) ≤ 2 * (ε * X) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hε0 hX)
      _ ≤ 2 / 200 * X := by linarith
  have hΔ' : 2 * (S + μ) * (ρ * (A + 3 * S * (1 + Y)) * X / (2 * S)) ≤ 5 / 400 * X := by
    rw [← hεdef]
    have : 2 * (S + μ) * (ε * X / (2 * S)) = (S + μ) / S * (ε * X) := by
      field_simp
    rw [this]
    have h1 : (S + μ) / S ≤ 5 / 2 := by rw [div_le_iff₀ hS0]; linarith
    have h2 : ε * X ≤ 1 / 200 * X := mul_le_mul_of_nonneg_right hε hX
    calc (S + μ) / S * (ε * X) ≤ 5 / 2 * (ε * X) := by
          apply mul_le_mul_of_nonneg_right h1 (mul_nonneg hε0 hX)
      _ ≤ 5 / 400 * X := by linarith
  have hZLb : ZL ≤ R2 + 2 * (S + 1) * η + 2 / 200 * X := by
    rw [hZL, mul_add]; linarith
  have hZL0 : 0 ≤ ZL := by
    rw [hZL]
    have : 0 ≤ ρ * (A + 3 * S * (1 + Y)) * X / (2 * S) := by positivity
    positivity
  have hPCb : PC ≤ R2 + 2 * (S + μ) * η + 5 / 400 * X + 1 / 200 * ZL + 1 / 400 * ZL := by
    have h1 : ρ * (A + S * Y) * ZL ≤ 1 / 200 * ZL := mul_le_mul_of_nonneg_right e4 hZL0
    have h2 : μ * ρ * Y * ZL ≤ 1 / 400 * ZL := mul_le_mul_of_nonneg_right e5 hZL0
    have h3 := hPC
    rw [mul_add] at h3
    linarith
  have hs2 : 29 / 5 ≤ (S + 1) ^ 2 := num_sq_five hr
  have hGzb : Gz ≤ 1 / 5 * X := by
    have h1 : X * (1 + ρ * A + ρ * S * Y) ≤ X * (1 + 1 / 200) := by
      apply mul_le_mul_of_nonneg_left _ hX
      linarith [e4]
    have h2 := mul_le_mul_of_nonneg_right hs2 hGz
    linarith
  have hZCb : ZC * (1 - 1 / 200) ≤ R2 + 2 * (2 * S + μ) * η + 7 / 400 * X + 1 / 200 * ZL +
      1 / 400 * ZL + 1 / 200 * Gz := by
    have h1 : ZC * (1 - 1 / 200) ≤ ZC * (1 - 3 * S * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) hZC
    have h2 : ρ * A * X + 3 * S * ρ * Y * X ≤ 1 / 200 * X := by
      have := mul_le_mul_of_nonneg_right e3 hX
      linarith
    have h3 : 3 * S * ρ * Gz ≤ 1 / 200 * Gz := mul_le_mul_of_nonneg_right e2 hGz
    linarith
  have hT1 : cL * (ρ * (A + S * Y) * ZL) ≤ 3 / 5 * (1 / 200 * ZL) := by
    have h1 : ρ * (A + S * Y) * ZL ≤ 1 / 200 * ZL := mul_le_mul_of_nonneg_right e4 hZL0
    have h0 : 0 ≤ ρ * (A + S * Y) * ZL := by positivity
    calc cL * (ρ * (A + S * Y) * ZL) ≤ 3 / 5 * (ρ * (A + S * Y) * ZL) :=
          mul_le_mul_of_nonneg_right hcL' h0
      _ ≤ 3 / 5 * (1 / 200 * ZL) := by linarith
  have hT2 : cR * (ρ * A * X + 3 * S * ρ * (ZC + Gz + Y * X)) ≤
      1 / 5 * (1 / 200 * X + 1 / 200 * (ZC + Gz)) := by
    have h0 : 0 ≤ ρ * A * X + 3 * S * ρ * (ZC + Gz + Y * X) := by positivity
    have h1 : ρ * A * X + 3 * S * ρ * (ZC + Gz + Y * X) ≤ 1 / 200 * X + 1 / 200 * (ZC + Gz) := by
      have a1 : ρ * A * X + 3 * S * ρ * Y * X ≤ 1 / 200 * X := by
        have := mul_le_mul_of_nonneg_right e3 hX
        linarith
      have a2 : 3 * S * ρ * (ZC + Gz) ≤ 1 / 200 * (ZC + Gz) :=
        mul_le_mul_of_nonneg_right e2 (by positivity)
      linarith
    calc cR * (ρ * A * X + 3 * S * ρ * (ZC + Gz + Y * X)) ≤
          1 / 5 * (ρ * A * X + 3 * S * ρ * (ZC + Gz + Y * X)) :=
          mul_le_mul_of_nonneg_right hcR' h0
      _ ≤ _ := by linarith
  have hT3 : cRy * (ρ * A * X + S * ρ * (3 * ((μ - 1) ^ 2 * Gy + X + Y * X))) ≤
      34 / 25 * (1 / 200 * X + 1 / 200 * (7 / 20 * ZL)) := by
    have hG0 : 0 ≤ (μ - 1) ^ 2 * Gy := by positivity
    have h0 : 0 ≤ ρ * A * X + S * ρ * (3 * ((μ - 1) ^ 2 * Gy + X + Y * X)) := by positivity
    have h1 : ρ * A * X + S * ρ * (3 * ((μ - 1) ^ 2 * Gy + X + Y * X)) ≤
        1 / 200 * X + 1 / 200 * (7 / 20 * ZL) := by
      have a1 : (ρ * A + 3 * S * ρ + 3 * S * ρ * Y) * X ≤ 1 / 200 * X := by
        apply mul_le_mul_of_nonneg_right _ hX
        linarith
      have a2 : 3 * S * ρ * ((μ - 1) ^ 2 * Gy) ≤ 1 / 200 * ((μ - 1) ^ 2 * Gy) :=
        mul_le_mul_of_nonneg_right e2 hG0
      have a3 : 1 / 200 * ((μ - 1) ^ 2 * Gy) ≤ 1 / 200 * (7 / 20 * ZL) := by linarith
      linarith
    calc cRy * (ρ * A * X + S * ρ * (3 * ((μ - 1) ^ 2 * Gy + X + Y * X))) ≤
          34 / 25 * (ρ * A * X + S * ρ * (3 * ((μ - 1) ^ 2 * Gy + X + Y * X))) :=
          mul_le_mul_of_nonneg_right hcRy' h0
      _ ≤ _ := by linarith
  have hT4 : cc * S * (ρ * Y * ZL) ≤ 7 / 50 * (1 / 600 * ZL) := by
    have h1 : S * ρ * Y * ZL ≤ 1 / 600 * ZL := mul_le_mul_of_nonneg_right hSY hZL0
    have h0 : 0 ≤ S * ρ * Y * ZL := by positivity
    have : cc * S * (ρ * Y * ZL) = cc * (S * ρ * Y * ZL) := by ring
    rw [this]
    calc cc * (S * ρ * Y * ZL) ≤ 7 / 50 * (S * ρ * Y * ZL) := mul_le_mul_of_nonneg_right hcc' h0
      _ ≤ _ := by linarith
  have hT5 : cz * S * (ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy))) ≤
      31 / 50 * (1 / 600 * (2 * X + 2 * (7 / 20 * ZL))) := by
    have hG0 : 0 ≤ (μ - 1) ^ 2 * Gy := by positivity
    have h0 : 0 ≤ S * ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy)) := by positivity
    have h1 : S * ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy)) ≤ 1 / 600 * (2 * X + 2 * (7 / 20 * ZL)) := by
      have a1 : S * ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy)) ≤ 1 / 600 * (2 * X + 2 * ((μ - 1) ^ 2 * Gy)) :=
        mul_le_mul_of_nonneg_right hSρ (by positivity)
      linarith
    have : cz * S * (ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy))) =
        cz * (S * ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy))) := by ring
    rw [this]
    calc cz * (S * ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy))) ≤
          31 / 50 * (S * ρ * (2 * X + 2 * ((μ - 1) ^ 2 * Gy))) := mul_le_mul_of_nonneg_right hcz' h0
      _ ≤ _ := by linarith
  have hT6 : θ2 * R2 + cIC * S * η ≤ θ2 * Z := by
    have h1 : cIC * S * η ≤ 2 * θ2 * (2 * S + μ + 1) * η := mul_le_mul_of_nonneg_right hcIC' hη
    rw [hZ]
    linarith
  have hθZ : θ2 * Z ≤ 3 / 5 * Z := by
    apply mul_le_mul_of_nonneg_right hθ'
    rw [hZ]
    have : 0 ≤ 2 * S + μ + 1 := by linarith
    positivity
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    have : 0 ≤ 2 * S + μ + 1 := by linarith
    positivity
  have hRZ : R2 + 2 * (S + 1) * η ≤ Z := by
    rw [hZ]; linarith [mul_nonneg (by linarith : (0:ℝ) ≤ S + μ) hη]
  have hRZ' : R2 + 2 * (2 * S + μ) * η ≤ Z := by rw [hZ]; linarith
  have hX1 : X ≤ (θ2 + 3 / 200) * Z := by
    have hθZ' : 0 ≤ θ2 * Z := mul_nonneg hθ hZ0
    linarith
  have hZL1 : ZL ≤ (1 + 13 / 2000) * Z := by linarith
  have hZC1 : ZC ≤ 41 / 40 * Z := by linarith
  exact ⟨hX1, hZL1, hZC1, hGzb⟩

lemma ref_identity_at (f : E → ℝ) (g : E → E) (hs : List ℝ) (p z r : E)
    (hz : z = run g hs p) :
    primitive f g hs p + defectSum f g r hs p =
      ‖p - (r - g r)‖ ^ 2 - ‖z - (r - g r)‖ ^ 2 - hs.sum * (hs.sum + 1) * ‖g z‖ ^ 2 -
        2 * hs.sum * (f z - f r) - hs.sum * ‖g r‖ ^ 2 := by
  subst hz
  exact reference_identity f g hs p r

noncomputable def θk (k : ℕ) : ℝ := if k < 3 then 3 / 5 else 2 / 5

set_option maxHeartbeats 8000000 in
lemma join_bound {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (_hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖)
    (hD : ∀ u v, -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v))
    {k : ℕ} (hk : 1 ≤ k) {n q A n' q' A' : ℝ} (hn : 50 ≤ n) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hε : ρ * (A + 3 * (steps k).sum * (1 + 2 * (n + q))) ≤ 1 / 200)
    (hB : BlockBound f g ρ k n q A)
    (hn' : 101 / 100 * n ≤ n') (hq' : 101 / 100 * q ≤ q')
    (hA' : A * (1 + 13 / 2000) + (1 + 2 * ratio) * A * (θk k + 3 / 200) +
      ratio * (steps k).sum * (106 / 100 + (3 + 8 * (n + q)) * (θk k + 3 / 200)) +
      ratio * ((ratio - 2) * ((steps k).sum + 1) + 1) * (2 * (θk k + 3 / 200) + 71 / 100) ≤ A') :
    BlockBound f g ρ (k + 1) n' q' A' := by
  intro x e R2 η hη hx hIC
  have hb := ratio_bounds
  obtain ⟨hr, hS1, hμS, hμ1, hμsq⟩ := level_facts k hk
  obtain ⟨S, hSdef⟩ : ∃ S, S = (steps k).sum := ⟨_, rfl⟩
  rw [← hSdef] at hr hS1 hμS hμ1 hμsq hε hA'
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = (ratio - 2) * (S + 1) + 1 := ⟨_, rfl⟩
  rw [← hμdef] at hμS hμ1 hμsq hA'
  have hsteps : steps (k + 1) = steps k ++ [μ] ++ steps k := by
    rw [show steps (k + 1) = steps k ++ [1 + ratio ^ k / ratio] ++ steps k from rfl,
      join_step k, ← hSdef, ← hμdef]
  obtain ⟨y, hy⟩ : ∃ y, y = run g (steps k) x := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = y - μ • g y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = run g (steps k) p := ⟨_, rfl⟩
  have hrun : run g (steps (k + 1)) x = z := by
    rw [hsteps, hz, hp, hy]
    simp only [run_append, run]
  have hsum : (steps (k + 1)).sum = 2 * S + μ := by
    rw [hsteps, hSdef]
    simp only [List.sum_append, List.sum_cons, List.sum_nil]
    ring
  rw [hsum, hrun] at hIC
  rw [hsum, hsteps]
  obtain ⟨c, hc⟩ : ∃ c, c = e - g e := ⟨_, rfl⟩
  rw [← hc] at hx
  rw [← hc]
  obtain ⟨fc, hfc⟩ : ∃ fc, fc = f e - ‖g e‖ ^ 2 / 2 := ⟨_, rfl⟩
  rw [← hfc] at hIC
  have hw : ∀ h ∈ steps k, 0 ≤ h := fun h hh => (steps_positive k h hh).le
  have hS0 : 0 < S := by linarith
  have hR20 : 0 ≤ R2 := le_trans (sq_nonneg _) hx
  set Y := 2 * (n + q) with hYdef
  have hX0 : 0 ≤ (‖p - (z - g z)‖ ^ 2) := sq_nonneg _
  have hGy0 : 0 ≤ ‖g y‖ ^ 2 := sq_nonneg _
  have hGz0 : 0 ≤ ‖g z‖ ^ 2 := sq_nonneg _
  have hY0 : 0 ≤ Y := by rw [hYdef]; linarith
  have hICR : -(1 / 10) * (steps k).sum * ‖g (run g (steps k) p)‖ ^ 2 - 0 ≤
      f (run g (steps k) p) - (f z - ‖g z‖ ^ 2 / 2) := by
    rw [← hz, ← hSdef]
    have : 0 ≤ S * ‖g z‖ ^ 2 := mul_nonneg hS0.le hGz0
    linarith
  obtain ⟨hRn, hRP⟩ := hB p z (‖p - (z - g z)‖ ^ 2) 0 le_rfl le_rfl hICR
  simp only [mul_zero, add_zero] at hRn hRP
  have hYR : ∀ w ∈ nodes g (steps k) p, ‖(z - g z) - (w - g w)‖ ^ 2 ≤ Y * (‖p - (z - g z)‖ ^ 2) := by
    intro w hm
    obtain ⟨h1, h2⟩ := hRn w hm
    have e : (z - g z) - (w - g w) = -(w - (z - g z)) + g w := by abel
    rw [e]
    have h3 := sq_add_le_two (-(w - (z - g z))) (g w)
    rw [norm_neg] at h3
    rw [hYdef]
    linarith
  have hIz := ref_identity_at f g (steps k) p z z hz
  have hDSz := defectSum_weak hρ hD z (steps k) p hw (Y * (‖p - (z - g z)‖ ^ 2)) hYR
  rw [← hSdef] at hIz
  rw [← hSdef] at hDSz
  have hzz : ‖z - (z - g z)‖ ^ 2 = ‖g z‖ ^ 2 := by rw [sub_sub_cancel]
  rw [hzz] at hIz
  have hGzb : (S + 1) ^ 2 * ‖g z‖ ^ 2 ≤ (‖p - (z - g z)‖ ^ 2) * (1 + ρ * A + ρ * S * Y) := by linarith
  have hpy : p - (y - g y) = -((μ - 1) • g y) := by rw [hp]; module
  have hpyn : ‖p - (y - g y)‖ ^ 2 = (μ - 1) ^ 2 * ‖g y‖ ^ 2 := by
    rw [hpy, norm_neg, norm_smul, Real.norm_of_nonneg hμ1, mul_pow]
  have hMy : ∀ w ∈ nodes g (steps k) p,
      ‖(y - g y) - (w - g w)‖ ^ 2 ≤ 3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)) := by
    intro w hm
    have e : (y - g y) - (w - g w) = -(p - (y - g y)) + (p - (z - g z)) +
        ((z - g z) - (w - g w)) := by abel
    rw [e]
    have h3 := sq_add_le_three (-(p - (y - g y))) (p - (z - g z)) ((z - g z) - (w - g w))
    rw [norm_neg, hpyn] at h3
    have := hYR w hm
    linarith
  have hIy := ref_identity_at f g (steps k) p z y hz
  have hDSy := defectSum_weak hρ hD y (steps k) p hw _ hMy
  rw [← hSdef] at hIy
  rw [← hSdef] at hDSy
  rw [hpyn] at hIy
  have hERy : ‖z - (y - g y)‖ ^ 2 + S * (S + 1) * ‖g z‖ ^ 2 + 2 * S * ((f z - fc) - (f y - fc)) +
      S * ‖g y‖ ^ 2 ≤ (μ - 1) ^ 2 * ‖g y‖ ^ 2 + (ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) := by
    linarith
  have hC1 : (μ - 1) ^ 2 * (1 + 3 * ρ * S) ≤ S + S ^ 2 / 5 := by
    have h3 : 3 * ρ * S ≤ 1 / 200 := by
      linarith [mul_nonneg hρ hA, mul_nonneg hρ (mul_nonneg hS0.le hY0)]
    rw [hμsq]
    exact num_C1 hS1 (mul_nonneg (mul_nonneg (by norm_num) hρ) hS0.le) h3
  obtain ⟨ηL, hηL⟩ : ∃ ηL, ηL = η + ρ * (A + 3 * S * (1 + Y)) * (‖p - (z - g z)‖ ^ 2) / (2 * S) := ⟨_, rfl⟩
  have hηL0 : 0 ≤ ηL := by rw [hηL]; positivity
  have hICy : -(1 / 10) * S * ‖g y‖ ^ 2 - ηL ≤ f y - fc := by
    have h1 : 0 ≤ ‖z - (y - g y)‖ ^ 2 := sq_nonneg _
    have h2 : S * (S + 1) * ‖g z‖ ^ 2 - 2 * S * (1 / 10) * (2 * S + μ) * ‖g z‖ ^ 2 ≥ 0 := by
      have h0 : 0 ≤ S * ‖g z‖ ^ 2 := mul_nonneg hS0.le hGz0
      have h00 : 0 ≤ S * ‖g z‖ ^ 2 * S := mul_nonneg h0 hS0.le
      have h01 : S * ‖g z‖ ^ 2 * μ ≤ S * ‖g z‖ ^ 2 * (3 / 2 * S) := mul_le_mul_of_nonneg_left hμS h0
      linarith
    have h3 : (μ - 1) ^ 2 * ‖g y‖ ^ 2 * (1 + 3 * ρ * S) ≤ (S + S ^ 2 / 5) * ‖g y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hC1 hGy0
      linarith
    have hIC2 := mul_le_mul_of_nonneg_left hIC (by linarith : (0:ℝ) ≤ 2 * S)
    have key : 2 * S * (f y - fc) ≥ -(S ^ 2 / 5) * ‖g y‖ ^ 2 - 2 * S * η -
        ρ * (A + 3 * S * (1 + Y)) * (‖p - (z - g z)‖ ^ 2) := by linarith
    have hdiv : 2 * S * (ρ * (A + 3 * S * (1 + Y)) * (‖p - (z - g z)‖ ^ 2) / (2 * S)) =
        ρ * (A + 3 * S * (1 + Y)) * (‖p - (z - g z)‖ ^ 2) := by field_simp
    have hT : 0 ≤ 2 * S * ((f y - fc) + 1 / 10 * S * ‖g y‖ ^ 2 + ηL) := by
      rw [hηL, mul_add, mul_add, mul_add, hdiv]
      linarith
    have hT' := (mul_nonneg_iff_of_pos_left (by linarith : (0:ℝ) < 2 * S)).mp hT
    linarith
  have hICL : -(1 / 10) * (steps k).sum * ‖g (run g (steps k) x)‖ ^ 2 - ηL ≤
      f (run g (steps k) x) - (f e - ‖g e‖ ^ 2 / 2) := by
    rw [← hy, ← hSdef, ← hfc]
    exact hICy
  have hxL : ‖x - (e - g e)‖ ^ 2 ≤ R2 := by rw [← hc]; exact hx
  obtain ⟨hLn, hLP⟩ := hB x e R2 ηL hηL0 hxL hICL
  rw [← hSdef, ← hc] at hLn
  rw [← hSdef] at hLP
  obtain ⟨ZL, hZL⟩ : ∃ ZL, ZL = R2 + 2 * (S + 1) * ηL := ⟨_, rfl⟩
  rw [← hZL] at hLn hLP
  have hZL0 : 0 ≤ ZL := by rw [hZL]; positivity
  have hYL : ∀ w ∈ nodes g (steps k) x, ‖(e - g e) - (w - g w)‖ ^ 2 ≤ Y * ZL := by
    intro w hm
    obtain ⟨h1, h2⟩ := hLn w hm
    have e1 : (e - g e) - (w - g w) = -(w - c) + g w := by rw [hc]; abel
    rw [e1]
    have h3 := sq_add_le_two (-(w - c)) (g w)
    rw [norm_neg] at h3
    rw [hYdef]
    linarith
  have hymem : y ∈ nodes g (steps k) x := by rw [hy]; exact run_mem_nodes g (steps k) x
  have hIe := ref_identity_at f g (steps k) x y e hy
  have hDSe := defectSum_weak hρ hD e (steps k) x hw _ hYL
  rw [← hSdef, ← hc] at hIe
  rw [← hSdef] at hDSe
  have hEL : ‖y - c‖ ^ 2 + S * (S + 1) * ‖g y‖ ^ 2 + 2 * S * (f y - fc) ≤
      R2 + ρ * (A + S * Y) * ZL := by
    rw [hfc]
    linarith
  have hcy0 := hD e y
  rw [anchor_defect, ← hc, ← hfc] at hcy0
  have hcyb : ‖(e - g e) - (y - g y)‖ ^ 2 ≤ Y * ZL := hYL y hymem
  rw [← hc] at hcyb
  have hcy : -(ρ * Y * ZL) ≤ -2 * (f y - fc) + 2 * ⟪g y, y - c⟫ - ‖g y‖ ^ 2 := by
    linarith [mul_le_mul_of_nonneg_left hcyb hρ]
  have hGyb : (S * (S + 1) - S ^ 2 / 5) * ‖g y‖ ^ 2 ≤ ZL * (1 + ρ * (A + S * Y)) := by
    have h1 : 0 ≤ ‖y - c‖ ^ 2 := sq_nonneg _
    have h2 : 2 * S * ηL ≤ 2 * (S + 1) * ηL := by linarith
    have h3 := mul_le_mul_of_nonneg_left hICy (by linarith : (0:ℝ) ≤ 2 * S)
    rw [hZL] at hEL ⊢
    linarith
  have hSa : 14142 / 10000 ≤ S := by linarith [hb.1]
  have hC4 : (μ - 1) ^ 2 * (1 + ρ * (A + S * Y)) ≤ 7 / 20 * (S * (S + 1) - S ^ 2 / 5) := by
    have h3 : ρ * (A + S * Y) ≤ 1 / 200 := by
      linarith [mul_nonneg hρ hS0.le, mul_nonneg hρ (mul_nonneg hS0.le hY0)]
    rw [hμsq]
    exact num_C4 hSa (mul_nonneg hρ (add_nonneg hA (mul_nonneg hS0.le hY0))) h3
  have hGy' : (μ - 1) ^ 2 * ‖g y‖ ^ 2 ≤ 7 / 20 * ZL := by
    have hpos : 0 < S * (S + 1) - S ^ 2 / 5 := by linarith [sq_nonneg S]
    have h1 : (μ - 1) ^ 2 * ‖g y‖ ^ 2 * (S * (S + 1) - S ^ 2 / 5) ≤
        (μ - 1) ^ 2 * (ZL * (1 + ρ * (A + S * Y))) := by
      have := mul_le_mul_of_nonneg_left hGyb (sq_nonneg (μ - 1))
      linarith
    have h2 : (μ - 1) ^ 2 * (ZL * (1 + ρ * (A + S * Y))) ≤
        7 / 20 * (S * (S + 1) - S ^ 2 / 5) * ZL := by
      have := mul_le_mul_of_nonneg_right hC4 hZL0
      linarith
    have h3 : (μ - 1) ^ 2 * ‖g y‖ ^ 2 * (S * (S + 1) - S ^ 2 / 5) ≤
        7 / 20 * ZL * (S * (S + 1) - S ^ 2 / 5) := by linarith
    exact le_of_mul_le_mul_right h3 hpos
  have hpc : p - c = (y - c) - μ • g y := by rw [hp]; abel
  have hC3 : S * (S + 1) + μ - μ ^ 2 - (S + μ) * S / 5 ≥ 0 := by
    rw [hμdef]
    exact num_C3 hSa
  have hPC : ‖p - c‖ ^ 2 ≤ R2 + 2 * (S + μ) * ηL + ρ * (A + S * Y) * ZL + μ * ρ * Y * ZL := by
    rw [hpc, norm_sub_sq_real, norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ μ),
      inner_smul_right, mul_pow, real_inner_comm]
    have h1 := mul_le_mul_of_nonneg_left hcy (by linarith : (0:ℝ) ≤ μ)
    have h2 := mul_le_mul_of_nonneg_left hICy (by linarith : (0:ℝ) ≤ 2 * (S + μ))
    have h3 := mul_nonneg hC3 hGy0
    linarith
  have hzy0 := hD z y
  have hzyb : ‖(z - g z) - (y - g y)‖ ^ 2 ≤ 2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2) := by
    have e1 : (z - g z) - (y - g y) = -(p - (z - g z)) + (p - (y - g y)) := by abel
    rw [e1]
    have := sq_add_le_two (-(p - (z - g z))) (p - (y - g y))
    rw [norm_neg, hpyn] at this
    linarith
  have hzy : -(ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2))) ≤
      2 * ((f z - fc) - (f y - fc)) - 2 * ⟪g y, (z - c) - (y - c)⟫ - ‖g z - g y‖ ^ 2 := by
    have e1 : (z - c) - (y - c) = z - y := by abel
    rw [e1]
    simp only [defect] at hzy0
    linarith [mul_le_mul_of_nonneg_left hzyb hρ]
  have hMe : ∀ w ∈ nodes g (steps k) p,
      ‖(e - g e) - (w - g w)‖ ^ 2 ≤ 3 * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2)) := by
    intro w hm
    have e1 : (e - g e) - (w - g w) = -(z - c) + g z + ((z - g z) - (w - g w)) := by
      rw [hc]; abel
    rw [e1]
    have h3 := sq_add_le_three (-(z - c)) (g z) ((z - g z) - (w - g w))
    rw [norm_neg] at h3
    have := hYR w hm
    linarith
  have hIc := ref_identity_at f g (steps k) p z e hz
  have hDSc := defectSum_weak hρ hD e (steps k) p hw _ hMe
  rw [← hSdef, ← hc] at hIc
  rw [← hSdef] at hDSc
  have hERc : ‖z - c‖ ^ 2 + S * (S + 1) * ‖g z‖ ^ 2 + 2 * S * (f z - fc) ≤
      ‖p - c‖ ^ 2 + (ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2))) := by
    rw [hfc]
    linarith
  have hZC : ‖z - c‖ ^ 2 * (1 - 3 * S * ρ) ≤ ‖p - c‖ ^ 2 + 2 * S * η + ρ * A * (‖p - (z - g z)‖ ^ 2) +
      3 * S * ρ * ‖g z‖ ^ 2 + 3 * S * ρ * Y * (‖p - (z - g z)‖ ^ 2) := by
    have h1 : S * (S + 1) * ‖g z‖ ^ 2 - 2 * S * (1 / 10) * (2 * S + μ) * ‖g z‖ ^ 2 - 3 * S * ρ * ‖g z‖ ^ 2 ≥ 0 := by
      have h3 : 3 * ρ ≤ 1 / 200 := by
        linarith [mul_nonneg hρ hA, mul_nonneg hρ (mul_nonneg hS0.le hY0),
          mul_nonneg hρ (by linarith : (0:ℝ) ≤ S - 1)]
      have h0 : 0 ≤ S * ‖g z‖ ^ 2 := mul_nonneg hS0.le hGz0
      have h00 : 0 ≤ S * ‖g z‖ ^ 2 * S := mul_nonneg h0 hS0.le
      have h01 : S * ‖g z‖ ^ 2 * μ ≤ S * ‖g z‖ ^ 2 * (3 / 2 * S) := mul_le_mul_of_nonneg_left hμS h0
      have h02 : S * ‖g z‖ ^ 2 * (3 * ρ) ≤ S * ‖g z‖ ^ 2 * (1 / 200) := mul_le_mul_of_nonneg_left h3 h0
      linarith
    have h2 := mul_le_mul_of_nonneg_left hIC (by linarith : (0:ℝ) ≤ 2 * S)
    have h3 := mul_nonneg (mul_nonneg hS0.le hρ) hGz0
    linarith
  have hpz : p - (z - g z) = (y - c) - μ • g y - ((z - c) - g z) := by rw [hp]; abel
  have hθ : (‖p - (z - g z)‖ ^ 2) ≤ θk k * R2 + 3 / 5 * (ρ * (A + S * Y) * ZL) +
      1 / 5 * (ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2))) +
      34 / 25 * (ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) +
      7 / 50 * S * (ρ * Y * ZL) + 31 / 50 * S * (ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2))) +
      2 * θk k * (2 * S + μ + 1) * η := by
    have hμ' : μ = 1 + (ratio - 2) * (S + 1) := by rw [hμdef]; ring
    have hS' : 2 * S + μ = ratio * (S + 1) - 1 := by rw [hμdef]; ring
    have hEL' : ‖y - c‖ ^ 2 + S * (S + 1) * ‖g y‖ ^ 2 + 2 * S * (f y - fc) ≤
        R2 + ρ * (A + S * Y) * ZL := hEL
    have hERc' : ‖z - c‖ ^ 2 + S * (S + 1) * ‖g z‖ ^ 2 + 2 * S * (f z - fc) ≤
        ‖(y - c) - (1 + (ratio - 2) * (S + 1)) • g y‖ ^ 2 +
          (ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2))) := by
      rw [← hμ', ← hpc]; exact hERc
    have hERy' : ‖(z - c) - ((y - c) - g y)‖ ^ 2 + S * (S + 1) * ‖g z‖ ^ 2 +
        2 * S * ((f z - fc) - (f y - fc)) + S * ‖g y‖ ^ 2 ≤
        ((1 + (ratio - 2) * (S + 1)) - 1) ^ 2 * ‖g y‖ ^ 2 +
          (ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) := by
      have e1 : (z - c) - ((y - c) - g y) = z - (y - g y) := by abel
      rw [e1, ← hμ']; exact hERy
    have hcy' : -(ρ * Y * ZL) ≤ -2 * (f y - fc) + 2 * ⟪g y, y - c⟫ - ‖g y‖ ^ 2 := hcy
    have hzy' : -(ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2))) ≤
        2 * ((f z - fc) - (f y - fc)) - 2 * ⟪g y, (z - c) - (y - c)⟫ - ‖g z - g y‖ ^ 2 := hzy
    have hIC' : -(1 / 10) * (ratio * (S + 1) - 1) * ‖g z‖ ^ 2 - η ≤ f z - fc := by
      rw [← hS']; exact hIC
    have hXe : (‖p - (z - g z)‖ ^ 2) = ‖(y - c) - (1 + (ratio - 2) * (S + 1)) • g y - ((z - c) - g z)‖ ^ 2 := by
      rw [hpz, hμ']
    unfold θk
    split_ifs with hk3
    · have hs1 : ratio ≤ S + 1 := hr
      have := scale_decay_three_fifths (y - c) (g y) (z - c) (g z) S R2 (f y - fc) (f z - fc) η
        (ρ * (A + S * Y) * ZL) (ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2)))
        (ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) (ρ * Y * ZL)
        (ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2))) hs1 hEL' hERc' hERy' hcy' hzy' hIC'
      rw [← hXe] at this
      have hS'' : 41 / 25 * S * η ≤ 2 * (3 / 5) * (2 * S + μ + 1) * η := by
        apply mul_le_mul_of_nonneg_right _ hη; linarith
      have hpos : 0 ≤ ρ * (A + S * Y) * ZL := by positivity
      have hpos2 : 0 ≤ ρ * Y * ZL := by positivity
      have hpos3 : 0 ≤ ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2)) := by positivity
      have hpos4 : 0 ≤ ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2))) := by positivity
      have hpos5 : 0 ≤ ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2)) := by positivity
      have hp6 := mul_nonneg hS0.le hpos2
      have hp7 := mul_nonneg hS0.le hpos5
      linarith
    · have hs3 : ratio ^ 3 ≤ S + 1 := by
        rw [hSdef, steps_sum k, sub_add_cancel]
        exact pow_le_pow_right₀ (by linarith) (by omega)
      have := scale_decay_two_fifths (y - c) (g y) (z - c) (g z) S R2 (f y - fc) (f z - fc) η
        (ρ * (A + S * Y) * ZL) (ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2)))
        (ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) (ρ * Y * ZL)
        (ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2))) hs3 hEL' hERc' hERy' hcy' hzy' hIC'
      rw [← hXe] at this
      have hS'' : 36 / 25 * S * η ≤ 2 * (2 / 5) * (2 * S + μ + 1) * η := by
        apply mul_le_mul_of_nonneg_right _ hη; linarith
      have hpos : 0 ≤ ρ * (A + S * Y) * ZL := by positivity
      have hpos2 : 0 ≤ ρ * Y * ZL := by positivity
      have hpos3 : 0 ≤ ρ * A * (‖p - (z - g z)‖ ^ 2) + 3 * S * ρ * (‖z - c‖ ^ 2 + ‖g z‖ ^ 2 + Y * (‖p - (z - g z)‖ ^ 2)) := by positivity
      have hpos4 : 0 ≤ ρ * A * (‖p - (z - g z)‖ ^ 2) + S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2))) := by positivity
      have hpos5 : 0 ≤ ρ * (2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2)) := by positivity
      have hp6 := mul_nonneg hS0.le hpos2
      have hp7 := mul_nonneg hS0.le hpos5
      linarith
  have hθ0 : 0 ≤ θk k := by unfold θk; split_ifs <;> norm_num
  have hθ1 : θk k ≤ 3 / 5 := by unfold θk; split_ifs <;> norm_num
  have hεY : ρ * (A + 3 * S * (1 + Y)) ≤ 1 / 200 := by rw [hYdef]; exact hε
  obtain ⟨hX1, hZL1, hZC1, hGz1⟩ := join_scalar (S := S) (μ := μ) (ρ := ρ) (A := A) (Y := Y)
    (X := ‖p - (z - g z)‖ ^ 2) (R2 := R2) (η := η) (ZL := ZL) (Gy := ‖g y‖ ^ 2)
    (Gz := ‖g z‖ ^ 2) (PC := ‖p - c‖ ^ 2)
    (ZC := ‖z - c‖ ^ 2) (θ2 := θk k) (cL := 3 / 5) (cR := 1 / 5) (cRy := 34 / 25)
    (cc := 7 / 50) (cz := 31 / 50) (cIC := 2 * θk k * (2 * S + μ + 1) / S)
    hS1 hμS (by linarith) hr hρ hA hY0 hX0 hη hR20 hGy0 hGz0 (sq_nonneg _) hεY
    (by rw [hZL, hηL]) hGy' hGzb (by rw [← hηL]; exact hPC) hZC
    (by
      have : 2 * θk k * (2 * S + μ + 1) / S * S * η = 2 * θk k * (2 * S + μ + 1) * η := by
        field_simp
      rw [this]; exact hθ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hθ0 hθ1
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ0) (by linarith)) hS0.le)
    (by rw [div_mul_cancel₀ _ hS0.ne'])
  set Z := R2 + 2 * (2 * S + μ + 1) * η with hZdef
  have hZ0 : 0 ≤ Z := by
    rw [hZdef]
    have : 0 ≤ 2 * S + μ + 1 := by linarith
    positivity
  refine ⟨?_, ?_⟩
  · intro w hm
    rcases nodes_join_cases g (steps k) μ x w hm with hL | hR
    · obtain ⟨h1, h2⟩ := hLn w hL
      have hn0 : 0 ≤ n := by linarith
      constructor
      · calc ‖w - c‖ ^ 2 ≤ n * ZL := h1
          _ ≤ n * ((1 + 13 / 2000) * Z) := mul_le_mul_of_nonneg_left hZL1 hn0
          _ ≤ n' * Z := by
            have := mul_le_mul_of_nonneg_right hn' hZ0
            have := mul_nonneg hn0 hZ0
            linarith
      · calc ‖g w‖ ^ 2 ≤ q * ZL := h2
          _ ≤ q * ((1 + 13 / 2000) * Z) := mul_le_mul_of_nonneg_left hZL1 hq
          _ ≤ q' * Z := by
            have := mul_le_mul_of_nonneg_right hq' hZ0
            have := mul_nonneg hq hZ0
            linarith
    · rw [← hy, ← hp] at hR
      obtain ⟨h1, h2⟩ := hRn w hR
      constructor
      · have e1 : w - c = (w - (z - g z)) + ((z - c) + -g z) := by abel
        rw [e1]
        have hy1 := sq_add_le_young (w - (z - g z)) ((z - c) + -g z) (l := 1 / 4) (by norm_num)
        have hy2 := sq_add_le_young (z - c) (-g z) (l := 1 / 3) (by norm_num)
        rw [norm_neg] at hy2
        have hn0 : 0 ≤ n := by linarith
        have h3 : n * (‖p - (z - g z)‖ ^ 2) ≤ n * ((θk k + 3 / 200) * Z) := mul_le_mul_of_nonneg_left hX1 hn0
        have h4 : n * ((θk k + 3 / 200) * Z) ≤ n * (123 / 200 * Z) := by
          apply mul_le_mul_of_nonneg_left _ hn0
          apply mul_le_mul_of_nonneg_right _ hZ0
          linarith
        have h5 : ‖g z‖ ^ 2 ≤ 1 / 5 * (123 / 200 * Z) := by
          have := mul_le_mul_of_nonneg_right hθ1 hZ0
          linarith
        have h6 := mul_le_mul_of_nonneg_right hn' hZ0
        have h7 := mul_le_mul_of_nonneg_right hn hZ0
        linarith
      · have h3 : q * (‖p - (z - g z)‖ ^ 2) ≤ q * ((θk k + 3 / 200) * Z) := mul_le_mul_of_nonneg_left hX1 hq
        have h4 : q * ((θk k + 3 / 200) * Z) ≤ q * Z := by
          apply mul_le_mul_of_nonneg_left _ hq
          have := mul_le_mul_of_nonneg_right hθ1 hZ0
          linarith
        have h6 := mul_le_mul_of_nonneg_right hq' hZ0
        have h7 := mul_nonneg hq hZ0
        linarith
  · have hj := primitive_join f g (steps k) x
    dsimp only at hj
    rw [← hSdef, ← hμdef, ← hy, ← hp, ← hz] at hj
    rw [hj]
    have hyz := hD y z
    have hzy1 := hD z y
    have hyzb : ‖(y - g y) - (z - g z)‖ ^ 2 ≤ 2 * (‖p - (z - g z)‖ ^ 2) + 2 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2) := by
      rw [← norm_neg, neg_sub]; exact hzyb
    have hDSy' := hDSy
    have hDSz' := hDSz
    have hP1 : -(ρ * A * ZL) ≤ primitive f g (steps k) x := hLP
    have hr0 : 0 ≤ 1 + 2 * ratio := by linarith
    have hm1 : (1 + 2 * ratio) * (-(ρ * A * (‖p - (z - g z)‖ ^ 2))) ≤ (1 + 2 * ratio) * primitive f g (steps k) p :=
      mul_le_mul_of_nonneg_left hRP hr0
    have hm2 : ratio * (-S * (ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) + -S * (ρ * (Y * (‖p - (z - g z)‖ ^ 2)))) ≤
        ratio * (defectSum f g y (steps k) p + defectSum f g z (steps k) p) :=
      mul_le_mul_of_nonneg_left (add_le_add hDSy hDSz) (by linarith)
    have hm3 : ratio * (-ρ * ‖(y - g y) - (z - g z)‖ ^ 2) ≤
        ratio * defect (f y) (f z) y z (g y) (g z) := mul_le_mul_of_nonneg_left hyz (by linarith)
    have hm4 : ratio * (μ - 1) * (-ρ * ‖(z - g z) - (y - g y)‖ ^ 2) ≤
        ratio * (μ - 1) * defect (f z) (f y) z y (g z) (g y) :=
      mul_le_mul_of_nonneg_left hzy1 (mul_nonneg (by linarith) hμ1)
    have hb1 : ρ * A * ZL ≤ ρ * A * ((1 + 13 / 2000) * Z) :=
      mul_le_mul_of_nonneg_left hZL1 (mul_nonneg hρ hA)
    have hb2 : ρ * A * (‖p - (z - g z)‖ ^ 2) ≤ ρ * A * ((θk k + 3 / 200) * Z) :=
      mul_le_mul_of_nonneg_left hX1 (mul_nonneg hρ hA)
    have hGyZ : (μ - 1) ^ 2 * ‖g y‖ ^ 2 ≤ 7 / 20 * ((1 + 13 / 2000) * Z) := by linarith
    have hb3 : ρ * ‖(y - g y) - (z - g z)‖ ^ 2 ≤
        ρ * (2 * ((θk k + 3 / 200) * Z) + 2 * (7 / 20 * ((1 + 13 / 2000) * Z))) := by
      apply mul_le_mul_of_nonneg_left _ hρ; linarith
    have hb4 : ρ * ‖(z - g z) - (y - g y)‖ ^ 2 ≤
        ρ * (2 * ((θk k + 3 / 200) * Z) + 2 * (7 / 20 * ((1 + 13 / 2000) * Z))) := by
      apply mul_le_mul_of_nonneg_left _ hρ; linarith
    have hb5 : S * (ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) + S * (ρ * (Y * (‖p - (z - g z)‖ ^ 2))) ≤
        S * ρ * (106 / 100 * Z + (3 + 4 * Y) * ((θk k + 3 / 200) * Z)) := by
      have e1 : S * (ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2 + (‖p - (z - g z)‖ ^ 2) + Y * (‖p - (z - g z)‖ ^ 2)))) + S * (ρ * (Y * (‖p - (z - g z)‖ ^ 2))) =
          S * ρ * (3 * ((μ - 1) ^ 2 * ‖g y‖ ^ 2) + (3 + 4 * Y) * (‖p - (z - g z)‖ ^ 2)) := by ring
      rw [e1]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hS0.le hρ)
      have h1 : (3 + 4 * Y) * (‖p - (z - g z)‖ ^ 2) ≤ (3 + 4 * Y) * ((θk k + 3 / 200) * Z) :=
        mul_le_mul_of_nonneg_left hX1 (by linarith)
      linarith
    have hfin : ρ * A * ((1 + 13 / 2000) * Z) + (1 + 2 * ratio) * (ρ * A * ((θk k + 3 / 200) * Z)) +
        ratio * (S * ρ * (106 / 100 * Z + (3 + 4 * Y) * ((θk k + 3 / 200) * Z))) +
        (ratio + ratio * (μ - 1)) *
          (ρ * (2 * ((θk k + 3 / 200) * Z) + 2 * (7 / 20 * ((1 + 13 / 2000) * Z)))) ≤
        ρ * A' * Z := by
      have e1 : ρ * A * ((1 + 13 / 2000) * Z) + (1 + 2 * ratio) * (ρ * A * ((θk k + 3 / 200) * Z)) +
          ratio * (S * ρ * (106 / 100 * Z + (3 + 4 * Y) * ((θk k + 3 / 200) * Z))) +
          (ratio + ratio * (μ - 1)) *
            (ρ * (2 * ((θk k + 3 / 200) * Z) + 2 * (7 / 20 * ((1 + 13 / 2000) * Z)))) =
          ρ * Z * (A * (1 + 13 / 2000) + (1 + 2 * ratio) * A * (θk k + 3 / 200) +
            ratio * S * (106 / 100 + (3 + 4 * Y) * (θk k + 3 / 200)) +
            ratio * μ * (2 * (θk k + 3 / 200) + 7 / 10 * (1 + 13 / 2000))) := by ring
      rw [e1]
      have h1 : A * (1 + 13 / 2000) + (1 + 2 * ratio) * A * (θk k + 3 / 200) +
            ratio * S * (106 / 100 + (3 + 4 * Y) * (θk k + 3 / 200)) +
            ratio * μ * (2 * (θk k + 3 / 200) + 7 / 10 * (1 + 13 / 2000)) ≤ A' := by
        have hμ0 : 0 ≤ ratio * μ := mul_nonneg (by linarith) (by linarith)
        have : ratio * μ * (7 / 10 * (1 + 13 / 2000)) ≤ ratio * μ * (71 / 100) :=
          mul_le_mul_of_nonneg_left (by norm_num) hμ0
        rw [hYdef]
        linarith
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hρ hZ0)
      linarith
    have hb2' := mul_le_mul_of_nonneg_left hb2 hr0
    have hb3' := mul_le_mul_of_nonneg_left hb3 (by linarith : (0:ℝ) ≤ ratio)
    have hb4' := mul_le_mul_of_nonneg_left hb4 (mul_nonneg (by linarith : (0:ℝ) ≤ ratio) hμ1)
    have hb5' := mul_le_mul_of_nonneg_left hb5 (by linarith : (0:ℝ) ≤ ratio)
    linarith

end LongTails.Proofs.WeaklyConvexSilverJoin
