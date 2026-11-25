import LongTails.Proofs.RhoSmoothPhaseTwo

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothUpperRun

open LongTails.Setups.RhoSmoothRadiusConvex LongTails.Algorithms.RhoSmoothThreePhase
open LongTails.Proofs.RhoSmoothLocal LongTails.Proofs.RhoSmoothParams
open LongTails.Proofs.RhoSmoothPhaseOne LongTails.Proofs.RhoSmoothPhaseTwo

lemma weight_rate_step {s m : ℝ} (hs : 0 ≤ s) (hm : 1 ≤ m) (hsm : s * m ≤ 3) :
    (s * (m + 1)) ^ 2 ≤ 9 + 9 * s := by
  have hs3 : s ≤ 3 := by nlinarith
  have h1 : s * (m + 1) ≤ 3 + s := by nlinarith
  have h2 : 0 ≤ s * (m + 1) := by positivity
  nlinarith

section
variable (p : Params) (hp : spec.valid p)
include hp

lemma weight_rate {Γ : ℝ} (hΓ : 0 < Γ) {m : ℕ} (hm : 1 ≤ m)
    (hle : Γ ≤ 72 * p.L0 / (m : ℝ) ^ 2) :
    Γ / (1 + momentum p Γ) ≤ 72 * p.L0 / ((m : ℝ) + 1) ^ 2 := by
  have hL := L0_pos p hp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set s := momentum p Γ with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Γ / (8 * p.L0) := by
    rw [hsdef]; unfold momentum stepSize
    rw [Real.sq_sqrt (by positivity)]; ring
  have hΓs : Γ = 8 * p.L0 * s ^ 2 := by rw [hs2]; field_simp
  have hsm : s * m ≤ 3 := by
    have h1 : (s * m) ^ 2 ≤ 3 ^ 2 := by
      rw [mul_pow, hs2]
      have : Γ * (m : ℝ) ^ 2 ≤ 72 * p.L0 := by
        rw [le_div_iff₀ (by positivity)] at hle; linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).mp h1
  have hkey := weight_rate_step hs hm1 hsm
  rw [div_le_div_iff₀ (by positivity) (by positivity), hΓs]
  nlinarith

end

section
variable (p : Params) (hp : spec.valid p) {f : p.E → ℝ} {g : p.E → p.E}
  (H : Hyp f g p.L0 p.L1 p.ρ) {u : p.E} (hu : IsMinOn f Set.univ u)
include hp H hu

lemma accel_phase (x : p.E) (hx : ‖x - u‖ ≤ p.R)
    (hgap : f x - f u ≤ initialWeight p * p.R ^ 2 / 2) :
    ∀ m : ℕ, ∃ y w Γ b, (trans p g)^[m] (.accel x x (initialWeight p) false) = .accel y w Γ b ∧
      Inv p f g u y w Γ b ∧ (1 ≤ m → nextWeight p Γ b ≤ 72 * p.L0 / (m : ℝ) ^ 2) := by
  have hR := R_pos p hp
  have hL := L0_pos p hp
  intro m
  induction m with
  | zero =>
      refine ⟨x, x, initialWeight p, false, rfl, ⟨?_, ?_, ?_, ?_⟩, fun h => absurd h (by norm_num)⟩
      · show f x - f u + initialWeight p / 2 * ‖x - u‖ ^ 2 ≤ initialWeight p * p.R ^ 2
        have h1 : ‖x - u‖ ^ 2 ≤ p.R ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) hx 2
        have h2 := initialWeight_pos p hp
        nlinarith
      · exact initialWeight_pos p hp
      · exact le_rfl
      · linarith [norm_nonneg (x - u)]
  | succ m ih =>
      obtain ⟨y, w, Γ, b, hs, hI, hrate⟩ := ih
      obtain ⟨hI', -⟩ := inv_step p hp H hu y w Γ b hI _ rfl
      refine ⟨_, _, _, true, ?_, hI', ?_⟩
      · rw [Function.iterate_succ_apply', hs, trans_accel]
      · intro _
        show nextWeight p Γ b / (1 + momentum p (nextWeight p Γ b)) ≤
          72 * p.L0 / ((m + 1 : ℕ) : ℝ) ^ 2
        push_cast
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0
          have h1 : nextWeight p Γ b / (1 + momentum p (nextWeight p Γ b)) ≤ nextWeight p Γ b := by
            have := hI.weight_pos
            have hmom : 0 ≤ momentum p (nextWeight p Γ b) := Real.sqrt_nonneg _
            rw [div_le_iff₀ (by linarith)]; nlinarith
          have h2 := hI.weight_le
          have h3 := initialWeight_le p
          norm_num
          linarith
        · exact weight_rate p hp hI.weight_pos (m := m) hpos (hrate hpos)

lemma accel_accuracy (x : p.E) (hx : ‖x - u‖ ≤ p.R)
    (hgap : f x - f u ≤ initialWeight p * p.R ^ 2 / 2) (m : ℕ) (hm : 1 ≤ m)
    (hmε : 72 * p.L0 * p.R ^ 2 / p.ε ≤ (m : ℝ) ^ 2) :
    f (point ((trans p g)^[m] (.accel x x (initialWeight p) false))) - f u ≤ p.ε := by
  obtain ⟨y, w, Γ, b, hs, hI, hrate⟩ := accel_phase p hp H hu x hx hgap m
  rw [hs]
  show f y - f u ≤ p.ε
  have hε := ε_pos p hp
  have hR := R_pos p hp
  have hL := L0_pos p hp
  have hV := hI.lyap_le
  have hlyap : lyap p f g u (.accel y w Γ b) =
      f y - f u + nextWeight p Γ b / 2 * ‖nextDual p w (g y) Γ b - u‖ ^ 2 := rfl
  rw [hlyap] at hV
  have hpos := hI.weight_pos
  have h1 : f y - f u ≤ nextWeight p Γ b * p.R ^ 2 := by
    have : 0 ≤ nextWeight p Γ b / 2 * ‖nextDual p w (g y) Γ b - u‖ ^ 2 := by positivity
    linarith
  have h2 : nextWeight p Γ b * p.R ^ 2 ≤ 72 * p.L0 / (m : ℝ) ^ 2 * p.R ^ 2 :=
    mul_le_mul_of_nonneg_right (hrate hm) (sq_nonneg _)
  have hm1 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have h3 : 72 * p.L0 / (m : ℝ) ^ 2 * p.R ^ 2 ≤ p.ε := by
    rw [div_le_iff₀ hε] at hmε
    rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
    linarith
  linarith

lemma warm_gap (x : p.E) (hx : ‖x - u‖ ≤ p.R)
    (hrate : f x - f u ≤ threshold p ^ 2 / (16384 * p.L0)) :
    f x - f u ≤ initialWeight p * p.R ^ 2 / 2 := by
  have hR := R_pos p hp
  have hL := L0_pos p hp
  have hG := threshold_pos p hp
  by_cases hcase : threshold p ^ 2 / (8192 * p.L0) / p.R ^ 2 ≤ 8 * p.L0
  · have hw : initialWeight p = threshold p ^ 2 / (8192 * p.L0) / p.R ^ 2 := min_eq_left hcase
    rw [hw]
    have e : threshold p ^ 2 / (8192 * p.L0) / p.R ^ 2 * p.R ^ 2 / 2 =
        threshold p ^ 2 / (16384 * p.L0) := by field_simp; ring
    rw [e]; exact hrate
  · rw [not_le] at hcase
    have hw : initialWeight p = 8 * p.L0 := min_eq_right hcase.le
    rw [hw]
    have hRsmall : p.R ^ 2 < threshold p ^ 2 / (65536 * p.L0 ^ 2) := by
      have h8 : 8 * p.L0 * p.R ^ 2 < threshold p ^ 2 / (8192 * p.L0) := by
        rwa [lt_div_iff₀ (by positivity)] at hcase
      have h9 : 8 * p.L0 * p.R ^ 2 * (8192 * p.L0) < threshold p ^ 2 := by
        rwa [lt_div_iff₀ (by positivity)] at h8
      rw [lt_div_iff₀ (by positivity)]
      have e : p.R ^ 2 * (65536 * p.L0 ^ 2) = 8 * p.L0 * p.R ^ 2 * (8192 * p.L0) := by ring
      linarith
    have hRG : p.R ≤ threshold p / (64 * p.L0) := by
      have h1 : p.R ^ 2 ≤ (threshold p / (64 * p.L0)) ^ 2 := by
        have e : (threshold p / (64 * p.L0)) ^ 2 = threshold p ^ 2 / (4096 * p.L0 ^ 2) := by
          field_simp; ring
        rw [e]
        have : threshold p ^ 2 / (65536 * p.L0 ^ 2) ≤ threshold p ^ 2 / (4096 * p.L0 ^ 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith
        linarith
      exact (pow_le_pow_iff_left₀ hR.le (by positivity) two_ne_zero).mp h1
    have hv : 2 * curv p.L0 p.L1 p.ρ (2 * (threshold p / 16)) * ‖x - u‖ ≤ threshold p / 16 := by
      rw [← curvature_eq]
      have hc : curvature p (2 * (threshold p / 16)) ≤ 2 * p.L0 :=
        curvature_le_of_le p hp (by positivity) (by linarith)
      have hcp := curvature_pos p hp (show (0 : ℝ) ≤ 2 * (threshold p / 16) by positivity)
      have h1 : 2 * curvature p (2 * (threshold p / 16)) * ‖x - u‖ ≤
          2 * (2 * p.L0) * (threshold p / (64 * p.L0)) :=
        mul_le_mul (by linarith) (hx.trans hRG) (norm_nonneg _) (by positivity)
      have e : 2 * (2 * p.L0) * (threshold p / (64 * p.L0)) = threshold p / 16 := by
        field_simp; ring
      linarith
    have hgrow := growth H hu (x - u) (a := threshold p / 16) (by positivity) hv
    rw [add_sub_cancel, ← curvature_eq] at hgrow
    have hc : curvature p (2 * (threshold p / 16)) ≤ 2 * p.L0 :=
      curvature_le_of_le p hp (by positivity) (by linarith)
    have hsq : ‖x - u‖ ^ 2 ≤ p.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have : curvature p (2 * (threshold p / 16)) * ‖x - u‖ ^ 2 ≤ 2 * p.L0 * p.R ^ 2 :=
      mul_le_mul hc hsq (sq_nonneg _) (by positivity)
    nlinarith

lemma run_accuracy (N : ℕ)
    (hN : ⌈p.R ^ 2 / depth p ^ 2⌉₊ + 1 + descentSteps p + ⌈Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε)⌉₊ ≤ N)
    (hx0 : ‖p.x0 - u‖ ≤ p.R) :
    f (point ((trans p g)^[N] (.cut p.x0))) - f u ≤ p.ε := by
  have hR := R_pos p hp
  have hD := depth_pos p hp
  set M := ⌈p.R ^ 2 / depth p ^ 2⌉₊
  have hstart : ‖p.x0 - u‖ ^ 2 ≤ (M : ℝ) * depth p ^ 2 := by
    have h1 : ‖p.x0 - u‖ ^ 2 ≤ p.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx0 2
    have h2 : p.R ^ 2 / depth p ^ 2 ≤ M := Nat.le_ceil _
    have h3 : p.R ^ 2 ≤ (M : ℝ) * depth p ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at h2; linarith
    linarith
  obtain ⟨m1, hm1, z, hz, hgz, hdz⟩ := cut_phase p hp H hu M p.x0 hstart
  have hzR : ‖z - u‖ ≤ p.R := hdz.trans hx0
  set K1 := descentSteps p
  set xb := gdSeq p g z K1
  have hxb := gdSeq_props p hp H hu z K1
  have hxbR : ‖xb - u‖ ≤ p.R := hxb.1.trans hzR
  have hzgap : f z - f u ≤ threshold p * p.R := by
    have h := gap_le_grad p H z hzR
    have : ‖g z‖ * p.R ≤ threshold p * p.R := mul_le_mul_of_nonneg_right hgz.le hR.le
    linarith
  have hrate := gd_rate p hp H hu z hzR hzgap
  have hwarm := warm_gap p hp H hu xb hxbR hrate
  set K2 := ⌈Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε)⌉₊
  set m2 := N - (m1 + 1) - K1
  have hm2 : K2 ≤ m2 := by omega
  have hNsplit : N = m2 + (K1 + (m1 + 1)) := by omega
  rw [hNsplit, Function.iterate_add_apply, Function.iterate_add_apply, hz, descend_exit]
  have hε := ε_pos p hp
  have hL := L0_pos p hp
  have hK2pos : 1 ≤ K2 := by
    have : 0 < Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε) := Real.sqrt_pos.mpr (by positivity)
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.ceil_eq_zero.mp h0
      linarith)
  apply accel_accuracy p hp H hu xb hxbR hwarm m2 (le_trans hK2pos hm2)
  have h1 : Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε) ≤ (m2 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm2)
  have h2 : 0 ≤ Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε) := Real.sqrt_nonneg _
  have h3 := Real.sq_sqrt (show 0 ≤ 72 * p.L0 * p.R ^ 2 / p.ε by positivity)
  nlinarith

end

lemma budget_sufficient (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : ⌈9 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) +
      262144 * (1 + (p.L0 * p.R / threshold p) ^ 2)⌉₊ ≤ N) :
    ⌈p.R ^ 2 / depth p ^ 2⌉₊ + 1 + descentSteps p + ⌈Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε)⌉₊ ≤ N := by
  have hR := R_pos p hp
  have hL := L0_pos p hp
  have hε := ε_pos p hp
  have hG := threshold_pos p hp
  have hD := depth_pos p hp
  set r := ratio p
  have hr : 0 ≤ r := ratio_nonneg p hp
  have hrdef : p.L0 * p.R / threshold p = r := rfl
  rw [hrdef] at hN
  have hA : p.R ^ 2 / depth p ^ 2 ≤ 400 * r ^ 2 := by
    have hDg := depth_ge p hp
    have h1 : (threshold p / (20 * p.L0)) ^ 2 ≤ depth p ^ 2 :=
      pow_le_pow_left₀ (by positivity) hDg 2
    rw [div_le_iff₀ (by positivity), ratio_sq p hp]
    have e : 400 * (p.L0 ^ 2 * p.R ^ 2 / threshold p ^ 2) * (threshold p / (20 * p.L0)) ^ 2 =
        p.R ^ 2 := by field_simp; ring
    have : 400 * (p.L0 ^ 2 * p.R ^ 2 / threshold p ^ 2) * (threshold p / (20 * p.L0)) ^ 2 ≤
        400 * (p.L0 ^ 2 * p.R ^ 2 / threshold p ^ 2) * depth p ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hS : Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε) ≤ 9 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := by
    have e : 72 * p.L0 * p.R ^ 2 / p.ε = 72 * (p.L0 * p.R ^ 2 / p.ε) := by ring
    rw [e, Real.sqrt_mul (by norm_num)]
    have h72 : Real.sqrt 72 ≤ 9 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right h72 (Real.sqrt_nonneg _)
  have hc1 : (⌈p.R ^ 2 / depth p ^ 2⌉₊ : ℝ) ≤ 400 * r ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)
  have hc2 : (descentSteps p : ℝ) ≤ 43 * r + 174763 * r ^ 2 + 2 := by
    unfold descentSteps
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 43 * ratio p + 174763 * ratio p ^ 2 by positivity)
    linarith
  have hc3 : (⌈Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε)⌉₊ : ℝ) ≤
      9 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le.trans (by linarith)
  have hN' : 9 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + 262144 * (1 + r ^ 2) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hsum : ((⌈p.R ^ 2 / depth p ^ 2⌉₊ + 1 + descentSteps p +
      ⌈Real.sqrt (72 * p.L0 * p.R ^ 2 / p.ε)⌉₊ : ℕ) : ℝ) ≤ N := by
    push_cast
    nlinarith [sq_nonneg (r - 1)]
  exact_mod_cast hsum

end LongTails.Proofs.RhoSmoothUpperRun
