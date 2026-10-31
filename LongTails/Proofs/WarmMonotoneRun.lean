import LongTails.Algorithms.WarmAnchoredMonotone
import LongTails.Proofs.MonotoneRadialSupport

open scoped RealInnerProductSpace

namespace OracleTemplate.WarmAnchoredMonotone

open GeneralizedMonotone MonotoneRadialSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma scale_bounds {L1 R : ℝ} (hC : 1 ≤ L1 * R) :
    1 ≤ warmScale L1 R ∧ warmScale L1 R ≤ L1 * R := by
  constructor
  · exact Real.one_le_rpow hC (by norm_num)
  · have hh := Real.rpow_le_rpow_of_exponent_le hC (show (1 : ℝ) / 3 ≤ 1 by norm_num)
    simpa [warmScale] using hh

lemma scale_power {C : ℝ} (hC : 0 < C) :
    C ^ ((4 : ℝ) / 3) * (C ^ ((1 : ℝ) / 3)) ^ 2 = C ^ 2 := by
  rw [← Real.rpow_mul_natCast hC.le, ← Real.rpow_add hC]
  norm_num

lemma warm_parameters {L1 R : ℝ} (hL1 : 0 ≤ L1) (hR : 0 ≤ R) (hC : 1 ≤ L1 * R) :
    0 < L1 ∧ 0 < R ∧ 0 < warmScale L1 R / L1 ∧ warmScale L1 R / L1 ≤ R ∧
      R ^ 2 < (warmLimit L1 R : ℝ) * (warmScale L1 R / L1) ^ 2 / 4 := by
  have hLp : 0 < L1 := by nlinarith
  have hRp : 0 < R := by nlinarith
  obtain ⟨hs1, hsC⟩ := scale_bounds hC
  have hsp : 0 < warmScale L1 R := by linarith
  have ht : 0 < warmScale L1 R / L1 := div_pos hsp hLp
  have htR : warmScale L1 R / L1 ≤ R := (div_le_iff₀ hLp).mpr (by nlinarith)
  refine ⟨hLp, hRp, ht, htR, ?_⟩
  have hn : 4 * (L1 * R) ^ ((4 : ℝ) / 3) < (warmLimit L1 R : ℝ) := by
    rw [warmLimit, ite_eq_left hC]
    have hh := Nat.le_ceil (4 * (L1 * R) ^ ((4 : ℝ) / 3))
    push_cast
    linarith
  have he : (L1 * R) ^ ((4 : ℝ) / 3) * (warmScale L1 R / L1) ^ 2 = R ^ 2 := by
    have hh := scale_power (show 0 < L1 * R by positivity)
    change (L1 * R) ^ ((4 : ℝ) / 3) * warmScale L1 R ^ 2 = (L1 * R) ^ 2 at hh
    field_simp
    nlinarith
  have hm := mul_lt_mul_of_pos_right hn (sq_pos_of_pos ht)
  nlinarith

lemma warm_step {F : E → E} {L0 L1 R : ℝ} (h : Hyp F L0 L1)
    {u x : E} (hu : F u = 0) (hR : 0 ≤ R) (hC : 1 ≤ L1 * R)
    (hd : ‖x - u‖ ≤ R) (hbig : warmThreshold L0 L1 R < ‖F x‖) :
    ‖warmNext L0 L1 R x (F x) - u‖ ^ 2 ≤
      ‖x - u‖ ^ 2 - (warmScale L1 R / L1) ^ 2 / 4 := by
  obtain ⟨hLp, hRp, ht, htR, _⟩ := warm_parameters h.L1_nonneg hR hC
  have hs : L1 * (warmScale L1 R / L1) = warmScale L1 R :=
    mul_div_cancel₀ _ (ne_of_gt hLp)
  have hb : 8 * L0 * R * Real.exp (2 * L1 * (warmScale L1 R / L1)) ≤ ‖F x‖ := by
    rw [mul_assoc 2 L1, hs]
    exact hbig.le
  have hi := large_residual_alignment h hu hRp hd ht.le htR hb
  have hg : 0 < ‖F x‖ := by
    have hL0 := h.L0_pos
    have hh : 0 < warmThreshold L0 L1 R := by unfold warmThreshold; positivity
    linarith
  have hh := normalized_step_drop hg ht.le hi
  rw [warmNext, ite_eq_left hbig]
  convert hh using 1
  congr 2
  field_simp

noncomputable def warmRun (F : E → E) (L0 L1 R : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | n + 1 => warmNext L0 L1 R (warmRun F L0 L1 R x0 n) (F (warmRun F L0 L1 R x0 n))

lemma warmRun_distance {F : E → E} {L0 L1 R : ℝ} (h : Hyp F L0 L1)
    {u x0 : E} (hu : F u = 0) (hR : 0 ≤ R) (hC : 1 ≤ L1 * R)
    (hd : ‖x0 - u‖ ≤ R) (n : ℕ) : ‖warmRun F L0 L1 R x0 n - u‖ ≤ R := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [warmRun]
    by_cases hb : warmThreshold L0 L1 R < ‖F (warmRun F L0 L1 R x0 n)‖
    · have hh := warm_step h hu hR hC ih hb
      have hn := norm_nonneg (warmNext L0 L1 R (warmRun F L0 L1 R x0 n)
        (F (warmRun F L0 L1 R x0 n)) - u)
      have hn' := norm_nonneg (warmRun F L0 L1 R x0 n - u)
      nlinarith [sq_nonneg (warmScale L1 R / L1)]
    · simpa only [warmNext, ite_eq_right hb] using ih

lemma warmRun_frozen (F : E → E) (L0 L1 R : ℝ) (x0 : E) (k : ℕ)
    (hk : ‖F (warmRun F L0 L1 R x0 k)‖ ≤ warmThreshold L0 L1 R) (j : ℕ) :
    warmRun F L0 L1 R x0 (k + j) = warmRun F L0 L1 R x0 k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, warmRun, ih, warmNext, ite_eq_right (not_lt.mpr hk)]

lemma warmRun_threshold {F : E → E} {L0 L1 R : ℝ} (h : Hyp F L0 L1)
    {u x0 : E} (hu : F u = 0) (hR : 0 ≤ R) (hC : 1 ≤ L1 * R)
    (hd : ‖x0 - u‖ ≤ R) :
    ‖F (warmRun F L0 L1 R x0 (warmLimit L1 R))‖ ≤ warmThreshold L0 L1 R := by
  by_contra hfail
  have hf : warmThreshold L0 L1 R < ‖F (warmRun F L0 L1 R x0 (warmLimit L1 R))‖ :=
    lt_of_not_ge hfail
  have hall : ∀ k ≤ warmLimit L1 R,
      warmThreshold L0 L1 R < ‖F (warmRun F L0 L1 R x0 k)‖ := by
    intro k hk
    by_contra hh
    have he := warmRun_frozen F L0 L1 R x0 k (le_of_not_gt hh) (warmLimit L1 R - k)
    rw [Nat.add_sub_of_le hk] at he
    rw [he] at hf
    exact hh hf
  have he : ∀ k ≤ warmLimit L1 R,
      ‖warmRun F L0 L1 R x0 k - u‖ ^ 2 ≤ R ^ 2 - k * (warmScale L1 R / L1) ^ 2 / 4 := by
    intro k hk
    induction k with
    | zero =>
      simp only [warmRun, Nat.cast_zero, zero_mul, zero_div, sub_zero]
      nlinarith [norm_nonneg (x0 - u)]
    | succ k ih =>
      have hi := ih (by omega)
      have hs := warm_step h hu hR hC (warmRun_distance h hu hR hC hd k)
        (hall k (by omega))
      rw [warmRun]
      push_cast
      nlinarith
  have hn := (warm_parameters h.L1_nonneg hR hC).2.2.2.2
  have hh := he (warmLimit L1 R) le_rfl
  nlinarith [sq_nonneg ‖warmRun F L0 L1 R x0 (warmLimit L1 R) - u‖]

lemma warmRun_good {F : E → E} {L0 L1 R : ℝ} (h : Hyp F L0 L1)
    {u x0 : E} (hu : F u = 0) (hR : 0 ≤ R) (hd : ‖x0 - u‖ ≤ R) :
    ‖warmRun F L0 L1 R x0 (warmLimit L1 R) - u‖ ≤ R ∧
    ‖F (warmRun F L0 L1 R x0 (warmLimit L1 R))‖ ≤ warmThreshold L0 L1 R := by
  by_cases hC : 1 ≤ L1 * R
  · exact ⟨warmRun_distance h hu hR hC hd _, warmRun_threshold h hu hR hC hd⟩
  · rw [warmLimit, ite_eq_right hC, warmRun]
    refine ⟨hd, ?_⟩
    have hL0 := h.L0_pos
    have hL1 := h.L1_nonneg
    have hCs : L1 * R ≤ warmScale L1 R :=
      Real.self_le_rpow_of_le_one (mul_nonneg hL1 hR) (le_of_lt (lt_of_not_ge hC)) (by norm_num)
    have hex : Real.exp (2 * L1 * ‖x0 - u‖) ≤ Real.exp (2 * warmScale L1 R) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hd hL1
      nlinarith
    calc
      _ ≤ 2 * L0 * ‖x0 - u‖ * Real.exp (2 * L1 * ‖x0 - u‖) := root_growth h hu x0
      _ ≤ 2 * L0 * R * Real.exp (2 * warmScale L1 R) :=
        mul_le_mul (by nlinarith) hex (by positivity) (by positivity)
      _ ≤ warmThreshold L0 L1 R := by
        unfold warmThreshold
        have hh : 0 ≤ L0 * R * Real.exp (2 * warmScale L1 R) := by positivity
        nlinarith

end OracleTemplate.WarmAnchoredMonotone
