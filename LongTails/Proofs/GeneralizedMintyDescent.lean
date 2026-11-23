import LongTails.Algorithms.GeneralizedMintyExtragradient
import LongTails.Proofs.AnchoredExtragradientStep
import LongTails.Proofs.Execution

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedMintyDescent

open LongTails.Setups.GeneralizedLipschitzMinty
open LongTails.Algorithms.GeneralizedMintyExtragradient

noncomputable def cycle (p : Params) (F : E p → E p) (x : E p) : E p :=
  let η := stepSize p (F x)
  x - η • F (x - η • F x)

lemma freeze (p : Params) (F : E p → E p) (x : E p) (h : ‖F x‖ ≤ p.ε) :
    cycle p F x = x := by simp [cycle, stepSize, h]

lemma decrease (p : Params) (hp : spec.valid p) (F : E p → E p)
    (hc : Continuous F) (hreg : LongTails.Setups.MirrorGeneralizedSmooth.SegmentSmooth F p.L0 p.L1) (x z : E p)
    (hm : ∀ y, 0 ≤ ⟪F y, y - z⟫) (hx : p.ε < ‖F x‖) :
    ‖cycle p F x - z‖ ^ 2 + (4 * (p.L0 / p.ε + p.L1))⁻¹ ^ 2 / 2 ≤ ‖x - z‖ ^ 2 := by
  obtain ⟨h0, h1, _, he⟩ := hp
  let v := F x
  let η := (4 * (p.L0 + p.L1 * ‖v‖))⁻¹
  let y := x - η • v
  let w := F y
  have ha : 0 < p.L0 + p.L1 * ‖v‖ := by positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hunit : 4 * η * (p.L0 + p.L1 * ‖v‖) = 1 := by dsimp [η]; field_simp
  have hd : ‖x - y‖ = η * ‖v‖ := by
    simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hshort : p.L1 * ‖x - y‖ ≤ 1 / 4 := by
    rw [hd]
    nlinarith [mul_nonneg hη.le h0.le]
  have hloc := GeneralizedMonotone.local_bound h0.le h1 hc hreg x y (by linarith)
  have hdiff : ‖v - w‖ ≤ ‖v‖ / 2 := by
    change ‖v - w‖ * (1 - p.L1 * ‖x - y‖) ≤ (p.L0 + p.L1 * ‖v‖) * ‖x - y‖ at hloc
    have hh := mul_nonneg (norm_nonneg (v - w)) (sub_nonneg.mpr hshort)
    rw [hd] at hloc hh
    nlinarith [congrArg (fun a : ℝ => a * ‖v‖) hunit]
  have hstep : cycle p F x - z = (x - z) - η • w := by
    simp [cycle, stepSize, not_le.mpr hx, η, v, y, w]; abel
  have hi := hm y
  have hy : y - z = (x - z) - η • v := by dsimp [y]; abel
  change 0 ≤ ⟪w, y - z⟫ at hi
  rw [hy, inner_sub_right, real_inner_smul_right] at hi
  have hs := norm_sub_sq_real v w
  rw [real_inner_comm w v] at hs
  have henergy : ‖cycle p F x - z‖ ^ 2 + (η * ‖v‖) ^ 2 / 2 ≤ ‖x - z‖ ^ 2 := by
    rw [hstep, norm_sub_sq_real, real_inner_smul_right, real_inner_comm w (x - z),
      norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hh : ‖v - w‖ ^ 2 ≤ (‖v‖ / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdiff 2
    nlinarith [mul_nonneg hη.le hi, mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hh),
      congrArg (fun t : ℝ => η ^ 2 * t) hs, sq_nonneg (η * ‖v‖)]
  have hv : p.ε ≤ ‖v‖ := hx.le
  have hA : 0 < p.L0 / p.ε + p.L1 := by positivity
  have hmin : (4 * (p.L0 / p.ε + p.L1))⁻¹ ≤ η * ‖v‖ := by
    dsimp only [η]
    rw [inv_mul_eq_div]
    rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hv)]
  linarith [pow_le_pow_left₀ (by positivity) hmin 2]

lemma output_after (p : Params) (F : E p → E p) (O : Oracle (E p) (E p))
    (hO : ∀ h s x, O.answer h (0, x) s = F x) (n : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => 2 * n) seed ξ = (cycle p F)^[n] p.x0 := by
  rw [execute_eq_of_answer_eq O F (fun h x s => hO h s x), execute_iterate]
  let step := fun s : State p => (algorithm p).update s (F ((algorithm p).query s).2)
  have h (x : E p) : step (step (.inl x)) = .inl (cycle p F x) := rfl
  have hi (x : E p) : step^[2 * n] (.inl x) = .inl ((cycle p F)^[n] x) := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, Function.iterate_succ_apply]
      change step^[2 * n] (step (step (.inl x))) = _
      rw [h, ih]
      rfl
  exact congrArg (output p) (hi p.x0)

lemma accuracy (p : Params) (hp : spec.valid p) (F : E p → E p)
    (hc : Continuous F) (hreg : LongTails.Setups.MirrorGeneralizedSmooth.SegmentSmooth F p.L0 p.L1) (z : E p)
    (hz : ‖p.x0 - z‖ ≤ p.R) (hm : ∀ y, 0 ≤ ⟪F y, y - z⟫) :
    let n := 1 + ⌈32 * (p.R * (p.L0 / p.ε + p.L1)) ^ 2⌉₊
    ‖F ((cycle p F)^[n] p.x0)‖ ≤ p.ε := by
  intro n
  obtain ⟨h0, h1, hR, he⟩ := hp
  let C := p.L0 / p.ε + p.L1
  have hC : 0 < C := by dsimp [C]; positivity
  have h (i : ℕ) (hi : p.ε < ‖F ((cycle p F)^[i] p.x0)‖) :
      ‖(cycle p F)^[i] p.x0 - z‖ ^ 2 + i * (4 * C)⁻¹ ^ 2 / 2 ≤ p.R ^ 2 := by
    induction i with
    | zero => simpa using pow_le_pow_left₀ (norm_nonneg _) hz 2
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at hi ⊢
      have hprev : p.ε < ‖F ((cycle p F)^[i] p.x0)‖ := by
        by_contra! hn
        rw [freeze _ _ _ hn] at hi
        linarith
      have hd := decrease p ⟨h0, h1, hR, he⟩ F hc hreg _ z hm hprev
      change _ + (4 * C)⁻¹ ^ 2 / 2 ≤ _ at hd
      push_cast
      linarith [ih hprev]
  by_contra! hb
  have hbad := h n hb
  have hbudget : 32 * (p.R * C) ^ 2 < n := by
    dsimp [n, C]
    push_cast
    linarith [Nat.le_ceil (32 * (p.R * (p.L0 / p.ε + p.L1)) ^ 2)]
  have hsmall : (n : ℝ) * (4 * C)⁻¹ ^ 2 / 2 ≤ p.R ^ 2 := by linarith [sq_nonneg ((‖(cycle p F)^[n] p.x0 - z‖))]
  field_simp at hsmall
  nlinarith

end LongTails.Proofs.GeneralizedMintyDescent
