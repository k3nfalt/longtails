import LongTails.Proofs.MirrorGeneralizedRun
import LongTails.Proofs.RelativeGeneralizedGrowth

namespace LongTails.Proofs.MirrorGeneralizedGrowth

open LongTails.Setups.MirrorGeneralizedSmooth
open LongTails.Algorithms.MirrorGeneralizedAcceleration
open MirrorGeneralizedStep MirrorGeneralizedRun

lemma scalar_weight_lower {A M Q s : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hQ : 1 ≤ Q) (hs : 0 ≤ s) (hc : M * A ≤ 16 * (Q + s) ^ 2) :
    A / (4096 * (Q + s)) ≤ min (Real.sqrt (A / (64 * M))) (A / (64 * Q)) := by
  have hden : 0 < 4096 * (Q + s) := by positivity
  apply le_min
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) (by positivity : 0 < 64 * M)).mpr
    have hh := mul_le_mul_of_nonneg_left hc hA.le
    nlinarith [mul_nonneg hA.le (sq_nonneg (Q + s))]
  · apply div_le_div_of_nonneg_left hA.le (by positivity : 0 < 64 * Q)
    nlinarith

lemma weight_lower {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hD : 0 < p.D)
    {xs : p.E} (hmin : ∀ u, I.f xs ≤ I.f u) {s : Core p} (hi : Inv I xs s) :
    s.A / (4096 * (1 + p.L1 * radius p + Real.sqrt (p.L0 * s.A))) ≤
      weight p s.A (p.L0 + p.L1 * ‖I.grad s.x‖) := by
  have hA := hi.positive
  have hr : 0 ≤ radius p := by unfold radius; positivity
  have hQ : 1 ≤ 1 + p.L1 * radius p := le_add_of_nonneg_right (mul_nonneg hL1 hr)
  have hM : 0 < p.L0 + p.L1 * ‖I.grad s.x‖ := by positivity
  have hc := curvature_bound h hL0 hL1 hmin hi
  have hc' := mul_le_mul_of_nonneg_right hc hi.positive.le
  have he : (64 * p.L1 ^ 2 * p.D / s.A) * s.A = 64 * p.L1 ^ 2 * p.D :=
    div_mul_cancel₀ _ hi.positive.ne'
  have hs := Real.sq_sqrt (show 0 ≤ p.L0 * s.A by positivity)
  have hroot := Real.sq_sqrt hD.le
  have hroot0 := Real.sqrt_nonneg p.D
  have hsq0 := Real.sqrt_nonneg (p.L0 * s.A)
  apply scalar_weight_lower hi.positive hM hQ hsq0
  dsimp [radius] at *
  simp only [add_mul, he] at hc'
  nlinarith [mul_nonneg (mul_nonneg hL1 hroot0) hsq0]

noncomputable def potential (L Q A : ℝ) : ℝ :=
  Real.sqrt (L * A) + 2 * Q * Real.log (Real.sqrt (L * A))

lemma potential_mono {L Q A B : ℝ} (hL : 0 < L) (hQ : 0 ≤ Q)
    (hA : 0 < A) (hAB : A ≤ B) : potential L Q A ≤ potential L Q B := by
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hAB hL.le)
  have hp : 0 < Real.sqrt (L * A) := by positivity
  have hl := Real.log_le_log hp hs
  unfold potential
  gcongr

lemma potential_increment {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hD : 0 < p.D)
    {xs : p.E} (hmin : ∀ u, I.f xs ≤ I.f u) {s : Core p} (hi : Inv I xs s) :
    potential p.L0 (1 + p.L1 * radius p) s.A + 1 / 12288 ≤
      potential p.L0 (1 + p.L1 * radius p) (step p I.grad I.prox s).A := by
  have hA := hi.positive
  have hr : 0 ≤ radius p := by unfold radius; positivity
  have hQ : 1 ≤ 1 + p.L1 * radius p := le_add_of_nonneg_right (mul_nonneg hL1 hr)
  have hg := OracleTemplate.RelativeGeneralized.weight_growth hi.positive hQ hL0
  have hw := weight_lower h hL0 hL1 hD hmin hi
  have hm := potential_mono hL0 (show 0 ≤ 1 + p.L1 * radius p by positivity)
    (show 0 < s.A + s.A / (4096 * (1 + p.L1 * radius p + Real.sqrt (p.L0 * s.A))) by
      positivity) (add_le_add le_rfl hw)
  dsimp [potential, step] at hm ⊢
  dsimp only at hg
  linarith

lemma potential_run {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hD : 0 < p.D) (hΔ : 0 < p.Δ)
    {xs : p.E} (hmin : ∀ u, I.f xs ≤ I.f u)
    (hb : bregman I xs p.x0 ≤ p.D) (hgap : I.f p.x0 - I.f xs ≤ p.Δ) (k : ℕ) :
    potential p.L0 (1 + p.L1 * radius p) (p.D / p.Δ) + (k : ℝ) / 12288 ≤
      potential p.L0 (1 + p.L1 * radius p) (run p I.grad I.prox k).A := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    have hi := inv_run h hL0 hL1 hD hΔ hmin hb hgap k
    have hh := potential_increment h hL0 hL1 hD hmin hi
    change potential p.L0 (1 + p.L1 * radius p) (p.D / p.Δ) +
      ((k + 1 : ℕ) : ℝ) / 12288 ≤ _
    simp only [Nat.cast_add, Nat.cast_one]
    change _ ≤ potential p.L0 (1 + p.L1 * radius p)
      (step p I.grad I.prox (run p I.grad I.prox k)).A
    linarith

end LongTails.Proofs.MirrorGeneralizedGrowth
