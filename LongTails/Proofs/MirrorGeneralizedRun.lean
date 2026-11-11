import LongTails.Proofs.MirrorGeneralizedStep

namespace LongTails.Proofs.MirrorGeneralizedRun

open LongTails.Setups.MirrorGeneralizedSmooth
open LongTails.Algorithms.MirrorGeneralizedAcceleration
open MirrorGeneralizedStep

structure Inv {p : Public} (I : Instance p) (xs : p.E) (s : Core p) : Prop where
  positive : 0 < s.A
  energy : s.A * (I.f s.x - I.f xs) + bregman I xs s.z ≤ 2 * p.D
  primal : ‖s.x - xs‖ ≤ radius p
  mirror : ‖s.z - xs‖ ≤ radius p

lemma bregman_nonneg {p : Public} {I : Instance p} (h : Hyp I) (u z : p.E) :
    0 ≤ bregman I u z := (by positivity : 0 ≤ ‖u - z‖ ^ 2 / 2).trans (h.strong z u)

lemma bregman_radius {p : Public} {I : Instance p} (h : Hyp I) (hD : 0 < p.D)
    {u z : p.E} (hb : bregman I u z ≤ 2 * p.D) : ‖z - u‖ ≤ radius p := by
  have hh := h.strong z u
  rw [norm_sub_rev u z] at hh
  have hs := Real.sq_sqrt hD.le
  have hp := Real.sqrt_nonneg p.D
  dsimp [radius]
  nlinarith [norm_nonneg (z - u)]

lemma initial_inv {p : Public} {I : Instance p} (h : Hyp I)
    (hD : 0 < p.D) (hΔ : 0 < p.Δ) {xs : p.E}
    (hb : bregman I xs p.x0 ≤ p.D) (hgap : I.f p.x0 - I.f xs ≤ p.Δ) :
    Inv I xs (run p I.grad I.prox 0) := by
  have hA : 0 < p.D / p.Δ := div_pos hD hΔ
  have hd := bregman_radius h hD (show bregman I xs p.x0 ≤ 2 * p.D by linarith)
  refine ⟨hA, ?_, hd, hd⟩
  change p.D / p.Δ * (I.f p.x0 - I.f xs) + bregman I xs p.x0 ≤ 2 * p.D
  have hh := mul_le_mul_of_nonneg_left hgap hA.le
  have he : p.D / p.Δ * p.Δ = p.D := div_mul_cancel₀ _ hΔ.ne'
  linarith

lemma inv_step {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hD : 0 < p.D)
    {xs : p.E} (hmin : ∀ u, I.f xs ≤ I.f u) {s : Core p} (hi : Inv I xs s) :
    Inv I xs (step p I.grad I.prox s) := by
  set M := p.L0 + p.L1 * ‖I.grad s.x‖
  set a := weight p s.A M
  set y := mix p s a s.z
  set w := I.prox s.z (a • I.grad y)
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := weight_pos hL1 hi.positive hM
  have hd : ‖s.z - s.x‖ ≤ 2 * radius p := by
    have ht : ‖s.z - s.x‖ ≤ ‖s.z - xs‖ + ‖s.x - xs‖ := by
      calc
        _ = ‖(s.z - xs) - (s.x - xs)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith [hi.primal, hi.mirror]
  have he := (actual_energy h s hL0 hL1 hi.positive hd xs).trans hi.energy
  change (s.A + a) * (I.f (mix p s a w) - I.f xs) + bregman I xs w ≤ 2 * p.D at he
  have hp : 0 < s.A + a := add_pos hi.positive ha
  have hgap : 0 ≤ I.f (mix p s a w) - I.f xs := sub_nonneg.mpr (hmin _)
  have hb : bregman I xs w ≤ 2 * p.D := by
    have := mul_nonneg hp.le hgap
    linarith
  have hw := bregman_radius h hD hb
  have hx := mix_ball s hi.positive ha.le xs w hi.primal hw
  exact ⟨hp, he, hx, hw⟩

lemma inv_run {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hD : 0 < p.D) (hΔ : 0 < p.Δ)
    {xs : p.E} (hmin : ∀ u, I.f xs ≤ I.f u)
    (hb : bregman I xs p.x0 ≤ p.D) (hgap : I.f p.x0 - I.f xs ≤ p.Δ) (k : ℕ) :
    Inv I xs (run p I.grad I.prox k) := by
  induction k with
  | zero => exact initial_inv h hD hΔ hb hgap
  | succ k ih => exact inv_step h hL0 hL1 hD hmin ih

lemma objective_bound {p : Public} {I : Instance p} (h : Hyp I)
    {xs : p.E} {s : Core p} (hi : Inv I xs s) :
    I.f s.x - I.f xs ≤ 2 * p.D / s.A := by
  apply (le_div_iff₀ hi.positive).mpr
  have hh := bregman_nonneg h xs s.z
  nlinarith [hi.energy]

lemma curvature_bound {p : Public} {I : Instance p} (h : Hyp I)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) {xs : p.E}
    (hmin : ∀ u, I.f xs ≤ I.f u) {s : Core p} (hi : Inv I xs s) :
    p.L0 + p.L1 * ‖I.grad s.x‖ ≤ 2 * p.L0 + 64 * p.L1 ^ 2 * p.D / s.A := by
  have hc := MirrorGeneralizedLocal.curvature_gap_bound hL0 hL1 h.grad h.cont h.smooth hmin s.x
  have hg := objective_bound h hi
  have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 32 * p.L1 ^ 2 by positivity)
  calc
    _ ≤ 2 * p.L0 + 32 * p.L1 ^ 2 * (I.f s.x - I.f xs) := hc
    _ ≤ 2 * p.L0 + 32 * p.L1 ^ 2 * (2 * p.D / s.A) := by linarith
    _ = _ := by ring

end LongTails.Proofs.MirrorGeneralizedRun
