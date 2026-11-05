import LongTails.Algorithms.AcceleratedQuarticNewton
import LongTails.Proofs.QuarticAccelerationEnergy

namespace LongTails.Proofs.QuarticAccelerationTrace

open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open LongTails.Proofs.QuarticAccelerationEnergy
open scoped RealInnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Trace where
  state : ℕ → State E
  guess : ℕ → ℝ
  point : ℕ → E
  gradient : ℕ → E

variable {E}

noncomputable def location (t : Trace E) (k : ℕ) : E := center E (t.guess k) (t.state k)

noncomputable def lam (t : Trace E) (γ : ℝ) (k : ℕ) : ℝ := parameter E γ (location t k) (t.point k)

structure Valid (t : Trace E) (f : E → ℝ) (γ : ℝ) (x0 : E) (N : ℕ) : Prop where
  initial : t.state 0 = ⟨0, x0, x0⟩
  guess_pos : ∀ k ≤ N, 0 < t.guess k
  lam_pos : ∀ k < N, 0 < lam t γ k
  first_guess : 0 < N → t.guess 0 = lam t γ 0
  advance_eq : ∀ k < N, t.state (k + 1) = advance E (t.guess k) γ (t.state k) (t.point k) (t.gradient k)
  guess_eq : ∀ k < N, t.guess (k + 1) = nextGuess (t.guess k) (lam t γ k)
  support : ∀ k < N, ∀ x, f (t.point k) + ⟪t.gradient k, x - t.point k⟫ ≤ f x
  residual : ∀ k < N, ‖t.gradient k + (lam t γ k) • (t.point k - location t k)‖ ≤
    γ * ‖t.point k - location t k‖ ^ 3 / 32

noncomputable def potential (t : Trace E) (f : E → ℝ) (xstar : E) (k : ℕ) : ℝ :=
  (t.state k).weight * (f (t.state k).point - f xstar) + ‖(t.state k).momentum - xstar‖ ^ 2 / 2

noncomputable def dissipation (t : Trace E) (γ : ℝ) (k : ℕ) : ℝ :=
  (1 - (1 / 32 : ℝ) ^ 2) * ((t.state k).weight + trialWeight (t.guess k) (t.state k).weight) *
    min (t.guess k) (lam t γ k) * ‖t.point k - location t k‖ ^ 2 / 2

lemma weight_nonneg {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) : ∀ k ≤ N, 0 ≤ (t.state k).weight := by
  intro k hk
  induction k with
  | zero => simp [hv.initial]
  | succ k ih =>
    have hlt : k < N := by omega
    have hp := (weight_bounds (t.state k) (g := t.gradient k) (hv.guess_pos k (by omega)) (ih (by omega)) (hv.lam_pos k hlt)).1
    rw [← hv.advance_eq k hlt] at hp
    exact (ih (by omega)).trans hp.le

lemma weight_strict {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) {k : ℕ} (hk : k < N) :
    (t.state k).weight < (t.state (k + 1)).weight := by
  rw [hv.advance_eq k hk]
  exact (weight_bounds (t.state k) (g := t.gradient k) (hv.guess_pos k hk.le) (weight_nonneg hv k hk.le) (hv.lam_pos k hk)).1

lemma potential_nonneg {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hmin : ∀ x, f xstar ≤ f x) {k : ℕ} (hk : k ≤ N) :
    0 ≤ potential t f xstar k := by
  unfold potential
  exact add_nonneg (mul_nonneg (weight_nonneg hv k hk) (sub_nonneg.mpr (hmin _))) (by positivity)

lemma dissipation_nonneg {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) {k : ℕ} (hk : k < N) : 0 ≤ dissipation t γ k := by
  have hA := weight_nonneg hv k hk.le
  have hμ := hv.guess_pos k hk.le
  have hlam := hv.lam_pos k hk
  have ha := LongTails.Proofs.CompositeCubicAcceleration.trialWeight_pos hμ hA
  unfold dissipation
  positivity

lemma potential_step {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ) {k : ℕ} (hk : k < N) :
    potential t f xstar (k + 1) + dissipation t γ k ≤ potential t f xstar k := by
  have hne : t.point k ≠ center E (t.guess k) (t.state k) := by
    intro he
    have hp := hv.lam_pos k hk
    simp [lam, parameter, location, he] at hp
  have hh := LongTails.Proofs.QuarticAcceleration.advance_certificate hc (t.state k)
    (z := t.point k) (s := t.gradient k) (xstar := xstar)
    (hv.guess_pos k hk.le) hγ (weight_nonneg hv k hk.le)
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hne
    (fun x _ => hv.support k hk x) (hv.residual k hk)
  simpa only [potential, dissipation, hv.advance_eq k hk, lam, parameter, location] using hh.2.2

lemma prefix_energy {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) : ∀ k ≤ N,
    potential t f xstar k + ∑ i ∈ Finset.range k, dissipation t γ i ≤ R ^ 2 / 2 := by
  intro k hk
  induction k with
  | zero =>
    have hh := pow_le_pow_left₀ (norm_nonneg _) hx0 2
    simpa only [potential, hv.initial, zero_mul, zero_add, Finset.range_zero, Finset.sum_empty, add_zero]
      using (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2))
  | succ k ih =>
    have hh := potential_step hv hc hγ (xstar := xstar) (by omega : k < N)
    rw [Finset.sum_range_succ]
    linarith [ih (by omega)]

lemma weight_mono {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    (t.state i).weight ≤ (t.state j).weight := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => exact (ih (by omega)).trans (weight_strict hv (by omega)).le

lemma weight_pos {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ N) :
    0 < (t.state k).weight := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0)
  exact (weight_nonneg hv j (by omega)).trans_lt (weight_strict hv (by omega))

lemma energy_bounds {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) {k : ℕ} (hk : k ≤ N) :
    potential t f xstar k ≤ R ^ 2 / 2 ∧
      (∑ i ∈ Finset.range k, dissipation t γ i) ≤ R ^ 2 / 2 := by
  have hh := prefix_energy hv hc hγ hx0 k hk
  have hpot := potential_nonneg hv hmin hk
  have hsum : 0 ≤ ∑ i ∈ Finset.range k, dissipation t γ i :=
    Finset.sum_nonneg (fun i hi => dissipation_nonneg hv (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
  constructor <;> linarith

lemma momentum_radius {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) {k : ℕ} (hk : k ≤ N) :
    ‖(t.state k).momentum - xstar‖ ≤ R := by
  have hh := (energy_bounds hv hc hγ hx0 hmin hk).1
  have hR : 0 ≤ R := (norm_nonneg _).trans hx0
  have hgap := mul_nonneg (weight_nonneg hv k hk) (sub_nonneg.mpr (hmin (t.state k).point))
  unfold potential at hh
  nlinarith only [hh, hgap, hR, norm_nonneg ((t.state k).momentum - xstar)]

lemma dissipation_bound {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) {k : ℕ} (hk : k < N) :
    dissipation t γ k ≤ R ^ 2 / 2 := by
  have hh := (energy_bounds hv hc hγ hx0 hmin (Nat.succ_le_of_lt hk)).2
  have hsingle : dissipation t γ k ≤ ∑ i ∈ Finset.range (k + 1), dissipation t γ i :=
    Finset.single_le_sum (fun i hi => dissipation_nonneg hv (k := i) (by have := Finset.mem_range.mp hi; omega))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  exact hsingle.trans hh


end LongTails.Proofs.QuarticAccelerationTrace
