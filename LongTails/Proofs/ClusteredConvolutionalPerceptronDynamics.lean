import LongTails.Proofs.ClusteredConvolutionalPerceptronStability
import LongTails.Proofs.ClusteredConvolutionalPerceptronHistory
import LongTails.Proofs.ManySampleConvolutionalPerceptronDynamics

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronDynamics

open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronStability
open ClusteredConvolutionalPerceptronHistory

structure Control where
  C : ℝ
  e : ℝ
  g : ℝ
  h : ℝ
  ρ : ℝ
  δ : ℝ
  L : ℝ
  C_pos : 0 < C
  e_nonneg : 0 ≤ e
  h_pos : 0 < h
  rho_pos : 0 < ρ
  rho_le : ρ ≤ 1
  delta_pos : 0 < δ
  L_nonneg : 0 ≤ L
  signal : h ≤ g - C * e - C * (C + e)
  lorentz_small : δ * h ≤ 1
  forcing_small : δ ≤ L ^ 2 * h
  cone_small : 6 * (C + e) * L ≤ C * ρ ^ 2

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def step (b δ : ℝ) (p r : E) (x : State E) : State E :=
  ⟨x.a + b * x.q + δ * ⟪p, x.z⟫, x.q + b * x.a,
    x.t + δ * ⟪r, x.z⟫, x.z + x.a • p + x.t • r⟩

noncomputable def mass (x : State E) : ℝ := |x.a + x.q| + |x.a - x.q|

structure Geometry (c : Control) (b : ι → ℝ) (p r : ι → E) : Prop where
  background_lower : ∀ i, c.ρ ≤ |b i|
  background_upper : ∀ i, |b i| ≤ 1
  plus_norm : ∀ i, ‖p i‖ ≤ 1
  cross : ∀ i j, |⟪p i, r j⟫| ≤ c.e
  gram : ∀ i j, c.g ≤ ⟪r i, r j⟫

structure Trajectory (c : Control) (b : ι → ℝ) (p r : ι → E)
    (x : ℕ → State E) (T : ℕ → ℝ) (i : ℕ → ι) (K : ℕ) : Prop where
  initial : x 0 = ⟨c.C, 0, 1, 0⟩
  time_zero : T 0 = 0
  update : ∀ k, k < K → x (k + 1) = step (b (i k)) c.δ (p (i k)) (r (i k)) (x k)
  time_update : ∀ k, k < K → T (k + 1) = T k + (x k).t
  mistake : ∀ k, k < K → b (i k) * (x k).a * (x k).q +
    c.δ * ((x k).a * ⟪p (i k), (x k).z⟫ + (x k).t * ⟪r (i k), (x k).z⟫) ≤ 0

structure Invariant (c : Control) (p r : ι → E) (x : State E) (T : ℝ) : Prop where
  signal : 1 ≤ x.t
  time_nonneg : 0 ≤ T
  lorentz : c.δ * c.h * T ^ 2 ≤ x.t ^ 2
  mass_bound : mass x ≤ 2 * c.C * x.t
  plus : ∀ i, |⟪p i, x.z⟫| ≤ (c.C + c.e) * T
  minus : ∀ i, (c.g - c.C * c.e) * T ≤ ⟪r i, x.z⟫

variable {c : Control} {b : ι → ℝ} {p r : ι → E}
    {x : ℕ → State E} {T : ℕ → ℝ} {i : ℕ → ι} {K : ℕ}

lemma control_signal : c.h ≤ c.g - c.C * c.e := by
  have hn := mul_nonneg c.C_pos.le (add_nonneg c.C_pos.le c.e_nonneg)
  linarith [c.signal]

lemma Invariant.mean {y : State E} {S : ℝ} (h : Invariant c p r y S) :
    |y.a| ≤ c.C * y.t := by
  have hm := mass_controls_mean y.a y.q
  have hb := h.mass_bound
  unfold mass at hb
  linarith

lemma Invariant.margin {y : State E} {S : ℝ} (h : Invariant c p r y S) (j : ι) :
    c.h * y.t * S ≤ y.a * ⟪p j, y.z⟫ + y.t * ⟪r j, y.z⟫ := by
  have hm := history_margin (by linarith [h.signal] : 0 ≤ y.t) h.mean (h.plus j) (h.minus j)
  have hs := mul_le_mul_of_nonneg_right c.signal
    (mul_nonneg (by linarith [h.signal] : 0 ≤ y.t) h.time_nonneg)
  nlinarith

lemma Invariant.forcing {y : State E} {S : ℝ} (h : Invariant c p r y S) (j : ι) :
    |c.δ * ⟪p j, y.z⟫| ≤ (c.C + c.e) * c.L * y.t := by
  have hl := lorentz_forcing c.delta_pos.le c.h_pos c.L_nonneg
    (by linarith [h.signal]) c.forcing_small h.lorentz
  have hp := mul_le_mul_of_nonneg_left (h.plus j) c.delta_pos.le
  have hm := mul_le_mul_of_nonneg_left hl (add_nonneg c.C_pos.le c.e_nonneg)
  rw [abs_mul, abs_of_pos c.delta_pos]
  nlinarith

lemma Invariant.switch (tr : Trajectory c b p r x T i K) {k : ℕ}
    (hk : k < K) (h : Invariant c p r (x k) (T k)) :
    b (i k) * (x k).a * (x k).q ≤ 0 := by
  have hm := h.margin (i k)
  have hn : 0 ≤ c.h * (x k).t * T k := by
    exact mul_nonneg (mul_nonneg c.h_pos.le (by linarith [h.signal])) h.time_nonneg
  have he := mul_nonneg c.delta_pos.le (show 0 ≤
    (x k).a * ⟪p (i k), (x k).z⟫ + (x k).t * ⟪r (i k), (x k).z⟫ by linarith)
  linarith [tr.mistake k hk]

lemma Invariant.signal_step (tr : Trajectory c b p r x T i K) {k : ℕ}
    (hk : k < K) (h : Invariant c p r (x k) (T k)) :
    (x k).t + c.δ * c.h * T k ≤ (x (k + 1)).t := by
  have hm := mul_le_mul_of_nonneg_right (control_signal (c := c)) h.time_nonneg
  have hi := mul_le_mul_of_nonneg_left (hm.trans (h.minus (i k))) c.delta_pos.le
  rw [tr.update k hk]
  simp only [step]
  nlinarith

lemma Invariant.signal_mono (tr : Trajectory c b p r x T i K) {k : ℕ}
    (hk : k < K) (h : Invariant c p r (x k) (T k)) : (x k).t ≤ (x (k + 1)).t := by
  have hs := h.signal_step tr hk
  have hn := mul_nonneg (mul_nonneg c.delta_pos.le c.h_pos.le) h.time_nonneg
  linarith

lemma trajectory_mass_two_step (G : Geometry c b p r) (tr : Trajectory c b p r x T i K)
    {k : ℕ} (hk : k + 2 ≤ K) (h0 : Invariant c p r (x k) (T k))
    (h1 : Invariant c p r (x (k + 1)) (T (k + 1))) :
    mass (x (k + 2)) ≤ (1 - c.ρ ^ 2 / 2) * mass (x k) +
      4 * |c.δ * ⟪p (i k), (x k).z⟫| +
      2 * |c.δ * ⟪p (i (k + 1)), (x (k + 1)).z⟫| := by
  have hb : ∀ j, b j ≠ 0 := by
    intro j hj
    have hl := G.background_lower j
    rw [hj, abs_zero] at hl
    linarith [c.rho_pos]
  have hs0 := h0.switch tr (by omega)
  have hs1 := h1.switch tr (by omega)
  rw [tr.update k (by omega)] at hs1
  simp only [step] at hs1
  have hm := signed_two_step c.rho_pos.le c.rho_le (hb (i k)) (hb (i (k + 1)))
    (G.background_lower (i k)) (G.background_lower (i (k + 1)))
    (G.background_upper (i k)) (G.background_upper (i (k + 1))) hs0 hs1
    (f' := c.δ * ⟪p (i (k + 1)), (x (k + 1)).z⟫)
  dsimp only at hm
  unfold mass
  rw [show k + 2 = (k + 1) + 1 by omega, tr.update (k + 1) (by omega)]
  simp only [step]
  convert hm using 1
  rw [tr.update k (by omega)]
  simp only [step]

lemma invariant_initial : Invariant c p r (⟨c.C, 0, 1, 0⟩ : State E) 0 := by
  constructor <;> simp [mass, abs_of_pos c.C_pos]
  linarith

lemma invariant_next (G : Geometry c b p r) (tr : Trajectory c b p r x T i K)
    {k : ℕ} (hk : k < K) (h : Invariant c p r (x k) (T k))
    (hmass : mass (x (k + 1)) ≤ 2 * c.C * (x (k + 1)).t) :
    Invariant c p r (x (k + 1)) (T (k + 1)) := by
  have hs := h.signal_step tr hk
  have ht : 0 ≤ (x k).t := by linarith [h.signal]
  have hm := h.signal_mono tr hk
  obtain ⟨hp, hr⟩ := history_step (i k) ht h.mean G.plus_norm G.cross G.gram h.plus h.minus
  refine ⟨le_trans h.signal hm, ?_, ?_, hmass, ?_, ?_⟩
  · rw [tr.time_update k hk]; exact add_nonneg h.time_nonneg ht
  · rw [tr.time_update k hk]
    exact lorentz_step (mul_nonneg c.delta_pos.le c.h_pos.le) c.lorentz_small
      ht h.time_nonneg h.lorentz hs
  · rw [tr.update k hk, tr.time_update k hk]
    exact hp
  · rw [tr.update k hk, tr.time_update k hk]
    exact hr

lemma trajectory_invariant (G : Geometry c b p r) (tr : Trajectory c b p r x T i K) :
    ∀ k, k ≤ K → Invariant c p r (x k) (T k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero => rw [tr.initial, tr.time_zero]; exact invariant_initial
    | succ n =>
      have hn : Invariant c p r (x n) (T n) := ih n (by omega) (by omega)
      apply invariant_next G tr (by omega) hn
      cases n with
      | zero =>
        have hb := abs_le.mp (G.background_upper (i 0))
        have hc := c.C_pos.le
        have hplus : 0 ≤ c.C + b (i 0) * c.C := by nlinarith [hb.1]
        have hminus : 0 ≤ c.C - b (i 0) * c.C := by nlinarith [hb.2]
        rw [tr.update 0 (by omega), tr.initial]
        simp [step, mass, abs_of_nonneg hplus, abs_of_nonneg hminus]
        linarith
      | succ m =>
        have h0 : Invariant c p r (x m) (T m) := ih m (by omega) (by omega)
        have h1 : Invariant c p r (x (m + 1)) (T (m + 1)) := hn
        have hm0 := h0.signal_mono tr (by omega)
        have hm1 := h1.signal_mono tr (by omega)
        have htn : 0 ≤ (x (m + 2)).t := by linarith [h1.signal]
        have hm := trajectory_mass_two_step G tr (by omega) h0 h1
        have hf0 := h0.forcing (i m)
        have hf1 := h1.forcing (i (m + 1))
        have hF : 0 ≤ (c.C + c.e) * c.L :=
          mul_nonneg (add_nonneg c.C_pos.le c.e_nonneg) c.L_nonneg
        have hf0' := mul_le_mul_of_nonneg_left (hm0.trans hm1) hF
        have hf1' := mul_le_mul_of_nonneg_left hm1 hF
        have hc0 := mul_le_mul_of_nonneg_left (hm0.trans hm1)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) c.C_pos.le)
        have hr : 0 ≤ 1 - c.ρ ^ 2 / 2 := by nlinarith [c.rho_pos, c.rho_le]
        have hmass := mul_le_mul_of_nonneg_left (h0.mass_bound.trans hc0) hr
        have hsmall := mul_le_mul_of_nonneg_right c.cone_small htn
        change mass (x (m + 2)) ≤ 2 * c.C * (x (m + 2)).t
        nlinarith

end LongTails.Proofs.ClusteredConvolutionalPerceptronDynamics
