import LongTails.Proofs.TwoSidedPerceptronPotential

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronTrajectory

open TwoSidedPerceptronDynamics TwoSidedPerceptronPotential

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Control where
  clo : ℝ
  C : ℝ
  κ : ℝ
  δ : ℝ
  a₀ : ℝ
  t₀ : ℝ
  clo_pos : 0 < clo
  clo_le : clo ≤ C
  C_le : C ≤ 1 / 8
  C_le_κ : 65 * C ≤ κ
  κ_pos : 0 < κ
  κ_le : κ ≤ 1
  δ_pos : 0 < δ
  a₀_pos : 0 < a₀
  t₀_pos : 0 < t₀

namespace Control

variable (c : Control)

noncomputable def F : ℝ := 2 * c.a₀ + 2 * c.t₀

noncomputable def Z (K : ℕ) : ℝ := c.δ * c.F * K

noncomputable def start : State E := ⟨c.a₀, 0, c.t₀, 0⟩

noncomputable def drift (K : ℕ) : ℝ :=
  4 * c.C * c.δ * c.F * c.Z K + c.δ ^ 2 * c.F ^ 2 + 12 * c.a₀ * c.δ * c.Z K +
    2 * c.δ ^ 2 * (c.Z K) ^ 2

lemma F_pos : 0 < c.F := by unfold F; linarith [c.a₀_pos, c.t₀_pos]

lemma Z_nonneg (K : ℕ) : 0 ≤ c.Z K := by
  unfold Z; exact mul_nonneg (mul_nonneg c.δ_pos.le c.F_pos.le) (Nat.cast_nonneg K)

lemma Z_mono {j K : ℕ} (h : j ≤ K) : c.Z j ≤ c.Z K := by
  unfold Z
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg c.δ_pos.le c.F_pos.le)
  exact_mod_cast h

lemma Z_succ (k : ℕ) : c.Z (k + 1) = c.Z k + c.δ * c.F := by
  unfold Z; push_cast; ring

lemma drift_nonneg (K : ℕ) : 0 ≤ c.drift K := by
  unfold drift
  have := c.Z_nonneg K
  have hC : 0 ≤ c.C := c.clo_pos.le.trans c.clo_le
  have hδ := c.δ_pos
  have hF := c.F_pos
  have ha := c.a₀_pos
  positivity

lemma C_nonneg : 0 ≤ c.C := c.clo_pos.le.trans c.clo_le

omit [InnerProductSpace ℝ E] in
lemma start_mass : mass (c.start : State E) = 2 * c.a₀ := by
  simp only [start, mass, add_zero, sub_zero, abs_of_pos c.a₀_pos]
  ring

omit [InnerProductSpace ℝ E] in
lemma start_potential : potential c.C (c.start : State E) = (2 * c.a₀) ^ 2 / (4 - 4 * c.C) := by
  unfold potential
  rw [start_mass]
  simp [start]

omit [InnerProductSpace ℝ E] in
lemma start_potential_ge : c.a₀ ^ 2 ≤ potential c.C (c.start : State E) := by
  rw [start_potential]
  have h : 0 < 4 - 4 * c.C := by linarith [c.C_le]
  rw [le_div_iff₀ h]
  nlinarith [c.C_nonneg, sq_nonneg c.a₀]

omit [InnerProductSpace ℝ E] in
lemma start_potential_le : potential c.C (c.start : State E) ≤ 8 * c.a₀ ^ 2 / 7 := by
  rw [start_potential]
  have h : 0 < 4 - 4 * c.C := by linarith [c.C_le]
  rw [div_le_div_iff₀ h (by norm_num)]
  nlinarith [c.C_le, sq_nonneg c.a₀]

end Control

structure Geometry (c : Control) (b : ι → ℝ) (p r : ι → E) (w : E) : Prop where
  lower : ∀ i, c.clo ≤ |b i|
  upper : ∀ i, |b i| ≤ c.C
  p_norm : ∀ i, ‖p i‖ ≤ 1
  r_norm : ∀ i, ‖r i‖ ≤ 1
  w_unit : ‖w‖ = 1
  margin : ∀ i, c.κ ≤ ⟪r i, w⟫

structure Trajectory (c : Control) (b : ι → ℝ) (p r : ι → E)
    (x : ℕ → State E) (i : ℕ → ι) (K : ℕ) : Prop where
  initial : x 0 = c.start
  update : ∀ k, k < K → x (k + 1) = step (b (i k)) c.δ (p (i k)) (r (i k)) (x k)
  mistake : ∀ k, k < K → margin (b (i k)) c.δ (p (i k)) (r (i k)) (x k) ≤ 0

structure Regime (c : Control) (K : ℕ) : Prop where
  drift_small : K * c.drift K ≤ c.a₀ ^ 2
  t_small : c.δ ^ 2 * c.F * (K : ℝ) ^ 2 ≤ c.t₀ / 2
  z_small : 2 * c.δ * c.Z K ≤ c.F
  small : c.δ * K ≤ 1 / 64
  δ_le : c.δ ≤ 1 / 2

structure Invariant (c : Control) (x : State E) (k K : ℕ) : Prop where
  potential_le : potential c.C x ≤ potential c.C (c.start : State E) + k * c.drift K
  z_le : ‖x.z‖ ≤ c.Z k
  t_close : |x.t - c.t₀| ≤ c.δ ^ 2 * c.F * (k : ℝ) ^ 2

variable {c : Control} {b : ι → ℝ} {p r : ι → E} {w : E}
    {x : ℕ → State E} {i : ℕ → ι} {K : ℕ}

omit [InnerProductSpace ℝ E] in
lemma invariant_zero : Invariant c (c.start : State E) 0 K := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp [Control.start, Control.Z]
  · simp [Control.start]

section Bounds

variable {y : State E} {k : ℕ}

omit [InnerProductSpace ℝ E] in
lemma Invariant.potential_le_two (hI : Invariant c y k K) (hR : Regime c K) (hk : k ≤ K) :
    potential c.C y ≤ 2 * potential c.C (c.start : State E) := by
  have h1 := hI.potential_le
  have h2 : (k : ℝ) * c.drift K ≤ K * c.drift K :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (c.drift_nonneg K)
  have h3 := hR.drift_small
  have h4 := c.start_potential_ge (E := E)
  linarith

omit [InnerProductSpace ℝ E] in
lemma Invariant.mass_le (hI : Invariant c y k K) (hR : Regime c K) (hk : k ≤ K) :
    mass y ≤ 4 * c.a₀ := by
  have h1 := sq_mass_le_potential c.C_nonneg (by linarith [c.C_le] : c.C ≤ 1 / 2) y
  have h2 := hI.potential_le_two hR hk
  have h3 := c.start_potential_le (E := E)
  have hm := mass_nonneg y
  have : (mass y) ^ 2 ≤ (4 * c.a₀) ^ 2 := by nlinarith [c.a₀_pos]
  exact (pow_le_pow_iff_left₀ hm (by linarith [c.a₀_pos]) two_ne_zero).mp this

omit [InnerProductSpace ℝ E] in
lemma Invariant.a_le (hI : Invariant c y k K) (hR : Regime c K) (hk : k ≤ K) :
    |y.a| ≤ 2 * c.a₀ := by
  have := two_abs_a_le_mass y
  have := hI.mass_le hR hk
  linarith

omit [InnerProductSpace ℝ E] in
lemma Invariant.t_le (hI : Invariant c y k K) (hR : Regime c K) (hk : k ≤ K) :
    |y.t| ≤ 2 * c.t₀ := by
  have h1 := hI.t_close
  have hF := c.F_pos
  have h2 : c.δ ^ 2 * c.F * (k : ℝ) ^ 2 ≤ c.δ ^ 2 * c.F * (K : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) hF.le)
    exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hk) 2
  have h3 := hR.t_small
  have := abs_le.mp h1
  rw [abs_le]
  constructor <;> linarith [c.t₀_pos]

omit [InnerProductSpace ℝ E] in
lemma Invariant.t_ge (hI : Invariant c y k K) (hR : Regime c K) (hk : k ≤ K) :
    c.t₀ / 2 ≤ y.t := by
  have h1 := hI.t_close
  have hF := c.F_pos
  have h2 : c.δ ^ 2 * c.F * (k : ℝ) ^ 2 ≤ c.δ ^ 2 * c.F * (K : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) hF.le)
    exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hk) 2
  have h3 := hR.t_small
  have := abs_le.mp h1
  linarith

omit [InnerProductSpace ℝ E] in
lemma Invariant.F_le (hI : Invariant c y k K) (hR : Regime c K) (hk : k ≤ K) :
    |y.a| + |y.t| ≤ c.F := by
  have := hI.a_le hR hk
  have := hI.t_le hR hk
  unfold Control.F
  linarith

omit [InnerProductSpace ℝ E] in
lemma Invariant.z_le_Z (hI : Invariant c y k K) (hk : k ≤ K) : ‖y.z‖ ≤ c.Z K :=
  hI.z_le.trans (c.Z_mono hk)

end Bounds

lemma invariant_step (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) {k : ℕ} (hk : k < K)
    (hI : Invariant c (x k) k K) : Invariant c (x (k + 1)) (k + 1) K := by
  have hk' : k ≤ K := hk.le
  have hupd := tr.update k hk
  have hmis := tr.mistake k hk
  have hδ := c.δ_pos
  have hF := hI.F_le hR hk'
  have hz := hI.z_le
  have hzK := hI.z_le_Z hk'
  have hmass := hI.mass_le hR hk'
  have hFpos := c.F_pos
  have hZk := c.Z_nonneg k
  have hZK := c.Z_nonneg K
  refine ⟨?_, ?_, ?_⟩
  · rw [hupd]
    have hstep := potential_step_le (c := b (i k)) (δ := c.δ) (C := c.C) (p := p (i k)) (r := r (i k))
      (x := x k) hδ.le (G.upper _) c.C_le (G.p_norm _) (G.r_norm _) hmis
    have hF0 : 0 ≤ |(x k).a| + |(x k).t| := by positivity
    have hz0 : 0 ≤ ‖(x k).z‖ := norm_nonneg _
    have hC := c.C_nonneg
    have e1 : 4 * c.C * c.δ * ((|(x k).a| + |(x k).t|) * ‖(x k).z‖) ≤
        4 * c.C * c.δ * c.F * c.Z K := by
      have : (|(x k).a| + |(x k).t|) * ‖(x k).z‖ ≤ c.F * c.Z K :=
        mul_le_mul hF hzK hz0 hFpos.le
      calc
        _ ≤ 4 * c.C * c.δ * (c.F * c.Z K) := by gcongr
        _ = _ := by ring
    have e2 : c.δ ^ 2 * (|(x k).a| + |(x k).t|) ^ 2 ≤ c.δ ^ 2 * c.F ^ 2 := by
      gcongr
    have e3 : 3 * mass (x k) * (c.δ * ‖(x k).z‖) ≤ 12 * c.a₀ * c.δ * c.Z K := by
      have h1 : mass (x k) * ‖(x k).z‖ ≤ 4 * c.a₀ * c.Z K :=
        mul_le_mul hmass hzK hz0 (by linarith [c.a₀_pos])
      nlinarith [hδ.le]
    have e4 : 2 * (c.δ * ‖(x k).z‖) ^ 2 ≤ 2 * c.δ ^ 2 * (c.Z K) ^ 2 := by
      have : c.δ * ‖(x k).z‖ ≤ c.δ * c.Z K := mul_le_mul_of_nonneg_left hzK hδ.le
      have h0 : 0 ≤ c.δ * ‖(x k).z‖ := by positivity
      nlinarith [pow_le_pow_left₀ h0 this 2]
    have hdrift : potential c.C (step (b (i k)) c.δ (p (i k)) (r (i k)) (x k)) ≤
        potential c.C (x k) + c.drift K := by
      unfold Control.drift
      linarith
    have := hI.potential_le
    push_cast
    linarith
  · rw [hupd, c.Z_succ]
    have h := step_z_norm_le (c := b (i k)) (δ := c.δ) (p := p (i k)) (r := r (i k)) (x := x k) hδ.le
    have hf := feature_norm_le (G.p_norm (i k)) (G.r_norm (i k)) (x k)
    calc
      _ ≤ ‖(x k).z‖ + c.δ * ‖feature (p (i k)) (r (i k)) (x k)‖ := h
      _ ≤ c.Z k + c.δ * c.F := by
        gcongr
        exact hf.trans hF
  · rw [hupd]
    have h := step_t_sub_le (c := b (i k)) (δ := c.δ) (p := p (i k)) (r := r (i k)) (x := x k)
      hδ.le (G.r_norm _)
    have h1 := hI.t_close
    have h2 : (step (b (i k)) c.δ (p (i k)) (r (i k)) (x k)).t - c.t₀ =
        ((step (b (i k)) c.δ (p (i k)) (r (i k)) (x k)).t - (x k).t) + ((x k).t - c.t₀) := by ring
    have h3 : c.δ * ‖(x k).z‖ ≤ c.δ * c.Z k := mul_le_mul_of_nonneg_left hz hδ.le
    have h4 : c.δ * c.Z k = c.δ ^ 2 * c.F * k := by unfold Control.Z; ring
    calc
      _ ≤ |(step (b (i k)) c.δ (p (i k)) (r (i k)) (x k)).t - (x k).t| + |(x k).t - c.t₀| := by
        rw [h2]; exact abs_add_le _ _
      _ ≤ c.δ ^ 2 * c.F * k + c.δ ^ 2 * c.F * (k : ℝ) ^ 2 := by linarith
      _ ≤ c.δ ^ 2 * c.F * ((k : ℝ) + 1) ^ 2 := by
        have : 0 ≤ c.δ ^ 2 * c.F := mul_nonneg (sq_nonneg _) c.F_pos.le
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      _ = _ := by push_cast; ring

lemma trajectory_invariant (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) : ∀ k, k ≤ K → Invariant c (x k) k K := by
  intro k
  induction k with
  | zero => intro _; rw [tr.initial]; exact invariant_zero
  | succ k ih =>
    intro hk
    exact invariant_step hR G tr (by omega) (ih (by omega))

end LongTails.Proofs.TwoSidedPerceptronTrajectory
