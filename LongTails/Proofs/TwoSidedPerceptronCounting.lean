import LongTails.Proofs.TwoSidedPerceptronContraction
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronCounting

open TwoSidedPerceptronDynamics TwoSidedPerceptronPotential TwoSidedPerceptronTrajectory
  TwoSidedPerceptronContraction

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Scalar

lemma absorb_sqrt {X a β : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (h : X ≤ a + β * Real.sqrt X) : X ≤ 2 * a + 4 * β ^ 2 := by
  by_cases hc : 4 * β ^ 2 ≤ X
  · have h1 : 2 * β ≤ Real.sqrt X := by
      rw [show (2 * β) = Real.sqrt ((2 * β) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : β * Real.sqrt X ≤ X / 2 := by
      have hs := Real.sq_sqrt hX
      nlinarith [Real.sqrt_nonneg X]
    have := sq_nonneg β
    linarith
  · have hc' := not_le.mp hc
    linarith

lemma sqrt_quadratic {X β γ : ℝ} (_hX : 0 ≤ X) (hβ : 0 ≤ β) (_hγ : 0 ≤ γ)
    (h : X ^ 2 ≤ β * X + γ) : X ≤ β + Real.sqrt γ := by
  by_cases hXb : X ≤ β
  · linarith [Real.sqrt_nonneg γ]
  · replace hXb := not_le.mp hXb
    have h1 : (X - β) ^ 2 ≤ γ := by nlinarith
    have h2 : X - β ≤ Real.sqrt γ := by
      rw [show X - β = Real.sqrt ((X - β) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt h1
    linarith

lemma pow_one_sub_le_exp {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    (1 - q) ^ m ≤ Real.exp (-(q * m)) := by
  have h1 : 1 - q ≤ Real.exp (-q) := by
    have := Real.add_one_le_exp (-q); linarith
  have h2 : (1 - q) ^ m ≤ (Real.exp (-q)) ^ m := pow_le_pow_left₀ (by linarith) h1 m
  rw [← Real.exp_nat_mul] at h2
  convert h2 using 2; ring

lemma geom_sum_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 - q) ^ j ≤ 1 / q := by
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpow : (1 - q) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpow0 : 0 ≤ (1 - q) ^ n := pow_nonneg (by linarith) n
    have hsum : ∑ j ∈ Finset.range n, (1 - q) ^ j = (1 - (1 - q) ^ n) / q := by
      have hne : (1 - q) ≠ 1 := by linarith
      rw [geom_sum_eq hne n]
      field_simp
      ring
    rw [hsum]
    rw [div_add' _ _ _ hq0.ne', div_le_div_iff_of_pos_right hq0]
    nlinarith

end Scalar

variable {c : Control} {b : ι → ℝ} {p r : ι → E} {w : E}
    {x : ℕ → State E} {i : ℕ → ι} {K K₁ : ℕ}

section PhaseOne

lemma even_mass_bound (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) (hK1 : K₁ ≤ K) (_hK1pos : 0 < K₁) :
    ∀ j, 2 * j ≤ K₁ → (∀ l, l < j → c.threshold K₁ ≤ mass (x (2 * l))) →
      mass (x (2 * j)) ≤ (1 - c.clo ^ 2 / 8) ^ j * (2 * c.a₀) + 40 * (c.δ * c.Z K₁) / c.clo ^ 2 := by
  intro j
  induction j with
  | zero =>
    intro _ _
    rw [Nat.mul_zero, tr.initial, c.start_mass]
    have : 0 ≤ 40 * (c.δ * c.Z K₁) / c.clo ^ 2 := by
      have := c.Z_nonneg K₁; have := c.δ_pos; positivity
    simp only [pow_zero, one_mul]; linarith
  | succ j ih =>
    intro hj hW
    have hW' : c.threshold K₁ ≤ mass (x (2 * j)) := hW j (Nat.lt_succ_self j)
    have ih' := ih (by omega) (fun l hl => hW l (by omega))
    have hts := two_step (K₁ := K₁) hR G tr (k := 2 * j) (by omega) (by omega) hK1 hW'
    have hq0 : 0 ≤ 1 - c.clo ^ 2 / 8 := by
      have := c.clo_le_one; have := c.clo_pos; nlinarith
    have hclo := c.clo_pos
    have e : (2 * (j + 1)) = 2 * j + 2 := by ring
    rw [e]
    have h40 : (1 - c.clo ^ 2 / 8) * (40 * (c.δ * c.Z K₁) / c.clo ^ 2) + 5 * (c.δ * c.Z K₁) =
        40 * (c.δ * c.Z K₁) / c.clo ^ 2 := by
      field_simp
      ring
    calc
      mass (x (2 * j + 2)) ≤ (1 - c.clo ^ 2 / 8) * mass (x (2 * j)) + 5 * (c.δ * c.Z K₁) := hts
      _ ≤ (1 - c.clo ^ 2 / 8) * ((1 - c.clo ^ 2 / 8) ^ j * (2 * c.a₀) +
            40 * (c.δ * c.Z K₁) / c.clo ^ 2) + 5 * (c.δ * c.Z K₁) := by
        gcongr
      _ = _ := by rw [pow_succ]; linear_combination h40

lemma odd_mass_bound (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) (_hK1 : K₁ ≤ K) {k : ℕ} (hk : k < K) (hk1 : k ≤ K₁) :
    mass (x (k + 1)) ≤ 9 / 8 * mass (x k) + 2 * (c.δ * c.Z K₁) := by
  have hI := trajectory_invariant hR G tr k hk.le
  have hz : ‖(x k).z‖ ≤ c.Z K₁ := hI.z_le.trans (c.Z_mono hk1)
  rw [tr.update k hk]
  exact mass_next_le_crude (G.upper _) (G.p_norm _) hz

lemma phase_one (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) {m : ℕ} (hm0 : 0 < m) (hmK : 2 * m ≤ K)
    (hdecay : (1 - c.clo ^ 2 / 8) ^ m * (2 * c.a₀) ≤ c.threshold (2 * m)) :
    ∃ j₁, j₁ ≤ m ∧ (∀ l, l < j₁ → c.threshold (2 * m) ≤ mass (x (2 * l))) ∧
      mass (x (2 * j₁)) ≤ c.threshold (2 * m) + 40 * (c.δ * c.Z (2 * m)) / c.clo ^ 2 := by
  classical
  by_cases h : ∃ j, j ≤ m ∧ mass (x (2 * j)) ≤ c.threshold (2 * m)
  · refine ⟨Nat.find h, (Nat.find_spec h).1, ?_, ?_⟩
    · intro l hl
      have hmin := Nat.find_min h hl
      by_contra hcon
      exact hmin ⟨by have := (Nat.find_spec h).1; omega, (not_le.mp hcon).le⟩
    · have h40 : 0 ≤ 40 * (c.δ * c.Z (2 * m)) / c.clo ^ 2 := by
        have := c.Z_nonneg (2 * m); have := c.δ_pos; positivity
      linarith [(Nat.find_spec h).2]
  · have h' : ∀ j, j ≤ m → c.threshold (2 * m) < mass (x (2 * j)) := fun j hj =>
      lt_of_not_ge (fun hle => h ⟨j, hj, hle⟩)
    refine ⟨m, le_rfl, fun l hl => (h' l hl.le).le, ?_⟩
    have := even_mass_bound (K₁ := 2 * m) hR G tr hmK (by omega) m le_rfl
      (fun l hl => (h' l hl.le).le)
    linarith

end PhaseOne

section PhaseTwo

lemma potential_phase_step (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) {l : ℕ} (hl : l < K) {X : ℝ} (hX : 0 ≤ X)
    (hΨ : potential c.C (x l) ≤ X ^ 2) :
    potential c.C (x (l + 1)) ≤
      potential c.C (x l) + 8 * c.C * c.t₀ * c.δ * X + 8 * c.δ * X ^ 2 + c.δ ^ 2 * c.F ^ 2 := by
  have hI := trajectory_invariant hR G tr l hl.le
  have hδ := c.δ_pos
  have hC := c.C_nonneg
  have hmis := tr.mistake l hl
  rw [tr.update l hl]
  have hstep := potential_step_le (c := b (i l)) (δ := c.δ) (C := c.C) (p := p (i l)) (r := r (i l))
    (x := x l) hδ.le (G.upper _) c.C_le (G.p_norm _) (G.r_norm _) hmis
  have hmass2 : (mass (x l)) ^ 2 ≤ 4 * X ^ 2 := by
    have := sq_mass_le_potential c.C_nonneg (by linarith [c.C_le] : c.C ≤ 1 / 2) (x l); linarith
  have hmass : mass (x l) ≤ 2 * X := by
    have hm := mass_nonneg (x l)
    have : (mass (x l)) ^ 2 ≤ (2 * X) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hm (by positivity) two_ne_zero).mp this
  have hz2 : ‖(x l).z‖ ^ 2 ≤ X ^ 2 := by
    have := norm_z_sq_le_potential (by linarith [c.C_le] : c.C ≤ 1 / 2) (x l); linarith
  have hz : ‖(x l).z‖ ≤ X :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) hX two_ne_zero).mp hz2
  have ha : |(x l).a| ≤ X := by have := two_abs_a_le_mass (x l); linarith
  have ht : |(x l).t| ≤ 2 * c.t₀ := hI.t_le hR hl.le
  have hF := hI.F_le hR hl.le
  have hF0 : 0 ≤ |(x l).a| + |(x l).t| := by positivity
  have hz0 : 0 ≤ ‖(x l).z‖ := norm_nonneg _
  have e1 : 4 * c.C * c.δ * ((|(x l).a| + |(x l).t|) * ‖(x l).z‖) ≤
      8 * c.C * c.t₀ * c.δ * X + 4 * c.C * c.δ * X ^ 2 := by
    have : (|(x l).a| + |(x l).t|) * ‖(x l).z‖ ≤ (X + 2 * c.t₀) * X :=
      mul_le_mul (by linarith) hz hz0 (by linarith [c.t₀_pos])
    have h0 : 0 ≤ 4 * c.C * c.δ := by positivity
    nlinarith
  have e2 : c.δ ^ 2 * (|(x l).a| + |(x l).t|) ^ 2 ≤ c.δ ^ 2 * c.F ^ 2 := by gcongr
  have e3 : 3 * mass (x l) * (c.δ * ‖(x l).z‖) ≤ 6 * c.δ * X ^ 2 := by
    have h1 : mass (x l) * ‖(x l).z‖ ≤ 2 * X * X := mul_le_mul hmass hz hz0 (by positivity)
    nlinarith [hδ.le]
  have e4 : 2 * (c.δ * ‖(x l).z‖) ^ 2 ≤ c.δ * X ^ 2 := by
    have h1 : (c.δ * ‖(x l).z‖) ^ 2 ≤ c.δ ^ 2 * X ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hz2 (by positivity)
    have h2 : c.δ ^ 2 ≤ c.δ / 2 := by nlinarith [hR.δ_le, hδ]
    nlinarith [sq_nonneg X]
  have hC4 : 4 * c.C * c.δ * X ^ 2 ≤ c.δ * X ^ 2 := by
    have : 4 * c.C ≤ 1 := by linarith [c.C_le]
    nlinarith [sq_nonneg X, hδ.le]
  linarith

lemma potential_phase (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) {k₁ : ℕ} {X : ℝ} (hX : 0 ≤ X)
    (hΨ : ∀ l, k₁ ≤ l → l ≤ K → potential c.C (x l) ≤ X ^ 2) :
    ∀ k, k₁ ≤ k → k ≤ K → potential c.C (x k) ≤
      potential c.C (x k₁) + (k - k₁ : ℕ) *
        (8 * c.C * c.t₀ * c.δ * X + 8 * c.δ * X ^ 2 + c.δ ^ 2 * c.F ^ 2) := by
  intro k
  induction k with
  | zero => intro h1 _; have : k₁ = 0 := by omega
            subst this; simp
  | succ k ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with heq | hlt
    · rw [← heq]; simp
    · have ih' := ih (by omega) (by omega)
      have hs := potential_phase_step hR G tr (l := k) (by omega) hX (hΨ k (by omega) (by omega))
      have e : ((k + 1 - k₁ : ℕ) : ℝ) = ((k - k₁ : ℕ) : ℝ) + 1 := by
        rw [Nat.sub_add_comm (by omega)]; push_cast; ring
      rw [e]
      have h0 : 0 ≤ 8 * c.C * c.t₀ * c.δ * X + 8 * c.δ * X ^ 2 + c.δ ^ 2 * c.F ^ 2 := by
        have := c.C_nonneg; have := c.t₀_pos; have := c.δ_pos; positivity
      nlinarith

end PhaseTwo

section Progress

lemma inner_feature_w (G : Geometry c b p r w) (j : ι) {y : State E} (ht : 0 ≤ y.t) :
    y.t * c.κ - |y.a| ≤ ⟪feature (p j) (r j) y, w⟫ := by
  rw [feature_inner_right]
  have h1 : |y.a * ⟪p j, w⟫| ≤ |y.a| := by
    rw [abs_mul]
    have := abs_real_inner_le_norm (p j) w
    rw [G.w_unit, mul_one] at this
    have := this.trans (G.p_norm j)
    nlinarith [abs_nonneg y.a]
  have h2 : y.t * c.κ ≤ y.t * ⟪r j, w⟫ := mul_le_mul_of_nonneg_left (G.margin j) ht
  linarith [neg_abs_le (y.a * ⟪p j, w⟫)]

lemma progress (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) :
    ∀ k, k ≤ K → c.δ * ∑ l ∈ Finset.range k, ((x l).t * c.κ - |(x l).a|) ≤ ⟪(x k).z, w⟫ := by
  intro k
  induction k with
  | zero => intro _; rw [tr.initial]; simp [Control.start]
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, mul_add, tr.update k (by omega), step_z, inner_add_left,
      real_inner_smul_left]
    have hI := trajectory_invariant hR G tr k (by omega)
    have ht : 0 ≤ (x k).t := by have := hI.t_ge hR (by omega); linarith [c.t₀_pos]
    have h := inner_feature_w G (i k) ht
    have := ih (by omega)
    have := mul_le_mul_of_nonneg_left h c.δ_pos.le
    linarith

end Progress

section Final

noncomputable def _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.phaseSum
    (c : Control) (m : ℕ) : ℝ :=
  17 / 16 * (8 * (2 * c.a₀) / c.clo ^ 2 + 40 * m * (c.δ * c.Z (2 * m)) / c.clo ^ 2) +
    m * (c.δ * c.Z (2 * m))

noncomputable def _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.tail
    (c : Control) (m : ℕ) : ℝ :=
  c.threshold (2 * m) / c.δ + 40 * c.Z (2 * m) / c.clo ^ 2

noncomputable def _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.bound
    (c : Control) (m : ℕ) : ℝ :=
  8 * (c.phaseSum m + 65 / 64 * (2 * Real.sqrt 2 * c.F * m + c.tail m)) / (c.t₀ * c.κ) +
    64 * (65 / 64 * Real.sqrt 2 * c.F) ^ 2 / (c.t₀ * c.κ) ^ 2

lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha
  have := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

set_option maxHeartbeats 4000000 in
lemma mistakes_le (hR : Regime c K) (G : Geometry c b p r w)
    (tr : Trajectory c b p r x i K) {m : ℕ} (hm0 : 0 < m)
    (hdecay : (1 - c.clo ^ 2 / 8) ^ m * (2 * c.a₀) ≤ c.threshold (2 * m)) :
    (K : ℝ) ≤ 2 * m + c.bound m := by
  have hbound0 : 0 ≤ c.bound m := by
    unfold Control.bound Control.phaseSum Control.tail
    have := c.Z_nonneg (2 * m); have := c.δ_pos; have := c.clo_pos; have := c.a₀_pos
    have := c.t₀_pos; have := c.κ_pos; have := c.F_pos; have := c.threshold_nonneg (2 * m)
    positivity
  by_cases hK : K < 2 * m
  · have : (K : ℝ) ≤ 2 * m := by exact_mod_cast hK.le
    linarith
  replace hK := not_lt.mp hK
  set Z₁ := c.Z (2 * m) with hZ₁
  set W₁ := c.threshold (2 * m) with hW₁
  set W₂ := W₁ + 40 * (c.δ * Z₁) / c.clo ^ 2 with hW₂
  set q := c.clo ^ 2 / 8 with hq
  have hδ := c.δ_pos
  have hclo := c.clo_pos
  have hclo1 := c.clo_le_one
  have ht₀ := c.t₀_pos
  have hκ := c.κ_pos
  have hF := c.F_pos
  have ha₀ := c.a₀_pos
  have hZ1 := c.Z_nonneg (2 * m)
  have hW1 := c.threshold_nonneg (2 * m)
  have hW2 : 0 ≤ W₂ := by positivity
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq]; nlinarith
  have hC := c.C_nonneg
  have hCκ := c.C_le_κ
  have hsmall := hR.small
  obtain ⟨j₁, hj₁m, hj₁W, hj₁mass⟩ := phase_one hR G tr hm0 hK hdecay
  set k₁ := 2 * j₁ with hk₁
  have hk₁K : k₁ ≤ K := by omega
  have hT1 : ∑ l ∈ Finset.range k₁, |(x l).a| ≤ c.phaseSum m := by
    have key : ∀ j, j ≤ j₁ → ∑ l ∈ Finset.range (2 * j), |(x l).a| ≤
        17 / 16 * ((∑ l ∈ Finset.range j, (1 - q) ^ l) * (2 * c.a₀) +
          j * (40 * (c.δ * Z₁) / c.clo ^ 2)) + j * (c.δ * Z₁) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have ih' := ih (by omega)
        have heven := even_mass_bound (K₁ := 2 * m) hR G tr hK (by omega) j (by omega)
          (fun l hl => hj₁W l (by omega))
        have hodd := odd_mass_bound (K₁ := 2 * m) hR G tr hK (k := 2 * j) (by omega) (by omega)
        have ha1 := two_abs_a_le_mass (x (2 * j))
        have ha2 := two_abs_a_le_mass (x (2 * j + 1))
        have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
        rw [e, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        have hpow0 : 0 ≤ (1 - q) ^ j := pow_nonneg (by linarith) j
        push_cast
        nlinarith [hδ.le, hZ1]
    have hgeom := geom_sum_le hq0 hq1 j₁
    have h8 : 1 / q = 8 / c.clo ^ 2 := by rw [hq]; field_simp
    rw [h8] at hgeom
    have hj₁R : (j₁ : ℝ) ≤ m := by exact_mod_cast hj₁m
    have := key j₁ le_rfl
    unfold Control.phaseSum
    have hδZ : 0 ≤ c.δ * Z₁ := by positivity
    have h40 : 0 ≤ 40 * (c.δ * Z₁) / c.clo ^ 2 := by positivity
    have hgeom' : (∑ l ∈ Finset.range j₁, (1 - q) ^ l) * (2 * c.a₀) ≤
        8 / c.clo ^ 2 * (2 * c.a₀) := mul_le_mul_of_nonneg_right hgeom (by positivity)
    have hj40 : (j₁ : ℝ) * (40 * (c.δ * Z₁) / c.clo ^ 2) ≤ m * (40 * (c.δ * Z₁) / c.clo ^ 2) :=
      mul_le_mul_of_nonneg_right hj₁R h40
    have hjZ : (j₁ : ℝ) * (c.δ * Z₁) ≤ m * (c.δ * Z₁) := mul_le_mul_of_nonneg_right hj₁R hδZ
    have e1 : 8 / c.clo ^ 2 * (2 * c.a₀) = 8 * (2 * c.a₀) / c.clo ^ 2 := by ring
    have e2 : (m : ℝ) * (40 * (c.δ * Z₁) / c.clo ^ 2) = 40 * m * (c.δ * Z₁) / c.clo ^ 2 := by ring
    linarith
  have hne : (Finset.Icc k₁ K).Nonempty := ⟨k₁, Finset.mem_Icc.mpr ⟨le_rfl, hk₁K⟩⟩
  obtain ⟨kmax, hkmax, hmax⟩ := Finset.exists_max_image (Finset.Icc k₁ K)
    (fun l => potential c.C (x l)) hne
  have hkmax' := Finset.mem_Icc.mp hkmax
  set X := Real.sqrt (potential c.C (x kmax)) with hX
  have hΨnn : ∀ l, 0 ≤ potential c.C (x l) := fun l =>
    potential_nonneg (by linarith [c.C_le]) (x l)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = potential c.C (x kmax) := Real.sq_sqrt (hΨnn kmax)
  have hΨX : ∀ l, k₁ ≤ l → l ≤ K → potential c.C (x l) ≤ X ^ 2 := by
    intro l h1 h2
    rw [hXsq]; exact hmax l (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hmassk₁ : mass (x k₁) ≤ W₂ := hj₁mass
  have hIk₁ := trajectory_invariant hR G tr k₁ hk₁K
  have hzk₁ : ‖(x k₁).z‖ ≤ c.δ * c.F * k₁ := by
    have := hIk₁.z_le; unfold Control.Z at this; exact this
  have hk₁R : (k₁ : ℝ) ≤ 2 * m := by exact_mod_cast (by omega : k₁ ≤ 2 * m)
  have hΨk₁ : 2 * potential c.C (x k₁) ≤ (Real.sqrt 2 * (c.δ * c.F) * (2 * m) + W₂) ^ 2 := by
    unfold potential
    have h47 : 7 / 2 ≤ 4 - 4 * c.C := by linarith [c.C_le]
    have hm0' := mass_nonneg (x k₁)
    have hmsq : (mass (x k₁)) ^ 2 ≤ W₂ ^ 2 := pow_le_pow_left₀ hm0' hmassk₁ 2
    have hdiv : (mass (x k₁)) ^ 2 / (4 - 4 * c.C) ≤ W₂ ^ 2 / (7 / 2) := by
      calc
        (mass (x k₁)) ^ 2 / (4 - 4 * c.C) ≤ (mass (x k₁)) ^ 2 / (7 / 2) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h47
        _ ≤ W₂ ^ 2 / (7 / 2) := by gcongr
    have hz2 : ‖(x k₁).z‖ ^ 2 ≤ (c.δ * c.F * (2 * m)) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖(x k₁).z‖ ≤ c.δ * c.F * k₁ := hzk₁
        _ ≤ c.δ * c.F * (2 * m) := by gcongr
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hpos : 0 ≤ c.δ * c.F * (2 * m) := by positivity
    nlinarith [mul_nonneg hpos hW2, mul_nonneg hs0 (mul_nonneg hpos hW2)]
  have hrec := potential_phase hR G tr (k₁ := k₁) hX0 hΨX kmax hkmax'.1 hkmax'.2
  have hKk : ((kmax - k₁ : ℕ) : ℝ) ≤ K := by exact_mod_cast (Nat.sub_le kmax k₁).trans hkmax'.2
  have hΔ0 : 0 ≤ 8 * c.C * c.t₀ * c.δ * X + 8 * c.δ * X ^ 2 + c.δ ^ 2 * c.F ^ 2 := by positivity
  have hX2 : X ^ 2 ≤ potential c.C (x k₁) +
      K * (8 * c.C * c.t₀ * c.δ * X + 8 * c.δ * X ^ 2 + c.δ ^ 2 * c.F ^ 2) := by
    calc
      X ^ 2 = potential c.C (x kmax) := hXsq
      _ ≤ _ := hrec
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hKk hΔ0)
  have h8δK : 8 * c.δ * K ≤ 1 / 2 := by linarith
  have hX2' : X ^ 2 ≤ 2 * potential c.C (x k₁) + 16 * c.C * c.t₀ * c.δ * K * X +
      2 * c.δ ^ 2 * c.F ^ 2 * K := by
    have hXX : 0 ≤ X ^ 2 := sq_nonneg X
    have := mul_le_mul_of_nonneg_right h8δK hXX
    linarith [hX2, this]
  have hγ0 : 0 ≤ 2 * potential c.C (x k₁) + 2 * c.δ ^ 2 * c.F ^ 2 * K := by
    have := hΨnn k₁; positivity
  have hXle : X ≤ 16 * c.C * c.t₀ * c.δ * K +
      Real.sqrt (2 * potential c.C (x k₁) + 2 * c.δ ^ 2 * c.F ^ 2 * K) := by
    apply sqrt_quadratic hX0 (by positivity) hγ0
    linarith
  have hsqrt : Real.sqrt (2 * potential c.C (x k₁) + 2 * c.δ ^ 2 * c.F ^ 2 * K) ≤
      (Real.sqrt 2 * (c.δ * c.F) * (2 * m) + W₂) + c.δ * c.F * Real.sqrt (2 * K) := by
    have h1 := sqrt_add_le' (by have := hΨnn k₁; positivity : 0 ≤ 2 * potential c.C (x k₁))
      (by positivity : 0 ≤ 2 * c.δ ^ 2 * c.F ^ 2 * K)
    have h2 : Real.sqrt (2 * potential c.C (x k₁)) ≤ Real.sqrt 2 * (c.δ * c.F) * (2 * m) + W₂ := by
      rw [Real.sqrt_le_left (by positivity)]; exact hΨk₁
    have h3 : Real.sqrt (2 * c.δ ^ 2 * c.F ^ 2 * K) = c.δ * c.F * Real.sqrt (2 * K) := by
      rw [show 2 * c.δ ^ 2 * c.F ^ 2 * (K : ℝ) = (c.δ * c.F) ^ 2 * (2 * K) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    linarith
  have hprog := progress hR G tr K le_rfl
  have hsum_t : ∀ l, l < K → c.t₀ / 2 * c.κ ≤ (x l).t * c.κ := fun l hl => by
    have := (trajectory_invariant hR G tr l hl.le).t_ge hR hl.le
    exact mul_le_mul_of_nonneg_right this hκ.le
  have hT : ∑ l ∈ Finset.range K, |(x l).a| ≤ c.phaseSum m + K * X := by
    have key : ∀ k, k₁ ≤ k → k ≤ K →
        ∑ l ∈ Finset.range k, |(x l).a| ≤ c.phaseSum m + ((k - k₁ : ℕ) : ℝ) * X := by
      intro k
      induction k with
      | zero => intro h1 _; have : k₁ = 0 := by omega
                rw [this] at hT1 ⊢; simpa using hT1
      | succ k ih =>
        intro h1 h2
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · rw [heq] at hT1
          have h0 : k + 1 - k₁ = 0 := by omega
          rw [h0]; simpa using hT1
        · have ih' := ih (by omega) (by omega)
          rw [Finset.sum_range_succ]
          have hΨk := hΨX k (by omega) (by omega)
          have ha : |(x k).a| ≤ X := by
            have h1 := two_abs_a_le_mass (x k)
            have h2 := sq_mass_le_potential c.C_nonneg (by linarith [c.C_le] : c.C ≤ 1 / 2) (x k)
            have h3 : (mass (x k)) ^ 2 ≤ (2 * X) ^ 2 := by nlinarith
            have h4 := (pow_le_pow_iff_left₀ (mass_nonneg _) (by positivity) two_ne_zero).mp h3
            linarith
          have e : ((k + 1 - k₁ : ℕ) : ℝ) = ((k - k₁ : ℕ) : ℝ) + 1 := by
            rw [Nat.sub_add_comm (by omega)]; push_cast; ring
          rw [e]; linarith
    have := key K hk₁K le_rfl
    have hKk' : ((K - k₁ : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K k₁
    nlinarith
  have hsum : c.δ * (c.t₀ / 2 * c.κ * K - (c.phaseSum m + K * X)) ≤ ⟪(x K).z, w⟫ := by
    have h1 : ∑ l ∈ Finset.range K, ((x l).t * c.κ - |(x l).a|) =
        ∑ l ∈ Finset.range K, (x l).t * c.κ - ∑ l ∈ Finset.range K, |(x l).a| :=
      Finset.sum_sub_distrib _ _
    have h2 : (K : ℝ) * (c.t₀ / 2 * c.κ) ≤ ∑ l ∈ Finset.range K, (x l).t * c.κ := by
      have := Finset.card_nsmul_le_sum (Finset.range K) (fun l => (x l).t * c.κ) (c.t₀ / 2 * c.κ)
        (fun l hl => hsum_t l (Finset.mem_range.mp hl))
      simpa using this
    have h3 : c.δ * (c.t₀ / 2 * c.κ * K - (c.phaseSum m + K * X)) ≤
        c.δ * ∑ l ∈ Finset.range K, ((x l).t * c.κ - |(x l).a|) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      rw [h1]; nlinarith
    exact h3.trans hprog
  have hzK : ⟪(x K).z, w⟫ ≤ X := by
    have h1 := real_inner_le_norm (x K).z w
    rw [G.w_unit, mul_one] at h1
    have h2 : ‖(x K).z‖ ^ 2 ≤ X ^ 2 := by
      have := norm_z_sq_le_potential (by linarith [c.C_le] : c.C ≤ 1 / 2) (x K)
      linarith [hΨX K hk₁K le_rfl]
    have h3 := (pow_le_pow_iff_left₀ (norm_nonneg _) hX0 two_ne_zero).mp h2
    linarith
  have hmain : c.t₀ / 2 * c.κ * K ≤ c.phaseSum m + K * X + X / c.δ := by
    have := hsum.trans hzK
    have h1 : c.δ * (c.t₀ / 2 * c.κ * K - (c.phaseSum m + K * X)) ≤ c.δ * (X / c.δ) := by
      rw [mul_div_cancel₀ _ hδ.ne']; exact this
    have := le_of_mul_le_mul_left h1 hδ
    linarith
  have hKX : (K : ℝ) * X ≤ (1 / 64) * (X / c.δ) := by
    have : (K : ℝ) * X = (c.δ * K) * (X / c.δ) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hsmall (by positivity)
  have hXδ : X / c.δ ≤ 16 * c.C * c.t₀ * K + (2 * Real.sqrt 2 * c.F * m + c.tail m) +
      c.F * Real.sqrt (2 * K) := by
    have h := hXle.trans (by linarith : 16 * c.C * c.t₀ * c.δ * K +
      Real.sqrt (2 * potential c.C (x k₁) + 2 * c.δ ^ 2 * c.F ^ 2 * K) ≤
        16 * c.C * c.t₀ * c.δ * K + ((Real.sqrt 2 * (c.δ * c.F) * (2 * m) + W₂) +
          c.δ * c.F * Real.sqrt (2 * K)))
    rw [div_le_iff₀ hδ]
    have htail : W₂ = c.δ * c.tail m := by
      unfold Control.tail; rw [hW₂, hW₁, hZ₁]; field_simp
      try ring
    rw [htail] at h
    linarith [h]
  have hCt : 65 / 64 * (16 * c.C * c.t₀ * K) ≤ c.t₀ / 4 * c.κ * K := by
    have : 65 * c.C * c.t₀ ≤ c.κ * c.t₀ := mul_le_mul_of_nonneg_right hCκ ht₀.le
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hfinal : c.t₀ / 4 * c.κ * K ≤
      (c.phaseSum m + 65 / 64 * (2 * Real.sqrt 2 * c.F * m + c.tail m)) +
        65 / 64 * Real.sqrt 2 * c.F * Real.sqrt K := by
    have hs2K : Real.sqrt (2 * K) = Real.sqrt 2 * Real.sqrt K := Real.sqrt_mul (by norm_num) _
    rw [hs2K] at hXδ
    have hX65 : X / c.δ ≥ 0 := by positivity
    nlinarith
  set A := c.phaseSum m + 65 / 64 * (2 * Real.sqrt 2 * c.F * m + c.tail m) with hA
  set B := 65 / 64 * Real.sqrt 2 * c.F with hB
  have hA0 : 0 ≤ A := by
    rw [hA]; unfold Control.phaseSum Control.tail; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have htκ : 0 < c.t₀ * c.κ := mul_pos ht₀ hκ
  have hK' : (K : ℝ) ≤ 4 * A / (c.t₀ * c.κ) + 4 * B / (c.t₀ * c.κ) * Real.sqrt K := by
    rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ htκ]
    nlinarith
  have habs := absorb_sqrt (Nat.cast_nonneg K) (by positivity) (by positivity) hK'
  have : 2 * (4 * A / (c.t₀ * c.κ)) + 4 * (4 * B / (c.t₀ * c.κ)) ^ 2 = c.bound m := by
    unfold Control.bound; rw [hA, hB]; field_simp; ring
  have hm0' : (0 : ℝ) ≤ 2 * m := by positivity
  linarith

end Final

end LongTails.Proofs.TwoSidedPerceptronCounting
