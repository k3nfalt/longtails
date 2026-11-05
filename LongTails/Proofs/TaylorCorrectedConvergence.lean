import LongTails.Proofs.TaylorCorrectedEpoch
import LongTails.Proofs.FiniteSumThirdSmoothGeometry

namespace LongTails.Proofs.TaylorCorrectedConvergence

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Algorithms.TaylorCorrectedNewton
open LongTails.Setups.FiniteSumSmoothAndConvex
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [NeZero n]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [NeZero n] in
lemma diagonal_potential_bound {μ η B : ℝ} (hμ : 0 < μ) (n : ℕ) (u v : E)
    (hB : μ * ‖u - v‖ ^ 2 / 2 ≤ B) :
    ‖v - u‖ ^ 2 / 2 + (n : ℝ) * (η * B) ≤ (1 / μ + (n : ℝ) * η) * B := by
  rw [norm_sub_rev v u]
  have hh := (le_div_iff₀ hμ).mpr (show ‖u - v‖ ^ 2 / 2 * μ ≤ B by nlinarith only [hB])
  calc
    _ ≤ B / μ + (n : ℝ) * (η * B) := by simpa only [add_comm] using add_le_add_right hh ((n : ℝ) * (η * B))
    _ = _ := by ring

lemma epochs_descent (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ η : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 ≤ η)
    (hstep : 32 * η * L * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c z w u : E) (hw : w ∈ Metric.closedBall c ρ) (hu : u ∈ Metric.closedBall c ρ) (m : ℕ) :
    let F := objective f
    let B := fun v => F u - F v - ⟪gradient F v, u - v⟫
    let V := fun st : E × E => ‖st.1 - u‖ ^ 2 / 2 + (n : ℝ) * (η * B st.2)
    let D := fun v => η * (F v - F u) + η * B v
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 seeds : Fin m → EpochSeed n,
      let result := eval answer (epochs η ρ c m z w seeds)
      V (result.1, result.2.1) + (result.2.2.map D).sum) ≤ V (z, w) := by
  dsimp only
  apply TaylorCorrectedEpoch.epochs_potential
    (fun q => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)) hρ η c
    (fun st => ‖st.1 - u‖ ^ 2 / 2 + (n : ℝ) *
      (η * (objective f u - objective f st.2 - ⟪gradient (objective f) st.2, u - st.2⟫)))
    (fun v => η * (objective f v - objective f u) +
      η * (objective f u - objective f v - ⟪gradient (objective f) v, u - v⟫)) _ m z w hw
  intro z' w' hw'
  exact TaylorCorrectedEpoch.epoch_potential _ η ρ c w'
    (fun z => ‖z - u‖ ^ 2 / 2)
    (fun v => η * (objective f v - objective f u))
    (fun v => η * (objective f u - objective f v - ⟪gradient (objective f) v, u - v⟫))
    (fun z => FiniteSumThirdSmoothGeometry.step_potential f hf hc hL hρ hη hstep hT c z w' u hw' hu) z'

lemma restart_descent (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ η : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 ≤ η)
    (hstep : 32 * η * L * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y u : E) (hy : y ∈ Metric.closedBall c ρ) (hu : u ∈ Metric.closedBall c ρ) (m : ℕ) :
    let F := objective f
    let B := fun v => F u - F v - ⟪gradient F v, u - v⟫
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
      let v := eval answer (restart η ρ c y m seeds selection)
      η * (F v - F u) + η * B v) ≤
        (‖y - u‖ ^ 2 / 2 + (n : ℝ) * (η * B y)) / (n * m : ℕ) := by
  dsimp only
  apply TaylorCorrectedEpoch.restart_average_bound
    (fun q => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)) hρ η c
    (fun st => ‖st.1 - u‖ ^ 2 / 2 + (n : ℝ) *
      (η * (objective f u - objective f st.2 - ⟪gradient (objective f) st.2, u - st.2⟫)))
    (fun v => η * (objective f v - objective f u) +
      η * (objective f u - objective f v - ⟪gradient (objective f) v, u - v⟫)) _ _ m y hy
  · intro st
    exact add_nonneg (by positivity) (mul_nonneg (by positivity)
      (mul_nonneg hη (FiniteSumThirdSmoothGeometry.bregman_nonneg f hf hc u st.2)))
  · intro z w hw
    exact TaylorCorrectedEpoch.epoch_potential _ η ρ c w
      (fun z => ‖z - u‖ ^ 2 / 2)
      (fun v => η * (objective f v - objective f u))
      (fun v => η * (objective f u - objective f v - ⟪gradient (objective f) v, u - v⟫))
      (fun z => FiniteSumThirdSmoothGeometry.step_potential f hf hc hL hρ hη hstep hT c z w u hw hu) z

lemma restart_gap_bound (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ η : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (hstep : 32 * η * L * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y u : E) (hy : y ∈ Metric.closedBall c ρ) (hu : u ∈ Metric.closedBall c ρ) (m : ℕ) :
    let F := objective f
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
      (F (eval answer (restart η ρ c y m seeds selection)) - F u)) ≤
        (‖y - u‖ ^ 2 / 2 + (n : ℝ) *
          (η * (F u - F y - ⟪gradient F y, u - y⟫))) / (η * (n * m : ℕ)) := by
  let F := objective f
  let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  let Y := fun (seeds : Fin m → EpochSeed n) (selection : Fin (n * m)) =>
    eval answer (restart η ρ c y m seeds selection)
  let Φ := ‖y - u‖ ^ 2 / 2 + (n : ℝ) * (η * (F u - F y - ⟪gradient F y, u - y⟫))
  have hh := restart_descent f hf hc hL hρ hη.le hstep hT c y u hy hu m
  change (𝔼 seeds, 𝔼 selection,
    (η * (F (Y seeds selection) - F u) +
      η * (F u - F (Y seeds selection) - ⟪gradient F (Y seeds selection), u - Y seeds selection⟫))) ≤
        Φ / (n * m : ℕ) at hh
  have hl : (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
      η * (F (Y seeds selection) - F u)) ≤
      (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
        (η * (F (Y seeds selection) - F u) +
          η * (F u - F (Y seeds selection) - ⟪gradient F (Y seeds selection), u - Y seeds selection⟫))) := by
    apply Finset.expect_le_expect
    intro seeds _
    apply Finset.expect_le_expect
    intro selection _
    exact le_add_of_nonneg_right (mul_nonneg hη.le
      (FiniteSumThirdSmoothGeometry.bregman_nonneg f hf hc u (Y seeds selection)))
  have ht := hl.trans hh
  simp only [← Finset.mul_expect] at ht
  change (𝔼 seeds, 𝔼 selection, (F (Y seeds selection) - F u)) ≤ Φ / (η * (n * m : ℕ))
  have hdiv := (le_div_iff₀ hη).mpr
    (show (𝔼 seeds, 𝔼 selection, (F (Y seeds selection) - F u)) * η ≤ Φ / (n * m : ℕ) by
      simpa only [mul_comm] using ht)
  simpa only [div_div, mul_comm] using hdiv

lemma restart_contraction (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ η μ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 < η) (hμ : 0 < μ)
    (hstep : 32 * η * L * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y u : E) (hy : y ∈ Metric.closedBall c ρ) (hu : u ∈ Metric.closedBall c ρ)
    (hmin : IsMinOn (objective f) (Metric.closedBall c ρ) u)
    (hstrong : ∀ v ∈ Metric.closedBall c ρ,
      μ * ‖u - v‖ ^ 2 / 2 ≤ objective f u - objective f v - ⟪gradient (objective f) v, u - v⟫)
    (m : ℕ) :
    let F := objective f
    let B := fun v => F u - F v - ⟪gradient F v, u - v⟫
    let Φ := fun v => ‖v - u‖ ^ 2 / 2 + (n : ℝ) * (η * B v)
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
      Φ (eval answer (restart η ρ c y m seeds selection))) ≤
        ((n : ℝ) + 1 / (η * μ)) / (n * m : ℕ) * Φ y := by
  dsimp only
  let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  let B := fun v => objective f u - objective f v - ⟪gradient (objective f) v, u - v⟫
  let Φ := fun v => ‖v - u‖ ^ 2 / 2 + (n : ℝ) * (η * B v)
  let C := (n : ℝ) + 1 / (η * μ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : C * η = 1 / μ + (n : ℝ) * η := by dsimp [C]; field_simp; ring
  have hp (v : E) (hv : v ∈ Metric.closedBall c ρ) :
      Φ v ≤ C * (η * (objective f v - objective f u) + η * B v) := by
    have hd := diagonal_potential_bound (η := η) hμ n u v (hstrong v hv)
    have hg : 0 ≤ objective f v - objective f u := sub_nonneg.mpr (hmin hv)
    have hn := mul_nonneg (mul_nonneg hC hη.le) hg
    dsimp only [Φ, B]
    rw [← he] at hd
    nlinarith only [hd, hn]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun seeds _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun selection _ =>
      hp _ (TaylorCorrectedEpoch.restart_mem answer hρ η c y m seeds selection)))
  simp only [← Finset.mul_expect] at hh
  have hd := mul_le_mul_of_nonneg_left
    (restart_descent f hf hc hL hρ hη.le hstep hT c y u hy hu m) hC
  dsimp only at hd
  change (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
    Φ (eval answer (restart η ρ c y m seeds selection))) ≤ C / (n * m : ℕ) * Φ y
  apply hh.trans
  convert hd using 1
  dsimp only [answer, Φ, B]
  ring

omit [NeZero n] in
lemma restarts_mem (oracle : Fin n × E → Reply E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (η : ℝ) (c : E) (m J : ℕ) (y : E) (hy : y ∈ Metric.closedBall c ρ)
    (seeds : Fin J → RestartSeed n m) :
    eval oracle (restarts η ρ c m J y seeds) ∈ Metric.closedBall c ρ := by
  induction J generalizing y with
  | zero => exact hy
  | succ J ih =>
    rw [restarts, eval_bind]
    exact ih _ (TaylorCorrectedEpoch.restart_mem oracle hρ η c y m (seeds 0).1 (seeds 0).2) _

omit [NeZero n] in
lemma restarts_potential (oracle : Fin n × E → Reply E) {ρ q : ℝ}
    (hρ : 0 ≤ ρ) (hq : 0 ≤ q) (η : ℝ) (c : E) (m : ℕ)
    (Φ : E → ℝ)
    (hr : ∀ y, y ∈ Metric.closedBall c ρ →
      (𝔼 seed : RestartSeed n m, Φ (eval oracle (restart η ρ c y m seed.1 seed.2))) ≤ q * Φ y)
    (J : ℕ) (y : E) (hy : y ∈ Metric.closedBall c ρ) :
    (𝔼 seeds : Fin J → RestartSeed n m, Φ (eval oracle (restarts η ρ c m J y seeds))) ≤
      q ^ J * Φ y := by
  induction J generalizing y with
  | zero => simp [restarts, eval]
  | succ J ih =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    simp only [restarts, eval_bind, Fin.cons_zero, Fin.cons_succ]
    have hh := Finset.expect_le_expect (s := Finset.univ) (fun (seed : RestartSeed n m) _ =>
      ih _ (TaylorCorrectedEpoch.restart_mem oracle hρ η c y m seed.1 seed.2))
    simp only [← Finset.mul_expect] at hh
    have hr' := mul_le_mul_of_nonneg_left (hr y hy) (pow_nonneg hq J)
    exact hh.trans (hr'.trans_eq (show q ^ J * (q * Φ y) = q ^ (J + 1) * Φ y by rw [pow_succ]; ring))

omit [NeZero n] in
lemma restarts_gap (oracle : Fin n × E → Reply E) {ρ q a : ℝ}
    (hρ : 0 ≤ ρ) (hq : 0 ≤ q) (ha : 0 ≤ a) (η : ℝ) (c : E) (m : ℕ)
    (Φ G : E → ℝ)
    (hr : ∀ y, y ∈ Metric.closedBall c ρ →
      (𝔼 seed : RestartSeed n m, Φ (eval oracle (restart η ρ c y m seed.1 seed.2))) ≤ q * Φ y)
    (hg : ∀ y, y ∈ Metric.closedBall c ρ →
      (𝔼 seed : RestartSeed n m, G (eval oracle (restart η ρ c y m seed.1 seed.2))) ≤ a * Φ y)
    (J : ℕ) (y : E) (hy : y ∈ Metric.closedBall c ρ) :
    (𝔼 seeds : Fin (J + 1) → RestartSeed n m,
      G (eval oracle (restarts η ρ c m (J + 1) y seeds))) ≤ a * q ^ J * Φ y := by
  induction J generalizing y with
  | zero =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    simpa only [restarts, eval_bind, eval, Fin.cons_zero, Fintype.expect_const, pow_zero, mul_one]
      using hg y hy
  | succ J ih =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    have he (seed : RestartSeed n m) (seeds : Fin (J + 1) → RestartSeed n m) :
        eval oracle (restarts η ρ c m (J + 1 + 1) y (Fin.cons seed seeds)) =
          eval oracle (restarts η ρ c m (J + 1)
            (eval oracle (restart η ρ c y m seed.1 seed.2)) seeds) := by
      rw [restarts, eval_bind]
      rfl
    simp only [he]
    have hh := Finset.expect_le_expect (s := Finset.univ) (fun (seed : RestartSeed n m) _ =>
      ih _ (TaylorCorrectedEpoch.restart_mem oracle hρ η c y m seed.1 seed.2))
    simp only [← Finset.mul_expect] at hh
    have hr' := mul_le_mul_of_nonneg_left (hr y hy) (mul_nonneg ha (pow_nonneg hq J))
    exact hh.trans (hr'.trans_eq (show a * q ^ J * (q * Φ y) = a * q ^ (J + 1) * Φ y by rw [pow_succ]; ring))

end LongTails.Proofs.TaylorCorrectedConvergence
