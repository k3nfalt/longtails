import LongTails.Proofs.NearestAimingExecution
import LongTails.Proofs.NearestAimingTuning
import LongTails.Proofs.NearestSetLocal
import LongTails.Proofs.NearestSetContainment

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.NearestAiming

open LongTails.Setups.LocalStrongAiming

lemma nesterov_rate (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x) (xstar : p.E)
    (hmin : IsMinOn f univ xstar) (hgap : f p.x0 - f xstar ≤ p.Δ)
    (hlocal : let M := {x | f x = f xstar}
      infDist p.x0 M < p.r ∧
      (∀ x y, infDist x M < p.r → infDist y M < p.r →
        ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
      (∀ x y, infDist x M < p.r → infDist y M < p.r →
        f x + ⟪gradient f x, y - x⟫ - Real.sqrt (p.μ * p.L) * ‖y - x‖ ^ 2 ≤ f y) ∧
      (∀ x z, infDist x M < p.r → z ∈ M → infDist x M = ‖x - z‖ →
        f x - f xstar + p.μ / 2 * ‖x - z‖ ^ 2 ≤ ⟪gradient f x, x - z⟫)) (K : ℕ) :
    f (nesterovOutput (gradient f) p.L p.μ p.x0 K) - f xstar ≤
      (1 - Real.sqrt p.μ * (1 / (2 * Real.sqrt p.L))) ^ K * (2 * p.Δ) := by
  classical
  have hpvalid := hp
  obtain ⟨hμ, hμL, hr, hΔ, hsmall, hε⟩ := hp
  let a := Real.sqrt p.μ
  let s := 1 / (2 * Real.sqrt p.L)
  let B := 2 * Real.sqrt p.Δ
  obtain ⟨ha, hs, hq, ha2, hsL, hρ, hB0, hB2, hB⟩ := parameters p hpvalid
  change 0 < a at ha
  change 0 < s at hs
  change a * s ≤ 1 / 2 at hq
  change a ^ 2 = p.μ at ha2
  change s ^ 2 * p.L = 1 / 4 at hsL
  change (2 * Real.sqrt (p.μ * p.L)) * s ^ 2 = a * s at hρ
  change 0 ≤ B at hB0
  change B ^ 2 / 2 = 2 * p.Δ at hB2
  change B ≤ a * p.r / 8 at hB
  let M : Set p.E := {x | f x = f xstar}
  let F := fun x => f x - f xstar
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)
  have hM : IsClosed M := isClosed_eq hfcont continuous_const
  have hne : M.Nonempty := ⟨xstar, rfl⟩
  let π := fun x => Classical.choose (hM.exists_infDist_eq_dist hne x)
  have hπmem : ∀ x, π x ∈ M := fun x =>
    (Classical.choose_spec (hM.exists_infDist_eq_dist hne x)).1
  have hπnear : ∀ x, infDist x M = ‖x - π x‖ := by
    intro x
    exact (Classical.choose_spec (hM.exists_infDist_eq_dist hne x)).2.trans (dist_eq_norm _ _)
  have hvalue : ∀ z ∈ M, f z = f xstar := fun _ hz => hz
  have hminz : ∀ z ∈ M, IsMinOn f univ z := by
    intro z hz w hw
    rw [hvalue z hz]
    exact hmin hw
  have hF0 : ∀ x, 0 ≤ F x := fun x => sub_nonneg.mpr (hmin (mem_univ x))
  obtain ⟨hstart, hlip, hweak, haim⟩ := hlocal
  have hgrowth : ∀ x, infDist x M < p.r → a ^ 2 / 2 * infDist x M ^ 2 ≤ F x := by
    intro x hx
    have h := NearestSet.local_quadratic_growth hg (hπmem x) (hminz _ (hπmem x))
      (hπnear x) hx (by
        intro y z hy hz hn
        simpa only [hvalue (π x) (hπmem x)] using haim y z hy hz hn)
    simpa only [ha2, hπnear x, F, hvalue (π x) (hπmem x)] using h
  let query := fun state : p.E × p.E => state.1 + s • state.2
  let T := fun state : p.E × p.E => nesterovStep p.L p.μ state (gradient f (query state))
  let En := fun state : p.E × p.E =>
    NearestSet.energy M F a s state.1 state.2 (π (query state))
  have hEn_ge : ∀ state, F state.1 ≤ En state := by
    intro state
    exact NearestSet.energy_nonneg ha.le hs.le (hπmem _) (hπnear _)
  have hinit : En (p.x0, 0) ≤ 2 * p.Δ := by
    have hqg := hgrowth p.x0 hstart
    dsimp [En, query, NearestSet.energy, NearestSet.divergence]
    simp only [smul_zero, add_zero, sub_self, inner_zero_right, mul_zero,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, zero_add]
    rw [← hπnear p.x0]
    change F p.x0 + 1 / 2 * (a ^ 2 * infDist p.x0 M ^ 2) ≤ 2 * p.Δ
    change F p.x0 ≤ p.Δ at hgap
    linarith
  have hq0 : 0 ≤ 1 - a * s := by linarith
  have hq1 : 1 - a * s ≤ 1 := by nlinarith [mul_nonneg ha.le hs.le]
  have hstep : ∀ state, infDist state.1 M < p.r → infDist (query state) M < p.r →
      En state ≤ 2 * p.Δ →
      infDist (T state).1 M < p.r ∧ infDist (query (T state)) M < p.r ∧
        En (T state) ≤ (1 - a * s) * En state := by
    intro state hx hy he
    let y := query state
    let g := gradient f y
    let z := y - s ^ 2 • g
    let w := ((1 - a * s) / (1 + a * s)) • (state.2 - s • g)
    have hT : T state = (z, w) := rfl
    have hcontrol := NearestSet.energy_control ha hs.le hq hB0
      (hπmem y) (hπnear y) (hgrowth state.1 hx) (he.trans_eq hB2.symm)
    have hgBound : ‖g‖ ≤ p.L * infDist y M :=
      NearestSet.gradient_bound hg hlip (hπmem y) (hminz _ (hπmem y)) (hπnear y) hy
    have hcontain := NearestSet.step_containment ha hs hr hq hsL.le hB
      hcontrol.1 hcontrol.2 hgBound
    change (∀ t ∈ Icc (0 : ℝ) 1, infDist (y - (t * s ^ 2) • g) M < p.r) ∧
      infDist z M < p.r ∧ infDist (z + s • w) M < p.r at hcontain
    have hd : F z ≤ F y - s ^ 2 / 2 * ‖g‖ ^ 2 := by
      have h := NearestSet.descent_on_segment hg hlip hy
        (show s ^ 2 * p.L ≤ 1 by linarith) hcontain.1
      dsimp [F, z, g]
      linarith
    have hwk : F y - s * ⟪g, state.2⟫ -
        (2 * Real.sqrt (p.μ * p.L)) * s ^ 2 / 2 * ‖state.2‖ ^ 2 ≤ F state.1 := by
      have h := hweak y state.1 hy hx
      have hvect : state.1 - y = -s • state.2 := by dsimp [y, query]; module
      rw [hvect] at h
      simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
      dsimp [F, g]
      nlinarith only [h]
    have haimy : F y + a ^ 2 / 2 * ‖y - π y‖ ^ 2 ≤ ⟪g, y - π y⟫ := by
      simpa only [ha2] using haim y (π y) hy (hπmem y) (hπnear y)
    have he' := NearestSet.energy_step hM hne F state.1 state.2 g (π y)
      (π (z + s • w)) a s (2 * Real.sqrt (p.μ * p.L)) ha.le hs
      (by linarith) hρ.le (hπmem y) (hπnear y) hd haimy hwk (hπnear (z + s • w))
    rw [hT]
    exact ⟨hcontain.2.1, hcontain.2.2, he'⟩
  have hind : ∀ k : ℕ,
      infDist (T^[k] (p.x0, 0)).1 M < p.r ∧
      infDist (query (T^[k] (p.x0, 0))) M < p.r ∧
      En (T^[k] (p.x0, 0)) ≤ (1 - a * s) ^ k * (2 * p.Δ) := by
    intro k
    induction k with
    | zero => simpa [query] using And.intro hstart (And.intro hstart hinit)
    | succ k ih =>
      have he : En (T^[k] (p.x0, 0)) ≤ 2 * p.Δ :=
        ih.2.2.trans (mul_le_of_le_one_left (by positivity) (pow_le_one₀ hq0 hq1))
      obtain ⟨hx, hy, he'⟩ := hstep (T^[k] (p.x0, 0)) ih.1 ih.2.1 he
      rw [Function.iterate_succ_apply']
      refine ⟨hx, hy, he'.trans ?_⟩
      calc
        (1 - a * s) * En (T^[k] (p.x0, 0)) ≤
            (1 - a * s) * ((1 - a * s) ^ k * (2 * p.Δ)) :=
          mul_le_mul_of_nonneg_left ih.2.2 hq0
        _ = (1 - a * s) ^ (k + 1) * (2 * p.Δ) := by ring
  exact (hEn_ge (T^[K] (p.x0, 0))).trans (hind K).2.2

end OracleTemplate.NearestAiming
