import LongTails.Proofs.MinimaxLmoTrack
import LongTails.Proofs.HessianNcscProcess

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO constantMomentum)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax clip)

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)} {ρ : ℝ}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}
  {lmo : Space d₁ → Space d₁}

noncomputable def trk (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
    (lmo : Space d₁ → Space d₁) (γ a β c : ℝ) (ξ : ℕ → Ω) (k : ℕ) : ℝ :=
  ‖(cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 - ystar H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1‖

noncomputable def nxt (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
    (β c : ℝ) (z : Space d₁ × Space d₂) (ω : Ω) : ℝ :=
  ‖z.2 + β • clip c (oy z.1 z.2 ω) - ystar H hμ z.1‖

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
  (γ a β c : ℝ)

include H

lemma trk_step (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo : IsBallLMO N ρ lmo) (hγ : 0 ≤ γ) (hloc : L₁ * (γ * ρ) ≤ 1)
    (ξ : ℕ → Ω) (k : ℕ) :
    trk H hμ lmo γ a β c ξ (k + 1) ≤
      nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k) +
        L₀ / μ * (γ * ρ) := by
  set X := (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1
  set X' := (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).1
  have hX' : X' = X + γ • lmo (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2 := by
    simp only [X', X, cpath_succ]
  have hY' : (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.1 =
      (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 + β • clip c (oy X (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k)) := by
    simp only [X, cpath_succ]
  have hN : N (X' - X) ≤ γ * ρ := by
    rw [hX', add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (hlmo.feasible _) hγ
  have hL1 : L₁ * N (X' - X) ≤ 1 := (mul_le_mul_of_nonneg_left hN hL₁).trans hloc
  have hy := ystar_lip H hμ X' X hL1
  have hκ : L₀ / μ * N (X' - X) ≤ L₀ / μ * (γ * ρ) :=
    mul_le_mul_of_nonneg_left hN (div_nonneg hL₀ hμ.le)
  simp only [trk, nxt]
  rw [hY']
  have e : (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 + β • clip c (oy X (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k)) -
      ystar H hμ X' = ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 +
        β • clip c (oy X (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k)) - ystar H hμ X) +
      (ystar H hμ X - ystar H hμ X') := by abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_sub_rev]
  exact hy.trans hκ

noncomputable def gp (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
    (lmo : Space d₁ → Space d₁) (γ a β c r₀ : ℝ) (ξ : ℕ → Ω) (k : ℕ) : ℝ :=
  if ∀ j < k, trk H hμ lmo γ a β c ξ j ≤ r₀ then 1 else 0

lemma gp_nonneg (r₀ : ℝ) (ξ : ℕ → Ω) (k : ℕ) : 0 ≤ gp H hμ lmo γ a β c r₀ ξ k := by
  unfold gp; split_ifs <;> norm_num

lemma gp_le_one (r₀ : ℝ) (ξ : ℕ → Ω) (k : ℕ) : gp H hμ lmo γ a β c r₀ ξ k ≤ 1 := by
  unfold gp; split_ifs <;> norm_num

lemma gp_succ_le (r₀ : ℝ) (ξ : ℕ → Ω) (k : ℕ) :
    gp H hμ lmo γ a β c r₀ ξ (k + 1) ≤ gp H hμ lmo γ a β c r₀ ξ k := by
  unfold gp
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (fun j hj => h1 j (by omega)) h2
  · norm_num
  · exact le_rfl

lemma gp_succ_pos (r₀ : ℝ) (ξ : ℕ → Ω) (k : ℕ) (h : gp H hμ lmo γ a β c r₀ ξ (k + 1) ≠ 0) :
    trk H hμ lmo γ a β c ξ k ≤ r₀ := by
  unfold gp at h
  split_ifs at h with h1
  · exact h1 k (by omega)
  · exact absurd rfl h

lemma gp_bad (r₀ : ℝ) (ξ : ℕ → Ω) (n : ℕ) :
    1 - gp H hμ lmo γ a β c r₀ ξ n ≤ ∑ k ∈ Finset.range n,
      gp H hμ lmo γ a β c r₀ ξ k * (if r₀ < trk H hμ lmo γ a β c ξ k then 1 else 0) := by
  induction n with
  | zero => simp [gp]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have key : 1 - gp H hμ lmo γ a β c r₀ ξ (n + 1) ≤ 1 - gp H hμ lmo γ a β c r₀ ξ n +
          gp H hμ lmo γ a β c r₀ ξ n * (if r₀ < trk H hμ lmo γ a β c ξ n then 1 else 0) := by
        unfold gp
        by_cases h1 : ∀ j < n, trk H hμ lmo γ a β c ξ j ≤ r₀
        · by_cases h2 : trk H hμ lmo γ a β c ξ n ≤ r₀
          · have : ∀ j < n + 1, trk H hμ lmo γ a β c ξ j ≤ r₀ := fun j hj => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
              · exact h1 j h
              · rw [h]; exact h2
            rw [ite_eq_left this, ite_eq_left h1, ite_eq_right (not_lt.mpr h2)]; norm_num
          · have : ¬ ∀ j < n + 1, trk H hμ lmo γ a β c ξ j ≤ r₀ := fun h => h2 (h n (by omega))
            rw [ite_eq_right this, ite_eq_left h1, ite_eq_left (lt_of_not_ge h2)]; norm_num
        · have : ¬ ∀ j < n + 1, trk H hμ lmo γ a β c ξ j ≤ r₀ := fun h => h1 (fun j hj => h j (by omega))
          rw [ite_eq_right this, ite_eq_right h1]; norm_num
      linarith

lemma trk_measurable (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo : Measurable lmo) (k : ℕ) :
    Measurable fun ξ => trk H hμ lmo γ a β c ξ k := by
  have hpath := measurable_gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy
    hlmo H.measurable_x H.measurable_y k
  have hys := (ystar_continuous H hμ hL₀ hL₁).measurable
  exact (hpath.snd.fst.sub (hys.comp hpath.fst)).norm

lemma trk_dep (k : ℕ) (ξ ξ' : ℕ → Ω) (h : ∀ i, i < k → ξ i = ξ' i) :
    trk H hμ lmo γ a β c ξ k = trk H hμ lmo γ a β c ξ' k := by
  simp only [trk, cpath, gpath_congr lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c)
    x₁ y₁ ox oy k h]

lemma gp_measurable (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo : Measurable lmo) (r₀ : ℝ) (k : ℕ) :
    Measurable fun ξ => gp H hμ lmo γ a β c r₀ ξ k := by
  have hset : MeasurableSet {ξ : ℕ → Ω | ∀ j < k, trk H hμ lmo γ a β c ξ j ≤ r₀} := by
    have e : {ξ : ℕ → Ω | ∀ j < k, trk H hμ lmo γ a β c ξ j ≤ r₀} =
        ⋂ j ∈ {j : ℕ | j < k}, {ξ | trk H hμ lmo γ a β c ξ j ≤ r₀} := by
      ext ξ; simp
    rw [e]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (trk_measurable H hμ γ a β c hL₀ hL₁ hlmo j) measurable_const
  unfold gp
  exact Measurable.ite hset measurable_const measurable_const

lemma gp_dep (r₀ : ℝ) (k : ℕ) (ξ ξ' : ℕ → Ω) (h : ∀ i, i < k → ξ i = ξ' i) :
    gp H hμ lmo γ a β c r₀ ξ (k + 1) = gp H hμ lmo γ a β c r₀ ξ' (k + 1) := by
  unfold gp
  have hall : ∀ j < k + 1, trk H hμ lmo γ a β c ξ j = trk H hμ lmo γ a β c ξ' j := fun j hj =>
    trk_dep H hμ γ a β c j ξ ξ' fun i hi => h i (by omega)
  have : (∀ j < k + 1, trk H hμ lmo γ a β c ξ j ≤ r₀) ↔ (∀ j < k + 1, trk H hμ lmo γ a β c ξ' j ≤ r₀) :=
    ⟨fun h1 j hj => hall j hj ▸ h1 j hj, fun h1 j hj => (hall j hj).symm ▸ h1 j hj⟩
  simp only [this]

lemma nxt_le (hβ : 0 ≤ β) (hc : 0 ≤ c) (z : Space d₁ × Space d₂) (ω : Ω) :
    nxt H hμ β c z ω ≤ ‖z.2 - ystar H hμ z.1‖ + β * c := by
  simp only [nxt]
  have e : z.2 + β • clip c (oy z.1 z.2 ω) - ystar H hμ z.1 = (z.2 - ystar H hμ z.1) + β • clip c (oy z.1 z.2 ω) := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left (clip_norm_le hc _) hβ

set_option maxHeartbeats 1000000 in
theorem exit_step [IsProbabilityMeasure p] (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo_m : Measurable lmo)
    (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo) (hγ : 0 ≤ γ) (hloc : L₁ * (γ * ρ) ≤ 1)
    {lam r₀ aB : ℝ} (hβ : 0 ≤ β) (hβ2 : 2 * β * L₀ ^ 2 ≤ μ) (hc : 0 < c) (haB : 0 < aB) (hlam : 0 ≤ lam)
    (hlamB : lam * (β * c + L₀ / μ * (γ * ρ)) ≤ 1) (hr₀L : L₁ * r₀ ≤ 1) (hr₀c : L₀ * r₀ ≤ c / 2)
    (hcond : (8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2) / (2 * aB) + L₀ / μ * (γ * ρ) +
      lam * (4 * β ^ 2 * (L₀ ^ 2 * r₀ ^ 2 + σy ^ 2) + 2 * (L₀ / μ * (γ * ρ)) ^ 2) ≤ β * μ * aB / 4)
    (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ (k + 1) * Real.exp (lam * trk H hμ lmo γ a β c ξ (k + 1)))
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ∫⁻ ξ, ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ k * Real.exp (lam * trk H hμ lmo γ a β c ξ k))
        ∂(Measure.infinitePi fun _ : ℕ => p) +
      ENNReal.ofReal (Real.exp (lam * (aB + β * c + L₀ / μ * (γ * ρ)))) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set κs := L₀ / μ * (γ * ρ)
  have hκs : 0 ≤ κs := mul_nonneg (div_nonneg hL₀ hμ.le) (mul_nonneg hγ hρ.le)
  set C := ENNReal.ofReal (Real.exp (lam * (aB + β * c + κs)))
  have hpath := measurable_gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy
    hlmo_m H.measurable_x H.measurable_y
  have hys := (ystar_continuous H hμ hL₀ hL₁).measurable
  let S : (ℕ → Ω) → (Space d₁ × Space d₂) × ℝ := fun ξ =>
    (((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1),
      gp H hμ lmo γ a β c r₀ ξ (k + 1))
  have hS : Measurable S :=
    ((hpath k).fst.prodMk (hpath k).snd.fst).prodMk (gp_measurable H hμ γ a β c hL₀ hL₁ hlmo_m r₀ (k + 1))
  have hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ' := by
    intro ξ ξ' h
    simp only [S, cpath, gpath_congr lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c)
      x₁ y₁ ox oy k h, gp_dep H hμ γ a β c r₀ k ξ ξ' h]
  let hfun : ((Space d₁ × Space d₂) × ℝ) × Ω → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (w.1.2 * Real.exp (lam * (nxt H hμ β c w.1.1 w.2 + κs)))
  have hoy : Measurable fun w : ((Space d₁ × Space d₂) × ℝ) × Ω => oy w.1.1.1 w.1.1.2 w.2 :=
    H.measurable_y.comp ((measurable_fst.fst.fst.prodMk measurable_fst.fst.snd).prodMk measurable_snd)
  have hh : Measurable hfun := by
    have h1 : Measurable fun w : ((Space d₁ × Space d₂) × ℝ) × Ω => nxt H hμ β c w.1.1 w.2 :=
      ((measurable_fst.fst.snd.add (((clip_measurable c).comp hoy).const_smul β)).sub
        (hys.comp measurable_fst.fst.fst)).norm
    exact ENNReal.measurable_ofReal.comp (measurable_fst.snd.mul
      (Real.measurable_exp.comp ((h1.add measurable_const).const_mul lam)))
  have hpt : ∀ ξ, ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ (k + 1) *
      Real.exp (lam * trk H hμ lmo γ a β c ξ (k + 1))) ≤ hfun (S ξ, ξ k) := by
    intro ξ
    simp only [hfun, S]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (gp_nonneg H hμ γ a β c r₀ ξ (k + 1))
    rw [Real.exp_le_exp]
    have := trk_step H hμ γ a β c hL₀ hL₁ hlmo hγ hloc ξ k
    exact mul_le_mul_of_nonneg_left (by simpa using this) hlam
  have hinner : ∀ ξ, ∫⁻ ω, hfun (S ξ, ω) ∂p ≤
      ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ (k + 1) * Real.exp (lam * trk H hμ lmo γ a β c ξ k)) + C := by
    intro ξ
    by_cases hg : gp H hμ lmo γ a β c r₀ ξ (k + 1) = 0
    · simp only [hfun, S, hg, zero_mul, ENNReal.ofReal_zero, lintegral_zero]
      exact bot_le
    · have hg1 : gp H hμ lmo γ a β c r₀ ξ (k + 1) = 1 := by
        have h01 : gp H hμ lmo γ a β c r₀ ξ (k + 1) = 0 ∨ gp H hμ lmo γ a β c r₀ ξ (k + 1) = 1 := by
          unfold gp; split_ifs <;> simp
        exact h01.resolve_left hg
      have hD := gp_succ_pos H hμ γ a β c r₀ ξ k hg
      set x := (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1
      set y := (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1
      have hDe : trk H hμ lmo γ a β c ξ k = ‖y - ystar H hμ x‖ := rfl
      have hDL : L₁ * ‖y - ystar H hμ x‖ ≤ 1 := by
        rw [← hDe]; exact (mul_le_mul_of_nonneg_left hD hL₁).trans hr₀L
      have hG := grad_y_near H hμ x y hDL
      have hgy : ‖gy x y‖ ≤ c / 2 := by
        rw [← hDe] at hG
        exact hG.trans ((mul_le_mul_of_nonneg_left hD hL₀).trans hr₀c)
      simp only [hfun, S, hg1, one_mul]
      by_cases ha : aB ≤ ‖y - ystar H hμ x‖
      · obtain ⟨hint, hle⟩ := track_step_exp H hμ (κs := κs) (r₀ := r₀) hβ hβ2 hc hκs haB hlam hlamB x y hgy hG ha
          (by rw [← hDe]; exact hD) hcond
        have e : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (nxt H hμ β c (x, y) ω + κs))) ∂p =
            ENNReal.ofReal (∫ ω, Real.exp (lam * (‖y + β • clip c (oy x y ω) - ystar H hμ x‖ + κs)) ∂p) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
        rw [e, hDe]
        exact (ENNReal.ofReal_le_ofReal hle).trans le_self_add
      · push Not at ha
        have hb : ∀ ω, ENNReal.ofReal (Real.exp (lam * (nxt H hμ β c (x, y) ω + κs))) ≤ C := by
          intro ω
          apply ENNReal.ofReal_le_ofReal
          rw [Real.exp_le_exp]
          have := nxt_le H hμ β c hβ hc.le (x, y) ω
          simp only at this
          have h2 : nxt H hμ β c (x, y) ω + κs ≤ aB + β * c + κs := by linarith
          exact mul_le_mul_of_nonneg_left h2 hlam
        calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (nxt H hμ β c (x, y) ω + κs))) ∂p ≤ ∫⁻ _, C ∂p :=
              lintegral_mono hb
          _ = C := by simp
          _ ≤ _ := le_add_self
  have hfresh := OracleTemplate.HessianNcsc.fresh_lintegral p k S hS hdep hfun hh
  have hgm := gp_measurable H hμ γ a β c hL₀ hL₁ hlmo_m r₀ (k + 1)
  have htm := trk_measurable H hμ γ a β c hL₀ hL₁ hlmo_m k
  calc ∫⁻ ξ, ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ (k + 1) * Real.exp (lam * trk H hμ lmo γ a β c ξ (k + 1))) ∂P
      ≤ ∫⁻ ξ, hfun (S ξ, ξ k) ∂P := lintegral_mono hpt
    _ = ∫⁻ ξ, ∫⁻ ω, hfun (S ξ, ω) ∂p ∂P := hfresh
    _ ≤ ∫⁻ ξ, (ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ (k + 1) *
          Real.exp (lam * trk H hμ lmo γ a β c ξ k)) + C) ∂P := lintegral_mono hinner
    _ = ∫⁻ ξ, ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ (k + 1) *
          Real.exp (lam * trk H hμ lmo γ a β c ξ k)) ∂P + C := by
        rw [lintegral_add_right _ measurable_const]; simp
    _ ≤ _ := by
        gcongr with ξ
        exact gp_succ_le H hμ γ a β c r₀ ξ k

set_option maxHeartbeats 1000000 in
theorem exit_total [IsProbabilityMeasure p] (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo_m : Measurable lmo)
    (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo) (hγ : 0 ≤ γ) (hloc : L₁ * (γ * ρ) ≤ 1)
    {lam r₀ aB : ℝ} (hβ : 0 ≤ β) (hβ2 : 2 * β * L₀ ^ 2 ≤ μ) (hc : 0 < c) (haB : 0 < aB) (hlam : 0 ≤ lam)
    (hlamB : lam * (β * c + L₀ / μ * (γ * ρ)) ≤ 1) (hr₀L : L₁ * r₀ ≤ 1) (hr₀c : L₀ * r₀ ≤ c / 2)
    (hcond : (8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2) / (2 * aB) + L₀ / μ * (γ * ρ) +
      lam * (4 * β ^ 2 * (L₀ ^ 2 * r₀ ^ 2 + σy ^ 2) + 2 * (L₀ / μ * (γ * ρ)) ^ 2) ≤ β * μ * aB / 4)
    (n : ℕ) :
    Integrable (fun ξ => 1 - gp H hμ lmo γ a β c r₀ ξ n) (Measure.infinitePi fun _ : ℕ => p) ∧
    ∫ ξ, (1 - gp H hμ lmo γ a β c r₀ ξ n) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      n * (Real.exp (lam * W) + n * Real.exp (lam * (aB + β * c + L₀ / μ * (γ * ρ)))) *
        Real.exp (-(lam * r₀)) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set Cr := Real.exp (lam * (aB + β * c + L₀ / μ * (γ * ρ)))
  set Q : ℕ → ℝ≥0∞ := fun k => ∫⁻ ξ, ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ k *
    Real.exp (lam * trk H hμ lmo γ a β c ξ k)) ∂P
  have hQ0 : Q 0 ≤ ENNReal.ofReal (Real.exp (lam * W)) := by
    have hys := ystar_max H hμ x₁
    have hw := H.warm_start (ystar H hμ x₁) hys
    have h0 : ∀ ξ : ℕ → Ω, gp H hμ lmo γ a β c r₀ ξ 0 * Real.exp (lam * trk H hμ lmo γ a β c ξ 0) ≤
        Real.exp (lam * W) := by
      intro ξ
      have hg : gp H hμ lmo γ a β c r₀ ξ 0 = 1 := by unfold gp; simp
      have ht : trk H hμ lmo γ a β c ξ 0 = ‖y₁ - ystar H hμ x₁‖ := rfl
      rw [hg, one_mul, ht, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hw hlam
    calc Q 0 ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (lam * W)) ∂P :=
          lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (h0 ξ)
      _ = ENNReal.ofReal (Real.exp (lam * W)) := by simp
  have hQk : ∀ k, Q k ≤ ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr := by
    intro k
    induction k with
    | zero => simpa using hQ0
    | succ k ih =>
        have h := exit_step H hμ γ a β c hL₀ hL₁ hlmo_m hρ hlmo hγ hloc hβ hβ2 hc haB hlam hlamB hr₀L hr₀c hcond k
        calc Q (k + 1) ≤ Q k + ENNReal.ofReal Cr := h
          _ ≤ ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr + ENNReal.ofReal Cr := by gcongr
          _ = _ := by push_cast; ring
  have hgm := fun k => gp_measurable H hμ γ a β c hL₀ hL₁ hlmo_m r₀ k
  have htm := fun k => trk_measurable H hμ γ a β c hL₀ hL₁ hlmo_m k
  have hbad : ∀ ξ, ENNReal.ofReal (1 - gp H hμ lmo γ a β c r₀ ξ n) ≤
      ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(lam * r₀))) *
        ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ k * Real.exp (lam * trk H hμ lmo γ a β c ξ k)) := by
    intro ξ
    have h1 := gp_bad (lmo := lmo) H hμ γ a β c r₀ ξ n
    have h2 : ∀ k, gp H hμ lmo γ a β c r₀ ξ k * (if r₀ < trk H hμ lmo γ a β c ξ k then 1 else 0) ≤
        Real.exp (-(lam * r₀)) * (gp H hμ lmo γ a β c r₀ ξ k * Real.exp (lam * trk H hμ lmo γ a β c ξ k)) := by
      intro k
      have hg := gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ k
      have hind : (if r₀ < trk H hμ lmo γ a β c ξ k then (1 : ℝ) else 0) ≤
          Real.exp (-(lam * r₀)) * Real.exp (lam * trk H hμ lmo γ a β c ξ k) := by
        rw [← Real.exp_add]
        split_ifs with h
        · rw [Real.one_le_exp_iff]; nlinarith
        · exact (Real.exp_pos _).le
      nlinarith
    calc ENNReal.ofReal (1 - gp H hμ lmo γ a β c r₀ ξ n)
        ≤ ENNReal.ofReal (∑ k ∈ Finset.range n, Real.exp (-(lam * r₀)) *
            (gp H hμ lmo γ a β c r₀ ξ k * Real.exp (lam * trk H hμ lmo γ a β c ξ k))) :=
          ENNReal.ofReal_le_ofReal (h1.trans (Finset.sum_le_sum fun k _ => h2 k))
      _ = ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(lam * r₀)) *
            (gp H hμ lmo γ a β c r₀ ξ k * Real.exp (lam * trk H hμ lmo γ a β c ξ k))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro k _
          exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ k) (Real.exp_pos _).le)
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hfm : ∀ k, Measurable fun ξ => ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ k *
      Real.exp (lam * trk H hμ lmo γ a β c ξ k)) := fun k =>
    ENNReal.measurable_ofReal.comp ((hgm k).mul (Real.measurable_exp.comp ((htm k).const_mul lam)))
  have hlint : ∫⁻ ξ, ENNReal.ofReal (1 - gp H hμ lmo γ a β c r₀ ξ n) ∂P ≤
      ENNReal.ofReal (Real.exp (-(lam * r₀))) * ∑ k ∈ Finset.range n,
        (ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr) := by
    calc ∫⁻ ξ, ENNReal.ofReal (1 - gp H hμ lmo γ a β c r₀ ξ n) ∂P
        ≤ ∫⁻ ξ, ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(lam * r₀))) *
            ENNReal.ofReal (gp H hμ lmo γ a β c r₀ ξ k * Real.exp (lam * trk H hμ lmo γ a β c ξ k)) ∂P :=
          lintegral_mono hbad
      _ = ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(lam * r₀))) * Q k := by
          rw [lintegral_finsetSum _ fun k _ => (hfm k).const_mul _]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [lintegral_const_mul _ (hfm k)]
      _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(lam * r₀))) *
            (ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr) := by
          gcongr with k; exact hQk k
      _ = _ := by rw [Finset.mul_sum]
  have hrhs : ENNReal.ofReal (Real.exp (-(lam * r₀))) * ∑ k ∈ Finset.range n,
      (ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr) ≤
      ENNReal.ofReal (n * (Real.exp (lam * W) + n * Cr) * Real.exp (-(lam * r₀))) := by
    have hCr : 0 ≤ Cr := (Real.exp_pos _).le
    have hs : ∑ k ∈ Finset.range n, (ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr) ≤
        ENNReal.ofReal (n * (Real.exp (lam * W) + n * Cr)) := by
      calc ∑ k ∈ Finset.range n, (ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr)
          ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.exp (lam * W) + n * Cr) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
            rw [ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
            gcongr
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
            gcongr
            exact_mod_cast (Finset.mem_range.mp hk).le
        _ = ENNReal.ofReal (n * (Real.exp (lam * W) + n * Cr)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    calc ENNReal.ofReal (Real.exp (-(lam * r₀))) * ∑ k ∈ Finset.range n,
          (ENNReal.ofReal (Real.exp (lam * W)) + k * ENNReal.ofReal Cr)
        ≤ ENNReal.ofReal (Real.exp (-(lam * r₀))) * ENNReal.ofReal (n * (Real.exp (lam * W) + n * Cr)) := by
          gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  have hfm1 : Measurable fun ξ => 1 - gp H hμ lmo γ a β c r₀ ξ n := measurable_const.sub (hgm n)
  have hint : Integrable (fun ξ => 1 - gp H hμ lmo γ a β c r₀ ξ n) P :=
    Integrable.of_bound hfm1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ n, gp_le_one (lmo := lmo) H hμ γ a β c r₀ ξ n])
  refine ⟨hint, ?_⟩
  have h0 : 0 ≤ᵐ[P] fun ξ => 1 - gp H hμ lmo γ a β c r₀ ξ n :=
    Filter.Eventually.of_forall fun ξ => by
      show 0 ≤ 1 - gp H hμ lmo γ a β c r₀ ξ n; linarith [gp_le_one (lmo := lmo) H hμ γ a β c r₀ ξ n]
  rw [integral_eq_lintegral_of_nonneg_ae h0 hfm1.aestronglyMeasurable]
  have hfin := hlint.trans hrhs
  have hpos : 0 ≤ n * (Real.exp (lam * W) + n * Cr) * Real.exp (-(lam * r₀)) := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal hpos hfin)

lemma trk_bound (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo : IsBallLMO N ρ lmo) (hγ : 0 ≤ γ)
    (hloc : L₁ * (γ * ρ) ≤ 1) (hβ : 0 ≤ β) (hc : 0 ≤ c) (ξ : ℕ → Ω) :
    ∀ k, trk H hμ lmo γ a β c ξ k ≤ W + k * (β * c + L₀ / μ * (γ * ρ)) := by
  intro k
  induction k with
  | zero =>
      have hw := H.warm_start (ystar H hμ x₁) (ystar_max H hμ x₁)
      simpa [trk, cpath, gpath] using hw
  | succ k ih =>
      have h1 := trk_step H hμ γ a β c hL₀ hL₁ hlmo hγ hloc ξ k
      have h2 := nxt_le H hμ β c hβ hc ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
        (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k)
      have e : ‖((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1).2 -
          ystar H hμ ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1).1‖ =
          trk H hμ lmo γ a β c ξ k := rfl
      rw [e] at h2
      push_cast
      linarith

set_option maxHeartbeats 1000000 in
theorem track_total [IsProbabilityMeasure p] (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo_m : Measurable lmo)
    (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo) (hγ : 0 ≤ γ) (hloc : L₁ * (γ * ρ) ≤ 1)
    {r₀ : ℝ} (hβ : 0 < β) (hβ2 : 2 * β * L₀ ^ 2 ≤ μ) (hβμ : β * μ ≤ 1) (hc : 0 < c)
    (hr₀L : L₁ * r₀ ≤ 1) (hr₀c : L₀ * r₀ ≤ c / 2) (k : ℕ) :
    Integrable (fun ξ => gp H hμ lmo γ a β c r₀ ξ (k + 1) * trk H hμ lmo γ a β c ξ k ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1) * trk H hμ lmo γ a β c ξ k ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        (1 - β * μ / 4) ^ k * W ^ 2 + 4 / (β * μ) * (2 * (8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2) +
          5 * (L₀ / μ * (γ * ρ)) ^ 2 / (β * μ)) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set κs := L₀ / μ * (γ * ρ)
  have hκs : 0 ≤ κs := mul_nonneg (div_nonneg hL₀ hμ.le) (mul_nonneg hγ hρ.le)
  set E₁ := 8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2
  have hE₁ : 0 ≤ E₁ := by positivity
  set q := β * μ / 4
  have hq : 0 < q := by positivity
  set η := 2 * E₁ + 5 * κs ^ 2 / (β * μ)
  have hη : 0 ≤ η := by positivity
  have hpath := measurable_gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy
    hlmo_m H.measurable_x H.measurable_y
  have hys := (ystar_continuous H hμ hL₀ hL₁).measurable
  have hgm := fun k => gp_measurable H hμ γ a β c hL₀ hL₁ hlmo_m r₀ k
  have htm := fun k => trk_measurable H hμ γ a β c hL₀ hL₁ hlmo_m k
  have hB : ∀ k ξ, trk H hμ lmo γ a β c ξ k ≤ W + k * (β * c + κs) := fun k ξ =>
    trk_bound H hμ γ a β c hL₀ hL₁ hlmo hγ hloc hβ.le hc.le ξ k
  have hV : ∀ k, Integrable (fun ξ => gp H hμ lmo γ a β c r₀ ξ (k + 1) * trk H hμ lmo γ a β c ξ k ^ 2) P := by
    intro k
    refine Integrable.of_bound ((hgm (k + 1)).mul ((htm k).pow_const 2)).aestronglyMeasurable
      ((W + k * (β * c + κs)) ^ 2) (Filter.Eventually.of_forall fun ξ => ?_)
    have h0 := norm_nonneg ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 - ystar H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1)
    have hg0 := gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
    have hg1 := gp_le_one (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
    rw [Real.norm_of_nonneg (mul_nonneg hg0 (sq_nonneg _))]
    have ht : trk H hμ lmo γ a β c ξ k ^ 2 ≤ (W + k * (β * c + κs)) ^ 2 :=
      pow_le_pow_left₀ h0 (hB k ξ) 2
    nlinarith [sq_nonneg (trk H hμ lmo γ a β c ξ k)]
  have hrec : ∀ k, ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1 + 1) * trk H hμ lmo γ a β c ξ (k + 1) ^ 2 ∂P ≤
      (1 - q) * ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1) * trk H hμ lmo γ a β c ξ k ^ 2 ∂P + η := by
    intro k
    let S : (ℕ → Ω) → (Space d₁ × Space d₂) × ℝ := fun ξ =>
      (((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1),
        gp H hμ lmo γ a β c r₀ ξ (k + 1))
    have hS : Measurable S := ((hpath k).fst.prodMk (hpath k).snd.fst).prodMk (hgm (k + 1))
    have hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ' := by
      intro ξ ξ' h
      simp only [S, cpath, gpath_congr lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c)
        x₁ y₁ ox oy k h, gp_dep H hμ γ a β c r₀ k ξ ξ' h]
    let Φf : (Space d₁ × Space d₂) × ℝ → Ω → ℝ := fun z ω =>
      z.2 * ((1 + q) * nxt H hμ β c z.1 ω ^ 2 + (1 + 1 / q) * κs ^ 2)
    have hoy : Measurable fun w : ((Space d₁ × Space d₂) × ℝ) × Ω => oy w.1.1.1 w.1.1.2 w.2 :=
      H.measurable_y.comp ((measurable_fst.fst.fst.prodMk measurable_fst.fst.snd).prodMk measurable_snd)
    have hΦ : Measurable (Function.uncurry Φf) := by
      have h1 : Measurable fun w : ((Space d₁ × Space d₂) × ℝ) × Ω => nxt H hμ β c w.1.1 w.2 :=
        ((measurable_fst.fst.snd.add (((clip_measurable c).comp hoy).const_smul β)).sub
          (hys.comp measurable_fst.fst.fst)).norm
      exact measurable_fst.snd.mul (((h1.pow_const 2).const_mul _).add measurable_const)
    have hptw : ∀ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1 + 1) * trk H hμ lmo γ a β c ξ (k + 1) ^ 2 ≤
        Φf (S ξ) (ξ k) := by
      intro ξ
      simp only [Φf, S]
      have hg := gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
      have hgs := gp_succ_le (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
      have h1 := trk_step H hμ γ a β c hL₀ hL₁ hlmo hγ hloc ξ k
      have ht0 := norm_nonneg ((cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.1 -
        ystar H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).1)
      have hn0 : 0 ≤ nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k) := norm_nonneg _
      set t := trk H hμ lmo γ a β c ξ (k + 1)
      set u := nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k)
      have ht : 0 ≤ t := ht0
      have hsq : t ^ 2 ≤ (1 + q) * u ^ 2 + (1 + 1 / q) * κs ^ 2 := by
        have h2 : t ^ 2 ≤ (u + κs) ^ 2 := pow_le_pow_left₀ ht h1 2
        have h3 : (u + κs) ^ 2 ≤ (1 + q) * u ^ 2 + (1 + 1 / q) * κs ^ 2 := by
          have key : (1 + q) * u ^ 2 + (1 + 1 / q) * κs ^ 2 - (u + κs) ^ 2 = (q * u - κs) ^ 2 / q := by
            field_simp; ring
          have : 0 ≤ (q * u - κs) ^ 2 / q := by positivity
          linarith
        linarith
      have hrhs : 0 ≤ (1 + q) * u ^ 2 + (1 + 1 / q) * κs ^ 2 := by positivity
      calc gp H hμ lmo γ a β c r₀ ξ (k + 1 + 1) * t ^ 2 ≤ gp H hμ lmo γ a β c r₀ ξ (k + 1) * t ^ 2 :=
            mul_le_mul_of_nonneg_right hgs (sq_nonneg t)
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq hg
    have hΦi : Integrable (fun ξ => Φf (S ξ) (ξ k)) P := by
      refine Integrable.of_bound (hΦ.comp (hS.prodMk (measurable_pi_apply k))).aestronglyMeasurable
        ((1 + q) * (W + (k + 1) * (β * c + κs)) ^ 2 + (1 + 1 / q) * κs ^ 2)
        (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [Φf, S]
      have hg0 := gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
      have hg1 := gp_le_one (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
      have hn := nxt_le H hμ β c hβ.le hc.le ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k)
      have e : ‖((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1).2 -
          ystar H hμ ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1).1‖ =
          trk H hμ lmo γ a β c ξ k := rfl
      rw [e] at hn
      have hn0 : 0 ≤ nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k) := norm_nonneg _
      have hb := hB k ξ
      have hnb : nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k) ≤ W + (k + 1) * (β * c + κs) := by
        have : 0 ≤ κs := hκs; nlinarith
      have hsq := pow_le_pow_left₀ hn0 hnb 2
      have hin : 0 ≤ (1 + q) * nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k) ^ 2 + (1 + 1 / q) * κs ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hin)]
      have : (1 + q) * nxt H hμ β c ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1,
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1) (ξ k) ^ 2 + (1 + 1 / q) * κs ^ 2 ≤
          (1 + q) * (W + (k + 1) * (β * c + κs)) ^ 2 + (1 + 1 / q) * κs ^ 2 := by gcongr
      nlinarith
    have hfresh := TwoSidedPL.integral_prefix_dep p k S hS hdep Φf hΦ hΦi
    have hinner : ∀ ξ, ∫ ω, Φf (S ξ) ω ∂p ≤
        gp H hμ lmo γ a β c r₀ ξ (k + 1) * ((1 - q) * trk H hμ lmo γ a β c ξ k ^ 2) + η := by
      intro ξ
      by_cases hg : gp H hμ lmo γ a β c r₀ ξ (k + 1) = 0
      · simp only [Φf, S, hg, zero_mul, integral_zero]; linarith
      · have hg1 : gp H hμ lmo γ a β c r₀ ξ (k + 1) = 1 := by
          have h01 : gp H hμ lmo γ a β c r₀ ξ (k + 1) = 0 ∨ gp H hμ lmo γ a β c r₀ ξ (k + 1) = 1 := by
            unfold gp; split_ifs <;> simp
          exact h01.resolve_left hg
        have hD := gp_succ_pos H hμ γ a β c r₀ ξ k hg
        set x := (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1
        set y := (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1
        have hDe : trk H hμ lmo γ a β c ξ k = ‖y - ystar H hμ x‖ := rfl
        have hDL : L₁ * ‖y - ystar H hμ x‖ ≤ 1 := by
          rw [← hDe]; exact (mul_le_mul_of_nonneg_left hD hL₁).trans hr₀L
        have hG := grad_y_near H hμ x y hDL
        have hgy : ‖gy x y‖ ≤ c / 2 := by
          rw [← hDe] at hG
          exact hG.trans ((mul_le_mul_of_nonneg_left hD hL₀).trans hr₀c)
        obtain ⟨hsi, hsb⟩ := track_step_sq H hμ hβ.le hβ2 hc x y hgy hG
        simp only [Φf, S, hg1, one_mul]
        have hnx : ∀ ω, nxt H hμ β c (x, y) ω ^ 2 = ‖y + β • clip c (oy x y ω) - ystar H hμ x‖ ^ 2 :=
          fun ω => rfl
        show ∫ ω, (1 + q) * ‖y + β • clip c (oy x y ω) - ystar H hμ x‖ ^ 2 + (1 + 1 / q) * κs ^ 2 ∂p ≤ _
        rw [integral_add (hsi.const_mul _) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        rw [← hDe] at hsb
        have hq1 : (1 + q) * (1 - β * μ / 2) ≤ 1 - q := by
          simp only [q]; nlinarith [mul_pos hβ hμ]
        have h1q : 1 + q ≤ 2 := by simp only [q]; linarith
        have h1q2 : (1 + 1 / q) * κs ^ 2 ≤ 5 * κs ^ 2 / (β * μ) := by
          have hbm : 0 < β * μ := mul_pos hβ hμ
          rw [show 1 + 1 / q = 1 + 4 / (β * μ) by simp only [q]; field_simp]
          rw [le_div_iff₀ hbm]
          have : (1 + 4 / (β * μ)) * κs ^ 2 * (β * μ) = (β * μ + 4) * κs ^ 2 := by field_simp
          rw [this]
          nlinarith [sq_nonneg κs]
        have ht2 := sq_nonneg (trk H hμ lmo γ a β c ξ k)
        have h5 := mul_le_mul_of_nonneg_left hsb (by linarith : (0 : ℝ) ≤ 1 + q)
        have h6 := mul_le_mul_of_nonneg_right hq1 ht2
        have h7 : (1 + q) * E₁ ≤ 2 * E₁ := by nlinarith
        simp only [η]
        nlinarith
    have hRi : Integrable (fun ξ => gp H hμ lmo γ a β c r₀ ξ (k + 1) * ((1 - q) * trk H hμ lmo γ a β c ξ k ^ 2) + η) P := by
      have := (hV k).const_mul (1 - q)
      refine (this.congr ?_).add (integrable_const η)
      exact Filter.Eventually.of_forall fun ξ => by ring
    have hInner_i : Integrable (fun ξ => ∫ ω, Φf (S ξ) ω ∂p) P := by
      have hm : Measurable fun ξ => ∫ ω, Φf (S ξ) ω ∂p :=
        ((hΦ.stronglyMeasurable.integral_prod_right' :
          StronglyMeasurable fun z => ∫ ω, Φf z ω ∂p).measurable).comp hS
      refine Integrable.mono' hRi hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      have h0 : 0 ≤ ∫ ω, Φf (S ξ) ω ∂p := integral_nonneg fun ω => by
        have hg0 := gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ (k + 1)
        have hq0 : 0 ≤ (1 + q) * nxt H hμ β c (S ξ).1 ω ^ 2 + (1 + 1 / q) * κs ^ 2 := by positivity
        exact mul_nonneg hg0 hq0
      rw [Real.norm_of_nonneg h0]
      exact hinner ξ
    calc ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1 + 1) * trk H hμ lmo γ a β c ξ (k + 1) ^ 2 ∂P
        ≤ ∫ ξ, Φf (S ξ) (ξ k) ∂P := integral_mono (hV (k + 1)) hΦi hptw
      _ = ∫ ξ, ∫ ω, Φf (S ξ) ω ∂p ∂P := hfresh
      _ ≤ ∫ ξ, (gp H hμ lmo γ a β c r₀ ξ (k + 1) * ((1 - q) * trk H hμ lmo γ a β c ξ k ^ 2) + η) ∂P :=
          integral_mono hInner_i hRi hinner
      _ = (1 - q) * ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1) * trk H hμ lmo γ a β c ξ k ^ 2 ∂P + η := by
          rw [integral_add (((hV k).const_mul (1 - q)).congr (Filter.Eventually.of_forall fun ξ => by ring))
            (integrable_const η)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          rw [← integral_const_mul]
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          simp only; ring
  have hq1 : q ≤ 1 := by simp only [q]; linarith
  have hgeo := OracleTemplate.NormBallLMO.geometric_recursion (u := fun k =>
      ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (k + 1) * trk H hμ lmo γ a β c ξ k ^ 2 ∂P) hq hq1 hη hrec k
  have hu0 : ∫ ξ, gp H hμ lmo γ a β c r₀ ξ (0 + 1) * trk H hμ lmo γ a β c ξ 0 ^ 2 ∂P ≤ W ^ 2 := by
    have hb : ∀ ξ, gp H hμ lmo γ a β c r₀ ξ (0 + 1) * trk H hμ lmo γ a β c ξ 0 ^ 2 ≤ W ^ 2 := by
      intro ξ
      have h0 := hB 0 ξ
      simp only [CharP.cast_eq_zero, zero_mul, add_zero] at h0
      have ht0 := norm_nonneg ((cpath lmo γ a β c x₁ y₁ ox oy ξ 0).2.1 - ystar H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ 0).1)
      have hg0 := gp_nonneg (lmo := lmo) H hμ γ a β c r₀ ξ (0 + 1)
      have hg1 := gp_le_one (lmo := lmo) H hμ γ a β c r₀ ξ (0 + 1)
      have : trk H hμ lmo γ a β c ξ 0 ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ ht0 h0 2
      nlinarith [sq_nonneg (trk H hμ lmo γ a β c ξ 0)]
    calc _ ≤ ∫ _, W ^ 2 ∂P := integral_mono (hV 0) (integrable_const _) hb
      _ = W ^ 2 := by simp
  refine ⟨hV k, hgeo.trans ?_⟩
  have hpow : 0 ≤ (1 - q) ^ k := pow_nonneg (by linarith) k
  have e : η / q = 4 / (β * μ) * (2 * E₁ + 5 * κs ^ 2 / (β * μ)) := by
    simp only [η, q]; field_simp
  have := mul_le_mul_of_nonneg_left hu0 hpow
  rw [e]
  linarith

end OracleTemplate.MinimaxLmo
