import LongTails.Proofs.HiddenConvexExpectation

open Set Metric InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

section pathwise

variable {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {U : Set E} {x0 : E} {R μ LJ : ℝ}

lemma energy_pathwise {u x z g : E} {L σ : ℝ} (k : ℕ)
    (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hreg : 32 * LJ * R ≤ μ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hF : ∀ x, HasGradientAt F (gradient F x) x)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hu : u ∈ closedBall x0 R) (hx : x ∈ closedBall x0 (2 * R))
    (hz : z ∈ closedBall x0 (2 * R)) :
    energy F c J x0 L σ R u (k + 1)
        (mixPoint k x (dualStep L σ R x0 k z g), dualStep L σ R x0 k z g) ≤
      energy F c J x0 L σ R u k (x, z) +
      ⟪g - gradient F (mixPoint k x z),
        -((((k : ℝ) + 1) / 2) • (z - u)) + (((k : ℝ) + 1) / 2) • corr c J (mixPoint k x z) u +
          ((k : ℝ) * ((k : ℝ) + 1) / 4) • corr c J (mixPoint k x z) x⟫ +
      ((k : ℝ) + 1) ^ 2 / (2 * stepScale L σ R k) * ‖g - gradient F (mixPoint k x z)‖ ^ 2 +
      ((96 * stepScale L σ R k * (LJ / μ) * R ^ 3 * (2 / ((k : ℝ) + 3)) +
          3328 * stepScale L σ R k * (LJ / μ) ^ 2 * R ^ 4 * (2 / ((k : ℝ) + 2)) ^ 2) +
        (stepScale L σ R (k + 1) - stepScale L σ R k) * (171 / 32 * R ^ 2)) := by
  set D := stepScale L σ R k with hD
  set D' := stepScale L σ R (k + 1) with hD'
  have hDpos : 0 < D := stepScale_pos hL hσ hR k
  have hDD : D ≤ D' := stepScale_mono hσ hR (Nat.le_succ k)
  set z' := dualStep L σ R x0 k z g with hz'
  set x' := mixPoint k x z' with hx'
  set y := mixPoint k x z with hy
  set y' := mixPoint (k + 1) x' z' with hy'
  have hz'B : z' ∈ closedBall x0 (2 * R) := ballProj_mem x0 _ (by positivity)
  have hx'B : x' ∈ closedBall x0 (2 * R) := mixPoint_mem k hx hz'B
  have hyB : y ∈ closedBall x0 (2 * R) := mixPoint_mem k hx hz
  have hy'B : y' ∈ closedBall x0 (2 * R) := mixPoint_mem (k + 1) hx'B hz'B
  have hw : z - (((k : ℝ) + 1) / (2 * D)) • g = z - ((((k : ℝ) + 1) / 2) / D) • g := by
    rw [div_div]
  have hb := step_bound (g := g) k hm hR hμ hLJ hreg hL.le (stepScale_ge hσ hR k) hDpos hF hlip
    hu hx hz (a := ((k : ℝ) + 1) / 2) (A := (k : ℝ) * ((k : ℝ) + 1) / 4)
    (A' := ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) (τ := 2 / ((k : ℝ) + 2))
    (τ' := 2 / ((k : ℝ) + 3)) (M := LJ / μ) rfl rfl rfl rfl rfl rfl
    (y := y) (w := z - (((k : ℝ) + 1) / (2 * D)) • g) (z' := z') (x' := x') (y' := y')
    rfl hw rfl rfl rfl
  have hq'n := hm.corr_small hR hμ hLJ hreg hu hy'B
  have h3 : ‖z' - u‖ ≤ 3 * R := by rw [norm_sub_rev]; exact norm_sub_le_three hz'B hu
  have hsq : 1 / 2 * ‖z' - u‖ ^ 2 ≤ 9 / 2 * R ^ 2 := by
    have : ‖z' - u‖ ^ 2 ≤ (3 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith
  have hin : -⟪z' - u, corr c J y' u⟫ ≤ 27 / 32 * R ^ 2 := by
    have e := neg_le_abs ⟪z' - u, corr c J y' u⟫
    have e2 := abs_real_inner_le_norm (z' - u) (corr c J y' u)
    have e3 : ‖z' - u‖ * ‖corr c J y' u‖ ≤ (3 * R) * (9 * R / 32) :=
      mul_le_mul h3 hq'n (norm_nonneg _) (by positivity)
    nlinarith
  have hgap : (D' - D) * (1 / 2 * ‖z' - u‖ ^ 2 - ⟪z' - u, corr c J y' u⟫) ≤
      (D' - D) * (171 / 32 * R ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hDD)
    linarith
  have hlin : ⟪g - gradient F y, -((((k : ℝ) + 1) / 2) • (z - u)) +
      (((k : ℝ) + 1) / 2) • corr c J y u + ((k : ℝ) * ((k : ℝ) + 1) / 4) • corr c J y x⟫ =
      -(((k : ℝ) + 1) / 2 * ⟪g - gradient F y, z - u⟫) +
        ((k : ℝ) + 1) / 2 * ⟪g - gradient F y, corr c J y u⟫ +
        (k : ℝ) * ((k : ℝ) + 1) / 4 * ⟪g - gradient F y, corr c J y x⟫ := by
    simp only [inner_add_right, inner_neg_right, inner_smul_right]
  have hcoef : 2 * (((k : ℝ) + 1) / 2) ^ 2 / D = ((k : ℝ) + 1) ^ 2 / (2 * D) := by
    field_simp
  have hE1 : energy F c J x0 L σ R u (k + 1) (x', z') =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 * (F x' - F u) + D / 2 * ‖z' - u‖ ^ 2 -
        D * ⟪z' - u, corr c J y' u⟫ +
        (D' - D) * (1 / 2 * ‖z' - u‖ ^ 2 - ⟪z' - u, corr c J y' u⟫) := by
    unfold energy
    simp only
    rw [qField_eq hy'B, ← hD']
    push_cast
    ring
  have hE0 : energy F c J x0 L σ R u k (x, z) =
      (k : ℝ) * ((k : ℝ) + 1) / 4 * (F x - F u) + D / 2 * ‖z - u‖ ^ 2 -
        D * ⟪z - u, corr c J y u⟫ := by
    unfold energy
    simp only
    rw [qField_eq hyB]
  rw [hE1, hE0, hlin]
  rw [hcoef] at hb
  linarith

end pathwise

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω]

section stochastic

variable {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {U : Set E} {x0 : E} {R μ LJ : ℝ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma measurable_dualStep {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L σ R : ℝ) (x0 : E) (k : ℕ) (y z : E) :
    Measurable (fun ω => dualStep L σ R x0 k z (g y ω)) := by
  have hgm : Measurable (g y) := hg.comp (measurable_const.prodMk measurable_id)
  unfold dualStep
  exact (ballProj_measurable x0 (2 * R)).comp (measurable_const.sub (hgm.const_smul _))

lemma energy_step {u x z : E} {L σ : ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    (k : ℕ) (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hreg : 32 * LJ * R ≤ μ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hF : ∀ x, HasGradientAt F (gradient F x) x)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient E Ω p F g σ)
    (hu : u ∈ closedBall x0 R) (hmin : IsMinOn F univ u)
    (hx : x ∈ closedBall x0 (2 * R)) (hz : z ∈ closedBall x0 (2 * R)) :
    Integrable (fun ω => energy F c J x0 L σ R u (k + 1)
      (mixPoint k x (dualStep L σ R x0 k z (g (mixPoint k x z) ω)),
        dualStep L σ R x0 k z (g (mixPoint k x z) ω))) p ∧
    (∫ ω, energy F c J x0 L σ R u (k + 1)
      (mixPoint k x (dualStep L σ R x0 k z (g (mixPoint k x z) ω)),
        dualStep L σ R x0 k z (g (mixPoint k x z) ω)) ∂p) ≤
      energy F c J x0 L σ R u k (x, z) + stepCost L σ R (LJ / μ) k := by
  set y := mixPoint k x z with hy
  set V : E := -((((k : ℝ) + 1) / 2) • (z - u)) + (((k : ℝ) + 1) / 2) • corr c J y u +
    ((k : ℝ) * ((k : ℝ) + 1) / 4) • corr c J y x with hV
  set κ := ((k : ℝ) + 1) ^ 2 / (2 * stepScale L σ R k) with hκ
  set C := (96 * stepScale L σ R k * (LJ / μ) * R ^ 3 * (2 / ((k : ℝ) + 3)) +
      3328 * stepScale L σ R k * (LJ / μ) ^ 2 * R ^ 4 * (2 / ((k : ℝ) + 2)) ^ 2) +
    (stepScale L σ R (k + 1) - stepScale L σ R k) * (171 / 32 * R ^ 2) with hC
  set e0 := energy F c J x0 L σ R u k (x, z) with he0
  set f := fun ω => energy F c J x0 L σ R u (k + 1)
      (mixPoint k x (dualStep L σ R x0 k z (g y ω)), dualStep L σ R x0 k z (g y ω)) with hf
  set B := fun ω => e0 + ⟪g y ω - gradient F y, V⟫ + κ * ‖g y ω - gradient F y‖ ^ 2 + C with hB
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg (sq_nonneg _) (by
    have := stepScale_pos hL hσ hR k; positivity)
  have hnoise : Integrable (fun ω => g y ω - gradient F y) p :=
    (ho.integrable y).sub (integrable_const _)
  have hBi : Integrable B p :=
    (((integrable_const e0).add (hnoise.inner_const V)).add
      ((ho.variance_integrable y).const_mul κ)).add (integrable_const C)
  have hbound : ∀ ω, f ω ≤ B ω := fun ω =>
    energy_pathwise k hm hR hμ hLJ hreg hL hσ hF hlip hu hx hz
  have hFm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have hdm := measurable_dualStep ho.measurable L σ R x0 k y z
  have hstepm : Measurable (fun ω => (mixPoint k x (dualStep L σ R x0 k z (g y ω)),
      dualStep L σ R x0 k z (g y ω))) := by
    have hmix : Measurable (fun w : E => mixPoint k x w) := by unfold mixPoint; fun_prop
    exact (hmix.comp hdm).prodMk hdm
  have hfm : Measurable f :=
    (measurable_energy hm hR hμ hLJ hreg hu hFm L σ (k + 1)).comp hstepm
  set l := -(27 / 32 * stepScale L σ R (k + 1) * R ^ 2) with hl
  have hlow : ∀ ω, l ≤ f ω := by
    intro ω
    have hz'B : dualStep L σ R x0 k z (g y ω) ∈ closedBall x0 (2 * R) :=
      ballProj_mem x0 _ (by positivity)
    exact energy_lower hm hR hμ hLJ hreg hu hmin hL hσ (k + 1) (mixPoint_mem k hx hz'B) hz'B
  have hfi : Integrable f p := by
    have hb : ∀ ω, ‖f ω‖ ≤ |B ω| + |l| := by
      intro ω
      have h1 := hbound ω
      have h2 := hlow ω
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le l, abs_nonneg (B ω)]
      · linarith [le_abs_self (B ω), abs_nonneg l]
    exact Integrable.mono' (hBi.abs.add (integrable_const |l|)) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  refine ⟨hfi, (integral_mono hfi hBi hbound).trans ?_⟩
  have hzero : (∫ ω, ⟪g y ω - gradient F y, V⟫ ∂p) = 0 := by
    simp_rw [real_inner_comm V]
    rw [integral_inner (𝕜 := ℝ) hnoise V, integral_sub (ho.integrable y) (integrable_const _),
      ho.unbiased]
    simp
  have hvar := ho.variance y
  have i0 : Integrable (fun ω => ⟪g y ω - gradient F y, V⟫) p := hnoise.inner_const V
  have i1 : Integrable (fun ω => e0 + ⟪g y ω - gradient F y, V⟫) p := (integrable_const e0).add i0
  have i3 : Integrable (fun ω => κ * ‖g y ω - gradient F y‖ ^ 2) p :=
    (ho.variance_integrable y).const_mul κ
  have i2 : Integrable (fun ω => e0 + ⟪g y ω - gradient F y, V⟫ +
      κ * ‖g y ω - gradient F y‖ ^ 2) p := i1.add i3
  change (∫ ω, e0 + ⟪g y ω - gradient F y, V⟫ + κ * ‖g y ω - gradient F y‖ ^ 2 + C ∂p) ≤ _
  rw [integral_add i2 (integrable_const C), integral_add i1 i3,
    integral_add (integrable_const e0) i0, hzero, integral_const_mul]
  try simp only [integral_const, probReal_univ, one_smul, add_zero]
  have hk := mul_le_mul_of_nonneg_left hvar hκ0
  unfold stepCost
  linarith [hκ, hC]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma measurable_safeguardedRun {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L σ R : ℝ) (x0 : E) (K k : ℕ) :
    Measurable (fun v : (E × E) × (Fin K → Ω) =>
      safeguardedRun g L σ R x0 K k v.1.1 v.1.2 v.2) := by
  induction K generalizing k with
  | zero => exact measurable_fst
  | succ K ih =>
    have hy : Measurable (fun v : (E × E) × (Fin (K + 1) → Ω) => mixPoint k v.1.1 v.1.2) := by
      unfold mixPoint
      fun_prop
    have hr : Measurable (fun v : (E × E) × (Fin (K + 1) → Ω) =>
        g (mixPoint k v.1.1 v.1.2) (v.2 0)) :=
      hg.comp (hy.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have hz : Measurable (fun v : (E × E) × (Fin (K + 1) → Ω) =>
        dualStep L σ R x0 k v.1.2 (g (mixPoint k v.1.1 v.1.2) (v.2 0))) := by
      unfold dualStep
      exact (ballProj_measurable x0 (2 * R)).comp (measurable_fst.snd.sub (hr.const_smul _))
    have hx : Measurable (fun v : (E × E) × (Fin (K + 1) → Ω) =>
        mixPoint k v.1.1 (dualStep L σ R x0 k v.1.2 (g (mixPoint k v.1.1 v.1.2) (v.2 0)))) := by
      unfold mixPoint
      exact (measurable_fst.fst.const_smul _).add (hz.const_smul _)
    exact (ih (k + 1)).comp ((hx.prodMk hz).prodMk
      (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)))

lemma energy_bound {u : E} {L σ : ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hreg : 32 * LJ * R ≤ μ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hF : ∀ x, HasGradientAt F (gradient F x) x)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient E Ω p F g σ)
    (hu : u ∈ closedBall x0 R) (hmin : IsMinOn F univ u) (K k : ℕ) (x z : E)
    (hx : x ∈ closedBall x0 (2 * R)) (hz : z ∈ closedBall x0 (2 * R)) :
    Integrable (fun ξ => energy F c J x0 L σ R u (k + K)
      (safeguardedRun g L σ R x0 K k x z ξ)) (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, energy F c J x0 L σ R u (k + K) (safeguardedRun g L σ R x0 K k x z ξ)
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      energy F c J x0 L σ R u k (x, z) +
        ∑ j ∈ Finset.range K, stepCost L σ R (LJ / μ) (k + j) := by
  have hFm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  induction K generalizing k x z with
  | zero => simp [safeguardedRun]
  | succ K ih =>
    let q := Measure.pi (fun _ : Fin K => p)
    let y := mixPoint k x z
    let zs := fun ω => dualStep L σ R x0 k z (g y ω)
    let step := fun ω => (mixPoint k x (zs ω), zs ω)
    let C := ∑ j ∈ Finset.range K, stepCost L σ R (LJ / μ) (k + 1 + j)
    let B := fun ω => energy F c J x0 L σ R u (k + 1) (step ω) + C
    let G := fun v : Ω × (Fin K → Ω) =>
      energy F c J x0 L σ R u (k + (K + 1))
        (safeguardedRun g L σ R x0 (K + 1) k x z (Fin.cons v.1 v.2))
    have hmp : Measurable (fun ξ : Fin (K + 1) → Ω =>
        energy F c J x0 L σ R u (k + (K + 1)) (safeguardedRun g L σ R x0 (K + 1) k x z ξ)) :=
      (measurable_energy hm hR hμ hLJ hreg hu hFm L σ _).comp
        ((measurable_safeguardedRun ho.measurable L σ R x0 (K + 1) k).comp
          (measurable_const.prodMk measurable_id :
            Measurable (fun ξ : Fin (K + 1) → Ω => ((x, z), ξ))))
    have hcons := StochasticGradient.cons_measurePreserving p K
    have hGm : Measurable G := hmp.comp hcons.measurable
    have hzsB : ∀ ω, zs ω ∈ closedBall x0 (2 * R) := fun ω => ballProj_mem x0 _ (by positivity)
    have hxsB : ∀ ω, mixPoint k x (zs ω) ∈ closedBall x0 (2 * R) :=
      fun ω => mixPoint_mem k hx (hzsB ω)
    have hGeq (ω : Ω) : (fun ξ => G (ω, ξ)) =
        fun ξ => energy F c J x0 L σ R u (k + 1 + K)
          (safeguardedRun g L σ R x0 K (k + 1) (step ω).1 (step ω).2 ξ) := by
      funext ξ
      simp only [G, safeguardedRun, Fin.cons_zero, Fin.cons_succ, step, zs, y]
      congr 1
      omega
    have hstep := energy_step k hm hR hμ hLJ hreg hL hσ hF hlip ho hu hmin hx hz
    have hBint : Integrable B p := hstep.1.add (integrable_const C)
    have hsection : ∀ ω, Integrable (fun ξ => G (ω, ξ)) q := by
      intro ω
      rw [hGeq]
      exact (ih (k + 1) (step ω).1 (step ω).2 (hxsB ω) (hzsB ω)).1
    have hbound : ∀ ω, (∫ ξ, G (ω, ξ) ∂q) ≤ B ω := by
      intro ω
      rw [hGeq]
      have h := (ih (k + 1) (step ω).1 (step ω).2 (hxsB ω) (hzsB ω)).2
      simpa only [B, C] using h
    set l := -(27 / 32 * stepScale L σ R (k + (K + 1)) * R ^ 2) with hl
    have hlow : ∀ v, l ≤ G v := by
      intro v
      have hmem := safeguardedRun_mem (g := g) (L := L) (σ := σ) (x0 := x0) hR.le (K + 1) k hx hz
        (Fin.cons v.1 v.2)
      exact energy_lower hm hR hμ hLJ hreg hu hmin hL hσ _ hmem.1 hmem.2
    have habs : ∀ v, ‖G v‖ ≤ G v + 2 * |l| := by
      intro v
      have h := hlow v
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le l, le_abs_self l]
      · linarith [abs_nonneg l]
    have hint : Integrable (fun ω => ∫ ξ, ‖G (ω, ξ)‖ ∂q) p := by
      apply (hBint.add (integrable_const (2 * |l|))).mono'
        hGm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ξ => norm_nonneg _))]
      calc (∫ ξ, ‖G (ω, ξ)‖ ∂q) ≤ ∫ ξ, G (ω, ξ) + 2 * |l| ∂q :=
            integral_mono ((hsection ω).norm) ((hsection ω).add (integrable_const _))
              (fun ξ => habs (ω, ξ))
        _ = (∫ ξ, G (ω, ξ) ∂q) + 2 * |l| := by
            rw [integral_add (hsection ω) (integrable_const _)]
            simp
        _ ≤ B ω + 2 * |l| := by linarith [hbound ω]
    have hGi : Integrable G (p.prod q) := (integrable_prod_iff hGm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have hi : Integrable (fun ξ =>
        energy F c J x0 L σ R u (k + (K + 1)) (safeguardedRun g L σ R x0 (K + 1) k x z ξ))
        (Measure.pi fun _ : Fin (K + 1) => p) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp hGi
    refine ⟨hi, ?_⟩
    calc
      _ = ∫ v, G v ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
      _ = ∫ ω, ∫ ξ, G (ω, ξ) ∂q ∂p := integral_prod G hGi
      _ ≤ ∫ ω, B ω ∂p := integral_mono hGi.integral_prod_left hBint hbound
      _ = (∫ ω, energy F c J x0 L σ R u (k + 1) (step ω) ∂p) + C := by
        rw [integral_add hstep.1 (integrable_const C)]
        simp only [integral_const, probReal_univ, one_smul]
        rfl
      _ ≤ energy F c J x0 L σ R u k (x, z) + stepCost L σ R (LJ / μ) k + C :=
        add_le_add hstep.2 (le_refl C)
      _ = _ := by
        rw [Finset.sum_range_succ', add_zero]
        simp only [C]
        have e : ∀ j, k + 1 + j = k + (j + 1) := fun j => by omega
        simp only [e]
        ring

end stochastic

end OracleTemplate.LocalHiddenConvex
