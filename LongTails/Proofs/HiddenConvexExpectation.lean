import LongTails.Proofs.HiddenConvexStep
import LongTails.Proofs.SgdConvex
import LongTails.Setups.StochasticSmoothAndConvex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open Set Metric InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.LocalHiddenConvex

section fields

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
noncomputable def qField (c : E → E) (J : E → E →L[ℝ] E) (x0 : E) (R : ℝ) (u : E) : E → E :=
  (closedBall x0 (2 * R)).piecewise (fun v => corr c J v u) 0

noncomputable def energy (F : E → ℝ) (c : E → E) (J : E → E →L[ℝ] E) (x0 : E) (L σ R : ℝ)
    (u : E) (k : ℕ) (s : E × E) : ℝ :=
  (k : ℝ) * ((k : ℝ) + 1) / 4 * (F s.1 - F u) + stepScale L σ R k / 2 * ‖s.2 - u‖ ^ 2 -
    stepScale L σ R k * ⟪s.2 - u, qField c J x0 R u (mixPoint k s.1 s.2)⟫

noncomputable def stepCost (L σ R M : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2 / (2 * stepScale L σ R k) * σ ^ 2 +
    (96 * stepScale L σ R k * M * R ^ 3 * (2 / ((k : ℝ) + 3)) +
      3328 * stepScale L σ R k * M ^ 2 * R ^ 4 * (2 / ((k : ℝ) + 2)) ^ 2) +
    (stepScale L σ R (k + 1) - stepScale L σ R k) * (171 / 32 * R ^ 2)

lemma qField_eq {c : E → E} {J : E → E →L[ℝ] E} {x0 u y : E} {R : ℝ}
    (hy : y ∈ closedBall x0 (2 * R)) : qField c J x0 R u y = corr c J y u := by
  classical
  unfold qField
  exact Set.piecewise_eq_of_mem _ _ _ hy

lemma stepScale_ge {L σ R : ℝ} (hσ : 0 ≤ σ) (hR : 0 < R) (k : ℕ) :
    4 * L ≤ stepScale L σ R k := by
  unfold stepScale
  have : 0 ≤ σ * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) / R := by positivity
  linarith

lemma stepScale_pos {L σ R : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) (hR : 0 < R) (k : ℕ) :
    0 < stepScale L σ R k := by
  have := stepScale_ge (L := L) hσ hR k
  linarith

lemma stepScale_mono {L σ R : ℝ} (hσ : 0 ≤ σ) (hR : 0 < R) {k l : ℕ} (h : k ≤ l) :
    stepScale L σ R k ≤ stepScale L σ R l := by
  unfold stepScale
  have hkl : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
  have hs : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((l : ℝ) + 1) := Real.sqrt_le_sqrt hkl
  have h1 : σ * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) ≤
      σ * ((l : ℝ) + 1) * Real.sqrt ((l : ℝ) + 1) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hkl hσ) hs (Real.sqrt_nonneg _) (by positivity)
  have := div_le_div_of_nonneg_right h1 hR.le
  linarith

lemma ballProj_measurable (x0 : E) (r : ℝ) [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] :
    Measurable (ballProj x0 r) := by
  classical
  unfold ballProj
  refine Measurable.ite ?_ measurable_id ?_
  · exact measurableSet_le ((measurable_id.sub_const x0).norm) measurable_const
  · exact measurable_const.add
      ((measurable_const.div ((measurable_id.sub_const x0).norm)).smul (measurable_id.sub_const x0))

end fields

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

section model

variable {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {U : Set E} {x0 : E} {R μ LJ : ℝ}

omit [CompleteSpace E] in
lemma LocalModel.corr_small (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ)
    (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u v : E} (hu : u ∈ closedBall x0 R)
    (hv : v ∈ closedBall x0 (2 * R)) : ‖corr c J v u‖ ≤ 9 * R / 32 := by
  have huB : u ∈ closedBall x0 (2 * R) := closedBall_subset_closedBall (by linarith) hu
  have h := hm.corr_le hμ hLJ hv huB
  have h3 := norm_sub_le_three hv hu
  have h9 : ‖u - v‖ ^ 2 ≤ 9 * R ^ 2 := by
    calc ‖u - v‖ ^ 2 ≤ (3 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 9 * R ^ 2 := by ring
  have hMR : LJ / μ * R ≤ 1 / 32 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hμ (by norm_num)]
    linarith
  calc ‖corr c J v u‖ ≤ LJ / μ * ‖u - v‖ ^ 2 := h
    _ ≤ LJ / μ * (9 * R ^ 2) := mul_le_mul_of_nonneg_left h9 (div_nonneg hLJ hμ.le)
    _ = 9 * R * (LJ / μ * R) := by ring
    _ ≤ 9 * R * (1 / 32) := mul_le_mul_of_nonneg_left hMR (by positivity)
    _ = 9 * R / 32 := by ring

omit [CompleteSpace E] in
lemma LocalModel.corr_continuousOn (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R)
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u : E} (hu : u ∈ closedBall x0 R) :
    ContinuousOn (fun v => corr c J v u) (closedBall x0 (2 * R)) := by
  set C := LJ / μ * (8 * R) + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hbound : ∀ v ∈ closedBall x0 (2 * R), ∀ v' ∈ closedBall x0 (2 * R),
      ‖corr c J v u - corr c J v' u‖ ≤ C * ‖v - v'‖ := by
    intro v hv v' hv'
    have h := hm.corr_lip hμ hLJ (w := u) hv hv'
    have h4 := norm_sub_le_four hv hv'
    have h3 := norm_sub_le_three hv hu
    have hq := hm.corr_small hR hμ hLJ hreg hu hv'
    have hb : ‖v - v'‖ + ‖u - v‖ + ‖corr c J v' u‖ ≤ 8 * R := by linarith
    calc ‖corr c J v u - corr c J v' u‖ ≤
          LJ / μ * ‖v - v'‖ * (‖v - v'‖ + ‖u - v‖ + ‖corr c J v' u‖) := h
      _ ≤ LJ / μ * ‖v - v'‖ * (8 * R) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (div_nonneg hLJ hμ.le) (norm_nonneg _))
      _ = LJ / μ * (8 * R) * ‖v - v'‖ := by ring
      _ ≤ C * ‖v - v'‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [hC]; linarith
  intro v hv
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / C, by positivity, fun {v'} hv' hd => ?_⟩
  rw [dist_eq_norm] at hd ⊢
  calc ‖corr c J v' u - corr c J v u‖ ≤ C * ‖v' - v‖ := hbound v' hv' v hv
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hd hCpos
    _ = ε := by field_simp

omit [CompleteSpace E] in
lemma LocalModel.qField_measurable [MeasurableSpace E] [BorelSpace E]
    (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R)
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u : E} (hu : u ∈ closedBall x0 R) :
    Measurable (qField c J x0 R u) := by
  classical
  unfold qField
  exact (hm.corr_continuousOn hR hμ hLJ hreg hu).measurable_piecewise continuousOn_const
    measurableSet_closedBall

omit [CompleteSpace E] in
lemma measurable_energy [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R)
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u : E} (hu : u ∈ closedBall x0 R)
    (hFm : Measurable F) (L σ : ℝ) (k : ℕ) :
    Measurable (energy F c J x0 L σ R u k) := by
  have hq := hm.qField_measurable hR hμ hLJ hreg hu
  have hmix : Measurable (fun s : E × E => mixPoint k s.1 s.2) := by
    unfold mixPoint
    fun_prop
  have hin : Measurable (fun s : E × E => ⟪s.2 - u, qField c J x0 R u (mixPoint k s.1 s.2)⟫) :=
    Measurable.inner (by fun_prop) (hq.comp hmix)
  have hn : Measurable (fun s : E × E => ‖s.2 - u‖ ^ 2) := by fun_prop
  have hf : Measurable (fun s : E × E => F s.1 - F u) := (hFm.comp measurable_fst).sub_const _
  unfold energy
  exact ((hf.const_mul _).add (hn.const_mul _)).sub (hin.const_mul _)

omit [CompleteSpace E] in
lemma energy_lower (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ)
    (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u : E} (hu : u ∈ closedBall x0 R)
    (hmin : IsMinOn F univ u) {L σ : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) (k : ℕ) {x z : E}
    (hx : x ∈ closedBall x0 (2 * R)) (hz : z ∈ closedBall x0 (2 * R)) :
    -(27 / 32 * stepScale L σ R k * R ^ 2) ≤ energy F c J x0 L σ R u k (x, z) := by
  have hyB := mixPoint_mem k hx hz
  have hD := stepScale_pos hL hσ hR k
  unfold energy
  simp only
  rw [qField_eq hyB]
  have hq := hm.corr_small hR hμ hLJ hreg hu hyB
  have h3 : ‖z - u‖ ≤ 3 * R := by rw [norm_sub_rev]; exact norm_sub_le_three hz hu
  have hin : ⟪z - u, corr c J (mixPoint k x z) u⟫ ≤ 27 / 32 * R ^ 2 := by
    calc ⟪z - u, corr c J (mixPoint k x z) u⟫ ≤ ‖z - u‖ * ‖corr c J (mixPoint k x z) u‖ :=
          real_inner_le_norm _ _
      _ ≤ (3 * R) * (9 * R / 32) := mul_le_mul h3 hq (norm_nonneg _) (by positivity)
      _ = 27 / 32 * R ^ 2 := by ring
  have hF0 : 0 ≤ F x - F u := sub_nonneg.mpr (hmin (mem_univ x))
  have hk : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) / 4 := by positivity
  have h1 := mul_nonneg hk hF0
  have h2 : 0 ≤ stepScale L σ R k / 2 * ‖z - u‖ ^ 2 := by positivity
  have h4 := mul_le_mul_of_nonneg_left hin hD.le
  nlinarith

end model

omit [FiniteDimensional ℝ E] in
omit [CompleteSpace E] in
lemma safeguardedRun_mem {Ω : Type*} {g : E → Ω → E} {L σ R : ℝ} {x0 : E} (hR : 0 ≤ R)
    (K k : ℕ) {x z : E} (hx : x ∈ closedBall x0 (2 * R)) (hz : z ∈ closedBall x0 (2 * R))
    (ξ : Fin K → Ω) :
    (safeguardedRun g L σ R x0 K k x z ξ).1 ∈ closedBall x0 (2 * R) ∧
      (safeguardedRun g L σ R x0 K k x z ξ).2 ∈ closedBall x0 (2 * R) := by
  induction K generalizing k x z with
  | zero => exact ⟨hx, hz⟩
  | succ K ih =>
    have hz' := ballProj_mem x0 (z - (((k : ℝ) + 1) / (2 * stepScale L σ R k)) •
      g (mixPoint k x z) (ξ 0)) (show 0 ≤ 2 * R by positivity)
    exact ih (k + 1) (mixPoint_mem k hx hz') hz' _

end OracleTemplate.LocalHiddenConvex
