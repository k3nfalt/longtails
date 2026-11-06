import LongTails.Algorithms.SurjectiveProxLinear
import LongTails.Proofs.ProxLinearDualSensitivity
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearModel

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear

lemma compact_dualBox (p : Params) : IsCompact (dualBox p) := by
  let h := PiLp.homeomorph 2 (fun _ : Fin p.m => ℝ)
  have hc : IsCompact {v : Fin p.m → ℝ | ∀ i, v i ∈ Set.Icc 0 (rho p)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  exact h.isCompact_preimage.mpr hc

lemma zero_mem_dualBox (p : Params) (hρ : 0 ≤ rho p) :
    (0 : Constraint p) ∈ dualBox p := by
  intro i
  exact ⟨le_rfl, hρ⟩

lemma continuous_transposeAction (p : Params) (J : Jacobian p) :
    Continuous (transposeAction p J) := by
  unfold transposeAction
  fun_prop

lemma continuous_dualObjective (p : Params) (v : Primitive p) :
    Continuous (dualObjective p v) := by
  unfold dualObjective
  have h := continuous_transposeAction p (OracleTemplate.clip p.H v.2.2)
  fun_prop

lemma exists_dual_minimum (p : Params) (v : Primitive p) (hρ : 0 ≤ rho p) :
    ∃ ℓ ∈ dualBox p, ∀ z ∈ dualBox p, dualObjective p v ℓ ≤ dualObjective p v z := by
  exact (compact_dualBox p).exists_isMinOn ⟨0, zero_mem_dualBox p hρ⟩
    (continuous_dualObjective p v).continuousOn

lemma dualPoint_spec (p : Params) (v : Primitive p) (hρ : 0 ≤ rho p) :
    dualPoint p v ∈ dualBox p ∧
      ∀ z ∈ dualBox p, dualObjective p v (dualPoint p v) ≤ dualObjective p v z := by
  have h := exists_dual_minimum p v hρ
  unfold dualPoint
  rw [dite_eq_left h]
  exact Classical.choose_spec h

lemma convex_dualBox (p : Params) : Convex ℝ (dualBox p) := by
  intro x hx y hy a b ha hb hab i
  change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ rho p
  constructor
  · exact add_nonneg (mul_nonneg ha (hx i).1) (mul_nonneg hb (hy i).1)
  · have hx' := mul_le_mul_of_nonneg_left (hx i).2 ha
    have hy' := mul_le_mul_of_nonneg_left (hy i).2 hb
    calc
      a * x i + b * y i ≤ a * rho p + b * rho p := add_le_add hx' hy'
      _ = (a + b) * rho p := by ring
      _ = rho p := by rw [hab, one_mul]

def transposeLinear (p : Params) (J : Jacobian p) : Constraint p →ₗ[ℝ] p.E where
  toFun := transposeAction p J
  map_add' a b := by
    simp [transposeAction, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp [transposeAction, Finset.smul_sum, smul_smul]

noncomputable def transposeContinuous (p : Params) (J : Jacobian p) :
    Constraint p →L[ℝ] p.E := (transposeLinear p J).toContinuousLinearMap

lemma transposeContinuous_apply (p : Params) (J : Jacobian p) (ℓ : Constraint p) :
    transposeContinuous p J ℓ = transposeAction p J ℓ := rfl

open LongTails.Proofs.ProxLinearDualSensitivity

lemma dual_minimum_vi (p : Params) (v : Primitive p) {u : Constraint p}
    (hu : u ∈ dualBox p)
    (hmin : ∀ z ∈ dualBox p, dualObjective p v u ≤ dualObjective p v z)
    {z : Constraint p} (hz : z ∈ dualBox p) :
    0 ≤ ⟪quadraticGradient (transposeContinuous p (OracleTemplate.clip p.H v.2.2))
      (OracleTemplate.clip p.H v.1) v.2.1 (eta p) (ridge p) u, z - u⟫ := by
  rw [quadraticGradient_direction]
  apply quadratic_min_directional
  intro t ht ht1
  have hseg := (convex_dualBox p).add_smul_sub_mem hu hz ⟨ht.le, ht1⟩
  simpa only [dualObjective, transposeContinuous_apply] using hmin _ hseg

lemma dualPoint_vi (p : Params) (v : Primitive p) (hρ : 0 ≤ rho p)
    {z : Constraint p} (hz : z ∈ dualBox p) :
    0 ≤ ⟪quadraticGradient (transposeContinuous p (OracleTemplate.clip p.H v.2.2))
      (OracleTemplate.clip p.H v.1) v.2.1 (eta p) (ridge p) (dualPoint p v),
      z - dualPoint p v⟫ := by
  exact dual_minimum_vi p v (dualPoint_spec p v hρ).1 (dualPoint_spec p v hρ).2 hz

lemma norm_transposeAction_le (p : Params) (J : Jacobian p) (ℓ : Constraint p) :
    ‖transposeAction p J ℓ‖ ≤ ‖ℓ‖ * ‖J‖ := by
  have hn : ‖transposeAction p J ℓ‖ ≤ ∑ i, ‖ℓ i‖ * ‖J i‖ := by
    simpa only [transposeAction, norm_smul] using
      (norm_sum_le (s := Finset.univ) (f := fun i => ℓ i • J i))
  have hs : ‖transposeAction p J ℓ‖ ^ 2 ≤ (∑ i, ‖ℓ i‖ * ‖J i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => by positivity))).2 hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖ℓ i‖) (fun i => ‖J i‖)
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin p.m => ℝ) ℓ,
    ← PiLp.norm_sq_eq_of_L2 (fun _ : Fin p.m => p.E) J] at hc
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
  simpa only [mul_pow] using hs.trans hc

lemma dual_minimum_unique (p : Params) (v : Primitive p)
    (hη : 0 ≤ eta p) (hτ : 0 < ridge p) {u z : Constraint p}
    (hu : u ∈ dualBox p) (hz : z ∈ dualBox p)
    (hminu : ∀ w ∈ dualBox p, dualObjective p v u ≤ dualObjective p v w)
    (hminz : ∀ w ∈ dualBox p, dualObjective p v z ≤ dualObjective p v w) : u = z := by
  let T := transposeContinuous p (OracleTemplate.clip p.H v.2.2)
  let G := quadraticGradient T (OracleTemplate.clip p.H v.1) v.2.1 (eta p) (ridge p)
  have hstrong : ridge p * ‖u - z‖ ^ 2 ≤ ⟪G u - G z, u - z⟫ := by
    dsimp [G]
    rw [quadraticGradient_inner]
    nlinarith [mul_nonneg hη (sq_nonneg ‖T (u - z)‖)]
  have hiu : 0 ≤ ⟪G u, z - u⟫ := dual_minimum_vi p v hu hminu hz
  have hiz : 0 ≤ ⟪G z, u - z⟫ := dual_minimum_vi p v hz hminz hu
  have hd := variational_solution_distance (A := G) (B := G) hstrong hiu hiz
  simp only [sub_self, norm_zero] at hd
  have hn : ‖u - z‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖u - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    exact (not_lt_of_ge hd) (mul_pos hτ hpos)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma continuous_dualObjective_joint (p : Params) (hH : 0 ≤ p.H) :
    Continuous (fun z : Primitive p × Constraint p => dualObjective p z.1 z.2) := by
  have hg := continuous_clipping (E := p.E) hH
  have hJ := continuous_clipping (E := Jacobian p) hH
  unfold dualObjective transposeAction
  fun_prop

set_option maxHeartbeats 800000 in
lemma continuous_dualPoint (p : Params) (hH : 0 ≤ p.H) (hρ : 0 ≤ rho p)
    (hη : 0 ≤ eta p) (hτ : 0 < ridge p) : Continuous (dualPoint p) := by
  let : CompactSpace (dualBox p) := isCompact_iff_compactSpace.mp (compact_dualBox p)
  let f : Primitive p → dualBox p := fun v => ⟨dualPoint p v, (dualPoint_spec p v hρ).1⟩
  have hq : Continuous (fun z : Primitive p × dualBox p => dualObjective p z.1 z.2.val) :=
    (continuous_dualObjective_joint p hH).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hmin : ∀ (v : Primitive p) (u : dualBox p),
      dualObjective p v (f v).val ≤ dualObjective p v u.val := by
    intro v u
    exact (dualPoint_spec p v hρ).2 u.val u.property
  have hunique : ∀ v (u : dualBox p),
      (∀ z : dualBox p, dualObjective p v u.val ≤ dualObjective p v z.val) → f v = u := by
    intro v u hminu
    apply Subtype.ext
    apply dual_minimum_unique p v hη hτ (dualPoint_spec p v hρ).1 u.property
      (dualPoint_spec p v hρ).2
    intro z hz
    exact hminu ⟨z, hz⟩
  have hf := continuous_unique_minimizer (fun v (u : dualBox p) => dualObjective p v u.val)
    f hq hmin hunique
  exact continuous_subtype_val.comp hf

lemma valid_tuning_positive (p : Params) (hp : spec.valid p) :
    0 < rho p ∧ 0 < gamma p ∧ 0 < eta p ∧ 0 < ridge p := by
  rcases hp with ⟨hm, hH, _, _, hε, _⟩
  have hm' : (0 : ℝ) < p.m := Nat.cast_pos.mpr hm
  have hH' : 0 < p.H := lt_of_lt_of_le zero_lt_one hH
  have hρ : 0 < rho p := by unfold rho; positivity
  have hγ : 0 < gamma p := by unfold gamma; positivity
  have hη : 0 < eta p := by unfold eta; positivity
  have hτ : 0 < ridge p := by unfold ridge; positivity
  exact ⟨hρ, hγ, hη, hτ⟩

lemma measurable_dualPoint (p : Params) (hp : spec.valid p) : Measurable (dualPoint p) := by
  have h := valid_tuning_positive p hp
  exact (continuous_dualPoint p (le_trans (by norm_num) hp.2.1) h.1.le h.2.2.1.le
    h.2.2.2).measurable

lemma continuous_modelStep (p : Params) (hp : spec.valid p) : Continuous (modelStep p) := by
  have h := valid_tuning_positive p hp
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hd := continuous_dualPoint p hH h.1.le h.2.2.1.le h.2.2.2
  have hg := continuous_clipping (E := p.E) hH
  have hJ := continuous_clipping (E := Jacobian p) hH
  unfold modelStep transposeAction
  fun_prop

lemma norm_transposeContinuous_le (p : Params) (J : Jacobian p) :
    ‖transposeContinuous p J‖ ≤ ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro ℓ
  simpa only [transposeContinuous_apply, mul_comm] using norm_transposeAction_le p J ℓ

lemma transposeContinuous_sub (p : Params) (J K : Jacobian p) :
    transposeContinuous p (J - K) = transposeContinuous p J - transposeContinuous p K := by
  ext ℓ
  simp [transposeContinuous_apply, transposeAction, smul_sub, Finset.sum_sub_distrib]

lemma norm_transposeContinuous_sub_le (p : Params) (J K : Jacobian p) :
    ‖transposeContinuous p J - transposeContinuous p K‖ ≤ ‖J - K‖ := by
  rw [← transposeContinuous_sub]
  exact norm_transposeContinuous_le p (J - K)

lemma norm_mem_dualBox_le (p : Params) (hm : 0 < p.m) (hρ : 0 ≤ rho p)
    {ℓ : Constraint p} (hℓ : ℓ ∈ dualBox p) : ‖ℓ‖ ≤ rho p * p.m := by
  have hm' : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hsq : ‖ℓ‖ ^ 2 ≤ (p.m : ℝ) * rho p ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, ℓ i ^ 2 ≤ ∑ _i : Fin p.m, rho p ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_sq₀ (hℓ i).1 hρ).2 (hℓ i).2
      _ = (p.m : ℝ) * rho p ^ 2 := by simp
  have hm2 : 0 ≤ (p.m : ℝ) ^ 2 - p.m := by nlinarith
  have hprod := mul_nonneg hm2 (sq_nonneg (rho p))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ (Nat.cast_nonneg _))).1
  nlinarith

lemma norm_modelStep_le (p : Params) (hp : spec.valid p) (v : Primitive p) :
    ‖modelStep p v‖ ≤ eta p * (p.H + (rho p * p.m) * p.H) := by
  have hpos := valid_tuning_positive p hp
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hΛ : 0 ≤ rho p * p.m := mul_nonneg hpos.1.le (Nat.cast_nonneg _)
  have hℓ := norm_mem_dualBox_le p hp.1 hpos.1.le (dualPoint_spec p v hpos.1.le).1
  have hJ := OracleTemplate.norm_clip_le hH v.2.2
  have hg := OracleTemplate.norm_clip_le hH v.1
  rw [modelStep, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hpos.2.2.1.le]
  apply mul_le_mul_of_nonneg_left _ hpos.2.2.1.le
  exact (norm_add_le _ _).trans (add_le_add hg
    ((norm_transposeAction_le p _ _).trans (mul_le_mul hℓ hJ (norm_nonneg _) hΛ)))

end LongTails.Proofs.SurjectiveProxLinearModel
