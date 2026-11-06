import LongTails.Proofs.MomentumSeparationInstance
import LongTails.Proofs.StochasticEqualityTuning
import LongTails.Proofs.StochasticEqualityMoments

namespace LongTails.Proofs.StochasticEqualityModel

open MeasureTheory OracleTemplate
open LongTails.Proofs.StochasticEqualityMoments
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.StochasticEqualityDirection
open LongTails.Proofs.StochasticEqualityTuning
open LongTails.Proofs.StochasticEqualityDescent

noncomputable def truth {p : Public} (I : Instance p) (x : Point p.d) : Reply p :=
  (gradient I.f x, I.c x, jacobian I x)

lemma truth_operator {p : Public} (I : Instance p) (x : Point p.d) :
    operatorEquiv p.d p.m (truth I x).2.2 = (fderiv ℝ I.c x).adjoint := by
  exact (operatorEquiv p.d p.m).apply_symm_apply _

set_option maxHeartbeats 1000000 in
lemma admissible_truth_measurable (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) : Measurable (truth I) := by
  obtain ⟨_, hc, _, _, hgL, _, hJL, _, _⟩ := hI
  rcases hp with ⟨_, _, _, _, hLf, _, hLJ, _, _, _, _, _, _⟩
  have hg : LipschitzWith ⟨p.Lf, hLf⟩ (gradient I.f) :=
    lipschitzWith_iff_norm_sub_le.mpr (fun x y => hgL y x)
  have hJ : LipschitzWith ⟨p.LJ, hLJ⟩ (jacobian I) :=
    lipschitzWith_iff_norm_sub_le.mpr (fun x y => hJL y x)
  exact hg.continuous.measurable.prodMk (hc.continuous.measurable.prodMk hJ.continuous.measurable)

lemma admissible_truth_derivative (p : Params)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (x : Point p.d) :
    HasFDerivAt (fun y => (truth I y).2.1)
      (operatorEquiv p.d p.m (truth I x).2.2).adjoint x := by
  rw [truth_operator, ContinuousLinearMap.adjoint_adjoint]
  exact hI.2.1 x |>.hasFDerivAt

lemma admissible_truth_regular (p : Params)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (x : Point p.d) :
    regular p.ν (operatorEquiv p.d p.m (truth I x).2.2) := by
  rw [truth_operator]
  exact hI.2.2.2.2.2.2.2.1 x

set_option maxHeartbeats 1000000 in
lemma admissible_merit_lower_of_lower (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (fLower : ℝ) (hlow : ∀ x, fLower ≤ I.f x) :
    ∀ x, 0 ≤ merit I.f I.c (fun y => (fderiv ℝ I.c y).adjoint)
      (gradient I.f) (10 ^ 10 * (scale p.toPublic) ^ 24) x - fLower := by
  obtain ⟨hf, _, _, _, hgL, _, _, hreg, _⟩ := hI
  obtain ⟨hS, hfS, _, _, _, _, hinv, _, _⟩ := scale_bounds p hp
  have hS1 : 1 ≤ scale p.toPublic := by linarith only [hS]
  rcases hp with ⟨_, _, _, hν, hLf, _, _, _, _, _, _, _, _⟩
  intro x
  have hL : 0 < 1 + p.Lf := by linarith only [hLf]
  have hβ : 0 < 10 ^ 10 * (scale p.toPublic) ^ 24 := by
    have hs : 0 < scale p.toPublic := by linarith only [hS]
    positivity
  have hpen := coercivity_penalty_bound hS1 hν
    (show 1 + p.Lf ≤ scale p.toPublic by linarith only [hfS])
    (show p.ν⁻¹ ≤ scale p.toPublic by simpa only [one_div] using hinv)
  have hLip : ∀ x y, ‖gradient I.f y - gradient I.f x‖ ≤
      (1 + p.Lf) * ‖y - x‖ := by
    intro x y
    exact (hgL x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hβL : 4 * (1 + p.Lf) ≤ (10 ^ 10 * (scale p.toPublic) ^ 24) * p.ν ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hν)).mp hpen
  have hh := field_coercive (c := I.c) (J := fun y => (fderiv ℝ I.c y).adjoint)
    hL hβ hν hf hLip hlow hβL x (hreg x)
  have hgap0 := sub_nonneg.mpr (hlow x)
  have hc : 0 ≤ (10 ^ 10 * (scale p.toPublic) ^ 24) * ‖I.c x‖ ^ 2 / 4 := by positivity
  apply sub_nonneg.mpr
  calc
    fLower ≤ fLower + (I.f x - fLower) / 2 :=
      le_add_of_nonneg_right (div_nonneg hgap0 (by norm_num))
    _ ≤ fLower + (I.f x - fLower) / 2 +
        (10 ^ 10 * (scale p.toPublic) ^ 24) * ‖I.c x‖ ^ 2 / 4 := le_add_of_nonneg_right hc
    _ ≤ _ := hh

lemma admissible_merit_lower (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) :
    ∃ fLower : ℝ, (∀ x, fLower ≤ I.f x) ∧ I.f p.x0 - fLower ≤ p.Δ ∧
      ∀ x, 0 ≤ merit I.f I.c (fun y => (fderiv ℝ I.c y).adjoint)
        (gradient I.f) (10 ^ 10 * (scale p.toPublic) ^ 24) x - fLower := by
  obtain ⟨fLower, hlow, hgap⟩ := hI.2.2.1
  exact ⟨fLower, hlow, hgap, admissible_merit_lower_of_lower p hp I O hI fLower hlow⟩

set_option maxHeartbeats 1000000 in
lemma admissible_oracle (p : Params) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O) :
    ∃ (g : Point p.d → p.Ω → Reply p.toPublic)
      (P : ProbabilityMeasure p.Ω) (Q : ProbabilityMeasure p.Ξ) (ξ : ℕ → p.Ξ → p.Ω),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (P : Measure _) (Q : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := Q.map (fun z n => ξ (n / 2) z)
            answer := fun _ (_, x) w => g x w } ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (P : Measure _)) ∧
      (∀ x, (∫ w, g x w ∂(P : Measure _)) = truth I x) ∧
      (∀ x, Integrable (fun w => ‖pack p.toPublic (g x w) - pack p.toPublic (truth I x)‖ ^ 2)
        (P : Measure _)) ∧
      (∀ x, (∫ w, ‖pack p.toPublic (g x w) - pack p.toPublic (truth I x)‖ ^ 2
        ∂(P : Measure _)) ≤ p.σ ^ 2) ∧
      (∀ x y, Integrable (fun w => ‖pack p.toPublic (g x w) - pack p.toPublic (g y w)‖ ^ 2)
        (P : Measure _)) ∧
      (∀ x y, (∫ w, ‖pack p.toPublic (g x w) - pack p.toPublic (g y w)‖ ^ 2
        ∂(P : Measure _)) ≤ p.Lnoise ^ 2 * ‖x - y‖ ^ 2) := by
  obtain ⟨g, c, J, P, Q, ξ, hiid, hO, hg, hc, hJ, hgi, hci, hJi,
    hgm, hcm, hJm, hni, hn, hdi, hd⟩ := hI.2.2.2.2.2.2.2.2
  have hspace (d : ℕ) : WithLp.measurableSpace 2 (Fin d → ℝ) = borel (Point d) :=
    @BorelSpace.measurable_eq (Point d) _ (WithLp.measurableSpace 2 (Fin d → ℝ))
      (PiLp.borelSpace (X := fun _ : Fin d => ℝ) 2)
  simp (config := { instances := true }) only [hspace] at hg hc hJ
  let G : Point p.d → p.Ω → Reply p.toPublic := fun x w => (g (x, w), c (x, w), J (x, w))
  have hnoise (x : Point p.d) (w : p.Ω) :
      ‖pack p.toPublic (G x w) - pack p.toPublic (truth I x)‖ ^ 2 =
      ‖g (x, w) - gradient I.f x‖ ^ 2 + ‖c (x, w) - I.c x‖ ^ 2 +
        ‖J (x, w) - jacobian I x‖ ^ 2 := by
    rw [← map_sub, pack_norm_sq]
    rfl
  have hdiff (x y : Point p.d) (w : p.Ω) :
      ‖pack p.toPublic (G x w) - pack p.toPublic (G y w)‖ ^ 2 =
      ‖g (x, w) - g (y, w)‖ ^ 2 + ‖c (x, w) - c (y, w)‖ ^ 2 +
        ‖J (x, w) - J (y, w)‖ ^ 2 := by
    rw [← map_sub, pack_norm_sq]
    rfl
  refine ⟨G, P, Q, ξ, hiid, hO, hg.prodMk (hc.prodMk hJ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hgi x).prodMk ((hci x).prodMk (hJi x))
  · intro x
    dsimp only [G, truth]
    rw [integral_pair (hgi x) ((hci x).prodMk (hJi x)), integral_pair (hci x) (hJi x),
      hgm, hcm, hJm]
  · intro x
    simpa only [hnoise] using hni x
  · intro x
    simpa only [hnoise] using hn x
  · intro x y
    simpa only [hdiff] using hdi y x
  · intro x y
    simpa only [hdiff] using hd y x

set_option maxHeartbeats 1000000 in
lemma admissible_sublevel_caps (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (fLower : ℝ) (hlow : ∀ y, fLower ≤ I.f y)
    (x : Point p.d)
    (hupper : merit I.f I.c (fun y => (fderiv ℝ I.c y).adjoint) (gradient I.f)
      (10 ^ 10 * (scale p.toPublic) ^ 24) x - fLower ≤ 2 * (10 ^ 6 * (scale p.toPublic) ^ 10) - 1) :
    ‖gradient I.f x‖ < (LongTails.Algorithms.StochasticEquality.tuning p.toPublic).gradientCap ∧
      ‖I.c x‖ < (LongTails.Algorithms.StochasticEquality.tuning p.toPublic).constraintCap := by
  let S := scale p.toPublic
  obtain ⟨hS, hfS, _, _, _, _, hinv, _, _⟩ := scale_bounds p hp
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hSpos : 0 < S := by linarith only [hS1]
  have hcaps := tuned_joint_caps (L := 1 + p.Lf) hS (by linarith only [hfS])
  rcases hp with ⟨_, _, _, hν, hLf, _, _, _, _, _, _, _, _⟩
  have hL : 0 < 1 + p.Lf := by linarith only [hLf]
  have hβ : 0 < 10 ^ 10 * S ^ 24 := by positivity
  have hW : 0 < 10 ^ 6 * S ^ 10 := by positivity
  have hLip : ∀ y z, ‖gradient I.f z - gradient I.f y‖ ≤ (1 + p.Lf) * ‖z - y‖ := by
    intro y z
    exact (hI.2.2.2.2.1 y z).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hpen := coercivity_penalty_bound hS1 hν
    (show 1 + p.Lf ≤ S by dsimp [S]; linarith only [hfS])
    (show p.ν⁻¹ ≤ S by simpa only [one_div] using hinv)
  have hβL : 4 * (1 + p.Lf) ≤ (10 ^ 10 * S ^ 24) * p.ν ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hν)).mp hpen
  have hh := field_coercive (c := I.c) (J := fun y => (fderiv ℝ I.c y).adjoint)
    hL hβ hν hI.1 hLip hlow hβL x (hI.2.2.2.2.2.2.2.1 x)
  have hcoercive : (I.f x - fLower) / 2 + (10 ^ 10 * S ^ 24) * ‖I.c x‖ ^ 2 / 4 ≤
      merit I.f I.c (fun y => (fderiv ℝ I.c y).adjoint) (gradient I.f) (10 ^ 10 * S ^ 24) x - fLower := by
    convert sub_le_sub_right hh fLower using 1
    ring
  have hg := HeavyTailedPL.gradient_sq_le hL hI.1 (fun y z => hLip z y) hlow x
  have hexit := StochasticEqualityStopped.joint_exit_bounds (sub_nonneg.mpr (hlow x)) hL.le hβ hW
    hcoercive hg hupper
  constructor
  · have hh := hexit.1.trans_le hcaps.1
    exact (sq_lt_sq₀ (norm_nonneg _) (show 0 ≤ 4000 * S ^ 6 by positivity)).mp hh
  · have hM : 16 * (10 ^ 6 * S ^ 10) / (10 ^ 10 * S ^ 24) ≤ (1 / (10 * S ^ 7)) ^ 2 := by
      apply (div_le_iff₀ hβ).mpr
      simpa only [mul_comm] using hcaps.2
    exact (sq_lt_sq₀ (norm_nonneg _) (show 0 ≤ 1 / (10 * S ^ 7) by positivity)).mp
      (hexit.2.trans_le hM)

lemma admissible_point_envelope (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (x : Point p.d) (lam : Point p.m)
    {D : ℝ} (hd : ‖x - p.x0‖ ≤ D) (hlam : ‖lam‖ ≤ 8000 * scale p.toPublic ^ 7) :
    let S := scale p.toPublic
    ‖gradient I.f x + (fderiv ℝ I.c x).adjoint lam‖ ≤ 2 * S + S * D + 8000 * S ^ 8 ∧
      ‖I.c x‖ ≤ S + S * D := by
  let S := scale p.toPublic
  have ⟨hS, hfS, hcS, hCS, _, _, _, hΔS, _⟩ := scale_bounds p hp
  have hS0 : 0 < S := by dsimp [S]; linarith only [hS]
  have hLf : 0 ≤ p.Lf := hp.2.2.2.2.1
  have hfS' : p.Lf ≤ S := by dsimp [S]; linarith only [hfS]
  have hcS' : p.Lc ≤ S := by dsimp [S]; linarith only [hcS]
  have hC0S : p.C0 ≤ S := by dsimp [S]; linarith only [hCS]
  have hJ (z : Point p.d) : ‖(fderiv ℝ I.c z).adjoint‖ ≤ p.Lc := by
    rw [← truth_operator I z]
    exact (MomentumSeparationInstance.spectralNorm_le_norm (jacobian I z)).trans (hI.2.2.2.2.2.1 z)
  obtain ⟨fLower, hlow, hgap⟩ := hI.2.2.1
  have hL : 0 < 1 + p.Lf := by linarith only [hLf]
  have hLip : ∀ y z, ‖gradient I.f y - gradient I.f z‖ ≤ (1 + p.Lf) * ‖y - z‖ := by
    intro y z
    exact (hI.2.2.2.2.1 z y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hg0 := HeavyTailedPL.gradient_sq_le hL hI.1 hLip hlow p.x0
  have hgap0 : 0 ≤ I.f p.x0 - fLower := sub_nonneg.mpr (hlow p.x0)
  have hg02 : ‖gradient I.f p.x0‖ ^ 2 ≤ 2 * S ^ 2 := by
    have hm := mul_le_mul (show 2 * (1 + p.Lf) ≤ 2 * S by dsimp [S]; linarith only [hfS])
      (hgap.trans hΔS) hgap0 (by positivity : 0 ≤ 2 * S)
    nlinarith only [hg0, hm]
  have hgn : ‖gradient I.f p.x0‖ ≤ 2 * S := by
    nlinarith only [hg02, norm_nonneg (gradient I.f p.x0), hS0, sq_nonneg S]
  have hgx : ‖gradient I.f x‖ ≤ 2 * S + S * D := by
    have hh := (hI.2.2.2.2.1 p.x0 x).trans
      (mul_le_mul hfS' hd (norm_nonneg _) hS0.le)
    have hn := norm_add_le (gradient I.f x - gradient I.f p.x0) (gradient I.f p.x0)
    rw [sub_add_cancel] at hn
    linarith only [hh, hgn, hn]
  have hcx : ‖I.c x‖ ≤ S + S * D := by
    have hh : ‖I.c x - I.c p.x0‖ ≤ p.Lc * ‖x - p.x0‖ :=
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z _ => (hI.2.1 z).hasFDerivAt.hasFDerivWithinAt)
        (fun z _ => by simpa only [ContinuousLinearMap.adjoint.norm_map] using hJ z)
        (convex_univ : Convex ℝ (Set.univ : Set (Point p.d))) (Set.mem_univ _) (Set.mem_univ _)
    have hb := hh.trans (mul_le_mul hcS' hd (norm_nonneg _) hS0.le)
    have hn := norm_add_le (I.c x - I.c p.x0) (I.c p.x0)
    rw [sub_add_cancel] at hn
    have hc0 := hI.2.2.2.1
    linarith only [hb, hn, hc0, hC0S]
  have hl : ‖(fderiv ℝ I.c x).adjoint lam‖ ≤ 8000 * S ^ 8 := by
    have hh := ((fderiv ℝ I.c x).adjoint.le_opNorm lam).trans
      (mul_le_mul ((hJ x).trans hcS') hlam (norm_nonneg _) hS0.le)
    exact hh.trans_eq (by ring)
  exact ⟨(norm_add_le _ _).trans (by linarith only [hgx, hl]), hcx⟩

lemma admissible_residual_measurable {Z : Type*} [MeasurableSpace Z]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (y : Z → Point p.d × Point p.m) (hy : Measurable y) :
    Measurable (fun z => ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 +
      ‖I.c (y z).1‖ ^ 2) := by
  have ht := (admissible_truth_measurable p hp I O hI).comp hy.fst
  have hJ : Measurable (fun z => LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m
      (truth I (y z).1).2.2) :=
    (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m).continuous.measurable.comp ht.snd.snd
  have heval : Continuous (fun z : (Point p.m →L[ℝ] Point p.d) × Point p.m => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hh := ((ht.fst.add (heval.measurable.comp (hJ.prodMk hy.snd))).norm.pow_const 2).add
    (ht.snd.fst.norm.pow_const 2)
  change Measurable (fun z => ‖(truth I (y z).1).1 +
    LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (truth I (y z).1).2.2 (y z).2‖ ^ 2 +
    ‖(truth I (y z).1).2.1‖ ^ 2) at hh
  simp only [truth_operator] at hh
  exact hh
end LongTails.Proofs.StochasticEqualityModel
