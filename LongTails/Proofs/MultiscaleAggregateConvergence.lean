import LongTails.Proofs.MultiscaleAggregateError
import LongTails.Proofs.HeavyTailedSospDescent

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultiscaleAggregateConvergence

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateHistory MultiscaleAggregateTrajectory MultiscaleAggregateBudget
open MultiscaleAggregateSampling MultiscaleAggregateCodec MultiscaleAggregateSchedule
open MultiscaleAggregateTracking MultiscaleAggregateMoments MultiscaleAggregateError

variable {p : Params}

lemma image_integrable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (φ : Model p → E) (k : ℕ) : Integrable (fun s => φ (trajectory p g s k)) P :=
  DistributedBatchedSgd.integrable_finite_range P _
    (measurable_trajectory_image p g hg k φ) (finite_trajectory_image p g k φ)

lemma estimate_mean_error (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 < p.L) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) (k : ℕ) (hk : k < rounds p) :
    let e := fun s => ‖estimate g s k - gradient (objective p f) (point g s k)‖
    Integrable e P ∧ (∫ s, e s ∂P) ≤ 198 * precision p := by
  let F := objective p f
  let G := fun i (s : Samples p) => gradient F (point g s i)
  let a := fun i s => ‖raw g s i - G i s‖
  let e := fun i s => ‖estimate g s i - G i s‖
  let u := fun i s => ‖unrounded p g s i (point g s i) - G i s‖ ^ 2
  let q := fun i s => 2 * (u i s + precision p ^ 2)
  let v := 4 * precision p ^ 2
  have hprec := precision_pos hε
  have hgrad (x) : HasGradientAt F (gradient F x) x := by
    rw [(objective_gradient f hg x).gradient]
    exact objective_gradient f hg x
  have hinit : ‖gradient F p.x0‖ ≤ radius p 0 := by
    apply initial_radius hε
    have hd := OracleTemplate.Gradient.descent hL hgrad hlip p.x0
    have h : ‖gradient F p.x0‖ ^ 2 / (2 * p.L) ≤ p.Δ := by
      have hb := hlower (p.x0 - (1 / p.L) • gradient F p.x0)
      change F _ - lower ≤ p.Δ at hgap
      change lower ≤ F _ at hb
      linarith
    nlinarith [(div_le_iff₀ (show 0 < 2 * p.L by positivity)).mp h]
  have hi (i : ℕ) : Integrable (u i) P ∧ (∫ s, u i s ∂P) ≤ precision p ^ 2 :=
    adaptive_variance P μ hw hIID g f hsg hg hh hε hlip hL i
  have hqi (i) : Integrable (q i) P := ((hi i).1.add (integrable_const _)).const_mul _
  have hq (i) : (∫ s, q i s ∂P) ≤ v := by
    dsimp only [q, v]
    rw [integral_const_mul, integral_add (hi i).1 (integrable_const _), integral_const,
      probReal_univ, one_smul]
    linarith [(hi i).2]
  have hmajor (i) (s) : a i s ^ 2 ≤ q i s := error_charge hε g s i (G i s)
  have hr (i) : 0 < radius p i := by unfold radius; positivity
  have hroot (s : Samples p) : overflow (e 0 s) (a 0 s) (radius p 0) ≤ 9 * a 0 s ^ 2 / radius p 0 := by
    have hmove := estimate_near_anchor g s hε 0
    have hann : anchor g s 0 = 0 := by simp [anchor]
    rw [hann, sub_zero] at hmove
    have hG : ‖G 0 s‖ ≤ radius p 0 := hinit
    apply overflow_root (hr 0)
    · exact (norm_sub_le _ _).trans (by linarith)
    · intro hraw
      have ht := norm_sub_le_norm_sub_add_norm_sub (raw g s 0) (G 0 s) (0 : Point p)
      simp only [sub_zero] at ht
      have hnear : ‖raw g s 0 - anchor g s 0‖ ≤ 3 * radius p 0 := by
        rw [hann, sub_zero]
        change ‖raw g s 0 - G 0 s‖ ≤ _ at hraw
        linarith [hr 0]
      change ‖estimate g s 0 - _‖ ≤ _
      rw [estimate_exact g s hε 0 hnear]
  obtain ⟨U, hUi, hU, hpath⟩ := tree_envelope P e a q (radius p) (schedule p).pred (rounds p) v
    (by dsimp [v]; positivity) (fun i _ => hr i)
    (fun i hi₁ hn => (schedule p).pred_lt (by
      have ht : (schedule p).pos i = i := Nat.mod_eq_of_lt hi₁
      rwa [ht]))
    (fun i hi₁ hn => by
      have h := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (scale_parent p i hi₁ hn)
      rw [pow_succ] at h
      unfold radius
      nlinarith [mul_le_mul_of_nonneg_right h hprec.le])
    (fun i _ => hmajor i) (fun i _ => hqi i) (fun i _ => hq i) hroot
    (fun i hi₁ hn s => tracking_step g s F hL hε hlip i hi₁ hn) k hk
  have hgm := fun i => (hsg i).measurable
  have hei : Integrable (e k) P :=
    ((image_integrable P g hgm (fun m => m.estimates k) (k + 1)).sub
      (image_integrable P g hgm (fun m => gradient F m.point) k)).norm
  refine ⟨hei, ?_⟩
  have hrk : precision p ≤ radius p k := by
    unfold radius
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))) hprec.le
  have hUpper : (∫ s, U s ∂P) ≤ 192 * precision p := by
    apply hU.trans
    apply (div_le_iff₀ (hr k)).mpr
    dsimp [v]
    nlinarith [mul_le_mul_of_nonneg_left hrk hprec.le]
  have hj : Integrable (fun s => (precision p)⁻¹ * q k s + precision p + U s) P :=
    (((hqi k).const_mul _).add (integrable_const _)).add hUi
  have hmono := integral_mono hei hj (fun s => by
    have h := error_le_raw_add_overflow (e := e k s) (a := a k s) (norm_nonneg _) (hr k).le
    have hlin : a k s ≤ (precision p)⁻¹ * q k s + precision p := by
      rw [inv_mul_eq_div]
      apply (sub_le_iff_le_add).mp
      apply (le_div_iff₀ hprec).mpr
      nlinarith [hmajor k s, sq_nonneg (a k s - precision p)]
    linarith [hpath s])
  change (∫ s, e k s ∂P) ≤ _
  have hpart : Integrable (fun s => (precision p)⁻¹ * q k s + precision p) P :=
    ((hqi k).const_mul _).add (integrable_const _)
  rw [integral_add hpart hUi,
    integral_add ((hqi k).const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hmono
  have hqk := mul_le_mul_of_nonneg_left (hq k) (inv_nonneg.mpr hprec.le)
  have hv : (precision p)⁻¹ * v = 4 * precision p := by dsimp [v]; field_simp
  linarith

end LongTails.Proofs.MultiscaleAggregateConvergence
