import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.MollifiedSmoothParameters
import LongTails.Proofs.FinitePrefixExpectation
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate Set

namespace LongTails.Proofs.MollifiedSmoothLowerBound

open LongTails.Setups.GeneralizedSmoothConvexFull
open MollifiedSmoothParameters MollifiedSmoothHardFamily CompactMollification

lemma exists_failure (p : Params) (hp : spec.valid p) (N : ℕ)
    (hlarge : 8192 ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε))
    (hN : N ≤ ⌊Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 16384⌋₊)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  rcases hp with ⟨h0, h1, hR, hε, hupper, hdim⟩
  let m := N + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmcast : (m : ℝ) = (N : ℝ) + 1 := by simp [m]
  let r := p.R / 4
  let a := amplitude p.R m
  let δ := deadWidth p.R m
  let φ := kernel p.d p.R hR m hm
  have hr : 0 < r := by dsimp [r]; positivity
  have ha0 : 0 < a := amplitude_pos p.R hR m hm
  have hδ : 0 < δ := deadWidth_pos p.R hR m hm
  have hρ : φ.rOut ≤ δ / 16 := (radius_bounds p.R hR m hm).1
  have hρr : φ.rOut ≤ r / 128 := (radius_bounds p.R hR m hm).2
  have ha : ((N : ℝ) + 1) * a ^ 2 = r ^ 2 := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using amplitude_square p.R m hm
  have hscale : ((N : ℝ) + 1) * δ ≤ a / 8 := by
    have hh := width_identity p.R m hm
    simpa only [m, Nat.cast_add, Nat.cast_one] using hh.le
  let f := fun π : Fin (N + 1) ↪ Fin p.d => value φ p.L0 r δ a π
  let g := fun π : Fin (N + 1) ↪ Fin p.d => grad φ p.L0 r δ a π
  have hmin (π : Fin (N + 1) ↪ Fin p.d) :
      ∃ z, ‖z‖ ≤ 4 * r ∧ IsMinOn (f π) univ z ∧ f π z ≤ p.L0 / 2 * φ.rOut ^ 2 :=
    value_minimum φ p.L0 r δ a h0.le hr hδ.le hρr π ha.le
  let z := fun π : Fin (N + 1) ↪ Fin p.d => (hmin π).choose
  have hz (π : Fin (N + 1) ↪ Fin p.d) := (hmin π).choose_spec
  let loss := fun π x => f π x - f π (z π)
  let gap := p.L0 * a ^ 2 / (16384 * (m : ℝ))
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hminGap (π : Fin (N + 1) ↪ Fin p.d) : f π (z π) ≤ gap := by
    apply (hz π).2.2.trans
    have hh := mul_le_mul_of_nonneg_left (radius_gap p.R m hm) h0.le
    dsimp [gap, φ, kernel, a]
    convert hh using 1 <;> ring
  have hnear (π : Fin (N + 1) ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
      (hx : |x (π (Fin.last N))| ≤ δ / 8) : gap ≤ loss π x := by
    have hh := value_near φ p.L0 r δ a h0.le hr hδ.le ha0.le hρ π hscale x hx
    rw [← hmcast] at hh
    change p.L0 * a ^ 2 / (8192 * (m : ℝ)) ≤ f π x at hh
    have he : p.L0 * a ^ 2 / (8192 * (m : ℝ)) = 2 * gap := by dsimp [gap]; ring
    rw [he] at hh
    dsimp [loss]
    linarith [hminGap π]
  have hfar (π : Fin (N + 1) ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
      (hx : p.R ≤ ‖x‖) : gap ≤ loss π x := by
    have hx' : 4 * r ≤ ‖x‖ := by dsimp [r]; linarith
    have hh := value_far φ p.L0 r δ a h0.le hr hδ.le (by linarith) π x hx'
    have hsmall : gap ≤ p.L0 * r ^ 2 / 16384 := by
      apply (div_le_iff₀ (by positivity : 0 < 16384 * (m : ℝ))).mpr
      have ha' : a ^ 2 ≤ r ^ 2 := by
        rw [← hmcast] at ha
        nlinarith [sq_nonneg a]
      have hh := mul_le_mul_of_nonneg_left ha' h0.le
      have hmore := mul_nonneg (show 0 ≤ p.L0 * r ^ 2 by positivity) (sub_nonneg.mpr hm1)
      nlinarith only [hh, hmore]
    change p.L0 * r ^ 2 / 64 ≤ f π x at hh
    dsimp [loss]
    have hpr : 0 ≤ p.L0 * r ^ 2 := by positivity
    linarith [hminGap π]
  let θ := δ / 8
  let D := 2 * (m : ℝ) ^ 2 * (p.R ^ 2 / θ ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hlen := floor_length p.L0 p.R p.ε hlarge N hN
  have hDs : D + (N + 1 : ℕ) ≤ (p.d : ℝ) := by
    have hratio := hiding_ratio p.R hR m hm
    have hd := hiding_dimension m hm
    have hmle : (m : ℝ) ≤ 1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := by
      have hq := mul_nonneg h1 hR.le
      have hs := Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)
      change (m : ℝ) ≤ _ at hlen
      linarith
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hmle 5
    have hceil := Nat.le_ceil (17592186044416 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5)
    have hdcast : (⌈17592186044416 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5⌉₊ : ℝ) ≤ p.d := by
      exact_mod_cast hdim
    have hpos : 0 ≤ (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5 := by positivity
    change p.R ^ 2 / θ ^ 2 = _ at hratio
    dsimp [D]
    rw [hratio]
    change 2 * (m : ℝ) ^ 2 * (65536 * (m : ℝ) ^ 3) + (m : ℝ) ≤ _
    nlinarith only [hd, hpow, hceil, hdcast, hpos]
  have hεgap : 2 * p.ε < gap := accuracy_gap p.L0 p.R p.ε h0 hR hε m hm hlen
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨π, hbad⟩ := FinitePrefixExpectation.exists_failure p.R θ D gap p.ε hR.le hθ hD hgap.le
    hDs le_rfl hεgap (fun π t => partialReply φ p.L0 r δ a π t) g loss
    (fun π ρ t x hp => partial_prefix φ p.L0 r δ a π ρ t hp x)
    (fun π t x _ hx => partial_eq φ p.L0 r δ a hr hδ.le hρ (by linarith) π ha.le t x
      (by intro hx'; exact hx (by dsimp [r] at hx'; linarith)))
    (fun π x => sub_nonneg.mpr ((hz π).2.1 (mem_univ x))) hnear hfar
    query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let O := SmoothConvexFiniteLowerBound.oracle p.x0 (g π)
  have hg := value_gradient φ p.L0 r δ a h0.le hr hδ.le π ha.le
  have hl := SmoothConvexFiniteWall.field_lipschitz p.L0 r δ a h0.le hr hδ.le π ha.le
  have hgl := SmoothConvexMollification.average_field_lipschitz φ _ p.L0 hl
  have hgd := SmoothConvexMollification.average_field_differentiable φ _ p.L0 hl
  have hadm : spec.admissible p (fun x : EuclideanSpace ℝ (Fin p.d) => f π (x - p.x0)) O := by
    refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _
      (average_convex φ _ (continuous_iff_continuousAt.mpr
        (fun x => (SmoothConvexFiniteWall.objective_gradient p.L0 r δ a hr hδ.le π x).continuousAt))
        (SmoothConvexFiniteWall.objective_convex p.L0 r δ a h0.le hr hδ.le π)), ?_, ?_, ?_,
      p.x0 + z π, ?_, ?_⟩
    · intro history seed x
      exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ hg x
    · intro history seed
      exact hgd.comp (differentiable_id.sub_const p.x0)
    · intro history seed x
      have hf := hgd.comp (differentiable_id.sub_const p.x0)
      have hb := GeneralizedSmoothMollification.derivative_bound_of_quadratic_increment
        (fun x => g π (x - p.x0)) x _ p.L0 0 (hf x).hasFDerivAt h0.le (by norm_num)
        (fun y => by simpa only [g, grad, zero_mul, add_zero, sub_sub_sub_cancel_right] using hgl (y - p.x0) (x - p.x0))
      exact hb.trans (le_add_of_nonneg_right (mul_nonneg h1 (norm_nonneg _)))
    · intro x _
      change f π (p.x0 + z π - p.x0) ≤ f π (x - p.x0)
      rw [add_sub_cancel_left]
      exact (hz π).2.1 (mem_univ (x - p.x0))
    · have hh := (hz π).1
      simpa only [z, sub_add_cancel_left, norm_neg, r, mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hh
  refine ⟨fun x : EuclideanSpace ℝ (Fin p.d) => f π (x - p.x0), O, hadm, ?_⟩
  rintro ⟨xstar, hmstar, hi, he⟩
  change EuclideanSpace ℝ (Fin p.d) at xstar
  have hstar : f π (xstar - p.x0) = f π (z π) := by
    apply le_antisymm
    · have hh := hmstar (mem_univ (p.x0 + z π))
      change f π (xstar - p.x0) ≤ f π (p.x0 + z π - p.x0) at hh
      simpa only [add_sub_cancel_left] using hh
    · exact (hz π).2.1 (mem_univ (xstar - p.x0))
  have hout :
      (fun w : A.Seed × (ℕ → Unit) => f π (execute O A (fun _ => N) w.1 w.2 - p.x0) - f π (xstar - p.x0)) =
      fun w => loss π (output ((fun s => A.update s (g π (query s)))^[N] (A.initial w.1))) := by
    funext w
    rw [hstar, SmoothConvexFiniteLowerBound.execute_translated p.x0 (g π) A N w.1 w.2]
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      f π (execute O A (fun _ => N) w.1 w.2 - p.x0) - f π (xstar - p.x0))
      (P : Measure (A.Seed × (ℕ → Unit))) at hi
    rw [hout] at hi
    exact hi
  · change (∫ w : A.Seed × (ℕ → Unit),
      f π (execute O A (fun _ => N) w.1 w.2 - p.x0) - f π (xstar - p.x0)
      ∂(P : Measure (A.Seed × (ℕ → Unit)))) ≤ p.ε at he
    rw [hout] at he
    exact he

end LongTails.Proofs.MollifiedSmoothLowerBound
