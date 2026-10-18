import LongTails.Proofs.PowerMirrorGeometry
import LongTails.Proofs.PowerMirrorTuning
import LongTails.Proofs.Execution

namespace LongTails.Proofs.PowerDualAveragingRun

open LongTails.Setups.PowerGeometryRelativeErrorConvex
open LongTails.Algorithms.PowerDualAveraging
open PowerMirrorGeometry PowerMirrorTuning

lemma direction_spec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E →L[ℝ] ℝ) :
    ‖direction g‖ ≤ ‖g‖ ∧ g (direction g) = ‖g‖ ^ 2 := by
  have hh := exists_direction g
  simp only [direction, dite_eq_left hh]
  exact Classical.choose_spec hh

lemma mirror_spec (d : Public) {β : ℝ} (hβ : 0 < β) (h : d.E →L[ℝ] ℝ) :
    ∀ w, β * d.ψ (mirror d β h) + h (mirror d β h) ≤ β * d.ψ w + h w := by
  intro w
  exact norm_square_prox_minimizer hβ (direction_spec h).1 (direction_spec h).2 w

def ValidState (d : Public) (s : State d) : Prop :=
  ∀ w, regularization d s.n * d.ψ s.z + s.h s.z ≤ regularization d s.n * d.ψ w + s.h w

lemma initial_valid (d : Public) (hd : d.Valid) :
    ValidState d ⟨0, d.x0, d.x0, 0⟩ := by
  intro w
  have hreg := regularization_pos d hd 0
  simp only [Public.ψ, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, mul_zero, zero_apply, add_zero]
  positivity

lemma step_valid (d : Public) (hd : d.Valid) (s : State d) (g : d.E →L[ℝ] ℝ) :
    ValidState d (step d s g) :=
  mirror_spec d (regularization_pos d hd _) _

noncomputable def potential (d : Public) (s : State d) (u : d.E) : ℝ :=
  regularization d s.n * d.ψ u + s.h u -
    (regularization d s.n * d.ψ s.z + s.h s.z)

lemma potential_nonneg (d : Public) {s : State d} (hs : ValidState d s)
    (u : d.E) : 0 ≤ potential d s u := sub_nonneg.mpr (hs u)

lemma query_identity (d : Public) (s : State d) :
    (totalWeight s.n + weight (s.n + 1)) • queryPoint d s =
      totalWeight s.n • s.x + weight (s.n + 1) • s.z := by
  rw [← totalWeight_succ]
  have hn := (totalWeight_pos (Nat.succ_pos s.n)).ne'
  have h₁ : totalWeight (s.n + 1) * (totalWeight s.n / totalWeight (s.n + 1)) =
      totalWeight s.n := by field_simp
  have h₂ : totalWeight (s.n + 1) * (weight (s.n + 1) / totalWeight (s.n + 1)) =
      weight (s.n + 1) := by field_simp
  simp only [queryPoint, smul_add, smul_smul, h₁, h₂]

lemma one_step (d : Public) (hd : d.Valid) {f : d.E → ℝ}
    (hf : ∀ x, HasFDerivAt f (fderiv ℝ f x) x)
    (hc : ConvexOn ℝ Set.univ f)
    (hlip : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ d.L * ‖x - y‖)
    {s : State d} (hs : ValidState d s) {u : d.E} {R : ℝ}
    (hdist : ‖u - d.x0‖ ≤ R) {g : d.E →L[ℝ] ℝ}
    (herr : ‖g - fderiv ℝ f (queryPoint d s)‖ ≤ d.α * ‖fderiv ℝ f (queryPoint d s)‖) :
    totalWeight (s.n + 1) * (f (step d s g).x - f u) + potential d (step d s g) u ≤
      totalWeight s.n * (f s.x - f u) + potential d s u +
        (regularization d (s.n + 1) - regularization d s.n) * d.ψ u +
        192 * d.L * d.α ^ 2 * R ^ 2 * ((s.n : ℝ) + 1) := by
  have hL := hd.1
  have hα := hd.2.2.2.1
  have hα' := hd.2.2.2.2.1
  have hdiff := hd.2.2.2.2.2.1
  have ha : 0 ≤ weight (s.n + 1) := by unfold weight; positivity
  have hμ : 0 < 64 * d.L * ((s.n : ℝ) + 1) := by positivity
  have hm := dual_averaging_drift (u := u) (g := g) (β' := regularization d (s.n + 1))
    (a := weight (s.n + 1)) ha hμ (hdiff s.z).hasFDerivAt hs
    (quadratic_surrogate d hd s.n s.z (step d s g).z)
  have hm' : potential d (step d s g) u ≤ potential d s u +
      (regularization d (s.n + 1) - regularization d s.n) * d.ψ u +
      weight (s.n + 1) * g (u - s.z) +
      weight (s.n + 1) ^ 2 * ‖g‖ ^ 2 / (2 * (64 * d.L * ((s.n : ℝ) + 1))) +
      (3 * (16 * d.L * ((s.n : ℝ) + 1) ^ (1 - 2 / d.p)) -
        (regularization d (s.n + 1) - regularization d s.n)) * d.ψ (step d s g).z -
      (16 * d.L * ((s.n : ℝ) + 1)) * ‖(step d s g).z - s.z‖ ^ 2 := by
    simpa only [potential, step] using hm
  have hconv := convex_coupling (u := u) (totalWeight_nonneg s.n) ha hc
    (hf (queryPoint d s)) (query_identity d s)
  rw [← totalWeight_succ] at hconv
  have hdescent := relative_steepest_descent hL hα hα' herr
    (direction_spec g).1 (direction_spec g).2 (smooth_upper hf hlip (queryPoint d s))
  have hA := totalWeight_pos (Nat.succ_pos s.n)
  have hdescent' := mul_le_mul_of_nonneg_left hdescent hA.le
  have hG : ‖fderiv ℝ f (queryPoint d s)‖ ≤ ‖g‖ + ‖g - fderiv ℝ f (queryPoint d s)‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le g (g - fderiv ℝ f (queryPoint d s))
  have he := PowerMirrorEnergy.relative_error_reply_bound hα' (norm_nonneg _) herr hG hα
  have hpair := (le_abs_self ((fderiv ℝ f (queryPoint d s) - g) (s.z - u))).trans
    ((fderiv ℝ f (queryPoint d s) - g).le_opNorm (s.z - u))
  rw [norm_sub_rev (fderiv ℝ f (queryPoint d s)) g] at hpair
  have hpair' : (fderiv ℝ f (queryPoint d s) - g) (s.z - u) ≤
      (4 / 3) * d.α * ‖g‖ * ‖s.z - u‖ :=
    hpair.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have herror := mul_le_mul_of_nonneg_left hpair' ha
  let residual :=
    (3 * (16 * d.L * ((s.n : ℝ) + 1) ^ (1 - 2 / d.p)) -
      (regularization d (s.n + 1) - regularization d s.n)) * d.ψ (step d s g).z -
      (16 * d.L * ((s.n : ℝ) + 1)) * ‖(step d s g).z - s.z‖ ^ 2
  have hbound :
      totalWeight (s.n + 1) * (f (step d s g).x - f u) + potential d (step d s g) u ≤
      (totalWeight s.n * (f s.x - f u) + potential d s u +
        (regularization d (s.n + 1) - regularization d s.n) * d.ψ u) + residual -
        totalWeight (s.n + 1) * ‖g‖ ^ 2 / (8 * d.L) +
        weight (s.n + 1) ^ 2 * ‖g‖ ^ 2 / (2 * (64 * d.L * ((s.n : ℝ) + 1))) +
        (4 / 3) * weight (s.n + 1) * d.α * ‖g‖ * ‖s.z - u‖ := by
    dsimp [residual]
    simp only [sub_apply, map_sub] at herror
    simp only [map_sub] at hm' hconv
    change totalWeight (s.n + 1) * f (step d s g).x ≤ _ at hdescent'
    simp only [div_eq_mul_inv] at hm' hconv hdescent' herror ⊢
    nlinarith only [hm', hconv, hdescent', herror]
  have hw := coupling_weight (Nat.succ_pos s.n) hL
  simp only [Nat.cast_succ] at hw
  have hh := PowerMirrorEnergy.coupling_error_bound hL hμ hA hw hbound
  have hr := squared_comparator_distance (w := (step d s g).z) (z := s.z) hdist
  have habs := PowerMirrorEnergy.radius_drift_absorption
    (show 0 ≤ 128 * d.L * ((s.n : ℝ) + 1) by positivity)
    (show 0 ≤ d.ψ (step d s g).z by unfold Public.ψ; positivity)
    (show d.α ^ 2 ≤ 1 / 16 by nlinarith)
    (drift_absorbs d hd s.n) hr
  dsimp [residual] at hh
  change _ ≤ (3 / 2) * (128 * d.L * ((s.n : ℝ) + 1)) * d.α ^ 2 * R ^ 2 at habs
  nlinarith only [hh, habs]

noncomputable def trajectory (d : Public) (oracle : ℕ → d.E → d.E →L[ℝ] ℝ) : ℕ → State d
  | 0 => ⟨0, d.x0, d.x0, 0⟩
  | n + 1 => step d (trajectory d oracle n) (oracle n (queryPoint d (trajectory d oracle n)))

lemma trajectory_count (d : Public) (oracle : ℕ → d.E → d.E →L[ℝ] ℝ) (n : ℕ) :
    (trajectory d oracle n).n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [trajectory, step] using congrArg Nat.succ ih

lemma trajectory_valid (d : Public) (hd : d.Valid)
    (oracle : ℕ → d.E → d.E →L[ℝ] ℝ) (n : ℕ) : ValidState d (trajectory d oracle n) := by
  cases n with
  | zero => exact initial_valid d hd
  | succ n => exact step_valid d hd _ _

lemma execute_eq (d : Public) (O : OracleTemplate.Oracle d.E (d.E →L[ℝ] ℝ))
    (T : ℕ) (seed : (algorithm d).Seed) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (algorithm d) (fun _ => T) seed ξ =
      (trajectory d (fun k x => O.answer k (0, x) (ξ k)) T).x := by
  rw [OracleTemplate.execute_indexed]
  have hi (n : ℕ) :
      ((fun sc : State d × ℕ =>
        (step d sc.1 (O.answer sc.2 (0, queryPoint d sc.1) (ξ sc.2)), sc.2 + 1))^[n]
        (⟨0, d.x0, d.x0, 0⟩, 0)) =
      (trajectory d (fun k x => O.answer k (0, x) (ξ k)) n, n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        rfl
  change output d (((fun sc : State d × ℕ =>
    (step d sc.1 (O.answer sc.2 (0, queryPoint d sc.1) (ξ sc.2)), sc.2 + 1))^[T]
    (⟨0, d.x0, d.x0, 0⟩, 0)).1) = _
  rw [hi]
  rfl


lemma trajectory_energy (d : Public) (hd : d.Valid) {f : d.E → ℝ}
    (hf : ∀ x, HasFDerivAt f (fderiv ℝ f x) x)
    (hc : ConvexOn ℝ Set.univ f)
    (hlip : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ d.L * ‖x - y‖)
    (oracle : ℕ → d.E → d.E →L[ℝ] ℝ)
    (herr : ∀ k x, ‖oracle k x - fderiv ℝ f x‖ ≤ d.α * ‖fderiv ℝ f x‖)
    {u : d.E} {R : ℝ} (hdist : ‖u - d.x0‖ ≤ R) {T : ℕ} :
    ∀ n ≤ T,
      totalWeight n * (f (trajectory d oracle n).x - f u) + potential d (trajectory d oracle n) u ≤
        regularization d n * d.ψ u + 192 * d.L * d.α ^ 2 * R ^ 2 * n * T := by
  have hL := hd.1
  intro n
  induction n with
  | zero =>
      intro _
      simp [trajectory, totalWeight, potential, Public.ψ]
  | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hh := one_step d hd hf hc hlip (trajectory_valid d hd oracle n) hdist
        (herr n (queryPoint d (trajectory d oracle n)))
      rw [trajectory_count] at hh
      change totalWeight (n + 1) * (f (trajectory d oracle (n + 1)).x - f u) +
        potential d (trajectory d oracle (n + 1)) u ≤ _ at hh
      have hnt : (n : ℝ) + 1 ≤ T := by exact_mod_cast hn
      have hnoise := mul_le_mul_of_nonneg_left hnt
        (show 0 ≤ 192 * d.L * d.α ^ 2 * R ^ 2 by positivity)
      simp only [Nat.cast_add, Nat.cast_one] at hh ⊢
      nlinarith only [hh, hprev, hnoise]

lemma execute_accuracy (d : Public) (hd : d.Valid) {f : d.E → ℝ}
    (hf : ∀ x, HasFDerivAt f (fderiv ℝ f x) x)
    (hc : ConvexOn ℝ Set.univ f)
    (hlip : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ d.L * ‖x - y‖)
    (O : OracleTemplate.Oracle d.E (d.E →L[ℝ] ℝ)) {R ε : ℝ} (hε : 0 < ε)
    (herr : ∀ k seed x, ‖O.answer k (0, x) seed - fderiv ℝ f x‖ ≤ d.α * ‖fderiv ℝ f x‖)
    {u : d.E} (hmin : ∀ x, f u ≤ f x) (hdist : ‖u - d.x0‖ ≤ R)
    {T : ℕ} (hT : 0 < T)
    (hbudget : (12 * geometryConstant d * d.L * R ^ 2 / ε) ^ (d.p / (d.p + 2)) +
      4224 * d.L * d.α ^ 2 * R ^ 2 / ε ≤ T)
    (seed : (algorithm d).Seed) (ξ : (k : ℕ) → O.Seed k) :
    f (OracleTemplate.execute O (algorithm d) (fun _ => T) seed ξ) - f u ≤ ε := by
  rw [execute_eq]
  let oracle := fun k x => O.answer k (0, x) (ξ k)
  have he := trajectory_energy d hd hf hc hlip oracle (fun k x => herr k (ξ k) x) hdist T le_rfl
  have hv := potential_nonneg d (trajectory_valid d hd oracle T) u
  have hreg := regularization_upper (R := R) d hd hT
  have hR : 0 ≤ R := (norm_nonneg _).trans hdist
  have hψ : d.ψ u ≤ R ^ 2 / 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) hR).mpr hdist
    unfold Public.ψ
    linarith
  have hregψ := mul_le_mul_of_nonneg_left hψ (regularization_pos d hd T).le
  have hL := hd.1
  have hp := hd.2.1
  have hB := geometryConstant_lower d
  have hnum : totalWeight T * (f (trajectory d oracle T).x - f u) ≤
      2 * (geometryConstant d * d.L * R ^ 2) * (T : ℝ) ^ (2 - 2 / d.p) +
      704 * (d.L * d.α ^ 2 * R ^ 2) * (T : ℝ) ^ 2 := by
    nlinarith only [he, hv, hreg, hregψ]
  apply accuracy_from_numerator hp (by positivity) (by positivity) hε hT
    (sub_nonneg.mpr (hmin _)) _ hnum
  have h₁ : 12 * (geometryConstant d * d.L * R ^ 2) / ε =
      12 * geometryConstant d * d.L * R ^ 2 / ε := by ring
  have h₂ : 4224 * (d.L * d.α ^ 2 * R ^ 2) / ε =
      4224 * d.L * d.α ^ 2 * R ^ 2 / ε := by ring
  rw [h₁, h₂]
  exact hbudget

end LongTails.Proofs.PowerDualAveragingRun
