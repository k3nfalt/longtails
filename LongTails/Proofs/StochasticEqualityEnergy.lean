import LongTails.Proofs.StochasticEqualityProcess
import LongTails.Proofs.StochasticEqualityStopped
import LongTails.Proofs.StochasticEqualityRestoration

namespace LongTails.Proofs.StochasticEqualityEnergy

open MeasureTheory OracleTemplate
open LongTails.Proofs.StochasticEqualityStopped

open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.StochasticEqualityDirection
open LongTails.Proofs.StochasticEqualityGeometry
open LongTails.Proofs.StochasticEqualityMoments

lemma packed_direction_error (p : Public) {G M K : ℝ} (hν : 0 < p.ν)
    (u v : Reply p)
    (hreg : regular p.ν (operatorEquiv p.d p.m u.2.2))
    (huG : ‖u.1‖ ≤ G) (huM : ‖u.2.1‖ ≤ M)
    (hvG : ‖v.1‖ ≤ G) (hvJ : ‖v.2.2‖ ≤ p.Lc)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * G / p.ν + 4 * p.Lc * G / p.ν ^ 2 + 4 * G / p.ν) +
      p.Lc + M ≤ K) :
    ‖direction p.ν (operatorEquiv p.d p.m v.2.2) v.1 v.2.1 -
      (-tangent (operatorEquiv p.d p.m u.2.2) u.1 - operatorEquiv p.d p.m u.2.2 u.2.1)‖ ^ 2 ≤
      K ^ 2 * ‖pack p v - pack p u‖ ^ 2 := by
  have hL : 0 ≤ p.Lc := (norm_nonneg v.2.2).trans hvJ
  have hG : 0 ≤ G := (norm_nonneg u.1).trans huG
  have hvL : ‖operatorEquiv p.d p.m v.2.2‖ ≤ p.Lc :=
    (MomentumSeparationInstance.spectralNorm_le_norm _).trans hvJ
  have hd : ‖operatorEquiv p.d p.m v.2.2 - operatorEquiv p.d p.m u.2.2‖ ≤ ‖v.2.2 - u.2.2‖ := by
    rw [← map_sub]
    exact MomentumSeparationInstance.spectralNorm_le_norm _
  obtain ⟨heg, hec, heJ⟩ := component_errors_le_pack p u v
  have heop := hd.trans heJ
  have ht := thresholded_tangent_error hν hreg huG hvG hvL
  have hh := direction_error_bound p.ν (operatorEquiv p.d p.m u.2.2)
    (operatorEquiv p.d p.m v.2.2) u.1 v.1 u.2.1 v.2.1
  have hb : ‖direction p.ν (operatorEquiv p.d p.m v.2.2) v.1 v.2.1 -
      (-tangent (operatorEquiv p.d p.m u.2.2) u.1 - operatorEquiv p.d p.m u.2.2 u.2.1)‖ ≤
      K * ‖pack p v - pack p u‖ := by
    calc
      _ ≤ ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * ‖v.1 - u.1‖ +
          ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * G / p.ν + 4 * p.Lc * G / p.ν ^ 2 + 4 * G / p.ν) *
            ‖operatorEquiv p.d p.m v.2.2 - operatorEquiv p.d p.m u.2.2‖) +
          ‖operatorEquiv p.d p.m v.2.2‖ * ‖v.2.1 - u.2.1‖ +
          ‖operatorEquiv p.d p.m v.2.2 - operatorEquiv p.d p.m u.2.2‖ * ‖u.2.1‖ := by
        linarith only [hh, ht]
      _ ≤ ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * ‖pack p v - pack p u‖ +
          ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * G / p.ν + 4 * p.Lc * G / p.ν ^ 2 + 4 * G / p.ν) *
            ‖pack p v - pack p u‖) + p.Lc * ‖pack p v - pack p u‖ +
          ‖pack p v - pack p u‖ * M := by gcongr
      _ = ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
          ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * G / p.ν + 4 * p.Lc * G / p.ν ^ 2 + 4 * G / p.ν) +
          p.Lc + M) * ‖pack p v - pack p u‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2

open LongTails.Algorithms.StochasticEquality
open LongTails.Proofs.StochasticEqualityProcess

noncomputable def traceDirectionError {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : Point p.d) (offset n : ℕ) (ξ : ℕ → Ω) : Point p.d :=
  let u := truth (trainingTrace p cfg g ξ x offset n).point
  let v := (trainingTrace p cfg g ξ x offset (n + 1)).estimate
  direction p.ν (operatorEquiv p.d p.m v.2.2) v.1 v.2.1 -
    (-tangent (operatorEquiv p.d p.m u.2.2) u.1 - operatorEquiv p.d p.m u.2.2 u.2.1)

lemma trace_step {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (x : Point p.d) (offset n : ℕ) (ξ : ℕ → Ω) :
    (trainingTrace p cfg g ξ x offset (n + 1)).point - (trainingTrace p cfg g ξ x offset n).point =
      cfg.step • direction p.ν
        (operatorEquiv p.d p.m (trainingTrace p cfg g ξ x offset (n + 1)).estimate.2.2)
        (trainingTrace p cfg g ξ x offset (n + 1)).estimate.1
        (trainingTrace p cfg g ξ x offset (n + 1)).estimate.2.1 := by
  simp only [trace_succ, trainingUpdate, add_sub_cancel_left]

lemma trace_step_error {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : Point p.d) (offset n : ℕ) (ξ : ℕ → Ω) :
    let u := truth (trainingTrace p cfg g ξ x offset n).point
    (trainingTrace p cfg g ξ x offset (n + 1)).point - (trainingTrace p cfg g ξ x offset n).point =
      cfg.step • (-tangent (operatorEquiv p.d p.m u.2.2) u.1 -
        operatorEquiv p.d p.m u.2.2 u.2.1 + traceDirectionError p cfg g truth x offset n ξ) := by
  rw [trace_step]
  congr 1
  dsimp only [traceDirectionError]
  abel

noncomputable def residual (p : Public) (truth : Point p.d → Reply p) (β : ℝ) (y : Point p.d) : ℝ :=
  ‖tangent (operatorEquiv p.d p.m (truth y).2.2) (truth y).1‖ ^ 2 +
    β / 2 * ‖operatorEquiv p.d p.m (truth y).2.2 (truth y).2.1‖ ^ 2

lemma residual_nonneg (p : Public) (truth : Point p.d → Reply p) {β : ℝ} (hβ : 0 ≤ β)
    (y : Point p.d) : 0 ≤ residual p truth β y := by
  unfold residual
  positivity

lemma measurable_residual (p : Public) (truth : Point p.d → Reply p) (ht : Measurable truth) (β : ℝ) :
    Measurable (residual p truth β) := by
  have hJ : Measurable (fun y => operatorEquiv p.d p.m (truth y).2.2) :=
    (operatorEquiv p.d p.m).continuous.measurable.comp ht.snd.snd
  have hm := StochasticEqualitySampling.measurable_multiplier.comp (hJ.prodMk ht.fst)
  have heval : Continuous (fun z : (Point p.m →L[ℝ] Point p.d) × Point p.m => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have ha := ht.fst.add (heval.measurable.comp (hJ.prodMk hm))
  have hb := heval.measurable.comp (hJ.prodMk ht.snd.fst)
  exact (ha.norm.pow_const 2).add ((hb.norm.pow_const 2).const_mul (β / 2))

noncomputable def stoppedResidual {Ω : Type*} (p : Public) (cfg : Config) (β : ℝ)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) : ℝ := by
  classical
  exact if active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ then
    residual p truth β (trainingTrace p cfg g ξ (x ξ) offset n).point else 0

lemma stoppedResidual_nonneg {Ω : Type*} (p : Public) (cfg : Config) {β : ℝ} (hβ : 0 ≤ β)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω) :
    0 ≤ stoppedResidual p cfg β g truth x good offset n ξ := by
  unfold stoppedResidual
  split_ifs
  · exact residual_nonneg p truth hβ _
  · exact le_rfl

lemma measurable_stoppedResidual {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config) (β : ℝ)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset n : ℕ) :
    Measurable (stoppedResidual p cfg β g truth x good offset n) := by
  classical
  have hm := (measurable_residual p truth ht β).comp
    (measurable_trace p cfg g hg id measurable_id x hx offset n).1
  have ha := measurableSet_active p cfg truth ht
    (fun k z => (trainingTrace p cfg g z (x z) offset k).point)
    (fun k => (measurable_trace p cfg g hg id measurable_id x hx offset k).1) good hgood n
  exact hm.ite ha measurable_const

lemma trace_movement_residual {Ω : Type*} (p : Public) (cfg : Config) {β : ℝ}
    (hν : 0 < p.ν) (hβ : 2 ≤ β)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (x : Point p.d) (offset n : ℕ) (ξ : ℕ → Ω) :
    ‖(trainingTrace p cfg g ξ x offset (n + 1)).point - (trainingTrace p cfg g ξ x offset n).point‖ ^ 2 ≤
      2 * cfg.step ^ 2 * (residual p truth β (trainingTrace p cfg g ξ x offset n).point +
        ‖traceDirectionError p cfg g truth x offset n ξ‖ ^ 2) := by
  let u := truth (trainingTrace p cfg g ξ x offset n).point
  have ht := StochasticEqualityMerit.orthogonal_direction_norm
    (e := traceDirectionError p cfg g truth x offset n ξ) (tangent_orthogonal hν (hreg (trainingTrace p cfg g ξ x offset n).point) u.1 u.2.1)
  rw [trace_step_error, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hm := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg cfg.step)
  have hb := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ β / 2 by linarith)
    (sq_nonneg ‖operatorEquiv p.d p.m u.2.2 u.2.1‖)
  simp only [one_mul] at hb
  have hs := add_le_add (add_le_add (le_refl (‖tangent (operatorEquiv p.d p.m u.2.2) u.1‖ ^ 2)) hb)
    (le_refl (‖traceDirectionError p cfg g truth x offset n ξ‖ ^ 2))
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg cfg.step)
  convert hm.trans hh using 1
  dsimp only [residual, u]
  ring

open scoped Classical in
lemma stopped_direction_error_le {Ω : Type*} (p : Public) (cfg : Config) {K : ℝ}
    (hν : 0 < p.ν) (hL : 0 ≤ p.Lc) (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap)
    (g : Point p.d → Ω → Reply p) (truth : Point p.d → Reply p)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (x : (ℕ → Ω) → Point p.d) (good : (ℕ → Ω) → Prop) (offset n : ℕ) (ξ : ℕ → Ω)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) +
      p.Lc + cfg.constraintCap ≤ K) :
    (if active p cfg truth (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ then
      ‖traceDirectionError p cfg g truth (x ξ) offset n ξ‖ ^ 2 else 0) ≤
      K ^ 2 * stoppedError p cfg g truth x good offset n ξ := by
  classical
  by_cases ha : active p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ
  · obtain ⟨hg, hc⟩ := active_caps p cfg truth
      (fun k z => (trainingTrace p cfg g z (x z) offset k).point) good n ξ ha
    obtain ⟨hvg, _, hvj⟩ := trace_estimate_caps p cfg hG hM hL g ξ (x ξ) offset (n + 1)
    simpa only [ha, ↓reduceIte, stoppedError, traceDirectionError] using
      packed_direction_error p hν _ _ (hreg _) hg hc hvg hvj hK
  · simp only [ha, ↓reduceIte, stoppedError, mul_zero, le_refl]

lemma trace_merit_descent {Ω : Type*} (p : Public) (cfg : Config) {κ β : ℝ}
    (hν : 0 < p.ν) (hLf : 0 ≤ p.Lf) (hLc : 0 ≤ p.Lc) (hLJ : 0 ≤ p.LJ)
    (hG : 0 ≤ cfg.gradientCap) (hη : 0 ≤ cfg.step)
    (f : Point p.d → ℝ) (truth : Point p.d → Reply p)
    (hf : ∀ y, HasGradientAt f (truth y).1 y)
    (hc : ∀ y, HasFDerivAt (fun z => (truth z).2.1) (operatorEquiv p.d p.m (truth y).2.2).adjoint y)
    (hgL : ∀ y z, ‖(truth z).1 - (truth y).1‖ ≤ p.Lf * ‖z - y‖)
    (hJn : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hJL : ∀ y z, ‖(truth z).2.2 - (truth y).2.2‖ ≤ p.LJ * ‖z - y‖)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (hκ : (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ)
    (hβ : 8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β)
    (hηD : (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16)
    (g : Point p.d → Ω → Reply p) (x : Point p.d) (offset n : ℕ) (ξ : ℕ → Ω)
    (hgc : ‖(truth (trainingTrace p cfg g ξ x offset n).point).1‖ ≤ cfg.gradientCap)
    (hcc : ‖(truth (trainingTrace p cfg g ξ x offset n).point).2.1‖ ≤ cfg.constraintCap) :
    let J := fun y => operatorEquiv p.d p.m (truth y).2.2
    let Φ := StochasticEqualityDescent.merit f (fun y => (truth y).2.1) J (fun y => (truth y).1) β
    Φ (trainingTrace p cfg g ξ x offset (n + 1)).point ≤ Φ (trainingTrace p cfg g ξ x offset n).point -
      cfg.step * residual p truth β (trainingTrace p cfg g ξ x offset n).point / 2 +
      cfg.step * (β + 3) * ‖traceDirectionError p cfg g truth x offset n ξ‖ ^ 2 := by
  let J := fun y => operatorEquiv p.d p.m (truth y).2.2
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hJB (y : Point p.d) : ‖J y‖ ≤ p.Lc :=
    (MomentumSeparationInstance.spectralNorm_le_norm _).trans (hJn y)
  have hJL' (y z : Point p.d) : ‖J z - J y‖ ≤ p.LJ * ‖z - y‖ := by
    change ‖operatorEquiv p.d p.m (truth z).2.2 - operatorEquiv p.d p.m (truth y).2.2‖ ≤ _
    rw [← map_sub]
    exact (MomentumSeparationInstance.spectralNorm_le_norm _).trans (hJL y z)
  have hm := (norm_multiplier_le hν (hreg (trainingTrace p cfg g ξ x offset n).point) (truth (trainingTrace p cfg g ξ x offset n).point).1).trans
    (div_le_div_of_nonneg_right hgc hν.le)
  have hml := (multiplier_field_lipschitz hν hreg hJB hgL hJL'
    (trainingTrace p cfg g ξ x offset n).point (trainingTrace p cfg g ξ x offset (n + 1)).point hgc).trans
    (mul_le_mul_of_nonneg_right hκ (norm_nonneg _))
  have h := StochasticEqualityDescent.field_descent hLf hLc hLJ
    (show 0 ≤ cfg.gradientCap / p.ν by positivity) hκ0 hν hη hβ hf hc hgL hJB hJL'
    hm hml (hreg (trainingTrace p cfg g ξ x offset n).point) hcc (trace_step_error p cfg g truth x offset n ξ) hηD
  convert h using 1
  dsimp only [residual, J]
  ring

lemma frozen_potential_upper {X : Type*} (active : ℕ → Prop) [DecidablePred active]
    (x : ℕ → X) (φ : X → ℝ) (r v e : ℕ → ℝ) {η C K W : ℝ}
    (hη : 0 ≤ η) (hC : 0 ≤ C) (T : ℕ)
    (hmono : ∀ k j, k ≤ j → active j → active k)
    (hinit : φ (x 0) ≤ W - 1) (hr : ∀ k, 0 ≤ r k) (he : ∀ k, 0 ≤ e k)
    (hstep : ∀ k < T, active k → φ (x (k + 1)) ≤ φ (x k) - η * r k / 2 + η * C * v k)
    (herr : ∀ k < T, (if active k then v k else 0) ≤ K ^ 2 * e k)
    (hbudget : η * C * K ^ 2 * (∑ k ∈ Finset.range T, e k) ≤ W)
    (n : ℕ) (hn : n ≤ T) : φ (freeze active x n) ≤ 2 * W - 1 := by
  have hf := frozen_energy active x φ r v η C n hmono (fun k hk => hstep k (by omega))
  have hres : 0 ≤ ∑ k ∈ Finset.range n, if active k then r k else 0 := by
    apply Finset.sum_nonneg
    intro k _
    split_ifs <;> first | exact hr k | exact le_rfl
  have hv := Finset.sum_le_sum (s := Finset.range n) (fun k hk => herr k (by
    have hh := Finset.mem_range.mp hk
    omega))
  rw [← Finset.mul_sum] at hv
  have hep : (∑ k ∈ Finset.range n, e k) ≤ ∑ k ∈ Finset.range T, e k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun k _ _ => he k)
  have hev := hv.trans (mul_le_mul_of_nonneg_left hep (sq_nonneg K))
  have hscaled := mul_le_mul_of_nonneg_left hev (mul_nonneg hη hC)
  have hrscaled := mul_nonneg (show 0 ≤ η / 2 by positivity) hres
  nlinarith only [hf, hscaled, hrscaled, hinit, hbudget]

open scoped Classical in
lemma active_of_frozen_upper {Z : Type*} (p : Public) (cfg : Config)
    (truth : Point p.d → Reply p) (path : ℕ → Z → Point p.d) (good : Z → Prop)
    (φ : Point p.d → ℝ) (U : ℝ) (T : ℕ) (z : Z)
    (hgood : good z) (hinit : ‖(truth (path 0 z)).1‖ ≤ cfg.gradientCap ∧
      ‖(truth (path 0 z)).2.1‖ ≤ cfg.constraintCap)
    (hguard : ∀ y, φ y ≤ U → ‖(truth y).1‖ ≤ cfg.gradientCap ∧ ‖(truth y).2.1‖ ≤ cfg.constraintCap)
    (hφ : ∀ n ≤ T, φ (freeze (fun k => active p cfg truth path good k z) (fun k => path k z) n) ≤ U) :
    ∀ n ≤ T, active p cfg truth path good n z := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨hgood, hinit⟩
  | succ n ih =>
    intro hn
    have ha := ih (by omega)
    have hh := hφ (n + 1) hn
    rw [freeze, ite_eq_left ha] at hh
    exact ⟨ha, hguard _ hh⟩

lemma frozen_error_bounds {X : Type*} (active : ℕ → Prop) [DecidablePred active]
    (good : Prop) [Decidable good] (x : ℕ → X) (φ : X → ℝ)
    (r v e a : ℕ → ℝ) {η C K W : ℝ} (hη : 0 < η) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (T : ℕ) (hgood : ∀ k, active k → good)
    (hmono : ∀ k j, k ≤ j → active j → active k)
    (hφ : ∀ y, 0 ≤ φ y) (hinit : good → φ (x 0) ≤ W)
    (hstep : ∀ k < T, active k → φ (x (k + 1)) ≤ φ (x k) - η * r k / 2 + η * C * v k)
    (hmove : ∀ k < T, active k → a k ≤ 2 * η ^ 2 * (r k + v k))
    (herr : ∀ k < T, (if active k then v k else 0) ≤ K ^ 2 * e k) :
    (∑ k ∈ Finset.range T, if active k then r k else 0) ≤
      2 * W / η + 2 * C * K ^ 2 * (∑ k ∈ Finset.range T, e k) ∧
    (∑ k ∈ Finset.range T, if active k then a k else 0) ≤
      4 * η * W + (4 * C + 2) * η ^ 2 * K ^ 2 * (∑ k ∈ Finset.range T, e k) := by
  have hf := frozen_masked_energy active good x φ r v η C T hgood hmono hstep
  have ht : 0 ≤ (if good then φ (freeze active x T) else 0) := by
    split_ifs <;> first | exact hφ _ | exact le_rfl
  have hi : (if good then φ (x 0) else 0) ≤ W := by
    split_ifs with hg
    · exact hinit hg
    · exact hW
  have he : η / 2 * (∑ k ∈ Finset.range T, if active k then r k else 0) ≤
      W + η * C * (∑ k ∈ Finset.range T, if active k then v k else 0) := by linarith
  have hv := Finset.sum_le_sum (s := Finset.range T) (fun k hk => herr k (Finset.mem_range.mp hk))
  rw [← Finset.mul_sum] at hv
  constructor
  · have hh := mul_le_mul_of_nonneg_left hv (show 0 ≤ η * C by positivity)
    have hw : (2 * W / η) * η = 2 * W := div_mul_cancel₀ _ hη.ne'
    apply (mul_le_mul_iff_left₀ hη).mp
    nlinarith only [he, hh, hw]
  · have hm : ∀ k < T, (if active k then a k else 0) ≤
        2 * η ^ 2 * ((if active k then r k else 0) + (if active k then v k else 0)) := by
      intro k hk
      split_ifs with ha
      · exact hmove k hk ha
      · simp
    have hs := Finset.sum_le_sum (s := Finset.range T) (fun k hk => hm k (Finset.mem_range.mp hk))
    simp_rw [mul_add] at hs
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 * η by positivity)
    have herror := mul_le_mul_of_nonneg_left hv (show 0 ≤ (4 * C + 2) * η ^ 2 by positivity)
    nlinarith only [hs, hscaled, herror]

open scoped Classical in
lemma trace_energy_bounds {Ω : Type*} (p : Public) (cfg : Config) {κ β K W fLower : ℝ}
    (hν : 0 < p.ν) (hLf : 0 ≤ p.Lf) (hLc : 0 ≤ p.Lc) (hLJ : 0 ≤ p.LJ)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 < cfg.step)
    (f : Point p.d → ℝ) (truth : Point p.d → Reply p)
    (hf : ∀ y, HasGradientAt f (truth y).1 y)
    (hc : ∀ y, HasFDerivAt (fun z => (truth z).2.1) (operatorEquiv p.d p.m (truth y).2.2).adjoint y)
    (hgL : ∀ y z, ‖(truth z).1 - (truth y).1‖ ≤ p.Lf * ‖z - y‖)
    (hJn : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hJL : ∀ y z, ‖(truth z).2.2 - (truth y).2.2‖ ≤ p.LJ * ‖z - y‖)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (hκ : (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ)
    (hβ : 8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β)
    (hηD : (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16)
    (hβ2 : 2 ≤ β) (hW : 0 ≤ W)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) +
      p.Lc + cfg.constraintCap ≤ K)
    (hφ : ∀ y, 0 ≤ StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower)
    (g : Point p.d → Ω → Reply p) (x : (ℕ → Ω) → Point p.d)
    (good : (ℕ → Ω) → Prop) (offset T : ℕ) (ξ : ℕ → Ω)
    (hinit : good ξ → StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β (x ξ) - fLower ≤ W) :
    (∑ k ∈ Finset.range T, if active p cfg truth
      (fun j z => (trainingTrace p cfg g z (x z) offset j).point) good k ξ then
        residual p truth β (trainingTrace p cfg g ξ (x ξ) offset k).point else 0) ≤
      2 * W / cfg.step + 2 * (β + 3) * K ^ 2 *
        (∑ k ∈ Finset.range T, stoppedError p cfg g truth x good offset k ξ) ∧
    (∑ k ∈ Finset.range T, stoppedMovement p cfg g truth x good offset k ξ) ≤
      4 * cfg.step * W + (4 * (β + 3) + 2) * cfg.step ^ 2 * K ^ 2 *
        (∑ k ∈ Finset.range T, stoppedError p cfg g truth x good offset k ξ) := by
  classical
  let path := fun k z => (trainingTrace p cfg g z (x z) offset k).point
  let Φ := fun y => StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
    (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower
  have h := frozen_error_bounds (fun k => active p cfg truth path good k ξ) (good ξ)
    (fun k => path k ξ) Φ (fun k => residual p truth β (path k ξ))
    (fun k => ‖traceDirectionError p cfg g truth (x ξ) offset k ξ‖ ^ 2)
    (fun k => stoppedError p cfg g truth x good offset k ξ)
    (fun k => ‖path (k + 1) ξ - path k ξ‖ ^ 2)
    hη (show 0 ≤ β + 3 by linarith) hW T
    (fun k hk => active_good p cfg truth path good k ξ hk)
    (fun k j hkj hj => active_mono p cfg truth path good hkj ξ hj) hφ hinit
    (fun k hk ha => by
      obtain ⟨hgc, hcc⟩ := active_caps p cfg truth path good k ξ ha
      have hd := trace_merit_descent p cfg hν hLf hLc hLJ hG hη.le f truth hf hc hgL hJn hJL hreg
        hκ hβ hηD g (x ξ) offset k ξ hgc hcc
      dsimp only [Φ, path]
      linarith only [hd])
    (fun k _ _ => trace_movement_residual p cfg hν hβ2 g truth hreg (x ξ) offset k ξ)
    (fun k _ => stopped_direction_error_le p cfg hν hLc hG hM g truth hreg x good offset k ξ hK)
  exact h

open scoped Classical in
lemma trace_no_exit {Ω : Type*} (p : Public) (cfg : Config) {κ β K W fLower : ℝ}
    (hν : 0 < p.ν) (hLf : 0 ≤ p.Lf) (hLc : 0 ≤ p.Lc) (hLJ : 0 ≤ p.LJ)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 < cfg.step)
    (f : Point p.d → ℝ) (truth : Point p.d → Reply p)
    (hf : ∀ y, HasGradientAt f (truth y).1 y)
    (hc : ∀ y, HasFDerivAt (fun z => (truth z).2.1) (operatorEquiv p.d p.m (truth y).2.2).adjoint y)
    (hgL : ∀ y z, ‖(truth z).1 - (truth y).1‖ ≤ p.Lf * ‖z - y‖)
    (hJn : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hJL : ∀ y z, ‖(truth z).2.2 - (truth y).2.2‖ ≤ p.LJ * ‖z - y‖)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (hκ : (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ)
    (hβ : 8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β)
    (hηD : (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16)
    (hβ2 : 2 ≤ β)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) +
      p.Lc + cfg.constraintCap ≤ K)
    (g : Point p.d → Ω → Reply p) (x : (ℕ → Ω) → Point p.d)
    (good : (ℕ → Ω) → Prop) (offset T : ℕ) (ξ : ℕ → Ω) (hg : good ξ)
    (hinit : StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β (x ξ) - fLower ≤ W - 1)
    (hcap0 : ‖(truth (x ξ)).1‖ ≤ cfg.gradientCap ∧ ‖(truth (x ξ)).2.1‖ ≤ cfg.constraintCap)
    (hguard : ∀ y, StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower ≤ 2 * W - 1 →
      ‖(truth y).1‖ ≤ cfg.gradientCap ∧ ‖(truth y).2.1‖ ≤ cfg.constraintCap)
    (hbudget : cfg.step * (β + 3) * K ^ 2 *
      (∑ k ∈ Finset.range T, stoppedError p cfg g truth x good offset k ξ) ≤ W) :
    ∀ n ≤ T, active p cfg truth (fun j z => (trainingTrace p cfg g z (x z) offset j).point) good n ξ := by
  classical
  let path := fun k z => (trainingTrace p cfg g z (x z) offset k).point
  let Φ := fun y => StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
    (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower
  apply active_of_frozen_upper p cfg truth path good Φ (2 * W - 1) T ξ hg hcap0 hguard
  intro n hn
  apply frozen_potential_upper (fun k => active p cfg truth path good k ξ)
    (fun k => path k ξ) Φ (fun k => residual p truth β (path k ξ))
    (fun k => ‖traceDirectionError p cfg g truth (x ξ) offset k ξ‖ ^ 2)
    (fun k => stoppedError p cfg g truth x good offset k ξ)
    hη.le (show 0 ≤ β + 3 by linarith only [hβ2]) T
    (fun k j hkj hj => active_mono p cfg truth path good hkj ξ hj) hinit
    (fun k => residual_nonneg p truth (by linarith only [hβ2]) (path k ξ))
    (fun k => stoppedError_nonneg p cfg g truth x good offset k ξ) ?_ ?_ hbudget n hn
  · intro k _ ha
    obtain ⟨hgc, hcc⟩ := active_caps p cfg truth path good k ξ ha
    have hd := trace_merit_descent p cfg hν hLf hLc hLJ hG hη.le f truth hf hc hgL hJn hJL hreg
      hκ hβ hηD g (x ξ) offset k ξ hgc hcc
    dsimp only [Φ, path]
    linarith only [hd]
  · intro k _
    exact stopped_direction_error_le p cfg hν hLc hG hM g truth hreg x good offset k ξ hK

open scoped Classical in
lemma expected_movement_energy {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P] {κ β K W fLower : ℝ}
    (hν : 0 < p.ν) (hLf : 0 ≤ p.Lf) (hLc : 0 ≤ p.Lc) (hLJ : 0 ≤ p.LJ)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 < cfg.step)
    (f : Point p.d → ℝ) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hf : ∀ y, HasGradientAt f (truth y).1 y)
    (hc : ∀ y, HasFDerivAt (fun z => (truth z).2.1) (operatorEquiv p.d p.m (truth y).2.2).adjoint y)
    (hgL : ∀ y z, ‖(truth z).1 - (truth y).1‖ ≤ p.Lf * ‖z - y‖)
    (hJn : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hJL : ∀ y z, ‖(truth z).2.2 - (truth y).2.2‖ ≤ p.LJ * ‖z - y‖)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (hκ : (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ)
    (hβ : 8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β)
    (hηD : (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16)
    (hβ2 : 2 ≤ β) (hW : 0 ≤ W)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) +
      p.Lc + cfg.constraintCap ≤ K)
    (hφ : ∀ y, 0 ≤ StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ)
    (hinit : ∀ ξ, good ξ → StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β (x ξ) - fLower ≤ W) :
    (∑ k ∈ Finset.range T, ∫ ξ, stoppedMovement p cfg g truth x good offset k ξ ∂P) ≤
      4 * cfg.step * W + (4 * (β + 3) + 2) * cfg.step ^ 2 * K ^ 2 *
        (∑ k ∈ Finset.range T, ∫ ξ, stoppedError p cfg g truth x good offset k ξ ∂P) := by
  have ha (k : ℕ) := integrable_stoppedMovement p cfg P hν hLc hG hM hη.le g hg truth ht x hx
    good hgood offset k
  have he (k : ℕ) := integrable_stoppedError p cfg P hG hM hLc g hg truth ht hJn x hx good hgood offset k
  have has := integrable_finsetSum (Finset.range T) (fun k _ => ha k)
  have hes := integrable_finsetSum (Finset.range T) (fun k _ => he k)
  have hb := integral_mono has ((integrable_const (4 * cfg.step * W)).add
    (hes.const_mul ((4 * (β + 3) + 2) * cfg.step ^ 2 * K ^ 2))) (fun ξ =>
      (trace_energy_bounds p cfg hν hLf hLc hLJ hG hM hη f truth hf hc hgL hJn hJL hreg
        hκ hβ hηD hβ2 hW hK hφ g x good offset T ξ (hinit ξ)).2)
  simp only [Pi.add_apply] at hb
  rw [integral_finsetSum _ (fun k _ => ha k),
    integral_add (integrable_const _) (hes.const_mul _),
    integral_const_mul ((4 * (β + 3) + 2) * cfg.step ^ 2 * K ^ 2),
    integral_finsetSum _ (fun k _ => he k)] at hb
  simpa using hb

open scoped Classical in
lemma expected_residual_energy {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P] {κ β K W fLower : ℝ}
    (hν : 0 < p.ν) (hLf : 0 ≤ p.Lf) (hLc : 0 ≤ p.Lc) (hLJ : 0 ≤ p.LJ)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 < cfg.step)
    (f : Point p.d → ℝ) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hf : ∀ y, HasGradientAt f (truth y).1 y)
    (hc : ∀ y, HasFDerivAt (fun z => (truth z).2.1) (operatorEquiv p.d p.m (truth y).2.2).adjoint y)
    (hgL : ∀ y z, ‖(truth z).1 - (truth y).1‖ ≤ p.Lf * ‖z - y‖)
    (hJn : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hJL : ∀ y z, ‖(truth z).2.2 - (truth y).2.2‖ ≤ p.LJ * ‖z - y‖)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (hκ : (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ)
    (hβ : 8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β)
    (hηD : (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16)
    (hβ2 : 2 ≤ β) (hW : 0 ≤ W)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) +
      p.Lc + cfg.constraintCap ≤ K)
    (hφ : ∀ y, 0 ≤ StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ)
    (hinit : ∀ ξ, good ξ → StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β (x ξ) - fLower ≤ W) :
    Integrable (fun ξ => ∑ k ∈ Finset.range T, stoppedResidual p cfg β g truth x good offset k ξ) P ∧
    (∫ ξ, ∑ k ∈ Finset.range T, stoppedResidual p cfg β g truth x good offset k ξ ∂P) ≤
      2 * W / cfg.step + 2 * (β + 3) * K ^ 2 *
        (∑ k ∈ Finset.range T, ∫ ξ, stoppedError p cfg g truth x good offset k ξ ∂P) := by
  have he (k : ℕ) := integrable_stoppedError p cfg P hG hM hLc g hg truth ht hJn x hx good hgood offset k
  have hes := integrable_finsetSum (Finset.range T) (fun k _ => he k)
  have hrm := Finset.measurable_sum (Finset.range T) (fun k _ =>
    measurable_stoppedResidual p cfg β g hg truth ht x hx good hgood offset k)
  have hrn (ξ : ℕ → Ω) : 0 ≤ ∑ k ∈ Finset.range T, stoppedResidual p cfg β g truth x good offset k ξ :=
    Finset.sum_nonneg (fun k _ => stoppedResidual_nonneg p cfg (by linarith) g truth x good offset k ξ)
  have hu := (integrable_const (2 * W / cfg.step)).add (hes.const_mul (2 * (β + 3) * K ^ 2))
  have hb (ξ : ℕ → Ω) : (∑ k ∈ Finset.range T, stoppedResidual p cfg β g truth x good offset k ξ) ≤
      2 * W / cfg.step + 2 * (β + 3) * K ^ 2 *
        (∑ k ∈ Finset.range T, stoppedError p cfg g truth x good offset k ξ) :=
    (trace_energy_bounds p cfg hν hLf hLc hLJ hG hM hη f truth hf hc hgL hJn hJL hreg
      hκ hβ hηD hβ2 hW hK hφ g x good offset T ξ (hinit ξ)).1
  have hri := hu.mono' hrm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hrn ξ)]
    exact hb ξ)
  refine ⟨hri, ?_⟩
  have hh := integral_mono hri hu hb
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (hes.const_mul _),
    integral_const_mul (2 * (β + 3) * K ^ 2), integral_finsetSum _ (fun k _ => he k)] at hh
  simpa using hh

lemma estimator_feedback {E A V t ρ η C K W : ℝ}
    (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hC : 0 ≤ C)
    (he : E ≤ t + ρ * A) (hv : V ≤ K ^ 2 * E)
    (ha : A ≤ 4 * η * W + (4 * C + 2) * η ^ 2 * V)
    (hsmall : ρ * (4 * C + 2) * η ^ 2 * K ^ 2 ≤ 1 / 2) :
    E ≤ 2 * t + 8 * ρ * η * W := by
  have h₁ := mul_le_mul_of_nonneg_left hv (show 0 ≤ (4 * C + 2) * η ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left ha hρ
  have h₃ := mul_le_mul_of_nonneg_left h₁ hρ
  have h₄ := mul_le_mul_of_nonneg_right hsmall hE
  nlinarith only [he, h₂, h₃, h₄]

open scoped Classical in
lemma expected_estimator_energy {Ω : Type} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] {κ β K W fLower : ℝ}
    (hν : 0 < p.ν) (hLf : 0 ≤ p.Lf) (hLc : 0 ≤ p.Lc) (hLJ : 0 ≤ p.LJ)
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hη : 0 < cfg.step)
    (f : Point p.d → ℝ) (truth : Point p.d → Reply p) (ht : Measurable truth)
    (hf : ∀ y, HasGradientAt f (truth y).1 y)
    (hc : ∀ y, HasFDerivAt (fun z => (truth z).2.1) (operatorEquiv p.d p.m (truth y).2.2).adjoint y)
    (hgL : ∀ y z, ‖(truth z).1 - (truth y).1‖ ≤ p.Lf * ‖z - y‖)
    (hJn : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (hJL : ∀ y z, ‖(truth z).2.2 - (truth y).2.2‖ ≤ p.LJ * ‖z - y‖)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (truth y).2.2))
    (hκ : (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ)
    (hβ : 8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β)
    (hηD : (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16)
    (hβ2 : 2 ≤ β) (hW : 0 ≤ W)
    (hK : (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) +
      p.Lc + cfg.constraintCap ≤ K)
    (hφ : ∀ y, 0 ≤ StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β y - fLower)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ)
    (hinit : ∀ ξ, good ξ → StochasticEqualityDescent.merit f (fun z => (truth z).2.1)
      (fun z => operatorEquiv p.d p.m (truth z).2.2) (fun z => (truth z).1) β (x ξ) - fLower ≤ W)
    (hi : ∀ y, Integrable (g y) P) (hmean : ∀ y, ∫ ω, g y ω ∂P = truth y)
    (hnoise2 : ∀ y, Integrable (fun ω => ‖pack p (g y ω) - pack p (truth y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ ω, ‖pack p (g y ω) - pack p (truth y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun ω => ‖pack p (g y ω) - pack p (g z ω)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ ω, ‖pack p (g y ω) - pack p (g z ω)‖ ^ 2 ∂P) ≤ p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (hsmall : ((cfg.epoch : ℝ) * p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ)) *
      (4 * (β + 3) + 2) * cfg.step ^ 2 * K ^ 2 ≤ 1 / 2) :
    (∑ k ∈ Finset.range T, ∫ ξ, stoppedError p cfg g truth x good offset k ξ
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      2 * (T * (p.σ ^ 2 / (cfg.resetBatch : ℝ))) +
        8 * ((cfg.epoch : ℝ) * p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ)) * cfg.step * W := by
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let E := ∑ k ∈ Finset.range T, ∫ ξ, stoppedError p cfg g truth x good offset k ξ ∂Q
  let A := ∑ k ∈ Finset.range T, ∫ ξ, stoppedMovement p cfg g truth x good offset k ξ ∂Q
  have he := estimator_error_energy p cfg P hν hLc hG hM hη.le g hg hi truth ht hJn hmean hdiff2 hdiff
    hnoise2 hnoise x hx good hgood offset T hdx hdgood
  have ha := expected_movement_energy p cfg Q hν hLf hLc hLJ hG hM hη f truth ht hf hc hgL hJn hJL hreg
    hκ hβ hηD hβ2 hW hK hφ g hg x hx good hgood offset T hinit
  have hn : 0 ≤ E := Finset.sum_nonneg (fun k _ =>
    integral_nonneg (stoppedError_nonneg p cfg g truth x good offset k))
  have ha' : A ≤ 4 * cfg.step * W + (4 * (β + 3) + 2) * cfg.step ^ 2 * (K ^ 2 * E) := by
    simpa only [mul_assoc] using ha
  exact estimator_feedback (E := E) (A := A) (V := K ^ 2 * E)
    hn (by positivity) (show 0 ≤ β + 3 by linarith) he le_rfl ha' hsmall

set_option maxHeartbeats 1000000 in
lemma admissible_no_exit {Ω : Type*} (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (fLower : ℝ) (hlow : ∀ y, fLower ≤ I.f y)
    (g : Point p.d → Ω → Reply p.toPublic) (x : (ℕ → Ω) → Point p.d)
    (good : (ℕ → Ω) → Prop) (offset T : ℕ) (ξ : ℕ → Ω) (hg : good ξ)
    (hgap : I.f (x ξ) - fLower ≤ 70000 * (StochasticEqualityTuning.scale p.toPublic) ^ 10)
    (hc0 : ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * (StochasticEqualityTuning.scale p.toPublic) ^ 7))
    (hbudget : (tuning p.toPublic).step * (2 * 10 ^ 10 * (StochasticEqualityTuning.scale p.toPublic) ^ 24) *
      (10 ^ 6 * (StochasticEqualityTuning.scale p.toPublic) ^ 11) ^ 2 *
      (∑ k ∈ Finset.range T, stoppedError p.toPublic (tuning p.toPublic) g
        (StochasticEqualityModel.truth I) x good offset k ξ) ≤ 10 ^ 6 * (StochasticEqualityTuning.scale p.toPublic) ^ 10) :
    ∀ n ≤ T, active p.toPublic (tuning p.toPublic) (StochasticEqualityModel.truth I)
      (fun j z => (trainingTrace p.toPublic (tuning p.toPublic) g z (x z) offset j).point) good n ξ := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let u := StochasticEqualityModel.truth I
  obtain ⟨hη, hG, hM, hκ, hK, hβ, hβ2, hηD, _, _⟩ := StochasticEqualityTuning.tuning_geometry p hp
  have hpCopy := hp
  obtain ⟨_, _, _, hν, hLf, hLc, hLJ, _, _, _, _, _, _⟩ := hpCopy
  have hi := StochasticEqualityRestoration.restored_initial_bounds p hp I O hI fLower hlow (x ξ) hgap hc0
  have hPhi (y : Point p.d) :
      StochasticEqualityDescent.merit I.f (fun z => (u z).2.1)
        (fun z => operatorEquiv p.d p.m (u z).2.2) (fun z => (u z).1) (10 ^ 10 * S ^ 24) y =
      StochasticEqualityDescent.merit I.f I.c (fun z => (fderiv ℝ I.c z).adjoint)
        (gradient I.f) (10 ^ 10 * S ^ 24) y := by
    simp only [u, StochasticEqualityModel.truth_operator]
    rfl
  have hC : 10 ^ 10 * S ^ 24 + 3 ≤ 2 * 10 ^ 10 * S ^ 24 := by
    have hs : 1 ≤ S := by
      have hh := (StochasticEqualityTuning.scale_bounds p hp).1
      dsimp [S]
      linarith only [hh]
    have hh : 1 ≤ S ^ 24 := one_le_pow₀ hs
    nlinarith only [hh]
  have he0 : 0 ≤ ∑ k ∈ Finset.range T, stoppedError p.toPublic cfg g u x good offset k ξ :=
    Finset.sum_nonneg (fun k _ => stoppedError_nonneg p.toPublic cfg g u x good offset k ξ)
  have hactual : cfg.step * (10 ^ 10 * S ^ 24 + 3) * (10 ^ 6 * S ^ 11) ^ 2 *
      (∑ k ∈ Finset.range T, stoppedError p.toPublic cfg g u x good offset k ξ) ≤ 10 ^ 6 * S ^ 10 := by
    have hh := mul_le_mul_of_nonneg_right hC (show 0 ≤ cfg.step * (10 ^ 6 * S ^ 11) ^ 2 *
      (∑ k ∈ Finset.range T, stoppedError p.toPublic cfg g u x good offset k ξ) by positivity)
    nlinarith only [hh, hbudget]
  apply trace_no_exit p.toPublic cfg (fLower := fLower) hν hLf hLc hLJ hG hM hη I.f u hI.1
    (StochasticEqualityModel.admissible_truth_derivative p I O hI)
    hI.2.2.2.2.1 hI.2.2.2.2.2.1 hI.2.2.2.2.2.2.1
    (StochasticEqualityModel.admissible_truth_regular p I O hI)
    hκ hβ hηD hβ2 hK g x good offset T ξ hg ?_ ⟨hi.1, hi.2.1⟩ ?_ hactual
  · rw [hPhi]
    exact hi.2.2
  · intro y hy
    rw [hPhi] at hy
    have hh := StochasticEqualityModel.admissible_sublevel_caps p hp I O hI fLower hlow y hy
    exact ⟨hh.1.le, hh.2.le⟩

lemma nonnegative_budget_failure {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    (F : Z → ℝ) (hi : Integrable F P) (hn : ∀ z, 0 ≤ F z) {W : ℝ} (hW : 0 < W)
    (hb : (∫ z, F z ∂P) ≤ W / 100) :
    P {z | W < F z} ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
  have hh := (hi.div_const W).measure_le_integral
    (Filter.Eventually.of_forall (fun z => div_nonneg (hn z) hW.le))
    (s := {z | W < F z}) (fun z hz => (one_le_div hW).mpr hz.le)
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  apply (div_le_iff₀ hW).mpr
  linarith only [hb]

lemma stopped_error_budget_failure {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (hG : 0 ≤ cfg.gradientCap) (hM : 0 ≤ cfg.constraintCap) (hL : 0 ≤ p.Lc)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p) (ht : Measurable truth) (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset T : ℕ)
    {A W : ℝ} (hA : 0 ≤ A) (hW : 0 < W)
    (hb : A * (∑ k ∈ Finset.range T, ∫ z, stoppedError p cfg g truth x good offset k z ∂P) ≤ W / 100) :
    P {z | W < A * (∑ k ∈ Finset.range T, stoppedError p cfg g truth x good offset k z)} ≤
      ENNReal.ofReal (1 / 100 : ℝ) := by
  have hi (k : ℕ) := integrable_stoppedError p cfg P hG hM hL g hg truth ht hJ x hx good hgood offset k
  have hs : Integrable (fun z => ∑ k ∈ Finset.range T, stoppedError p cfg g truth x good offset k z) P :=
    integrable_finsetSum _ (fun k _ => hi k)
  apply nonnegative_budget_failure P _ (hs.const_mul A)
    (fun z => mul_nonneg hA (Finset.sum_nonneg (fun k _ => stoppedError_nonneg p cfg g truth x good offset k z))) hW
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)]
  exact hb


lemma tuned_stopped_error_budget_failure {Ω : Type*} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (P : Measure (ℕ → Ω)) [IsFiniteMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (truth : Point p.d → Reply p.toPublic) (ht : Measurable truth)
    (hJ : ∀ y, ‖(truth y).2.2‖ ≤ p.Lc)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset : ℕ)
    (hE : (∑ k ∈ Finset.range (tuning p.toPublic).steps,
      ∫ z, stoppedError p.toPublic (tuning p.toPublic) g truth x good offset k z ∂P) ≤
      2 * (tuning p.toPublic).steps * (p.σ ^ 2 / (tuning p.toPublic).resetBatch) +
        8 * ((tuning p.toPublic).epoch * p.Lnoise ^ 2 / (tuning p.toPublic).incrementBatch) *
          (tuning p.toPublic).step * (10 ^ 6 * (StochasticEqualityTuning.scale p.toPublic) ^ 10)) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    P {z | 10 ^ 6 * S ^ 10 < cfg.step * (2 * 10 ^ 10 * S ^ 24) * (10 ^ 6 * S ^ 11) ^ 2 *
      (∑ k ∈ Finset.range cfg.steps, stoppedError p.toPublic cfg g truth x good offset k z)} ≤
      ENNReal.ofReal (1 / 100 : ℝ) := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let E := ∑ k ∈ Finset.range cfg.steps,
    ∫ z, stoppedError p.toPublic cfg g truth x good offset k z ∂P
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun k _ =>
    integral_nonneg (stoppedError_nonneg p.toPublic cfg g truth x good offset k))
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (StochasticEqualityTuning.scale_bounds p hp).1
  obtain ⟨hη, hG, hM, _⟩ := StochasticEqualityTuning.tuning_geometry p hp
  have hb := (StochasticEqualityTuning.tuning_energy_accuracy p hp E 0 hE0 hE (by positivity)).1
  exact stopped_error_budget_failure p.toPublic cfg P hG hM hp.2.2.2.2.2.1
    g hg truth ht hJ x hx good hgood offset cfg.steps (by positivity) (by positivity) hb

set_option maxHeartbeats 1000000 in
lemma admissible_expected_energy {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (fLower : ℝ) (hlow : ∀ y, fLower ≤ I.f y)
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset : ℕ)
    (hdx : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → x ξ = x ζ)
    (hdgood : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → (good ξ ↔ good ζ))
    (hgap : ∀ ξ, I.f (x ξ) - fLower ≤ 70000 * (StochasticEqualityTuning.scale p.toPublic) ^ 10)
    (hc0 : ∀ ξ, good ξ → ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * (StochasticEqualityTuning.scale p.toPublic) ^ 7)) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let E := ∑ k ∈ Finset.range cfg.steps,
      ∫ ξ, stoppedError p.toPublic cfg g (StochasticEqualityModel.truth I) x good offset k ξ ∂Q
    let R := fun ξ => ∑ k ∈ Finset.range cfg.steps,
      stoppedResidual p.toPublic cfg (10 ^ 10 * S ^ 24) g (StochasticEqualityModel.truth I) x good offset k ξ
    Integrable R Q ∧
      cfg.step * (2 * 10 ^ 10 * S ^ 24) * (10 ^ 6 * S ^ 11) ^ 2 * E ≤ (10 ^ 6 * S ^ 10) / 100 ∧
      (∫ ξ, R ξ ∂Q) / cfg.steps ≤ (p.ε / (32 * S)) ^ 2 / 100 := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let u := StochasticEqualityModel.truth I
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  obtain ⟨hη, hG, hM, hκ, hK, hβ, hβ2, hηD, _, hsmall⟩ := StochasticEqualityTuning.tuning_geometry p hp
  have hpCopy := hp
  obtain ⟨_, _, _, hν, hLf, hLc, hLJ, _, _, _, _, _, _⟩ := hpCopy
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (StochasticEqualityTuning.scale_bounds p hp).1
  have ht := StochasticEqualityModel.admissible_truth_measurable p hp I O hI
  have hder := StochasticEqualityModel.admissible_truth_derivative p I O hI
  have hreg := StochasticEqualityModel.admissible_truth_regular p I O hI
  have hPhi (y : Point p.d) :
      StochasticEqualityDescent.merit I.f (fun z => (u z).2.1)
        (fun z => operatorEquiv p.d p.m (u z).2.2) (fun z => (u z).1) (10 ^ 10 * S ^ 24) y =
      StochasticEqualityDescent.merit I.f I.c (fun z => (fderiv ℝ I.c z).adjoint)
        (gradient I.f) (10 ^ 10 * S ^ 24) y := by
    simp only [u, StochasticEqualityModel.truth_operator]
    rfl
  have hφ (y : Point p.d) : 0 ≤ StochasticEqualityDescent.merit I.f (fun z => (u z).2.1)
      (fun z => operatorEquiv p.d p.m (u z).2.2) (fun z => (u z).1) (10 ^ 10 * S ^ 24) y - fLower := by
    rw [hPhi]
    exact StochasticEqualityModel.admissible_merit_lower_of_lower p hp I O hI fLower hlow y
  have hinit (ξ : ℕ → Ω) (hh : good ξ) :
      StochasticEqualityDescent.merit I.f (fun z => (u z).2.1)
        (fun z => operatorEquiv p.d p.m (u z).2.2) (fun z => (u z).1) (10 ^ 10 * S ^ 24) (x ξ) -
          fLower ≤ 10 ^ 6 * S ^ 10 := by
    rw [hPhi]
    have hh := (StochasticEqualityRestoration.restored_initial_bounds p hp I O hI fLower hlow
      (x ξ) (hgap ξ) (hc0 ξ hh)).2.2
    linarith only [hh]
  have he := expected_estimator_energy p.toPublic cfg P hν hLf hLc hLJ hG hM hη I.f u ht hI.1 hder
    hI.2.2.2.2.1 hI.2.2.2.2.2.1 hI.2.2.2.2.2.2.1 hreg hκ hβ hηD hβ2
    (show 0 ≤ 10 ^ 6 * S ^ 10 by positivity) hK hφ g hg x hx good hgood offset cfg.steps hinit
    hi hmean hnoise2 hnoise hdiff2 hdiff hdx hdgood hsmall
  have hr := expected_residual_energy p.toPublic cfg Q hν hLf hLc hLJ hG hM hη I.f u ht hI.1 hder
    hI.2.2.2.2.1 hI.2.2.2.2.2.1 hI.2.2.2.2.2.2.1 hreg hκ hβ hηD hβ2
    (show 0 ≤ 10 ^ 6 * S ^ 10 by positivity) hK hφ g hg x hx good hgood offset cfg.steps hinit
  refine ⟨hr.1, ?_⟩
  apply StochasticEqualityTuning.tuning_energy_accuracy p hp _ _ ?_ ?_ hr.2
  · exact Finset.sum_nonneg (fun k _ => integral_nonneg
      (stoppedError_nonneg p.toPublic cfg g u x good offset k))
  · simpa only [mul_assoc] using he

lemma residual_controls_kkt (p : Public) (u : Point p.d → Reply p) {β : ℝ}
    (hν : 0 < p.ν) (hβ : 0 ≤ β) (hβν : 2 ≤ β * p.ν ^ 2)
    (hreg : ∀ y, regular p.ν (operatorEquiv p.d p.m (u y).2.2)) (y : Point p.d) :
    ‖tangent (operatorEquiv p.d p.m (u y).2.2) (u y).1‖ ^ 2 + ‖(u y).2.1‖ ^ 2 ≤
      residual p u β y := by
  have hh := hreg y (u y).2.1
  have hsq : (p.ν * ‖(u y).2.1‖) ^ 2 ≤ ‖operatorEquiv p.d p.m (u y).2.2 (u y).2.1‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hh
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ β / 2 by positivity)
  have hmul2 := mul_le_mul_of_nonneg_right hβν (sq_nonneg ‖(u y).2.1‖)
  unfold residual
  nlinarith only [hmul, hmul2]

lemma admissible_residual_controls_kkt (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (y : Point p.d) :
    ‖tangent ((fderiv ℝ I.c y).adjoint) (gradient I.f y)‖ ^ 2 + ‖I.c y‖ ^ 2 ≤
      residual p.toPublic (StochasticEqualityModel.truth I)
        (10 ^ 10 * (StochasticEqualityTuning.scale p.toPublic) ^ 24) y := by
  obtain ⟨_, _, _, _, _, _, hβ2, _, hcoerc, _⟩ := StochasticEqualityTuning.tuning_geometry p hp
  have hν := hp.2.2.2.1
  have hLf := hp.2.2.2.2.1
  have hβν : 2 ≤ (10 ^ 10 * (StochasticEqualityTuning.scale p.toPublic) ^ 24) * p.ν ^ 2 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hν)).mp hcoerc
    linarith only [hh, hLf]
  have hh := residual_controls_kkt p.toPublic (StochasticEqualityModel.truth I) hν (by linarith only [hβ2])
    hβν (StochasticEqualityModel.admissible_truth_regular p I O hI) y
  rw [StochasticEqualityModel.truth_operator] at hh
  exact hh

end LongTails.Proofs.StochasticEqualityEnergy
