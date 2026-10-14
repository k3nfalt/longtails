import LongTails.Proofs.ScalarProfile
import LongTails.Proofs.ScalarConditional
import LongTails.Proofs.ScalarExecution

open MeasureTheory

namespace OracleTemplate.BoundedScalarConvex

open LongTails.Setups.BoundedScalarConvex

open ScalarStopLoss

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit mΩ in
lemma measurable_profile {m : MeasurableSpace Ω} {F : ℝ → ℝ} (hF : Continuous F)
    {b v Z : Ω → ℝ} (hb : Measurable[m] b) (hv : Measurable[m] v)
    (hZ : Measurable[m] Z) (h H : ℝ) :
    Measurable[m] (fun ω => profile F (b ω) (v ω) h H (Z ω)) := by
  unfold profile
  exact (measurable_const.max ((hF.measurable.comp (hb.add (hZ.const_mul h))).sub hv)).div_const _

lemma profile_le_coordinate {F : ℝ → ℝ} {b v h H z : ℝ}
    (hh : 0 < h) (hH : 0 < H) (hb : F b ≤ v)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|) (hz : 0 ≤ z) :
    profile F b v h H z ≤ z := by
  have ht := profile_lipschitz (b := b) (v := v) hh hH hL z 0
  rw [profile_zero hb, sub_zero, sub_zero, abs_of_nonneg hz] at ht
  exact (le_abs_self _).trans ht

lemma conditional_profile_bound (m : ℕ → MeasurableSpace Ω) (hm : Monotone m)
    (hambient : ∀ n, m n ≤ mΩ) {F : ℝ → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    {h H : ℝ} (hh : 0 < h) (hH : 0 < H)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|)
    (b v : Ω → ℝ) (hb : Measurable[m 0] b) (hv : Measurable[m 0] v)
    (hbv : ∀ ω, F (b ω) ≤ v ω)
    (Z : ℕ → Ω → ℝ) (N : ℕ)
    (hZ : ∀ n, Measurable[m n] (Z n)) (hZi : ∀ n, Integrable (Z n) μ)
    (hZpos : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ Z n ω) (hZ0 : Z 0 =ᵐ[μ] 0)
    (hZn : ∀ n ≤ N, ∀ᵐ ω ∂μ, Z n ω ≤ n)
    (hjump : ∀ n < N, ∀ᵐ ω ∂μ, |Z (n+1) ω-Z n ω| ≤ 1)
    (hmean : ∀ n < N, ∀ k : ℕ, 2 ≤ k → ∀ᵐ ω ∂μ,
      (k : ℝ)-1 ≤ Z n ω → μ[Z (n+1)-Z n | m n] ω ≤
        -(profile F (b ω) (v ω) h H ((k-2 : ℕ)+1)-
          profile F (b ω) (v ω) h H (k-2 : ℕ))) :
    μ[fun ω => profile F (b ω) (v ω) h H (Z N ω) | m 0] ≤ᵐ[μ] fun _ => 6 := by
  let d : ℕ → Ω → ℝ := fun j ω => profile F (b ω) (v ω) h H (j+1)-
    profile F (b ω) (v ω) h H j
  have hd : ∀ j, Measurable[m 0] (d j) := fun j =>
    (measurable_profile hFc hb hv measurable_const h H).sub
      (measurable_profile hFc hb hv measurable_const h H)
  have hdB : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ d j ω ∧ d j ω ≤ 1 := fun j =>
    Filter.Eventually.of_forall (fun ω => profile_grid_bounds hF hh hH (hbv ω) hL j)
  have hdmono : ∀ᵐ ω ∂μ, Monotone (fun j => d j ω) :=
    Filter.Eventually.of_forall (fun ω => profile_grid_mono hF hh hH)
  have hHinge := conditional_finite_envelope (mΩ := mΩ) (μ := μ) m hm hambient Z d N
    hZ hZi hZ0 hZn hjump hd hdB hmean
  have hbase := measurable_profile hFc hb hv (measurable_const (a := (2 : ℝ))) h H
  have hbasei : Integrable (fun ω => profile F (b ω) (v ω) h H 2) μ := by
    apply Integrable.of_bound (hbase.mono (hambient 0) le_rfl).aestronglyMeasurable 2
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg hh hH)]
    exact profile_two hh hH (hbv ω) hL
  have hscorem := measurable_profile hFc (hb.mono (hambient 0) le_rfl)
    (hv.mono (hambient 0) le_rfl) ((hZ N).mono (hambient N) le_rfl) h H
  have hscorei : Integrable (fun ω => profile F (b ω) (v ω) h H (Z N ω)) μ := by
    apply (hZi N).mono' hscorem.aestronglyMeasurable
    filter_upwards [hZpos N] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg hh hH)]
    exact profile_le_coordinate hh hH (hbv ω) hL hω
  apply conditional_objective_of_hinges (mΩ := mΩ) (μ := μ) (hambient 0) d (Z N)
    (fun ω => profile F (b ω) (v ω) h H 2)
    (fun ω => profile F (b ω) (v ω) h H (Z N ω)) N hd hdB hdmono hbase hbasei
    (Filter.Eventually.of_forall (fun ω => profile_two hh hH (hbv ω) hL))
    (hZi N) hscorei ?_ hHinge
  filter_upwards [hZpos N, hZn N le_rfl] with ω hz hn
  have hp := polygon_majorizes (profile_convex hF hh hH)
    (profile_monotone hF hh hH (hbv ω)) N (Z N ω) hz (by linarith)
  rw [polygon_sum] at hp
  dsimp [d]
  norm_num only [Nat.cast_zero, Nat.cast_ofNat, zero_add] at hp
  simp only [Nat.cast_add, Nat.cast_ofNat, add_assoc] at hp ⊢
  norm_num at hp ⊢
  linarith

lemma conditional_excursion_drift {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {l u η H : ℝ} (hlu : l ≤ u) (hη : 0 < η) (hH : 0 < H)
    (X X' Y v : Ω → ℝ) (hX : Measurable[m] X) (hv : Measurable[m] v)
    (hXi : Integrable X μ) (hX'i : Integrable X' μ) (hYi : Integrable Y μ)
    (hXm : ∀ ω, X ω ∈ Set.Icc l u)
    (hY : ∀ᵐ ω ∂μ, |Y ω| ≤ H)
    (hstep : ∀ᵐ ω ∂μ, X' ω = project l u (X ω-η*Y ω))
    (hsub : ∀ᵐ ω ∂μ, ∀ y, F (X ω)+μ[Y | m] ω*(y-X ω) ≤ F y)
    (k : ℕ) (hk : 2 ≤ k) :
    let b := fun ω => rightEndpoint F l u (v ω)
    let Z := fun ω => max 0 (X ω-b ω)/(η*H)
    let Z' := fun ω => max 0 (X' ω-b ω)/(η*H)
    ∀ᵐ ω ∂μ, (k : ℝ)-1 ≤ Z ω → μ[Z'-Z | m] ω ≤
      -(profile F (b ω) (v ω) (η*H) H ((k-2 : ℕ)+1)-
        profile F (b ω) (v ω) (η*H) H (k-2 : ℕ)) := by
  dsimp only
  let b := fun ω => rightEndpoint F l u (v ω)
  let Z := fun ω => max 0 (X ω-b ω)/(η*H)
  let Z' := fun ω => max 0 (X' ω-b ω)/(η*H)
  have hb : Measurable[m] b := (rightEndpoint_measurable hlu).comp hv
  have hbi : Integrable b μ := by
    apply Integrable.of_bound (hb.mono hm le_rfl).aestronglyMeasurable (|l|+|u|)
    filter_upwards [] with ω
    have hbmem := rightEndpoint_mem (f := F) hlu (v ω)
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [hbmem.1, hbmem.2, le_abs_self l, neg_abs_le l, le_abs_self u, neg_abs_le u]
  have hZi : Integrable Z μ := ((integrable_const (0 : ℝ)).sup (hXi.sub hbi)).div_const _
  have hZ'i : Integrable Z' μ := ((integrable_const (0 : ℝ)).sup (hX'i.sub hbi)).div_const _
  have hZm : Measurable[m] Z := (measurable_const.max (hX.sub hb)).div_const _
  let E : Set Ω := {ω | (k : ℝ)-1 ≤ Z ω}
  have hE : MeasurableSet[m] E := measurableSet_le measurable_const hZm
  have hpoint : ∀ᵐ ω ∂μ, ω ∈ E → (Z'-Z) ω ≤ -Y ω/H := by
    filter_upwards [hY, hstep] with ω hYω hstepω hω
    change Z' ω-Z ω ≤ -Y ω/H
    dsimp [Z', Z]
    rw [hstepω]
    apply excursion_step_drift (hXm ω) (rightEndpoint_mem hlu (v ω)) hη hH hYω
    change (k : ℝ)-1 ≤ Z ω at hω
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcond := conditional_mono_on (mΩ := mΩ) (μ := μ) hm hE (hZ'i.sub hZi)
    (hYi.neg.div_const H) hpoint
  have hscale : μ[fun ω => -Y ω/H | m] =ᵐ[μ] fun ω => -μ[Y | m] ω/H := by
    have hs := condExp_smul (μ := μ) (-H⁻¹) Y m
    change μ[fun ω => (-H⁻¹)*Y ω | m] =ᵐ[μ] fun ω => (-H⁻¹)*μ[Y | m] ω at hs
    have heq : (fun ω => (-H⁻¹)*Y ω) = (fun ω => -Y ω/H) := by
      funext ω
      simp only [div_eq_mul_inv]
      ring
    rw [heq] at hs
    filter_upwards [hs] with ω hsω
    rw [hsω]
    simp only [div_eq_mul_inv]
    ring
  filter_upwards [hcond, hscale, hsub] with ω hc he hs hω
  have hkpos : 0 < (k : ℝ)-1 := by
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hx := excursion_threshold (mul_pos hη hH) hkpos hω
  have hxb : b ω < X ω := by
    have hp := mul_pos (mul_pos hη hH) hkpos
    dsimp [b] at hx ⊢
    linarith
  have hsec := profile_secant_support (b := b ω) hF (mul_pos hη hH) hH
    (rightEndpoint_strict hlu (hXm ω) hxb).le hs (k-2) (by
      rw [Nat.cast_sub hk, Nat.cast_ofNat]
      change b ω+η*H*((k : ℝ)-2+1) ≤ X ω
      dsimp [b]
      nlinarith)
  have hbound := hc hω
  change μ[Z'-Z | m] ω ≤ μ[fun ω => -Y ω/H | m] ω at hbound
  rw [he] at hbound
  change μ[Z'-Z | m] ω ≤ _
  dsimp [b] at hsec
  calc
    _ ≤ -μ[Y | m] ω/H := hbound
    _ = -(μ[Y | m] ω/H) := by ring
    _ ≤ _ := neg_le_neg hsec

lemma integrable_interval {X : Ω → ℝ} (hX : Measurable X) {l u : ℝ}
    (hXm : ∀ ω, X ω ∈ Set.Icc l u) : Integrable X μ := by
  apply Integrable.of_bound hX.aestronglyMeasurable (|l|+|u|)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [(hXm ω).1, (hXm ω).2, le_abs_self l, neg_abs_le l,
    le_abs_self u, neg_abs_le u]

lemma conditional_right_profile (m : ℕ → MeasurableSpace Ω) (hm : Monotone m)
    (hambient : ∀ n, m n ≤ mΩ) {F : ℝ → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    {l u η H : ℝ} (hlu : l ≤ u) (hη : 0 < η) (hH : 0 < H)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|)
    (X Y : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[m n] (X n))
    (hXm : ∀ n ω, X n ω ∈ Set.Icc l u)
    (hYi : ∀ n, Integrable (Y n) μ)
    (hY : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ H)
    (hstep : ∀ n, ∀ᵐ ω ∂μ, X (n+1) ω = project l u (X n ω-η*Y n ω))
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ∀ y, F (X n ω)+μ[Y n | m n] ω*(y-X n ω) ≤ F y)
    (N : ℕ) :
    let b := fun ω => rightEndpoint F l u (F (X 0 ω))
    μ[fun ω => profile F (b ω) (F (X 0 ω)) (η*H) H
      (max 0 (X N ω-b ω)/(η*H)) | m 0] ≤ᵐ[μ] fun _ => 6 := by
  dsimp only
  let v := fun ω => F (X 0 ω)
  let b := fun ω => rightEndpoint F l u (v ω)
  let Z := fun n ω => max 0 (X n ω-b ω)/(η*H)
  have hv : Measurable[m 0] v := hFc.measurable.comp (hX 0)
  have hb : Measurable[m 0] b := (rightEndpoint_measurable hlu).comp hv
  have hbmem : ∀ ω, b ω ∈ Set.Icc l u := fun ω => rightEndpoint_mem hlu (v ω)
  have hbv : ∀ ω, F (b ω) ≤ v ω := fun ω =>
    rightEndpoint_sublevel hFc ⟨X 0 ω, hXm 0 ω, le_rfl⟩
  have hbi : Integrable b μ := integrable_interval (hb.mono (hambient 0) le_rfl) hbmem
  have hXi : ∀ n, Integrable (X n) μ := fun n =>
    integrable_interval ((hX n).mono (hambient n) le_rfl) (hXm n)
  have hZm : ∀ n, Measurable[m n] (Z n) := fun n =>
    (measurable_const.max ((hX n).sub (hb.mono (hm (Nat.zero_le n)) le_rfl))).div_const _
  have hZi : ∀ n, Integrable (Z n) μ := fun n =>
    ((integrable_const (0 : ℝ)).sup ((hXi n).sub hbi)).div_const _
  have hZ0 : ∀ ω, Z 0 ω = 0 := by
    intro ω
    have hx : X 0 ω ≤ b ω := le_rightEndpoint hlu (hXm 0 ω) le_rfl
    simp [Z, max_eq_left (sub_nonpos.mpr hx)]
  have hjump : ∀ n, ∀ᵐ ω ∂μ, |Z (n+1) ω-Z n ω| ≤ 1 := by
    intro n
    filter_upwards [hY n, hstep n] with ω hYω hSω
    dsimp [Z]
    rw [hSω]
    exact excursion_step_distance (hXm n ω) hη hH hYω
  have hZn : ∀ n, ∀ᵐ ω ∂μ, Z n ω ≤ n := by
    intro n
    induction n with
    | zero => exact Filter.Eventually.of_forall (fun ω => by rw [hZ0 ω]; norm_num)
    | succ n ih =>
      filter_upwards [ih, hjump n] with ω hn hj
      have hu := (abs_le.mp hj).2
      push_cast
      linarith
  apply conditional_profile_bound (mΩ := mΩ) (μ := μ) m hm hambient hF hFc
    (mul_pos hη hH) hH hL b v hb hv hbv Z N hZm hZi
    (fun n => Filter.Eventually.of_forall (fun ω => div_nonneg (le_max_left _ _) (by positivity)))
    (Filter.Eventually.of_forall hZ0) (fun n _ => hZn n) (fun n _ => hjump n)
  intro n _ k hk
  exact conditional_excursion_drift (mΩ := mΩ) (μ := μ) (hambient n) hF hlu hη hH
    (X n) (X (n+1)) (Y n) v (hX n) (hv.mono (hm (Nat.zero_le n)) le_rfl)
    (hXi n) (hXi (n+1)) (hYi n) (hXm n) (hY n) (hstep n) (hsub n) k hk

end OracleTemplate.BoundedScalarConvex
