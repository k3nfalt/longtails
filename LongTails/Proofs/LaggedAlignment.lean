import Mathlib.Tactic
import Mathlib.Probability.Moments.Basic
import LongTails.Proofs.RobustEnergyConcentration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace LongTails.Proofs.LaggedAlignment

open MeasureTheory

lemma integral_mul_of_conditional_bound {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ m₀)
    {X Y : Ω → ℝ} {c : ℝ} (hX : StronglyMeasurable[m] X)
    (hiX : Integrable X P) (hiY : Integrable Y P) (hiXY : Integrable (X * Y) P)
    (hzero : ∀ᵐ ω ∂P, 0 ≤ X ω) (hbound : ∀ᵐ ω ∂P, P[Y | m] ω ≤ c) :
    (∫ ω, X ω * Y ω ∂P) ≤ c * ∫ ω, X ω ∂P := by
  have hp := condExp_mul_of_stronglyMeasurable_left hX hiXY hiY
  have hc : ∀ᵐ ω ∂P, P[X * Y | m] ω ≤ c * X ω := by
    filter_upwards [hp, hzero, hbound] with ω hp hz hb
    simp only [Pi.mul_apply] at hp
    rw [hp]
    simpa only [mul_comm c] using mul_le_mul_of_nonneg_left hb hz
  have hh := integral_mono_ae integrable_condExp (hiX.const_mul c) hc
  rw [integral_condExp hm, integral_const_mul] at hh
  exact hh

lemma conditional_nonnegative_mgf {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ m₀)
    {Z : Ω → ℝ} (hZ : Measurable Z) {H μ : ℝ} (hH : 0 < H)
    (hzero : ∀ ω, 0 ≤ Z ω) (hbound : ∀ ω, Z ω ≤ H)
    (hmean : ∀ᵐ ω ∂P, P[Z | m] ω ≤ μ) :
    ∀ᵐ ω ∂P, P[fun u => Real.exp (Z u / H) | m] ω ≤ Real.exp (2 * μ / H) := by
  have hi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable H
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hzero ω)]
      exact hbound ω))
  have he : Integrable (fun ω => Real.exp (Z ω / H)) P :=
    Integrable.of_bound (hZ.div_const H).exp.aestronglyMeasurable (Real.exp 1)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, Real.abs_exp]
        exact Real.exp_le_exp.mpr ((div_le_one hH).mpr (hbound ω))))
  have hp (ω : Ω) : Real.exp (Z ω / H) ≤ 1 + (2 / H) * Z ω := by
    have hl : 0 ≤ Z ω / H := div_nonneg (hzero ω) hH.le
    have hu : Z ω / H ≤ 1 := (div_le_one hH).mpr (hbound ω)
    have hh := OracleTemplate.RobustGradient.exp_le_quadratic
      (show |Z ω / H| ≤ 1 by rwa [abs_of_nonneg hl])
    have hsq : (Z ω / H) ^ 2 ≤ Z ω / H := by nlinarith
    calc
      _ ≤ 1 + 2 * (Z ω / H) := by linarith
      _ = _ := by ring
  have hc := condExp_mono (m := m) he ((integrable_const 1).add (hi.const_mul (2 / H)))
    (Filter.Eventually.of_forall hp)
  have ha := condExp_add (μ := P) (integrable_const (1 : ℝ)) (hi.const_mul (2 / H)) m
  have hs := condExp_smul (μ := P) (2 / H) Z m
  filter_upwards [hc, ha, hs, hmean] with ω hc ha hs hmean
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at ha hs
  change P[fun u => (2 / H) * Z u | m] ω = (2 / H) * P[Z | m] ω at hs
  have hscale := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 / H by positivity)
  calc
    _ ≤ 1 + (2 / H) * P[Z | m] ω := by simpa only [ha, hs] using hc
    _ ≤ 1 + (2 / H) * μ := by linarith only [hscale]
    _ = 1 + 2 * μ / H := by ring
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (2 * μ / H)

lemma bounded_exp_sum_integrable {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ} {H : ℝ}
    (hH : 0 < H) (hZ : ∀ i, Measurable (Z i))
    (hbound : ∀ i ω, Z i ω ≤ H) (n : ℕ) :
    Integrable (fun ω => Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H)) P := by
  apply Integrable.of_bound
    ((Finset.measurable_sum _ (fun i _ => hZ i)).div_const H).exp.aestronglyMeasurable
    (Real.exp n)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hH).mpr
  simpa using Finset.sum_le_sum (s := Finset.range n) (fun i _ => hbound i ω)

lemma exp_sum_integral_le {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ m₀) {Z : ℕ → Ω → ℝ} {H μ : ℝ}
    (hH : 0 < H) (hZ : ∀ i, Measurable (Z i))
    (hzero : ∀ i ω, 0 ≤ Z i ω) (hbound : ∀ i ω, Z i ω ≤ H)
    (hpast : ∀ n, StronglyMeasurable[m n]
      (fun ω => Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H)))
    (hmean : ∀ n, ∀ᵐ ω ∂P, P[Z n | m n] ω ≤ μ) (n : ℕ) :
    (∫ ω, Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H) ∂P) ≤
      Real.exp (2 * μ * n / H) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : (fun ω => Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H)) *
        (fun ω => Real.exp (Z n ω / H)) =
        (fun ω => Real.exp ((∑ i ∈ Finset.range (n + 1), Z i ω) / H)) := by
      funext ω
      simp only [Pi.mul_apply, Finset.sum_range_succ, add_div, Real.exp_add]
    have hiY : Integrable (fun ω => Real.exp (Z n ω / H)) P := by
      apply Integrable.of_bound (hZ n |>.div_const H |>.exp.aestronglyMeasurable)
        (Real.exp 1)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_le_exp.mpr ((div_le_one hH).mpr (hbound n ω))
    have hiXY := bounded_exp_sum_integrable (P := P) hH hZ hbound (n + 1)
    rw [← hprod] at hiXY
    have hb := integral_mul_of_conditional_bound (hm n) (hpast n)
      (bounded_exp_sum_integrable hH hZ hbound n) hiY hiXY
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
      (conditional_nonnegative_mgf (hm n) (hZ n) hH (hzero n) (hbound n) (hmean n))
    change (∫ ω, ((fun ω => Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H)) *
      (fun ω => Real.exp (Z n ω / H))) ω ∂P) ≤ _ at hb
    rw [hprod] at hb
    calc
      _ ≤ Real.exp (2 * μ / H) *
          ∫ ω, Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H) ∂P := hb
      _ ≤ Real.exp (2 * μ / H) * Real.exp (2 * μ * n / H) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma sum_tail_le {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ m₀) {Z : ℕ → Ω → ℝ} {H μ : ℝ}
    (hH : 0 < H) (hZ : ∀ i, Measurable (Z i))
    (hzero : ∀ i ω, 0 ≤ Z i ω) (hbound : ∀ i ω, Z i ω ≤ H)
    (hpast : ∀ n, StronglyMeasurable[m n]
      (fun ω => Real.exp ((∑ i ∈ Finset.range n, Z i ω) / H)))
    (hmean : ∀ n, ∀ᵐ ω ∂P, P[Z n | m n] ω ≤ μ) (n : ℕ) (u : ℝ) :
    P.real {ω | 2 * μ * n + H * u ≤ ∑ i ∈ Finset.range n, Z i ω} ≤
      Real.exp (-u) := by
  have hi := bounded_exp_sum_integrable (P := P) hH hZ hbound n
  have hi' : Integrable (fun ω => Real.exp (H⁻¹ *
      (∑ i ∈ Finset.range n, Z i ω))) P := by
    simpa only [div_eq_mul_inv, mul_comm _ H⁻¹] using hi
  have hc := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (2 * μ * n + H * u) (inv_nonneg.mpr hH.le) hi'
  have he := exp_sum_integral_le hm hH hZ hzero hbound hpast hmean n
  have he' : ProbabilityTheory.mgf (fun ω => ∑ i ∈ Finset.range n, Z i ω) P H⁻¹ ≤
      Real.exp (2 * μ * n / H) := by
    simpa only [ProbabilityTheory.mgf, div_eq_mul_inv, mul_comm _ H⁻¹] using he
  calc
    _ ≤ Real.exp (-H⁻¹ * (2 * μ * n + H * u)) *
        ProbabilityTheory.mgf (fun ω => ∑ i ∈ Finset.range n, Z i ω) P H⁻¹ := hc
    _ ≤ Real.exp (-H⁻¹ * (2 * μ * n + H * u)) * Real.exp (2 * μ * n / H) :=
      mul_le_mul_of_nonneg_left he' (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp; ring

lemma finite_family_prefix_tail {Ω R : Type*} [Fintype R]
    {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {m : R → ℕ → MeasurableSpace Ω} (hm : ∀ r i, m r i ≤ m₀)
    {Z : R → ℕ → Ω → ℝ} {H μ : ℝ} (hH : 0 < H)
    (hZ : ∀ r i, Measurable (Z r i))
    (hzero : ∀ r i ω, 0 ≤ Z r i ω) (hbound : ∀ r i ω, Z r i ω ≤ H)
    (hpast : ∀ r n, StronglyMeasurable[m r n]
      (fun ω => Real.exp ((∑ i ∈ Finset.range n, Z r i ω) / H)))
    (hmean : ∀ r n, ∀ᵐ ω ∂P, P[Z r n | m r n] ω ≤ μ) (T : ℕ) (u : ℝ) :
    P.real {ω | ∃ r n, n ≤ T ∧
      2 * μ * n + H * u ≤ ∑ i ∈ Finset.range n, Z r i ω} ≤
      Fintype.card R * (T + 1) * Real.exp (-u) := by
  classical
  have heq : {ω | ∃ r n, n ≤ T ∧
      2 * μ * n + H * u ≤ ∑ i ∈ Finset.range n, Z r i ω} =
      ⋃ r : R, ⋃ n ∈ Finset.range (T + 1),
        {ω | 2 * μ * n + H * u ≤ ∑ i ∈ Finset.range n, Z r i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
  rw [heq]
  calc
    _ ≤ ∑ r : R, P.real (⋃ n ∈ Finset.range (T + 1),
        {ω | 2 * μ * n + H * u ≤ ∑ i ∈ Finset.range n, Z r i ω}) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ r : R, ∑ n ∈ Finset.range (T + 1),
        P.real {ω | 2 * μ * n + H * u ≤ ∑ i ∈ Finset.range n, Z r i ω} := by
      exact Finset.sum_le_sum (fun r _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _r : R, ∑ _n ∈ Finset.range (T + 1), Real.exp (-u) := by
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun n _ => sum_tail_le (hm r) hH (hZ r)
        (hzero r) (hbound r) (hpast r) (hmean r) n u)
    _ = _ := by simp; ring

lemma residue_sum (z : ℕ → ℝ) (K q : ℕ) :
    (∑ r ∈ Finset.range K, ∑ j ∈ Finset.range q, z (j * K + r)) =
      ∑ i ∈ Finset.range (q * K), z i := by
  induction q with
  | zero => simp
  | succ q ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, Nat.succ_mul, Finset.sum_range_add]

lemma prefix_bound_of_residues {z : ℕ → ℝ} {K n : ℕ} {μ b : ℝ}
    (hK : 0 < K) (hμ : 0 ≤ μ) (hz : ∀ i, 0 ≤ z i)
    (hb : ∀ r < K, (∑ j ∈ Finset.range (n / K + 1), z (j * K + r)) ≤
      μ * ((n / K + 1 : ℕ) : ℝ) + b) :
    (∑ i ∈ Finset.range n, z i) ≤ μ * (n + K) + K * b := by
  have hn : n ≤ (n / K + 1) * K := by
    have hh := Nat.mod_lt n hK
    have he := Nat.mod_add_div n K
    nlinarith
  have hn' : (n / K + 1) * K ≤ n + K := by
    have hh := Nat.div_mul_le_self n K
    nlinarith
  calc
    _ ≤ ∑ i ∈ Finset.range ((n / K + 1) * K), z i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun i _ _ => hz i)
    _ = ∑ r ∈ Finset.range K, ∑ j ∈ Finset.range (n / K + 1), z (j * K + r) :=
      (residue_sum z K (n / K + 1)).symm
    _ ≤ ∑ _r ∈ Finset.range K, (μ * ((n / K + 1 : ℕ) : ℝ) + b) :=
      Finset.sum_le_sum (fun r hr => hb r (Finset.mem_range.mp hr))
    _ = μ * (((n / K + 1) * K : ℕ) : ℝ) + K * b := by simp; ring
    _ ≤ _ := by
      have hc : (((n / K + 1) * K : ℕ) : ℝ) ≤ n + K := by exact_mod_cast hn'
      have hh := mul_le_mul_of_nonneg_left hc hμ
      linarith

lemma prefix_bound_with_warmup {w : ℕ → ℝ} {j T : ℕ} {μ H u : ℝ}
    (hj : 1 ≤ j) (hμ : 0 ≤ μ) (hH : 0 ≤ H) (hu : 0 ≤ u)
    (hw : ∀ i, 0 ≤ w i) (hbound : ∀ i < j, w i ≤ H)
    (hres : ∀ r < j + 1, ∀ N ≤ T,
      (∑ i ∈ Finset.range N, w (r + (j + 1) * i + j)) ≤ 2 * μ * N + H * u)
    {n : ℕ} (hn : n ≤ T) :
    (∑ i ∈ Finset.range n, w i) ≤
      2 * μ * n + (j + 1 : ℕ) * (2 * μ + H * (1 + u)) := by
  have hjR : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
  by_cases hnj : n ≤ j
  · have hb : (∑ i ∈ Finset.range n, w i) ≤ n * H := by
      simpa using Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => hbound i (lt_of_lt_of_le (Finset.mem_range.mp hi) hnj))
    have hnR : (n : ℝ) ≤ j := by exact_mod_cast hnj
    have hmul := mul_le_mul_of_nonneg_right (hnR.trans hjR) hH
    have hpos : 0 ≤ 2 * μ * n := by positivity
    have htail : 0 ≤ (j + 1 : ℕ) * (2 * μ + H * u) := by positivity
    nlinarith
  · have hjn : j ≤ n := by omega
    have hN : (n - j) / (j + 1) + 1 ≤ T := by
      have hh := Nat.div_le_self (n - j) (j + 1)
      omega
    have hp := prefix_bound_of_residues (z := fun i => w (i + j))
      (K := j + 1) (n := n - j) (μ := 2 * μ) (b := H * u)
      (by omega) (by positivity) (fun i => hw (i + j))
      (fun r hr => by
        simpa only [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          hres r hr ((n - j) / (j + 1) + 1) hN)
    have hb : (∑ i ∈ Finset.range j, w i) ≤ j * H := by
      simpa using Finset.sum_le_sum (s := Finset.range j)
        (fun i hi => hbound i (Finset.mem_range.mp hi))
    have he : n = j + (n - j) := by omega
    have hs : (∑ i ∈ Finset.range n, w i) =
        (∑ i ∈ Finset.range j, w i) + ∑ i ∈ Finset.range (n - j), w (i + j) := by
      conv_lhs => rw [he, Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_comm]
    rw [hs]
    have hc : ((n - j : ℕ) : ℝ) + j = n := by exact_mod_cast Nat.sub_add_cancel hjn
    have hmul := mul_le_mul_of_nonneg_right hjR hH
    have hnonneg : 0 ≤ 2 * μ * j := by positivity
    push_cast at hp ⊢
    nlinarith

lemma alignment_deficit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g m : E →L[ℝ] ℝ) (v : E) (hv : ‖v‖ ≤ 1) (hm : m v = ‖m‖) :
    0 ≤ ‖g‖ - g v ∧ ‖g‖ - g v ≤ 2 * ‖g‖ ∧
      ‖g‖ - g v ≤ 2 * ‖m - g‖ := by
  have hg : |g v| ≤ ‖g‖ := by
    calc
      _ = ‖g v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖g‖ * ‖v‖ := g.le_opNorm v
      _ ≤ ‖g‖ := by nlinarith [norm_nonneg g]
  have he : |(m - g) v| ≤ ‖m - g‖ := by
    calc
      _ = ‖(m - g) v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖m - g‖ * ‖v‖ := (m - g).le_opNorm v
      _ ≤ ‖m - g‖ := by nlinarith [norm_nonneg (m - g)]
  have hn : ‖g‖ - ‖m‖ ≤ ‖m - g‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le g m
  have he' := (abs_le.mp he).2
  simp only [sub_apply, hm] at he'
  exact ⟨by linarith [(abs_le.mp hg).2], by linarith [(abs_le.mp hg).1], by linarith⟩

lemma descent_sum {f g z : ℕ → ℝ} {η c : ℝ} {n : ℕ}
    (hstep : ∀ i < n, f (i + 1) ≤ f i - η * g i + η * z i + c) :
    f n + η * ∑ i ∈ Finset.range n, g i ≤
      f 0 + η * ∑ i ∈ Finset.range n, z i + n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hn := hstep n (Nat.lt_succ_self n)
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma stopped_sublevel {f g z w : ℕ → ℝ} {η c Δ μ b : ℝ} {T : ℕ}
    (hη : 0 ≤ η)
    (hg : ∀ i < T, 0 ≤ g i)
    (hstep : ∀ i < T, f (i + 1) ≤ f i - η * g i + η * z i + c)
    (hstop : ∀ i < T, (∀ j ≤ i, f j ≤ f 0 + Δ) → z i = w i)
    (hconcentration : ∀ n ≤ T, (∑ i ∈ Finset.range n, w i) ≤ μ * n + b)
    (hmargin : ∀ n ≤ T, η * (μ * n + b) + n * c ≤ Δ) :
    ∀ n ≤ T, f n ≤ f 0 + Δ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have heq : (∑ i ∈ Finset.range n, z i) = ∑ i ∈ Finset.range n, w i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin := Finset.mem_range.mp hi
      exact hstop i (lt_of_lt_of_le hin hn)
        (fun j hji => ih j (lt_of_le_of_lt hji hin) (le_trans hji (le_trans hin.le hn)))
    have hd := descent_sum (fun i hi => hstep i (lt_of_lt_of_le hi hn))
    have hgSum : 0 ≤ η * ∑ i ∈ Finset.range n, g i := by
      apply mul_nonneg hη
      exact Finset.sum_nonneg (fun i hi => hg i (lt_of_lt_of_le (Finset.mem_range.mp hi) hn))
    rw [heq] at hd
    have hc := mul_le_mul_of_nonneg_left (hconcentration n hn) hη
    have hm := hmargin n hn
    linarith

lemma average_from_descent {f g z : ℕ → ℝ} {η c Δ μ b lower : ℝ} {T : ℕ}
    (hη : 0 ≤ η)
    (hstep : ∀ i < T, f (i + 1) ≤ f i - η * g i + η * z i + c)
    (hlower : lower ≤ f T) (hgap : f 0 - lower ≤ Δ)
    (hconcentration : (∑ i ∈ Finset.range T, z i) ≤ μ * T + b) :
    η * ∑ i ∈ Finset.range T, g i ≤ Δ + η * (μ * T + b) + T * c := by
  have hd := descent_sum hstep
  have hc := mul_le_mul_of_nonneg_left hconcentration hη
  linarith

lemma self_bound {L g gap : ℝ} (hL : 0 < L)
    (hdescent : ∀ t : ℝ, 0 ≤ t → t * g - L / 2 * t ^ 2 ≤ gap)
    (hg : 0 ≤ g) :
    g ^ 2 ≤ 2 * L * gap := by
  have h := hdescent (g / L) (div_nonneg hg hL.le)
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg L)
  field_simp at h'
  nlinarith [sq_pos_of_pos hL]

end LongTails.Proofs.LaggedAlignment
