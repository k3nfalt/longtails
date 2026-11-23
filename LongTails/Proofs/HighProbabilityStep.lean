import LongTails.Proofs.HighProbabilityEstimator
import LongTails.Proofs.AdaptivePilotConfidence
import LongTails.Proofs.WeakGradientConvolution

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HighProbabilityStep

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient
open LongTails.Proofs.HighProbabilityPilot LongTails.Proofs.HighProbabilityEstimator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma far_prob {V : Ω → E} {u : E}
    (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p) {σ s : ℝ} (hs : 0 < s)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) :
    p.real {ω | s < ‖V ω - u‖} ≤ σ ^ 2 / s ^ 2 := by
  have hsub : {ω | s < ‖V ω - u‖} ⊆ {ω | s ^ 2 ≤ ‖V ω - u‖ ^ 2} := by
    intro ω hω
    exact pow_le_pow_left₀ hs.le (le_of_lt hω) 2
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := p)
    (Filter.Eventually.of_forall fun ω => sq_nonneg ‖V ω - u‖) hvi (s ^ 2)
  have h1 : p.real {ω | s < ‖V ω - u‖} ≤ p.real {ω | s ^ 2 ≤ ‖V ω - u‖ ^ 2} :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma pilot_tail {V : Ω → E} (hV : Measurable V) {u : E}
    (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p) {σ S s B : ℝ} {K mp : ℕ}
    (hσS : σ ≤ S) (hσ0 : 0 ≤ σ) (hS : 0 < S) (hSs : S ≤ s) (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2)
    (hs : B ≤ 12 * s) (hK : 6 * s ≤ 2 ^ K * B) :
    (Measure.pi fun _ : Fin mp => p) {a | 5 * s < ‖gradedPilot B K (fun i => V (a i)) 0 - u‖} ≤
      ENNReal.ofReal ((2 * S / s) ^ mp) := by
  classical
  have hspos : 0 < s := lt_of_lt_of_le hS hSs
  let A : Set Ω := {ω | s < ‖V ω - u‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((hV.sub_const u).norm)
  have hpA : p.real A ≤ (S / s) ^ 2 := by
    have h := far_prob hvi hspos hvar
    exact h.trans (le_of_le_of_eq (div_le_div_of_nonneg_right (pow_le_pow_left₀ hσ0 hσS 2)
      (by positivity)) (div_pow _ _ 2).symm)
  have hθ : 0 < (S / s) ^ 2 := by positivity
  have hθ1 : (S / s) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hS.le hSs 2
  have hmaj := majority_failure_probability_le hA hθ hθ1 hpA mp
  have hsq : Real.sqrt ((S / s) ^ 2) = S / s := Real.sqrt_sq (by positivity)
  rw [hsq] at hmaj
  have hmul : 2 * (S / s) = 2 * S / s := by ring
  rw [hmul] at hmaj
  refine le_trans (measure_mono ?_) hmaj
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  by_contra hcon
  push Not at hcon
  have hgood : mp < 2 * (Finset.univ.filter (fun i => ‖V (a i) - u‖ ≤ s)).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin mp))) (fun i => a i ∈ A)
    have hneg : (Finset.univ.filter (fun i => ¬ a i ∈ A)) =
        Finset.univ.filter (fun i => ‖V (a i) - u‖ ≤ s) := by
      ext i
      simp [A, not_lt]
    rw [hneg, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  have hclose := gradedPilot_close (fun i => V (a i)) u 0 hs hK hgood
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma pilot_ok_fail {V : Ω → E} (hV : Measurable V) {u : E}
    (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p) {σ S B : ℝ} {K mp : ℕ}
    (hσS : σ ≤ S) (hσ0 : 0 ≤ σ) (hS : 0 < S) (hSB : 6 * S ≤ B)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) :
    (Measure.pi fun _ : Fin mp => p) {a | B / 2 < ‖gradedPilot B K (fun i => V (a i)) 0 - u‖} ≤
      ENNReal.ofReal ((12 * S / B) ^ mp) := by
  classical
  have hB : 0 < B := by linarith
  let s := B / 6
  have hspos : 0 < s := by positivity
  have hSs : S ≤ s := by simp only [s]; linarith
  let A : Set Ω := {ω | s < ‖V ω - u‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((hV.sub_const u).norm)
  have hpA : p.real A ≤ (S / s) ^ 2 := by
    have h := far_prob hvi hspos hvar
    exact h.trans (le_of_le_of_eq (div_le_div_of_nonneg_right (pow_le_pow_left₀ hσ0 hσS 2)
      (by positivity)) (div_pow _ _ 2).symm)
  have hθ : 0 < (S / s) ^ 2 := by positivity
  have hθ1 : (S / s) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hS.le hSs 2
  have hmaj := majority_failure_probability_le hA hθ hθ1 hpA mp
  have hsq : Real.sqrt ((S / s) ^ 2) = S / s := Real.sqrt_sq (by positivity)
  rw [hsq] at hmaj
  have hmul : 2 * (S / s) = 12 * S / B := by simp only [s]; field_simp; ring
  rw [hmul] at hmaj
  refine le_trans (measure_mono ?_) hmaj
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  by_contra hcon
  push Not at hcon
  have hgood : mp < 2 * (Finset.univ.filter (fun i => ‖V (a i) - u‖ ≤ B / 6)).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin mp))) (fun i => a i ∈ A)
    have hneg : (Finset.univ.filter (fun i => ¬ a i ∈ A)) =
        Finset.univ.filter (fun i => ‖V (a i) - u‖ ≤ B / 6) := by
      ext i
      simp [A, s, not_lt]
    rw [hneg, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  have hclose := gradedPilot_ok (K := K) (fun i => V (a i)) u 0 hgood
  linarith

lemma exp_tail_sum (N : ℕ) (x a0 a1 : ℝ) (ha1 : 0 < a1) (hxN : x ≤ a0 + a1 * (N + 1)) :
    Real.exp (x / (2 * a1)) ≤ Real.exp ((a0 + a1) / (2 * a1)) +
      ∑ k ∈ Finset.range N, Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) *
        Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) x := by
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range N, Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) *
      Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) x :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Real.exp_pos _).le
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  by_cases hsmall : x ≤ a0 + a1
  · have : Real.exp (x / (2 * a1)) ≤ Real.exp ((a0 + a1) / (2 * a1)) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsmall (by positivity))
    linarith
  · push Not at hsmall
    set k := ⌈(x - a0) / a1⌉₊ - 2 with hk
    have hceil := Nat.le_ceil ((x - a0) / a1)
    have hceil2 := Nat.ceil_lt_add_one (show 0 ≤ (x - a0) / a1 by
      apply div_nonneg (by linarith) ha1.le)
    have hgt : 1 < (x - a0) / a1 := by rw [lt_div_iff₀ ha1]; linarith
    have hc2 : 2 ≤ ⌈(x - a0) / a1⌉₊ := by
      have : (1 : ℝ) < ⌈(x - a0) / a1⌉₊ := lt_of_lt_of_le hgt hceil
      exact_mod_cast (show (1 : ℕ) < ⌈(x - a0) / a1⌉₊ by exact_mod_cast this)
    have hkcast : (k : ℝ) + 2 = ⌈(x - a0) / a1⌉₊ := by
      rw [hk]; push_cast [Nat.cast_sub hc2]; ring
    have hlow : a0 + a1 * (k + 1) < x := by
      have : (k : ℝ) + 1 < (x - a0) / a1 := by linarith
      rw [lt_div_iff₀ ha1] at this
      linarith
    have hup : x ≤ a0 + a1 * (k + 2) := by
      have : (x - a0) / a1 ≤ (k : ℝ) + 2 := by rw [hkcast]; exact hceil
      rw [div_le_iff₀ ha1] at this
      linarith
    have hkN : k < N := by
      have : (k : ℝ) + 1 < N + 1 := by
        have h1 : a0 + a1 * (k + 1) < a0 + a1 * (N + 1) := lt_of_lt_of_le hlow hxN
        have h2 : a1 * (k + 1) < a1 * (N + 1) := by linarith
        exact lt_of_mul_lt_mul_left h2 ha1.le
      exact_mod_cast (show (k : ℝ) < N by linarith)
    have hterm : Real.exp (x / (2 * a1)) ≤ Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) *
        Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) x := by
      rw [Set.indicator_of_mem (show x ∈ {y : ℝ | a0 + a1 * (k + 1) < y} from hlow), mul_one]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hup (by positivity))
    have hsingle := Finset.single_le_sum (f := fun k : ℕ => Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) *
        Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) x)
      (fun j _ => mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      (s := Finset.range N) (Finset.mem_range.mpr hkN)
    have : 0 < Real.exp ((a0 + a1) / (2 * a1)) := Real.exp_pos _
    linarith

lemma mgf_of_tail {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {X : α → ℝ} (hX : Measurable X) {M a0 a1 : ℝ} (hM : ∀ ω, X ω ≤ M)
    (ha0 : 0 ≤ a0) (ha1 : 0 < a1)
    (htail : ∀ k : ℕ, μ.real {ω | a0 + a1 * (k + 1) < X ω} ≤ 2 * Real.exp (-(k + 1))) :
    Integrable (fun ω => Real.exp (X ω / (2 * a1))) μ ∧
      (∫ ω, Real.exp (X ω / (2 * a1)) ∂μ) ≤ 5 * Real.exp ((a0 + a1) / (2 * a1)) := by
  set N := ⌈M / a1⌉₊ with hN
  have hMbound : ∀ ω, X ω ≤ a0 + a1 * (N + 1) := by
    intro ω
    have h1 := Nat.le_ceil (M / a1)
    rw [div_le_iff₀ ha1] at h1
    nlinarith [hM ω]
  have hint : Integrable (fun ω => Real.exp (X ω / (2 * a1))) μ := by
    refine Integrable.of_bound (hX.div_const _).exp.aestronglyMeasurable
      (Real.exp ((a0 + a1 * (N + 1)) / (2 * a1))) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hMbound ω) (by positivity))
  refine ⟨hint, ?_⟩
  let G : α → ℝ := fun ω => Real.exp ((a0 + a1) / (2 * a1)) +
    ∑ k ∈ Finset.range N, Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) *
      Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) (X ω)
  have hset (k : ℕ) : MeasurableSet {ω | a0 + a1 * (k + 1) < X ω} :=
    measurableSet_lt measurable_const hX
  have hind (k : ℕ) : Integrable (fun ω => Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y}
      (fun _ => (1 : ℝ)) (X ω)) μ := by
    have he : (fun ω => Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) (X ω)) =
        Set.indicator {ω | a0 + a1 * (k + 1) < X ω} (fun _ => (1 : ℝ)) := by
      funext ω; simp [Set.indicator]
    rw [he]
    exact (integrable_const 1).indicator (hset k)
  have hGi : Integrable G μ :=
    (integrable_const _).add (integrable_finsetSum _ fun k _ => (hind k).const_mul _)
  have hle : ∀ ω, Real.exp (X ω / (2 * a1)) ≤ G ω :=
    fun ω => exp_tail_sum N (X ω) a0 a1 ha1 (hMbound ω)
  have hstep := integral_mono hint hGi hle
  refine hstep.trans ?_
  simp only [G]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ => (hind k).const_mul _),
    integral_const, probReal_univ, one_smul, integral_finsetSum _ fun k _ => (hind k).const_mul _]
  have hterm (k : ℕ) : ∫ ω, Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) *
      Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) (X ω) ∂μ ≤
      Real.exp ((a0 + a1) / (2 * a1)) * (2 * Real.exp (-((k : ℝ) + 1) / 2)) := by
    rw [integral_const_mul]
    have he : (fun ω => Set.indicator {y : ℝ | a0 + a1 * (k + 1) < y} (fun _ => (1 : ℝ)) (X ω)) =
        fun ω => Set.indicator {ω | a0 + a1 * (k + 1) < X ω} (fun _ => (1 : ℝ)) ω := by
      funext ω; simp [Set.indicator]
    rw [he, integral_indicator_const (1 : ℝ) (hset k), smul_eq_mul, mul_one]
    have hexp : Real.exp ((a0 + a1 * (k + 2)) / (2 * a1)) =
        Real.exp ((a0 + a1) / (2 * a1)) * Real.exp (((k : ℝ) + 1) / 2) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hexp]
    have ht := htail k
    have hpos : 0 ≤ Real.exp ((a0 + a1) / (2 * a1)) * Real.exp (((k : ℝ) + 1) / 2) := by positivity
    calc Real.exp ((a0 + a1) / (2 * a1)) * Real.exp (((k : ℝ) + 1) / 2) *
          μ.real {ω | a0 + a1 * (k + 1) < X ω} ≤
        Real.exp ((a0 + a1) / (2 * a1)) * Real.exp (((k : ℝ) + 1) / 2) *
          (2 * Real.exp (-((k : ℝ) + 1))) := mul_le_mul_of_nonneg_left ht hpos
      _ = Real.exp ((a0 + a1) / (2 * a1)) * (2 * Real.exp (-((k : ℝ) + 1) / 2)) := by
          rw [mul_assoc, mul_left_comm (Real.exp _) 2, ← Real.exp_add]
          congr 3; ring
  have hgeo : ∑ k ∈ Finset.range N, 2 * Real.exp (-((k : ℝ) + 1) / 2) ≤ 4 := by
    set r := Real.exp (-(1 : ℝ) / 2) with hr
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr23 : r ≤ 2 / 3 := by
      have h1 : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
        have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
      have h2 : r * Real.exp (1 / 2) = 1 := by
        rw [hr, ← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have hpow (k : ℕ) : Real.exp (-((k : ℝ) + 1) / 2) = r ^ (k + 1) := by
      rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsum : ∑ k ∈ Finset.range N, r ^ k ≤ 1 / (1 - r) := by
      have hgeom := geom_sum_eq (show r ≠ 1 by linarith) N
      have e : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring
      rw [hgeom, e]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 N]) (by linarith)
    calc ∑ k ∈ Finset.range N, 2 * Real.exp (-((k : ℝ) + 1) / 2) =
          2 * r * ∑ k ∈ Finset.range N, r ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hpow, pow_succ]; ring
      _ ≤ 2 * r * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 4 := by
          have h1r : 0 < 1 - r := by linarith
          rw [mul_one_div, div_le_iff₀ h1r]
          linarith
  have hsumterm := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) => hterm k
  rw [← Finset.mul_sum] at hsumterm
  have hc : 0 < Real.exp ((a0 + a1) / (2 * a1)) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left hgeo hc.le]

noncomputable def pilotOf (B : ℝ) (K mp mc : ℕ) (V : Ω → E) (z : Fin (mp + mc) → Ω) : E :=
  gradedPilot B K (fun i : Fin mp => V (z (Fin.castAdd mc i))) 0

noncomputable def estimateOf (B : ℝ) (K mp mc : ℕ) (V : Ω → E) (z : Fin (mp + mc) → Ω) : E :=
  clipEstimate B K mp mc (fun i => V (z i))

noncomputable def okError (B : ℝ) (K mp mc : ℕ) (V : Ω → E) (u : E) (z : Fin (mp + mc) → Ω) : ℝ := by
  classical
  exact if ‖pilotOf B K mp mc V z - u‖ ≤ B / 2 then ‖estimateOf B K mp mc V z - u‖ else 0

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_pilotOf (B : ℝ) (K mp mc : ℕ) {V : Ω → E} (hV : Measurable V) :
    Measurable (pilotOf B K mp mc V) := by
  unfold pilotOf
  exact (measurable_gradedPilot (m := mp) B K 0).comp
    (Measurable.of_eval fun i => hV.comp (measurable_pi_apply _))

omit [CompleteSpace E] in
lemma measurable_estimateOf (B : ℝ) (K mp mc : ℕ) {V : Ω → E} (hV : Measurable V) :
    Measurable (estimateOf B K mp mc V) := by
  have hc := measurable_pilotOf B K mp mc hV
  have he : estimateOf B K mp mc V = fun z => pilotOf B K mp mc V z +
      (1 / (mc : ℝ)) • ∑ i : Fin mc, clip B (V (z (Fin.natAdd mp i)) - pilotOf B K mp mc V z) := by
    funext z; rfl
  rw [he]
  refine hc.add (Measurable.const_smul ?_ _)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_clip B).comp ((hV.comp (measurable_pi_apply _)).sub hc)

omit [CompleteSpace E] in
lemma measurable_okError (B : ℝ) (K mp mc : ℕ) {V : Ω → E} (hV : Measurable V) (u : E) :
    Measurable (okError B K mp mc V u) := by
  classical
  unfold okError
  exact Measurable.ite (measurableSet_le ((measurable_pilotOf B K mp mc hV).sub_const u).norm
    measurable_const) ((measurable_estimateOf B K mp mc hV).sub_const u).norm measurable_const

lemma block_prefix {mp mc : ℕ} (F : (Fin (mp + mc) → Ω) → ℝ) (hF : Measurable F) :
    ∫ z, F z ∂(Measure.pi fun _ : Fin (mp + mc) => p) =
      ∫ ξ, F (fun i => ξ i) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  have h := OracleTemplate.StochasticGeneralized.prefix_preserving p (mp + mc)
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hF.aestronglyMeasurable]

lemma block_ok_mgf {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) {u : E}
    (hmean : ∫ ω, V ω ∂p = u) (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p)
    {σ B : ℝ} (hσ : 0 ≤ σ) (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) (hB : 0 < B)
    {K mp mc : ℕ} (hmc : 0 < mc) :
    let a0 := clipRadius σ B mc 0 / mc
    let a1 := 12 * B / mc
    Integrable (fun z => Real.exp (okError B K mp mc V u z / (2 * a1)))
        (Measure.pi fun _ : Fin (mp + mc) => p) ∧
      (∫ z, Real.exp (okError B K mp mc V u z / (2 * a1))
        ∂(Measure.pi fun _ : Fin (mp + mc) => p)) ≤ 5 * Real.exp ((a0 + a1) / (2 * a1)) := by
  classical
  intro a0 a1
  have hmcpos : (0 : ℝ) < mc := by exact_mod_cast hmc
  have ha1 : 0 < a1 := by positivity
  have ha0 : 0 ≤ a0 := by
    simp only [a0, clipRadius]
    have : 0 ≤ 3 * Real.sqrt mc * σ + 12 * B * (1 + 0) + 22 * mc * σ ^ 2 / B := by positivity
    positivity
  have hthr (ell : ℝ) : clipRadius σ B mc ell / mc = a0 + a1 * ell := by
    simp only [a0, a1, clipRadius]
    field_simp
    ring
  let H : (Fin mp → Ω) × (ℕ → Ω) → ℝ := fun w =>
    Real.exp (okError B K mp mc V u (fun i => if h : (i : ℕ) < mp then w.1 ⟨i, h⟩
      else w.2 ((i : ℕ) - mp)) / (2 * a1))
  have hjoin : Measurable (fun w : (Fin mp → Ω) × (ℕ → Ω) => fun i : Fin (mp + mc) =>
      if h : (i : ℕ) < mp then w.1 ⟨i, h⟩ else w.2 ((i : ℕ) - mp)) := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : (i : ℕ) < mp
    · simp only [h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_snd
  have hH : Measurable H :=
    (((measurable_okError B K mp mc hV u).comp hjoin).div_const _).exp
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving
    p mp
  have hcomp : (fun ξ : ℕ → Ω => Real.exp (okError B K mp mc V u (fun i => ξ i) / (2 * a1))) =
      H ∘ (OracleTemplate.StochasticGeneralized.splitStream mp) := by
    funext ξ
    simp only [H, Function.comp_apply]
    congr 3
    funext i
    by_cases h : (i : ℕ) < mp
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte]
      show ξ i = ξ (mp + ((i : ℕ) - mp))
      congr 1
      omega
  have hfiber : ∀ a : Fin mp → Ω, Integrable (fun τ => H (a, τ)) (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ τ, H (a, τ) ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ 5 * Real.exp ((a0 + a1) / (2 * a1)) := by
    intro a
    set c := gradedPilot B K (fun i => V (a i)) 0 with hc
    have hpilot : ∀ τ : ℕ → Ω, pilotOf B K mp mc V (fun i : Fin (mp + mc) =>
        if h : (i : ℕ) < mp then (a, τ).1 ⟨i, h⟩ else (a, τ).2 ((i : ℕ) - mp)) = c := by
      intro τ
      simp only [pilotOf, hc]
      congr 1
      funext i
      simp [Fin.castAdd, i.isLt]
    have hest : ∀ τ : ℕ → Ω, estimateOf B K mp mc V (fun i : Fin (mp + mc) =>
        if h : (i : ℕ) < mp then (a, τ).1 ⟨i, h⟩ else (a, τ).2 ((i : ℕ) - mp)) =
        clipMean B c mc (fun j => V (τ j)) := by
      intro τ
      rw [estimateOf, clipEstimate_eq]
      have := hpilot τ
      simp only [pilotOf] at this
      rw [this]
      congr 1
      funext j
      simp [Fin.natAdd]
    by_cases hok : ‖c - u‖ ≤ B / 2
    · have hX : Measurable (fun τ : ℕ → Ω => ‖clipMean B c mc (fun j => V (τ j)) - u‖) := by
        have : Measurable (fun τ : ℕ → Ω => clipMean B c mc (fun j => V (τ j))) := by
          unfold clipMean
          refine measurable_const.add (Measurable.const_smul ?_ _)
          exact Finset.measurable_sum _ fun i _ =>
            (measurable_clip B).comp ((hV.comp (measurable_pi_apply _)).sub_const c)
        exact (this.sub_const u).norm
      have hM : ∀ τ : ℕ → Ω, ‖clipMean B c mc (fun j => V (τ j)) - u‖ ≤ 3 * B / 2 := by
        intro τ
        have h1 := clipMean_sub_center hB.le c hmc (fun j => V (τ j))
        have h2 : ‖clipMean B c mc (fun j => V (τ j)) - u‖ ≤
            ‖clipMean B c mc (fun j => V (τ j)) - c‖ + ‖c - u‖ := by
          have := norm_add_le (clipMean B c mc (fun j => V (τ j)) - c) (c - u)
          simpa only [sub_add_sub_cancel] using this
        linarith
      have htail : ∀ k : ℕ, (Measure.infinitePi fun _ : ℕ => p).real
          {τ | a0 + a1 * (k + 1) < ‖clipMean B c mc (fun j => V (τ j)) - u‖} ≤
            2 * Real.exp (-(k + 1)) := by
        intro k
        have h := clip_tail hV hVi hmean hvi hσ hvar hB (by rw [norm_sub_rev]; exact hok) hmc
          (ell := (k : ℝ) + 1) (by positivity)
        rw [hthr] at h
        exact h
      have hmgf := mgf_of_tail hX hM ha0 ha1 htail
      have hHeq : (fun τ => H (a, τ)) =
          fun τ => Real.exp (‖clipMean B c mc (fun j => V (τ j)) - u‖ / (2 * a1)) := by
        funext τ
        simp only [H, okError, hpilot τ, hok, ↓reduceIte, hest τ]
      rw [hHeq]
      exact hmgf
    · have hHeq : (fun τ => H (a, τ)) = fun _ => 1 := by
        funext τ
        simp only [H, okError, hpilot τ, hok, ↓reduceIte, zero_div, Real.exp_zero]
      rw [hHeq]
      refine ⟨integrable_const 1, ?_⟩
      simp only [integral_const, probReal_univ, one_smul]
      have : 1 ≤ Real.exp ((a0 + a1) / (2 * a1)) := Real.one_le_exp (by positivity)
      linarith
  have hbound := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := Measure.pi fun _ : Fin mp => p) (Q := Measure.infinitePi fun _ : ℕ => p)
    hH.stronglyMeasurable (fun w => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun a => (hfiber a).1)
    (integrable_const (5 * Real.exp ((a0 + a1) / (2 * a1))))
    (Filter.Eventually.of_forall fun a => (hfiber a).2)
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving p (mp + mc)
  have hFm : Measurable (fun z : Fin (mp + mc) → Ω => Real.exp (okError B K mp mc V u z / (2 * a1))) :=
    ((measurable_okError B K mp mc hV u).div_const _).exp
  have hi : Integrable (fun ξ : ℕ → Ω => Real.exp (okError B K mp mc V u (fun i => ξ i) / (2 * a1)))
      (Measure.infinitePi fun _ : ℕ => p) := by
    rw [hcomp]
    exact hsplit.integrable_comp_of_integrable hbound.1
  refine ⟨?_, ?_⟩
  · rw [← hpre.map_eq]
    exact (integrable_map_measure hFm.aestronglyMeasurable hpre.measurable.aemeasurable).mpr hi
  · rw [block_prefix _ hFm]
    rw [hcomp, Function.comp_def, hsplit.integral_comp' H]
    refine hbound.2.trans ?_
    simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma block_pilot_measure {B : ℝ} {K mp mc : ℕ} {V : Ω → E} (hV : Measurable V) (u : E) (t : ℝ) :
    (Measure.pi fun _ : Fin (mp + mc) => p) {z | t < ‖pilotOf B K mp mc V z - u‖} =
      (Measure.pi fun _ : Fin mp => p) {a | t < ‖gradedPilot B K (fun i => V (a i)) 0 - u‖} := by
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving p (mp + mc)
  have hpre' := OracleTemplate.StochasticGeneralized.prefix_preserving p mp
  have hS : MeasurableSet {z : Fin (mp + mc) → Ω | t < ‖pilotOf B K mp mc V z - u‖} :=
    measurableSet_lt measurable_const ((measurable_pilotOf B K mp mc hV).sub_const u).norm
  have hS' : MeasurableSet {a : Fin mp → Ω | t < ‖gradedPilot B K (fun i => V (a i)) 0 - u‖} :=
    measurableSet_lt measurable_const
      (((measurable_gradedPilot (m := mp) B K 0).comp
        (Measurable.of_eval fun i => hV.comp (measurable_pi_apply _))).sub_const u).norm
  rw [← hpre.map_eq, Measure.map_apply hpre.measurable hS, ← hpre'.map_eq,
    Measure.map_apply hpre'.measurable hS']
  rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma block_scale {V : Ω → E} (hV : Measurable V) {u : E}
    (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p) {σ S t B : ℝ} {K mp mc : ℕ}
    (hσS : σ ≤ S) (hσ0 : 0 ≤ σ) (hS : 0 < S) (hSt : 5 * S ≤ t)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) (ht : 5 * B ≤ 12 * t) (hK : 6 * t ≤ 5 * (2 ^ K * B)) :
    (Measure.pi fun _ : Fin (mp + mc) => p) {z | t < ‖pilotOf B K mp mc V z - u‖} ≤
      ENNReal.ofReal ((10 * S / t) ^ mp) := by
  rw [block_pilot_measure hV u t]
  have h := pilot_tail (mp := mp) hV hvi hσS hσ0 hS (s := t / 5) (by linarith) hvar
    (by linarith) (by linarith) (K := K) (B := B)
  have he : 5 * (t / 5) = t := by ring
  have he2 : 2 * S / (t / 5) = 10 * S / t := by
    have : 0 < t := by linarith
    field_simp; ring
  rw [he, he2] at h
  exact h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma block_ok_fail {V : Ω → E} (hV : Measurable V) {u : E}
    (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p) {σ S B : ℝ} {K mp mc : ℕ}
    (hσS : σ ≤ S) (hσ0 : 0 ≤ σ) (hS : 0 < S) (hSB : 6 * S ≤ B)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) :
    (Measure.pi fun _ : Fin (mp + mc) => p) {z | B / 2 < ‖pilotOf B K mp mc V z - u‖} ≤
      ENNReal.ofReal ((12 * S / B) ^ mp) := by
  rw [block_pilot_measure hV u (B / 2)]
  exact pilot_ok_fail hV hvi hσS hσ0 hS hSB hvar

end LongTails.Proofs.HighProbabilityStep
