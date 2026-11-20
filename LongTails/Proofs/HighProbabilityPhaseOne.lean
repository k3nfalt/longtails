import LongTails.Proofs.HighProbabilityStep
import LongTails.Proofs.HighProbabilityDescent
import LongTails.Proofs.HighProbabilityExecution

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityPhaseOne

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient
open LongTails.Proofs.HighProbabilityPilot LongTails.Proofs.HighProbabilityEstimator
open LongTails.Proofs.HighProbabilityStep LongTails.Proofs.HighProbabilityAdapted
open LongTails.Proofs.HighProbabilityExecution LongTails.Proofs.HighProbabilityDescent

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma estimate_center {B : ℝ} (hB : 0 ≤ B) (K mp : ℕ) {mc : ℕ} (hmc : 0 < mc) (V : Ω → E)
    (z : Fin (mp + mc) → Ω) :
    ‖estimateOf B K mp mc V z - pilotOf B K mp mc V z‖ ≤ B :=
  clipMean_sub_center hB _ hmc _

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma okError_nonneg (B : ℝ) (K mp mc : ℕ) (V : Ω → E) (u : E) (z : Fin (mp + mc) → Ω) :
    0 ≤ okError B K mp mc V u z := by
  unfold okError
  split_ifs <;> simp

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma error_split {B Gcap : ℝ} (hB : 0 < B) {K mp mc J : ℕ} (hmc : 0 < mc)
    (hJ : Gcap ≤ 4 * (2 ^ J * B)) (V : Ω → E) (u : E) (hu : ‖u‖ ≤ Gcap)
    (z : Fin (mp + mc) → Ω) :
    2 * min ‖estimateOf B K mp mc V z - u‖ ‖u‖ ≤
      2 * okError B K mp mc V u z + ∑ j ∈ Finset.range (J + 1),
        8 * (2 ^ j * B) * Set.indicator {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc V z - u‖}
          (fun _ => (1 : ℝ)) z := by
  classical
  set e := ‖pilotOf B K mp mc V z - u‖ with he
  have hok := okError_nonneg B K mp mc V u z
  have hterm (j : ℕ) (hj : j ≤ J) (hlt : 2 ^ j * B / 2 < e) :
      8 * (2 ^ j * B) ≤ ∑ j ∈ Finset.range (J + 1),
        8 * (2 ^ j * B) * Set.indicator {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc V z - u‖}
          (fun _ => (1 : ℝ)) z := by
    have hmem : j ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum (f := fun j => 8 * (2 ^ j * B) *
        Set.indicator {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc V z - u‖} (fun _ => (1 : ℝ)) z)
      (fun i _ => mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      hmem
    have hind : Set.indicator {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc V z - u‖}
        (fun _ => (1 : ℝ)) z = 1 := Set.indicator_of_mem (show z ∈ {z | 2 ^ j * B / 2 <
          ‖pilotOf B K mp mc V z - u‖} from hlt) _
    simp only [hind, mul_one] at h
    exact h
  have hsum : 0 ≤ ∑ j ∈ Finset.range (J + 1),
      8 * (2 ^ j * B) * Set.indicator {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc V z - u‖}
        (fun _ => (1 : ℝ)) z :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hmin1 := min_le_left ‖estimateOf B K mp mc V z - u‖ ‖u‖
  have hmin2 := min_le_right ‖estimateOf B K mp mc V z - u‖ ‖u‖
  by_cases h0 : e ≤ B / 2
  · have hokeq : okError B K mp mc V u z = ‖estimateOf B K mp mc V z - u‖ := by
      unfold okError
      rw [ite_eq_left h0]
    rw [hokeq]
    linarith
  · push Not at h0
    have hcen := estimate_center hB.le K mp hmc V z
    have htri : ‖estimateOf B K mp mc V z - u‖ ≤ B + e := by
      calc ‖estimateOf B K mp mc V z - u‖ = ‖(estimateOf B K mp mc V z - pilotOf B K mp mc V z) +
            (pilotOf B K mp mc V z - u)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ B + e := by linarith
    by_cases hJe : e ≤ 2 ^ J * B
    · have hex : ∃ j, e ≤ 2 ^ j * B := ⟨J, hJe⟩
      have hj : e ≤ 2 ^ Nat.find hex * B := Nat.find_spec hex
      have hjJ : Nat.find hex ≤ J := Nat.find_min' hex hJe
      have hlt : 2 ^ Nat.find hex * B / 2 < e := by
        by_cases hj0 : Nat.find hex = 0
        · rw [hj0]; simpa using h0
        · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
          push Not at hmin
          have hp : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [hp]
          linarith
      have h1 : (1 : ℝ) ≤ 2 ^ Nat.find hex := one_le_pow₀ (by norm_num)
      have hB1 : B ≤ 2 ^ Nat.find hex * B := by nlinarith
      have := hterm _ hjJ hlt
      nlinarith
    · push Not at hJe
      have hlt : 2 ^ J * B / 2 < e := by
        have : 0 < 2 ^ J * B := by positivity
        linarith
      have := hterm J le_rfl hlt
      linarith

omit [CompleteSpace E] in
lemma measurable_clipEstimate (B : ℝ) (K mp mc : ℕ) :
    Measurable (clipEstimate (E := E) B K mp mc) := by
  have hc : Measurable (fun v : Fin (mp + mc) → E =>
      gradedPilot B K (fun i : Fin mp => v (Fin.castAdd mc i)) 0) :=
    (measurable_gradedPilot (m := mp) B K 0).comp
      (Measurable.of_eval fun i => measurable_pi_apply _)
  have he : clipEstimate (E := E) B K mp mc = fun v =>
      gradedPilot B K (fun i : Fin mp => v (Fin.castAdd mc i)) 0 + (1 / (mc : ℝ)) •
        ∑ i : Fin mc, clip B (v (Fin.natAdd mp i) -
          gradedPilot B K (fun i : Fin mp => v (Fin.castAdd mc i)) 0) := by
    funext v; rfl
  rw [he]
  refine hc.add (Measurable.const_smul ?_ _)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_clip B).comp ((measurable_pi_apply _).sub hc)

lemma measurable_normalizedStep (η : ℝ) :
    Measurable (fun w : E × E => normalizedStep η w.1 w.2) := by
  classical
  unfold normalizedStep
  refine Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_fst ?_
  exact measurable_fst.sub ((measurable_const.div measurable_snd.norm).smul measurable_snd)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma measurable_samples {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun w : E × (Fin n → Ω) => fun i => g w.1 (w.2 i)) :=
  Measurable.of_eval fun i =>
    hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_stepMap (B η : ℝ) (K mp mc : ℕ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (stepMap B η K mp mc g)) := by
  have h := (measurable_normalizedStep (E := E) η).comp (measurable_fst.prodMk
    ((measurable_clipEstimate B K mp mc).comp (measurable_samples hg (mp + mc))))
  exact h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_pilot_joint (B : ℝ) (K mp mc : ℕ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : E × (Fin (mp + mc) → Ω) => pilotOf B K mp mc (g w.1) w.2) := by
  unfold pilotOf
  exact (measurable_gradedPilot (m := mp) B K 0).comp (Measurable.of_eval fun i =>
    hg.comp (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)))

omit [CompleteSpace E] in
lemma measurable_okError_joint (B : ℝ) (K mp mc : ℕ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) {G : E → E} (hG : Measurable G) :
    Measurable (Function.uncurry fun x z => okError B K mp mc (g x) (G x) z) := by
  classical
  have hp := measurable_pilot_joint B K mp mc hg
  have hest : Measurable (fun w : E × (Fin (mp + mc) → Ω) => estimateOf B K mp mc (g w.1) w.2) :=
    (measurable_clipEstimate B K mp mc).comp (measurable_samples hg (mp + mc))
  change Measurable (fun w : E × (Fin (mp + mc) → Ω) => okError B K mp mc (g w.1) (G w.1) w.2)
  unfold okError
  exact Measurable.ite (measurableSet_le (hp.sub (hG.comp measurable_fst)).norm measurable_const)
    (hest.sub (hG.comp measurable_fst)).norm measurable_const

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_scale_joint (B : ℝ) (K mp mc : ℕ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) {G : E → E} (hG : Measurable G) (t : ℝ) :
    Measurable (Function.uncurry fun x z => Set.indicator
      {z | t < ‖pilotOf B K mp mc (g x) z - G x‖} (fun _ => (1 : ℝ)) z) := by
  have hset : MeasurableSet {w : E × (Fin (mp + mc) → Ω) |
      t < ‖pilotOf B K mp mc (g w.1) w.2 - G w.1‖} :=
    measurableSet_lt measurable_const
      ((measurable_pilot_joint B K mp mc hg).sub (hG.comp measurable_fst)).norm
  have he : (Function.uncurry fun x z => Set.indicator
      {z | t < ‖pilotOf B K mp mc (g x) z - G x‖} (fun _ => (1 : ℝ)) z) =
      Set.indicator {w : E × (Fin (mp + mc) → Ω) |
        t < ‖pilotOf B K mp mc (g w.1) w.2 - G w.1‖} (fun _ => (1 : ℝ)) := by
    funext w
    simp only [Function.uncurry, Set.indicator, Set.mem_ofPred_eq]
  rw [he]
  exact measurable_const.indicator hset

variable {p : Measure Ω} [IsProbabilityMeasure p]

lemma ok_tail {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {G : E → E}
    (hG : Measurable G) (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p) {σ : ℝ} (hσ : 0 ≤ σ)
    (hvar : ∀ x, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂p) ≤ σ ^ 2) {B η : ℝ} (hB : 0 < B) {K mp mc : ℕ}
    (hmc : 0 < mc) (x0 : E) (T : ℕ) (r : ℝ) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (mp + mc) => p).real
      {b | r ≤ ∑ t ∈ Finset.range T, okError B K mp mc (g (traj (stepMap B η K mp mc g) x0 b t))
        (G (traj (stepMap B η K mp mc g) x0 b t)) (b t)} ≤
      Real.exp (T * (Real.log 5 + (clipRadius σ B mc 0 / mc + 12 * B / mc) / (2 * (12 * B / mc)))
        - 1 / (2 * (12 * B / mc)) * r) := by
  have ha1 : 0 < 12 * B / mc := by positivity
  have hθ : 0 ≤ 1 / (2 * (12 * B / mc)) := by positivity
  have hfun (x : E) : (fun z => Real.exp (1 / (2 * (12 * B / mc)) * okError B K mp mc (g x) (G x) z)) =
      fun z => Real.exp (okError B K mp mc (g x) (G x) z / (2 * (12 * B / mc))) := by
    funext z; congr 1; ring
  refine adapted_tail (measurable_stepMap B η K mp mc hg) x0
    (measurable_okError_joint B K mp mc hg hG) hθ (fun x => ?_) (fun x => ?_) T r
  · have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
    have h := (block_ok_mgf (K := K) (mp := mp) hgx (hgi x) (hmean x) (hvi x) hσ (hvar x) hB
      hmc).1
    rw [hfun x]
    exact h
  · have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
    have h := (block_ok_mgf (K := K) (mp := mp) hgx (hgi x) (hmean x) (hvi x) hσ (hvar x) hB
      hmc).2
    rw [hfun x, Real.exp_add, Real.exp_log (by norm_num)]
    exact h

lemma scale_tail {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {G : E → E}
    (hG : Measurable G) {B η t : ℝ} {K mp mc : ℕ} (n : ℕ)
    (hρ : ∀ x, (Measure.pi fun _ : Fin (mp + mc) => p)
      {z | t < ‖pilotOf B K mp mc (g x) z - G x‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * n)))
    (x0 : E) (T : ℕ) (r : ℝ) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (mp + mc) => p).real
      {b | r ≤ ∑ s ∈ Finset.range T, Set.indicator
        {z | t < ‖pilotOf B K mp mc (g (traj (stepMap B η K mp mc g) x0 b s)) z -
          G (traj (stepMap B η K mp mc g) x0 b s)‖} (fun _ => (1 : ℝ)) (b s)} ≤
      Real.exp (T * (1 / 2 : ℝ) ^ n - n * Real.log 2 * r) := by
  have hθ : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  refine adapted_tail (measurable_stepMap B η K mp mc hg) x0
    (measurable_scale_joint B K mp mc hg hG t) hθ (fun x => ?_) (fun x => ?_) T r
  · have hA : MeasurableSet {z | t < ‖pilotOf B K mp mc (g x) z - G x‖} :=
      measurableSet_lt measurable_const
        ((measurable_pilotOf B K mp mc (V := g x) (hg.comp measurable_prodMk_left)).sub_const _).norm
    exact (indicator_mgf hA hθ (ρ := 1) (measureReal_le_one)).1
  · have hA : MeasurableSet {z | t < ‖pilotOf B K mp mc (g x) z - G x‖} :=
      measurableSet_lt measurable_const
        ((measurable_pilotOf B K mp mc (V := g x) (hg.comp measurable_prodMk_left)).sub_const _).norm
    have hreal : (Measure.pi fun _ : Fin (mp + mc) => p).real
        {z | t < ‖pilotOf B K mp mc (g x) z - G x‖} ≤ (1 / 2 : ℝ) ^ (2 * n) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hρ x)
    refine (indicator_mgf hA hθ hreal).2.trans (Real.exp_le_exp.mpr ?_)
    have he : Real.exp ((n : ℝ) * Real.log 2) = 2 ^ n := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    rw [he]
    have h1 : ((2 : ℝ) ^ n - 1) * (1 / 2 : ℝ) ^ (2 * n) ≤ 2 ^ n * (1 / 2 : ℝ) ^ (2 * n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (2 * n) = (1 / 2 : ℝ) ^ n := by
      rw [pow_mul, show ((1 / 2 : ℝ) ^ 2) ^ n = (1 / 2) ^ n * (1 / 2) ^ n by
        rw [← mul_pow]; norm_num, ← mul_assoc, ← mul_pow]
      norm_num
    linarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma bad_subset {g : E → Ω → E} {f : E → ℝ} {L η Δ fstar B Gcap ra : ℝ} (hL : 0 < L)
    (hη : 0 ≤ η) (hB : 0 < B) {K mp mc J T : ℕ} (hmc : 0 < mc)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlow : ∀ y, fstar ≤ f y)
    (hJ : Gcap ≤ 4 * (2 ^ J * B)) (hG : 0 ≤ Gcap) (m : ℕ → ℝ) (x0 : E)
    (hgap : f x0 - fstar ≤ Δ)
    (hroom : 2 * L * (Δ + η * (2 * ra + ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j) +
      T * (L / 2 * η ^ 2)) ≤ Gcap ^ 2) :
    {b : ℕ → Fin (mp + mc) → Ω | Δ + η * (2 * ra + ∑ j ∈ Finset.range (J + 1),
        8 * (2 ^ j * B) * m j) + T * (L / 2 * η ^ 2) <
      η * ∑ t ∈ Finset.range T, ‖gradient f (traj (stepMap B η K mp mc g) x0 b t)‖} ⊆
      {b | ra ≤ ∑ t ∈ Finset.range T, okError B K mp mc (g (traj (stepMap B η K mp mc g) x0 b t))
        (gradient f (traj (stepMap B η K mp mc g) x0 b t)) (b t)} ∪
      ⋃ j ∈ Finset.range (J + 1), {b | m j ≤ ∑ s ∈ Finset.range T, Set.indicator
        {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc (g (traj (stepMap B η K mp mc g) x0 b s)) z -
          gradient f (traj (stepMap B η K mp mc g) x0 b s)‖} (fun _ => (1 : ℝ)) (b s)} := by
  intro b hb
  by_contra hcon
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_le] at hcon
  obtain ⟨hok, hsc⟩ := hcon
  set x := traj (stepMap B η K mp mc g) x0 b with hx
  let ind : ℕ → ℕ → ℝ := fun j s => Set.indicator {z | 2 ^ j * B / 2 <
    ‖pilotOf B K mp mc (g (x s)) z - gradient f (x s)‖} (fun _ => (1 : ℝ)) (b s)
  let Dbar : ℕ → ℝ := fun t => 2 * okError B K mp mc (g (x t)) (gradient f (x t)) (b t) +
    ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * ind j t
  have hD0 (t : ℕ) : 0 ≤ Dbar t := add_nonneg (by
      have := okError_nonneg B K mp mc (g (x t)) (gradient f (x t)) (b t); linarith)
    (Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
  have hcap (t : ℕ) (ht : ‖gradient f (x t)‖ ≤ Gcap) :
      2 * min ‖clipEstimate B K mp mc (fun i => g (x t) (b t i)) - gradient f (x t)‖
        ‖gradient f (x t)‖ ≤ Dbar t :=
    error_split hB hmc hJ (g (x t)) (gradient f (x t)) ht (b t)
  have hW : (∑ t ∈ Finset.range T, Dbar t) ≤
      2 * ra + ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j := by
    have hs : (∑ t ∈ Finset.range T, Dbar t) =
        2 * (∑ t ∈ Finset.range T, okError B K mp mc (g (x t)) (gradient f (x t)) (b t)) +
          ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * ∑ t ∈ Finset.range T, ind j t := by
      simp only [Dbar, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hs]
    have h1 : (∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * ∑ t ∈ Finset.range T, ind j t) ≤
        ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hsc j hj).le (by positivity)
    linarith
  have hstep (t : ℕ) : x (t + 1) =
      normalizedStep η (x t) (clipEstimate B K mp mc (fun i => g (x t) (b t i))) := rfl
  have hmain := trajectory_bound hL hη hgrad hlip hlow x
    (fun t => clipEstimate B K mp mc (fun i => g (x t) (b t i))) hstep Dbar hD0 hcap T hW
    hgap hG hroom
  exact absurd hb (not_lt.mpr hmain)

lemma phase_one_prob {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {f : E → ℝ}
    {L η Δ fstar B Gcap ra σ : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hB : 0 < B) (hσ : 0 ≤ σ)
    {K mp mc J T : ℕ} (hmc : 0 < mc)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlow : ∀ y, fstar ≤ f y)
    (hgm : Measurable (gradient f)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hvar : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p) ≤ σ ^ 2)
    (hJ : Gcap ≤ 4 * (2 ^ J * B)) (hG : 0 ≤ Gcap) (m : ℕ → ℝ) (n : ℕ → ℕ)
    (hρ : ∀ j ∈ Finset.range (J + 1), ∀ x, (Measure.pi fun _ : Fin (mp + mc) => p)
      {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc (g x) z - gradient f x‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * n j)))
    (x0 : E) (hgap : f x0 - fstar ≤ Δ)
    (hroom : 2 * L * (Δ + η * (2 * ra + ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j) +
      T * (L / 2 * η ^ 2)) ≤ Gcap ^ 2) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (mp + mc) => p).real
      {b | Δ + η * (2 * ra + ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j) +
        T * (L / 2 * η ^ 2) <
        η * ∑ t ∈ Finset.range T, ‖gradient f (traj (stepMap B η K mp mc g) x0 b t)‖} ≤
      Real.exp (T * (Real.log 5 + (clipRadius σ B mc 0 / mc + 12 * B / mc) / (2 * (12 * B / mc)))
        - 1 / (2 * (12 * B / mc)) * ra) +
      ∑ j ∈ Finset.range (J + 1), Real.exp (T * (1 / 2 : ℝ) ^ n j - n j * Real.log 2 * m j) := by
  refine (measureReal_mono (bad_subset (K := K) hL hη hB hmc hgrad hlip hlow hJ hG m x0 hgap
    hroom)).trans ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
  · exact ok_tail hg hgm hgi hmean hvi hσ hvar hB hmc x0 T ra
  · refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    exact scale_tail hg hgm (n j) (hρ j hj) x0 T (m j)

end LongTails.Proofs.HighProbabilityPhaseOne
