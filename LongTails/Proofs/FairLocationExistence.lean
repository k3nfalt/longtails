import LongTails.Proofs.RadialFairStability
import Mathlib.Topology.MetricSpace.Contracting

namespace OracleTemplate.RadialFairLocation

open scoped RealInnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma monotone_step_contraction {α μ K : ℝ} (hα : 0 < α) (hstep : α * K ^ 2 ≤ μ) (hsmall : α * μ ≤ 1)
    (x y u v : E) (hlip : ‖u - v‖ ≤ K * ‖x - y‖)
    (hmono : μ * ‖x - y‖ ^ 2 ≤ ⟪u - v, x - y⟫) :
    ‖(x - α • u) - (y - α • v)‖ ≤ (1 - α * μ / 2) * ‖x - y‖ := by
  have he : (x - α • u) - (y - α • v) = (x - y) - α • (u - v) := by
    rw [smul_sub]
    abel
  rw [he]
  have hnorm : ‖u - v‖ ^ 2 ≤ K ^ 2 * ‖x - y‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg (u - v)) hlip 2
    nlinarith
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (sq_nonneg α)
  have hm := mul_le_mul_of_nonneg_left hmono (by linarith : 0 ≤ 2 * α)
  have hs := mul_le_mul_of_nonneg_right hstep
    (mul_nonneg hα.le (sq_nonneg ‖x - y‖))
  have hid : ‖(x - y) - α • (u - v)‖ ^ 2 = ‖x - y‖ ^ 2 +
      α ^ 2 * ‖u - v‖ ^ 2 - 2 * α * ⟪u - v, x - y⟫ := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hα,
      real_inner_smul_right, real_inner_comm (x - y) (u - v)]
    ring
  have hb : ‖(x - y) - α • (u - v)‖ ^ 2 ≤ (1 - α * μ) * ‖x - y‖ ^ 2 := by
    rw [hid]
    nlinarith
  have hq : 0 ≤ 1 - α * μ / 2 := by linarith
  have hdiff := mul_nonneg (sq_nonneg (α * μ / 2)) (sq_nonneg ‖x - y‖)
  have htarget : 0 ≤ (1 - α * μ / 2) * ‖x - y‖ := mul_nonneg hq (norm_nonneg _)
  nlinarith [sq_nonneg (‖(x - y) - α • (u - v)‖ - (1 - α * μ / 2) * ‖x - y‖)]

lemma exists_root_on [CompleteSpace E] {s : Set E} (hs : IsClosed s) (hne : s.Nonempty)
    {F : E → E} {α μ K : ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hstep : α * K ^ 2 ≤ μ) (hsmall : α * μ ≤ 1)
    (hmap : ∀ x ∈ s, x - α • F x ∈ s)
    (hlip : ∀ x ∈ s, ∀ y ∈ s, ‖F x - F y‖ ≤ K * ‖x - y‖)
    (hmono : ∀ x ∈ s, ∀ y ∈ s, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) :
    ∃ z ∈ s, F z = 0 := by
  let q : ℝ≥0 := ⟨1 - α * μ / 2, by linarith⟩
  let step : E → E := fun x => x - α • F x
  have hmaps : Set.MapsTo step s s := hmap
  have hc : ContractingWith q (hmaps.restrict step s s) := by
    constructor
    · change 1 - α * μ / 2 < 1
      nlinarith [mul_pos hα hμ]
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (x.val - α • F x.val) (y.val - α • F y.val) ≤
        (1 - α * μ / 2) * dist x.val y.val
      simpa only [dist_eq_norm] using monotone_step_contraction hα hstep hsmall x.val y.val (F x.val) (F y.val)
        (hlip x.val x.property y.val y.property) (hmono x.val x.property y.val y.property)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z, hz, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    hs.isComplete hmaps hc hx (edist_ne_top x (step x))
  refine ⟨z, hz, ?_⟩
  have he : α • F z = 0 := sub_eq_self.mp hfix
  exact (smul_eq_zero.mp he).resolve_left hα.ne'

lemma score_step_ball {n : ℕ} {r α M : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hstep : α * n ≤ r) (a : Fin n → E) (ha : ∀ i, ‖a i‖ ≤ M)
    (z : E) (hz : ‖z‖ ≤ M) : ‖z - α • (∑ i, score r (z - a i))‖ ≤ M := by
  let w : Fin n → ℝ := fun i => α / (r + ‖z - a i‖)
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg hα (by positivity)
  have hwi : ∀ i, w i ≤ α / r := fun i =>
    div_le_div_of_nonneg_left hα hr (le_add_of_nonneg_right (norm_nonneg _))
  have hsum : ∑ i, w i ≤ 1 := by
    calc
      _ ≤ ∑ _i : Fin n, α / r := Finset.sum_le_sum (fun i _ => hwi i)
      _ = α * n / r := by simp; ring
      _ ≤ 1 := (div_le_one hr).mpr hstep
  have he : z - α • (∑ i, score r (z - a i)) =
      (1 - ∑ i, w i) • z + ∑ i, (w i) • a i := by
    calc
      _ = z - ∑ i, (w i) • (z - a i) := by
        simp only [Finset.smul_sum, score, smul_smul, w, div_eq_mul_inv]
      _ = z - ((∑ i, w i) • z - ∑ i, (w i) • a i) := by
        rw [Finset.sum_smul]
        simp only [smul_sub, Finset.sum_sub_distrib]
      _ = _ := by rw [sub_smul, one_smul]; abel
  rw [he]
  have hfirst : ‖(1 - ∑ i, w i) • z‖ ≤ (1 - ∑ i, w i) * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsum)]
    exact mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hsum)
  have hsecond : ‖∑ i, (w i) • a i‖ ≤ (∑ i, w i) * M := by
    calc
      _ ≤ ∑ i, ‖(w i) • a i‖ := norm_sum_le _ _
      _ ≤ ∑ i, (w i) * M := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (ha i) (hw i)
      _ = _ := (Finset.sum_mul _ _ _).symm
  exact (norm_add_le _ _).trans (by linarith)

lemma exists_location_bounded [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) : ∃ z, ‖z‖ ≤ ∑ i, ‖a i‖ ∧ ∑ i, score r (z - a i) = 0 := by
  let M : ℝ := ∑ i, ‖a i‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have ha : ∀ i, ‖a i‖ ≤ M := fun i => Finset.single_le_sum
    (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let D := r + 2 * M
  have hD : 0 < D := by dsimp [D]; positivity
  have hrD : r ≤ D := by dsimp [D]; linarith
  let α := r ^ 3 / (16 * n * D ^ 2)
  let μ := (n : ℝ) * r / D ^ 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hαn : α * n ≤ r := by
    dsimp [α]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 16 * (n : ℝ) * D ^ 2)]
    have hsq := pow_le_pow_left₀ hr.le hrD 2
    have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ r * (n : ℝ))
    have hp : 0 ≤ r * (n : ℝ) * D ^ 2 := by positivity
    nlinarith
  have hstep : α * (4 * n / r) ^ 2 ≤ μ := by
    apply le_of_eq
    dsimp [α, μ]
    field_simp
    ring
  have hsmall : α * μ ≤ 1 := by
    have he : α * μ = r ^ 4 / (16 * D ^ 4) := by
      dsimp [α, μ]
      field_simp
    rw [he, div_le_one (by positivity : 0 < 16 * D ^ 4)]
    have hh := pow_le_pow_left₀ hr.le hrD 4
    nlinarith [pow_nonneg hD.le 4]
  obtain ⟨z, hzn, hz⟩ := exists_root_on
    (s := Metric.closedBall (0 : E) M) Metric.isClosed_closedBall
    ⟨0, by simpa using hM⟩ hα hμ hstep hsmall
    (F := fun z => ∑ i, score r (z - a i))
    (by
      intro z hz
      have hz' : ‖z‖ ≤ M := by simpa using hz
      simpa using score_step_ball hr hα.le hαn a ha z hz')
    (by
      intro z _ w _
      exact sum_score_lipschitz hr a z w)
    (by
      intro z hz w hw
      exact sum_score_local_strong hr a ha z w (by simpa using hz) (by simpa using hw))
  exact ⟨z, by simpa using hzn, hz⟩

lemma location_equation [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) :
    ∑ i, score r (location r a - a i) = 0 :=
  Classical.epsilon_spec (by
    obtain ⟨z, _, hz⟩ := exists_location_bounded hn hr a
    exact ⟨z, hz⟩)

lemma location_unique {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (a : Fin n → E) (z w : E)
    (hz : ∑ i, score r (z - a i) = 0) (hw : ∑ i, score r (w - a i) = 0) : z = w := by
  let M := ‖z‖ + ‖w‖ + ∑ i, ‖a i‖
  have hsum : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha : ∀ i, ‖a i‖ ≤ M := by
    intro i
    have h := Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)
    dsimp [M]
    linarith [norm_nonneg z, norm_nonneg w]
  have hzm : ‖z‖ ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hwm : ‖w‖ ≤ M := by dsimp [M]; linarith [norm_nonneg z]
  have hs := sum_score_local_strong hr a ha z w hzm hwm
  rw [hz, hw, sub_self, inner_zero_left] at hs
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) * r / (r + 2 * M) ^ 2 := by positivity
  have hd : ‖z - w‖ ^ 2 = 0 := le_antisymm ((mul_le_mul_iff_right₀ hp).mp (by simpa using hs)) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hd))

lemma location_norm [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) : ‖location r a‖ ≤ ∑ i, ‖a i‖ := by
  obtain ⟨z, hz, he⟩ := exists_location_bounded hn hr a
  rw [location_unique hn hr a (location r a) z (location_equation hn hr a) he]
  exact hz

lemma location_translate [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) (c : E) :
    location r (fun i => a i + c) = location r a + c := by
  apply location_unique hn hr (fun i => a i + c)
    (location r (fun i => a i + c)) (location r a + c) (location_equation hn hr _)
  simpa only [add_sub_add_right_eq_sub] using location_equation hn hr a

lemma location_neg [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) :
    location r (fun i => -a i) = -location r a := by
  apply location_unique hn hr (fun i => -a i)
    (location r (fun i => -a i)) (-location r a) (location_equation hn hr _)
  simp only [neg_sub_neg, ← neg_sub (location r a), score_neg, Finset.sum_neg_distrib,
    location_equation hn hr a, neg_zero]

lemma location_distance [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a b : Fin n → E) :
    ‖location r a - location r b‖ ≤
      ((4 / r) * ∑ i, ‖a i - b i‖) /
        ((n : ℝ) * r / (r + 2 * ((∑ i, ‖a i‖) + ∑ i, ‖b i‖)) ^ 2) := by
  let M := (∑ i, ‖a i‖) + ∑ i, ‖b i‖
  have ha0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hb0 : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hM : 0 ≤ M := add_nonneg ha0 hb0
  have ha : ∀ i, ‖a i‖ ≤ M := by
    intro i
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right hb0)
  have hz : ‖location r a‖ ≤ M := (location_norm hn hr a).trans (le_add_of_nonneg_right hb0)
  have hw : ‖location r b‖ ≤ M := (location_norm hn hr b).trans (le_add_of_nonneg_left ha0)
  have hza : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖location r a - a i‖ ≤ 2 * M := by
    intro i _
    exact (norm_sub_le _ _).trans (by linarith [ha i])
  have hwa : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖location r b - a i‖ ≤ 2 * M := by
    intro i _
    exact (norm_sub_le _ _).trans (by linarith [ha i])
  have hs := cluster_root_stability hr (fun i => (4 / r) * ‖a i - b i‖)
    a b (location r a) (location r b) Finset.univ hza hwa
    (location_equation hn hr a) (location_equation hn hr b) (by
      intro i
      have he : (location r b - a i) - (location r b - b i) = -(a i - b i) := by abel
      simpa only [he, norm_neg] using score_lipschitz hr
        (location r b - a i) (location r b - b i))
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) * r / (r + 2 * M) ^ 2 := by positivity
  rw [le_div_iff₀ hp]
  simpa only [Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, ← mul_div_assoc,
    mul_comm ‖location r a - location r b‖] using hs

lemma continuous_location [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) : Continuous (location (E := E) (n := n) r) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let D : (Fin n → E) → ℝ := fun a =>
    (n : ℝ) * r / (r + 2 * ((∑ i, ‖a i‖) + ∑ i, ‖b i‖)) ^ 2
  have hDpos : ∀ a, 0 < D a := by
    intro a
    dsimp [D]
    positivity
  have hDc : Continuous D := by
    dsimp [D]
    apply Continuous.div continuous_const (by fun_prop)
    intro a
    apply ne_of_gt
    positivity
  have hNc : Continuous (fun a : Fin n → E => (4 / r) * ∑ i, ‖a i - b i‖) := by fun_prop
  have hlim : Filter.Tendsto (fun a : Fin n → E => ((4 / r) * ∑ i, ‖a i - b i‖) / D a)
      (nhds b) (nhds 0) := by
    have hh := (hNc.tendsto b).div (hDc.tendsto b) (hDpos b).ne'
    change Filter.Tendsto (fun a => ((4 / r) * ∑ i, ‖a i - b i‖) / D a)
      (nhds b) (nhds (((4 / r) * ∑ i, ‖b i - b i‖) / D b)) at hh
    simpa only [sub_self, norm_zero, Finset.sum_const_zero, mul_zero, zero_div] using hh
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun a => norm_nonneg _) (fun a => location_distance hn hr a b) hlim

end OracleTemplate.RadialFairLocation
