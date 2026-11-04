import LongTails.Proofs.SymmetricThirdOrderEnergy
import LongTails.Proofs.SymmetricThirdOrderMinimizers
import Mathlib.Data.Nat.Dist

namespace LongTails.Proofs.SymmetricThirdOrderOuter

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.CompositeCubicAcceleration
open LongTails.Proofs.SymmetricThirdOrderMinimizers
open LongTails.Proofs.SymmetricThirdOrderEnergy
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma grid_scale_lower {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) : δ ≤ δ * 4 ^ j := by
  have hh : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

lemma outerCenter_mem {C : Set E} (hC : Convex ℝ C) {δ : ℝ} (hδ : 0 < δ)
    (s : OuterState E) (hA : 0 ≤ s.weight) (hx : s.point ∈ C) (hv : s.momentum ∈ C) :
    outerCenter δ s ∈ C := by
  have hμ : 0 < δ * 4 ^ s.grid := by positivity
  have ha := trialWeight_pos hμ hA
  exact (convex_mixture (convexOn_const (0 : ℝ) hC) hx hv hA ha.le
    (add_pos_of_nonneg_of_pos hA ha)).1

lemma outer_curvature_bounds {x0 z : E} {R L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (s : OuterState E) (hA : 0 ≤ s.weight)
    (hx : s.point ∈ Metric.closedBall x0 R) (hv : s.momentum ∈ Metric.closedBall x0 R)
    (hz : z ∈ Metric.closedBall x0 R) :
    δ ≤ δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2 ∧
    δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2 ≤ δ + 32 * L * R ^ 2 := by
  have hc := outerCenter_mem (convex_closedBall x0 R) hδ s hA hx hv
  have hd : ‖z - outerCenter δ s‖ ≤ 2 * R := by
    have ht := dist_triangle z x0 (outerCenter δ s)
    have hz' : dist z x0 ≤ R := hz
    have hc' : dist (outerCenter δ s) x0 ≤ R := hc
    rw [dist_comm x0] at ht
    rw [dist_eq_norm] at ht
    linarith
  have hn := mul_nonneg hL (sq_nonneg ‖z - outerCenter δ s‖)
  have hR : 0 ≤ R := (dist_nonneg (x := z) (y := x0)).trans hz
  have hh : ‖z - outerCenter δ s‖ ^ 2 ≤ (2 * R) ^ 2 := by gcongr
  have hm := mul_le_mul_of_nonneg_left hh hL
  constructor <;> nlinarith

lemma outerAdvance_frozen (C : Set E) (fallback : E) (L δ X : ℝ) (M : ℕ)
    (s : OuterState E) (z g : E) (hstop : X ≤ s.weight) :
    outerAdvance C fallback L δ X M s z g = s := by simp [outerAdvance, hstop]

lemma outerAdvance_grid_le (C : Set E) (fallback : E) (L δ X : ℝ) (M : ℕ)
    (s : OuterState E) (z g : E) (hgrid : s.grid ≤ M) :
    (outerAdvance C fallback L δ X M s z g).grid ≤ M := by
  unfold outerAdvance
  split_ifs
  · exact hgrid
  · dsimp only
    split_ifs
    · omega
    · exact min_le_left _ _

lemma outerAdvance_weight_mono (C : Set E) (fallback : E) {L δ X : ℝ} (M : ℕ)
    (hL : 0 ≤ L) (hδ : 0 < δ) (s : OuterState E) (z g : E) (hA : 0 ≤ s.weight) :
    s.weight ≤ (outerAdvance C fallback L δ X M s z g).weight := by
  by_cases hs : X ≤ s.weight
  · rw [outerAdvance_frozen C fallback L δ X M s z g hs]
  · have hμ : 0 < δ * 4 ^ s.grid := by positivity
    have hl : 0 < δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2 := by positivity
    have ha := trialWeight_pos hμ hA
    have hβ := (damping_properties hμ hl).1
    simp only [outerAdvance, ite_eq_right hs]
    exact le_add_of_nonneg_right (mul_nonneg hβ.le ha.le)

lemma outerAdvance_weight_bound (C : Set E) (fallback : E) {L δ X : ℝ} (M : ℕ)
    (hδ : 0 < δ) (hδX : 1 ≤ δ * X)
    (s : OuterState E) (z g : E) (hA : 0 ≤ s.weight) (hAX : s.weight ≤ 3 * X) :
    (outerAdvance C fallback L δ X M s z g).weight ≤ 3 * X := by
  by_cases hs : X ≤ s.weight
  · simpa only [outerAdvance_frozen C fallback L δ X M s z g hs] using hAX
  · have hμ : 0 < δ * 4 ^ s.grid := by positivity
    have hX : 0 < X := hA.trans_lt (lt_of_not_ge hs)
    have hμX : 1 ≤ (δ * 4 ^ s.grid) * X :=
      hδX.trans (mul_le_mul_of_nonneg_right (grid_scale_lower hδ.le s.grid) hX.le)
    simp only [outerAdvance, ite_eq_right hs]
    exact stopping_overshoot hμ hA (lt_of_not_ge hs) hμX (min_le_left _ _)

lemma outerAdvance_feasible (C : Set E) (fallback : E) {L δ X : ℝ} (M : ℕ)
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C) (hL : 0 ≤ L) (hδ : 0 < δ)
    (s : OuterState E) (z g : E) (hA : 0 ≤ s.weight)
    (hx : s.point ∈ C) (hv : s.momentum ∈ C) (hz : z ∈ C) :
    (outerAdvance C fallback L δ X M s z g).point ∈ C ∧
    (outerAdvance C fallback L δ X M s z g).momentum ∈ C := by
  by_cases hs : X ≤ s.weight
  · simpa only [outerAdvance_frozen C fallback L δ X M s z g hs] using And.intro hx hv
  let μ := δ * 4 ^ s.grid
  let a := LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ s.weight
  let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
  let β := min 1 (μ / lam)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hl : 0 < lam := by dsimp [lam]; positivity
  have ha : 0 < a := trialWeight_pos hμ hA
  have hb : 0 < β ∧ β ≤ 1 := ⟨(damping_properties hμ hl).1, (damping_properties hμ hl).2.1⟩
  have hleft : 0 ≤ (1 - β) * s.weight := mul_nonneg (sub_nonneg.mpr hb.2) hA
  have hright : 0 < β * (s.weight + a) := mul_pos hb.1 (add_pos_of_nonneg_of_pos hA ha)
  have hmix := convex_mixture (convexOn_const (0 : ℝ) hconv) hx hz hleft hright.le
    (add_pos_of_nonneg_of_pos hleft hright)
  have he : (1 - β) * s.weight + β * (s.weight + a) = s.weight + β * a := by ring
  rw [he] at hmix
  simp only [outerAdvance, ite_eq_right hs]
  exact ⟨hmix.1, projectPoint_mem C fallback _ hC hne⟩

lemma grid_down_charge (j k : ℕ) :
    1 + Nat.dist (j - 1) k ≤ (if j ≤ k then 2 else 0) + Nat.dist j k := by
  unfold Nat.dist
  split_ifs <;> omega

lemma grid_up_charge {j k M : ℕ} (hj : j ≤ M) (hk : k ≤ M) :
    1 + Nat.dist (min M (j + 1)) k ≤ (if k ≤ j then 2 else 0) + Nat.dist j k := by
  unfold Nat.dist
  split_ifs <;> omega

lemma phase_grid_charge (j : ℕ → ℕ) (down : ℕ → Prop) [DecidablePred down]
    {M k n : ℕ} (hk : k ≤ M) (hgrid : ∀ t ≤ n, j t ≤ M)
    (hstep : ∀ t < n, j (t + 1) = if down t then j t - 1 else min M (j t + 1)) :
    n ≤ 2 * (∑ t ∈ Finset.range n, if down t then (if j t ≤ k then 1 else 0)
      else (if k ≤ j t then 1 else 0)) + M := by
  let fav := fun t => if down t then (if j t ≤ k then 1 else 0) else (if k ≤ j t then 1 else 0)
  have hlocal (t : ℕ) (ht : t < n) : 1 + Nat.dist (j (t + 1)) k ≤ 2 * fav t + Nat.dist (j t) k := by
    rw [hstep t ht]
    by_cases hd : down t
    · simp only [hd, ite_true, fav]
      have hh := grid_down_charge (j t) k
      split_ifs at hh ⊢ <;> omega
    · simp only [hd, ite_false, fav]
      have hh := grid_up_charge (hgrid t (Nat.le_of_lt ht)) hk
      split_ifs at hh ⊢ <;> omega
  have hsum (r : ℕ) (hr : r ≤ n) :
      r + Nat.dist (j r) k ≤ 2 * (∑ t ∈ Finset.range r, fav t) + Nat.dist (j 0) k := by
    induction r with
    | zero => simp
    | succ r ih =>
      have hi := ih (by omega)
      have hh := hlocal r (by omega)
      rw [Finset.sum_range_succ]
      omega
  have hh := hsum n le_rfl
  have hd : Nat.dist (j 0) k ≤ M := by
    have h₀ := hgrid 0 (Nat.zero_le n)
    unfold Nat.dist
    omega
  change n ≤ 2 * (∑ t ∈ Finset.range n, fav t) + M
  omega

lemma low_down_progress {μ A h : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A)
    (hh : 0 < h) (hμh : μ ≤ 4 * h) :
    1 / (4 * Real.sqrt h) ≤
      Real.sqrt (A + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ A) - Real.sqrt A := by
  have hr : Real.sqrt μ ≤ 2 * Real.sqrt h := by
    nlinarith [Real.sq_sqrt hμ.le, Real.sq_sqrt hh.le,
      Real.sqrt_nonneg μ, Real.sqrt_nonneg h]
  apply le_trans ?_ (success_sqrt_progress hμ hA)
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt h)
    (by positivity : 0 < 2 * Real.sqrt μ)).mpr
  nlinarith

lemma high_up_dissipation {δ L μ lam β T b h r : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hb : 0 ≤ b) (hbT : b ≤ T)
    (hh : 2 * δ ≤ h) (hμ : h ≤ μ) (hup : μ < lam)
    (hlam : lam = δ + 8 * L * r ^ 2) (hβ : β = μ / lam) :
    b * h ^ 2 / (16 * L) ≤ β * T * lam * r ^ 2 := by
  have hh₀ : 0 < h := by linarith
  have hμ₀ : 0 < μ := hh₀.trans_le hμ
  have hl₀ : 0 < lam := hμ₀.trans hup
  have hr : h / (16 * L) ≤ r ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * L)).mpr
    rw [hlam] at hup
    linarith
  have hT₀ : 0 ≤ T := hb.trans hbT
  calc
    _ = b * h * (h / (16 * L)) := by ring
    _ ≤ T * μ * r ^ 2 := by gcongr
    _ = _ := by rw [hβ]; field_simp

lemma count_progress_before_exit (A : ℕ → ℝ) (good : ℕ → Prop) [DecidablePred good]
    {n : ℕ} {c U : ℝ} (hc : 0 ≤ c)
    (hmono : ∀ t < n, A t ≤ A (t + 1)) (hupper : ∀ t < n, A t ≤ U)
    (hprogress : ∀ t < n, good t → c ≤ Real.sqrt (A (t + 1)) - Real.sqrt (A t)) :
    ((Finset.range n).filter good).card * c ≤ Real.sqrt U + c := by
  have he (r : ℕ) : (∑ t ∈ Finset.range r, if good t then c else 0) =
      ((Finset.range r).filter good).card * c := by
    rw [← Finset.sum_filter]
    simp
  rw [← he]
  cases n with
  | zero => simp; positivity
  | succ n =>
    have hs : (∑ t ∈ Finset.range n, if good t then c else 0) ≤
        ∑ t ∈ Finset.range n, (Real.sqrt (A (t + 1)) - Real.sqrt (A t)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htn : t < n + 1 := Nat.lt_succ_of_lt (Finset.mem_range.mp ht)
      by_cases hg : good t
      · simpa only [hg, ite_true] using hprogress t htn hg
      · simp only [hg, ite_false]
        exact sub_nonneg.mpr (Real.sqrt_le_sqrt (hmono t htn))
    rw [Finset.sum_range_sub (fun t => Real.sqrt (A t)) n] at hs
    have hu := Real.sqrt_le_sqrt (hupper n (Nat.lt_succ_self n))
    have hn := Real.sqrt_nonneg (A 0)
    rw [Finset.sum_range_succ]
    split_ifs <;> linarith

lemma count_dissipation (d : ℕ → ℝ) (good : ℕ → Prop) [DecidablePred good]
    {n : ℕ} {c D : ℝ} (hd : ∀ t < n, 0 ≤ d t)
    (hgood : ∀ t < n, good t → c ≤ d t) (hsum : ∑ t ∈ Finset.range n, d t ≤ D) :
    ((Finset.range n).filter good).card * c ≤ D := by
  have he : (∑ t ∈ Finset.range n, if good t then c else 0) =
      ((Finset.range n).filter good).card * c := by
    rw [← Finset.sum_filter]
    simp
  rw [← he]
  apply le_trans (Finset.sum_le_sum ?_) hsum
  intro t ht
  have htn := Finset.mem_range.mp ht
  by_cases hg : good t
  · simpa only [hg, ite_true] using hgood t htn hg
  · simpa only [hg, ite_false] using hd t htn

lemma grid_threshold_exists {δ h : ℝ} (hδ : 0 < δ) (hh : δ ≤ h) (M : ℕ) :
    ∃ k ≤ M, (∀ j ≤ k, δ * 4 ^ j ≤ 4 * h) ∧
      ∀ j, k ≤ j → h ≤ δ * 4 ^ j ∨ δ * 4 ^ M ≤ δ * 4 ^ j := by
  have hh₀ : 0 < h := hδ.trans_le hh
  by_cases htop : h ≤ δ * 4 ^ M
  · have hex : ∃ j : ℕ, h ≤ δ * 4 ^ j := ⟨M, htop⟩
    let k := Nat.find hex
    have hkM : k ≤ M := Nat.find_min' hex htop
    have hklo : h ≤ δ * 4 ^ k := Nat.find_spec hex
    have hkhi : δ * 4 ^ k ≤ 4 * h := by
      cases he : k with
      | zero => simp only [pow_zero, mul_one]; linarith
      | succ r =>
        have hmin : ¬h ≤ δ * 4 ^ r := Nat.find_min hex (by change r < k; omega)
        have hr := lt_of_not_ge hmin
        rw [pow_succ]
        nlinarith
    refine ⟨k, hkM, ?_, ?_⟩
    · intro j hj
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj) hδ.le).trans hkhi
    · intro j hj
      exact Or.inl (hklo.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj) hδ.le))
  · refine ⟨M, le_rfl, ?_, ?_⟩
    · intro j hj
      have hm := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj) hδ.le
      have ht := lt_of_not_ge htop
      linarith
    · intro j hj
      exact Or.inr (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj) hδ.le)

lemma phase_grid_charge_counts (j : ℕ → ℕ) (down : ℕ → Prop) [DecidablePred down]
    {M k n : ℕ} (hk : k ≤ M) (hgrid : ∀ t ≤ n, j t ≤ M)
    (hstep : ∀ t < n, j (t + 1) = if down t then j t - 1 else min M (j t + 1)) :
    n ≤ 2 * (((Finset.range n).filter (fun t => down t ∧ j t ≤ k)).card +
      ((Finset.range n).filter (fun t => ¬down t ∧ k ≤ j t)).card) + M := by
  have hh := phase_grid_charge j down hk hgrid hstep
  have he : (∑ t ∈ Finset.range n, if down t then (if j t ≤ k then 1 else 0)
      else (if k ≤ j t then 1 else 0)) =
      ((Finset.range n).filter (fun t => down t ∧ j t ≤ k)).card +
      ((Finset.range n).filter (fun t => ¬down t ∧ k ≤ j t)).card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hd : down t <;> simp [hd]
  rwa [he] at hh

lemma phase_count_bound (j : ℕ → ℕ) (down : ℕ → Prop) [DecidablePred down]
    (A d : ℕ → ℝ) {M k n : ℕ} {b h L D : ℝ} (hb : 0 < b) (hh : 0 < h) (hL : 0 < L)
    (hk : k ≤ M) (hgrid : ∀ t ≤ n, j t ≤ M)
    (hstep : ∀ t < n, j (t + 1) = if down t then j t - 1 else min M (j t + 1))
    (hmono : ∀ t < n, A t ≤ A (t + 1)) (hupper : ∀ t < n, A t ≤ 2 * b)
    (hlow : ∀ t < n, down t ∧ j t ≤ k →
      1 / (4 * Real.sqrt h) ≤ Real.sqrt (A (t + 1)) - Real.sqrt (A t))
    (hd : ∀ t < n, 0 ≤ d t)
    (hhigh : ∀ t < n, ¬down t ∧ k ≤ j t → b * h ^ 2 / (16 * L) ≤ d t)
    (hsum : ∑ t ∈ Finset.range n, d t ≤ D) :
    (n : ℝ) ≤ 8 * Real.sqrt h * Real.sqrt (2 * b) + 2 + 32 * L * D / (b * h ^ 2) + M := by
  let Nd : ℝ := ((Finset.range n).filter (fun t => down t ∧ j t ≤ k)).card
  let Nu : ℝ := ((Finset.range n).filter (fun t => ¬down t ∧ k ≤ j t)).card
  have hcount : (n : ℝ) ≤ 2 * (Nd + Nu) + M := by
    dsimp [Nd, Nu]
    exact_mod_cast phase_grid_charge_counts j down hk hgrid hstep
  have hlo := count_progress_before_exit A (fun t => down t ∧ j t ≤ k)
    (by positivity : 0 ≤ 1 / (4 * Real.sqrt h)) hmono hupper hlow
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hNd : Nd ≤ 4 * Real.sqrt h * Real.sqrt (2 * b) + 1 := by
    have hdpos : 0 < 4 * Real.sqrt h := by positivity
    calc
      _ = (Nd * (1 / (4 * Real.sqrt h))) * (4 * Real.sqrt h) := by field_simp
      _ ≤ (Real.sqrt (2 * b) + 1 / (4 * Real.sqrt h)) * (4 * Real.sqrt h) :=
        mul_le_mul_of_nonneg_right hlo hdpos.le
      _ = _ := by field_simp
  have hhi := count_dissipation d (fun t => ¬down t ∧ k ≤ j t) hd hhigh hsum
  have hNu : Nu ≤ 16 * L * D / (b * h ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < b * h ^ 2)).mpr
    have hm := mul_le_mul_of_nonneg_right hhi (by positivity : 0 ≤ 16 * L)
    have he : (Nu * (b * h ^ 2 / (16 * L))) * (16 * L) = Nu * (b * h ^ 2) := by field_simp
    change (Nu * (b * h ^ 2 / (16 * L))) * (16 * L) ≤ D * (16 * L) at hm
    rw [he] at hm
    nlinarith
  have he : 32 * L * D / (b * h ^ 2) = 2 * (16 * L * D / (b * h ^ 2)) := by ring
  rw [he]
  linarith

lemma trialWeight_zero {μ : ℝ} (hμ : 0 < μ) :
    LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ 0 = 1 / μ := by
  unfold LongTails.Algorithms.CompositeCubicAcceleration.trialWeight
  norm_num
  field_simp

lemma outerCenter_initial {δ : ℝ} (hδ : 0 < δ) (x0 : E) (M : ℕ) :
    outerCenter δ (outerInitial x0 M) = x0 := by
  have ha := trialWeight_pos (show 0 < δ * 4 ^ M by positivity) (le_refl (0 : ℝ))
  change (0 + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ M) 0)⁻¹ •
    ((0 : ℝ) • x0 + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ M) 0 • x0) = x0
  simp only [zero_add, zero_smul]
  exact inv_smul_smul₀ ha.ne' x0

lemma first_weight_exact (C : Set E) (x0 : E) {L δ X : ℝ} (M : ℕ) (z g : E)
    (hδ : 0 < δ) (hX : 0 < X)
    (hlam : 0 < δ + 8 * L * ‖z - outerCenter δ (outerInitial x0 M)‖ ^ 2)
    (hdown : δ + 8 * L * ‖z - outerCenter δ (outerInitial x0 M)‖ ^ 2 ≤ δ * 4 ^ M) :
    (outerAdvance C x0 L δ X M (outerInitial x0 M) z g).weight = 1 / (δ * 4 ^ M) := by
  have hβ : min 1 ((δ * 4 ^ M) /
      (δ + 8 * L * ‖z - outerCenter δ (outerInitial x0 M)‖ ^ 2)) = 1 := by
    apply min_eq_left
    exact (le_div_iff₀ hlam).mpr (by simpa using hdown)
  rw [outerAdvance, ite_eq_right (show ¬X ≤ (outerInitial x0 M).weight from not_le.mpr hX)]
  change 0 + min 1 ((δ * 4 ^ M) /
    (δ + 8 * L * ‖z - outerCenter δ (outerInitial x0 M)‖ ^ 2)) *
    LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ M) 0 = _
  rw [hβ, one_mul, zero_add, trialWeight_zero (by positivity)]

lemma first_weight_lower (x0 : E) {L δ X R : ℝ} (M : ℕ) (z g : E)
    (hL : 0 ≤ L) (hδ : 0 < δ) (hX : 0 < X) (hR : 0 ≤ R)
    (hz : z ∈ Metric.closedBall x0 R)
    (htop : δ + 32 * L * R ^ 2 ≤ δ * 4 ^ M)
    (htop_upper : δ * 4 ^ M ≤ 4 * (δ + 32 * L * R ^ 2)) :
    1 / (4 * (δ + 32 * L * R ^ 2)) ≤
      (outerAdvance (Metric.closedBall x0 R) x0 L δ X M (outerInitial x0 M) z g).weight := by
  have hx : x0 ∈ Metric.closedBall x0 R := by simpa using hR
  have hc := outer_curvature_bounds hL hδ (outerInitial x0 M) (le_refl (0 : ℝ)) hx hx hz
  rw [first_weight_exact _ _ _ _ _ hδ hX (hδ.trans_le hc.1) (hc.2.trans htop)]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (δ + 32 * L * R ^ 2))
    (by positivity : 0 < δ * 4 ^ M)).mpr
  simpa using htop_upper

end LongTails.Proofs.SymmetricThirdOrderOuter
