import LongTails.Algorithms.OnlineMetricAccelerated
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

lemma bestCut_spec (cuts : List (Fin d → ℝ)) (φ : Fin d → ℝ) :
    1 ≤ (bestCut cuts φ).1 ∧ (∀ a ∈ cuts, cutValue a φ ≤ (bestCut cuts φ).1) ∧
      (((bestCut cuts φ).1 = 1 ∧ (bestCut cuts φ).2 = 0) ∨
        ((bestCut cuts φ).2 ∈ cuts ∧ cutValue (bestCut cuts φ).2 φ = (bestCut cuts φ).1)) := by
  induction cuts with
  | nil => simp [bestCut]
  | cons a t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hdef : bestCut (a :: t) φ =
        if (bestCut t φ).1 < cutValue a φ then (cutValue a φ, a) else bestCut t φ := rfl
    rw [hdef]
    split_ifs with h
    · refine ⟨by linarith, ?_, Or.inr ⟨List.mem_cons_self, rfl⟩⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_rfl
      · exact (h2 b hb).trans h.le
    · push Not at h
      refine ⟨h1, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact h
        · exact h2 b hb
      · rcases h3 with h3 | ⟨hm, hv⟩
        · exact Or.inl h3
        · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hv⟩

lemma bestCut_le (cuts : List (Fin d → ℝ)) (φ : Fin d → ℝ) {M : ℝ} (hM : 1 ≤ M)
    (h : ∀ a ∈ cuts, cutValue a φ ≤ M) : (bestCut cuts φ).1 ≤ M := by
  rcases (bestCut_spec cuts φ).2.2 with ⟨h1, _⟩ | ⟨hm, hv⟩
  · rw [h1]; exact hM
  · rw [← hv]; exact h _ hm

lemma exp_jensen {w x : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    Real.exp (∑ i, w i * x i) ≤ ∑ i, w i * Real.exp (x i) := by
  have := (convexOn_exp).map_sum_le (t := Finset.univ) (w := w) (p := x)
    (fun i _ => hw i) hs (fun i _ => Set.mem_univ _)
  simpa [smul_eq_mul] using this

lemma lossL_linear {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) {cuts : List (Fin d → ℝ)}
    (hcuts : ∀ a ∈ cuts, ∀ i, 0 ≤ a i) (φ u : Fin d → ℝ) :
    lossL c cuts φ + ∑ i, lossGrad c cuts φ i * (u i - φ i) ≤ lossL c cuts u := by
  obtain ⟨hV1, hVmax, hVcase⟩ := bestCut_spec cuts φ
  obtain ⟨hU1, hUmax, -⟩ := bestCut_spec cuts u
  set ℓ := lossEll c φ
  set V := (bestCut cuts φ).1
  set a := (bestCut cuts φ).2
  have hℓ0 : 0 ≤ ℓ := Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le
  rcases eq_or_lt_of_le hℓ0 with hℓ | hℓ
  · have hL : lossL c cuts φ = 0 := by simp [lossL, ℓ, ← hℓ]
    have hg : ∀ i, lossGrad c cuts φ i = 0 := by intro i; simp [lossGrad, hL]
    simp only [hL, hg, zero_mul, Finset.sum_const_zero, add_zero]
    exact Real.sqrt_nonneg _
  set π : Fin d → ℝ := fun i => c i * Real.exp (-φ i) / ℓ
  set ρ : Fin d → ℝ := fun i => a i * Real.exp (φ i) / V
  have hVpos : 0 < V := by linarith
  have hπ0 : ∀ i, 0 ≤ π i := fun i => div_nonneg (mul_nonneg (hc i) (Real.exp_pos _).le) hℓ.le
  have hπ1 : ∑ i, π i = 1 := by
    simp only [π, ← Finset.sum_div]; exact div_self hℓ.ne'
  have hellu : ℓ * Real.exp (∑ i, π i * (-(u i - φ i))) ≤ lossEll c u := by
    have hj := exp_jensen (x := fun i => -(u i - φ i)) hπ0 hπ1
    have e : lossEll c u = ℓ * ∑ i, π i * Real.exp (-(u i - φ i)) := by
      simp only [lossEll, π, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]; exact mul_le_mul_of_nonneg_left hj hℓ.le
  have hVu : V * Real.exp (∑ i, ρ i * (u i - φ i)) ≤ (bestCut cuts u).1 := by
    rcases hVcase with ⟨hV, ha⟩ | ⟨hm, hv⟩
    · have hρ : ∀ i, ρ i = 0 := by intro i; simp [ρ, ha]
      simp only [hρ, zero_mul, Finset.sum_const_zero, Real.exp_zero, mul_one]
      rw [show V = 1 from hV]; exact hU1
    · have hρ0 : ∀ i, 0 ≤ ρ i := fun i =>
        div_nonneg (mul_nonneg (hcuts a hm i) (Real.exp_pos _).le) hVpos.le
      have hρ1 : ∑ i, ρ i = 1 := by
        simp only [ρ, ← Finset.sum_div]
        have : ∑ i, a i * Real.exp (φ i) = V := hv
        rw [this]; exact div_self hVpos.ne'
      have hj := exp_jensen (x := fun i => u i - φ i) hρ0 hρ1
      have e : cutValue a u = V * ∑ i, ρ i * Real.exp (u i - φ i) := by
        simp only [cutValue, ρ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
        rw [mul_assoc, ← Real.exp_add]; ring_nf
      calc V * Real.exp (∑ i, ρ i * (u i - φ i)) ≤ V * ∑ i, ρ i * Real.exp (u i - φ i) :=
            mul_le_mul_of_nonneg_left hj hVpos.le
        _ = cutValue a u := e.symm
        _ ≤ (bestCut cuts u).1 := hUmax a hm
  set t := ∑ i, (ρ i - π i) * (u i - φ i)
  have hprod : 8 * ℓ * V * (Real.exp (t / 2)) ^ 2 ≤ 8 * lossEll c u * (bestCut cuts u).1 := by
    have e : (Real.exp (t / 2)) ^ 2 =
        Real.exp (∑ i, π i * (-(u i - φ i))) * Real.exp (∑ i, ρ i * (u i - φ i)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1
      simp only [t, ← Finset.sum_add_distrib]; push_cast
      rw [mul_div_cancel₀ _ (two_ne_zero)]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have hlu : 0 ≤ lossEll c u :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le
    have h1 := mul_le_mul hellu hVu (mul_nonneg hVpos.le (Real.exp_pos _).le) hlu
    nlinarith [h1]
  have hsq : lossL c cuts φ * Real.exp (t / 2) ≤ lossL c cuts u := by
    unfold lossL
    rw [← Real.sqrt_sq (Real.exp_pos (t / 2)).le, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hprod
  have hexp : 1 + t / 2 ≤ Real.exp (t / 2) := by linarith [Real.add_one_le_exp (t / 2)]
  have hL0 : 0 ≤ lossL c cuts φ := Real.sqrt_nonneg _
  have hgrad : ∑ i, lossGrad c cuts φ i * (u i - φ i) = lossL c cuts φ * (t / 2) := by
    simp only [lossGrad, t, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [π, ρ, ℓ, V, a]; ring
  rw [hgrad]
  nlinarith [mul_le_mul_of_nonneg_left hexp hL0]

lemma sum_sq_le_sq_sum {x : Fin d → ℝ} (hx : ∀ i, 0 ≤ x i) : ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  have h : ∀ i ∈ Finset.univ, x i ^ 2 ≤ x i * ∑ j, x j := by
    intro i _
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)) (hx i)
  calc ∑ i, x i ^ 2 ≤ ∑ i, x i * ∑ j, x j := Finset.sum_le_sum h
    _ = (∑ i, x i) ^ 2 := by rw [← Finset.sum_mul, sq]

lemma lossGrad_sq {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) {cuts : List (Fin d → ℝ)}
    (hcuts : ∀ a ∈ cuts, ∀ i, 0 ≤ a i) (φ : Fin d → ℝ) :
    ∑ i, lossGrad c cuts φ i ^ 2 ≤ lossL c cuts φ ^ 2 := by
  obtain ⟨hV1, -, hVcase⟩ := bestCut_spec cuts φ
  set ℓ := lossEll c φ
  set V := (bestCut cuts φ).1
  set a := (bestCut cuts φ).2
  have hVpos : 0 < V := by linarith
  set π : Fin d → ℝ := fun i => c i * Real.exp (-φ i) / ℓ
  set ρ : Fin d → ℝ := fun i => a i * Real.exp (φ i) / V
  have hℓ0 : 0 ≤ ℓ := Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le
  have hπ0 : ∀ i, 0 ≤ π i := fun i => div_nonneg (mul_nonneg (hc i) (Real.exp_pos _).le) hℓ0
  have hπ1 : ∑ i, π i ≤ 1 := by
    simp only [π, ← Finset.sum_div]
    change ℓ / ℓ ≤ 1
    rcases eq_or_lt_of_le hℓ0 with h | h
    · rw [← h]; simp
    · rw [div_self h.ne']
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    rcases hVcase with ⟨-, ha⟩ | ⟨hm, -⟩
    · simp [ρ, ha]
    · exact div_nonneg (mul_nonneg (hcuts a hm i) (Real.exp_pos _).le) hVpos.le
  have hρ1 : ∑ i, ρ i ≤ 1 := by
    rcases hVcase with ⟨-, ha⟩ | ⟨-, hv⟩
    · simp [ρ, ha]
    · simp only [ρ, ← Finset.sum_div]
      have : ∑ i, a i * Real.exp (φ i) = V := hv
      rw [this, div_self hVpos.ne']
  have hsq : ∑ i, (ρ i - π i) ^ 2 ≤ 4 := by
    have h1 : ∀ i, (ρ i - π i) ^ 2 ≤ (ρ i + π i) ^ 2 := by
      intro i; nlinarith [hρ0 i, hπ0 i]
    have h2 := sum_sq_le_sq_sum (x := fun i => ρ i + π i) (fun i => add_nonneg (hρ0 i) (hπ0 i))
    have h3 : ∑ i, (ρ i + π i) ≤ 2 := by rw [Finset.sum_add_distrib]; linarith
    have h4 : 0 ≤ ∑ i, (ρ i + π i) := Finset.sum_nonneg fun i _ => add_nonneg (hρ0 i) (hπ0 i)
    calc ∑ i, (ρ i - π i) ^ 2 ≤ ∑ i, (ρ i + π i) ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ ≤ (∑ i, (ρ i + π i)) ^ 2 := h2
      _ ≤ 4 := by nlinarith
  have e : ∑ i, lossGrad c cuts φ i ^ 2 = (lossL c cuts φ / 2) ^ 2 * ∑ i, (ρ i - π i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lossGrad, π, ρ, ℓ, V, a]; ring
  rw [e]
  nlinarith [sq_nonneg (lossL c cuts φ)]

lemma lossL_band {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) {cuts : List (Fin d → ℝ)}
    (hcuts : ∀ a ∈ cuts, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ 4 * d) (hd : 1 ≤ (d : ℝ))
    {φ : Fin d → ℝ} (hlo : ∀ i, Real.exp (-φ i) ≤ 4 * d) (hhi : ∀ i, Real.exp (φ i) ≤ 1 / 2) :
    lossL c cuts φ ≤ 8 * d * Real.sqrt (∑ i, c i) := by
  have hℓ : lossEll c φ ≤ 4 * d * ∑ i, c i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_comm (4 * (d : ℝ))]; exact mul_le_mul_of_nonneg_left (hlo i) (hc i)
  have hV : (bestCut cuts φ).1 ≤ 2 * d := by
    apply bestCut_le cuts φ (by linarith)
    intro a ha
    obtain ⟨ha0, has⟩ := hcuts a ha
    have : cutValue a φ ≤ (∑ i, a i) / 2 := by
      rw [cutValue, Finset.sum_div]
      exact Finset.sum_le_sum fun i _ => by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (hhi i) (ha0 i)
    linarith
  have hℓ0 : 0 ≤ lossEll c φ := Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have h8 : 8 * lossEll c φ * (bestCut cuts φ).1 ≤ (8 * d * Real.sqrt (∑ i, c i)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc0]
    have hV1 := (bestCut_spec cuts φ).1
    nlinarith [mul_le_mul hℓ hV (by linarith) (by positivity)]
  unfold lossL
  calc Real.sqrt (8 * lossEll c φ * (bestCut cuts φ).1)
      ≤ Real.sqrt ((8 * d * Real.sqrt (∑ i, c i)) ^ 2) := Real.sqrt_le_sqrt h8
    _ = 8 * d * Real.sqrt (∑ i, c i) := Real.sqrt_sq (by positivity)

lemma lossL_comparator {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) {cuts : List (Fin d → ℝ)}
    {r u : Fin d → ℝ} (hr : ∀ i, 0 < r i)
    (hcuts : ∀ a ∈ cuts, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ 4 * d ∧ ∑ i, a i * r i ≤ 1)
    (hd : 1 ≤ (d : ℝ)) (hu1 : ∀ i, r i ≤ Real.exp (u i))
    (hu2 : ∀ i, Real.exp (u i) ≤ r i + 1 / (4 * d)) :
    lossL c cuts u ≤ Real.sqrt (16 * ∑ i, c i / r i) := by
  have hℓ : lossEll c u ≤ ∑ i, c i / r i := by
    apply Finset.sum_le_sum; intro i _
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (hc i) (hr i) (hu1 i)
  have hV : (bestCut cuts u).1 ≤ 2 := by
    apply bestCut_le cuts u (by norm_num)
    intro a ha
    obtain ⟨ha0, has, har⟩ := hcuts a ha
    have h1 : cutValue a u ≤ ∑ i, a i * (r i + 1 / (4 * d)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu2 i) (ha0 i)
    have h2 : ∑ i, a i * (r i + 1 / (4 * d)) = ∑ i, a i * r i + (∑ i, a i) / (4 * d) := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h3 : (∑ i, a i) / (4 * d) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact has
    linarith
  have hℓ0 : 0 ≤ lossEll c u := Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le
  have hV1 := (bestCut_spec cuts u).1
  unfold lossL
  apply Real.sqrt_le_sqrt
  nlinarith [mul_le_mul hℓ hV (by linarith) (by linarith [hℓ0, hℓ])]

end OracleTemplate.OnlineMetricAccelerated
