import LongTails.Proofs.FiniteScaleConvolutionalSgdDrift

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdTrajectory

open LongTails.Proofs.ManySampleConvolutionalPerceptronDynamics (State)
open FiniteScaleConvolutionalSgdDynamics

lemma readout_step_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w A B : ℝ) (p r : E) (x : State E)
    (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (ha : |x.a| ≤ A) (ht : |x.t| ≤ B) :
    ‖(weightedNext c δ w p r x).z‖ ≤ ‖x.z‖ + A + B := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hB : 0 ≤ B := (abs_nonneg _).trans ht
  have hn : ‖x.a • p + x.t • r‖ ≤ A + B := by
    calc
      _ ≤ ‖x.a • p‖ + ‖x.t • r‖ := norm_add_le _ _
      _ = |x.a| * ‖p‖ + |x.t| * ‖r‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ A * 1 + B * 1 := by gcongr
      _ = _ := by ring
  change ‖x.z + w • (x.a • p + x.t • r)‖ ≤ _
  calc
    _ ≤ ‖x.z‖ + ‖w • (x.a • p + x.t • r)‖ := norm_add_le _ _
    _ = ‖x.z‖ + w * ‖x.a • p + x.t • r‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    _ ≤ ‖x.z‖ + 1 * (A + B) := by gcongr
    _ = _ := by ring

lemma difference_step_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w H : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hr : |⟪r, x.z⟫| ≤ H) :
    |(weightedNext c δ w p r x).t - x.t| ≤ δ * H := by
  change |x.t + δ * w * ⟪r, x.z⟫ - x.t| ≤ _
  rw [add_sub_cancel_left, abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg hw]
  calc
    _ ≤ δ * 1 * H := by gcongr
    _ = _ := by ring

lemma early_mean_step_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w H ζ : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hcu : |c| ≤ 1 / 4)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ δ * H) (hdH : δ * H ≤ 1)
    (hp : |⟪p, x.z⟫| ≤ H) (hr : |⟪r, x.z⟫| ≤ H)
    (ht : |x.t| ≤ 2) (hW : meanPotential x ≤ 4)
    (hgate : w * (c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫) ≤ ζ) :
    meanPotential (weightedNext c δ w p r x) ≤ meanPotential x + 44 * δ * H := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hp
  have hd : 0 ≤ δ * H := mul_nonneg hδ hH
  have hs : Real.sqrt (meanPotential x) ≤ 2 := by
    nlinarith [Real.sq_sqrt (mean_potential_nonneg x), Real.sqrt_nonneg (meanPotential x)]
  have hfirst : δ * H * w * Real.sqrt (meanPotential x) ≤ 2 * (δ * H) := by
    calc
      _ ≤ δ * H * 1 * 2 := by gcongr
      _ = _ := by ring
  have hsecond : δ * H * w ≤ δ * H := mul_le_of_le_one_right hd hw₁
  have hthird : δ ^ 2 * H ^ 2 * w ^ 2 ≤ δ * H := by
    calc
      _ = (δ * H * w) ^ 2 := by ring
      _ ≤ (δ * H) ^ 2 := by gcongr
      _ ≤ δ * H := by nlinarith
  have hh := soft_mean_drift c δ w 0 H ζ p r x hδ hw hw₁ le_rfl
    (abs_nonneg c) hcu hζ hp hr ht hgate
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div, sub_zero] at hh
  nlinarith

lemma early_path_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E) (δ H ζ : ℝ) (T : ℕ)
    (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ) (hζH : ζ ≤ δ * H)
    (hH : H = 4 * (T : ℝ) + 1) (hsmall : δ * H * (T : ℝ) ≤ 1 / 100)
    (hdH : δ * H ≤ 1)
    (hW₀ : meanPotential (x 0) ≤ 3) (ht₀ : 1 ≤ (x 0).t ∧ (x 0).t ≤ 3 / 2)
    (hz₀ : ‖(x 0).z‖ ≤ 1)
    (hstep : ∀ k < T, x (k + 1) = weightedNext (c k) δ (w k) (p k) (r k) (x k))
    (hw : ∀ k < T, 0 ≤ w k ∧ w k ≤ 1)
    (hc : ∀ k < T, |c k| ≤ 1 / 4)
    (hp : ∀ k < T, ‖p k‖ ≤ 1) (hr : ∀ k < T, ‖r k‖ ≤ 1)
    (hgate : ∀ k < T, w k * (c k * (x k).a * (x k).q +
      δ * ⟪(x k).a • p k + (x k).t • r k, (x k).z⟫) ≤ ζ) :
    ∀ k ≤ T, meanPotential (x k) ≤ 3 + 44 * δ * H * (k : ℝ) ∧
      |(x k).t - (x 0).t| ≤ δ * H * (k : ℝ) ∧ ‖(x k).z‖ ≤ 1 + 4 * (k : ℝ) := by
  have hH₀ : 0 ≤ H := by rw [hH]; positivity
  have hd : 0 ≤ δ * H := mul_nonneg hδ hH₀
  intro k
  induction k with
  | zero =>
    intro _
    simpa using And.intro hW₀ (And.intro (le_refl (0 : ℝ)) hz₀)
  | succ k ih =>
    intro hk
    have hkT : k < T := Nat.lt_of_succ_le hk
    obtain ⟨hWk, htk, hzk⟩ := ih (Nat.le_of_lt hkT)
    have hcast : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.le_of_lt hkT
    have hdk : δ * H * (k : ℝ) ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_left hcast hd).trans hsmall
    have hW : meanPotential (x k) ≤ 4 := by nlinarith
    have ht : |(x k).t| ≤ 2 := by
      have htd := abs_le.mp htk
      rw [abs_le]
      constructor <;> linarith [ht₀.1, ht₀.2]
    have hz : ‖(x k).z‖ ≤ H := by rw [hH]; linarith
    have hpi : |⟪p k, (x k).z⟫| ≤ H := by
      calc
        _ ≤ ‖p k‖ * ‖(x k).z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * H := by gcongr; exact hp k hkT
        _ = H := one_mul H
    have hri : |⟪r k, (x k).z⟫| ≤ H := by
      calc
        _ ≤ ‖r k‖ * ‖(x k).z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * H := by gcongr; exact hr k hkT
        _ = H := one_mul H
    obtain ⟨hw₀, hw₁⟩ := hw k hkT
    have hmean := early_mean_step_bound (c k) δ (w k) H ζ (p k) (r k) (x k)
      hδ hw₀ hw₁ (hc k hkT) hζ hζH hdH hpi hri ht hW (hgate k hkT)
    have hdiff := difference_step_bound (c k) δ (w k) H (p k) (r k) (x k)
      hδ hw₀ hw₁ hri
    have ha : |(x k).a| ≤ 2 := by
      have hcoord := (mean_coordinate_bound (x k)).1
      have hs := Real.sq_sqrt (mean_potential_nonneg (x k))
      have hn := Real.sqrt_nonneg (meanPotential (x k))
      nlinarith
    have hnorm := readout_step_bound (c k) δ (w k) 2 2 (p k) (r k) (x k)
      hw₀ hw₁ (hp k hkT) (hr k hkT) ha ht
    rw [← hstep k hkT] at hmean hdiff hnorm
    have htri : |(x (k + 1)).t - (x 0).t| ≤
        |(x (k + 1)).t - (x k).t| + |(x k).t - (x 0).t| := abs_sub_le _ _ _
    simp only [Nat.cast_add, Nat.cast_one]
    exact ⟨by nlinarith, by nlinarith, by linarith⟩

lemma late_mean_step_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w H ζ A : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hcu : |c| ≤ 1 / 4)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ δ * H) (hdH : δ * H ≤ 1)
    (hp : |⟪p, x.z⟫| ≤ H) (hr : |⟪r, x.z⟫| ≤ H)
    (ht : |x.t| ≤ 2) (hA : 0 ≤ A) (hA₁ : A ≤ 1 / 1000)
    (hW : meanPotential x ≤ A ^ 2)
    (hgate : w * (c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫) ≤ ζ) :
    meanPotential (weightedNext c δ w p r x) ≤ meanPotential x + 30 * δ * H := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hp
  have hd : 0 ≤ δ * H := mul_nonneg hδ hH
  have hs : Real.sqrt (meanPotential x) ≤ 1 / 1000 := by
    nlinarith [Real.sq_sqrt (mean_potential_nonneg x), Real.sqrt_nonneg (meanPotential x)]
  have hfirst : δ * H * w * Real.sqrt (meanPotential x) ≤ δ * H / 1000 := by
    calc
      _ ≤ δ * H * 1 * (1 / 1000) := by gcongr
      _ = _ := by ring
  have hsecond : δ * H * w ≤ δ * H := mul_le_of_le_one_right hd hw₁
  have hthird : δ ^ 2 * H ^ 2 * w ^ 2 ≤ δ * H := by
    calc
      _ = (δ * H * w) ^ 2 := by ring
      _ ≤ (δ * H) ^ 2 := by gcongr
      _ ≤ δ * H := by nlinarith
  have hh := soft_mean_drift c δ w 0 H ζ p r x hδ hw hw₁ le_rfl
    (abs_nonneg c) hcu hζ hp hr ht hgate
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div, sub_zero] at hh
  nlinarith

lemma separator_step_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w κ A : ℝ) (p r v : E) (x : State E)
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hv : ‖v‖ ≤ 1) (hp : ‖p‖ ≤ 1)
    (hr : κ ≤ ⟪v, r⟫) (ha : |x.a| ≤ A) (ht : 1 / 2 ≤ x.t) :
    ⟪v, x.z⟫ + (κ / 2 - A) * w ≤ ⟪v, (weightedNext c δ w p r x).z⟫ := by
  have hpv : |⟪v, p⟫| ≤ 1 := by
    calc
      _ ≤ ‖v‖ * ‖p‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hap : -A ≤ x.a * ⟪v, p⟫ := by
    have hh : |x.a * ⟪v, p⟫| ≤ A := by
      rw [abs_mul]
      calc
        _ ≤ |x.a| * 1 := by gcongr
        _ ≤ A := by simpa using ha
    exact (abs_le.mp hh).1
  have htr : κ / 2 ≤ x.t * ⟪v, r⟫ := by
    calc
      _ = (1 / 2) * κ := by ring
      _ ≤ x.t * ⟪v, r⟫ := mul_le_mul ht hr hκ (by linarith)
  have hh := mul_le_mul_of_nonneg_right (add_le_add hap htr) hw
  simp only [weightedNext, inner_add_right, inner_smul_right]
  nlinarith

lemma cumulative_work_bound (E D Q X U : ℕ → ℝ) (b : ℝ) (n : ℕ)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) (hE : 0 ≤ E n) (hD : 0 ≤ D n)
    (hQ : ∀ k < n, 0 ≤ Q k) (hU : ∀ k < n, 0 ≤ U k)
    (henergy : ∀ k < n, E (k + 1) - E k ≤ 4 * X k + Q k + U k)
    (hwork : ∀ k < n, Q k ≤ 2 * b * |X k| + (D k - D (k + 1)) + U k) :
    (∑ k ∈ Finset.range n, Q k) ≤
      8 * b * (∑ k ∈ Finset.range n, max (X k) 0) +
      3 * (∑ k ∈ Finset.range n, U k) + b * E 0 + 2 * D 0 := by
  have he := Finset.sum_le_sum (fun k hk => henergy k (Finset.mem_range.mp hk))
  have hd := Finset.sum_le_sum (fun k hk => hwork k (Finset.mem_range.mp hk))
  rw [Finset.sum_range_sub] at he
  simp only [Finset.sum_add_distrib] at he hd
  rw [Finset.sum_range_sub'] at hd
  have hx : (∑ k ∈ Finset.range n, X k) =
      (∑ k ∈ Finset.range n, max (X k) 0) -
      (∑ k ∈ Finset.range n, max (-X k) 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rcases le_total 0 (X k) with hh | hh
    · rw [max_eq_left hh, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right hh, max_eq_left (by linarith)]
      ring
  have ha : (∑ k ∈ Finset.range n, |X k|) =
      (∑ k ∈ Finset.range n, max (X k) 0) +
      (∑ k ∈ Finset.range n, max (-X k) 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rcases le_total 0 (X k) with hh | hh
    · rw [abs_of_nonneg hh, max_eq_left hh, max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos hh, max_eq_right hh, max_eq_left (by linarith)]
      ring
  simp only [← Finset.mul_sum] at he hd
  rw [hx] at he
  rw [ha] at hd
  apply SoftQuadraticDynamics.cumulative_mean_discretization_bound b _ _
    (∑ k ∈ Finset.range n, max (-X k) 0) _ _ _ hb hb₁
    (Finset.sum_nonneg (fun k hk => hQ k (Finset.mem_range.mp hk)))
    (Finset.sum_nonneg (fun k hk => hU k (Finset.mem_range.mp hk)))
  · linarith
  · linarith

lemma discretization_step_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w b : ℝ) (p r : E) (x : State E)
    (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hb : b ≤ 1) (hc : |c| ≤ b) :
    (c * w) ^ 2 * meanEnergy x ≤ 2 * b * |c * w * x.a * x.q| +
      (|imbalance x| - |imbalance (weightedNext c δ w p r x)|) + |forcing c δ w p x| := by
  have hcw : |c * w| ≤ b := by
    rw [abs_mul, abs_of_nonneg hw]
    exact (mul_le_of_le_one_right (abs_nonneg c) hw₁).trans hc
  have hs : (c * w) ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (abs_nonneg (c * w)) (show (0 : ℝ) ≤ 1 by norm_num)).2
      (hcw.trans hb)
    simpa only [sq_abs, one_pow] using hh
  have hid : imbalance (weightedNext c δ w p r x) =
      (1 - (c * w) ^ 2) * imbalance x + forcing c δ w p x := by
    rw [imbalance_step]
    unfold forcing
    ring
  have hD : |imbalance (weightedNext c δ w p r x)| ≤
      (1 - (c * w) ^ 2) * |imbalance x| + |forcing c δ w p x| := by
    rw [hid]
    exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_of_nonneg (by linarith)])
  have hprod : (c * w) ^ 2 * |x.a * x.q| ≤ b * |c * w * x.a * x.q| := by
    calc
      _ = |c * w| ^ 2 * |x.a * x.q| := by rw [sq_abs]
      _ = |c * w| * |c * w * x.a * x.q| := by simp only [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcw (abs_nonneg _)
  have hE := SoftQuadraticDynamics.mean_energy_bound x.a x.q
  change meanEnergy x ≤ 2 * |x.a * x.q| + |imbalance x| at hE
  have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg (c * w))
  nlinarith

lemma cumulative_discretization_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E)
    (δ b : ℝ) (n : ℕ) (hb : 0 ≤ b) (hb₁ : b ≤ 1)
    (hstep : ∀ k < n, x (k + 1) = weightedNext (c k) δ (w k) (p k) (r k) (x k))
    (hw : ∀ k < n, 0 ≤ w k ∧ w k ≤ 1) (hc : ∀ k < n, |c k| ≤ b) :
    (∑ k ∈ Finset.range n, (c k * w k) ^ 2 * meanEnergy (x k)) ≤
      8 * b * (∑ k ∈ Finset.range n, max (c k * w k * (x k).a * (x k).q) 0) +
      3 * (∑ k ∈ Finset.range n, |forcing (c k) δ (w k) (p k) (x k)|) +
      b * meanEnergy (x 0) + 2 * |imbalance (x 0)| := by
  apply cumulative_work_bound (fun k => meanEnergy (x k)) (fun k => |imbalance (x k)|)
    (fun k => (c k * w k) ^ 2 * meanEnergy (x k))
    (fun k => c k * w k * (x k).a * (x k).q)
    (fun k => |forcing (c k) δ (w k) (p k) (x k)|) b n hb hb₁
  · unfold meanEnergy
    positivity
  · exact abs_nonneg _
  · intro k _
    unfold meanEnergy
    positivity
  · intro k _
    exact abs_nonneg _
  · intro k hk
    rw [hstep k hk, mean_energy_step]
    have hf := le_abs_self (forcing (c k) δ (w k) (p k) (x k))
    unfold forcing at hf ⊢
    nlinarith
  · intro k hk
    rw [hstep k hk]
    exact discretization_step_bound (c k) δ (w k) b (p k) (r k) (x k)
      (hw k hk).1 (hw k hk).2 hb₁ (hc k hk)

lemma positive_work_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w A H ζ : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hζ : 0 ≤ ζ)
    (hp : |⟪p, x.z⟫| ≤ H) (hr : |⟪r, x.z⟫| ≤ H)
    (ha : |x.a| ≤ A) (ht : |x.t| ≤ 2)
    (hgate : w * (c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫) ≤ ζ) :
    max (c * w * x.a * x.q) 0 ≤ ζ + δ * w * H * (A + 2) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hp
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hres : |⟪x.a • p + x.t • r, x.z⟫| ≤ H * (A + 2) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc
      _ ≤ |x.a * ⟪p, x.z⟫| + |x.t * ⟪r, x.z⟫| := abs_add_le _ _
      _ = |x.a| * |⟪p, x.z⟫| + |x.t| * |⟪r, x.z⟫| := by rw [abs_mul, abs_mul]
      _ ≤ A * H + 2 * H := by gcongr
      _ = _ := by ring
  apply max_le
  · have hh := mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hres) (mul_nonneg hδ hw)
    nlinarith
  · positivity

lemma coupled_readout_step_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c δ w b A H ζ : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hb : 0 ≤ b) (hc : |c| ≤ b)
    (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) (hz : ‖x.z‖ ≤ H)
    (ha : |x.a| ≤ A) (hq : |x.q| ≤ A) (ht : |x.t| ≤ 2)
    (hgate : w * (c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫) ≤ ζ) :
    2 * δ * ‖(weightedNext c δ w p r x).z‖ ^ 2 + meanEnergy (weightedNext c δ w p r x) ≤
      2 * δ * ‖x.z‖ ^ 2 + meanEnergy x + 4 * ζ +
        2 * δ * w * (1 + b) * A * H + (c * w) ^ 2 * meanEnergy x +
        δ ^ 2 * w ^ 2 * H ^ 2 + 2 * δ * w ^ 2 * (A + 2) ^ 2 := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hH : 0 ≤ H := (norm_nonneg _).trans hz
  have hpi : |⟪p, x.z⟫| ≤ H := by
    calc
      _ ≤ ‖p‖ * ‖x.z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * H := by gcongr
      _ = H := one_mul H
  have hcq : |c * w * x.q| ≤ b * A := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ b * 1 * A := by gcongr
      _ = _ := by ring
  have haq : |x.a + c * w * x.q| ≤ (1 + b) * A := by
    have hh := abs_add_le x.a (c * w * x.q)
    nlinarith
  have hcross : (x.a + c * w * x.q) * ⟪p, x.z⟫ ≤ (1 + b) * A * H := by
    calc
      _ ≤ |(x.a + c * w * x.q) * ⟪p, x.z⟫| := le_abs_self _
      _ = |x.a + c * w * x.q| * |⟪p, x.z⟫| := abs_mul _ _
      _ ≤ _ := by gcongr
  have hs : ⟪p, x.z⟫ ^ 2 ≤ H ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hH).2 hpi
  have hn : ‖x.a • p + x.t • r‖ ≤ A + 2 := by
    calc
      _ ≤ ‖x.a • p‖ + ‖x.t • r‖ := norm_add_le _ _
      _ = |x.a| * ‖p‖ + |x.t| * ‖r‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ A * 1 + 2 * 1 := by gcongr
      _ = _ := by ring
  have hn₂ := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ A + 2 by positivity)).2 hn
  rw [coupled_readout_identity]
  have h₁ := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 * δ * w by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hs (show 0 ≤ δ ^ 2 * w ^ 2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hn₂ (show 0 ≤ 2 * δ * w ^ 2 by positivity)
  nlinarith

lemma cumulative_readout_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E)
    (δ b A H ζ : ℝ) (n : ℕ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hstep : ∀ k < n, x (k + 1) = weightedNext (c k) δ (w k) (p k) (r k) (x k))
    (hw : ∀ k < n, 0 ≤ w k ∧ w k ≤ 1) (hc : ∀ k < n, |c k| ≤ b)
    (hp : ∀ k < n, ‖p k‖ ≤ 1) (hr : ∀ k < n, ‖r k‖ ≤ 1)
    (hz : ∀ k < n, ‖(x k).z‖ ≤ H)
    (ha : ∀ k < n, |(x k).a| ≤ A) (hq : ∀ k < n, |(x k).q| ≤ A)
    (ht : ∀ k < n, |(x k).t| ≤ 2)
    (hgate : ∀ k < n, w k * (c k * (x k).a * (x k).q +
      δ * ⟪(x k).a • p k + (x k).t • r k, (x k).z⟫) ≤ ζ) :
    2 * δ * ‖(x n).z‖ ^ 2 ≤ 2 * δ * ‖(x 0).z‖ ^ 2 + meanEnergy (x 0) +
      4 * (n : ℝ) * ζ +
      (2 * δ * (1 + b) * A * H + δ ^ 2 * H ^ 2 + 2 * δ * (A + 2) ^ 2) *
        (∑ k ∈ Finset.range n, w k) +
      (∑ k ∈ Finset.range n, (c k * w k) ^ 2 * meanEnergy (x k)) := by
  have hlocal : ∀ k ∈ Finset.range n,
      (2 * δ * ‖(x (k + 1)).z‖ ^ 2 + meanEnergy (x (k + 1))) -
        (2 * δ * ‖(x k).z‖ ^ 2 + meanEnergy (x k)) ≤ 4 * ζ +
      (2 * δ * (1 + b) * A * H + δ ^ 2 * H ^ 2 + 2 * δ * (A + 2) ^ 2) * w k +
      (c k * w k) ^ 2 * meanEnergy (x k) := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have hh := coupled_readout_step_bound (c k) δ (w k) b A H ζ (p k) (r k) (x k)
      hδ (hw k hkn).1 (hw k hkn).2 hb (hc k hkn) (hp k hkn) (hr k hkn)
      (hz k hkn) (ha k hkn) (hq k hkn) (ht k hkn) (hgate k hkn)
    rw [← hstep k hkn] at hh
    have hw₂ : (w k) ^ 2 ≤ w k := by nlinarith [(hw k hkn).1, (hw k hkn).2]
    have h₁ := mul_le_mul_of_nonneg_left hw₂ (show 0 ≤ δ ^ 2 * H ^ 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hw₂ (show 0 ≤ 2 * δ * (A + 2) ^ 2 by positivity)
    nlinarith
  have hh := Finset.sum_le_sum hlocal
  rw [Finset.sum_range_sub (fun k => 2 * δ * ‖(x k).z‖ ^ 2 + meanEnergy (x k))] at hh
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  have hEn : 0 ≤ meanEnergy (x n) := by unfold meanEnergy; positivity
  nlinarith

lemma cumulative_perturbation_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E)
    (δ b A H ζ : ℝ) (n : ℕ) (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hH : 0 ≤ H) (hζ : 0 ≤ ζ)
    (hw : ∀ k < n, 0 ≤ w k ∧ w k ≤ 1) (hc : ∀ k < n, |c k| ≤ b)
    (hp : ∀ k < n, |⟪p k, (x k).z⟫| ≤ H)
    (hr : ∀ k < n, |⟪r k, (x k).z⟫| ≤ H)
    (ha : ∀ k < n, |(x k).a| ≤ A) (hq : ∀ k < n, |(x k).q| ≤ A)
    (ht : ∀ k < n, |(x k).t| ≤ 2)
    (hgate : ∀ k < n, w k * (c k * (x k).a * (x k).q +
      δ * ⟪(x k).a • p k + (x k).t • r k, (x k).z⟫) ≤ ζ) :
    (∑ k ∈ Finset.range n, max (c k * w k * (x k).a * (x k).q) 0) ≤
      (n : ℝ) * ζ + δ * H * (A + 2) * (∑ k ∈ Finset.range n, w k) ∧
    (∑ k ∈ Finset.range n, |forcing (c k) δ (w k) (p k) (x k)|) ≤
      (2 * δ * H * (1 + b) * A + δ ^ 2 * H ^ 2) * (∑ k ∈ Finset.range n, w k) := by
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.range n) (fun k hk =>
      positive_work_bound (c k) δ (w k) A H ζ (p k) (r k) (x k) hδ
        (hw k (Finset.mem_range.mp hk)).1 hζ (hp k (Finset.mem_range.mp hk))
        (hr k (Finset.mem_range.mp hk)) (ha k (Finset.mem_range.mp hk))
        (ht k (Finset.mem_range.mp hk)) (hgate k (Finset.mem_range.mp hk)))
    have he : (∑ k ∈ Finset.range n, (ζ + δ * w k * H * (A + 2))) =
        (n : ℝ) * ζ + δ * H * (A + 2) * (∑ k ∈ Finset.range n, w k) := by
      calc
        _ = ∑ k ∈ Finset.range n, (ζ + (δ * H * (A + 2)) * w k) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← Finset.mul_sum]
    exact hh.trans_eq he
  · have hlocal : ∀ k ∈ Finset.range n, |forcing (c k) δ (w k) (p k) (x k)| ≤
        (2 * δ * H * (1 + b) * A + δ ^ 2 * H ^ 2) * w k := by
      intro k hk
      have hkn := Finset.mem_range.mp hk
      have hh := forcing_bound (c k) δ (w k) b A H (p k) (x k) hδ
        (hw k hkn).1 (hw k hkn).2 hb hH (hc k hkn) (ha k hkn) (hq k hkn) (hp k hkn)
      have hw₂ : (w k) ^ 2 ≤ w k := by nlinarith [(hw k hkn).1, (hw k hkn).2]
      have hs := mul_le_mul_of_nonneg_left hw₂ (show 0 ≤ δ ^ 2 * H ^ 2 by positivity)
      nlinarith
    have hh := Finset.sum_le_sum hlocal
    simpa only [← Finset.mul_sum] using hh

lemma cumulative_separator_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E)
    (v : E) (δ κ A : ℝ) (n : ℕ) (hκ : 0 ≤ κ) (hv : ‖v‖ ≤ 1)
    (hstep : ∀ k < n, x (k + 1) = weightedNext (c k) δ (w k) (p k) (r k) (x k))
    (hw : ∀ k < n, 0 ≤ w k) (hp : ∀ k < n, ‖p k‖ ≤ 1)
    (hr : ∀ k < n, κ ≤ ⟪v, r k⟫)
    (ha : ∀ k < n, |(x k).a| ≤ A) (ht : ∀ k < n, 1 / 2 ≤ (x k).t) :
    ⟪v, (x 0).z⟫ + (κ / 2 - A) * (∑ k ∈ Finset.range n, w k) ≤ ⟪v, (x n).z⟫ := by
  have hlocal : ∀ k ∈ Finset.range n,
      (κ / 2 - A) * w k ≤ ⟪v, (x (k + 1)).z⟫ - ⟪v, (x k).z⟫ := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have hh := separator_step_bound (c k) δ (w k) κ A (p k) (r k) v (x k)
      (hw k hkn) hκ hv (hp k hkn) (hr k hkn) (ha k hkn) (ht k hkn)
    rw [← hstep k hkn] at hh
    linarith
  have hh := Finset.sum_le_sum hlocal
  rw [Finset.sum_range_sub (fun k => ⟪v, (x k).z⟫), ← Finset.mul_sum] at hh
  linarith

lemma late_readout_algebra (δ b A H ζ S n E D F Z Z₀ Q X U : ℝ)
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hb₁ : b ≤ 1 / 4)
    (hA : 0 ≤ A) (hA₁ : A ≤ 1) (hH : 0 ≤ H) (hζ : 0 ≤ ζ)
    (hS : 0 ≤ S) (hn : 0 ≤ n) (hE : 0 ≤ E) (hD : 0 ≤ D) (hF : E + 2 * D ≤ F)
    (hX : X ≤ n * ζ + δ * H * (A + 2) * S)
    (hU : U ≤ (2 * δ * H * (1 + b) * A + δ ^ 2 * H ^ 2) * S)
    (hQ : Q ≤ 8 * b * X + 3 * U + b * E + 2 * D)
    (hZ : 2 * δ * Z ≤ 2 * δ * Z₀ + E + 4 * n * ζ +
      (2 * δ * (1 + b) * A * H + δ ^ 2 * H ^ 2 + 2 * δ * (A + 2) ^ 2) * S + Q) :
    2 * δ * Z ≤ 2 * δ * Z₀ + 4 * F + 6 * n * ζ +
      2 * δ * ((12 * b + 6 * A + 2 * δ * H) * H * S + 9 * S) := by
  have hXb := mul_le_mul_of_nonneg_left hX (show 0 ≤ 8 * b by positivity)
  have hinit : (1 + b) * E + 2 * D ≤ 4 * F := by
    have hh := mul_le_mul_of_nonneg_right hb₁ hE
    nlinarith
  have hthermal : (4 + 8 * b) * (n * ζ) ≤ 6 * n * ζ := by
    have hh := mul_le_mul_of_nonneg_right hb₁ (show 0 ≤ n * ζ by positivity)
    nlinarith
  have hcoef : 8 * (1 + b) * A + 8 * b * (A + 2) ≤ 24 * b + 12 * A := by
    have hh := mul_le_mul_of_nonneg_right hb₁ hA
    nlinarith
  have hcoefmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ δ * H * S by positivity)
  have hnorm : (A + 2) ^ 2 ≤ 9 := by nlinarith
  have hnormmul := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * δ * S by positivity)
  nlinarith

lemma late_prefix_energy_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E)
    (δ b A H ζ F : ℝ) (n : ℕ) (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hb₁ : b ≤ 1 / 4)
    (hA : 0 ≤ A) (hA₁ : A ≤ 1) (hH : 0 ≤ H) (hζ : 0 ≤ ζ)
    (hF : meanPotential (x 0) ≤ F)
    (hstep : ∀ k < n, x (k + 1) = weightedNext (c k) δ (w k) (p k) (r k) (x k))
    (hw : ∀ k < n, 0 ≤ w k ∧ w k ≤ 1) (hc : ∀ k < n, |c k| ≤ b)
    (hp : ∀ k < n, ‖p k‖ ≤ 1) (hr : ∀ k < n, ‖r k‖ ≤ 1)
    (hz : ∀ k < n, ‖(x k).z‖ ≤ H)
    (ha : ∀ k < n, |(x k).a| ≤ A) (hq : ∀ k < n, |(x k).q| ≤ A)
    (ht : ∀ k < n, |(x k).t| ≤ 2)
    (hgate : ∀ k < n, w k * (c k * (x k).a * (x k).q +
      δ * ⟪(x k).a • p k + (x k).t • r k, (x k).z⟫) ≤ ζ) :
    2 * δ * ‖(x n).z‖ ^ 2 ≤ 2 * δ * ‖(x 0).z‖ ^ 2 + 4 * F + 6 * (n : ℝ) * ζ +
      2 * δ * ((12 * b + 6 * A + 2 * δ * H) * H * (∑ k ∈ Finset.range n, w k) +
        9 * (∑ k ∈ Finset.range n, w k)) := by
  have hpi : ∀ k < n, |⟪p k, (x k).z⟫| ≤ H := by
    intro k hk
    calc
      _ ≤ ‖p k‖ * ‖(x k).z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * H := by gcongr; exact hp k hk; exact hz k hk
      _ = H := one_mul H
  have hri : ∀ k < n, |⟪r k, (x k).z⟫| ≤ H := by
    intro k hk
    calc
      _ ≤ ‖r k‖ * ‖(x k).z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * H := by gcongr; exact hr k hk; exact hz k hk
      _ = H := one_mul H
  obtain ⟨hX, hU⟩ := cumulative_perturbation_bound x c w p r δ b A H ζ n
    hδ hb hH hζ hw hc hpi hri ha hq ht hgate
  have hQ := cumulative_discretization_bound x c w p r δ b n hb
    (show b ≤ 1 by linarith) hstep hw hc
  have hZ := cumulative_readout_bound x c w p r δ b A H ζ n hδ hb hstep hw hc
    hp hr hz ha hq ht hgate
  exact late_readout_algebra δ b A H ζ (∑ k ∈ Finset.range n, w k) n
    (meanEnergy (x 0)) |imbalance (x 0)| F (‖(x n).z‖ ^ 2) (‖(x 0).z‖ ^ 2) _ _ _
    hδ hb hb₁ hA hA₁ hH hζ (Finset.sum_nonneg (fun k hk => (hw k (Finset.mem_range.mp hk)).1))
    (by positivity) (by unfold meanEnergy; positivity) (abs_nonneg _) hF hX hU hQ hZ

lemma radius_bound_algebra (δ κ b A H H₀ F ζ n S Z : ℝ)
    (hδ : 0 < δ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1 / 4)
    (hb : b ≤ κ / 1000) (hA : A ≤ κ / 1000) (hdH : δ * H ≤ κ / 1000)
    (hH₀ : 0 ≤ H₀) (hH₀H : H₀ ≤ H / 10) (hH : 1000 ≤ κ * H)
    (hF : 2 * F ≤ δ * H ^ 2 / 100) (hthermal : n * ζ ≤ δ)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hover : Z ≤ H + 3)
    (hproj : κ / 3 * S ≤ Z + H₀)
    (henergy : 2 * δ * Z ^ 2 ≤ 2 * δ * H₀ ^ 2 + 4 * F + 6 * n * ζ +
      2 * δ * ((12 * b + 6 * A + 2 * δ * H) * H * S + 9 * S)) :
    Z < H := by
  have hHpos : 0 < H := by nlinarith
  have hHlarge : 4000 ≤ H := by nlinarith
  have hmass : κ * S ≤ 9 * H := by nlinarith
  have hcoeff : (12 * b + 6 * A + 2 * δ * H) * H + 9 ≤ 29 * κ * H / 1000 := by
    have hh : 12 * b + 6 * A + 2 * δ * H ≤ κ / 50 := by linarith
    have hm := mul_le_mul_of_nonneg_right hh hHpos.le
    nlinarith
  have hwork : ((12 * b + 6 * A + 2 * δ * H) * H + 9) * S ≤ 261 * H ^ 2 / 1000 := by
    have hh := mul_le_mul_of_nonneg_right hcoeff hS
    have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 29 * H / 1000 by positivity)
    nlinarith
  have hinit : H₀ ^ 2 ≤ H ^ 2 / 100 := by nlinarith
  have hini := mul_le_mul_of_nonneg_left hinit (show 0 ≤ 2 * δ by positivity)
  have hwo := mul_le_mul_of_nonneg_left hwork (show 0 ≤ 2 * δ by positivity)
  have hscale : 6 * δ ≤ δ * H ^ 2 / 100 := by
    have hh : 600 ≤ H ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh hδ.le
    nlinarith
  have hstrict : 2 * δ * Z ^ 2 < 2 * δ * H ^ 2 := by
    have hh : 0 < δ * H ^ 2 := by positivity
    nlinarith
  have hs : Z ^ 2 < H ^ 2 := by nlinarith
  nlinarith

lemma late_path_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℕ → State E) (c w : ℕ → ℝ) (p r : ℕ → E) (v : E)
    (δ κ b A H H₀ F ζ : ℝ) (T : ℕ)
    (hδ : 0 < δ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1 / 4)
    (hb : 0 ≤ b) (hbκ : b ≤ κ / 1000) (hA : 0 ≤ A) (hAκ : A ≤ κ / 1000)
    (hH₀ : 0 ≤ H₀) (hH₀H : H₀ ≤ H / 10) (hH : 1000 ≤ κ * H)
    (hFsmall : F ≤ A ^ 2 / 4) (hFscale : 2 * F ≤ δ * H ^ 2 / 100)
    (hmean : 30 * δ * H * (T : ℝ) ≤ A ^ 2 / 4)
    (htime : δ * H * (T : ℝ) ≤ 1 / 4) (hdH : δ * H ≤ κ / 1000)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ δ * H) (hthermal : (T : ℝ) * ζ ≤ δ)
    (hW₀ : meanPotential (x 0) ≤ F) (hz₀ : ‖(x 0).z‖ ≤ H₀)
    (ht₀ : 3 / 4 ≤ (x 0).t ∧ (x 0).t ≤ 7 / 4) (hv : ‖v‖ ≤ 1)
    (hstep : ∀ k < T, x (k + 1) = weightedNext (c k) δ (w k) (p k) (r k) (x k))
    (hw : ∀ k < T, 0 ≤ w k ∧ w k ≤ 1) (hc : ∀ k < T, |c k| ≤ b)
    (hp : ∀ k < T, ‖p k‖ ≤ 1) (hr : ∀ k < T, ‖r k‖ ≤ 1)
    (hsep : ∀ k < T, κ ≤ ⟪v, r k⟫)
    (hgate : ∀ k < T, w k * (c k * (x k).a * (x k).q +
      δ * ⟪(x k).a • p k + (x k).t • r k, (x k).z⟫) ≤ ζ) :
    ∀ k ≤ T, meanPotential (x k) ≤ F + 30 * δ * H * (k : ℝ) ∧
      |(x k).t - (x 0).t| ≤ δ * H * (k : ℝ) ∧ ‖(x k).z‖ < H ∧
      (∑ j ∈ Finset.range k, w j) ≤ 6 * H / κ := by
  have hHpos : 0 < H := by nlinarith
  have hd : 0 ≤ δ * H := by positivity
  have hA₁ : A ≤ 1 / 1000 := by linarith
  have hb₁ : b ≤ 1 / 4 := by linarith
  have hdH₁ : δ * H ≤ 1 := by linarith
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkT
    by_cases hk₀ : k = 0
    · subst k
      simp only [Nat.cast_zero, mul_zero, add_zero, sub_self, abs_zero, Finset.range_zero,
        Finset.sum_empty]
      exact ⟨hW₀, le_rfl, by linarith, by positivity⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₀
      have hmT : m < T := Nat.lt_of_succ_le hkT
      have hcast : ((m + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hkT
      have hpre (j : ℕ) (hj : j < m + 1) := ih j hj (Nat.le_trans (Nat.le_of_lt hj) hkT)
      have hWpre : ∀ j < m + 1, meanPotential (x j) ≤ A ^ 2 := by
        intro j hj
        have hjT : (j : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.le_trans (Nat.le_of_lt hj) hkT
        have hh := mul_le_mul_of_nonneg_left hjT (show 0 ≤ 30 * δ * H by positivity)
        have hhW := (hpre j hj).1
        nlinarith [sq_nonneg A]
      have htpre : ∀ j < m + 1, 1 / 2 ≤ (x j).t ∧ (x j).t ≤ 2 := by
        intro j hj
        have hjT : (j : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.le_trans (Nat.le_of_lt hj) hkT
        have hh := mul_le_mul_of_nonneg_left hjT hd
        have htj := abs_le.mp (hpre j hj).2.1
        constructor <;> linarith [ht₀.1, ht₀.2]
      have htAbs : ∀ j < m + 1, |(x j).t| ≤ 2 := by
        intro j hj
        rw [abs_le]
        exact ⟨by linarith [(htpre j hj).1], (htpre j hj).2⟩
      have hzpre : ∀ j < m + 1, ‖(x j).z‖ ≤ H := fun j hj => (hpre j hj).2.2.1.le
      have hcoords : ∀ j < m + 1, |(x j).a| ≤ A ∧ |(x j).q| ≤ A := by
        intro j hj
        have hs := Real.sq_sqrt (mean_potential_nonneg (x j))
        have hn := Real.sqrt_nonneg (meanPotential (x j))
        have hh := hWpre j hj
        have hroot : Real.sqrt (meanPotential (x j)) ≤ A := by nlinarith
        exact ⟨(mean_coordinate_bound (x j)).1.trans hroot,
          (mean_coordinate_bound (x j)).2.trans hroot⟩
      have hpi : |⟪p m, (x m).z⟫| ≤ H := by
        calc
          _ ≤ ‖p m‖ * ‖(x m).z‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * H := by gcongr; exact hp m hmT; exact hzpre m (Nat.lt_succ_self m)
          _ = H := one_mul H
      have hri : |⟪r m, (x m).z⟫| ≤ H := by
        calc
          _ ≤ ‖r m‖ * ‖(x m).z‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * H := by gcongr; exact hr m hmT; exact hzpre m (Nat.lt_succ_self m)
          _ = H := one_mul H
      obtain ⟨hWm, htm, hzm, _⟩ := hpre m (Nat.lt_succ_self m)
      have hmeanStep := late_mean_step_bound (c m) δ (w m) H ζ A (p m) (r m) (x m)
        hδ.le (hw m hmT).1 (hw m hmT).2 ((hc m hmT).trans hb₁)
        hζ hζH hdH₁ hpi hri (htAbs m (Nat.lt_succ_self m)) hA hA₁
        (hWpre m (Nat.lt_succ_self m)) (hgate m hmT)
      have htStep := difference_step_bound (c m) δ (w m) H (p m) (r m) (x m)
        hδ.le (hw m hmT).1 (hw m hmT).2 hri
      have hzStep := readout_step_bound (c m) δ (w m) A 2 (p m) (r m) (x m)
        (hw m hmT).1 (hw m hmT).2 (hp m hmT) (hr m hmT)
        (hcoords m (Nat.lt_succ_self m)).1 (htAbs m (Nat.lt_succ_self m))
      rw [← hstep m hmT] at hmeanStep htStep hzStep
      have henergy := late_prefix_energy_bound x c w p r δ b A H ζ F (m + 1)
        hδ.le hb hb₁ hA (by linarith) hHpos.le hζ hW₀
        (fun j hj => hstep j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => hw j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => hc j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => hp j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => hr j (Nat.lt_of_lt_of_le hj hkT)) hzpre
        (fun j hj => (hcoords j hj).1) (fun j hj => (hcoords j hj).2) htAbs
        (fun j hj => hgate j (Nat.lt_of_lt_of_le hj hkT))
      have hproj := cumulative_separator_bound x c w p r v δ κ A (m + 1) hκ.le hv
        (fun j hj => hstep j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => (hw j (Nat.lt_of_lt_of_le hj hkT)).1)
        (fun j hj => hp j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => hsep j (Nat.lt_of_lt_of_le hj hkT))
        (fun j hj => (hcoords j hj).1) (fun j hj => (htpre j hj).1)
      have hS : 0 ≤ ∑ j ∈ Finset.range (m + 1), w j :=
        Finset.sum_nonneg (fun j hj => (hw j (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) hkT)).1)
      have hinner₀ : -H₀ ≤ ⟪v, (x 0).z⟫ := by
        have hh : |⟪v, (x 0).z⟫| ≤ H₀ := by
          calc
            _ ≤ ‖v‖ * ‖(x 0).z‖ := abs_real_inner_le_norm _ _
            _ ≤ 1 * H₀ := by gcongr
            _ = H₀ := one_mul H₀
        exact (abs_le.mp hh).1
      have hinner : ⟪v, (x (m + 1)).z⟫ ≤ ‖(x (m + 1)).z‖ := by
        calc
          _ ≤ |⟪v, (x (m + 1)).z⟫| := le_abs_self _
          _ ≤ ‖v‖ * ‖(x (m + 1)).z‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * ‖(x (m + 1)).z‖ := by gcongr
          _ = _ := one_mul _
      have hproj' : κ / 3 * (∑ j ∈ Finset.range (m + 1), w j) ≤ ‖(x (m + 1)).z‖ + H₀ := by
        have hh := mul_le_mul_of_nonneg_right (show κ / 3 ≤ κ / 2 - A by linarith) hS
        linarith
      have hz₀sq := (sq_le_sq₀ (norm_nonneg _) hH₀).2 hz₀
      have hinit := mul_le_mul_of_nonneg_left hz₀sq (show 0 ≤ 2 * δ by positivity)
      have htherm := (mul_le_mul_of_nonneg_right hcast hζ).trans hthermal
      have hzfinal : ‖(x (m + 1)).z‖ < H := radius_bound_algebra δ κ b A H H₀ F ζ ((m + 1 : ℕ) : ℝ)
        (∑ j ∈ Finset.range (m + 1), w j) ‖(x (m + 1)).z‖ hδ hκ hκ₁ hbκ hAκ hdH
        hH₀ hH₀H hH hFscale htherm hS (norm_nonneg _) (by linarith) hproj' (by linarith)
      have htri := abs_sub_le (x (m + 1)).t (x m).t (x 0).t
      refine ⟨?_, ?_, hzfinal, ?_⟩
      · simp only [Nat.cast_succ]
        nlinarith only [hmeanStep, hWm]
      · simp only [Nat.cast_succ]
        nlinarith only [htri, htStep, htm]
      · apply (le_div_iff₀ hκ).2
        nlinarith only [hproj', hzfinal, hH₀H, hHpos]

end LongTails.Proofs.FiniteScaleConvolutionalSgdTrajectory
