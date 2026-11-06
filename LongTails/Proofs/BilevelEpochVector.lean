import LongTails.Proofs.BilevelEpochEnergy
import LongTails.Proofs.ScheduleBlockVector
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.ReshufflingPermutationMoments

namespace LongTails.Proofs.BilevelEpochVector

open Finset BilevelEpochEnergy
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma quadratic_epoch_decrease (H : E →L[ℝ] E) (hsym : H.toLinearMap.IsSymmetric)
    {L η θ : ℝ} (hH : ‖H‖ ≤ L) (hη : 0 < η) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hηL : η * L ≤ 1 / 4) (Z D δ : ℕ → E) (γ : E) (m : ℕ)
    (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hvel : ∀ k, k < m → D (k + 1) = (1 - θ) • D k -
      η • (γ + H (Z k + (1 - θ) • D k) + δ k)) :
    ⟪γ, Z m⟫ + ⟪H (Z m), Z m⟫ / 2 ≤
      -(3 * θ / (8 * η)) * (∑ k ∈ range m, ‖D (k + 1)‖ ^ 2) +
      (2 * η / θ) * ∑ k ∈ range m, ‖δ k‖ ^ 2 := by
  classical
  let b := hsym.eigenvectorBasis rfl
  let lam := hsym.eigenvalues rfl
  have hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i :=
    fun v i => hsym.eigenvectorBasis_apply_self_apply rfl v i
  have hray : ∀ v, |⟪H v, v⟫| ≤ L * ‖v‖ ^ 2 := by
    intro v
    calc
      _ ≤ ‖H v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg v)
      _ ≤ (L * ‖v‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  have heig : ∀ i, -L ≤ lam i ∧ lam i ≤ L := by
    intro i
    apply OracleTemplate.TemporalDiscrepancy.spectral_eigenvalue_bounds H hsym
    · intro v
      have hh := (abs_le.mp (hray v)).1
      nlinarith only [hh]
    · intro v
      exact (abs_le.mp (hray v)).2
  have hscalar : ∀ i : Fin (Module.finrank ℝ E),
      b.repr γ i * b.repr (Z m) i + lam i / 2 * (b.repr (Z m) i) ^ 2 ≤
      -(3 * θ / (8 * η)) * (∑ k ∈ range m, (b.repr (D (k + 1)) i) ^ 2) +
      (2 * η / θ) * ∑ k ∈ range m, (b.repr (δ k) i) ^ 2 := by
    intro i
    have hzi : b.repr (Z 0) i = 0 := by simp [hZ0]
    have hdi : b.repr (D 0) i = 0 := by simp [hD0]
    have hpi : ∀ k, k < m → b.repr (Z (k + 1)) i = b.repr (Z k) i + b.repr (D (k + 1)) i := by
      intro k hk
      simpa only [map_add, PiLp.add_apply] using congrArg (fun v => b.repr v i) (hpos k hk)
    have hvi : ∀ k, k < m → b.repr (D (k + 1)) i = (1 - θ) * b.repr (D k) i -
        η * (b.repr γ i + lam i * (b.repr (Z k) i + (1 - θ) * b.repr (D k) i) + b.repr (δ k) i) := by
      intro k hk
      have hv := congrArg (fun v => b.repr v i) (hvel k hk)
      simp only [map_sub, map_smul, map_add, PiLp.sub_apply, PiLp.smul_apply,
        PiLp.add_apply, hb, smul_eq_mul] at hv
      rw [hv]
      ring
    by_cases hi : -θ / η ≤ lam i
    · exact weak_scalar_epoch (g := b.repr γ i) hη hθ hθhalf hi
        (by nlinarith [mul_le_mul_of_nonneg_left (heig i).2 hη.le]) (fun k => b.repr (Z k) i) (fun k => b.repr (D k) i) (fun k => b.repr (δ k) i) m hzi hdi hpi hvi
    · exact negative_scalar_epoch (g := b.repr γ i) hη hθ hθhalf (lt_of_not_ge hi)
        (by nlinarith [mul_le_mul_of_nonneg_left (heig i).1 hη.le]) (fun k => b.repr (Z k) i) (fun k => b.repr (D k) i) (fun k => b.repr (δ k) i) m hzi hdi hpi hvi
  have hDsum : (∑ i : Fin (Module.finrank ℝ E), ∑ k ∈ range m, (b.repr (D (k + 1)) i) ^ 2) =
      ∑ k ∈ range m, ‖D (k + 1)‖ ^ 2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    exact (OracleTemplate.ScheduleBlock.norm_sq_coord b (D (k + 1))).symm
  have hδsum : (∑ i : Fin (Module.finrank ℝ E), ∑ k ∈ range m, (b.repr (δ k) i) ^ 2) =
      ∑ k ∈ range m, ‖δ k‖ ^ 2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    exact (OracleTemplate.ScheduleBlock.norm_sq_coord b (δ k)).symm
  have hs := sum_le_sum (s := univ) (fun i _ => hscalar i)
  simp only [sum_add_distrib] at hs
  rw [← mul_sum, ← mul_sum, hDsum, hδsum] at hs
  rw [OracleTemplate.ScheduleBlock.model_coord H b lam hb γ (Z m)]
  simp only [sum_add_distrib]
  convert hs using 1
  congr 1
  apply sum_congr rfl
  intro i _
  ring

lemma nonlinear_epoch_decrease {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    {L ρ η θ B σ R : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (a : E) (hsym : (A a).toLinearMap.IsSymmetric) (hA : ‖A a‖ ≤ L)
    (hη : 0 < η) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) (hηL : η * L ≤ 1 / 4)
    (Z D V : ℕ → E) (m : ℕ) (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hvel : ∀ k, k < m → D (k + 1) = (1 - θ) • D k - η • V k)
    (herr : ∀ k, k < m → ‖V k - g (a + (Z k + (1 - θ) • D k))‖ ≤ σ)
    (hquery : ∀ k, k < m → ‖Z k + (1 - θ) • D k‖ ≤ 2 * B)
    (hend : ‖Z m‖ ≤ R) :
    f (a + Z m) - f a ≤
      -(3 * θ / (8 * η)) * (∑ k ∈ range m, ‖D (k + 1)‖ ^ 2) +
      (2 * η / θ) * m * (σ + 2 * ρ * B ^ 2) ^ 2 + ρ * R ^ 3 / 6 := by
  let δ := fun k => V k - g a - A a (Z k + (1 - θ) • D k)
  have hδ : ∀ k, k < m → ‖δ k‖ ≤ σ + 2 * ρ * B ^ 2 := by
    intro k hk
    let z := Z k + (1 - θ) • D k
    have ht := CubicRegularization.gradient_taylor hg hLip a z
    have he : δ k = (V k - g (a + z)) + (g (a + z) - g a - A a z) := by dsimp [δ]; abel
    rw [he]
    calc
      _ ≤ ‖V k - g (a + z)‖ + ‖g (a + z) - g a - A a z‖ := norm_add_le _ _
      _ ≤ σ + ρ * ‖z‖ ^ 2 / 2 := add_le_add (herr k hk) ht
      _ ≤ _ := by
        have hz : ‖z‖ ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hquery k hk) 2
        nlinarith [mul_le_mul_of_nonneg_left hz hρ]
  have hv : ∀ k, k < m → D (k + 1) = (1 - θ) • D k -
      η • (g a + A a (Z k + (1 - θ) • D k) + δ k) := by
    intro k hk
    rw [hvel k hk]
    congr 2
    dsimp [δ]
    abel
  have hq := quadratic_epoch_decrease (A a) hsym hA hη hθ hθhalf hηL Z D δ (g a) m hZ0 hD0 hpos hv
  have hs : (∑ k ∈ range m, ‖δ k‖ ^ 2) ≤ m * (σ + 2 * ρ * B ^ 2) ^ 2 := by
    calc
      _ ≤ ∑ k ∈ range m, (σ + 2 * ρ * B ^ 2) ^ 2 := sum_le_sum fun k hk =>
        pow_le_pow_left₀ (norm_nonneg _) (hδ k (mem_range.mp hk)) 2
      _ = _ := by simp
  have ht := (abs_le.mp (CubicRegularization.objective_taylor hf hg hLip a (Z m))).2
  rw [← real_inner_comm (Z m) (A a (Z m))] at ht
  have hp : ρ * ‖Z m‖ ^ 3 ≤ ρ * R ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hend 3) hρ
  have hc := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * η / θ by positivity)
  nlinarith only [hq, ht, hp, hc]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma position_eq_sum (Z D : ℕ → E) (m : ℕ) (hZ0 : Z 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1)) :
    Z m = ∑ k ∈ range m, D (k + 1) := by
  induction m with
  | zero => simpa using hZ0
  | succ m ih =>
    rw [hpos m (by omega), ih (fun k hk => hpos k (by omega)), sum_range_succ]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma prefix_radius (Z D : ℕ → E) (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hmove : (m : ℝ) * (∑ k ∈ range m, ‖D (k + 1)‖ ^ 2) ≤ B ^ 2) :
    ‖Z m‖ ≤ B ∧ ‖D m‖ ≤ B := by
  have hz := OracleTemplate.Reshuffling.norm_sum_sq_le_card (range m) (fun k => D (k + 1))
  rw [← position_eq_sum Z D m hZ0 hpos] at hz
  simp only [card_range] at hz
  constructor
  · nlinarith [norm_nonneg (Z m)]
  · cases m with
    | zero => simpa [hD0] using hB
    | succ n =>
      have hs : ‖D (n + 1)‖ ^ 2 ≤ ∑ k ∈ range (n + 1), ‖D (k + 1)‖ ^ 2 :=
        single_le_sum (f := fun k => ‖D (k + 1)‖ ^ 2) (a := n) (fun k _ => sq_nonneg _) (mem_range.mpr (Nat.lt_succ_self n))
      have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hh := mul_le_mul_of_nonneg_right hn (show 0 ≤ ∑ k ∈ range (n + 1), ‖D (k + 1)‖ ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
      nlinarith [norm_nonneg (D (n + 1))]

omit [FiniteDimensional ℝ E] in
lemma extrapolated_radius {z d : E} {B θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hz : ‖z‖ ≤ B) (hd : ‖d‖ ≤ B) : ‖z + (1 - θ) • d‖ ≤ 2 * B := by
  calc
    _ ≤ ‖z‖ + ‖(1 - θ) • d‖ := norm_add_le _ _
    _ = ‖z‖ + (1 - θ) * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    _ ≤ ‖z‖ + ‖d‖ := by nlinarith [norm_nonneg d]
    _ ≤ _ := by linarith

omit [FiniteDimensional ℝ E] in
lemma momentum_sum (Z D V : ℕ → E) (m : ℕ) {η θ : ℝ}
    (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hvel : ∀ k, k < m → D (k + 1) = (1 - θ) • D k - η • V k) :
    η • (∑ k ∈ range m, V k) = -θ • Z m - (1 - θ) • D m := by
  induction m with
  | zero => simp [hZ0, hD0]
  | succ m ih =>
    rw [sum_range_succ, smul_add, ih (fun k hk => hpos k (by omega)) (fun k hk => hvel k (by omega))]
    rw [hpos m (by omega), hvel m (by omega)]
    module

omit [FiniteDimensional ℝ E] in
lemma average_gradient_bound {g : E → E} {A : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (A x) x) {ρ R σ : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (a : E) (Z V : ℕ → E) {m : ℕ} (hm : 0 < m)
    (hZ : ∀ k, k < m → ‖Z k‖ ≤ R)
    (herr : ∀ k, k < m → ‖V k - g (a + Z k)‖ ≤ σ) :
    ‖g (a + (m : ℝ)⁻¹ • (∑ k ∈ range m, Z k))‖ ≤
      ‖(m : ℝ)⁻¹ • (∑ k ∈ range m, V k)‖ + σ + ρ * R ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let z := (m : ℝ)⁻¹ • (∑ k ∈ range m, Z k)
  let δ := fun k => V k - g a - A a (Z k)
  have hz : ‖z‖ ≤ R := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmR)]
    calc
      _ ≤ (m : ℝ)⁻¹ * ∑ k ∈ range m, ‖Z k‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hmR.le)
      _ ≤ (m : ℝ)⁻¹ * ∑ k ∈ range m, R := mul_le_mul_of_nonneg_left
        (sum_le_sum fun k hk => hZ k (mem_range.mp hk)) (inv_nonneg.mpr hmR.le)
      _ = R := by simp only [sum_const, card_range, nsmul_eq_mul]; field_simp
  have hd : ∀ k, k < m → ‖δ k‖ ≤ σ + ρ * R ^ 2 / 2 := by
    intro k hk
    have ht := CubicRegularization.gradient_taylor hg hLip a (Z k)
    have he : δ k = (V k - g (a + Z k)) + (g (a + Z k) - g a - A a (Z k)) := by dsimp [δ]; abel
    rw [he]
    have hn := (norm_add_le (V k - g (a + Z k)) (g (a + Z k) - g a - A a (Z k))).trans (add_le_add (herr k hk) ht)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hZ k hk) 2) hρ
    nlinarith only [hn, hp]
  have hds : ‖(m : ℝ)⁻¹ • (∑ k ∈ range m, δ k)‖ ≤ σ + ρ * R ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmR)]
    calc
      _ ≤ (m : ℝ)⁻¹ * ∑ k ∈ range m, ‖δ k‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hmR.le)
      _ ≤ (m : ℝ)⁻¹ * ∑ k ∈ range m, (σ + ρ * R ^ 2 / 2) := mul_le_mul_of_nonneg_left
        (sum_le_sum fun k hk => hd k (mem_range.mp hk)) (inv_nonneg.mpr hmR.le)
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; field_simp
  have he : (m : ℝ)⁻¹ • (∑ k ∈ range m, δ k) =
      (m : ℝ)⁻¹ • (∑ k ∈ range m, V k) - g a - A a z := by
    simp only [δ, z, sum_sub_distrib, sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_sub, smul_smul, inv_mul_cancel₀ hmR.ne', one_smul, map_smul, map_sum]
  have ht := CubicRegularization.gradient_taylor hg hLip a z
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) hρ
  have he2 : g (a + z) = (m : ℝ)⁻¹ • (∑ k ∈ range m, V k) +
      (g (a + z) - g a - A a z) - (m : ℝ)⁻¹ • (∑ k ∈ range m, δ k) := by rw [he]; abel
  change ‖g (a + z)‖ ≤ _
  rw [he2]
  have hn := (norm_sub_le ((m : ℝ)⁻¹ • (∑ k ∈ range m, V k) + (g (a + z) - g a - A a z))
    ((m : ℝ)⁻¹ • (∑ k ∈ range m, δ k))).trans
    (add_le_add (norm_add_le _ _) (le_refl _))
  nlinarith only [hn, ht, hp, hds]

omit [FiniteDimensional ℝ E] in
lemma momentum_average_bound (Z D V : ℕ → E) {m : ℕ} (hm : 0 < m) {η θ B b : ℝ}
    (hη : 0 < η) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hvel : ∀ k, k < m → D (k + 1) = (1 - θ) • D k - η • V k)
    (hz : ‖Z m‖ ≤ B) (hd : ‖D m‖ ≤ b) :
    ‖(m : ℝ)⁻¹ • (∑ k ∈ range m, V k)‖ ≤ (θ * B + b) / (η * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he := congrArg norm (momentum_sum Z D V m hZ0 hD0 hpos hvel)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη] at he
  have hh := norm_sub_le (-θ • Z m) ((1 - θ) • D m)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg hθ, abs_of_nonneg (by linarith : 0 ≤ 1 - θ)] at hh
  have hs : ‖∑ k ∈ range m, V k‖ ≤ (θ * B + b) / η := by
    apply (le_div_iff₀ hη).mpr
    have hz' := mul_le_mul_of_nonneg_left hz hθ
    have hd' : (1 - θ) * ‖D m‖ ≤ b := by nlinarith [norm_nonneg (D m)]
    nlinarith only [he, hh, hz', hd']
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmR)]
  calc
    _ ≤ (m : ℝ)⁻¹ * ((θ * B + b) / η) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hmR.le)
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma selected_movement_bound (D : ℕ → E) {K j : ℕ} (hK : 0 < K)
    {B : ℝ} (hB : 0 ≤ B)
    (hmin : ∀ k ∈ Ico (K / 2) K, ‖D (j + 1)‖ ^ 2 ≤ ‖D (k + 1)‖ ^ 2)
    (hmove : (K : ℝ) * (∑ k ∈ range K, ‖D (k + 1)‖ ^ 2) ≤ B ^ 2) :
    ‖D (j + 1)‖ ≤ 2 * B / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : ((K - K / 2 : ℕ) : ℝ) * ‖D (j + 1)‖ ^ 2 ≤ ∑ k ∈ range K, ‖D (k + 1)‖ ^ 2 := by
    calc
      _ = ∑ k ∈ Ico (K / 2) K, ‖D (j + 1)‖ ^ 2 := by simp
      _ ≤ ∑ k ∈ Ico (K / 2) K, ‖D (k + 1)‖ ^ 2 := sum_le_sum hmin
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by intro k hk; exact mem_range.mpr (mem_Ico.mp hk).2)
        (fun _ _ _ => sq_nonneg _)
  have hc : (K : ℝ) ≤ 2 * ((K - K / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show K ≤ 2 * (K - K / 2) by omega)
  have hsq : (K : ℝ) ^ 2 * ‖D (j + 1)‖ ^ 2 ≤ 2 * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖D (j + 1)‖)
    have hh' := mul_le_mul_of_nonneg_left hh hKR.le
    have hs' := mul_le_mul_of_nonneg_left hs hKR.le
    nlinarith only [hh', hs', hmove]
  apply (le_div_iff₀ hKR).mpr
  nlinarith [sq_nonneg (‖D (j + 1)‖ * (K : ℝ) - 2 * B)]

omit [FiniteDimensional ℝ E] in
lemma average_translate (a z : E) {m : ℕ} (hm : 0 < m) :
    (m : ℝ)⁻¹ • ((m : ℝ) • a + z) = a + (m : ℝ)⁻¹ • z := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hm), one_smul]

end LongTails.Proofs.BilevelEpochVector
