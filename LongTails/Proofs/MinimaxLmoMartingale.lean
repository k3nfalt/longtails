import LongTails.Proofs.NormalizedStormOrthogonality

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.MinimaxLmo

variable {Ω : Type*} [MeasurableSpace Ω] {Y : Type*} [MeasurableSpace Y]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma mm_sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  have h := Real.sq_sqrt hx
  nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma mm_norm_inv_sqrt_smul_sq {B : ℝ} (hB : 0 < B) (x : E) :
    ‖(Real.sqrt B)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / B := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow,
    inv_pow, Real.sq_sqrt hB.le]
  field_simp

lemma mm_sq_sub_div_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (b ^ 2 - a ^ 2) / b ≤ 2 * (b - a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_iff₀ hb]
  nlinarith

lemma mm_le_amgm {a B : ℝ} (hB : 0 < B) :
    a ≤ a ^ 2 / B / (2 * Real.sqrt 2) + B / Real.sqrt 2 := by
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : a ^ 2 / B / (2 * Real.sqrt 2) + B / Real.sqrt 2 - a =
      (a - Real.sqrt 2 * B) ^ 2 / (2 * Real.sqrt 2 * B) := by
    field_simp
    nlinarith [hs]
  have : 0 ≤ (a - Real.sqrt 2 * B) ^ 2 / (2 * Real.sqrt 2 * B) := by positivity
  linarith

lemma mm_sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem mm_martingale_first_moment (p : Measure Ω) [IsProbabilityMeasure p]
    (S : ℕ → (ℕ → Ω) → Y) (hS : ∀ j, Measurable (S j))
    (hdep : ∀ j (ξ ξ' : ℕ → Ω), (∀ i, i < j → ξ i = ξ' i) → S j ξ = S j ξ')
    (W : ℕ → Y → Ω → E) (hW : ∀ j, Measurable (Function.uncurry (W j)))
    (hWi : ∀ j y, Integrable (W j y) p) (hW0 : ∀ j y, ∫ ω, W j y ω ∂p = 0)
    (hW2 : ∀ j y, Integrable (fun ω => ‖W j y ω‖ ^ 2) p)
    (v : ℕ → Y → ℝ) (hv : ∀ j, Measurable (v j)) (hv0 : ∀ j y, 0 ≤ v j y)
    (hvle : ∀ j y, ∫ ω, ‖W j y ω‖ ^ 2 ∂p ≤ v j y)
    (hvi : ∀ j, Integrable (fun ξ => v j (S j ξ)) (Measure.infinitePi fun _ : ℕ => p)) (k : ℕ) :
    Integrable (fun ξ : ℕ → Ω => ‖∑ j ∈ Finset.range k, W j (S j ξ) (ξ j)‖)
        (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ‖∑ j ∈ Finset.range k, W j (S j ξ) (ξ j)‖ ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        Real.sqrt 2 * ∫ ξ, Real.sqrt (∑ j ∈ Finset.range k, v j (S j ξ))
          ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set M : ℕ → (ℕ → Ω) → E := fun k ξ => ∑ j ∈ Finset.range k, W j (S j ξ) (ξ j) with hMdef
  set V : ℕ → (ℕ → Ω) → ℝ := fun k ξ => ∑ j ∈ Finset.range k, v j (S j ξ) with hVdef
  have hterm : ∀ j, Measurable fun ξ : ℕ → Ω => W j (S j ξ) (ξ j) := fun j =>
    (hW j).comp ((hS j).prodMk (measurable_pi_apply j))
  have hMm : ∀ k, Measurable (M k) := fun k => Finset.measurable_sum _ fun j _ => hterm j
  have hVm : ∀ k, Measurable (V k) := fun k => Finset.measurable_sum _ fun j _ => (hv j).comp (hS j)
  have hV0 : ∀ k ξ, 0 ≤ V k ξ := fun k ξ => Finset.sum_nonneg fun j _ => hv0 j _
  have hVi : ∀ k, Integrable (V k) P := fun k => integrable_finsetSum _ fun j _ => hvi j
  have hMdep : ∀ k (ξ ξ' : ℕ → Ω), (∀ i, i < k → ξ i = ξ' i) → M k ξ = M k ξ' := by
    intro k ξ ξ' h
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hdep j ξ ξ' fun i hi => h i (by omega), h j hj']
  have hVdep : ∀ k (ξ ξ' : ℕ → Ω), (∀ i, i < k → ξ i = ξ' i) → V (k + 1) ξ = V (k + 1) ξ' := by
    intro k ξ ξ' h
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hdep j ξ ξ' fun i hi => h i (by omega)]
  have hsqrt_int : ∀ k (δ : ℝ), 0 ≤ δ → Integrable (fun ξ => Real.sqrt (δ + V k ξ)) P := by
    intro k δ hδ
    refine Integrable.mono' ((integrable_const (δ + 1)).add (hVi k))
      ((hVm k).const_add δ).sqrt.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := mm_sqrt_le_add_one (add_nonneg hδ (hV0 k ξ))
    simp only [Pi.add_apply]
    linarith
  have hmain : ∀ δ : ℝ, 0 < δ → ∀ k,
      Integrable (fun ξ => ‖M k ξ‖ ^ 2 / Real.sqrt (δ + V k ξ)) P ∧
        ∫ ξ, ‖M k ξ‖ ^ 2 / Real.sqrt (δ + V k ξ) ∂P ≤
          2 * ∫ ξ, (Real.sqrt (δ + V k ξ) - Real.sqrt δ) ∂P := by
    intro δ hδ k
    have hBpos : ∀ k ξ, 0 < Real.sqrt (δ + V k ξ) := fun k ξ =>
      Real.sqrt_pos.mpr (by linarith [hV0 k ξ])
    have hBge : ∀ k ξ, Real.sqrt δ ≤ Real.sqrt (δ + V k ξ) := fun k ξ =>
      Real.sqrt_le_sqrt (by linarith [hV0 k ξ])
    have hBm : ∀ k, Measurable fun ξ => Real.sqrt (δ + V k ξ) := fun k =>
      ((hVm k).const_add δ).sqrt
    have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    induction k with
    | zero =>
        simp [M, V]
    | succ k ih =>
        obtain ⟨ih1, ih2⟩ := ih
        set B1 : (ℕ → Ω) → ℝ := fun ξ => Real.sqrt (δ + V (k + 1) ξ) with hB1
        set B0 : (ℕ → Ω) → ℝ := fun ξ => Real.sqrt (δ + V k ξ) with hB0
        have hVsucc : ∀ ξ, V (k + 1) ξ = V k ξ + v k (S k ξ) := fun ξ => Finset.sum_range_succ _ _
        have hMsucc : ∀ ξ, M (k + 1) ξ = M k ξ + W k (S k ξ) (ξ k) := fun ξ => Finset.sum_range_succ _ _
        have hmono : ∀ ξ, B0 ξ ≤ B1 ξ := by
          intro ξ
          refine Real.sqrt_le_sqrt ?_
          rw [hVsucc]
          linarith [hv0 k (S k ξ)]
        let S' : (ℕ → Ω) → Y × E × ℝ := fun ξ => (S k ξ, M k ξ, B1 ξ)
        have hS' : Measurable S' := (hS k).prodMk ((hMm k).prodMk (hBm (k + 1)))
        have hdep' : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S' ξ = S' ξ' := by
          intro ξ ξ' h
          simp only [S', B1, hdep k ξ ξ' h, hMdep k ξ ξ' h, hVdep k ξ ξ' h]
        let U : Y × E × ℝ → E := fun y => (Real.sqrt y.2.2)⁻¹ • y.2.1
        have hU : Measurable U := (measurable_snd.snd.sqrt.inv).smul measurable_snd.fst
        let W' : Y × E × ℝ → Ω → E := fun y ω => (Real.sqrt y.2.2)⁻¹ • W k y.1 ω
        have hW' : Measurable (Function.uncurry W') :=
          (measurable_fst.snd.snd.sqrt.inv).smul ((hW k).comp (measurable_fst.fst.prodMk measurable_snd))
        have hW'i : ∀ y, Integrable (W' y) p := fun y => (hWi k y.1).smul _
        have hW'0 : ∀ y, ∫ ω, W' y ω ∂p = 0 := by
          intro y
          simp only [W', integral_smul, hW0 k y.1, smul_zero]
        have hW'2 : ∀ y, Integrable (fun ω => ‖W' y ω‖ ^ 2) p := by
          intro y
          simp only [W', norm_smul, mul_pow]
          exact (hW2 k y.1).const_mul _
        let w : Y × E × ℝ → ℝ := fun y => ‖(Real.sqrt y.2.2)⁻¹‖ ^ 2 * v k y.1
        have hw : ∀ y, ∫ ω, ‖W' y ω‖ ^ 2 ∂p ≤ w y := by
          intro y
          simp only [W', w, norm_smul, mul_pow]
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hvle k y.1) (sq_nonneg _)
        have hwS : ∀ ξ, w (S' ξ) = v k (S k ξ) / B1 ξ := by
          intro ξ
          simp only [w, S', Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
            inv_pow]
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ B1 ξ from (hBpos (k + 1) ξ).le), div_eq_inv_mul]
        have hUS : ∀ ξ, ‖U (S' ξ)‖ ^ 2 = ‖M k ξ‖ ^ 2 / B1 ξ := fun ξ =>
          mm_norm_inv_sqrt_smul_sq (hBpos (k + 1) ξ) _
        have hsumS : ∀ ξ, ‖(1 : ℝ) • U (S' ξ) + W' (S' ξ) (ξ k)‖ ^ 2 = ‖M (k + 1) ξ‖ ^ 2 / B1 ξ := by
          intro ξ
          simp only [one_smul, U, W', S']
          rw [← smul_add, ← hMsucc]
          exact mm_norm_inv_sqrt_smul_sq (hBpos (k + 1) ξ) _
        have hwm : Measurable fun ξ => v k (S k ξ) / B1 ξ := ((hv k).comp (hS k)).div (hBm (k + 1))
        have hwi : Integrable (fun ξ => w (S' ξ)) P := by
          simp_rw [hwS]
          refine Integrable.mono' ((hvi k).div_const (Real.sqrt δ)) hwm.aestronglyMeasurable
            (Filter.Eventually.of_forall fun ξ => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hv0 k _) (hBpos (k + 1) ξ).le)]
          exact div_le_div_of_nonneg_left (hv0 k _) hsδ (hBge (k + 1) ξ)
        have hqm : Measurable fun ξ => ‖M k ξ‖ ^ 2 / B1 ξ := ((hMm k).norm.pow_const 2).div (hBm (k + 1))
        have hq_le : ∀ ξ, ‖M k ξ‖ ^ 2 / B1 ξ ≤ ‖M k ξ‖ ^ 2 / B0 ξ := fun ξ =>
          div_le_div_of_nonneg_left (sq_nonneg _) (hBpos k ξ) (hmono ξ)
        have hU2 : Integrable (fun ξ => ‖U (S' ξ)‖ ^ 2) P := by
          simp_rw [hUS]
          refine Integrable.mono' ih1 hqm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hBpos (k + 1) ξ).le)]
          exact hq_le ξ
        obtain ⟨key1, key2⟩ := NormalizedStorm.fresh_step_sq p k S' hS' hdep' U hU W' hW' hW'i hW'0
          hW'2 w hw hwi hU2 1
        simp_rw [hsumS] at key1 key2
        simp_rw [hUS, hwS, one_pow, one_mul] at key2
        refine ⟨key1, ?_⟩
        have hB0i : Integrable B0 P := hsqrt_int k δ hδ.le
        have hB1i : Integrable B1 P := hsqrt_int (k + 1) δ hδ.le
        have hqint : Integrable (fun ξ => ‖M k ξ‖ ^ 2 / B1 ξ) P := by
          have := hU2; simp_rw [hUS] at this; exact this
        have hwint : Integrable (fun ξ => v k (S k ξ) / B1 ξ) P := by
          have := hwi; simp_rw [hwS] at this; exact this
        have h1 : ∫ ξ, ‖M k ξ‖ ^ 2 / B1 ξ ∂P ≤ ∫ ξ, ‖M k ξ‖ ^ 2 / B0 ξ ∂P :=
          integral_mono hqint ih1 hq_le
        have h2 : ∫ ξ, v k (S k ξ) / B1 ξ ∂P ≤ ∫ ξ, 2 * (B1 ξ - B0 ξ) ∂P := by
          refine integral_mono hwint ((hB1i.sub hB0i).const_mul 2) fun ξ => ?_
          have e : v k (S k ξ) = B1 ξ ^ 2 - B0 ξ ^ 2 := by
            have a1 : B1 ξ ^ 2 = δ + V (k + 1) ξ := Real.sq_sqrt (by linarith [hV0 (k + 1) ξ])
            have a0 : B0 ξ ^ 2 = δ + V k ξ := Real.sq_sqrt (by linarith [hV0 k ξ])
            rw [a1, a0, hVsucc]
            ring
          rw [e]
          exact mm_sq_sub_div_le (hBpos k ξ) (hmono ξ)
        have e3 : ∫ ξ, 2 * (B1 ξ - B0 ξ) ∂P =
            2 * ∫ ξ, (B1 ξ - Real.sqrt δ) ∂P - 2 * ∫ ξ, (B0 ξ - Real.sqrt δ) ∂P := by
          rw [integral_const_mul, integral_sub hB1i hB0i, integral_sub hB1i (integrable_const _),
            integral_sub hB0i (integrable_const _)]
          ring
        linarith
  have hδbound : ∀ δ : ℝ, 0 < δ → ∀ k,
      Integrable (fun ξ => ‖M k ξ‖) P ∧
        ∫ ξ, ‖M k ξ‖ ∂P ≤ Real.sqrt 2 * ∫ ξ, Real.sqrt (δ + V k ξ) ∂P := by
    intro δ hδ k
    obtain ⟨h1, h2⟩ := hmain δ hδ k
    have hBpos : ∀ ξ, 0 < Real.sqrt (δ + V k ξ) := fun ξ =>
      Real.sqrt_pos.mpr (by linarith [hV0 k ξ])
    have hBi := hsqrt_int k δ hδ.le
    have hr : Integrable (fun ξ => ‖M k ξ‖ ^ 2 / Real.sqrt (δ + V k ξ) / (2 * Real.sqrt 2) +
        Real.sqrt (δ + V k ξ) / Real.sqrt 2) P :=
      (h1.div_const _).add (hBi.div_const _)
    have hpt : ∀ ξ, ‖M k ξ‖ ≤ ‖M k ξ‖ ^ 2 / Real.sqrt (δ + V k ξ) / (2 * Real.sqrt 2) +
        Real.sqrt (δ + V k ξ) / Real.sqrt 2 := fun ξ => mm_le_amgm (hBpos ξ)
    have hMi : Integrable (fun ξ => ‖M k ξ‖) P :=
      Integrable.mono' hr (hMm k).norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => by rw [norm_norm]; exact hpt ξ)
    refine ⟨hMi, ?_⟩
    have hmono := integral_mono hMi hr hpt
    rw [integral_add (h1.div_const _) (hBi.div_const _), integral_div, integral_div] at hmono
    have hsub : ∫ ξ, (Real.sqrt (δ + V k ξ) - Real.sqrt δ) ∂P ≤ ∫ ξ, Real.sqrt (δ + V k ξ) ∂P := by
      rw [integral_sub hBi (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith [Real.sqrt_nonneg δ]
    have h2' : ∫ ξ, ‖M k ξ‖ ^ 2 / Real.sqrt (δ + V k ξ) ∂P ≤ 2 * ∫ ξ, Real.sqrt (δ + V k ξ) ∂P := by
      linarith
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    set I := ∫ ξ, Real.sqrt (δ + V k ξ) ∂P
    set Q := ∫ ξ, ‖M k ξ‖ ^ 2 / Real.sqrt (δ + V k ξ) ∂P
    have ha : Q / (2 * Real.sqrt 2) ≤ I / Real.sqrt 2 := by
      rw [div_le_div_iff₀ (by positivity) hs2]
      nlinarith [mul_le_mul_of_nonneg_right h2' hs2.le]
    have hb : I / Real.sqrt 2 + I / Real.sqrt 2 = Real.sqrt 2 * I := by
      rw [← add_div, div_eq_iff hs2.ne']
      linear_combination (-I) * hss
    linarith
  obtain ⟨hMi, -⟩ := hδbound 1 one_pos k
  refine ⟨hMi, ?_⟩
  have hVsq : Integrable (fun ξ => Real.sqrt (V k ξ)) P := by
    have := hsqrt_int k 0 le_rfl
    simpa using this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := (ε / Real.sqrt 2) ^ 2
  have hδ : 0 < δ := by positivity
  obtain ⟨-, hb⟩ := hδbound δ hδ k
  have hsd : Real.sqrt δ = ε / Real.sqrt 2 := Real.sqrt_sq (by positivity)
  have hle : ∫ ξ, Real.sqrt (δ + V k ξ) ∂P ≤ ∫ ξ, Real.sqrt (V k ξ) ∂P + ε / Real.sqrt 2 := by
    have hi2 : Integrable (fun ξ => Real.sqrt (V k ξ) + Real.sqrt δ) P :=
      hVsq.add (integrable_const _)
    have hpt : ∀ ξ, Real.sqrt (δ + V k ξ) ≤ Real.sqrt (V k ξ) + Real.sqrt δ := fun ξ => by
      have := mm_sqrt_add_le_add_sqrt hδ.le (hV0 k ξ)
      linarith
    have := integral_mono (hsqrt_int k δ hδ.le) hi2 hpt
    rw [integral_add hVsq (integrable_const _)] at this
    simpa [hsd] using this
  have hs2 : 0 < Real.sqrt 2 := by positivity
  calc ∫ ξ, ‖M k ξ‖ ∂P ≤ Real.sqrt 2 * ∫ ξ, Real.sqrt (δ + V k ξ) ∂P := hb
    _ ≤ Real.sqrt 2 * (∫ ξ, Real.sqrt (V k ξ) ∂P + ε / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left hle hs2.le
    _ = Real.sqrt 2 * ∫ ξ, Real.sqrt (V k ξ) ∂P + ε := by
        field_simp

end OracleTemplate.MinimaxLmo
