import LongTails.Proofs.ChiSquareBoundedCentreDroPerspective

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open ChiSquareDro LongTails.Setups.ChiSquareConstrainedDro
noncomputable section

variable {q : Params} (I : Instance q) {x : q.E}

lemma low_bias_comparator (hρ : 0 < q.ρ) (hB : 0 < q.B) (hε : 0 < q.ε) (heB : q.ε < q.B)
    (hm : Measurable (I.loss x)) (hz : ∀ ω, I.loss x ω ∈ Icc 0 q.B) :
    ∃ a ∈ Icc 0 q.B, ∃ l ∈ Icc (q.ε/(8*q.ρ)) (q.B/q.ρ),
      Q I.law q.ρ (I.loss x) a l ≤ objective I x + q.ε/8 := by
  let p := (I.law : Measure q.Ξ)
  let Z := I.loss x
  have hb := fun ω => (hz ω).2
  have h0 := fun ω => (hz ω).1
  obtain ⟨η, _, hη⟩ := dual_attained I hρ hB hm h0 hb
  let c := radius q
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith : 0 < 1+2*q.ρ)
  have hc2 : c^2 = 1+2*q.ρ := Real.sq_sqrt (by linarith)
  let s := nrm p Z η
  have hs : 0 ≤ s := nrm_nonneg _ _ _
  have hs2 : s ^ 2 = ChiSquareDro.sq p Z η := nrm_sq _ _ _
  change η+c*s ≤ objective I x at hη
  let l := s/c
  let d := q.ε/(8*q.ρ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdB : d ≤ q.B/q.ρ := by dsimp [d]; field_simp [hρ]; linarith
  let l' := max d l
  have hl' : 0 < l' := hd.trans_le (le_max_left _ _)
  have hd' : l' - l ≤ d := by
    have hl : 0 ≤ l := div_nonneg hs hc.le
    dsimp [l']; rcases le_total d l with h|h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hρd : q.ρ*d = q.ε/8 := by dsimp [d]; field_simp
  let a := η+l
  have ha : a-l = η := by dsimp [a]; ring
  have ⟨hlB, hQ⟩ : l ≤ q.B/q.ρ ∧ Q p q.ρ Z a l' ≤ objective I x + q.ε/8 := by
    rcases eq_or_lt_of_le hs with he | he
    · have hl : l = 0 := by simp [l, ← he]
      have hsq : (∫ ω, tail Z η ω ^ 2 ∂p) = 0 := by change ChiSquareDro.sq p Z η = 0; rw [← hs2, ← he]; norm_num
      have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (tail Z η ω))
        (integrable_tail_sq p hm hb η)).mp hsq
      have hpoint : ∀ᵐ ω ∂p, majorant q.ρ (Z ω) a l' ≤ η + q.ρ*l' := by
        filter_upwards [hae] with ω hw
        change tail Z η ω ^ 2 = 0 at hw
        have htail := sub_le_tail Z η ω
        have hZ : Z ω ≤ η := by nlinarith [sq_eq_zero_iff.mp hw]
        have hv := weight_nonneg (z := Z ω) (a := a) hl'
        rw [← payoff_weight hl']
        have hmul := mul_le_mul_of_nonneg_left hZ hv
        have hsq' := mul_nonneg hl'.le (sq_nonneg (weight (Z ω) a l'-1))
        dsimp [a] at *
        rw [hl, add_zero] at *
        unfold payoff
        nlinarith
      have hle := integral_mono_ae (majorant_integrable p hm hb q.ρ a l') (integrable_const _) hpoint
      refine ⟨hl ▸ (div_nonneg hB.le hρ.le), ?_⟩
      have heq : l' = d := by simp [l', hl, hd.le]
      simpa [Q] using (show (∫ ω, majorant q.ρ (Z ω) a l' ∂p) ≤ objective I x + q.ε/8 by
        simp only [integral_const, probReal_univ, one_smul, heq, hρd] at hle ⊢
        rw [← he, mul_zero, add_zero] at hη
        linarith)
    · have hl : 0 < l := div_pos he hc
      have heq : Q p q.ρ Z a l = η+c*s := by
        rw [Q_eq p hm hb, ha, ← hs2, ← hc2]
        dsimp [l]; field_simp; ring
      have hlow := Q_ge p hm hb h0 q.ρ a hl
      have htop := objective_le_bound I hρ.le hm h0 hb
      rw [heq] at hlow
      refine ⟨(le_div_iff₀ hρ).mpr (by linarith), ?_⟩
      have hi := majorant_integrable p hm hb q.ρ a l
      have H := integral_mono (majorant_integrable p hm hb q.ρ a l') (hi.add (integrable_const _))
        (fun ω => scale_rise (ρ := q.ρ) (z := Z ω) (a := a) hl (le_max_right d l))
      change Q p q.ρ Z a l' ≤ ∫ ω, majorant q.ρ (Z ω) a l + q.ρ*(l'-l) ∂p at H
      rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul] at H
      change _ ≤ Q p q.ρ Z a l + _ at H
      rw [heq] at H
      linarith [mul_le_mul_of_nonneg_left hd' hρ.le]
  let b := max 0 (min q.B a)
  refine ⟨b, ⟨le_max_left _ _, max_le hB.le (min_le_left _ _)⟩, l',
    ⟨le_max_left _ _, max_le hdB hlB⟩, le_trans ?_ hQ⟩
  exact integral_mono (majorant_integrable p hm hb q.ρ b l') (majorant_integrable p hm hb q.ρ a l')
    (fun ω => clamp_centre hl' (hz ω))

lemma bracket_cover (hρ : 0 < q.ρ) (hε : 0 < q.ε) {l : ℝ}
    (hl : l ∈ Icc (q.ε/(8*q.ρ)) (q.B/q.ρ)) :
    ∃ j < bracketCount q, l ∈ Icc (leftEndpoint q j) (2*leftEndpoint q j) ∧
      q.ρ*leftEndpoint q j ≤ q.B := by
  let d := q.ε/(8*q.ρ)
  have hd : 0 < d := by dsimp [d]; positivity
  let n := ⌊l/d⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr ((one_le_div hd).mpr hl.1)
  have hu : l/d ≤ 8*q.B/q.ε := by
    dsimp [d]; field_simp [hε, hρ]; linarith [(le_div_iff₀ hρ).mp hl.2]
  let j := Nat.log 2 n
  have hj := Nat.log_mono_right (b := 2) (Nat.floor_mono hu)
  refine ⟨j, by unfold bracketCount; dsimp [j,n]; omega, ?_⟩
  have h1 : (2:ℝ)^j ≤ (n:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have h2 : n+1 ≤ 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have h2' : (n:ℝ)+1 ≤ (2:ℝ)^(j+1) := by exact_mod_cast h2
  have hlo := (le_div_iff₀ hd).mp (h1.trans (Nat.floor_le (show 0 ≤ l/d by
    exact div_nonneg (hd.le.trans hl.1) hd.le)))
  have hhi := (div_le_iff₀ hd).mp ((Nat.lt_floor_add_one (l/d)).le.trans h2')
  change (2^j*d ≤ l ∧ l ≤ 2*(2^j*d)) ∧ _
  rw [pow_succ] at hhi
  refine ⟨⟨hlo, by linarith⟩, ?_⟩
  change q.ρ*(2^j*d) ≤ _
  linarith [mul_le_mul_of_nonneg_left (hlo.trans hl.2) hρ.le, (le_div_iff₀ hρ).mp (hlo.trans hl.2)]

end
end OracleTemplate.ChiSquareBoundedCentreDro
