import LongTails.Proofs.ChiSquareBoundedCentreDroPerspective

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open ChiSquareDro LongTails.Setups.ChiSquareConstrainedDro
noncomputable section

variable {q : Params} (I : Instance q) {x : q.E}

lemma weight_memLp (hm : Measurable (I.loss x)) (hz : ∀ ω, I.loss x ω ∈ Icc 0 q.B)
    {a l : ℝ} (ha : a ∈ Icc 0 q.B) (hl : 0 < l) :
    MemLp (fun ω => weight (I.loss x ω) a l) 2 (I.law : Measure q.Ξ) := by
  apply MemLp.of_bound (C := q.B/l + 1)
  · unfold weight; fun_prop
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hl)]
    linarith [(abs_le.mp (weight_width hl (hz ω) ha)).2]

lemma centred_moment (hρ : 0 ≤ q.ρ) (hm : Measurable (I.loss x))
    (hz : ∀ ω, I.loss x ω ∈ Icc 0 q.B) {a l : ℝ} (ha : a ∈ Icc 0 q.B) (hl : 0 < l) (t : ℝ) :
    (∫ ω, (weight (I.loss x ω) a l - t)^2 ∂(I.law : Measure q.Ξ)) ≤
      4*(Q I.law q.ρ (I.loss x) a l - objective I x)/l + 4*q.ρ + 2*(1-t)^2 := by
  let p := (I.law : Measure q.Ξ)
  let Z := I.loss x
  let v := fun ω => weight (Z ω) a l
  let S := ∫ ω, (v ω-t)^2 ∂p
  let A := a/l-(1+t)
  let C := (1+t^2)/2-a/l-q.ρ
  have hA : l*A = a-l*(1+t) := by dsimp [A]; field_simp
  have hC : l*C = l*((1+t^2)/2-q.ρ)-a := by dsimp [C]; field_simp; ring
  have hv := weight_memLp I hm hz ha hl
  have hv2 : Integrable (fun ω => (v ω-t)^2) p := (hv.sub (memLp_const t)).integrable_sq
  have hH := majorant_integrable p hm (fun ω => (hz ω).2) q.ρ a l
  have hobj : objective I x ≤ Q p q.ρ Z a l + l*(q.ρ+(1-t)^2/2) - l/4*S := by
    apply csSup_le
    · exact ⟨_, fun _ => 1, one_feasible _ hρ, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hw1 : ∫ ω, w ω ∂p = 1 := hw.2.2.2.1
      have hwi := Feasible.integrable p hw
      have hw2 := Feasible.integrable_sq p hw
      have hwc := Feasible.second p hw
      have hi := integrable_density_mul I hw hm (fun ω => by
        rw [abs_of_nonneg (hz ω).1]; exact (hz ω).2)
      let poly := fun ω => w ω ^ 2 + A*w ω + C
      have hpoly : Integrable poly p := (hw2.add (hwi.const_mul A)).add (integrable_const C)
      have hpt (ω) : w ω * Z ω + l/4*(v ω-t)^2 ≤
          majorant q.ρ (Z ω) a l + l*poly ω := by
        have hgap := payoff_gap (ρ := q.ρ) (z := Z ω) (a := a) hl (hw.2.1 ω)
        change payoff q.ρ (Z ω) a l (w ω) + l/2*(v ω-w ω)^2 ≤ _ at hgap
        unfold payoff at hgap
        dsimp [poly]
        linear_combination hgap + (l/4)*sq_nonneg (v ω-2*w ω+t) + (w ω)*hA.symm + hC.symm
      have hint := integral_mono (hi.add (hv2.const_mul (l/4))) (hH.add (hpoly.const_mul l)) hpt
      change (∫ ω, w ω*Z ω + l/4*(v ω-t)^2 ∂p) ≤ ∫ ω, majorant q.ρ (Z ω) a l + l*poly ω ∂p at hint
      rw [integral_add (f := fun ω => w ω*Z ω) (g := fun ω => l/4*(v ω-t)^2) hi (hv2.const_mul _),
        integral_add (f := fun ω => majorant q.ρ (Z ω) a l) (g := fun ω => l*poly ω) hH (hpoly.const_mul _),
        integral_const_mul, integral_const_mul] at hint
      have hpolyE : (∫ ω, poly ω ∂p) = (∫ ω, w ω ^ 2 ∂p) + A + C := by
        rw [show (∫ ω, poly ω ∂p) = _ from integral_quad p hwi hw2 A C, hw1, mul_one]
      rw [hpolyE] at hint
      change (∫ ω, w ω*Z ω ∂p) + l/4*S ≤ Q p q.ρ Z a l + l*((∫ ω, w ω^2 ∂p)+A+C) at hint
      have hAC : A+C = -(1+t)+(1+t^2)/2-q.ρ := by dsimp [A,C]; ring
      change (∫ ω, w ω * Z ω ∂p) ≤ _
      linarith only [hint, mul_le_mul_of_nonneg_left hwc hl.le, congrArg (l * ·) hAC]
  change S ≤ _
  field_simp [hl]
  linarith only [hobj]

end
end OracleTemplate.ChiSquareBoundedCentreDro
