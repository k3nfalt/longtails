import LongTails.Proofs.ChiSquareBoundedCentreDroMoments

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro

noncomputable section
variable (q : Params)

def centreStep := q.ε/(64*(1+2*q.ρ))
def scaleStep (d : ℝ) := q.ε/(64*(q.ρ^2+(1+2*q.ρ)*q.B^2/d^2))
def pointStep := q.ε/(64*(1+2*q.ρ)*q.G^2)

def noise (d v : ℝ) :=
  centreStep q*v^2 + (centreStep q + scaleStep q d*(q.B^2/(2*d^2)))*(v-1)^2 +
  2*scaleStep q d*q.ρ^2

lemma noise_le (hq : spec.valid q) {d l a z : ℝ} (hd : 0 < d) (hl : d ≤ l)
    (ha : a ∈ Icc 0 q.B) (hz : z ∈ Icc 0 q.B) (g : q.E) (hg : ‖g‖ ≤ q.G) :
    let v := weight z a l
    pointStep q * ‖v • g‖^2 + centreStep q*(1-v)^2 +
      scaleStep q d*(q.ρ-(v-1)^2/2)^2 ≤ noise q d v := by
  intro v
  obtain ⟨hρ,hG,hB,_,hε⟩ := hq
  have hx : 0 < pointStep q := by unfold pointStep; positivity
  have hs : 0 < scaleStep q d := by unfold scaleStep; positivity
  have hxe : pointStep q*q.G^2 = centreStep q := by unfold pointStep centreStep; field_simp
  have hv : |v-1| ≤ q.B/d := (weight_width (hd.trans_le hl) hz ha).trans
    (div_le_div_of_nonneg_left hB.le hd hl)
  have hv2 := pow_le_pow_left₀ (abs_nonneg _) hv 2
  rw [sq_abs, div_pow] at hv2
  have hscale : (q.ρ-(v-1)^2/2)^2 ≤ 2*q.ρ^2 + q.B^2/(2*d^2)*(v-1)^2 := by
    have H := mul_le_mul_of_nonneg_right hv2 (sq_nonneg (v-1))
    rw [show q.B^2/(2*d^2) = (q.B^2/d^2)/2 by ring]
    nlinarith [sq_nonneg (q.ρ+(v-1)^2/2)]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold noise
  have Hg := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hg 2)
    (mul_nonneg hx.le (sq_nonneg v))
  linear_combination Hg + scaleStep q d * hscale + v^2*hxe

lemma expected_noise (hq : spec.valid q) (I : Instance q) {x : q.E}
    (hm : Measurable (I.loss x)) (hz : ∀ ω, I.loss x ω ∈ Icc 0 q.B) {a d l L : ℝ}
    (ha : a ∈ Icc 0 q.B) (hd0 : q.ε/(8*q.ρ) ≤ d) (hl : d ≤ l) (hmin : L ≤ objective I x)
    (hgap : L ≤ Q I.law q.ρ (I.loss x) a l) :
    (∫ ω, noise q d (weight (I.loss x ω) a l) ∂(I.law : Measure q.Ξ)) ≤
      6*q.ε/64 + (5/8)*(Q I.law q.ρ (I.loss x) a l-L) := by
  obtain ⟨hρ,hG,hB,_,hε⟩ := hq
  have hd := lt_of_lt_of_le (by positivity : 0 < q.ε/(8*q.ρ)) hd0
  have hl' := hd.trans_le hl
  let Δ := Q I.law q.ρ (I.loss x) a l - L
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hgap
  let p := (I.law : Measure q.Ξ)
  let v := fun ω => weight (I.loss x ω) a l
  let A := centreStep q
  let D := scaleStep q d
  let b := q.B^2/(2*d^2)
  let c := 1+2*q.ρ
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 < A := by dsimp [A,centreStep]; positivity
  have hD : 0 < D := by dsimp [D,scaleStep]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hv := weight_memLp I hm hz ha hl'
  have hi : Integrable (fun ω => v ω ^ 2) p := hv.integrable_sq
  have hi' : Integrable (fun ω => (v ω-1)^2) p := (hv.sub (memLp_const 1)).integrable_sq
  have hratio : 4*(Q p q.ρ (I.loss x) a l-objective I x)/l ≤ 4*Δ/d := by
    refine le_trans (b := 4*Δ/l) (div_le_div_of_nonneg_right (by dsimp [p,Δ]; linarith) hl'.le) ?_
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hΔ) hd hl
  have h1 := centred_moment I hρ.le hm hz ha hl' 0
  simp only [sub_zero, one_pow, mul_one] at h1
  have h2 := centred_moment I hρ.le hm hz ha hl' 1
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at h2
  have hu : (∫ ω, v ω ^ 2 ∂p) ≤ 2*c+4*Δ/d := by dsimp [v,p,c]; linarith
  have hu' : (∫ ω, (v ω-1)^2 ∂p) ≤ 4*q.ρ+4*Δ/d := by dsimp [v,p]; linarith
  have hconst : A*c = q.ε/64 := by dsimp [A,c,centreStep]; field_simp
  have hDden : D*(q.ρ^2+c*q.B^2/d^2) = q.ε/64 := by
    have H : 0 < q.ρ^2+c*q.B^2/d^2 := by positivity
    change q.ε/(64*(q.ρ^2+c*q.B^2/d^2)) * _ = _
    field_simp
  have heqb : 2*b=q.B^2/d^2 := by dsimp [b]; ring
  have hcd : D*(q.ρ^2+2*c*b) = q.ε/64 := by linear_combination hDden - D*c*heqb
  have hDb : 2*D*b ≤ A := by
    apply le_of_mul_le_mul_right (a := c)
    · nlinarith [mul_nonneg hD.le (sq_nonneg q.ρ)]
    · exact hc
  have hρc : 2*q.ρ ≤ c := by dsimp [c]; linarith
  have hstep : A/d ≤ 1/16 := by
    change q.ε/(64*c)/d ≤ 1/16
    rw [div_le_iff₀ hd, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hd0
    nlinarith [mul_le_mul_of_nonneg_right hρc hd.le]
  have hcoef : 4*A/d + 4*(A+D*b)/d ≤ 5/8 := by
    have H := (div_le_iff₀ hd).mp hstep
    rw [← add_div, div_le_iff₀ hd]
    linarith
  have hconstant : A*(2*c)+(A+D*b)*(4*q.ρ)+2*D*q.ρ^2 ≤ 6*q.ε/64 := by
    have hh := mul_le_mul_of_nonneg_left hρc hA.le
    have hh' := mul_le_mul_of_nonneg_left (show q.ρ ≤ c by linarith) (mul_nonneg hD.le hb)
    linarith only [hconst,hcd,hh,hh']
  change (∫ ω, A*v ω^2 + (A+D*b)*(v ω-1)^2 + 2*D*q.ρ^2 ∂p) ≤ _
  rw [ChiSquareDro.integral_add_const' p (f := fun ω => A*v ω^2+(A+D*b)*(v ω-1)^2) ((hi.const_mul A).add (hi'.const_mul _)),
    integral_add (f := fun ω => A*v ω^2) (g := fun ω => (A+D*b)*(v ω-1)^2)
      (hi.const_mul _) (hi'.const_mul _), integral_const_mul, integral_const_mul]
  change _ ≤ 6*q.ε/64+(5/8)*Δ
  linear_combination A*hu + (A+D*b)*hu' + Δ*hcoef + hconstant

end
end OracleTemplate.ChiSquareBoundedCentreDro
