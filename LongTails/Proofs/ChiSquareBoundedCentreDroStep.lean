import LongTails.Proofs.ChiSquareBoundedCentreDroNoise
import LongTails.Proofs.ChiSquareBoundedCentreDroExecution
import LongTails.Proofs.ChiSquareConstants

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro
open ChiSquareDro (Adm clampTo clampTo_dist clampTo_mem proj_dist proj_fix)

noncomputable section
variable {q : Params} {I : Instance q} {proj : q.E → q.E}

def replyAt (I : Instance q) (proj : q.E → q.E) (x : q.E) (ω : q.Ξ) :=
  (proj x, I.loss (proj x) ω, I.sub (proj x) ω)

def trajectory (q : Params) (I : Instance q) (proj : q.E → q.E) (d : ℝ) (ξ : ℕ → q.Ξ) :
    ℕ → Triple q.E
  | 0 => (q.x0,0,d)
  | t+1 => let z := trajectory q I proj d ξ t
           nextPoint q d z (replyAt I proj z.1 (ξ t))

def energy (q : Params) (proj : q.E → q.E) (d : ℝ) (xs : q.E) (a l : ℝ) (z : Triple q.E) :=
  ‖proj z.1-xs‖^2/pointStep q + (z.2.1-a)^2/centreStep q + (z.2.2-l)^2/scaleStep q d

lemma clamp_energy {a b u γ : ℝ} (hu : u ∈ Icc a b) (hγ : 0 < γ) (z g : ℝ) :
    (clampTo a b (z-γ*g)-u)^2/γ ≤ (z-u)^2/γ + 2*g*(u-z)+γ*g^2 := by
  have h := clampTo_dist hu (z-γ*g)
  field_simp [hγ]
  linarith only [h]

lemma step_energy (h : Adm q I proj) (hq : spec.valid q) {d : ℝ} (hd : 0 < d)
    {xs : q.E} (hxs : xs ∈ I.domain) {a l : ℝ} (ha : a ∈ Icc 0 q.B) (hl : l ∈ Icc d (2*d))
    {z : Triple q.E} (hz : z.2.1 ∈ Icc 0 q.B ∧ z.2.2 ∈ Icc d (2*d)) (ω : q.Ξ) :
    let r := replyAt I proj z.1 ω
    energy q proj d xs a l (nextPoint q d z r) ≤ energy q proj d xs a l z -
      2*(majorant q.ρ r.2.1 z.2.1 z.2.2 - majorant q.ρ (I.loss xs ω) a l) +
      noise q d (weight r.2.1 z.2.1 z.2.2) := by
  intro r
  let x := proj z.1
  let v := weight r.2.1 z.2.1 z.2.2
  let g := r.2.2
  let X := pointStep q
  let A := centreStep q
  let D := scaleStep q d
  let s := q.ρ-(v-1)^2/2
  obtain ⟨hρ,hG,hB,hR,hε⟩ := hq
  have hX : 0 < X := by dsimp [X,pointStep]; positivity
  have hA : 0 < A := by dsimp [A,centreStep]; positivity
  have hD : 0 < D := by dsimp [D,scaleStep]; positivity
  have hdist := proj_dist h.proj_vi (x-X • (v • g)) hxs
  have hsq : ‖x-X • (v • g)-xs‖^2 =
      ‖x-xs‖^2+2*X*v*⟪g,xs-x⟫+X^2*‖v • g‖^2 := by
    rw [show x-X • (v • g)-xs = (x-xs)-X • (v • g) by abel, norm_sub_sq_real,
      real_inner_smul_right, real_inner_smul_right, ← real_inner_comm (x-xs) g,
      show xs-x = -(x-xs) by abel, inner_neg_right, norm_smul X, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hsq] at hdist
  have hx : ‖proj (x-X • (v • g))-xs‖^2/X ≤ ‖x-xs‖^2/X+2*v*⟪g,xs-x⟫+X*‖v • g‖^2 := by
    field_simp [hX]; linarith only [hdist]
  have hcent := clamp_energy ha hA z.2.1 (1-v)
  have hscale := clamp_energy hl hD z.2.2 s
  have hsupp := support (ρ := q.ρ) (a := z.2.1) (a' := a) (hd.trans_le hz.2.1) (hd.trans_le hl.1)
    (h.subgrad ω x (h.proj_mem _) xs hxs)
  change majorant q.ρ r.2.1 z.2.1 z.2.2 + v*⟪g,xs-x⟫ + (1-v)*(a-z.2.1) + s*(l-z.2.2) ≤ _ at hsupp
  have hn := noise_le q ⟨hρ,hG,hB,hR,hε⟩ hd hz.2.1 hz.1 (h.bounds ω x (h.proj_mem _)) g (h.sub_le ω x (h.proj_mem _))
  change X*‖v • g‖^2+A*(1-v)^2+D*s^2 ≤ noise q d v at hn
  change ‖proj (x-X • (v • g))-xs‖^2/X + (clampTo 0 q.B (z.2.1-A*(1-v))-a)^2/A +
    (clampTo d (2*d) (z.2.2-D*s)-l)^2/D ≤
    ‖x-xs‖^2/X+(z.2.1-a)^2/A+(z.2.2-l)^2/D - _ + noise q d v
  linarith only [hx,hcent,hscale,hsupp,hn]

lemma trajectory_mem (hB : 0 ≤ q.B) {d : ℝ} (hd : 0 ≤ d) (ξ : ℕ → q.Ξ) (t : ℕ) :
    let z := trajectory q I proj d ξ t
    z.2.1 ∈ Icc 0 q.B ∧ z.2.2 ∈ Icc d (2*d) := by
  cases t with
  | zero => exact ⟨⟨le_rfl,hB⟩,⟨le_rfl,show d ≤ 2*d by linarith⟩⟩
  | succ t => exact ⟨clampTo_mem hB _,clampTo_mem (by linarith) _⟩

lemma trajectory_past {d : ℝ} {ξ ζ : ℕ → q.Ξ} (t : ℕ) (h : ∀ i < t, ξ i = ζ i) :
    trajectory q I proj d ξ t = trajectory q I proj d ζ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [trajectory, ih (fun i hi => h i (by omega)), h t (by omega)]

lemma trajectory_meas (h : Adm q I proj) (d : ℝ) (t : ℕ) :
    Measurable (fun ξ => trajectory q I proj d ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let z := fun ξ => trajectory q I proj d ξ t
    have hx := h.proj_meas.comp ih.fst
    have hpair := hx.prodMk (measurable_pi_apply t)
    have hl := h.loss_meas.comp hpair
    have hg := h.sub_meas.comp hpair
    have ha := ih.snd.fst
    have hs := ih.snd.snd
    have hv := (((hl.sub (ha.sub hs)).max (measurable_const (a := (0:ℝ)))).div hs)
    exact (hx.sub ((hv.smul hg).const_smul _)).prodMk
      ((measurable_const.max (measurable_const.min (ha.sub (measurable_const.mul
        (measurable_const.sub hv))))).prodMk
       (measurable_const.max (measurable_const.min (hs.sub (measurable_const.mul
         (measurable_const.sub (((hv.sub_const 1).pow_const 2).div_const 2)))))))

lemma initial_energy (h : Adm q I proj) (hq : spec.valid q) {xs : q.E} (hR : ‖q.x0-xs‖ ≤ q.R)
    {a d l : ℝ} (ha : a ∈ Icc 0 q.B) (hd : 0 < d) (hl : l ∈ Icc d (2*d)) (hdB : q.ρ*d ≤ q.B) :
    energy q proj d xs a l (q.x0,0,d) ≤ (trainingCount q : ℝ)*q.ε/4 := by
  obtain ⟨hρ,hG,hB,_,hε⟩ := hq
  let c := 1+2*q.ρ
  have hc : 1 ≤ c := by dsimp [c]; linarith
  have hΓ : 0 < q.ρ^2+c*q.B^2/d^2 := by dsimp [c]; positivity
  have hT := Nat.le_ceil (256*c*(q.G^2*q.R^2+3*q.B^2)/q.ε^2)
  change _ ≤ (trainingCount q : ℝ) at hT
  rw [div_le_iff₀ (by positivity)] at hT
  have hx := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have he := pow_le_pow_left₀ ha.1 ha.2 2
  have hs : (d-l)^2 ≤ d^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hl.2) (show 0 ≤ l by linarith [hl.1])]
  have hb := pow_le_pow_left₀ (mul_nonneg hρ.le hd.le) hdB 2
  have H : (d-l)^2*(q.ρ^2+c*q.B^2/d^2) ≤ q.B^2+c*q.B^2 := by
    refine (mul_le_mul_of_nonneg_right hs hΓ.le).trans ?_
    rw [mul_add, show d^2*(c*q.B^2/d^2) = c*q.B^2 by field_simp]
    nlinarith
  have hcB := mul_le_mul_of_nonneg_right hc (sq_nonneg q.B)
  unfold energy pointStep centreStep scaleStep
  dsimp only
  rw [proj_fix h.proj_vi h.x0_mem, zero_sub, neg_sq]
  simp only [div_div_eq_mul_div]
  change ‖q.x0-xs‖^2*(64*c*q.G^2)/q.ε + a^2*(64*c)/q.ε +
    (d-l)^2*(64*(q.ρ^2+c*q.B^2/d^2))/q.ε ≤ _
  rw [← add_div, ← add_div, div_le_iff₀ hε]
  nlinarith only [hT,mul_le_mul_of_nonneg_right hx (show 0 ≤ c*q.G^2 by dsimp [c]; positivity),
    mul_le_mul_of_nonneg_right he (by dsimp [c]; positivity : 0 ≤ c),H,hcB]

end
end OracleTemplate.ChiSquareBoundedCentreDro
