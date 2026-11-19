import LongTails.Proofs.DuelingReferenceSampling

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceDrift
open LongTails.Proofs.DuelingReferenceField
open LongTails.Proofs.DuelingReferenceSampling

namespace LongTails.Proofs.DuelingReferencePotential

noncomputable def storage (μ m V ε t Z D : ℝ) : ℝ :=
  t*(t+1)/2*(Z-ε/4) + μ/8*t*(t+1)*D - 2*t*V/(m^2*μ)

lemma scalar_step {μ m V ε t Z Z' X D D' g : ℝ} (hμ : 0 < μ) (hm : 0 < m) (ht : 0 ≤ t)
    (hz : (t+2)*Z' ≤ t*Z+2*X)
    (hd : D' ≤ D-2*(4/(m*μ*(t+2)))*g+(4/(m*μ*(t+2)))^2*V) (hV : 0 ≤ V) :
    storage μ m V ε (t+1) Z' D' ≤ storage μ m V ε t Z D +
      ((t+1)/m)*(m*X + m*μ/4*D - m*ε/4 - g) := by
  have ht' : 0 < t+2 := by linarith
  have ha := mul_le_mul_of_nonneg_left hz (show 0 ≤ (t+1)/2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hd (show 0 ≤ μ/8*(t+1)*(t+2) by positivity)
  have hnoise : μ/8*(t+1)*(t+2)*((4/(m*μ*(t+2)))^2*V) ≤ 2*V/(m^2*μ) := by
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ t+2 by linarith) hV]
  have hg : μ/8*(t+1)*(t+2)*(2*(4/(m*μ*(t+2)))*g) = (t+1)/m*g := by
    field_simp
    ring
  rw [mul_add _ (D-_) _, mul_sub _ D _,hg] at hb
  unfold storage
  have he : 2*(t+1)*V/(m^2*μ) = 2*t*V/(m^2*μ)+2*V/(m^2*μ) := by ring
  rw [he]
  have hc : ((t+1)/m)*(m*X+m*μ/4*D-m*ε/4-g) =
      (t+1)*(X+μ/4*D-ε/4)-(t+1)/m*g := by field_simp
  rw [hc]
  linarith

noncomputable def energy {p : Params} (f : Point p.d → ℝ) (u : Point p.d) (s : State p.d) : ℝ :=
  storage p.μ (slope p) ((p.d/radius p)^2) p.ε s.1
    (f s.2.2.val-f u) (‖s.2.1.val-u‖^2)

lemma objective_mix {p : Params} {f : Point p.d → ℝ} (hμ : 0 < p.μ) (hf : Objective p f)
    {x z : Point p.d} (hx : x ∈ Ball p.d) (hz : z ∈ Ball p.d)
    {t : ℝ} (ht : 0 ≤ t) :
    (t+2)*f ((t/(t+2)) • z + (2/(t+2)) • x) ≤ t*f z + 2*f x := by
  let y := (t/(t+2)) • z + (2/(t+2)) • x
  have ht' : 0 < t+2 := by linarith
  have hsum : t/(t+2) + 2/(t+2) = 1 := by field_simp
  have hy : y ∈ Ball p.d := (convex_closedBall (0 : Point p.d) 1) hz hx (by positivity) (by positivity) hsum
  have hcut (a : Point p.d) (ha : a ∈ Ball p.d) : f y + ⟪gradient f y,a-y⟫ ≤ f a := by
    nlinarith [hf.strongly_convex y hy a ha, mul_nonneg hμ.le (sq_nonneg ‖a-y‖)]
  have hvec : t • (z-y) + (2:ℝ) • (x-y) = 0 := by
    calc
      _ = t • z + (2:ℝ) • x - (t+2) • y := by module
      _ = 0 := by
        dsimp only [y]
        rw [smul_add, smul_smul, smul_smul, show (t+2)*(t/(t+2)) = t by field_simp,
          show (t+2)*(2/(t+2)) = 2 by field_simp]
        abel
  have hi := congrArg (fun w => ⟪gradient f y,w⟫) hvec
  simp only [inner_add_right,inner_smul_right,inner_zero_right] at hi
  change (t+2)*f y ≤ _
  nlinarith [mul_le_mul_of_nonneg_left (hcut z hz) ht,hcut x hx]

lemma projected_step {p : Params} (hp : spec.valid p) (f : Point p.d → ℝ) (hf : Objective p f)
    (u : Ball p.d) (s : State p.d) (a : Draw p.d) (b : Bool) :
    energy (p := p) f u (update p s a b) ≤ energy (p := p) f u s +
      (((s.1:ℝ)+1)/(slope p))*(target (p := p) f s.2.1 u -
        ⟪s.2.1.val-u.val, estimate p a b⟫) := by
  let t := (s.1:ℝ)
  let x := s.2.1.val
  let z := s.2.2.val
  let m := slope p
  let η := 4/(m*p.μ*(t+2))
  let G := estimate p a b
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have ht' : 0 < t+2 := by linarith
  have hm : 0 < m := (tuning hp).1
  have hμ := hp.1
  have hη : 0 ≤ η := by unfold η; positivity
  have hsum : t/(t+2) + 2/(t+2) = 1 := by field_simp
  have hav := (convex_closedBall (0 : Point p.d) 1) s.2.2.property s.2.1.property
    (by positivity : 0 ≤ t/(t+2)) (by positivity : 0 ≤ 2/(t+2)) hsum
  have hz := objective_mix hp.1 hf s.2.1.property s.2.2.property ht
  have hd := pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_sub_le (by norm_num : (0:ℝ)≤1)
    (norm_ball u.property) (x-η • G)) 2
  rw [show x-η • G-u.val = (x-u.val)-η • G by abel, norm_sub_sq_real (x-u.val) (η • G), inner_smul_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_pow] at hd
  have hG : ‖G‖ = (p.d:ℝ)/radius p := norm_estimate p hp a b
  rw [hG] at hd
  unfold energy
  dsimp only [update, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one]
  rw [retract_eq hav, Nat.cast_succ]
  unfold target
  apply scalar_step hp.1 hm ht _ _ (sq_nonneg _)
  · dsimp only [t,x,z] at hz ⊢
    linarith
  · change ‖OracleTemplate.clip 1 (x-η • G)-u.val‖^2 ≤ _
    convert hd using 1; ring

end LongTails.Proofs.DuelingReferencePotential
