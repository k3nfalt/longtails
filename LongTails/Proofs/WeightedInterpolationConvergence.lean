import LongTails.Proofs.WeightedInterpolationAdaptive
import LongTails.Proofs.WeightedInterpolationTuning

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationConvergence

open MeasureTheory Metric
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationPrecision
open WeakInterpolationGeometry WeightedInterpolationStep WeightedInterpolationSampling
open WeightedInterpolationDescent WeightedInterpolationAdaptive WeightedInterpolationTuning

variable {p : Params} {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

lemma rounding_expected (hp : spec.valid p) {d : ℝ} (hd : d ≤ scale p^2) :
    64*tolerance p*scale p*(1+d/scale p^2) ≤ p.ε/(32*rounds p) := by
  have hB := (scale_bounds hp).1
  have he := tolerance_pos hp
  have hK : 0 < (rounds p : ℝ) := by exact_mod_cast (show 0 < rounds p by unfold rounds; omega)
  have h1 := (div_le_one (sq_pos_of_pos hB)).mpr hd
  calc
    _ ≤ 64*tolerance p*scale p*2 := by gcongr; linarith
    _ = _ := by unfold tolerance; field_simp; ring

lemma radius_control_of_model (D : Model p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (hk : k ≤ rounds p) :
    (∫ s, ‖iterate p T g s k-z‖^2 ∂P) ≤ scale p^2 := by
  let E := fun j => ∫ s, ‖iterate p T g s j-z‖^2 ∂P
  have h : ∀ j ≤ rounds p, E j ≤ p.R^2+(j : ℝ)*((phase p : ℝ)+1)*p.ε := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa [E,iterate] using pow_le_pow_left₀ (norm_nonneg _) D.initial 2
    | succ j ih =>
      intro hj
      have hb := ih (by omega)
      have hround := rounding_expected D.valid (hb.trans (coarse_radius D.valid (by omega)))
      have hfix (x : Point p) := fixed_descent_of_model D T j x z D.solution le_rfl
      have hstep := adaptive_of_model D T j (fun x => ‖x-z‖^2) (by fun_prop) (fun _ => sq_nonneg _) 1 (fun x => by
        have hh := hfix x
        unfold varianceTerm perturbation
        linarith only [hh,mul_nonneg (step_bounds D.valid j).1 (sub_nonneg.mpr (surrogate_min (weight_nonneg D.valid) D.solution x))])
      change E (j+1) ≤ 1*E j+varianceTerm p j+_ at hstep
      have hcoarse := coarse_variance D.valid j
      change varianceTerm p j ≤ _ at hcoarse
      have he := D.valid.2.2.2.2.2.2
      have hK : 1 ≤ (rounds p : ℝ) := by exact_mod_cast (show 1 ≤ rounds p by unfold rounds; omega)
      have hsmall : p.ε/(32*rounds p) ≤ p.ε := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hK he.le]
      push_cast
      linarith only [hstep,hcoarse,hround,hsmall,hb]
  exact (h k hk).trans (coarse_radius D.valid hk)

lemma radius_control (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (hk : k ≤ rounds p) :
    (∫ s, ‖iterate p T g s k-z‖^2 ∂P) ≤ scale p^2 :=
  radius_control_of_model D.model T k hk

lemma accuracy_of_model (D : Model p f g z P ν) (T : DistributedTemplate.Time) :
    ∫ s, infDist (output p T g s) (solutions p f)^2 ∂P ≤ p.ε := by
  let E j := ∫ s, infDist (iterate p T g s j) (solutions p f)^2 ∂P
  let I := information p
  let H := phase p
  let m : ℝ := period p
  let t := (batchTime p : ℝ)
  let V := 4*p.σ^2/(I*t)
  let e := p.ε/(32*rounds p)
  have hi : 0 < I := information_pos D.valid
  have hh : 0 < (H : ℝ) := by dsimp [H]; exact_mod_cast phase_pos p
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (show 1 ≤ period p from period_pos p)
  have hm' : 0 < m := by linarith
  have ht : 0 < t := by dsimp [t]; exact_mod_cast (D.valid.1 0).trans_le (local_time p 0)
  have heps := D.valid.2.2.2.2.2.2
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have h0 : E 0 ≤ p.R^2 := by
    have hx := infDist_le_dist_of_mem (x := p.x0) D.solution
    rw [dist_eq_norm] at hx
    simpa [E,iterate] using pow_le_pow_left₀ infDist_nonneg (hx.trans D.initial) 2
  have hrec (k : ℕ) (hk : k ≤ rounds p) :
      E (k+1) ≤ (1-stepSize p k*I/2)*E k + varianceTerm p k + e := by
    have h := adaptive_of_model D T k _ ((continuous_infDist_pt (solutions p f)).pow 2).measurable
      (fun x => sq_nonneg _) _ (fixed_distance_of_model D T k)
    exact h.trans (add_le_add le_rfl (rounding_expected D.valid (radius_control_of_model D T k hk)))
  have warm (k : ℕ) (hk : k < H) : E (k+1) ≤ (1-1/m)*E k+4*V/m^2+e := by
    have hk' : k ≤ rounds p := by unfold rounds; dsimp [H] at hk; omega
    have h := hrec k hk'
    have hη : stepSize p k = 2/(I*m) := ite_eq_left hk
    unfold varianceTerm at h
    rw [hη] at h
    refine h.trans_eq ?_
    change (1-2/(I*m)*I/2)*E k+4*(2/(I*m))^2*p.σ^2*I/t+e = _
    unfold V
    field_simp [hi.ne',hm'.ne',ht.ne']; ring
  have w := WeakInterpolationSchedule.initial_phase hm hV he h0 warm H le_rfl
  have hw : E H ≤ p.ε/64+4*V/m+(H:ℝ)*e := by linarith only [w,warm_decay D.valid]
  have cool (j : ℕ) (hj : j < H) : let s : ℝ := 2*m+j
      E (H+j+1) ≤ (1-2/s)*E (H+j)+16*V/s^2+e := by
    have hk : H+j ≤ rounds p := by unfold rounds; dsimp [H] at *; omega
    have h := hrec (H+j) hk
    have hη : stepSize p (H+j) = 4/(I*(2*m+j)) := by
      unfold stepSize
      rw [ite_eq_right (show ¬ H+j < phase p by dsimp [H]; omega)]
      simp [H,I,m]
    unfold varianceTerm at h
    rw [hη] at h
    refine h.trans_eq ?_
    change (1-4/(I*(2*m+j))*I/2)*E (H+j)+4*(4/(I*(2*m+j)))^2*p.σ^2*I/t+e = _
    unfold V
    have hjpos : 0 < 2*m+(j : ℝ) := by positivity
    field_simp [hi.ne',hjpos.ne',ht.ne']; ring
  have c := WeakInterpolationSchedule.final_phase hm (show 0 ≤ p.ε/64 by positivity) hV he hw cool H le_rfl
  have hV' : 64*V ≤ (H:ℝ)*p.ε := by
    dsimp [V]
    rw [←mul_div_assoc,div_le_iff₀ (mul_pos hi ht)]
    linarith only [variance_scale D.valid]
  have hs : 16*V/(2*m+H) ≤ p.ε/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hm'.le heps.le]
  have he' : ((H+H : ℕ):ℝ)*e ≤ p.ε/32 := by
    have hK : 0 < (rounds p : ℝ) := by exact_mod_cast (show 0 < rounds p by unfold rounds; omega)
    dsimp [e]
    rw [←mul_div_assoc,div_le_iff₀ (by positivity : 0 < 32*(rounds p : ℝ))]
    have hk : ((H+H : ℕ):ℝ) ≤ rounds p := by exact_mod_cast (show H+H ≤ rounds p by unfold rounds; dsimp [H]; omega)
    linarith only [mul_le_mul_of_nonneg_right hk heps.le]
  change E (2*H) ≤ p.ε
  rw [two_mul]
  linarith only [c,hs,he',heps]

lemma accuracy (D : Data p f g z P ν) (T : DistributedTemplate.Time) :
    ∫ s, infDist (output p T g s) (solutions p f)^2 ∂P ≤ p.ε :=
  accuracy_of_model D.model T

end LongTails.Proofs.WeightedInterpolationConvergence
