import LongTails.Proofs.OptimumHeterogeneityAdaptive
import LongTails.Proofs.OptimumHeterogeneityTuning

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.OptimumHeterogeneityConvergence

open MeasureTheory Metric
open LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneitySgd LongTails.Algorithms.OptimumHeterogeneityDesign
open OptimumHeterogeneityGrowth OptimumHeterogeneityDrift OptimumHeterogeneityAllocation
open OptimumHeterogeneityPrecision OptimumHeterogeneityStep OptimumHeterogeneityMoments
open OptimumHeterogeneityAdaptive OptimumHeterogeneityDescent OptimumHeterogeneityTuning

variable {p : Params} {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

lemma rounding_expected (hp : spec.valid p) {d : ℝ} (hd : d ≤ scale p^2) :
    192*tolerance p*scale p*(1+d/scale p^2) ≤ p.ε^2/(8*rounds p) := by
  have hB := (scale_bounds hp).1
  have he := tolerance_pos hp
  have hK : 0 < (rounds p : ℝ) := by exact_mod_cast round_pos p
  have h1 := (div_le_one (sq_pos_of_pos hB)).mpr hd
  calc
    _ ≤ 192*tolerance p*scale p*2 := by gcongr; linarith
    _ ≤ _ := by unfold tolerance; field_simp; nlinarith [sq_nonneg p.ε]

lemma coarse_bias {η ε B d : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (he : 0 < ε)
    (hB : 0 < B) (heb : ε ≤ B) (hd : 0 ≤ d) :
    2*η*(ε/64)*d+(η*(ε/64))^2 ≤ B*ε/4*(1+d^2/B^2) := by
  have h₁ := mul_le_mul_of_nonneg_right hη' (show 0 ≤ ε/64 by positivity)
  have h₂ := pow_le_pow_left₀ (mul_nonneg hη (by positivity : 0 ≤ ε/64)) h₁ 2
  have h₃ := mul_le_mul_of_nonneg_right h₁ hd
  have h₄ := mul_le_mul_of_nonneg_right heb he.le
  have h₅ := mul_nonneg he.le (sq_nonneg (B-d))
  have h₆ := mul_le_mul_of_nonneg_right h₄ hB.le
  calc
    _ ≤ 2*(ε/64)*d+(ε/64)^2 := by linarith only [h₂,h₃]
    _ ≤ _ := by
      field_simp
      nlinarith only [mul_nonneg hB.le h₅, mul_le_mul_of_nonneg_right h₆ hB.le,
        mul_nonneg (mul_nonneg he.le (sq_nonneg d)) hB.le, mul_nonneg he.le (pow_nonneg hB.le 3)]

lemma fixed_distance (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x : Point p) :
    ∫ s, infDist (x-estimate p T k g x s) (solutions p f)^2 ∂P ≤
      (1-stepSize p k/4)*infDist x (solutions p f)^2+
      (varianceTerm p k+stepSize p k*p.ε^2/64)+
      192*tolerance p*scale p*(1+‖x-z‖^2/scale p^2) := by
  obtain ⟨y,hy,hd⟩ := (solution_closed D.toGeometry).exists_infDist_eq_dist ⟨z,D.optimal⟩ x
  rw [dist_eq_norm] at hd
  have hmin := infDist_le_dist_of_mem (x := x) D.optimal
  rw [dist_eq_norm,hd] at hmin
  have hh := fixed_descent D T k x y hy hmin
  have hg : ‖x-y‖^2/2 ≤ gap p f y x := weighted_growth D.toGeometry hy x hd
  have hη := (step_bounds D.valid k).1
  have he := D.valid.1.2.2.2.2.2.2
  have hsq := mul_le_mul_of_nonneg_left (step_le_one D.valid k) hη
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg p.ε)
  have hb := mul_nonneg hη (sq_nonneg (‖x-y‖ - p.ε/16))
  have hmono := integral_mono (fixed_integrable D T k x (fun v => infDist v (solutions p f)^2)
      ((continuous_infDist_pt _).pow 2).measurable)
    (fixed_integrable D T k x (fun v => ‖v-y‖^2) (by fun_prop))
    (fun s => pow_le_pow_left₀ infDist_nonneg (by simpa [dist_eq_norm] using
      (infDist_le_dist_of_mem (x := x-estimate p T k g x s) hy)) 2)
  rw [hd]
  nlinarith only [hh,hmono,hb,hm,mul_le_mul_of_nonneg_left hg hη,mul_nonneg hη (sq_nonneg p.ε)]

lemma radius_control (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (hk : k ≤ rounds p) :
    (∫ s, ‖iterate p T g s k-z‖^2 ∂P) ≤ scale p^2 := by
  let E j := ∫ s, ‖iterate p T g s j-z‖^2 ∂P
  have h : ∀ j ≤ rounds p, E j ≤ p.R^2+(j : ℝ)*(scale p*p.ε+((phase p : ℝ)+1)*p.ε^2) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa [E,iterate] using pow_le_pow_left₀ (norm_nonneg _) D.initial 2
    | succ j ih =>
      intro hj
      have hb := ih (by omega)
      have hsc := hb.trans (coarse_radius D.valid (by omega))
      have hround := rounding_expected D.valid hsc
      have hB := scale_bounds D.valid
      have he := D.valid.1.2.2.2.2.2.2
      have hη := (step_bounds D.valid j).1
      have hstep := adaptive D T j (fun x => ‖x-z‖^2) (by fun_prop) (fun _ => sq_nonneg _) 1
        (varianceTerm p j) (192*tolerance p*scale p+scale p*p.ε/4) (fun x => by
          have hh := fixed_descent D T j x z D.optimal le_rfl
          have hgap : 0 ≤ gap p f z x := Finset.sum_nonneg fun i _ => mul_nonneg (weight_nn D.valid i)
            (OptimumHeterogeneityGeometry.remainder_bounds (D.convex i) (D.grad i) (D.lip i) z x).1
          have hv := coarse_bias hη (step_le_one D.valid j) he hB.1 hB.2.1 (norm_nonneg (x-z))
          linarith only [hh,mul_nonneg hη hgap,hv])
      change E (j+1) ≤ 1*E j+varianceTerm p j+_*(1+E j/scale p^2) at hstep
      have hK : 1 ≤ (rounds p : ℝ) := by exact_mod_cast round_pos p
      have hsmall : p.ε^2/(8*rounds p) ≤ p.ε^2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg p.ε)]
      have h2 := (div_le_one (sq_pos_of_pos hB.1)).mpr hsc
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hB.1.le he.le)
      push_cast
      linarith only [hstep,hround,hsmall,h3,coarse_variance D.valid j,hb,mul_nonneg hB.1.le he.le]
  exact (h k hk).trans (coarse_radius D.valid hk)

lemma accuracy (D : Data p f g z P ν) (T : DistributedTemplate.Time) :
    ∫ s, infDist (output p T g s) (solutions p f)^2 ∂P ≤ p.ε^2 := by
  let F j := ∫ s, infDist (iterate p T g s j) (solutions p f)^2 ∂P
  let E j := F j - p.ε^2/16
  let H := phase p
  let m : ℝ := period p
  let t := (batchTime p : ℝ)
  let V := 16*p.σ^2*cost p (weights p)/t
  let e := p.ε^2/(8*rounds p)
  have hh : 0 < (H : ℝ) := by dsimp [H]; exact_mod_cast phase_pos p
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (show 1 ≤ period p by have := period_lower p; omega)
  have hm' : 0 < m := by linarith
  have ht : 0 < t := by dsimp [t]; exact time_pos D.valid
  have heps := D.valid.1.2.2.2.2.2.2
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hcost := cost_nn p
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have h0 : E 0 ≤ p.R^2 := by
    have hx := infDist_le_dist_of_mem (x := p.x0) D.optimal
    rw [dist_eq_norm] at hx
    apply (sub_le_self (F 0) (by positivity)).trans
    simpa [F,iterate] using pow_le_pow_left₀ infDist_nonneg (hx.trans D.initial) 2
  have hrec (k : ℕ) (hk : k ≤ rounds p) :
      E (k+1) ≤ (1-stepSize p k/4)*E k + varianceTerm p k + e := by
    have h := adaptive D T k _ ((continuous_infDist_pt (solutions p f)).pow 2).measurable
      (fun x => sq_nonneg _) _ _ _ (fixed_distance D T k)
    have hh' := h.trans (add_le_add le_rfl (rounding_expected D.valid (radius_control D T k hk)))
    change F (k+1) ≤ (1-stepSize p k/4)*F k+(varianceTerm p k+stepSize p k*p.ε^2/64)+e at hh'
    dsimp only [E]
    linarith only [hh']
  have warm (k : ℕ) (hk : k < H) : E (k+1) ≤ (1-1/m)*E k+4*V/m^2+e := by
    have hk' : k ≤ rounds p := by unfold rounds; dsimp [H] at hk; omega
    have h := hrec k hk'
    have hη : stepSize p k = 4/m := ite_eq_left hk
    unfold varianceTerm at h
    rw [hη] at h
    refine h.trans_eq ?_
    change (1-4/m/4)*E k+4*(4/m)^2*p.σ^2*cost p (weights p)/t+e = _
    unfold V
    field_simp [hm'.ne',ht.ne']; ring
  have w := WeakInterpolationSchedule.initial_phase hm hV he h0 warm H le_rfl
  have hw : E H ≤ p.ε^2/64+4*V/m+(H:ℝ)*e := by linarith only [w,warm_decay D.valid]
  have cool (j : ℕ) (hj : j < H) : let s : ℝ := 2*m+j
      E (H+j+1) ≤ (1-2/s)*E (H+j)+16*V/s^2+e := by
    have hk : H+j ≤ rounds p := by unfold rounds; dsimp [H] at *; omega
    have h := hrec (H+j) hk
    have hη : stepSize p (H+j) = 8/(2*m+j) := by
      unfold stepSize
      rw [ite_eq_right (show ¬ H+j < phase p by dsimp [H]; omega)]
      simp [H,m]
    unfold varianceTerm at h
    rw [hη] at h
    refine h.trans_eq ?_
    change (1-8/(2*m+j)/4)*E (H+j)+4*(8/(2*m+j))^2*p.σ^2*cost p (weights p)/t+e = _
    unfold V
    have hjpos : 0 < 2*m+(j : ℝ) := by positivity
    field_simp [hjpos.ne',ht.ne']; ring
  have c := WeakInterpolationSchedule.final_phase hm (show 0 ≤ p.ε^2/64 by positivity) hV he hw cool H le_rfl
  have hV' : 64*V ≤ (H:ℝ)*p.ε^2 := by
    dsimp [V]
    rw [←mul_div_assoc,div_le_iff₀ ht]
    nlinarith only [variance_scale D.valid,mul_nonneg (sq_nonneg p.σ) hcost]
  have hs : 16*V/(2*m+H) ≤ p.ε^2/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hm'.le (sq_nonneg p.ε)]
  have he' : ((H+H : ℕ):ℝ)*e ≤ p.ε^2/8 := by
    have hK : 0 < (rounds p : ℝ) := by exact_mod_cast (show 0 < rounds p by unfold rounds; omega)
    dsimp [e]
    rw [←mul_div_assoc,div_le_iff₀ (by positivity : 0 < 8*(rounds p : ℝ))]
    have hk : ((H+H : ℕ):ℝ) ≤ rounds p := by exact_mod_cast (show H+H ≤ rounds p by unfold rounds; dsimp [H]; omega)
    linarith only [mul_le_mul_of_nonneg_right hk (sq_nonneg p.ε)]
  change F (2*H) ≤ p.ε^2
  rw [two_mul]
  dsimp only [E] at c
  linarith only [c,hs,he',sq_nonneg p.ε]

end LongTails.Proofs.OptimumHeterogeneityConvergence
