import LongTails.Proofs.BrightnessComparatorProgress
import LongTails.Proofs.BrightnessDominantEnvelope
import LongTails.Proofs.BrightnessStiffPhase

namespace LongTails.Proofs.BrightnessTerminalEnergy

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open BrightnessScaledCoordinates
open BrightnessScaledForces
open BrightnessFirstFitParameters
open BrightnessFirstFitWork
open BrightnessComparatorProgress
open BrightnessTrajectoryBounds
open BrightnessFirstFitDescent (separator_average)

noncomputable def energy {d : ℕ} (s : State d) (v : Features d) (k R : ℝ) :=
  (‖s.w-v‖^2+k*R^2*max (s.P^2) (s.T^2))/2

lemma post_decrease (p : Params) (x : Images p) (s : State p.d) (G : Geometry p x)
    (c : Scales) (h : Tuning p c) (u : Features p.d) (M : ℝ)
    (hM : c.M ≤ M) (hw : ‖s.w‖ ≤ 3*M) (hcen : ⟪axis p.d,s.w⟫ = 0)
    (hU : max |s.Q| |s.P| * p.J ≤ c.U) (hpt : max |s.P| |s.T| ≤ c.δ)
    (he : |kick p c.κ s (meanRow p x s)| ≤ c.δ)
    (hm : ∀ i, 2*c.Γ ≤ ⟪u,readout s (x i)⟫) (hn : ¬Fitted p x (physical p s)) :
    let k := (1-c.κ*p.D)⁻¹
    energy (advance p c.κ s (meanRow p x s)) (M • u) k p.R + c.κ*c.Γ*M/(2*p.n) ≤
      energy s (M • u) k p.R := by
  let g := votes p x s
  let z := meanRow p x s
  let d := readout s z
  let a := c.κ*p.D
  let k := (1-a)⁻¹
  let L := 1+Real.log (2*(p.n:ℝ))
  let t := p.R^2*s.P*s.T
  let β := c.κ*brightness z
  have κ := h.κpos
  have Γ := h.Γpos
  have J := h.Jpos
  have U := h.Upos
  have δ := h.δpos
  have D := h.Dpos
  have R : 0 < p.R := by linarith only [h.Rlarge]
  have Mpos := h.Mpos.trans_le hM
  have a₀ : 0 ≤ a := mul_nonneg κ.le D.le
  have ⟨sm,tiny,_,_⟩ := small_tunings h
  change 32*a*(1+c.U) ≤ c.Γ at sm
  have ha : a ≤ 1/2 := by nlinarith only [sm,h.Γle,mul_nonneg a₀ U.le]
  have hs : 0 < 1-a := by linarith only [ha]
  have hk : 0 ≤ k := inv_nonneg.mpr hs.le
  have hk₂ : k ≤ 2 := by
    change (1-a)⁻¹ ≤ 2
    rw [inv_le_comm₀ hs (by norm_num)]
    norm_num
    linarith only [ha]
  have hk' : k-1 = k*a := by dsimp [k]; field_simp; ring
  have massB := vote_mass p x s
  have hn' : (1:ℝ) ≤ p.n := by exact_mod_cast p.n.property
  have logn : 0 ≤ Real.log (2*(p.n:ℝ)) := Real.log_nonneg (by linarith only [hn'])
  have L₀ : 0 ≤ L := by dsimp [L]; linarith
  have ds : ‖d‖ ≤ c.U*mass p g := (readout_force p x G s g (fun _ => Real.sigmoid_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hU massB.1)
  obtain ⟨hf,_,hC⟩ := force_bounds p x G s
  have hb : |β| ≤ a := by
    rw [show |β| = c.κ * |brightness z| by simp [β,abs_mul,abs_of_nonneg κ.le]]
    exact mul_le_mul_of_nonneg_left hf κ.le
  have hw' : ⟪s.w,d⟫+t*brightness z ≤ L*mass p g := by
    have H := work p x s R hcen hn
    change t*brightness z+⟪s.w,d⟫ ≤ _ at H
    linarith only [H]
  have error_bound : p.R^2 * |kick p c.κ s z| ≤ c.κ*p.J*‖s.w‖*mass p g := by
    rw [kick,abs_div,abs_mul,abs_of_nonneg κ.le,abs_of_nonneg (sq_nonneg p.R),
      mul_div_cancel₀ _ (pow_ne_zero 2 R.ne')]
    have H := (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg s.w))
    change |⟪smooth z,s.w⟫| ≤ p.J*mass p g*‖s.w‖ at H
    nlinarith only [mul_le_mul_of_nonneg_left H κ.le]
  have sizes := (comparator_size h).2.2
  change 8*(L+c.κ*c.U^2) ≤ c.M*c.Γ at sizes
  have HH := post_step s.w u d s.P s.T β (kick p c.κ s z) c.κ p.R k a (c.κ*(t*brightness z))
    c.U (mass p g) L c.Γ M p.J c.δ κ.le hk hk₂ a₀ ha hb (by dsimp [β,t]; ring)
    hk' U.le massB.1 massB.2 ds Mpos.le Γ.le J.le δ.le L₀
    (by nlinarith only [mul_le_mul_of_nonneg_left hw' κ.le]) (separator_average p x s u _ hm)
    error_bound he hpt hw (by nlinarith only [sizes,mul_le_mul_of_nonneg_right hM Γ.le])
    (by nlinarith only [sm,a₀]) (by nlinarith only [tiny,δ])
  have Hfit : (2*(p.n:ℝ))⁻¹ ≤ mass p g := vote_mass_nonfit p x s hn
  change energy (advance p c.κ s z) (M • u) k p.R + _ ≤ energy s (M • u) k p.R
  change energy (advance p c.κ s z) (M • u) k p.R + c.κ*c.Γ*M*mass p g ≤ energy s (M • u) k p.R at HH
  nlinarith only [HH,mul_le_mul_of_nonneg_left Hfit (by positivity : 0 ≤ c.κ*c.Γ*M),
    show c.κ*c.Γ*M/(2*(p.n:ℝ)) = c.κ*c.Γ*M*(2*(p.n:ℝ))⁻¹ from div_eq_mul_inv ..]

end LongTails.Proofs.BrightnessTerminalEnergy

namespace LongTails.Proofs.BrightnessTerminalLength

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open BrightnessScaledCoordinates
open BrightnessFirstFitParameters
open BrightnessFirstFitGuard
open BrightnessTrajectoryBounds
open BrightnessStiffPhase
open BrightnessTerminalEnergy
open BrightnessFirstFitWork

lemma terminal (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x)
    (j : ℕ) (hj : j ≤ (scales p).H)
    (start : let c := scales p
      pole p x c j ≤ c.V*c.M/p.R ∧ ‖(path p x c.κ j).w‖ ≤ c.V*c.M)
    (nonfit : ∀ t < (scales p).H, ¬Fitted p x (physical p (path p x (scales p).κ t))) :
    let c := scales p
    ((c.H:ℝ)-j)*c.κ*c.Γ ≤ 8*p.n*c.V*c.M := by
  let c := scales p
  let S := path p x c.κ
  have h : Tuning p c := tuning p valid
  have env : Envelope p x c := envelope p x valid G
  have κ := h.κpos
  have Γ := h.Γpos
  have J := h.Jpos
  have U := h.Upos
  have μ := h.μpos
  have δ := h.δpos
  have M := h.Mpos
  have R : 0 < p.R := by linarith only [h.Rlarge]
  have V : 0 < c.V := by linarith only [h.Vge]
  have hn : 0 < (p.n:ℝ) := by exact_mod_cast p.n.property
  let A := c.V*c.M
  have Apos : 0 < A := mul_pos V M
  let k := (1-c.κ*p.D)⁻¹
  have D := h.Dpos
  have hsm := (small_tunings h).1
  have hc : c.κ*p.D ≤ 1/2 := by
    nlinarith only [hsm,h.Γle,mul_nonneg (mul_nonneg κ.le D.le) U.le]
  have hkc : 0 < 1-c.κ*p.D := by linarith only [hc]
  have hk : 0 ≤ k := inv_nonneg.mpr hkc.le
  have hk₂ : k ≤ 2 := by
    change (1-c.κ*p.D)⁻¹ ≤ 2
    rw [inv_le_comm₀ hkc (by norm_num)]
    norm_num
    linarith only [hc]
  obtain ⟨u,hu,hm⟩ := BrightnessScaledForces.contrast_margin p x G
  let E t := energy (S t) ((4*A) • u) k p.R
  let l := c.κ*c.Γ*(4*A)/(2*p.n)
  have l₀ : 0 ≤ l := by dsimp [l]; positivity
  let m t := pole p x c t
  let q t := max ((S t).P^2) ((S t).T^2)
  have qm (t : ℕ) : q t = m t^2 := by
    dsimp [q,m,pole,S]
    rcases le_total |(S t).P| |(S t).T| with hh | hh
    · have hh' : (S t).P^2 ≤ (S t).T^2 := by simpa using pow_le_pow_left₀ (abs_nonneg _) hh 2
      change max ((S t).P^2) ((S t).T^2) = (max |(S t).P| |(S t).T|)^2
      simp [max_eq_right hh,max_eq_right hh']
    · have hh' : (S t).T^2 ≤ (S t).P^2 := by simpa using pow_le_pow_left₀ (abs_nonneg _) hh 2
      change max ((S t).P^2) ((S t).T^2) = (max |(S t).P| |(S t).T|)^2
      simp [max_eq_left hh,max_eq_left hh']
  have mq (t : ℕ) : 0 ≤ m t := (abs_nonneg _).trans (le_max_left _ _)
  have hW : 0 ≤ radius p c := by unfold radius; positivity
  have hε : 0 ≤ error p c := by unfold error; positivity
  have hg : 0 ≤ growth p c := by unfold growth; positivity
  obtain ⟨he,_,hsmall⟩ := scale_remainders p valid
  change c.H*error p c ≤ c.δ/4 at he
  change (‖p.readout‖/p.R^2)^2 + c.H*growth p c +
    2*(1+c.U*radius p c)/(p.μ*p.R^2)+(A/p.R)^2 ≤ c.δ^2 at hsmall
  have qj : q j ≤ (A/p.R)^2 := (qm j).le.trans (pow_le_pow_left₀ (mq j) start.1 2)
  have md (t : ℕ) (ht : j+t ≤ c.H) : m (j+t) ≤ c.δ := by
    have ini (i : ℕ) (hi : j+i ≤ c.H) : q (j+i) ≤ q j+i*growth p c := by
      induction i with
      | zero => simp
      | succ i ih =>
        have H := (env.growth (j+i) (by omega)).1
        rw [Nat.add_succ,Nat.cast_succ]
        change q (j+i+1) ≤ q (j+i)+growth p c at H
        linarith only [H,ih (by omega)]
    have Ht : (t:ℝ) ≤ c.H := by exact_mod_cast (show t ≤ c.H by omega)
    nlinarith only [hsmall,ini t ht,qj,qm (j+t),mq (j+t),δ,
      mul_le_mul_of_nonneg_right Ht hg,sq_nonneg (‖p.readout‖/p.R^2),
      (by positivity : 0 ≤ 2*(1+c.U*radius p c)/(p.μ*p.R^2))]
  have normu : ‖(4*A) • u‖ = 4*A := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),hu,mul_one]
  have Ej : E j ≤ (4*A)^2 := by
    have hdist := norm_sub_le (S j).w ((4*A) • u)
    rw [normu] at hdist
    have hh : ‖(S j).w-(4*A) • u‖ ≤ 5*A := by linarith only [hdist,start.2]
    have hqr : p.R^2*q j ≤ A^2 := by
      rw [div_pow] at qj
      exact (mul_comm _ _).le.trans ((le_div_iff₀ (sq_pos_of_pos R)).mp qj)
    change (‖(S j).w-(4*A) • u‖^2+k*p.R^2*q j)/2 ≤ _
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hh 2,
      mul_le_mul hk₂ hqr (mul_nonneg (sq_nonneg _) ((qm j).symm ▸ sq_nonneg (m j))) (by norm_num : (0:ℝ) ≤ 2),
      sq_nonneg A]
  have bound (t : ℕ) (ht : j+t ≤ c.H) : E (j+t)+t*l ≤ E j := by
    induction t with
    | zero => simp
    | succ t ih =>
      have ht' : j+t < c.H := by omega
      have H := ih ht'.le
      have qnn : 0 ≤ q (j+t) := (qm _).symm ▸ sq_nonneg _
      have dist : ‖(S (j+t)).w-(4*A) • u‖ ≤ 2*(4*A) := by
        change (‖(S (j+t)).w-(4*A) • u‖^2+k*p.R^2*q (j+t))/2 + t*l ≤ _ at H
        nlinarith only [H,Ej,mul_nonneg (mul_nonneg hk (sq_nonneg p.R)) qnn,
          mul_nonneg (by positivity : (0:ℝ) ≤ t) l₀,norm_nonneg ((S (j+t)).w-(4*A) • u),Apos]
      have hh := norm_add_le ((S (j+t)).w-(4*A) • u) ((4*A) • u)
      rw [sub_add_cancel,normu] at hh
      have hδ := md t ht'.le
      have Hrow (i : Fin p.n) : 2*c.Γ ≤ ⟪u,readout (S (j+t)) (x i)⟫ := by
        have ha : ‖contrast (x i)‖ ≤ p.J := by linarith only [(G.1 i).2,norm_nonneg (smooth (x i))]
        have hc' : ‖smooth (x i)‖ ≤ p.J := by linarith only [(G.1 i).2,norm_nonneg (contrast (x i))]
        have hd := BrightnessComparatorProgress.row_drift u (contrast (x i)) (smooth (x i))
          (S (j+t)).Q p.Q (S (j+t)).P 0 p.J _ hu.le ha hc' (hm i)
        rw [sub_zero] at hd
        have hQ := (env.cap (j+t) ht'.le).2.2.1
        have hP : |(S (j+t)).P| ≤ c.δ := (le_max_left _ _).trans hδ
        change _ ≤ ⟪u,(S (j+t)).Q • contrast (x i)+(S (j+t)).P • smooth (x i)⟫
        nlinarith only [hd,h.δeq,h.margin,δ,mul_le_mul_of_nonneg_right hQ J.le,
          mul_le_mul_of_nonneg_right hP J.le,mul_nonneg δ.le J.le]
      have H' := post_decrease p x (S (j+t)) G c h u (4*A)
        (by dsimp [A]; nlinarith only [mul_le_mul_of_nonneg_right h.Vge M.le,M.le])
        (by linarith only [hh,dist]) (path_centered p x c.κ _) (readout_cap p x c h env _ ht'.le)
        hδ ((env.growth _ ht').2.2.trans (by
          have Hh : 1 ≤ (c.H:ℝ) := by exact_mod_cast env.horizon
          nlinarith only [he,δ,mul_le_mul_of_nonneg_right Hh hε]))
        Hrow (nonfit _ ht')
      change E (j+t+1)+l ≤ E (j+t) at H'
      rw [Nat.add_succ,Nat.cast_succ]
      linarith only [H,H']
  change j ≤ c.H at hj
  have H := bound (c.H-j) (by omega)
  rw [Nat.add_sub_of_le hj,Nat.cast_sub hj] at H
  have hEn : 0 ≤ E c.H := by
    change 0 ≤ (‖_‖^2+k*p.R^2*q c.H)/2
    rw [qm]
    positivity
  have hh : ((c.H:ℝ)-j)*l ≤ (4*A)^2 := by linarith only [H,Ej,hEn]
  dsimp only [l] at hh
  rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at hh
  change ((c.H:ℝ)-j)*c.κ*c.Γ ≤ 8*p.n*c.V*c.M
  rw [mul_assoc (8*(p.n:ℝ))]
  apply le_of_mul_le_mul_right (a := A) _ Apos
  nlinarith only [hh]

end LongTails.Proofs.BrightnessTerminalLength
