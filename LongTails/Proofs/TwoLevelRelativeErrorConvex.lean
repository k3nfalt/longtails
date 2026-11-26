import LongTails.Proofs.TwoLevelRelativeErrorConvexPotential
import LongTails.Proofs.TwoLevelRelativeErrorConvexBudget

open scoped RealInnerProductSpace
namespace LongTails.Proofs.TwoLevelRelativeErrorConvex
open OracleTemplate LongTails.Algorithms.TwoLevelRelativeErrorConvex
open RecursiveEnvelopeExecution RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma loop_bound {L α q : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    (ha : 0 < α) (hb : α ≤ 1/32) (hq : 0 < q) (hq6 : q ≤ 1/6)
    {xs : E} (hm : ∀ t, f xs ≤ f t) (ans : ℕ → E → E)
    (herr : ∀ k t, ‖ans k t-g t‖ ≤ α*‖g t‖) (n k call : ℕ) (x z : E) :
    let F := fun t => (f t-f xs)/(L*α^4)
    weight q (k+n) * F (evalAt ans (outer L α q (innerCount α) n k x z) call) ≤
      (1+3*q*(16*α)^2)^n * energy F xs q k x z := by
  let F := fun t => (f t-f xs)/(L*α^4)
  have hL := h.pos
  have hμ : 0 < L*α^4 := by positivity
  induction n generalizing k call x z with
  | zero =>
    simp only [outer,evalAt,Nat.add_zero,pow_zero,one_mul,energy]
    linarith [sq_nonneg ‖z-xs‖]
  | succ n ih =>
    let y := center k x z
    let u := evalAt ans (solve L α (innerCount α) y) call
    let z' := z - (q*((k:ℝ)+1)/2) • (y-u)
    obtain ⟨he,hf⟩ := solve_bounds h ha hb ans herr y call
    have hs := energy_step (F := F) (xs := xs) (x := x) (z := z) (u := u) k hq hq6
      (by linarith : 16*α ≤ 1/2) (div_nonneg (sub_nonneg.mpr (hm x)) hμ.le) he
      (fun t => by dsimp [F]; rw [← sub_div]; simpa using hf t) (by simp [F])
    have hi := ih (k+1) (call+1*innerCount α) u z'
    simp only [outer,evalAt_bind]
    rw [show k+(n+1) = k+1+n by omega,pow_succ (1+3*q*(16*α)^2) n,
      mul_assoc ((1+3*q*(16*α)^2)^n)]
    exact hi.trans (mul_le_mul_of_nonneg_left hs (by positivity))

lemma plan_accuracy {L α R ε : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    (ha : 0 < α) (hb : α ≤ 1/32) (hε : 0 < ε) (hT : 1 ≤ L*R^2/ε)
    {xs x0 : E} (hm : ∀ t, f xs ≤ f t) (hd : ‖x0-xs‖ ≤ R)
    (ans : ℕ → E → E) (herr : ∀ k t, ‖ans k t-g t‖ ≤ α*‖g t‖) :
    let K := horizon α (L*R^2/ε)
    f (evalAt ans (outer L α (damp α K) (innerCount α) K 0 x0 x0) 0) - f xs ≤ ε := by
  let T := L*R^2/ε
  let K := horizon α T
  let q := damp α K
  let D := 6+768*α^2*(K:ℝ)
  have hD : 0 < D := by dsimp [D]; linarith [show 0 ≤ 768*α^2*(K:ℝ) by positivity]
  have hq : 0 < q := one_div_pos.mpr hD
  have hqD : q*D = 1 := one_div_mul_cancel hD.ne'
  have hq6 : q ≤ 1/6 := by
    change 1/D ≤ 1/6; apply one_div_le_one_div_of_le (by norm_num)
    dsimp [D]; linarith [show 0 ≤ 768*α^2*(K:ℝ) by positivity]
  let u := evalAt ans (outer L α q (innerCount α) K 0 x0 x0) 0
  change f u - f xs ≤ ε
  have he := loop_bound h ha hb hq hq6 hm ans herr K 0 0 x0 x0
  let c := 3*q*(16*α)^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcK : (K:ℝ)*c ≤ 1 := by dsimp [c]; dsimp [D] at hqD; nlinarith only [hqD,hq]
  have hex : (1+c)^K ≤ Real.exp 1 := by
    calc _ ≤ (Real.exp c)^K := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp c]) _
         _ = Real.exp ((K:ℝ)*c) := (Real.exp_nat_mul _ _).symm
         _ ≤ _ := Real.exp_le_exp.mpr hcK
  simp only [energy,weight,Nat.cast_zero,mul_zero,zero_mul,zero_div,zero_add] at he
  change q*(K:ℝ)*(K+1)/4*((f u-f xs)/(L*α^4)) ≤ (1+c)^K*(‖x0-xs‖^2/2) at he
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have he' := he.trans (mul_le_mul hex (by linarith : ‖x0-xs‖^2/2 ≤ R^2/2) (by positivity) (Real.exp_pos _).le)
  let v := 12*Real.exp 1*α^4*T
  let b := 1536*Real.exp 1*α^6*T
  have hT0 : 0 < T := by change 1 ≤ T at hT; linarith
  have hv : 0 < v := by dsimp [v]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hK : Real.sqrt v + b ≤ (K:ℝ) := Nat.le_ceil _
  have hK0 : 0 < (K:ℝ) := by linarith [Real.sqrt_pos.mpr hv]
  have hprod := mul_le_mul (by linarith : Real.sqrt v ≤ (K:ℝ)) (by linarith : Real.sqrt v ≤ (K:ℝ)-b)
    (Real.sqrt_nonneg _) hK0.le
  rw [← sq, Real.sq_sqrt hv.le] at hprod
  have hK2 : 2*Real.exp 1*α^4*T*D ≤ (K:ℝ)^2 := by
    dsimp [v,b] at hprod; dsimp [D]; linarith only [hprod]
  have hTε : T*ε = L*R^2 := div_mul_cancel₀ _ hε.ne'
  have hL := h.pos
  have hμ : 0 < L*α^4 := by positivity
  have hbound : 2*Real.exp 1*R^2*(L*α^4) ≤ q*(K:ℝ)*(K+1)*ε := by
    have hh := mul_le_mul_of_nonneg_right hK2 (show 0 ≤ q*ε by positivity)
    calc _ = 2*Real.exp 1*α^4*T*D*(q*ε) := by rw [show 2*Real.exp 1*α^4*T*D*(q*ε) =
                      2*Real.exp 1*α^4*(T*ε)*(q*D) by ring,hqD,hTε]; ring
         _ ≤ _ := by nlinarith only [hh,mul_nonneg (mul_nonneg hq.le hK0.le) hε.le]
  have hgap : q*(K:ℝ)*(K+1)*(f u-f xs) ≤ 2*Real.exp 1*R^2*(L*α^4) := by
    field_simp at he'
    linarith only [he']
  exact le_of_mul_le_mul_left (hgap.trans hbound) (by positivity)

lemma execute_accuracy {L α R ε : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    (ha : 0 < α) (hb : α ≤ 1 / 32) (hε : 0 < ε) (hT : 1 ≤ L * R ^ 2 / ε)
    {xs x0 : E} (hm : ∀ t, f xs ≤ f t) (hd : ‖x0 - xs‖ ≤ R)
    (O : Oracle E E) (herr : ∀ history x seed,
      ‖O.answer history (0, x) seed - g x‖ ≤ α * ‖g x‖)
    (seed : Unit) (ξ : (k : ℕ) → O.Seed k) :
    let T := L * R ^ 2 / ε
    f (execute O (output L α T x0) (fun _ => horizon α T * innerCount α) seed ξ) - f xs ≤ ε := by
  let T := L * R ^ 2 / ε
  let K := horizon α T
  let m := innerCount α
  let A := output L α T x0
  have hh := plan_accuracy h ha hb hε hT hm hd (fun n x => executeAnswerAt O A seed ξ n (0, x))
    (fun _ x => herr _ x (ξ _))
  have hx := execute_plan_indexed
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    x0 x0 (fun _ => outer L α (damp α K) m K 0 x0 x0) O seed ξ
    (K := K * m) (by simp [Nat.mul_comm])
  exact (congrArg (fun t => f t - f xs) hx).le.trans hh

end LongTails.Proofs.TwoLevelRelativeErrorConvex
