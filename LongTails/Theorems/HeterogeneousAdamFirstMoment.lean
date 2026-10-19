import LongTails.Setups.HeterogeneousSymmetricFirstMoment
import LongTails.Proofs.HeterogeneousAdamDescent

open MeasureTheory OracleTemplate LongTails.Algorithms.HeterogeneousAdam
open LongTails.Setups.HeterogeneousSymmetricFirstMoment
open LongTails.Proofs.AdaptiveHistoryAlgebra LongTails.Proofs.HeterogeneousAdamExecution
open LongTails.Proofs.HeterogeneousAdamDescent

namespace LongTails.Theorems.HeterogeneousAdamFirstMoment

noncomputable def budget : (let S := LongTails.Setups.HeterogeneousSymmetricFirstMoment.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(10 : ℝ)^84*(1+(1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L)*(q.bodyDim*q.δ+q.σBody+Real.sqrt q.headDim*q.σHead)^2/q.ε^4+((1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L)+(q.headDim*(1+2*q.L*q.Δ+q.headDim*q.σHead^2))*Real.sqrt (1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L))/q.ε^2)*(Real.log ((10 : ℝ)^84*(1+q.σBody)*(1+(1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L)*(q.bodyDim*q.δ+q.σBody+Real.sqrt q.headDim*q.σHead)^2/q.ε^4+((1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L)+(q.headDim*(1+2*q.L*q.Δ+q.headDim*q.σHead^2))*Real.sqrt (1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L))/q.ε^2)))^4⌉₊

set_option maxHeartbeats 4000000 in
theorem result : Convergence LongTails.Setups.HeterogeneousSymmetricFirstMoment.spec budget := by
  classical
  refine ⟨fun q => method (tunedConfig q.bodyDim q.headDim (budget q 0) q.L q.Δ q.σHead q.δ) q.x₀,?_,?_⟩
  · intro q hv f O hadm
    rcases hv with ⟨hd,hL,hM,hσb,hσh,hΔ,hε,hδ⟩
    rcases hadm with ⟨g,p,P,K,hs,hO,hf,hlip,hgap,hg,hi,hmean,hnb,hni,hnh,hsym,hKm,hKi,hKM,hKlip⟩
    subst O
    let A := 1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L
    let R := 1+((q.bodyDim : ℝ)+q.headDim)*(q.L+q.M)*Real.sqrt (q.Δ/q.L)
    let N₀ := q.bodyDim*q.δ+q.σBody+Real.sqrt q.headDim*q.σHead
    let N := q.bodyDim*q.δ+66*q.σBody+Real.sqrt q.headDim*q.σHead
    let r := 1+2*q.L*q.Δ+q.headDim*q.σHead^2
    let H := q.headDim*r
    let Q := 1+A*N₀^2/q.ε^4+(A+H*Real.sqrt A)/q.ε^2
    let T := budget q 0
    let cfg := tunedConfig q.bodyDim q.headDim T q.L q.Δ q.σHead q.δ
    let ℓ := Real.log (10*(1+q.σBody)*T)
    have hd' : (0 : ℝ) < (q.bodyDim : ℝ)+q.headDim := by exact_mod_cast hd
    rcases dimension_scale_square hd'.le hL hM hΔ.le with ⟨hA,hR,hR2,hRA⟩
    have hN : 0 ≤ N := by dsimp [N]; positivity
    have hN₀ : 0 ≤ N₀ := by dsimp [N₀]; positivity
    have hr : 0 < r := by dsimp [r]; positivity
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hNN : N ≤ 66*N₀ := block_noise_simplification hδ.le hσh
    have hbudget := structured_budget_suffices hA (show 0 ≤ R by linarith) hN hN₀ hH hε hσb hR2 hRA hNN
    change 1 ≤ T ∧ 10000000000000000000*(Real.sqrt (N*R)*ℓ/Real.sqrt (Real.sqrt T)+
      Real.sqrt (R^2+H*R)*ℓ^2/Real.sqrt T) ≤ q.ε at hbudget
    have hT := hbudget.1
    have hidx : cfg.lastIndex+1=T := by change T-1+1=T; omega
    have hbc : budget q=(fun _ => cfg.lastIndex+1) := by funext i; exact hidx.symm
    have hgradm : Measurable (gradient f) := by
      have hl : LipschitzWith ⟨q.L,hL.le⟩ (gradient f) := by
        apply lipschitzWith_iff_dist_le_mul.mpr
        intro x y
        change ‖gradient f x-gradient f y‖ ≤ q.L*‖x-y‖
        exact hlip x y
      exact hl.continuous.measurable
    have hneg (x) (j : Fin q.bodyDim) :
        ((p : Measure _).map (fun ω => (g x ω-gradient f x) (.inl j))).map (fun z : ℝ => -z)=
          (p : Measure _).map (fun ω => (g x ω-gradient f x) (.inl j)) := by
      have hx : Measurable (fun ω => (g x ω-gradient f x) (.inl j)) := by
        have hm : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
        fun_prop
      rw [Measure.map_map measurable_neg hx]
      exact (hsym x j).symm
    have hK0 : ∀ᵐ ω ∂(p : Measure _),0 ≤ K ω := hKlip.mono fun ω hw => hw.1
    have hnoise : ∀ᵐ ω ∂(p : Measure _),∀ x y (j : Fin q.bodyDim),
        |(g x ω-gradient f x) (.inl j)-(g y ω-gradient f y) (.inl j)| ≤ K ω*‖x-y‖ :=
      hKlip.mono fun ω hw => hw.2
    let a₀ : q.Ω := Classical.choice (nonempty_of_isProbabilityMeasure (p : Measure _))
    have hsum := iid_tuned_gradient_sum cfg rfl rfl hδ hr q.x₀ 0 a₀ hg hgradm hi hlip hL hΔ hd
      hs hf hgap hmean hni hnh hM hσb hσh hnoise hKi hK0 hKM hnb hneg T hT rfl
      (fun _ => rfl) (fun _ => rfl)
    let x := fun t (ω : ℕ → q.Ω) => trajectory cfg q.x₀ (fun r x => g x (ω r)) t
    change (∀ t,t<T → Integrable (fun ω => ‖gradient f (x t ω)‖) (P : Measure _)) ∧
      (∑ t ∈ Finset.range T,∫ ω,‖gradient f (x t ω)‖ ∂(P : Measure _)) ≤
        10000000000000000000*(Real.sqrt (N*R)*ℓ*Real.sqrt T*Real.sqrt (Real.sqrt T)+
          Real.sqrt (R^2+H*R)*ℓ^2*Real.sqrt T) at hsum
    have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hu : 0 < Real.sqrt (T : ℝ) := by positivity
    have hv : 0 < Real.sqrt (Real.sqrt (T : ℝ)) := by positivity
    have havg := gradient_rate_normalization hu hv (Real.sq_sqrt (Nat.cast_nonneg T))
      (Real.sq_sqrt (Real.sqrt_nonneg (T : ℝ))) hsum.2
    have hacc := havg.trans hbudget.2
    have hexe := execute_uniform_gradient_integral cfg q.x₀ P hg hgradm
      (fun t ht => hsum.1 t (by omega))
    dsimp only at hexe
    have hsuccess : Measurable (fun (z : Fin (cfg.lastIndex+1) × (ℕ → q.Ω)) => execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω } :
          Oracle (Point q.bodyDim q.headDim) (Point q.bodyDim q.headDim))
        (method cfg q.x₀) (fun _ => cfg.lastIndex+1) z.1 z.2) ∧
      Integrable (fun z => ‖gradient f (execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω } :
          Oracle (Point q.bodyDim q.headDim) (Point q.bodyDim q.headDim))
        (method cfg q.x₀) (fun _ => cfg.lastIndex+1) z.1 z.2)‖)
        ((PMF.uniformOfFintype (Fin (cfg.lastIndex+1))).toMeasure.prod (P : Measure _)) ∧
      (∫ z,‖gradient f (execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω } :
          Oracle (Point q.bodyDim q.headDim) (Point q.bodyDim q.headDim))
        (method cfg q.x₀) (fun _ => cfg.lastIndex+1) z.1 z.2)‖
          ∂((PMF.uniformOfFintype (Fin (cfg.lastIndex+1))).toMeasure.prod (P : Measure _))) ≤ q.ε := by
      refine ⟨hexe.1,hexe.2.1,?_⟩
      rw [hexe.2.2,hidx]
      have hidxR : (cfg.lastIndex : ℝ)+1=T := by exact_mod_cast hidx
      rw [hidxR]
      exact hacc
    convert hsuccess using 1 <;> simp only [← hbc, cfg, T, method, ProbabilityMeasure.toMeasure] <;> rfl
  · intro q hv
    rcases hv with ⟨hd,hL,hM,hσb,hσh,hΔ,hε,hδ⟩
    let A := 1+((q.bodyDim : ℝ)+q.headDim)^2*(q.L+q.M)^2*q.Δ/q.L
    let N₀ := q.bodyDim*q.δ+q.σBody+Real.sqrt q.headDim*q.σHead
    let r := 1+2*q.L*q.Δ+q.headDim*q.σHead^2
    let Q := 1+A*N₀^2/q.ε^4+(A+q.headDim*r*Real.sqrt A)/q.ε^2
    let T := budget q 0
    let cfg := tunedConfig q.bodyDim q.headDim T q.L q.Δ q.σHead q.δ
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hr : 0 < r := by dsimp [r]; positivity
    have hQ : 1 ≤ Q := by
      dsimp [Q]
      linarith only [show 0 ≤ A*N₀^2/q.ε^4 by positivity,
        show 0 ≤ (A+q.headDim*r*Real.sqrt A)/q.ε^2 by positivity]
    have hT := (rounded_log_budget (C := (10 : ℝ)^84) (by norm_num) hQ hσb).2.1
    change 1 ≤ T at hT
    have hd' : (0 : ℝ) < (q.bodyDim : ℝ)+q.headDim := by exact_mod_cast hd
    have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
    refine ⟨cfg,rfl,rfl,rfl,hr,?_,?_,rfl⟩
    · intro t
      change 0 < Real.sqrt (q.Δ/(q.L*((q.bodyDim : ℝ)+q.headDim)))/Real.sqrt T
      positivity
    · intro t
      change 0 < Real.sqrt (q.Δ/(q.L*((q.bodyDim : ℝ)+q.headDim)))
      positivity

end LongTails.Theorems.HeterogeneousAdamFirstMoment
