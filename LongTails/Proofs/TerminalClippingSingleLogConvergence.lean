import LongTails.Proofs.TerminalClippingSingleLogRate

set_option backward.isDefEq.respectTransparency false

open MeasureTheory LongTails.Setups.TerminalClippingConvex

namespace OracleTemplate.TerminalClippingSingleLog

lemma budget_accuracy (p : Public) (hR : 0 < p.R) (hG : 0 < p.G)
    (hδ : 0 < p.δ) (hδ' : p.δ < 1) (hε : 0 < p.ε) (h : ¬p.G*p.R ≤ p.ε) :
    0 < horizon p ∧ 24*p.R*momentScale p*Real.sqrt (Real.log (8/p.δ)/horizon p) ≤ p.ε := by
  let q := Real.log (8/p.δ)
  let v := p.G^2+16*p.B^2*p.R^2
  have hv : 0 < v := by dsimp [v]; positivity
  have hq : 0 < q := TerminalClipping.confidence_pos hδ hδ'
  have ht : 0 < horizon p := by
    rw [horizon,ite_eq_right h]
    apply Nat.ceil_pos.mpr
    change 0 < 576*p.R^2*v*q/p.ε^2
    positivity
  refine ⟨ht, ?_⟩
  have ht' : 0 < (horizon p:ℝ) := by exact_mod_cast ht
  have hn : 576*p.R^2*v*q/p.ε^2 ≤ horizon p := by
    rw [horizon,ite_eq_right h]; exact Nat.le_ceil _
  have hM : 0 ≤ momentScale p := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (by positivity) hε.le).mp
  change (24*p.R*Real.sqrt v*Real.sqrt (q/(horizon p:ℝ)))^2 ≤ p.ε^2
  simp only [mul_pow,Real.sq_sqrt hv.le,Real.sq_sqrt (div_nonneg hq.le ht'.le)]
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hn
  rw [← mul_div_assoc, div_le_iff₀ ht']
  linarith only [hh]

lemma convergence : Convergence spec (fun p _ => 2*horizon p.toPublic) := by
  apply convergence_of_public_budget (S := spec) (fun p => 2*horizon p)
  refine ⟨algorithm, ?_, fun p _ => algorithm_allowed p.toPublic⟩
  rintro p ⟨_,hG,hδ,hδ',hR,hε⟩ I O
    ⟨g,proj,ν,P,hiid,hO,hcv,hclosed,hx,hf,_,⟨u,hu,hmin,hd⟩,hp,hpm,hpv,hg,hgi,hsub,hmi,hm⟩
  have hO' : O = TerminalClipping.sampleOracle p.toPublic g proj P := by
    rw [hO]
    unfold TerminalClipping.sampleOracle
    congr 1
    funext k query seed
    rcases query with ⟨i,query⟩
    cases query <;> rfl
  subst hO'
  let T := horizon p.toPublic
  let y := fun a : ℕ → p.Ω => path g proj (slope p.toPublic T) (level p.toPublic T)
    T p.x0 (fun i => a (2*i)) T
  have he (a : ℕ → p.Ω) : execute (TerminalClipping.sampleOracle p.toPublic g proj P)
      (algorithm p.toPublic) (fun _ => 2*T) () a = y a :=
    execute_path p.toPublic g proj P a T le_rfl
  have hy : Measurable y := (path_measurable hg hp _ _ _ _).comp
    (measurable_const.prodMk (Measurable.of_eval (fun i => measurable_pi_apply (2*i))))
  have hyX (a : ℕ → p.Ω) : y a ∈ I.domain := path_mem g hpm _ _ _ hx _ _
  have hevent : (P : Measure _) {a | p.ε < I.f (y a)-I.f u} ≤ ENNReal.ofReal p.δ := by
    by_cases h : p.G*p.R ≤ p.ε
    · have ht : T=0 := ite_eq_left h
      have hinit (a : ℕ → p.Ω) : y a=p.x0 := by simp [y,ht,path]
      have hh := TerminalClipping.objective_difference_from_moment
        (hgi _ hx) (hmi _ hx) hG.le (by simpa using hm _ hx) (hsub _ hx _ hu)
      have hb := (hh.trans (mul_le_mul_of_nonneg_left hd hG.le)).trans h
      simp [hinit,hb.not_gt]
    · have hr : 0 < p.R := by
        rcases lt_or_eq_of_le hR with hr|hr
        · exact hr
        · simp [← hr, hε.le] at h
      obtain ⟨ht,ha⟩ := budget_accuracy p.toPublic hr hG hδ hδ' hε h
      have hh := iid_accuracy p.toPublic T ht hr.le hG hδ hδ' hcv hclosed hx hf hu
        (fun _ h => hmin h) hd proj hpm hpv g hg ν P hiid hgi hmi hm hsub
      exact ((measure_mono (fun a hbad => lt_of_le_of_lt ha hbad)).trans hh).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
  have hy' : (fun s : Unit × (ℕ → p.Ω) => execute (TerminalClipping.sampleOracle p.toPublic g proj P)
    (algorithm p.toPublic) (fun _ => 2*T) s.1 s.2) = fun s => y s.2 := funext fun ⟨⟨⟩,a⟩ => he a
  change spec.successful p I (fun s : Unit × (ℕ → p.Ω) =>
    execute (TerminalClipping.sampleOracle p.toPublic g proj P) (algorithm p.toPublic)
      (fun _ => 2*T) s.1 s.2) ⟨(Measure.dirac ()).prod (P : Measure (ℕ → p.Ω)),inferInstance⟩
  rw [hy']
  refine ⟨hy.comp measurable_snd,fun a => hyX a.2,u,hu,hmin,?_⟩
  exact ((measurePreserving_snd (μ := (Measure.dirac () : Measure Unit)) (ν := (P : Measure _))).measure_preimage_le
    {a | p.ε < I.f (y a)-I.f u}).trans hevent

end OracleTemplate.TerminalClippingSingleLog
