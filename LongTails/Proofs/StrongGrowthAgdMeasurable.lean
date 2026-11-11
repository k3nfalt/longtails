import LongTails.Proofs.StrongGrowthAgdMoments

namespace LongTails.Proofs.StrongGrowthAgdMeasurable

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

abbrev Enc (E : Type) := ℕ × ℕ × E × E × E × E × E × ℝ × E × Bool × ℕ × E × Bool

def enc (s : State E) : Enc E :=
  (s.t, s.i, s.acc, s.xPrev, s.x, s.xStart, s.glast, s.S, s.ybar, s.trig, s.vCount, s.out, s.done)

noncomputable instance : MeasurableSpace (State E) := MeasurableSpace.comap enc inferInstance

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_enc : Measurable (enc : State E → Enc E) := comap_measurable enc

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_to_state {α : Type*} [MeasurableSpace α] (f : α → State E)
    (h : Measurable (enc ∘ f)) : Measurable f := by
  rw [measurable_iff_comap_le]
  change (MeasurableSpace.comap enc inferInstance).comap f ≤ _
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 h

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_t : Measurable (fun s : State E => s.t) := measurable_fst.comp measurable_enc
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_i : Measurable (fun s : State E => s.i) :=
  measurable_fst.comp (measurable_snd.comp measurable_enc)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_acc : Measurable (fun s : State E => s.acc) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_enc))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_xPrev : Measurable (fun s : State E => s.xPrev) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_enc)))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_x : Measurable (fun s : State E => s.x) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_enc))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_xStart : Measurable (fun s : State E => s.xStart) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_enc)))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_glast : Measurable (fun s : State E => s.glast) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_enc))))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_S : Measurable (fun s : State E => s.S) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    measurable_enc)))))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_ybar : Measurable (fun s : State E => s.ybar) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_enc))))))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_trig : Measurable (fun s : State E => s.trig) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_enc)))))))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_vCount : Measurable (fun s : State E => s.vCount) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_enc))))))))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_out : Measurable (fun s : State E => s.out) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    measurable_enc)))))))))))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_done : Measurable (fun s : State E => s.done) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    measurable_enc)))))))))))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_mk13 {α : Type*} [MeasurableSpace α] {f1 f2 : α → ℕ} {f3 f4 f5 f6 f7 : α → E}
    {f8 : α → ℝ} {f9 : α → E} {f10 : α → Bool} {f11 : α → ℕ} {f12 : α → E} {f13 : α → Bool}
    (h1 : Measurable f1) (h2 : Measurable f2) (h3 : Measurable f3) (h4 : Measurable f4)
    (h5 : Measurable f5) (h6 : Measurable f6) (h7 : Measurable f7) (h8 : Measurable f8)
    (h9 : Measurable f9) (h10 : Measurable f10) (h11 : Measurable f11) (h12 : Measurable f12)
    (h13 : Measurable f13) :
    Measurable (fun a => (f1 a, f2 a, f3 a, f4 a, f5 a, f6 a, f7 a, f8 a, f9 a, f10 a, f11 a, f12 a,
      f13 a) : α → Enc E) :=
  h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk (h6.prodMk (h7.prodMk (h8.prodMk
    (h9.prodMk (h10.prodMk (h11.prodMk (h12.prodMk h13)))))))))))

lemma measurable_decide {α : Type*} [MeasurableSpace α] {P : α → Prop} [DecidablePred P]
    (h : MeasurableSet {a | P a}) : Measurable (fun a => decide (P a)) := by
  refine measurable_to_countable' (fun b => ?_)
  cases b
  · have : (fun a => decide (P a)) ⁻¹' {false} = {a | P a}ᶜ := by
      ext a; simp
    rw [this]; exact h.compl
  · have : (fun a => decide (P a)) ⁻¹' {true} = {a | P a} := by
      ext a; simp
    rw [this]; exact h

variable (cfg : Config) (x0 : E)

lemma measurable_ypoint : Measurable (fun s : State E => ypoint cfg s) := by
  unfold ypoint
  exact measurable_x.add ((measurable_x.sub measurable_xPrev).const_smul _)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurableSet_nat_pred (P : ℕ → Prop) : MeasurableSet {s : State E | P s.t} :=
  measurable_t (MeasurableSet.of_discrete (s := {n | P n}))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurableSet_trig : MeasurableSet {s : State E | s.trig = true} :=
  measurable_trig (MeasurableSet.of_discrete (s := {true}))

lemma measurable_queryPoint : Measurable (fun s : State E => queryPoint cfg s) := by
  unfold queryPoint
  refine Measurable.ite (measurableSet_nat_pred (fun n => cfg.pos n < cfg.K)) ?_ ?_
  · exact Measurable.ite measurableSet_trig measurable_x (measurable_ypoint cfg)
  · exact Measurable.ite (measurableSet_nat_pred (fun n => cfg.pos n = cfg.K)) measurable_x measurable_ybar

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurableSet_nat_pred' (P : ℕ → Prop) : MeasurableSet {p : State E × E | P p.1.t} :=
  (measurable_t.comp measurable_fst) (MeasurableSet.of_discrete (s := {n | P n}))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurableSet_trig' : MeasurableSet {p : State E × E | p.1.trig = true} :=
  (measurable_trig.comp measurable_fst) (MeasurableSet.of_discrete (s := {true}))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma enc_batchUpdate (p : State E × E) :
    enc (batchUpdate cfg x0 p.1 p.2) =
      if cfg.pos p.1.t < cfg.K then
        if p.1.trig = true then
          (p.1.t + 1, p.1.i, p.1.acc, p.1.xPrev, p.1.x, p.1.xStart, p.1.glast, p.1.S, p.1.ybar,
            p.1.trig, p.1.vCount, p.1.out, p.1.done)
        else
          (p.1.t + 1, p.1.i, p.1.acc, p.1.x, ypoint cfg p.1 - cfg.η • p.2, p.1.xStart, p.2,
            p.1.S + ‖ypoint cfg p.1 - cfg.η • p.2 - p.1.x‖ ^ 2,
            p.1.ybar + pw cfg.K (cfg.pos p.1.t) • ypoint cfg p.1,
            decide (cfg.B ^ 2 < ((cfg.pos p.1.t + 1 : ℕ) : ℝ) *
              (p.1.S + ‖ypoint cfg p.1 - cfg.η • p.2 - p.1.x‖ ^ 2)),
            p.1.vCount, p.1.out, p.1.done)
      else if cfg.pos p.1.t = cfg.K then
        (p.1.t + 1, p.1.i, p.1.acc, p.1.x - cfg.ηf • p.2, p.1.x - cfg.ηf • p.2, p.1.xStart, p.1.glast,
          p.1.S, p.1.ybar, p.1.trig, p.1.vCount, p.1.out, p.1.done)
      else if cfg.pos p.1.t + 1 < cfg.Eb then
        (p.1.t + 1, p.1.i, p.1.acc, p.1.xPrev, p.1.x, p.1.xStart, p.1.glast, p.1.S, p.1.ybar, p.1.trig,
          (if p.1.trig = true then p.1.vCount else p.1.vCount + (if ‖p.2‖ ≤ cfg.thr then 1 else 0)),
          p.1.out, p.1.done)
      else if ¬ p.1.trig = true ∧
          2 * (if p.1.trig = true then p.1.vCount else p.1.vCount + (if ‖p.2‖ ≤ cfg.thr then 1 else 0))
            > cfg.m then
        (p.1.t + 1, p.1.i, p.1.acc, p.1.xPrev, p.1.x, p.1.xStart, p.1.glast, p.1.S, p.1.ybar, p.1.trig,
          p.1.vCount, p.1.ybar, true)
      else
        (p.1.t + 1, p.1.i, p.1.acc,
          (if (p.1.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else p.1.x),
          (if (p.1.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else p.1.x),
          (if (p.1.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else p.1.x),
          0, 0, 0, false, 0, p.1.out, p.1.done) := by
  simp only [batchUpdate, restart]
  split_ifs <;> rfl

lemma measurable_batchUpdate :
    Measurable (fun p : State E × E => batchUpdate cfg x0 p.1 p.2) := by
  apply measurable_to_state
  have hT : Measurable (fun p : State E × E => p.1.t) := measurable_t.comp measurable_fst
  have hT1 : Measurable (fun p : State E × E => p.1.t + 1) := hT.add_const 1
  have hI : Measurable (fun p : State E × E => p.1.i) := measurable_i.comp measurable_fst
  have hAcc : Measurable (fun p : State E × E => p.1.acc) := measurable_acc.comp measurable_fst
  have hXP : Measurable (fun p : State E × E => p.1.xPrev) := measurable_xPrev.comp measurable_fst
  have hX : Measurable (fun p : State E × E => p.1.x) := measurable_x.comp measurable_fst
  have hXS : Measurable (fun p : State E × E => p.1.xStart) := measurable_xStart.comp measurable_fst
  have hGl : Measurable (fun p : State E × E => p.1.glast) := measurable_glast.comp measurable_fst
  have hS : Measurable (fun p : State E × E => p.1.S) := measurable_S.comp measurable_fst
  have hYb : Measurable (fun p : State E × E => p.1.ybar) := measurable_ybar.comp measurable_fst
  have hTr : Measurable (fun p : State E × E => p.1.trig) := measurable_trig.comp measurable_fst
  have hVC : Measurable (fun p : State E × E => p.1.vCount) := measurable_vCount.comp measurable_fst
  have hOut : Measurable (fun p : State E × E => p.1.out) := measurable_out.comp measurable_fst
  have hD : Measurable (fun p : State E × E => p.1.done) := measurable_done.comp measurable_fst
  have hV : Measurable (fun p : State E × E => p.2) := measurable_snd
  have hY : Measurable (fun p : State E × E => ypoint cfg p.1) := (measurable_ypoint cfg).comp measurable_fst
  have hXN : Measurable (fun p : State E × E => ypoint cfg p.1 - cfg.η • p.2) := hY.sub (hV.const_smul _)
  have hS' : Measurable (fun p : State E × E => p.1.S + ‖ypoint cfg p.1 - cfg.η • p.2 - p.1.x‖ ^ 2) :=
    hS.add ((hXN.sub hX).norm.pow_const 2)
  have hW : Measurable (fun p : State E × E => pw cfg.K (cfg.pos p.1.t)) :=
    (measurable_from_nat (f := fun n => pw cfg.K (cfg.pos n))).comp hT
  have hYb' : Measurable (fun p : State E × E => p.1.ybar + pw cfg.K (cfg.pos p.1.t) • ypoint cfg p.1) :=
    hYb.add (hW.smul hY)
  have hJ1 : Measurable (fun p : State E × E => ((cfg.pos p.1.t + 1 : ℕ) : ℝ)) :=
    (measurable_from_nat (f := fun n => ((cfg.pos n + 1 : ℕ) : ℝ))).comp hT
  have hFire : Measurable (fun p : State E × E =>
      decide (cfg.B ^ 2 < ((cfg.pos p.1.t + 1 : ℕ) : ℝ) *
        (p.1.S + ‖ypoint cfg p.1 - cfg.η • p.2 - p.1.x‖ ^ 2))) :=
    measurable_decide (measurableSet_lt measurable_const (hJ1.mul hS'))
  have hXG : Measurable (fun p : State E × E => p.1.x - cfg.ηf • p.2) := hX.sub (hV.const_smul _)
  have hThr : MeasurableSet {p : State E × E | ‖p.2‖ ≤ cfg.thr} := measurableSet_le hV.norm measurable_const
  have hTrS : MeasurableSet {p : State E × E | p.1.trig = true} := measurableSet_trig' (E := E)
  have hVC' : Measurable (fun p : State E × E =>
      if p.1.trig = true then p.1.vCount else p.1.vCount + (if ‖p.2‖ ≤ cfg.thr then 1 else 0)) :=
    Measurable.ite hTrS hVC (hVC.add (Measurable.ite hThr measurable_const measurable_const))
  have hXs : Measurable (fun p : State E × E =>
      if (p.1.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else p.1.x) :=
    Measurable.ite (measurableSet_nat_pred' (E := E) (fun n => (n + 1) % (cfg.N1 * cfg.Eb) = 0))
      measurable_const hX
  have hAcc' : MeasurableSet {p : State E × E | ¬ p.1.trig = true ∧
      2 * (if p.1.trig = true then p.1.vCount else p.1.vCount + (if ‖p.2‖ ≤ cfg.thr then 1 else 0))
        > cfg.m} :=
    hTrS.compl.inter (hVC' (MeasurableSet.of_discrete (s := {n | cfg.m < 2 * n})))
  have hrw : (enc ∘ fun p : State E × E => batchUpdate cfg x0 p.1 p.2) =
      fun p => enc (batchUpdate cfg x0 p.1 p.2) := rfl
  rw [hrw]
  simp_rw [enc_batchUpdate cfg x0]
  refine Measurable.ite (measurableSet_nat_pred' (E := E) (fun n => cfg.pos n < cfg.K)) ?_ ?_
  · refine Measurable.ite hTrS ?_ ?_
    · exact measurable_mk13 hT1 hI hAcc hXP hX hXS hGl hS hYb hTr hVC hOut hD
    · exact measurable_mk13 hT1 hI hAcc hX hXN hXS hV hS' hYb' hFire hVC hOut hD
  · refine Measurable.ite (measurableSet_nat_pred' (E := E) (fun n => cfg.pos n = cfg.K)) ?_ ?_
    · exact measurable_mk13 hT1 hI hAcc hXG hXG hXS hGl hS hYb hTr hVC hOut hD
    · refine Measurable.ite (measurableSet_nat_pred' (E := E) (fun n => cfg.pos n + 1 < cfg.Eb)) ?_ ?_
      · exact measurable_mk13 hT1 hI hAcc hXP hX hXS hGl hS hYb hTr hVC' hOut hD
      · refine Measurable.ite hAcc' ?_ ?_
        · exact measurable_mk13 hT1 hI hAcc hXP hX hXS hGl hS hYb hTr hVC hYb measurable_const
        · exact measurable_mk13 hT1 hI hAcc hXs hXs hXs measurable_const measurable_const
            measurable_const measurable_const measurable_const hOut hD

variable {Ω : Type} [MeasurableSpace Ω] {g : E → Ω → E}

lemma measurable_blockStep (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : State E × (Fin cfg.b → Ω) => blockStep cfg x0 g z.1 z.2) := by
  have hrw : (fun z : State E × (Fin cfg.b → Ω) => blockStep cfg x0 g z.1 z.2) =
      fun z => if z.1.done = true then z.1 else
        ((fun p : State E × E => batchUpdate cfg x0 p.1 p.2) ∘
          (fun z : State E × (Fin cfg.b → Ω) => (z.1, bmean cfg g (queryPoint cfg z.1) z.2))) z := by
    funext z; rfl
  rw [hrw]
  refine Measurable.ite ?_ measurable_fst ?_
  · exact (measurable_done.comp measurable_fst) (MeasurableSet.of_discrete (s := {true}))
  · exact Measurable.comp (measurable_batchUpdate cfg x0)
      (measurable_fst.prodMk (bmean_measurable_joint cfg hg (measurable_queryPoint cfg)))

end LongTails.Proofs.StrongGrowthAgdMeasurable
