import LongTails.Algorithms.ReparameterizedProxSgd

namespace OracleTemplate.GaussianVariational
open LongTails.Setups.GaussianVariationalInference MeasureTheory

noncomputable def twoPhaseSgd {d : ℕ} (μ a : ℝ) (T : ℕ) (z : Location d × Scale d) :
    Algorithm (Point d) (Point d) (Location d × Scale d) :=
  let base := reparameterizedProxSgd μ a z.1 z.2
  { Seed := ℕ → Fin d → ℝ
    law := base.law
    State := ℕ × SgdState d
    initial := fun ω => (T, base.initial ω)
    query := fun s => base.query s.2
    update := fun s g => match s.1 with
      | 0 => (0, base.update s.2 g)
      | t + 1 =>
        let ω := s.2.seeds
        (t, ⟨fun i => ω (i+1), 0, proxStep (stepSize μ a 0) s.2.current g (ω 0), 0, 0⟩)
    output := fun s => base.output s.2 }

end OracleTemplate.GaussianVariational
