import LongTails.Algorithms.Muon

namespace OracleTemplate.SimplifiedMuon

open Muon

structure Public where
  m : ℕ
  n : ℕ
  η : ℝ
  T : ℕ
  W0 : Mat m n

structure State (p : Public) where
  iter : ℕ
  point : Mat p.m p.n
  iterates : ℕ → Mat p.m p.n

noncomputable def step (p : Public) (s : State p) (G : Mat p.m p.n) : State p :=
  let W := s.point - p.η • orthogonalize G
  ⟨s.iter + 1, W, Function.update s.iterates (s.iter + 1) W⟩

noncomputable def simplifiedMuon (p : Public) :
    Algorithm (Mat p.m p.n) (Mat p.m p.n) (Fin (p.T + 1) → Mat p.m p.n) where
  State := State p
  initial _ := ⟨0, p.W0, fun _ => p.W0⟩
  query s := (0, s.point)
  update := step p
  output s := fun j => s.iterates j

noncomputable def trajectory (p : Public) (G : Mat p.m p.n → Mat p.m p.n) (t : ℕ) : Mat p.m p.n :=
  (fun W => W - p.η • orthogonalize (G W))^[t] p.W0

attribute [local simp] step simplifiedMuon trajectory

end OracleTemplate.SimplifiedMuon

namespace OracleTemplate.MuonBest

open OracleTemplate OracleTemplate.Muon

structure Public where
  m : ℕ
  n : ℕ
  s : ℝ
  J : ℝ
  Δ : ℝ
  ε : ℝ
  W0 : Mat m n

noncomputable def horizon (p : Public) : ℕ := ⌈8 * p.J * p.Δ / p.ε ^ 2 + 2 * p.s * (((min p.m p.n : ℕ) : ℝ) * Real.sqrt ((min p.m p.n : ℕ) : ℝ)) * p.Δ / (3 * p.J * p.ε)⌉₊ + 1

noncomputable def stepSize (p : Public) : ℝ :=
  Real.sqrt (2 * p.Δ / (p.J * (horizon p : ℝ)))

noncomputable def sourceInput (p : Public) : OracleTemplate.SimplifiedMuon.Public :=
  ⟨p.m, p.n, stepSize p, horizon p, p.W0⟩

structure State (p : Public) where
  point : Mat p.m p.n
  best : Mat p.m p.n
  score : ℝ
  seen : Bool

def initial (p : Public) : State p := ⟨p.W0, p.W0, 0, false⟩

noncomputable def step (p : Public) (st : State p) (G : Mat p.m p.n) : State p :=
  let score := nuclearNorm G
  let point := st.point - stepSize p • orthogonalize G
  if st.seen = false ∨ score ≤ st.score then ⟨point, st.point, score, true⟩
  else ⟨point, st.best, st.score, true⟩

noncomputable def algorithm (p : Public) : Algorithm (Mat p.m p.n) (Mat p.m p.n) (Mat p.m p.n) where
  State := State p
  initial _ := initial p
  query st := (0, st.point)
  update := step p
  output st := st.best

noncomputable def stateAt (p : Public) (G : Mat p.m p.n → Mat p.m p.n) (K : ℕ) : State p :=
  (fun st => step p st (G st.point))^[K] (initial p)

attribute [local simp] horizon stepSize sourceInput initial step algorithm stateAt

end OracleTemplate.MuonBest
