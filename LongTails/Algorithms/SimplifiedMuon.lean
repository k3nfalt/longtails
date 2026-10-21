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
