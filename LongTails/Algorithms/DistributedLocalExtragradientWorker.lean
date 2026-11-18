import LongTails.Setups.DistributedJacobianStrongGrowth
import LongTails.Algorithms.LocalNonlinearExtragradient

namespace LongTails.Algorithms.DistributedLocalExtragradientWorker

open LongTails.Setups.DistributedJacobianStrongGrowth

inductive Work (p : Params) where
  | warm (remaining : ℕ) (point : Point p)
  | first (remaining : ℕ) (point : Point p)
  | second (remaining : ℕ) (base predictor : Point p)

def point {p : Params} : Work p → Point p
  | .warm _ x => x
  | .first _ x => x
  | .second _ x _ => x

def query {p : Params} : Work p → Option (Point p)
  | .warm 0 _ => none
  | .warm (_ + 1) x => some x
  | .first 0 _ => none
  | .first (_ + 1) x => some x
  | .second 0 _ _ => none
  | .second (_ + 1) _ y => some y

noncomputable def reply (p : Params) (state : Work p) (value : Point p) : Work p :=
  match state with
  | .warm 0 x => .warm 0 x
  | .warm (k + 1) x => .warm k (x - (p.μ / (p.ρ * p.L ^ 2)) • value)
  | .first 0 x => .first 0 x
  | .first (k + 1) x => .second (k + 1) x (x - (1 / (4 * p.L)) • value)
  | .second 0 x y => .second 0 x y
  | .second (k + 1) x _ => .first k (x - (1 / (4 * p.L)) • value)

def remainingQueries {p : Params} : Work p → ℕ
  | .warm k _ => k
  | .first k _ => 2 * k
  | .second k _ _ => 2 * k - 1

end LongTails.Algorithms.DistributedLocalExtragradientWorker
