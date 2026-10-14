import LongTails.Template

namespace OracleTemplate.BallProximal

noncomputable def algorithm {E : Type*} (x0 : E) : Algorithm E E E where
  State := E
  initial := fun _ => x0
  query := fun x => (0, x)
  update := fun _ y => y
  output := id

def iterate {E : Type*} (x0 : E) (reply : ℕ → E → E) : ℕ → E
  | 0 => x0
  | k + 1 => reply k (iterate x0 reply k)

end OracleTemplate.BallProximal
