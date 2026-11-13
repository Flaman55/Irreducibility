module

public import Mathlib
public import Irreducibility.Residues

/-!
# T2: Euclid's algorithm on residues gives the greatest common divisor

`euclid a b`, Euclid's algorithm run on residues computed by counting, equals `Nat.gcd a b`
for all `a`, `b`. The fuel `b + 1` always suffices.
-/

namespace Irreducibility

public theorem euclidAux_eq_gcd :
    ∀ fuel a b, b < fuel → euclidAux fuel a b = Nat.gcd a b
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, b, h => by
    simp only [euclidAux]
    split_ifs with hb
    · subst hb; simp
    · have hlt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
      rw [resid_eq_mod, euclidAux_eq_gcd fuel b (a % b) (by omega)]
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

public theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b :=
  euclidAux_eq_gcd (b + 1) a b (Nat.lt_succ_self b)

end Irreducibility
