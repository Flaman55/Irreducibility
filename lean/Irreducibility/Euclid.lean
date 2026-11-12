module

public import Mathlib
public import Irreducibility.Ticking

/-!
# T2: Euclid's procedure on relations gives the greatest common divisor

`commonPart a b`, Euclid's procedure run on relations read by ticking, equals `Nat.gcd a b`
for all `a`, `b`. The fuel `b + 1` always suffices.
-/

namespace Irreducibility

public theorem commonPartAux_eq_gcd :
    ∀ fuel a b, b < fuel → commonPartAux fuel a b = Nat.gcd a b
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, b, h => by
    simp only [commonPartAux]
    split_ifs with hb
    · subst hb; simp
    · have hlt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
      rw [relation_eq_mod, commonPartAux_eq_gcd fuel b (a % b) (by omega)]
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

public theorem commonPart_eq_gcd (a b : Nat) : commonPart a b = Nat.gcd a b :=
  commonPartAux_eq_gcd (b + 1) a b (Nat.lt_succ_self b)

end Irreducibility
