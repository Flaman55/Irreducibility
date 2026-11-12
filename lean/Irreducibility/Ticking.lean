module

public import Mathlib
public import Irreducibility.Defs

/-!
# T1: ticking reads the remainder

Ticking a ring of period `d` for `t` ticks leaves it at `t % d`; hence the relation of ring
`a` to ring `b`, read when `a` completes its first turn, is `a % b`. Holds for every period,
`d = 0` included (a ring without teeth never returns, `t % 0 = t`).
-/

namespace Irreducibility

public theorem pos_eq_mod (d : Nat) : ∀ t, pos d t = t % d
  | 0 => by simp [pos]
  | t + 1 => by
    have ih := pos_eq_mod d t
    have key : (t + 1) % d = (t % d + 1) % d := by
      have h := Nat.div_add_mod t d
      calc (t + 1) % d = (t % d + 1 + d * (t / d)) % d := by congr 1; omega
        _ = (t % d + 1) % d := Nat.add_mul_mod_self_left _ _ _
    simp only [pos, ih, key]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hlt : t % d < d := Nat.mod_lt t hd
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact (Nat.mod_eq_of_lt (by omega)).symm

public theorem relation_eq_mod (a b : Nat) : relation a b = a % b := pos_eq_mod b a

end Irreducibility
