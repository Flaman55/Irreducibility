module

public import Mathlib
public import Irreducibility.Defs

/-!
# T1: counting gives the residue

Counting `t` steps modulo `d` gives `t % d`; hence `resid a b = a % b`. Holds for every
modulus, `d = 0` included (counting modulo `0` never resets, `t % 0 = t`).
-/

namespace Irreducibility

public theorem countMod_eq_mod (d : Nat) : ∀ t, countMod d t = t % d
  | 0 => by simp [countMod]
  | t + 1 => by
    have ih := countMod_eq_mod d t
    have key : (t + 1) % d = (t % d + 1) % d := by
      have h := Nat.div_add_mod t d
      calc (t + 1) % d = (t % d + 1 + d * (t / d)) % d := by congr 1; omega
        _ = (t % d + 1) % d := Nat.add_mul_mod_self_left _ _ _
    simp only [countMod, ih, key]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hlt : t % d < d := Nat.mod_lt t hd
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact (Nat.mod_eq_of_lt (by omega)).symm

public theorem resid_eq_mod (a b : Nat) : resid a b = a % b := countMod_eq_mod b a

end Irreducibility
