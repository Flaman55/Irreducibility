module

public import Mathlib
public import Irreducibility.Euclid

/-!
# T3: the drum

* `turnOn_eq`: where a whole turn stands on ring `c`, read level by level, is
  `turn % c`, where the turn is the product of the level sizes.
* `commonPartWithTurn_eq`: Euclid's procedure on that state and `m` gives `gcd (turn) m`;
  the turn itself is never formed by the procedure.
* `prod_levels`: the drum built from positive rings turns once per their least common
  multiple.
* `irreducibleAfter_iff`: a positive ring is irreducible after the rings before it exactly
  when it shares nothing with their common turn.
-/

namespace Irreducibility

public theorem turnOn_eq (rs : List Nat) (c : Nat) : turnOn rs c = rs.prod % c := by
  induction rs with
  | nil => simp [turnOn]
  | cons r rs ih =>
    simp only [turnOn, ih, relation_eq_mod, List.prod_cons]
    exact (Nat.mul_mod r rs.prod c).symm

public theorem commonPartWithTurn_eq (radices : List Nat) (m : Nat) :
    commonPartWithTurn radices m = Nat.gcd radices.prod m := by
  rw [commonPartWithTurn, commonPart_eq_gcd, turnOn_eq, ← Nat.gcd_rec, Nat.gcd_comm]

public theorem levels_append (rs : List Nat) (m : Nat) :
    levels (rs ++ [m]) = levels rs ++ [m / commonPartWithTurn (levels rs) m] := by
  simp [levels, List.foldl_append]

/-- The drum built from positive rings turns once per their least common multiple. -/
public theorem prod_levels (rs : List Nat) (h : ∀ x ∈ rs, 0 < x) :
    (levels rs).prod = rs.foldl Nat.lcm 1 := by
  induction rs using List.reverseRecOn with
  | nil => simp [levels]
  | append_singleton rs m ih =>
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [levels_append, List.prod_append, List.prod_singleton, commonPartWithTurn_eq,
      ih', List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.lcm,
      Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

public theorem levelSize_eq (before : List Nat) (m : Nat) (h : ∀ x ∈ before, 0 < x) :
    levelSize before m = m / Nat.gcd (before.foldl Nat.lcm 1) m := by
  rw [levelSize, commonPartWithTurn_eq, prod_levels _ h]

/-- A positive ring is irreducible after positive rings exactly when it shares nothing with
their common turn. -/
public theorem irreducibleAfter_iff (before : List Nat) (m : Nat) (hm : 0 < m)
    (h : ∀ x ∈ before, 0 < x) :
    IrreducibleAfter before m ↔ Nat.Coprime (before.foldl Nat.lcm 1) m := by
  rw [IrreducibleAfter, levelSize_eq _ _ h, Nat.div_eq_self, Nat.Coprime]
  omega

end Irreducibility
