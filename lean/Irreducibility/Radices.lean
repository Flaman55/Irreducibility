module

public import Mathlib
public import Irreducibility.Euclid

/-!
# T3: the mixed-radix system of arbitrary moduli

* `prodMod_eq`: the residue modulo `c` of a product, computed factor by factor, is
  `prod % c`.
* `gcdProd_eq`: Euclid's algorithm on that residue and `m` gives `gcd prod m`; the product
  itself is never formed.
* `prod_radices`: the product of the radices of positive moduli is their least common
  multiple.
* `irreducibleAfter_iff`: a positive modulus is irreducible after the moduli before it
  exactly when it is coprime to their lcm.
-/

namespace Irreducibility

public theorem prodMod_eq (rs : List Nat) (c : Nat) : prodMod rs c = rs.prod % c := by
  induction rs with
  | nil => simp [prodMod]
  | cons r rs ih =>
    simp only [prodMod, ih, resid_eq_mod, List.prod_cons]
    exact (Nat.mul_mod r rs.prod c).symm

public theorem gcdProd_eq (radices : List Nat) (m : Nat) :
    gcdProd radices m = Nat.gcd radices.prod m := by
  rw [gcdProd, euclid_eq_gcd, prodMod_eq, ← Nat.gcd_rec, Nat.gcd_comm]

public theorem radices_append (rs : List Nat) (m : Nat) :
    radices (rs ++ [m]) = radices rs ++ [m / gcdProd (radices rs) m] := by
  simp [radices, List.foldl_append]

/-- The product of the radices of positive moduli is their least common multiple. -/
public theorem prod_radices (rs : List Nat) (h : ∀ x ∈ rs, 0 < x) :
    (radices rs).prod = rs.foldl Nat.lcm 1 := by
  induction rs using List.reverseRecOn with
  | nil => simp [radices]
  | append_singleton rs m ih =>
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [radices_append, List.prod_append, List.prod_singleton, gcdProd_eq,
      ih', List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.lcm,
      Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

public theorem newRadix_eq (before : List Nat) (m : Nat) (h : ∀ x ∈ before, 0 < x) :
    newRadix before m = m / Nat.gcd (before.foldl Nat.lcm 1) m := by
  rw [newRadix, gcdProd_eq, prod_radices _ h]

/-- A positive modulus is irreducible after positive moduli exactly when it is coprime to
their lcm. -/
public theorem irreducibleAfter_iff (before : List Nat) (m : Nat) (hm : 0 < m)
    (h : ∀ x ∈ before, 0 < x) :
    IrreducibleAfter before m ↔ Nat.Coprime (before.foldl Nat.lcm 1) m := by
  rw [IrreducibleAfter, newRadix_eq _ _ h, Nat.div_eq_self, Nat.Coprime]
  omega

end Irreducibility
