module

public import Mathlib
public import Irreducibility.Euclid

/-!
# T3: the drum

* `absorb_eq`: absorbing one level takes the common part once; after one step nothing is
  left to share (`Nat.coprime_div_gcd_div_gcd`), so the loop never runs twice.
* `commonPartWithTurn_eq`: the level-by-level procedure gives `gcd (turn) m`, where the turn
  is the product of the level sizes; the turn itself is never formed by the procedure.
* `prod_levels`: the drum built from positive rings turns once per their least common
  multiple.
* `irreducibleAfter_iff`: a positive ring is irreducible after the rings before it exactly
  when it shares nothing with their common turn.
-/

namespace Irreducibility

/-- `gcd (a * b) m = gcd a m * gcd b (m / gcd a m)`: the part of `m` shared with a product,
taken factor by factor. -/
public theorem gcd_mul_split (a b m : Nat) :
    Nat.gcd (a * b) m = Nat.gcd a m * Nat.gcd b (m / Nat.gcd a m) := by
  rcases Nat.eq_zero_or_pos (Nat.gcd a m) with hg | hg
  · rw [Nat.gcd_eq_zero_iff] at hg
    obtain ⟨rfl, rfl⟩ := hg
    simp
  · set g := Nat.gcd a m with hgdef
    obtain ⟨a', ha⟩ := Nat.gcd_dvd_left a m
    obtain ⟨m', hm⟩ := Nat.gcd_dvd_right a m
    have hcop : Nat.Coprime (a / g) (m / g) := Nat.coprime_div_gcd_div_gcd hg
    have ha' : a / g = a' := by rw [← hgdef] at ha; rw [ha, Nat.mul_div_cancel_left _ hg]
    have hm' : m / g = m' := by rw [← hgdef] at hm; rw [hm, Nat.mul_div_cancel_left _ hg]
    rw [ha', hm'] at hcop
    rw [hm', ← hgdef] at *
    conv_lhs => rw [ha, hm, Nat.mul_assoc, Nat.gcd_mul_left]
    rw [Nat.Coprime.gcd_mul_left_cancel b hcop]

public theorem absorb_eq (fuel r g rest : Nat) (hrest : 0 < rest) (hfuel : 2 ≤ fuel) :
    absorb fuel r g rest = (g * Nat.gcd r rest, rest / Nat.gcd r rest) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
  have ht : 0 < Nat.gcd r rest := Nat.gcd_pos_of_pos_right r hrest
  simp only [absorb, commonPart_eq_gcd]
  split_ifs with h1 h2
  · have : Nat.gcd r rest = 1 := by omega
    simp [this]
  · rfl
  · exfalso
    have := Nat.coprime_div_gcd_div_gcd ht
    rw [Nat.Coprime] at this
    omega

theorem foldl_absorb (m : Nat) (hm : 0 < m) :
    ∀ (rs : List Nat) (g rest P : Nat), g * rest = m → g = Nat.gcd P m →
      (rs.foldl (fun acc r => absorb (m + 1) r acc.1 acc.2) (g, rest)).1 =
        Nat.gcd (P * rs.prod) m
  | [], g, rest, P, _, hg => by simp [hg]
  | r :: rs, g, rest, P, hgr, hg => by
    have hrest : 0 < rest := by
      rcases Nat.eq_zero_or_pos rest with h | h
      · subst h; omega
      · exact h
    have hgpos : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h | h
      · subst h; omega
      · exact h
    have hrest_eq : rest = m / g := by
      rw [← hgr, Nat.mul_div_cancel_left _ hgpos]
    simp only [List.foldl_cons, List.prod_cons]
    rw [absorb_eq (m + 1) r g rest hrest (by omega)]
    have := foldl_absorb m hm rs (g * Nat.gcd r rest) (rest / Nat.gcd r rest) (P * r)
      (by
        rw [Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right r rest), hgr])
      (by rw [gcd_mul_split, ← hg, ← hrest_eq])
    simpa [Nat.mul_assoc] using this

public theorem commonPartWithTurn_eq (radices : List Nat) (m : Nat) (hm : 0 < m) :
    commonPartWithTurn radices m = Nat.gcd radices.prod m := by
  have := foldl_absorb m hm radices 1 m 1 (by simp) (by simp)
  simpa [commonPartWithTurn] using this

public theorem levels_append (rs : List Nat) (m : Nat) :
    levels (rs ++ [m]) = levels rs ++ [m / commonPartWithTurn (levels rs) m] := by
  simp [levels, List.foldl_append]

/-- The drum built from positive rings turns once per their least common multiple. -/
public theorem prod_levels (rs : List Nat) (h : ∀ x ∈ rs, 0 < x) :
    (levels rs).prod = rs.foldl Nat.lcm 1 := by
  induction rs using List.reverseRecOn with
  | nil => simp [levels]
  | append_singleton rs m ih =>
    have hm : 0 < m := h m (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [levels_append, List.prod_append, List.prod_singleton, commonPartWithTurn_eq _ _ hm,
      ih', List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.lcm,
      Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

public theorem levelSize_eq (before : List Nat) (m : Nat) (hm : 0 < m)
    (h : ∀ x ∈ before, 0 < x) :
    levelSize before m = m / Nat.gcd (before.foldl Nat.lcm 1) m := by
  rw [levelSize, commonPartWithTurn_eq _ _ hm, prod_levels _ h]

/-- A positive ring is irreducible after positive rings exactly when it shares nothing with
their common turn. -/
public theorem irreducibleAfter_iff (before : List Nat) (m : Nat) (hm : 0 < m)
    (h : ∀ x ∈ before, 0 < x) :
    IrreducibleAfter before m ↔ Nat.Coprime (before.foldl Nat.lcm 1) m := by
  rw [IrreducibleAfter, levelSize_eq _ _ hm h, Nat.div_eq_self, Nat.Coprime]
  omega

end Irreducibility
