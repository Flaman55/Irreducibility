module

public import Mathlib
public import Irreducibility.Compare

/-!
# T5c: drums of packs and comparing across different packings

* `packRing_spec`: a pack of positive rings in the states `n % m` is one ring of period
  `lcm members` in state `n % lcm members`.
* `flatten_spec`: a number given on packs and rotation packs becomes one drum of packs on
  which every ring `c` stands at `n % c`.
* `extend_spec`: below the turn of a drum, carrying its position onto other rings gives
  `n % c` on each of them.
* `comparePacked_eq`: two numbers below the turns of their own packings, packed in any two
  ways, compare as `compare n n'`.
-/

namespace Irreducibility

/-- The number `n` given on packs `D` and rotation packs `K`: the member states of `D` are
`n % m`, those of `K` are the number of whole turns of `D`, `n / lcm D`, modulo `m`
(statements only). -/
@[expose] public def Packed.of (n : Nat) (D K : List (List Nat)) : Packed :=
  ⟨D, D.map (·.map (n % ·)), K, K.map (·.map (n / D.flatten.foldl Nat.lcm 1 % ·))⟩

theorem foldl_lcm_dvd_iff (l : List Nat) (a M : Nat) :
    l.foldl Nat.lcm a ∣ M ↔ a ∣ M ∧ ∀ x ∈ l, x ∣ M := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, Nat.lcm_dvd_iff]
    simp [and_assoc]

theorem foldl_lcm_one_dvd_iff (l : List Nat) (M : Nat) :
    l.foldl Nat.lcm 1 ∣ M ↔ ∀ x ∈ l, x ∣ M := by
  simp [foldl_lcm_dvd_iff]

public theorem dvd_foldl_lcm {l : List Nat} {x : Nat} (hx : x ∈ l) : x ∣ l.foldl Nat.lcm 1 :=
  (foldl_lcm_one_dvd_iff l _).1 dvd_rfl x hx

public theorem foldl_lcm_pos {l : List Nat} (h : ∀ x ∈ l, 0 < x) : 0 < l.foldl Nat.lcm 1 := by
  suffices ∀ a, 0 < a → 0 < l.foldl Nat.lcm a from this 1 Nat.one_pos
  induction l with
  | nil => simp
  | cons x l ih =>
    intro a ha
    rw [List.foldl_cons]
    exact ih (fun y hy => h y (by simp [hy])) _ (Nat.lcm_pos ha (h x (by simp)))

/-- The lcm of the pack lcms is the lcm of all members. -/
theorem foldl_lcm_map (P : List (List Nat)) :
    (P.map (·.foldl Nat.lcm 1)).foldl Nat.lcm 1 = P.flatten.foldl Nat.lcm 1 := by
  apply Nat.dvd_antisymm
  · rw [foldl_lcm_one_dvd_iff]
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    rw [foldl_lcm_one_dvd_iff]
    exact fun y hy => dvd_foldl_lcm (List.mem_flatten.2 ⟨p, hp, hy⟩)
  · rw [foldl_lcm_one_dvd_iff]
    intro y hy
    obtain ⟨p, hp, hyp⟩ := List.mem_flatten.1 hy
    exact (dvd_foldl_lcm hyp).trans (dvd_foldl_lcm (List.mem_map.2 ⟨p, hp, rfl⟩))

theorem foldr_mul_snd (ds : List (Nat × Nat)) :
    ds.foldr (fun p acc => p.2 * acc) 1 = (ds.map Prod.snd).prod := by
  induction ds with
  | nil => rfl
  | cons p ds ih => simp [ih]

/-- A pack of positive rings in the states `n % m` is one ring of period `lcm members` in
state `n % lcm members`. -/
public theorem packRing_spec (n : Nat) (members : List Nat) (h : ∀ x ∈ members, 0 < x) :
    packRing members (members.map (n % ·)) =
      some (members.foldl Nat.lcm 1, n % members.foldl Nat.lcm 1) := by
  obtain ⟨ds, hds, hrad, _, hval⟩ := digitsOf_spec n members h
  simp only [packRing, hds, foldr_mul_snd, hrad, prod_levels _ h, hval]

public theorem drumOfPacks_spec (n : Nat) :
    ∀ (P : List (List Nat)), (∀ p ∈ P, ∀ x ∈ p, 0 < x) →
      drumOfPacks P (P.map (·.map (n % ·))) =
        some (P.map (·.foldl Nat.lcm 1), P.map (n % ·.foldl Nat.lcm 1))
  | [], _ => rfl
  | p :: P, h => by
    simp only [List.map_cons, drumOfPacks, packRing_spec n p (h p (by simp)),
      drumOfPacks_spec n P (fun q hq => h q (by simp [hq]))]

/-- Below the turn of a drum of positive rings, carrying its position onto other rings
gives `n % c` on each of them. -/
public theorem extend_spec (rings target : List Nat) (h : ∀ x ∈ rings, 0 < x) {n : Nat}
    (hn : n < rings.foldl Nat.lcm 1) :
    extend rings (rings.map (n % ·)) target = some (target.map (n % ·)) := by
  obtain ⟨ds, hds, _, _, hval⟩ := digitsOf_spec n rings h
  rw [Nat.mod_eq_of_lt hn] at hval
  simp only [extend, hds, Option.some.injEq]
  exact List.map_congr_left fun c _ => by rw [positionOn_eq, hval]

theorem map_zip_map {α : Type} (P : List α) (f g : α → Nat) (h : Nat × Nat → Nat) :
    ((P.map f).zip (P.map g)).map h = P.map fun p => h (f p, g p) := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [ih]

/-- A number given on packs `D` and rotation packs `K` of positive rings becomes one drum of
packs on which every ring `c` stands at `n % c`. -/
public theorem flatten_spec (n : Nat) (D K : List (List Nat))
    (hD : ∀ p ∈ D, ∀ x ∈ p, 0 < x) (hK : ∀ p ∈ K, ∀ x ∈ p, 0 < x) :
    flatten (Packed.of n D K) =
      some (D.map (·.foldl Nat.lcm 1) ++ K.map (·.foldl Nat.lcm 1),
        (D.map (·.foldl Nat.lcm 1) ++ K.map (·.foldl Nat.lcm 1)).map (n % ·)) := by
  have hDpos : ∀ x ∈ D.map (·.foldl Nat.lcm 1), 0 < x := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact foldl_lcm_pos (hD p hp)
  obtain ⟨dd, hdd, hrad, _, hval⟩ := digitsOf_spec n _ hDpos
  have hturn : (dd.map Prod.snd).prod = D.flatten.foldl Nat.lcm 1 := by
    rw [hrad, prod_levels _ hDpos, foldl_lcm_map]
  rw [foldl_lcm_map] at hval
  have hmod : ∀ c, (n / D.flatten.foldl Nat.lcm 1 % c * turnOn (dd.map Prod.snd) c +
      positionOn dd c) % c = n % c := by
    intro c
    rw [turnOn_eq, hturn, positionOn_eq, hval, Nat.add_mod, ← Nat.mul_mod, Nat.mod_mod,
      ← Nat.add_mod, Nat.div_add_mod']
  simp only [List.map_map, Function.comp_def] at hdd
  simp only [flatten, Packed.of, drumOfPacks_spec n D hD, drumOfPacks_spec _ K hK, hdd,
    map_zip_map, hmod, List.map_append, List.map_map, Function.comp_def]

/-- Two numbers, each below the turn of all the rings of its own packing, packed in any two
ways on positive rings, compare as `compare n n'`. -/
public theorem comparePacked_eq {n n' : Nat} {D K D' K' : List (List Nat)}
    (hD : ∀ p ∈ D, ∀ x ∈ p, 0 < x) (hK : ∀ p ∈ K, ∀ x ∈ p, 0 < x)
    (hD' : ∀ p ∈ D', ∀ x ∈ p, 0 < x) (hK' : ∀ p ∈ K', ∀ x ∈ p, 0 < x)
    (hn : n < (D ++ K).flatten.foldl Nat.lcm 1) (hn' : n' < (D' ++ K').flatten.foldl Nat.lcm 1) :
    comparePacked (Packed.of n D K) (Packed.of n' D' K') = some (compare n n') := by
  set rx := D.map (·.foldl Nat.lcm 1) ++ K.map (·.foldl Nat.lcm 1) with hrxd
  set ry := D'.map (·.foldl Nat.lcm 1) ++ K'.map (·.foldl Nat.lcm 1) with hryd
  have hpos : ∀ (P : List (List Nat)), (∀ p ∈ P, ∀ x ∈ p, 0 < x) →
      ∀ x ∈ P.map (·.foldl Nat.lcm 1), 0 < x := fun P h x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact foldl_lcm_pos (h p hp)
  have hrx : ∀ x ∈ rx, 0 < x := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    exacts [hpos D hD x hx, hpos K hK x hx]
  have hry : ∀ x ∈ ry, 0 < x := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    exacts [hpos D' hD' x hx, hpos K' hK' x hx]
  have hLx : rx.foldl Nat.lcm 1 = (D ++ K).flatten.foldl Nat.lcm 1 := by
    rw [hrxd, ← List.map_append, foldl_lcm_map]
  have hLy : ry.foldl Nat.lcm 1 = (D' ++ K').flatten.foldl Nat.lcm 1 := by
    rw [hryd, ← List.map_append, foldl_lcm_map]
  have hmem : ∀ c, c ∈ union rx ry ↔ c ∈ rx ∨ c ∈ ry := fun c => by
    simp only [union, List.mem_append, List.mem_filter]
    by_cases hc : c ∈ rx <;> simp [hc]
  have hu : ∀ x ∈ union rx ry, 0 < x := fun x hx => by
    rcases (hmem x).1 hx with hx | hx
    exacts [hrx x hx, hry x hx]
  have hle : ∀ r : List Nat, (∀ c ∈ r, c ∈ union rx ry) →
      r.foldl Nat.lcm 1 ≤ (union rx ry).foldl Nat.lcm 1 := fun r h =>
    Nat.le_of_dvd (foldl_lcm_pos hu)
      ((foldl_lcm_one_dvd_iff _ _).2 fun c hc => dvd_foldl_lcm (h c hc))
  have hnx : n < rx.foldl Nat.lcm 1 := hLx ▸ hn
  have hny : n' < ry.foldl Nat.lcm 1 := hLy ▸ hn'
  simp only [comparePacked, flatten_spec n D K hD hK, flatten_spec n' D' K' hD' hK', ← hrxd,
    ← hryd]
  simp only [extend_spec rx (union rx ry) hrx hnx, extend_spec ry (union rx ry) hry hny]
  exact compareOn_eq _ hu
    (Nat.lt_of_lt_of_le hnx (hle rx fun c hc => (hmem c).2 (Or.inl hc)))
    (Nat.lt_of_lt_of_le hny (hle ry fun c hc => (hmem c).2 (Or.inr hc)))

end Irreducibility
