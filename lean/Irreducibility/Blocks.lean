module

public import Mathlib
public import Irreducibility.Compare

/-!
# T5c: block representations and comparison across different blockings

* `blockModulus_spec`: a block of positive moduli with the residues `n % m` is one modulus
  `lcm moduli` with the residue `n % lcm moduli`.
* `flatten_spec`: a number given on blocks and quotient blocks becomes one list of moduli on
  which every modulus `c` has the residue `n % c`.
* `baseExtend_spec`: below the lcm of the moduli, base extension gives `n % c` on every
  target modulus `c`.
* `compareBlocks_eq`: two numbers, each below the lcm of all moduli of its own blocking,
  blocked in any two ways, compare as `compare n n'`.
-/

namespace Irreducibility

/-- The number `n` given on blocks `D` and quotient blocks `K`: the member residues of `D`
are `n % m`, those of `K` are the quotient `n / lcm D` modulo `m` (statements only). -/
@[expose] public def BlockRep.of (n : Nat) (D K : List (List Nat)) : BlockRep :=
  ⟨D, D.map (·.map (n % ·)), K, K.map (·.map (n / D.flatten.foldl Nat.lcm 1 % ·))⟩

theorem foldl_lcm_dvd_iff (l : List Nat) (a M : Nat) :
    l.foldl Nat.lcm a ∣ M ↔ a ∣ M ∧ ∀ x ∈ l, x ∣ M := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, Nat.lcm_dvd_iff]
    simp [and_assoc]

public theorem foldl_lcm_one_dvd_iff (l : List Nat) (M : Nat) :
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

/-- The lcm of the block lcms is the lcm of all members. -/
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

/-- A block of positive moduli with the residues `n % m` is one modulus `lcm moduli` with the
residue `n % lcm moduli`. -/
public theorem blockModulus_spec (n : Nat) (moduli : List Nat) (h : ∀ x ∈ moduli, 0 < x) :
    blockModulus moduli (moduli.map (n % ·)) =
      some (moduli.foldl Nat.lcm 1, n % moduli.foldl Nat.lcm 1) := by
  obtain ⟨ds, hds, hrad, _, hval⟩ := toMixedRadix_spec n moduli h
  simp only [blockModulus, hds, foldr_mul_snd, hrad, prod_radices _ h, hval]

public theorem blockModuli_spec (n : Nat) :
    ∀ (P : List (List Nat)), (∀ p ∈ P, ∀ x ∈ p, 0 < x) →
      blockModuli P (P.map (·.map (n % ·))) =
        some (P.map (·.foldl Nat.lcm 1), P.map (n % ·.foldl Nat.lcm 1))
  | [], _ => rfl
  | p :: P, h => by
    simp only [List.map_cons, blockModuli, blockModulus_spec n p (h p (by simp)),
      blockModuli_spec n P (fun q hq => h q (by simp [hq]))]

/-- Below the lcm of positive moduli, base extension gives `n % c` on every target
modulus `c`. -/
public theorem baseExtend_spec (moduli target : List Nat) (h : ∀ x ∈ moduli, 0 < x) {n : Nat}
    (hn : n < moduli.foldl Nat.lcm 1) :
    baseExtend moduli (moduli.map (n % ·)) target = some (target.map (n % ·)) := by
  obtain ⟨ds, hds, _, _, hval⟩ := toMixedRadix_spec n moduli h
  rw [Nat.mod_eq_of_lt hn] at hval
  simp only [baseExtend, hds, Option.some.injEq]
  exact List.map_congr_left fun c _ => by rw [evalMod_eq, hval]

theorem map_zip_map {α : Type} (P : List α) (f g : α → Nat) (h : Nat × Nat → Nat) :
    ((P.map f).zip (P.map g)).map h = P.map fun p => h (f p, g p) := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [ih]

/-- A number given on blocks `D` and quotient blocks `K` of positive moduli becomes one list
of moduli on which every modulus `c` has the residue `n % c`. -/
public theorem flatten_spec (n : Nat) (D K : List (List Nat))
    (hD : ∀ p ∈ D, ∀ x ∈ p, 0 < x) (hK : ∀ p ∈ K, ∀ x ∈ p, 0 < x) :
    flatten (BlockRep.of n D K) =
      some (D.map (·.foldl Nat.lcm 1) ++ K.map (·.foldl Nat.lcm 1),
        (D.map (·.foldl Nat.lcm 1) ++ K.map (·.foldl Nat.lcm 1)).map (n % ·)) := by
  have hDpos : ∀ x ∈ D.map (·.foldl Nat.lcm 1), 0 < x := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact foldl_lcm_pos (hD p hp)
  obtain ⟨dd, hdd, hrad, _, hval⟩ := toMixedRadix_spec n _ hDpos
  have hturn : (dd.map Prod.snd).prod = D.flatten.foldl Nat.lcm 1 := by
    rw [hrad, prod_radices _ hDpos, foldl_lcm_map]
  rw [foldl_lcm_map] at hval
  have hmod : ∀ c, (n / D.flatten.foldl Nat.lcm 1 % c * prodMod (dd.map Prod.snd) c +
      evalMod dd c) % c = n % c := by
    intro c
    rw [prodMod_eq, hturn, evalMod_eq, hval, Nat.add_mod, ← Nat.mul_mod, Nat.mod_mod,
      ← Nat.add_mod, Nat.div_add_mod']
  simp only [List.map_map, Function.comp_def] at hdd
  simp only [flatten, BlockRep.of, blockModuli_spec n D hD, blockModuli_spec _ K hK, hdd,
    map_zip_map, hmod, List.map_append, List.map_map, Function.comp_def]

/-- Two numbers, each below the lcm of all moduli of its own blocking, blocked in any two
ways on positive moduli, compare as `compare n n'`. -/
public theorem compareBlocks_eq {n n' : Nat} {D K D' K' : List (List Nat)}
    (hD : ∀ p ∈ D, ∀ x ∈ p, 0 < x) (hK : ∀ p ∈ K, ∀ x ∈ p, 0 < x)
    (hD' : ∀ p ∈ D', ∀ x ∈ p, 0 < x) (hK' : ∀ p ∈ K', ∀ x ∈ p, 0 < x)
    (hn : n < (D ++ K).flatten.foldl Nat.lcm 1) (hn' : n' < (D' ++ K').flatten.foldl Nat.lcm 1) :
    compareBlocks (BlockRep.of n D K) (BlockRep.of n' D' K') = some (compare n n') := by
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
  simp only [compareBlocks, flatten_spec n D K hD hK, flatten_spec n' D' K' hD' hK', ← hrxd,
    ← hryd]
  simp only [baseExtend_spec rx (union rx ry) hrx hnx, baseExtend_spec ry (union rx ry) hry hny]
  exact compareRes_eq _ hu
    (Nat.lt_of_lt_of_le hnx (hle rx fun c hc => (hmem c).2 (Or.inl hc)))
    (Nat.lt_of_lt_of_le hny (hle ry fun c hc => (hmem c).2 (Or.inr hc)))

end Irreducibility
