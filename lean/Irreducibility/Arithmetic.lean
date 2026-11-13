module

public import Mathlib
public import Irreducibility.Packs

/-!
# T8: arithmetic on a drum

A number `x` below the turn `W` of a drum of positive rings stands at `x % m` on each ring
`m`. Every operation below works on those states ring by ring and gives the states of the
result in `Z/WZ`.

* `addOn_spec`, `subOn_spec`, `mulOn_spec`, `powOn_spec`: sums, differences, products and
  powers.
* `addWraps_iff`, `subWraps_iff`: comparing states detects a pass over the end of the turn,
  `W ≤ x + y` for a sum and `x < y` for a difference.
* `exactDivOn_spec`, `div_lt_exactDivRings`: for `t ∣ x`, the quotient `x / t` stands on the
  rings `m / gcd m t`, and it is below their turn.
* `modR_spec`, `addressR_spec`: the phase `x % T` and the number of whole turns `x / T`, and
  the address `(k, i)` with `x = T * (k - 1) + i` and `1 ≤ i ≤ T`.
* `chapters_spec`: when `p ^ v` is the highest power of a prime `p` dividing `W`, adding the
  rings `p ^ (v + 1), ..., p ^ (v + j)` multiplies the turn by exactly `p ^ j`.
-/

namespace Irreducibility

theorem ringwise_map (f : Nat → Nat → Nat → Nat) (g h : Nat → Nat) :
    ∀ rings : List Nat,
      ringwise f rings (rings.map g) (rings.map h) = rings.map fun m => f m (g m) (h m)
  | [] => rfl
  | m :: rs => by simp [ringwise, ringwise_map f g h rs]

theorem zipWith_map_self (f : Nat → Nat → Nat) (g : Nat → Nat) :
    ∀ rings : List Nat, List.zipWith f rings (rings.map g) = rings.map fun m => f m (g m)
  | [] => rfl
  | m :: rs => by simp [zipWith_map_self f g rs]

theorem map_relation (rings : List Nat) (x : Nat) :
    rings.map (relation x ·) = rings.map (x % ·) :=
  List.map_congr_left fun c _ => relation_eq_mod x c

/-- The states of a sum are the states of `x + y`. -/
public theorem addOn_spec (rings : List Nat) (x y : Nat) :
    addOn rings (rings.map (x % ·)) (rings.map (y % ·)) = rings.map ((x + y) % ·) := by
  rw [addOn, ringwise_map]
  exact List.map_congr_left fun m _ => (Nat.add_mod x y m).symm

/-- Below the turn, a sum passes the end of the turn exactly when `W ≤ x + y`. -/
public theorem addWraps_iff {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {x y : Nat}
    (hx : x < rings.foldl Nat.lcm 1) (hy : y < rings.foldl Nat.lcm 1) :
    addWraps rings (rings.map (x % ·)) (rings.map (y % ·)) = true ↔
      rings.foldl Nat.lcm 1 ≤ x + y := by
  have hW := foldl_lcm_pos h
  have hs : rings.map ((x + y) % ·) = rings.map ((x + y) % rings.foldl Nat.lcm 1 % ·) :=
    List.map_congr_left fun c hc => (Nat.mod_mod_of_dvd _ (dvd_foldl_lcm hc)).symm
  rw [addWraps, addOn_spec, hs, compareOn_eq rings h (Nat.mod_lt _ hW) hx, decide_eq_true_iff,
    Option.some.injEq, Nat.compare_eq_lt]
  constructor
  · intro hlt
    by_contra hc
    rw [Nat.mod_eq_of_lt (by omega)] at hlt
    omega
  · intro hle
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Taking `y % m` back from `x % m` around ring `m` gives `(x - y) % m` when `y ≤ x`. -/
theorem sub_mod_states {m x y : Nat} (hm : 0 < m) (hy : y ≤ x) :
    (x % m + (m - y % m)) % m = (x - y) % m := by
  have hym := Nat.mod_lt y hm
  have hdm := Nat.div_add_mod y m
  have key : Nat.ModEq m (x % m + (m - y % m) + y) (x - y + y) := by
    unfold Nat.ModEq
    have : x % m + (m - y % m) + y = x % m + m * (y / m + 1) := by
      rw [Nat.mul_succ]; omega
    rw [Nat.sub_add_cancel hy, this, Nat.add_mul_mod_self_left, Nat.mod_mod]
  exact Nat.ModEq.add_right_cancel' y key

/-- The states of a difference with `y ≤ x` are the states of `x - y`. -/
public theorem subOn_spec_of_le {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {x y : Nat}
    (hy : y ≤ x) :
    subOn rings (rings.map (x % ·)) (rings.map (y % ·)) = rings.map ((x - y) % ·) := by
  rw [subOn, ringwise_map]
  exact List.map_congr_left fun m hm => sub_mod_states (h m hm) hy

/-- The states of a difference are the states of `x + (W - y)`, the difference in `Z/WZ`. -/
public theorem subOn_spec {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {x y : Nat}
    (hy : y ≤ rings.foldl Nat.lcm 1) :
    subOn rings (rings.map (x % ·)) (rings.map (y % ·)) =
      rings.map ((x + (rings.foldl Nat.lcm 1 - y)) % ·) := by
  rw [subOn, ringwise_map]
  refine List.map_congr_left fun m hm => ?_
  obtain ⟨k, hk⟩ := dvd_foldl_lcm hm
  have hxW : (x + rings.foldl Nat.lcm 1) % m = x % m := by rw [hk, Nat.add_mul_mod_self_left]
  have := sub_mod_states (x := x + rings.foldl Nat.lcm 1) (h m hm) (show y ≤ _ by omega)
  rw [hxW, show x + rings.foldl Nat.lcm 1 - y = x + (rings.foldl Nat.lcm 1 - y) by omega] at this
  exact this

/-- Below the turn, a difference passes below `0` exactly when `x < y`. -/
public theorem subWraps_iff {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {x y : Nat}
    (hx : x < rings.foldl Nat.lcm 1) (hy : y < rings.foldl Nat.lcm 1) :
    subWraps rings (rings.map (x % ·)) (rings.map (y % ·)) = true ↔ x < y := by
  rw [subWraps, compareOn_eq rings h hx hy, decide_eq_true_iff, Option.some.injEq,
    Nat.compare_eq_lt]

/-- The states of a product are the states of `x * y`. -/
public theorem mulOn_spec (rings : List Nat) (x y : Nat) :
    mulOn rings (rings.map (x % ·)) (rings.map (y % ·)) = rings.map ((x * y) % ·) := by
  rw [mulOn, ringwise_map]
  exact List.map_congr_left fun m _ => (Nat.mul_mod x y m).symm

/-- The states of the `e`-th power are the states of `x ^ e`. -/
public theorem powOn_spec (rings : List Nat) (x : Nat) :
    ∀ e, powOn rings (rings.map (x % ·)) e = rings.map ((x ^ e) % ·)
  | 0 => by rw [powOn, map_relation, pow_zero]
  | e + 1 => by rw [powOn, powOn_spec rings x e, mulOn_spec, pow_succ]

/-- On one ring `m`, exact division of `x` by `t` gives `(x / t) % (m / gcd m t)`. -/
theorem exactDiv_ring {m t x : Nat} (hm : 0 < m) (ht : 0 < t) (hd : t ∣ x) :
    x % m / Nat.gcd m t * inverse (t / Nat.gcd m t % (m / Nat.gcd m t)) (m / Nat.gcd m t) %
      (m / Nat.gcd m t) = x / t % (m / Nat.gcd m t) := by
  have hcop := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left t hm)
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd m t := ⟨_, rfl⟩
  rw [← hg] at hcop ⊢
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left t hm
  obtain ⟨r, hr⟩ : g ∣ m := hg ▸ Nat.gcd_dvd_left m t
  obtain ⟨T, hT⟩ : g ∣ t := hg ▸ Nat.gcd_dvd_right m t
  obtain ⟨q, rfl⟩ := hd
  have hmr : m / g = r := by rw [hr, Nat.mul_div_cancel_left _ hg0]
  have htT : t / g = T := by rw [hT, Nat.mul_div_cancel_left _ hg0]
  have hx : t * q % m / g = T * q % r := by
    rw [hT, hr, Nat.mul_assoc, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hg0]
  rw [hmr, htT] at hcop
  rw [hmr, htT, hx, Nat.mul_div_cancel_left _ ht]
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, Nat.mul_zero] at hr; omega
    · exact h0
  rcases Nat.lt_or_ge 1 r with hr1 | hr1
  · have hc : Nat.Coprime (T % r) r := by
      rw [Nat.Coprime, ← Nat.gcd_rec]; exact hcop
    have hinv := inverse_spec hr1 hc
    rw [Nat.mod_mul_mod] at hinv
    rw [Nat.mod_mul_mod, show T * q * inverse (T % r) r = q * (T * inverse (T % r) r) by ring,
      Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod]
  · obtain rfl : r = 1 := by omega
    simp [Nat.mod_one]

/-- For `t ∣ x`, exact division by `t` gives the states of `x / t` on the rings
`m / gcd m t`. -/
public theorem exactDivOn_spec {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {t x : Nat}
    (ht : 0 < t) (hd : t ∣ x) :
    exactDivOn rings (rings.map (x % ·)) t = (exactDivRings rings t).map ((x / t) % ·) := by
  simp only [exactDivOn, exactDivRings, zipWith_map_self, List.map_map, Function.comp_def]
  refine List.map_congr_left fun m hm => ?_
  rw [commonPart_eq_gcd]
  exact exactDiv_ring (h m hm) ht hd

theorem pos_of_mem_exactDivRings {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) (t : Nat) :
    ∀ c ∈ exactDivRings rings t, 0 < c := by
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
  rw [commonPart_eq_gcd]
  exact Nat.div_pos (Nat.le_of_dvd (h m hm) (Nat.gcd_dvd_left m t))
    (Nat.gcd_pos_of_pos_left t (h m hm))

/-- Below the turn, the quotient `x / t` is below the turn of the rings `m / gcd m t`, so
their states determine it. -/
public theorem div_lt_exactDivRings {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {t x : Nat}
    (ht : 0 < t) (hd : t ∣ x) (hx : x < rings.foldl Nat.lcm 1) :
    x / t < (exactDivRings rings t).foldl Nat.lcm 1 := by
  have hL := foldl_lcm_pos (pos_of_mem_exactDivRings h t)
  have hW : rings.foldl Nat.lcm 1 ∣ t * (exactDivRings rings t).foldl Nat.lcm 1 := by
    rw [foldl_lcm_one_dvd_iff]
    intro m hm
    have hmem : m / commonPart m t ∈ exactDivRings rings t := List.mem_map.2 ⟨m, hm, rfl⟩
    refine Nat.dvd_trans ?_ (Nat.mul_dvd_mul_left t (dvd_foldl_lcm hmem))
    rw [commonPart_eq_gcd]
    have := Nat.mul_dvd_mul_right (Nat.gcd_dvd_right m t) (m / Nat.gcd m t)
    rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left m t)] at this
  obtain ⟨q, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left q ht]
  have := Nat.le_of_dvd (Nat.mul_pos ht hL) hW
  exact Nat.lt_of_mul_lt_mul_left (a := t) (by omega)

/-- Below the turn, `modR` reads the phase `x % T` and the states of the number of whole
turns `x / T` of ring `T`. -/
public theorem modR_spec {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {x T : Nat}
    (hT : 0 < T) (hx : x < rings.foldl Nat.lcm 1) :
    modR rings (rings.map (x % ·)) T = some (x % T, (exactDivRings rings T).map ((x / T) % ·)) := by
  obtain ⟨ds, hds, -, -, hval⟩ := digitsOf_spec x rings h
  rw [Nat.mod_eq_of_lt hx] at hval
  have hq : x - x % T = T * (x / T) := by have := Nat.div_add_mod x T; omega
  simp only [modR, hds, positionOn_eq, hval, map_relation]
  rw [subOn_spec_of_le h (Nat.mod_le x T), exactDivOn_spec h hT (Nat.dvd_sub_mod x), hq,
    Nat.mul_div_cancel_left _ hT]

/-- For `0 < x` below the turn, the address `(k, i)` on ring `T` has phase
`i = (x - 1) % T + 1` and turn number `k = (x - 1) / T + 1`, so `x = T * (k - 1) + i`. -/
public theorem addressR_spec {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {x T : Nat}
    (hT : 0 < T) (hx0 : 0 < x) (hx : x < rings.foldl Nat.lcm 1) :
    addressR rings (rings.map (x % ·)) T =
      some ((x - 1) % T + 1, (exactDivRings rings T).map (((x - 1) / T + 1) % ·)) := by
  have hdm := Nat.div_add_mod x T
  have hrT := Nat.mod_lt x hT
  simp only [addressR, modR_spec h hT hx]
  split_ifs with hr
  · obtain ⟨q, hq⟩ : ∃ q, q = x / T := ⟨_, rfl⟩
    rw [← hq] at hdm ⊢
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0] at hdm; omega
      · exact h0
    have hsub := Nat.mul_sub_one T q
    have hle : T ≤ T * q := Nat.le_mul_of_pos_right T hq1
    obtain ⟨hd, hm⟩ := (Nat.div_mod_unique hT).2 (show T - 1 + T * (q - 1) = x - 1 ∧ T - 1 < T by
      constructor <;> omega)
    rw [hd, hm, show T - 1 + 1 = T by omega, show q - 1 + 1 = q by omega]
  · rw [map_relation, addOn_spec]
    obtain ⟨hd, hm⟩ := (Nat.div_mod_unique hT).2
      (show x % T - 1 + T * (x / T) = x - 1 ∧ x % T - 1 < T by constructor <;> omega)
    rw [hd, hm, show x % T - 1 + 1 = x % T by omega]

theorem foldl_lcm_append_single (rings : List Nat) (c : Nat) :
    (rings ++ [c]).foldl Nat.lcm 1 = Nat.lcm (rings.foldl Nat.lcm 1) c := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- When `p ^ v` is the highest power of a prime `p` dividing `W`, the ring `p ^ (v + 1)`
multiplies `W` by exactly `p`. -/
theorem lcm_pow_succ {W p v : Nat} (hp : p.Prime) (hv : p ^ v ∣ W) (hv' : ¬ p ^ (v + 1) ∣ W) :
    Nat.lcm W (p ^ (v + 1)) = p * W := by
  have hg : Nat.gcd W (p ^ (v + 1)) = p ^ v := by
    obtain ⟨j, hj, hjg⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right W (p ^ (v + 1)))
    have hvj : p ^ v ∣ p ^ j := by
      rw [← hjg]; exact Nat.dvd_gcd hv (Nat.pow_dvd_pow p (Nat.le_succ v))
    have hle : v ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hvj
    have hne : j ≠ v + 1 := by
      rintro rfl
      exact hv' (hjg ▸ Nat.gcd_dvd_left W (p ^ (v + 1)))
    rw [hjg, show j = v by omega]
  have hpv : 0 < p ^ v := Nat.pow_pos (n := v) hp.pos
  have := Nat.gcd_mul_lcm W (p ^ (v + 1))
  rw [hg] at this
  apply Nat.eq_of_mul_eq_mul_left hpv
  rw [this, pow_succ]
  ring

/-- Chapters: when `p ^ v` is the highest power of a prime `p` dividing the turn of the
drum, adding the rings `p ^ (v + 1), ..., p ^ (v + j)` multiplies the turn by `p ^ j`, one
factor `p` per ring. -/
public theorem chapters_spec (rings : List Nat) {p v : Nat} (hp : p.Prime)
    (hv : p ^ v ∣ rings.foldl Nat.lcm 1) (hv' : ¬ p ^ (v + 1) ∣ rings.foldl Nat.lcm 1) :
    ∀ j, (rings ++ (List.range j).map fun i => p ^ (v + 1 + i)).foldl Nat.lcm 1 =
      p ^ j * rings.foldl Nat.lcm 1
  | 0 => by simp
  | j + 1 => by
    have hpj : 0 < p ^ j := Nat.pow_pos (n := j) hp.pos
    rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc,
      foldl_lcm_append_single, chapters_spec rings hp hv hv' j,
      show v + 1 + j = v + j + 1 by omega, lcm_pow_succ hp]
    · ring
    · rw [pow_add, Nat.mul_comm (p ^ j)]
      exact Nat.mul_dvd_mul_right hv _
    · intro hdvd
      rw [show v + j + 1 = j + (v + 1) by omega, pow_add] at hdvd
      exact hv' (Nat.dvd_of_mul_dvd_mul_left hpj hdvd)

example : ([4, 3, 5] ++ (List.range 2).map fun i => 2 ^ (2 + 1 + i)).foldl Nat.lcm 1 = 240 := by
  decide

end Irreducibility
