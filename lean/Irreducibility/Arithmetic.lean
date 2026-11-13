module

public import Mathlib
public import Irreducibility.Blocks

/-!
# T8: arithmetic on residues

A number `x` below the lcm `W` of positive moduli has the residue `x % m` for each modulus `m`.
Every operation below works on those residues modulus by modulus and gives the residues of the
result in `Z/WZ`.

* `addRes_spec`, `subRes_spec`, `mulRes_spec`, `powRes_spec`: sums, differences, products and
  powers.
* `addOverflow_iff`, `subUnderflow_iff`: comparing residue vectors detects overflow,
  `W ≤ x + y`, of a sum and underflow, `x < y`, of a difference.
* `exactDivRes_spec`, `div_lt_divModuli`: for `t ∣ x`, the quotient `x / t` is given on the
  moduli `m / gcd m t`, and it is below their lcm.
* `divModRes_spec`, `addressRes_spec`: the remainder `x % T` and the quotient `x / T`, and the
  address `(k, i)` with `x = T * (k - 1) + i` and `1 ≤ i ≤ T`.
* `lcm_append_prime_powers`: when `p ^ v` is the highest power of a prime `p` dividing `W`,
  appending the moduli `p ^ (v + 1), ..., p ^ (v + j)` multiplies the lcm by exactly `p ^ j`.
-/

namespace Irreducibility

theorem pointwise_map (f : Nat → Nat → Nat → Nat) (g h : Nat → Nat) :
    ∀ moduli : List Nat,
      pointwise f moduli (moduli.map g) (moduli.map h) = moduli.map fun m => f m (g m) (h m)
  | [] => rfl
  | m :: rs => by simp [pointwise, pointwise_map f g h rs]

theorem zipWith_map_self (f : Nat → Nat → Nat) (g : Nat → Nat) :
    ∀ moduli : List Nat, List.zipWith f moduli (moduli.map g) = moduli.map fun m => f m (g m)
  | [] => rfl
  | m :: rs => by simp [zipWith_map_self f g rs]

theorem map_resid (moduli : List Nat) (x : Nat) :
    moduli.map (resid x ·) = moduli.map (x % ·) :=
  List.map_congr_left fun c _ => resid_eq_mod x c

/-- The residues of a sum are the residues of `x + y`. -/
public theorem addRes_spec (moduli : List Nat) (x y : Nat) :
    addRes moduli (moduli.map (x % ·)) (moduli.map (y % ·)) = moduli.map ((x + y) % ·) := by
  rw [addRes, pointwise_map]
  exact List.map_congr_left fun m _ => (Nat.add_mod x y m).symm

/-- Below the lcm, a sum overflows exactly when `W ≤ x + y`. -/
public theorem addOverflow_iff {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {x y : Nat}
    (hx : x < moduli.foldl Nat.lcm 1) (hy : y < moduli.foldl Nat.lcm 1) :
    addOverflow moduli (moduli.map (x % ·)) (moduli.map (y % ·)) = true ↔
      moduli.foldl Nat.lcm 1 ≤ x + y := by
  have hW := foldl_lcm_pos h
  have hs : moduli.map ((x + y) % ·) = moduli.map ((x + y) % moduli.foldl Nat.lcm 1 % ·) :=
    List.map_congr_left fun c hc => (Nat.mod_mod_of_dvd _ (dvd_foldl_lcm hc)).symm
  rw [addOverflow, addRes_spec, hs, compareRes_eq moduli h (Nat.mod_lt _ hW) hx, decide_eq_true_iff,
    Option.some.injEq, Nat.compare_eq_lt]
  constructor
  · intro hlt
    by_contra hc
    rw [Nat.mod_eq_of_lt (by omega)] at hlt
    omega
  · intro hle
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `(x % m + (m - y % m)) % m = (x - y) % m` when `y ≤ x`. -/
theorem sub_mod_residues {m x y : Nat} (hm : 0 < m) (hy : y ≤ x) :
    (x % m + (m - y % m)) % m = (x - y) % m := by
  have hym := Nat.mod_lt y hm
  have hdm := Nat.div_add_mod y m
  have key : Nat.ModEq m (x % m + (m - y % m) + y) (x - y + y) := by
    unfold Nat.ModEq
    have : x % m + (m - y % m) + y = x % m + m * (y / m + 1) := by
      rw [Nat.mul_succ]; omega
    rw [Nat.sub_add_cancel hy, this, Nat.add_mul_mod_self_left, Nat.mod_mod]
  exact Nat.ModEq.add_right_cancel' y key

/-- The residues of a difference with `y ≤ x` are the residues of `x - y`. -/
public theorem subRes_spec_of_le {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {x y : Nat}
    (hy : y ≤ x) :
    subRes moduli (moduli.map (x % ·)) (moduli.map (y % ·)) = moduli.map ((x - y) % ·) := by
  rw [subRes, pointwise_map]
  exact List.map_congr_left fun m hm => sub_mod_residues (h m hm) hy

/-- The residues of a difference are the residues of `x + (W - y)`, the difference in `Z/WZ`. -/
public theorem subRes_spec {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {x y : Nat}
    (hy : y ≤ moduli.foldl Nat.lcm 1) :
    subRes moduli (moduli.map (x % ·)) (moduli.map (y % ·)) =
      moduli.map ((x + (moduli.foldl Nat.lcm 1 - y)) % ·) := by
  rw [subRes, pointwise_map]
  refine List.map_congr_left fun m hm => ?_
  obtain ⟨k, hk⟩ := dvd_foldl_lcm hm
  have hxW : (x + moduli.foldl Nat.lcm 1) % m = x % m := by rw [hk, Nat.add_mul_mod_self_left]
  have := sub_mod_residues (x := x + moduli.foldl Nat.lcm 1) (h m hm) (show y ≤ _ by omega)
  rw [hxW, show x + moduli.foldl Nat.lcm 1 - y = x + (moduli.foldl Nat.lcm 1 - y) by omega] at this
  exact this

/-- Below the lcm, a difference underflows exactly when `x < y`. -/
public theorem subUnderflow_iff {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {x y : Nat}
    (hx : x < moduli.foldl Nat.lcm 1) (hy : y < moduli.foldl Nat.lcm 1) :
    subUnderflow moduli (moduli.map (x % ·)) (moduli.map (y % ·)) = true ↔ x < y := by
  rw [subUnderflow, compareRes_eq moduli h hx hy, decide_eq_true_iff, Option.some.injEq,
    Nat.compare_eq_lt]

/-- The residues of a product are the residues of `x * y`. -/
public theorem mulRes_spec (moduli : List Nat) (x y : Nat) :
    mulRes moduli (moduli.map (x % ·)) (moduli.map (y % ·)) = moduli.map ((x * y) % ·) := by
  rw [mulRes, pointwise_map]
  exact List.map_congr_left fun m _ => (Nat.mul_mod x y m).symm

/-- The residues of the `e`-th power are the residues of `x ^ e`. -/
public theorem powRes_spec (moduli : List Nat) (x : Nat) :
    ∀ e, powRes moduli (moduli.map (x % ·)) e = moduli.map ((x ^ e) % ·)
  | 0 => by rw [powRes, map_resid, pow_zero]
  | e + 1 => by rw [powRes, powRes_spec moduli x e, mulRes_spec, pow_succ]

/-- For one modulus `m`, exact division of `x` by `t` gives `(x / t) % (m / gcd m t)`. -/
theorem exactDiv_modulus {m t x : Nat} (hm : 0 < m) (ht : 0 < t) (hd : t ∣ x) :
    x % m / Nat.gcd m t * invMod (t / Nat.gcd m t % (m / Nat.gcd m t)) (m / Nat.gcd m t) %
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
    have hinv := invMod_spec hr1 hc
    rw [Nat.mod_mul_mod] at hinv
    rw [Nat.mod_mul_mod, show T * q * invMod (T % r) r = q * (T * invMod (T % r) r) by ring,
      Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod]
  · obtain rfl : r = 1 := by omega
    simp [Nat.mod_one]

/-- For `t ∣ x`, exact division by `t` gives the residues of `x / t` on the moduli
`m / gcd m t`. -/
public theorem exactDivRes_spec {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {t x : Nat}
    (ht : 0 < t) (hd : t ∣ x) :
    exactDivRes moduli (moduli.map (x % ·)) t = (divModuli moduli t).map ((x / t) % ·) := by
  simp only [exactDivRes, divModuli, zipWith_map_self, List.map_map, Function.comp_def]
  refine List.map_congr_left fun m hm => ?_
  rw [euclid_eq_gcd]
  exact exactDiv_modulus (h m hm) ht hd

theorem pos_of_mem_divModuli {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) (t : Nat) :
    ∀ c ∈ divModuli moduli t, 0 < c := by
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
  rw [euclid_eq_gcd]
  exact Nat.div_pos (Nat.le_of_dvd (h m hm) (Nat.gcd_dvd_left m t))
    (Nat.gcd_pos_of_pos_left t (h m hm))

/-- Below the lcm, the quotient `x / t` is below the lcm of the moduli `m / gcd m t`, so its
residues determine it. -/
public theorem div_lt_divModuli {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {t x : Nat}
    (ht : 0 < t) (hd : t ∣ x) (hx : x < moduli.foldl Nat.lcm 1) :
    x / t < (divModuli moduli t).foldl Nat.lcm 1 := by
  have hL := foldl_lcm_pos (pos_of_mem_divModuli h t)
  have hW : moduli.foldl Nat.lcm 1 ∣ t * (divModuli moduli t).foldl Nat.lcm 1 := by
    rw [foldl_lcm_one_dvd_iff]
    intro m hm
    have hmem : m / euclid m t ∈ divModuli moduli t := List.mem_map.2 ⟨m, hm, rfl⟩
    refine Nat.dvd_trans ?_ (Nat.mul_dvd_mul_left t (dvd_foldl_lcm hmem))
    rw [euclid_eq_gcd]
    have := Nat.mul_dvd_mul_right (Nat.gcd_dvd_right m t) (m / Nat.gcd m t)
    rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left m t)] at this
  obtain ⟨q, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left q ht]
  have := Nat.le_of_dvd (Nat.mul_pos ht hL) hW
  exact Nat.lt_of_mul_lt_mul_left (a := t) (by omega)

/-- Below the lcm, `divModRes` gives the remainder `x % T` and the residues of the quotient
`x / T`. -/
public theorem divModRes_spec {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {x T : Nat}
    (hT : 0 < T) (hx : x < moduli.foldl Nat.lcm 1) :
    divModRes moduli (moduli.map (x % ·)) T = some (x % T, (divModuli moduli T).map ((x / T) % ·)) := by
  obtain ⟨ds, hds, -, -, hval⟩ := toMixedRadix_spec x moduli h
  rw [Nat.mod_eq_of_lt hx] at hval
  have hq : x - x % T = T * (x / T) := by have := Nat.div_add_mod x T; omega
  simp only [divModRes, hds, evalMod_eq, hval, map_resid]
  rw [subRes_spec_of_le h (Nat.mod_le x T), exactDivRes_spec h hT (Nat.dvd_sub_mod x), hq,
    Nat.mul_div_cancel_left _ hT]

/-- For `0 < x` below the lcm, the address `(k, i)` with respect to `T` has offset
`i = (x - 1) % T + 1` and block index `k = (x - 1) / T + 1`, so `x = T * (k - 1) + i`. -/
public theorem addressRes_spec {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {x T : Nat}
    (hT : 0 < T) (hx0 : 0 < x) (hx : x < moduli.foldl Nat.lcm 1) :
    addressRes moduli (moduli.map (x % ·)) T =
      some ((x - 1) % T + 1, (divModuli moduli T).map (((x - 1) / T + 1) % ·)) := by
  have hdm := Nat.div_add_mod x T
  have hrT := Nat.mod_lt x hT
  simp only [addressRes, divModRes_spec h hT hx]
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
  · rw [map_resid, addRes_spec]
    obtain ⟨hd, hm⟩ := (Nat.div_mod_unique hT).2
      (show x % T - 1 + T * (x / T) = x - 1 ∧ x % T - 1 < T by constructor <;> omega)
    rw [hd, hm, show x % T - 1 + 1 = x % T by omega]

theorem foldl_lcm_append_single (moduli : List Nat) (c : Nat) :
    (moduli ++ [c]).foldl Nat.lcm 1 = Nat.lcm (moduli.foldl Nat.lcm 1) c := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- When `p ^ v` is the highest power of a prime `p` dividing `W`, appending the modulus
`p ^ (v + 1)` multiplies `W` by exactly `p`. -/
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

/-- When `p ^ v` is the highest power of a prime `p` dividing the lcm of the moduli,
appending the moduli `p ^ (v + 1), ..., p ^ (v + j)` multiplies the lcm by `p ^ j`, one
factor `p` per modulus. -/
public theorem lcm_append_prime_powers (moduli : List Nat) {p v : Nat} (hp : p.Prime)
    (hv : p ^ v ∣ moduli.foldl Nat.lcm 1) (hv' : ¬ p ^ (v + 1) ∣ moduli.foldl Nat.lcm 1) :
    ∀ j, (moduli ++ (List.range j).map fun i => p ^ (v + 1 + i)).foldl Nat.lcm 1 =
      p ^ j * moduli.foldl Nat.lcm 1
  | 0 => by simp
  | j + 1 => by
    have hpj : 0 < p ^ j := Nat.pow_pos (n := j) hp.pos
    rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc,
      foldl_lcm_append_single, lcm_append_prime_powers moduli hp hv hv' j,
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
