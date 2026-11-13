module

public import Mathlib
public import Irreducibility.Drum

/-!
# T4: consecutive rings

Take the rings `2, 3, ..., n - 1` in order and put ring `n` (`2 ≤ n`) on top. Its level has
size `p` when `n = p ^ k` is a prime power and size `1` otherwise. Hence:

* `irreducibleAfter_ringsBelow_iff`: ring `n` is irreducible exactly when `n` is prime;
* `log_levelSize_ringsBelow`: the logarithm of its level size is the von Mangoldt function
  `Λ n`.

The mechanism itself does not use primes. They appear only in the statements that describe
what it produces.
-/

namespace Irreducibility

public theorem mem_ringsBelow {n x : Nat} : x ∈ ringsBelow n ↔ 2 ≤ x ∧ x < n := by
  simp only [ringsBelow, List.mem_iff_getElem, List.length_drop, List.length_range,
    List.getElem_drop, List.getElem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - 2, by omega, by omega⟩

theorem dvd_foldl_lcm_init (l : List Nat) (a : Nat) : a ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => exact (Nat.dvd_lcm_left a x).trans (ih _)

theorem dvd_foldl_lcm_of_mem {l : List Nat} {x : Nat} (a : Nat) (hx : x ∈ l) :
    x ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hx with hx | hx
    · rw [hx]; exact (Nat.dvd_lcm_right a y).trans (dvd_foldl_lcm_init _ _)
    · exact ih _ hx

/-- A prime power that divides none of the rings does not divide their common turn. -/
theorem not_pow_dvd_foldl_lcm {p k : Nat} (hp : p.Prime) :
    ∀ (l : List Nat) (a : Nat), a ≠ 0 → ¬ p ^ k ∣ a → (∀ x ∈ l, x ≠ 0 ∧ ¬ p ^ k ∣ x) →
      ¬ p ^ k ∣ l.foldl Nat.lcm a
  | [], a, _, ha, _ => by simpa using ha
  | x :: l, a, ha0, ha, hl => by
    rw [List.foldl_cons]
    obtain ⟨hx0, hx⟩ := hl x (by simp)
    have hl0 : Nat.lcm a x ≠ 0 := Nat.lcm_ne_zero ha0 hx0
    apply not_pow_dvd_foldl_lcm hp l (Nat.lcm a x) hl0
    · rw [hp.pow_dvd_iff_le_factorization hl0, Nat.factorization_lcm ha0 hx0]
      rw [hp.pow_dvd_iff_le_factorization ha0] at ha
      rw [hp.pow_dvd_iff_le_factorization hx0] at hx
      simp only [Finsupp.sup_apply, le_sup_iff, not_or]
      exact ⟨ha, hx⟩
    · exact fun y hy => hl y (by simp [hy])

/-- Below `p ^ k` the rings share `p ^ (k - 1)` with ring `p ^ k`. -/
theorem gcd_turn_prime_pow {p k : Nat} (hp : p.Prime) (hk : 0 < k) :
    Nat.gcd ((ringsBelow (p ^ k)).foldl Nat.lcm 1) (p ^ k) = p ^ (k - 1) := by
  set L := (ringsBelow (p ^ k)).foldl Nat.lcm 1 with hL
  have hpk : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hone : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hlow : p ^ (k - 1) ∣ L := by
    rcases Nat.lt_or_ge 1 k with h | h
    · apply dvd_foldl_lcm_of_mem
      rw [mem_ringsBelow]
      refine ⟨?_, hpk⟩
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (k - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    · rw [show k - 1 = 0 by omega, pow_zero]; exact one_dvd _
  have hhigh : ¬ p ^ k ∣ L := by
    apply not_pow_dvd_foldl_lcm hp _ 1 one_ne_zero
    · intro h; have := Nat.le_of_dvd one_pos h; omega
    · intro x hx
      rw [mem_ringsBelow] at hx
      refine ⟨by omega, fun h => ?_⟩
      have := Nat.le_of_dvd (by omega) h; omega
  obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right L (p ^ k))
  have h1 : p ^ (k - 1) ∣ p ^ j := by
    rw [← hg]; exact Nat.dvd_gcd hlow (Nat.pow_dvd_pow p (by omega))
  have h2 : j ≠ k := by
    rintro rfl; apply hhigh; rw [← hg]; exact Nat.gcd_dvd_left L _
  rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h1
  rw [hg]; congr 1; omega

/-- When `n` is not a prime power, the rings below `n` carry all of ring `n`. -/
theorem gcd_turn_not_prime_pow {n : Nat} (hn : 2 ≤ n) (h : ¬ IsPrimePow n) :
    Nat.gcd ((ringsBelow n).foldl Nat.lcm 1) n = n := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  set p := n.minFac
  have hk : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
  set a := p ^ n.factorization p with ha_def
  have ha_dvd : a ∣ n := Nat.ordProj_dvd n p
  set b := n / a with hb_def
  have hab : a * b = n := Nat.mul_div_cancel' ha_dvd
  have hcop : Nat.Coprime a b := (Nat.coprime_ordCompl hp hn0).pow_left _
  have ha : 1 < a := Nat.one_lt_pow (by omega) hp.one_lt
  have hb : 1 < b := by
    rcases Nat.lt_or_ge 1 b with hb | hb
    · exact hb
    · exfalso; apply h
      have hb1 : b = 1 := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · rw [h0, Nat.mul_zero] at hab; omega
        · omega
      rw [isPrimePow_nat_iff]
      exact ⟨p, n.factorization p, hp, hk, by rw [← ha_def, ← hab, hb1, Nat.mul_one]⟩
  have han : a < n := by rw [← hab]; nlinarith
  have hbn : b < n := by rw [← hab]; nlinarith
  have haL := dvd_foldl_lcm_of_mem (l := ringsBelow n) 1 (mem_ringsBelow.2 ⟨by omega, han⟩)
  have hbL := dvd_foldl_lcm_of_mem (l := ringsBelow n) 1 (mem_ringsBelow.2 ⟨by omega, hbn⟩)
  apply Nat.gcd_eq_right
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop haL hbL
  rwa [hab] at this

/-- The level of ring `n` on top of the rings `2, ..., n - 1`: the prime `p` when
`n = p ^ k`, otherwise `1`. -/
public theorem levelSize_ringsBelow {n : Nat} (hn : 2 ≤ n) :
    levelSize (ringsBelow n) n = if IsPrimePow n then n.minFac else 1 := by
  rw [levelSize_eq _ _ (fun x hx => by have := mem_ringsBelow.1 hx; omega)]
  split_ifs with h
  · rw [isPrimePow_nat_iff] at h
    obtain ⟨p, k, hp, hk, rfl⟩ := h
    rw [gcd_turn_prime_pow hp hk, hp.pow_minFac hk.ne']
    have hsplit : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hsplit, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  · rw [gcd_turn_not_prime_pow hn h, Nat.div_self (by omega)]

/-- Ring `n` is irreducible after the rings `2, ..., n - 1` exactly when `n` is prime. -/
public theorem irreducibleAfter_ringsBelow_iff {n : Nat} (hn : 2 ≤ n) :
    IrreducibleAfter (ringsBelow n) n ↔ n.Prime := by
  rw [IrreducibleAfter, levelSize_ringsBelow hn]
  split_ifs with h
  · rw [Nat.prime_def_minFac]
    exact ⟨fun h1 => ⟨hn, h1⟩, fun h1 => h1.2⟩
  · constructor
    · intro h1; omega
    · intro hp; exact absurd hp.isPrimePow h

/-- The logarithm of the level size of ring `n` is the von Mangoldt function. -/
public theorem log_levelSize_ringsBelow {n : Nat} (hn : 2 ≤ n) :
    Real.log (levelSize (ringsBelow n) n) = ArithmeticFunction.vonMangoldt n := by
  rw [levelSize_ringsBelow hn, ArithmeticFunction.vonMangoldt_apply]
  split_ifs <;> simp

/-! ## Checks by evaluation (kernel `decide`) -/

example : levelSize (ringsBelow 8) 8 = 2 := by decide
example : levelSize (ringsBelow 9) 9 = 3 := by decide
example : levelSize (ringsBelow 12) 12 = 1 := by decide
example : levelSize (ringsBelow 13) 13 = 13 := by decide

end Irreducibility
