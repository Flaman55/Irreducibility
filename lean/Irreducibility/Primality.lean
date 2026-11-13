module

public import Mathlib
public import Irreducibility.Blocks

/-!
# T6: primality on residues without assembling the number

`isPrimeRes fuel moduli residues` tries divisors `m = 2, 3, ...` against a number given by its
residues. It compares `m` and `m * m` with the number by `compareRes`, from their residues,
and computes the residue of the number modulo `m` from its mixed-radix representation.

* `isPrimeRes_sound`: whenever `isPrimeRes` answers, the answer is `Nat.Prime n`.
* `isPrimeRes_eq`: it answers once the fuel exceeds `n`, or exceeds `Nat.sqrt n` when
  `(Nat.sqrt n + 1) ^ 2` is below the lcm of the moduli.
-/

namespace Irreducibility

/-- Comparing residues `x % c` with residues `n % c`, for `n` below the lcm `W`, compares
`x % W` with `n`. -/
theorem compareRes_mod (moduli : List Nat) (h : ∀ x ∈ moduli, 0 < x) (x : Nat) {n : Nat}
    (hn : n < moduli.foldl Nat.lcm 1) :
    compareRes moduli (moduli.map (x % ·)) (moduli.map (n % ·)) =
      some (compare (x % moduli.foldl Nat.lcm 1) n) := by
  have hx : moduli.map (x % ·) = moduli.map (x % moduli.foldl Nat.lcm 1 % ·) :=
    List.map_congr_left fun c hc => (Nat.mod_mod_of_dvd x (dvd_foldl_lcm hc)).symm
  rw [hx]
  exact compareRes_eq moduli h (Nat.mod_lt _ (foldl_lcm_pos h)) hn

theorem residues_resid (moduli : List Nat) (m : Nat) :
    moduli.map (resid m) = moduli.map (m % ·) :=
  List.map_congr_left fun c _ => resid_eq_mod m c

theorem residues_resid_sq (moduli : List Nat) (m : Nat) :
    moduli.map (fun c => resid m c * resid m c % c) = moduli.map (m * m % ·) :=
  List.map_congr_left fun c _ => by rw [resid_eq_mod, ← Nat.mul_mod]

/-- A number at least `2` with no divisor in `[2, m)` and below `m * m` is prime. -/
theorem prime_of_no_divisor_below {n m : Nat} (hn : 2 ≤ n) (hm : n < m * m)
    (hd : ∀ k, 2 ≤ k → k < m → ¬ k ∣ n) : n.Prime := by
  by_contra hp
  have h1 : n ≠ 1 := by omega
  have hmin := Nat.minFac_sq_le_self (by omega) hp
  have h2 : 2 ≤ n.minFac := (Nat.minFac_prime h1).two_le
  have hlt : n.minFac < m := by
    by_contra hge
    have := Nat.mul_le_mul (not_lt.1 hge) (not_lt.1 hge)
    rw [sq] at hmin
    omega
  exact hd _ h2 hlt (Nat.minFac_dvd n)

section

variable {moduli : List Nat} {n : Nat} {ds : List (Nat × Nat)}

/-- Every answer of `isPrimeResAux` from a divisor `m` with no divisor of `n` in `[2, m)` is
`Nat.Prime n`. -/
theorem isPrimeResAux_sound (h : ∀ x ∈ moduli, 0 < x) (hn : n < moduli.foldl Nat.lcm 1)
    (h2 : 2 < moduli.foldl Nat.lcm 1) (hds : ∀ c, evalMod ds c = n % c) :
    ∀ fuel m b, 2 ≤ m → (m ≤ n ∨ m = 2) → (∀ k, 2 ≤ k → k < m → ¬ k ∣ n) →
      isPrimeResAux moduli (moduli.map (n % ·)) ds fuel m = some b → b = decide n.Prime
  | 0, _, _, _, _, _, hb => by simp [isPrimeResAux] at hb
  | fuel + 1, m, b, hm2, hmn, hd, hb => by
    have hmL : m < moduli.foldl Nat.lcm 1 := by omega
    have c1 := compareRes_mod moduli h m hn
    rw [Nat.mod_eq_of_lt hmL] at c1
    have c2 := compareRes_mod moduli h (m * m) hn
    simp only [isPrimeResAux, residues_resid, residues_resid_sq, c1, c2, hds] at hb
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.2 hlt] at hb
      simp only at hb
      by_cases hsq : compare (m * m % moduli.foldl Nat.lcm 1) n = .gt
      · rw [hsq] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        have hgt : n < m * m := lt_of_lt_of_le (Nat.compare_eq_gt.1 hsq) (Nat.mod_le _ _)
        exact (decide_eq_true (prime_of_no_divisor_below (by omega) hgt hd)).symm
      · have hb' : (if n % m = 0 then some false
            else isPrimeResAux moduli (moduli.map (n % ·)) ds fuel (m + 1)) = some b := by
          rcases hc : compare (m * m % moduli.foldl Nat.lcm 1) n with _ | _ | _
          · rw [hc] at hb; exact hb
          · rw [hc] at hb; exact hb
          · exact absurd hc hsq
        split_ifs at hb' with hz
        · simp only [Option.some.injEq] at hb'
          subst hb'
          refine (decide_eq_false fun hp => ?_).symm
          rcases hp.eq_one_or_self_of_dvd m (Nat.dvd_of_mod_eq_zero hz) with h' | h' <;> omega
        · refine isPrimeResAux_sound h hn h2 hds fuel (m + 1) b (by omega) (by omega) ?_ hb'
          intro k hk2 hkm
          rcases Nat.lt_or_ge k m with hk | hk
          · exact hd k hk2 hk
          · have : k = m := by omega
            rw [this]
            exact fun hdvd => hz (Nat.mod_eq_zero_of_dvd hdvd)
    · rw [heq, Nat.compare_eq_eq.2 rfl] at hb
      simp only [Option.some.injEq] at hb
      subst hb heq
      exact (decide_eq_true (Nat.prime_def_lt'.2 ⟨hm2, hd⟩)).symm
    · rw [Nat.compare_eq_gt.2 hgt] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      refine (decide_eq_false fun hp => ?_).symm
      have := hp.two_le
      omega

/-- `isPrimeResAux` answers once it reaches a divisor `s` that is `n` itself, or whose square
exceeds `n` while staying below the lcm of the moduli. -/
theorem isPrimeResAux_isSome (h : ∀ x ∈ moduli, 0 < x) (hn : n < moduli.foldl Nat.lcm 1)
    (hds : ∀ c, evalMod ds c = n % c) :
    ∀ fuel m, 2 ≤ m → m ≤ n →
      (∃ s, m ≤ s ∧ s < m + fuel ∧ (s = n ∨ (n < s * s ∧ s * s < moduli.foldl Nat.lcm 1))) →
        (isPrimeResAux moduli (moduli.map (n % ·)) ds fuel m).isSome
  | 0, _, _, _, ⟨s, h1, h2, _⟩ => by omega
  | fuel + 1, m, hm2, hmn, ⟨s, hs1, hs2, hs⟩ => by
    have hmL : m < moduli.foldl Nat.lcm 1 := by omega
    have c1 := compareRes_mod moduli h m hn
    rw [Nat.mod_eq_of_lt hmL] at c1
    have c2 := compareRes_mod moduli h (m * m) hn
    simp only [isPrimeResAux, residues_resid, residues_resid_sq, c1, c2, hds]
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [Nat.compare_eq_lt.2 hlt]
      simp only
      by_cases hsq : compare (m * m % moduli.foldl Nat.lcm 1) n = .gt
      · rw [hsq]; rfl
      · have hsm : m < s := by
          rcases Nat.lt_or_ge m s with h' | h'
          · exact h'
          · exfalso
            have hms : m = s := by omega
            subst hms
            rcases hs with hs | ⟨hs1, hs2⟩
            · omega
            · exact hsq (Nat.compare_eq_gt.2 (by rw [Nat.mod_eq_of_lt hs2]; exact hs1))
        have ih := isPrimeResAux_isSome h hn hds fuel (m + 1) (by omega) (by omega)
          ⟨s, by omega, by omega, hs⟩
        revert hsq
        cases compare (m * m % moduli.foldl Nat.lcm 1) n <;> intro hsq <;>
          simp only [reduceCtorEq, not_true_eq_false] at hsq ⊢ <;> split_ifs <;> simp_all
    · rw [show m = n by omega, Nat.compare_eq_eq.2 rfl]; rfl

end

/-- Whenever `isPrimeRes` answers on the residues `n % c` of positive moduli, with `n` and
`2` below their lcm, the answer is whether `n` is prime. -/
public theorem isPrimeRes_sound {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {n : Nat}
    (hn : n < moduli.foldl Nat.lcm 1) (h2 : 2 < moduli.foldl Nat.lcm 1) {fuel : Nat} {b : Bool}
    (hb : isPrimeRes fuel moduli (moduli.map (n % ·)) = some b) : b = decide n.Prime := by
  obtain ⟨ds, hds, _, _, hval⟩ := toMixedRadix_spec n moduli h
  rw [Nat.mod_eq_of_lt hn] at hval
  have hpos : ∀ c, evalMod ds c = n % c := fun c => by rw [evalMod_eq, hval]
  simp only [isPrimeRes, hds] at hb
  exact isPrimeResAux_sound h hn h2 hpos fuel 2 b le_rfl (Or.inr rfl)
    (fun k hk hk2 => absurd hk2 (by omega)) hb

/-- On the residues `n % c` of positive moduli, with `n` and `2` below their lcm, `isPrimeRes`
decides whether `n` is prime once the fuel exceeds `n`, or exceeds `Nat.sqrt n` when
`(Nat.sqrt n + 1) ^ 2` is below the lcm. -/
public theorem isPrimeRes_eq {moduli : List Nat} (h : ∀ x ∈ moduli, 0 < x) {n : Nat}
    (hn : n < moduli.foldl Nat.lcm 1) (h2 : 2 < moduli.foldl Nat.lcm 1) {fuel : Nat}
    (hfuel : n < fuel ∨ (Nat.sqrt n < fuel ∧
      (Nat.sqrt n + 1) * (Nat.sqrt n + 1) < moduli.foldl Nat.lcm 1)) :
    isPrimeRes fuel moduli (moduli.map (n % ·)) = some (decide n.Prime) := by
  obtain ⟨ds, hds, _, _, hval⟩ := toMixedRadix_spec n moduli h
  rw [Nat.mod_eq_of_lt hn] at hval
  have hpos : ∀ c, evalMod ds c = n % c := fun c => by rw [evalMod_eq, hval]
  have hsome : (isPrimeRes fuel moduli (moduli.map (n % ·))).isSome := by
    simp only [isPrimeRes, hds]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        rcases hfuel with hf | ⟨hf, _⟩ <;> omega⟩
      have c1 := compareRes_mod moduli h 2 hn
      rw [Nat.mod_eq_of_lt h2] at c1
      simp only [isPrimeResAux, residues_resid, c1, Nat.compare_eq_gt.2 hn2]
      rfl
    · apply isPrimeResAux_isSome h hn hpos fuel 2 le_rfl hn2
      rcases hfuel with hf | ⟨hf, hL⟩
      · exact ⟨n, hn2, by omega, Or.inl rfl⟩
      · have hs : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.2 (by omega)
        exact ⟨Nat.sqrt n + 1, by omega, by omega, Or.inr ⟨Nat.lt_succ_sqrt n, hL⟩⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
  rw [hb, isPrimeRes_sound h hn h2 hb]

end Irreducibility
