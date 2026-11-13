module

public import Mathlib
public import Irreducibility.Drum

/-!
# T5: comparing on a drum without forming values

`digitsOf rings states` builds a drum position from ring states using relations, Euclid's
procedure and stepping around rings only. `compareOn` compares two such positions digit by
digit from the top.

* `digitsOf_spec`: for the states `n % m` of positive rings, `digitsOf` returns the
  mixed-radix digits of `n % lcm rings` on the levels `levels rings`.
* `compareTop_eq`: comparing digits from the top orders positions as their values.
* `compareOn_eq`: below the turn of the drum, `compareOn` decides `compare n n'`.

`value ds` is the number the drum position `ds` stands for, below the turn of its levels.
-/

namespace Irreducibility

public theorem value_append (ds : List (Nat × Nat)) (d r : Nat) :
    value (ds ++ [(d, r)]) = value ds + (ds.map Prod.snd).prod * d := by
  induction ds with
  | nil => simp [value]
  | cons p ds ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, value, ih, List.map_cons, List.prod_cons]
    ring

/-- Reading a position on ring `c` gives its value modulo `c`. -/
public theorem positionOn_eq (ds : List (Nat × Nat)) (c : Nat) :
    positionOn ds c = value ds % c := by
  induction ds with
  | nil => simp [positionOn, value]
  | cons p ds ih =>
    obtain ⟨d, r⟩ := p
    simp only [positionOn, value, ih, relation_eq_mod]
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem inverseAux_spec (step b : Nat) :
    ∀ fuel t pos, pos = t * step % b → (∃ x, t < x ∧ x ≤ t + fuel ∧ x * step % b = 1) →
      inverseAux step b fuel t pos * step % b = 1
  | 0, _, _, _, ⟨_, h1, h2, _⟩ => by omega
  | fuel + 1, t, pos, hpos, ⟨x, h1, h2, hx⟩ => by
    have hnext : (pos + step) % b = (t + 1) * step % b := by
      rw [hpos, Nat.mod_add_mod, Nat.add_mul, Nat.one_mul]
    simp only [inverseAux]
    split_ifs with h
    · rw [← hnext]; exact h
    · apply inverseAux_spec step b fuel (t + 1) _ hnext
      refine ⟨x, ?_, by omega, hx⟩
      rcases Nat.lt_or_ge (t + 1) x with h' | h'
      · exact h'
      · exfalso
        have hx1 : x = t + 1 := by omega
        rw [hnext, ← hx1] at h
        exact h hx

/-- Stepping `a` teeth at a time around ring `b` finds the inverse of `a` modulo `b`. -/
public theorem inverse_spec {a b : Nat} (hb : 1 < b) (h : Nat.Coprime a b) :
    a * inverse a b % b = 1 := by
  have hcop : Nat.Coprime (a % b) b := by
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact h
  obtain ⟨x, hxb, hx⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hb
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0] at hx; simp at hx
    · exact h0
  have hspec := inverseAux_spec (a % b) b b 0 0 (by simp)
    ⟨x, hx0, by omega, by rw [Nat.mul_comm]; exact hx⟩
  simp only [inverse, Nat.ne_of_gt hb, ↓reduceIte, relation_eq_mod]
  rw [← Nat.mod_mul_mod, Nat.mul_comm]; exact hspec

theorem digit_solve {L1 r q y1 inv k : Nat} (hr : 1 < r) (hq : q < r)
    (hy : y1 + r * k = L1 * q) (hinv : L1 % r * inv % r = 1) :
    y1 * inv % r = q := by
  have h1 : ((L1 : ZMod r)) * inv = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (L1 % r * inv) 1 r).2
      (by rw [hinv, Nat.mod_eq_of_lt hr])
    push_cast [ZMod.natCast_mod] at this
    exact this
  have h2 : ((y1 : ℕ) : ZMod r) = L1 * q := by
    have := congrArg (fun x : ℕ => (x : ZMod r)) hy
    push_cast [ZMod.natCast_self] at this
    simpa using this
  have h3 : ((y1 * inv : ℕ) : ZMod r) = ((q : ℕ) : ZMod r) := by
    push_cast
    rw [h2]
    linear_combination (q : ZMod r) * h1
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hq] at h3
  exact h3

/-- The arithmetic of one level: the drum below has turn `L`, ring `m` is added. -/
theorem digit_arith {n m L : Nat} (hm : 0 < m) (hL : 0 < L) :
    let g := Nat.gcd L m
    let r := m / g
    let q := n % (L * r) / L
    let y := (n % m + m - n % L % m) % m
    y % g = 0 ∧ q < r ∧ (r ≤ 1 → q = 0) ∧
      (1 < r → y / g * inverse (L % m / g % r) r % r = q) ∧ n % L + L * q = n % (L * r) := by
  intro g r q y
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hgm : g ∣ m := Nat.gcd_dvd_right L m
  have hgL : g ∣ L := Nat.gcd_dvd_left L m
  have hmr : m = g * r := (Nat.mul_div_cancel' hgm).symm
  have hr : 0 < r := Nat.div_pos (Nat.le_of_dvd hm hgm) hg
  obtain ⟨L1, hLL1⟩ := hgL
  have hlcm : L * r = Nat.lcm L m := by
    show L * (m / g) = L * m / Nat.gcd L m
    rw [Nat.mul_div_assoc _ hgm]
  have hw : n % (L * r) < L * r := Nat.mod_lt _ (Nat.mul_pos hL hr)
  have hq : q < r := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm r L]; exact hw)
  have hwL : n % (L * r) % L = n % L := Nat.mod_mod_of_dvd n (Dvd.intro r rfl)
  have hwdec : n % (L * r) = n % L + L * q := by
    have := Nat.mod_add_div (n % (L * r)) L
    rw [hwL] at this; exact this.symm
  have hwm : n % (L * r) % m = n % m := Nat.mod_mod_of_dvd n (hlcm ▸ Nat.dvd_lcm_right L m)
  have hylt : y < m := Nat.mod_lt _ hm
  have hya : (y + n % L) % m = n % m := by
    have h1 := Nat.mod_add_div (n % L) m
    have hlt : n % L % m < m := Nat.mod_lt _ hm
    have hnm : n % m < m := Nat.mod_lt _ hm
    calc (y + n % L) % m = ((n % m + m - n % L % m) + n % L) % m := Nat.mod_add_mod _ _ _
      _ = (n % m + m + m * (n % L / m)) % m := by congr 1; omega
      _ = n % m := by
        rw [Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hnm]
  have hqa : (L * q + n % L) % m = n % m := by rw [Nat.add_comm, ← hwdec, hwm]
  have hy : y = L * q % m := by
    have : y % m = L * q % m := Nat.ModEq.add_right_cancel' (n % L) (hya.trans hqa.symm)
    rwa [Nat.mod_eq_of_lt hylt] at this
  have hyg : g ∣ y := by
    rw [hy]
    exact (Nat.dvd_mod_iff hgm).2 (Dvd.dvd.mul_right ⟨L1, hLL1⟩ q)
  refine ⟨Nat.mod_eq_zero_of_dvd hyg, hq, fun h => Nat.lt_one_iff.1 (Nat.lt_of_lt_of_le hq h), fun h1r => ?_, hwdec.symm⟩
  · -- the digit equation divided by `g`
    obtain ⟨y1, hy1⟩ := hyg
    have hydiv : y / g = y1 := by rw [hy1, Nat.mul_div_cancel_left _ hg]
    have hk := Nat.mod_add_div (L * q) m
    rw [← hy] at hk
    have hyk : y1 + r * (L * q / m) = L1 * q := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc g * (y1 + r * (L * q / m)) = y + m * (L * q / m) := by rw [hy1, hmr]; ring
        _ = L * q := hk
        _ = g * (L1 * q) := by rw [hLL1]; ring
    have hgLm : g ∣ L % m := (Nat.dvd_mod_iff hgm).2 ⟨L1, hLL1⟩
    obtain ⟨t1, ht1⟩ := hgLm
    have htdiv : L % m / g = t1 := by rw [ht1, Nat.mul_div_cancel_left _ hg]
    have hj := Nat.mod_add_div L m
    have htj : t1 + r * (L / m) = L1 := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc g * (t1 + r * (L / m)) = L % m + m * (L / m) := by rw [ht1, hmr]; ring
        _ = L := hj
        _ = g * L1 := hLL1
    have hcopL : Nat.Coprime L1 r := by
      have := Nat.coprime_div_gcd_div_gcd (m := L) (n := m) hg
      have hL1 : L / Nat.gcd L m = L1 := by
        show L / g = L1
        rw [hLL1, Nat.mul_div_cancel_left _ hg]
      rw [hL1] at this; exact this
    have htr : t1 % r = L1 % r := by rw [← htj, Nat.add_mul_mod_self_left]
    have hcop : Nat.Coprime (t1 % r) r := by
      rw [htr, Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact hcopL
    have hinv := inverse_spec h1r hcop
    rw [htr] at hinv
    rw [hydiv, htdiv, htr]
    exact digit_solve h1r hq hyk hinv

/-- `n` fits the drum position `ds`: digits below their level sizes, and `ds` stands for `n`
modulo the turn of its levels. -/
@[expose] public def Fits (n : Nat) (ds : List (Nat × Nat)) : Prop :=
  (∀ p ∈ ds, p.1 < p.2) ∧ value ds = n % (ds.map Prod.snd).prod

theorem prod_pos_of_fits {ds : List (Nat × Nat)} (h : ∀ p ∈ ds, p.1 < p.2) :
    0 < (ds.map Prod.snd).prod :=
  List.prod_pos (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (h p hp))

theorem digitStep_spec {n m : Nat} {acc : List (Nat × Nat)} (hm : 0 < m) (hacc : Fits n acc) :
    ∃ d, digitStep acc m (n % m) = some (d, m / commonPartWithTurn (acc.map Prod.snd) m) ∧
      Fits n (acc ++ [(d, m / commonPartWithTurn (acc.map Prod.snd) m)]) := by
  obtain ⟨hlt, hval⟩ := hacc
  have hL := prod_pos_of_fits hlt
  obtain ⟨hyg, hq, hq0, hdig, hsum⟩ := digit_arith (n := n) hm hL
  refine ⟨n % ((acc.map Prod.snd).prod * (m / Nat.gcd (acc.map Prod.snd).prod m)) /
    (acc.map Prod.snd).prod, ?_, ?_, ?_⟩
  · simp only [digitStep, commonPartWithTurn_eq, positionOn_eq, turnOn_eq, hval]
    simp only [hyg, ↓reduceIte]
    split_ifs with h1r
    · rw [hdig h1r]
    · rw [hq0 (by omega)]
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hlt p hp
    · rw [List.mem_singleton] at hp
      rw [hp, commonPartWithTurn_eq]
      exact hq
  · rw [value_append, hval, commonPartWithTurn_eq]
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, Nat.mul_one]
    exact hsum

theorem digitsOfAux_spec (n : Nat) :
    ∀ (ms : List Nat) (acc : List (Nat × Nat)), (∀ x ∈ ms, 0 < x) → Fits n acc →
      ∃ ds, digitsOfAux acc ms (ms.map (n % ·)) = some ds ∧ Fits n ds ∧
        ds.map Prod.snd =
          ms.foldl (fun rs m => rs ++ [m / commonPartWithTurn rs m]) (acc.map Prod.snd)
  | [], acc, _, hacc => ⟨acc, by simp [digitsOfAux], hacc, by simp⟩
  | m :: ms, acc, hpos, hacc => by
    obtain ⟨d, hstep, hfits⟩ := digitStep_spec (hpos m (by simp)) hacc
    obtain ⟨ds, hds, hfds, hrad⟩ :=
      digitsOfAux_spec n ms _ (fun x hx => hpos x (by simp [hx])) hfits
    refine ⟨ds, ?_, hfds, ?_⟩
    · simp only [List.map_cons, digitsOfAux, hstep]
      exact hds
    · rw [hrad]
      simp

/-- For the states `n % m` of positive rings, `digitsOf` returns the mixed-radix digits of
`n` modulo the turn of the drum, on the levels `levels rings`. -/
public theorem digitsOf_spec (n : Nat) (rings : List Nat) (h : ∀ x ∈ rings, 0 < x) :
    ∃ ds, digitsOf rings (rings.map (n % ·)) = some ds ∧ ds.map Prod.snd = levels rings ∧
      (∀ p ∈ ds, p.1 < p.2) ∧ value ds = n % rings.foldl Nat.lcm 1 := by
  obtain ⟨ds, hds, ⟨hlt, hval⟩, hrad⟩ := digitsOfAux_spec n rings [] h ⟨by simp, by simp [value, Nat.mod_one]⟩
  refine ⟨ds, hds, hrad, hlt, ?_⟩
  rw [hval, hrad]
  simp only [List.map_nil]
  rw [show rings.foldl (fun rs m => rs ++ [m / commonPartWithTurn rs m]) [] = levels rings
    from rfl, prod_levels _ h]

/-- Comparing digits from the top orders drum positions with the same levels as their
values. -/
public theorem compareTop_eq :
    ∀ (ds es : List (Nat × Nat)), ds.map Prod.snd = es.map Prod.snd →
      (∀ p ∈ ds, p.1 < p.2) → (∀ p ∈ es, p.1 < p.2) →
        compareTop ds es = compare (value ds) (value es)
  | [], [], _, _, _ => by simp [compareTop, value]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | (a, r) :: ds, (b, r') :: es, h, hd, he => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hr, h⟩ := h
    subst hr
    have ha : a < r := hd (a, r) (by simp)
    have hb : b < r := he (b, r) (by simp)
    have ih := compareTop_eq ds es h (fun p hp => hd p (by simp [hp]))
      (fun p hp => he p (by simp [hp]))
    simp only [compareTop, value, ih]
    rcases Nat.lt_trichotomy (value ds) (value es) with hv | hv | hv
    · rw [Nat.compare_eq_lt.2 hv]
      refine (Nat.compare_eq_lt.2 ?_).symm
      nlinarith
    · rw [hv, Nat.compare_eq_eq.2 rfl]
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · rw [Nat.compare_eq_lt.2 hab, Nat.compare_eq_lt.2 (by omega)]
      · rw [hab, Nat.compare_eq_eq.2 rfl, Nat.compare_eq_eq.2 rfl]
      · rw [Nat.compare_eq_gt.2 hab, Nat.compare_eq_gt.2 (by omega)]
    · rw [Nat.compare_eq_gt.2 hv]
      refine (Nat.compare_eq_gt.2 ?_).symm
      nlinarith

/-- Below the turn of a drum of positive rings, comparing ring states digit by digit from
the top decides `compare n n'`. -/
public theorem compareOn_eq (rings : List Nat) (h : ∀ x ∈ rings, 0 < x) {n n' : Nat}
    (hn : n < rings.foldl Nat.lcm 1) (hn' : n' < rings.foldl Nat.lcm 1) :
    compareOn rings (rings.map (n % ·)) (rings.map (n' % ·)) = some (compare n n') := by
  obtain ⟨ds, hds, hrd, hld, hvd⟩ := digitsOf_spec n rings h
  obtain ⟨es, hes, hre, hle, hve⟩ := digitsOf_spec n' rings h
  rw [Nat.mod_eq_of_lt hn] at hvd
  rw [Nat.mod_eq_of_lt hn'] at hve
  simp only [compareOn, hds, hes]
  rw [compareTop_eq ds es (hrd.trans hre.symm) hld hle, hvd, hve]

end Irreducibility
