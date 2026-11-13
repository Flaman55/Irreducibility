module

public import Mathlib
public import Irreducibility.SechComb

/-!
# T1w, ratio form: a pulse as a ratio of powers

With `x = exp s`, a pulse of the sech comb is a rational function of two powers of `x`:
`sech (s * (t - u)) = 2 X Y / (X ^ 2 + Y ^ 2)` for `X = x ^ t` and `Y = x ^ u`.

* `sech_sub_eq_sechRatio`: `sech (a - b) = sechRatio (exp a) (exp b)`.
* `sechRatio_le_one`, `sechRatio_eq_one_iff`: for positive `x, y`, `sechRatio x y ≤ 1`, with
  equality exactly when `x = y`; in particular `sechRatio (x ^ n) y = 1` exactly when
  `y = x ^ n`.
* `sechComb_log_eq`: the comb at scale `log x` is a sum of `sechRatio` of integer powers of `x`.
* `one_half_lt_sechComb_log_iff`: the scale condition `3 ≤ log x` is `exp 3 ≤ x`; from there on,
  `t` is a peak for `d` exactly when `d ∣ t`.
-/

namespace Irreducibility

/-- `2 x y / (x ^ 2 + y ^ 2)`. -/
@[expose] public noncomputable def sechRatio (x y : ℝ) : ℝ := 2 * x * y / (x ^ 2 + y ^ 2)

public theorem sech_sub_eq_sechRatio (a b : ℝ) :
    sech (a - b) = sechRatio (Real.exp a) (Real.exp b) := by
  have ha := Real.exp_pos a
  have hb := Real.exp_pos b
  rw [sech, Real.cosh_eq, sechRatio, neg_sub, Real.exp_sub, Real.exp_sub]
  field_simp

public theorem sech_mul_sub_eq_sechRatio (s t u : ℝ) :
    sech (s * (t - u)) = sechRatio (Real.exp (s * t)) (Real.exp (s * u)) := by
  rw [mul_sub, sech_sub_eq_sechRatio]

public theorem sechRatio_le_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : sechRatio x y ≤ 1 := by
  rw [sechRatio, div_le_one (by positivity)]
  nlinarith [sq_nonneg (x - y)]

public theorem sechRatio_eq_one_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    sechRatio x y = 1 ↔ x = y := by
  rw [sechRatio, div_eq_one_iff_eq (by positivity)]
  constructor
  · intro h
    nlinarith [sq_nonneg (x - y)]
  · rintro rfl
    ring

public theorem sechRatio_pow_eq_one_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    sechRatio (x ^ n) y = 1 ↔ y = x ^ n := by
  rw [sechRatio_eq_one_iff (pow_pos hx n) hy, eq_comm]

theorem exp_log_mul_int {x : ℝ} (hx : 0 < x) (k : ℤ) : Real.exp (Real.log x * k) = x ^ k := by
  rw [← Real.rpow_def_of_pos hx, Real.rpow_intCast]

/-- The comb at scale `log x` as a sum of `sechRatio` of integer powers of `x`. -/
public theorem sechComb_log_eq {x : ℝ} (hx : 0 < x) (d t : ℕ) :
    sechComb (Real.log x) d t =
      (([-1, 0, 1, 2] : List ℤ).map fun i =>
        sechRatio (x ^ (t : ℤ)) (x ^ ((d : ℤ) * ((t / d : ℕ) + i)))).sum := by
  simp only [sechComb, sech_mul_sub_eq_sechRatio]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  · rw [← exp_log_mul_int hx]
    norm_cast
  · rw [← exp_log_mul_int hx]
    push_cast
    ring_nf

public theorem three_le_log_iff {x : ℝ} (hx : 0 < x) : 3 ≤ Real.log x ↔ Real.exp 3 ≤ x :=
  Real.le_log_iff_exp_le hx

/-- From `x = exp 3` on, step `t` is a peak for modulus `d` at scale `log x` exactly when
`d ∣ t`. -/
public theorem one_half_lt_sechComb_log_iff {x : ℝ} (hx : Real.exp 3 ≤ x) {d : ℕ} (hd : 0 < d)
    (t : ℕ) : 1 / 2 < sechComb (Real.log x) d t ↔ d ∣ t :=
  one_half_lt_sechComb_iff ((three_le_log_iff ((Real.exp_pos 3).trans_le hx)).2 hx) hd t

end Irreducibility
