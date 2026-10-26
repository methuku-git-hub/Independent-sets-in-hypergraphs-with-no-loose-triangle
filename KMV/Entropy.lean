module
public import KMV.FiniteLaw
public section
namespace KMV

/-- The value at zero is p because Lean's real logarithm is total. -/
@[expose] noncomputable def entropy (p t : ℝ) : ℝ := t * Real.log (t/p) - t + p

theorem entropy_zero (p : ℝ) : entropy p 0 = p := by simp [entropy]

theorem entropy_self {p : ℝ} (hp : 0 < p) : entropy p p = 0 := by
  simp [entropy, hp.ne']

theorem entropy_nonneg {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) : 0 ≤ entropy p t := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa [entropy_zero] using hp.le
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hp ht)) ht.le
  simp only [Real.log_div hp.ne' ht.ne', mul_sub, mul_div_cancel₀ p ht.ne', mul_one] at h
  rw [entropy, Real.log_div ht.ne' hp.ne']
  nlinarith

theorem mean_weight_update {a b : ℝ} (ha : a < 1) :
    a * 0 + (1-a) * (b/(1-a)) = b := by
  simp only [mul_zero, zero_add]
  exact mul_div_cancel₀ b (by linarith)

theorem entropy_update {p a b : ℝ} (hp : 0 < p) (ha : a < 1) (hb : 0 ≤ b) :
    a * entropy p 0 + (1-a) * entropy p (b/(1-a)) - entropy p b =
      -b * Real.log (1-a) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [entropy]; ring
  have ha' : 1-a ≠ 0 := by linarith
  rw [entropy_zero]
  simp only [entropy]
  rw [Real.log_div (div_ne_zero hb.ne' ha') hp.ne', Real.log_div hb.ne' ha',
    Real.log_div hb.ne' hp.ne']
  field_simp
  <;> ring

theorem neg_log_one_sub_le {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    -Real.log (1-a) ≤ 2*a := by
  have hpos : 0 < 1-a := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hfrac : (1-a)⁻¹ ≤ 1+2*a := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith
  linarith

theorem entropy_update_le {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (ha' : a ≤ 1/2) (hb : 0 ≤ b) :
    a * entropy p 0 + (1-a) * entropy p (b/(1-a)) ≤ entropy p b + 2*a*b := by
  have he := entropy_update hp (by linarith : a < 1) hb
  have hm := mul_le_mul_of_nonneg_left (neg_log_one_sub_le ha ha') hb
  nlinarith

theorem entropy_freezing_bound {p β t : ℝ} (hp : 0 < p) (hβ : 0 < β)
    (ht : β ≤ t) : t * (Real.log (β/p) - 1) ≤ entropy p t := by
  have htp : 0 < t := hβ.trans_le ht
  have hl := Real.log_le_log (div_pos hβ hp) (div_le_div_of_nonneg_right ht hp.le)
  have hm := mul_le_mul_of_nonneg_left hl htp.le
  dsimp [entropy]
  nlinarith

end KMV
