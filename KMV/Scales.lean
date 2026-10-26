module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public section
namespace KMV
open Filter Topology

/-- A bookkeeping device for the three asymptotic scales used below. -/
@[expose] noncomputable def scale (a b c x : ℝ) : ℝ :=
  x^a * (Real.log x)^b * (Real.log (Real.log x))^c

theorem scale_pos {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c : ℝ) : 0 < scale a b c x := by
  have hx0 : 0 < x := hx.1
  have hl : 0 < Real.log x := by linarith [hx.2]
  have hq : 0 < Real.log (Real.log x) := Real.log_pos hx.2
  unfold scale
  positivity

theorem scale_mul {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c d e f : ℝ) :
    scale a b c x * scale d e f x = scale (a+d) (b+e) (c+f) x := by
  have hx0 : 0 < x := hx.1
  have hl : 0 < Real.log x := by linarith [hx.2]
  have hq := Real.log_pos hx.2
  simp only [scale,Real.rpow_add hx0,Real.rpow_add hl,Real.rpow_add hq]
  ring

theorem scale_inv {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c : ℝ) :
    (scale a b c x)⁻¹ = scale (-a) (-b) (-c) x := by
  have hx0 : 0 < x := hx.1
  have hl : 0 ≤ Real.log x := by linarith [hx.2]
  have hq := (Real.log_pos hx.2).le
  simp only [scale,Real.rpow_neg hx0.le,Real.rpow_neg hl,Real.rpow_neg hq,mul_inv_rev]
  ring

theorem scale_div {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c d e f : ℝ) :
    scale a b c x / scale d e f x = scale (a-d) (b-e) (c-f) x := by
  rw [div_eq_mul_inv,scale_inv hx,scale_mul hx]
  rfl

theorem scale_pow {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c : ℝ) (k : ℕ) :
    (scale a b c x)^k = scale (a*k) (b*k) (c*k) x := by
  induction k with
  | zero => simp [scale]
  | succ k ih =>
    rw [pow_succ,ih,scale_mul hx]
    congr 1 <;> push_cast <;> ring

@[simp] theorem scale_zero (x : ℝ) : scale 0 0 0 x = 1 := by simp [scale]
@[simp] theorem scale_n (x : ℝ) : scale 1 0 0 x = x := by simp [scale]
@[simp] theorem scale_log (x : ℝ) : scale 0 1 0 x = Real.log x := by simp [scale]
@[simp] theorem scale_loglog (x : ℝ) : scale 0 0 1 x = Real.log (Real.log x) := by simp [scale]

theorem scale_tendsto_zero_first {a b c : ℝ} (ha : a < 0) :
    Tendsto (scale a b c) atTop (𝓝 0) := by
  have h₁ := (isLittleO_log_rpow_rpow_atTop (b+1) (neg_pos.mpr ha)).tendsto_div_nhds_zero
  have h₂ := ((isLittleO_log_rpow_rpow_atTop c (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero).comp
    Real.tendsto_log_atTop
  have hm := h₁.mul h₂
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx0 hxlog
  have hx := And.intro hx0 hxlog
  have hx0 : 0 < x := hx.1
  have hl : 0 < Real.log x := by linarith [hx.2]
  simp only [Function.comp_apply,Real.rpow_one,Real.rpow_neg hx0.le,
    div_inv_eq_mul,Real.rpow_add hl,scale]
  field_simp

theorem scale_tendsto_zero_second {b c : ℝ} (hb : b < 0) :
    Tendsto (scale 0 b c) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop c (neg_pos.mpr hb)).tendsto_div_nhds_zero).comp
    Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx0 hxlog
  have hx := And.intro hx0 hxlog
  have hl : 0 ≤ Real.log x := by linarith [hx.2]
  simp only [Function.comp_apply,Real.rpow_neg hl,div_inv_eq_mul,scale,Real.rpow_zero,one_mul,mul_comm]

theorem scale_tendsto_zero_third {c : ℝ} (hc : c < 0) :
    Tendsto (scale 0 0 c) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hc)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun x => by simp [scale,Function.comp_def])


theorem eventually_scale_domain : ∀ᶠ x : ℝ in atTop, 0 < x ∧ 1 < Real.log x :=
  (eventually_gt_atTop 0).and (Real.tendsto_log_atTop.eventually_gt_atTop 1)

theorem scale_rpow {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c k : ℝ) :
    (scale a b c x)^k = scale (a*k) (b*k) (c*k) x := by
  have hx0 := hx.1
  have hl : 0 ≤ Real.log x := by linarith [hx.2]
  have hq := (Real.log_pos hx.2).le
  simp only [scale,Real.mul_rpow (by positivity : 0 ≤ x^a * (Real.log x)^b)
    (Real.rpow_nonneg hq c),Real.mul_rpow (Real.rpow_nonneg hx.1.le a) (Real.rpow_nonneg hl b),
    ← Real.rpow_mul hx.1.le, ← Real.rpow_mul hl, ← Real.rpow_mul hq]

theorem log_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c : ℝ) :
    Real.log (scale a b c x) = a*Real.log x + b*Real.log (Real.log x) +
      c*Real.log (Real.log (Real.log x)) := by
  have hl : 0 < Real.log x := by linarith [hx.2]
  have hx0 := hx.1
  have hq := Real.log_pos hx.2
  unfold scale
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hx.1,Real.log_rpow hl,Real.log_rpow hq]

theorem scale_tendsto_atTop_first {a b c : ℝ} (ha : 0 < a) :
    Tendsto (scale a b c) atTop atTop := by
  have h := scale_tendsto_zero_first (b:= -b) (c:= -c) (neg_neg_of_pos ha)
  have hn : Tendsto (scale (-a) (-b) (-c)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h,eventually_scale_domain.mono (fun x hx => scale_pos hx _ _ _)⟩
  apply hn.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_scale_domain] with x hx
  simp only [Pi.inv_apply,scale_inv hx,neg_neg]

theorem scale_tendsto_atTop_second {b c : ℝ} (hb : 0 < b) :
    Tendsto (scale 0 b c) atTop atTop := by
  have h := scale_tendsto_zero_second (c:= -c) (neg_neg_of_pos hb)
  have hn : Tendsto (scale 0 (-b) (-c)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h,eventually_scale_domain.mono (fun x hx => scale_pos hx _ _ _)⟩
  apply hn.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_scale_domain] with x hx
  simp only [Pi.inv_apply,scale_inv hx,neg_neg,neg_zero]

end KMV
