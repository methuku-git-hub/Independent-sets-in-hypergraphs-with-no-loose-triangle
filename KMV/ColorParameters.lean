module
public import KMV.SamplingParameters
public section
namespace KMV
open Finset

theorem final_degree_log_bounds {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x)
    (hQ : 1 ≤ Real.log (Real.log x)) {B : ℕ} (hB : 0 < B) :
    ∀ j ∈ ({3,4} : Finset ℕ), 8 ≤ finalDegree B x j ∧
      Real.log (Real.log x)/100 ≤ Real.log (finalDegree B x j) := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hcoeff : 1 ≤ 128*(B : ℝ) := by linarith
  have hcoeffpos : 0 < 128*(B : ℝ) := by linarith
  have hlogcoeff := Real.log_nonneg hcoeff
  have hlogQ := Real.log_nonneg hQ
  have hQ0 : 0 ≤ Real.log (Real.log x) := by linarith
  have hscale₃ : 1 ≤ scale 0 (1/50) (1/3) x := by
    simp only [scale,Real.rpow_zero,one_mul]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx.2.le (by norm_num)) (Real.one_le_rpow hQ (by norm_num))
  have hscale₄ : 1 ≤ scale 0 (3/100) 0 x := by
    simpa only [scale,Real.rpow_zero,one_mul,mul_one] using Real.one_le_rpow hx.2.le (by norm_num : (0:ℝ)≤3/100)
  intro j hj
  simp only [mem_insert,mem_singleton] at hj
  rcases hj with rfl | rfl
  · norm_num only [finalDegree,ite_true]
    constructor
    · nlinarith
    · rw [Real.log_mul hcoeffpos.ne' (scale_pos hx _ _ _).ne',log_scale hx]
      nlinarith
  · norm_num only [finalDegree,show (4:ℕ) ≠ 3 by decide,ite_false]
    constructor
    · nlinarith
    · rw [Real.log_mul hcoeffpos.ne' (scale_pos hx _ _ _).ne',log_scale hx]
      nlinarith

theorem color_power_bound {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) {B : ℕ}
    (hB : 0 < B) {k : ℕ} (hk : 0 < k) :
    100*(128*(B : ℝ)*scale 0 ((k : ℝ)/100) (1-(k : ℝ)/3) x)/Real.log (Real.log x) ≤
      (colorEnvelope B x)^k := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hK : 1 ≤ 12800*(B : ℝ) := by linarith
  have hl : 100*(128*(B : ℝ)*scale 0 ((k : ℝ)/100) (1-(k : ℝ)/3) x)/Real.log (Real.log x) =
      12800*(B : ℝ)*scale 0 ((k : ℝ)/100) (-(k : ℝ)/3) x := by
    rw [← scale_loglog x]
    calc
      _ = 12800*(B : ℝ)*(scale 0 ((k : ℝ)/100) (1-(k : ℝ)/3) x / scale 0 0 1 x) := by ring
      _ = _ := by rw [scale_div hx]; congr 2 <;> ring
  have hr : (colorEnvelope B x)^k = (12800*(B : ℝ))^k *
      scale 0 ((k : ℝ)/100) (-(k : ℝ)/3) x := by
    rw [colorEnvelope,mul_pow,scale_pow hx]
    congr 2 <;> ring
  rw [hl,hr]
  exact mul_le_mul_of_nonneg_right (le_self_pow₀ hK (Nat.ne_of_gt hk)) (scale_pos hx _ _ _).le

theorem coloring_denominator_bound {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x)
    (hQ : 1 ≤ Real.log (Real.log x)) {B : ℕ} (hB : 0 < B) :
    max (Real.rpow (finalDegree B x 3/Real.log (finalDegree B x 3)) (1/2:ℝ))
      (Real.rpow (finalDegree B x 4/Real.log (finalDegree B x 4)) (1/3:ℝ)) ≤ colorEnvelope B x := by
  have hb : 0 < (B : ℝ) := by exact_mod_cast hB
  have hz : 0 < colorEnvelope B x := by
    unfold colorEnvelope
    exact mul_pos (by positivity) (scale_pos hx _ _ _)
  have hq : 0 < Real.log (Real.log x)/100 := by positivity
  have hlog := final_degree_log_bounds hx hQ hB
  have hratio : ∀ j ∈ ({3,4} : Finset ℕ), finalDegree B x j/Real.log (finalDegree B x j) ≤
      100*finalDegree B x j/Real.log (Real.log x) := by
    intro j hj
    have hd : 0 ≤ finalDegree B x j := by have := (hlog j hj).1; linarith
    calc
      _ ≤ finalDegree B x j/(Real.log (Real.log x)/100) :=
        div_le_div_of_nonneg_left hd hq (hlog j hj).2
      _ = _ := by ring
  have hs₃ : finalDegree B x 3/Real.log (finalDegree B x 3) ≤ (colorEnvelope B x)^2 :=
    (hratio 3 (by simp)).trans (by convert color_power_bound hx hB (k:=2) (by norm_num) using 1 <;> norm_num [finalDegree])
  have hs₄ : finalDegree B x 4/Real.log (finalDegree B x 4) ≤ (colorEnvelope B x)^3 :=
    (hratio 4 (by simp)).trans (by simpa [finalDegree] using color_power_bound hx hB (k:=3) (by norm_num))
  apply max_le
  · have hn : 0 ≤ finalDegree B x 3/Real.log (finalDegree B x 3) :=
      div_nonneg (by have := (hlog 3 (by simp)).1; linarith) (hq.le.trans (hlog 3 (by simp)).2)
    have hh := Real.rpow_le_rpow hn hs₃ (by norm_num : (0:ℝ)≤1/2)
    rw [← Real.rpow_natCast_mul hz.le] at hh
    norm_num at hh
    exact hh
  · have hn : 0 ≤ finalDegree B x 4/Real.log (finalDegree B x 4) :=
      div_nonneg (by have := (hlog 4 (by simp)).1; linarith) (hq.le.trans (hlog 4 (by simp)).2)
    have hh := Real.rpow_le_rpow hn hs₄ (by norm_num : (0:ℝ)≤1/3)
    rw [← Real.rpow_natCast_mul hz.le] at hh
    norm_num at hh
    exact hh

end KMV
