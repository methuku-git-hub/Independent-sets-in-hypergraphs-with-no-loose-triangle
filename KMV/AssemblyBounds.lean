module
public import KMV.ColorParameters
public section
namespace KMV
open Filter Topology Finset
open scoped Classical

@[expose] noncomputable def initialDegree (B : ℕ) (x : ℝ) (j : ℕ) : ℝ :=
  if j=3 then (B : ℝ)*targetSize x else (B : ℝ)*x
@[expose] noncomputable def roundedDegree (B : ℕ) (x : ℝ) (j : ℕ) : ℕ :=
  Nat.ceil (initialDegree B x j)
@[expose] noncomputable def roundedPair (x : ℝ) (j : ℕ) : ℕ := Nat.ceil (pairThreshold x j)

theorem ceil_le_twice {x : ℝ} (hx : 1 ≤ x) : (Nat.ceil x : ℝ) ≤ 2*x := by
  have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  linarith

theorem rounded_degree_bound {B : ℕ} (hB : 0 < B) {x : ℝ}
    (hx : 1 ≤ x) (ht : 1 ≤ targetSize x) (j : ℕ) :
    (roundedDegree B x j : ℝ) ≤ degreeEnvelope B x j := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  unfold roundedDegree initialDegree degreeEnvelope
  by_cases hj : j=3
  · simp only [hj,ite_true]
    have hh := ceil_le_twice (one_le_mul_of_one_le_of_one_le hb ht)
    linarith
  · simp only [hj,ite_false]
    have hh := ceil_le_twice (one_le_mul_of_one_le_of_one_le hb hx)
    linarith

theorem final_degree_identity {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (B : ℕ) :
    finalDegree B x 3 = 128*initialDegree B x 3*(sampleP x)^2 ∧
    finalDegree B x 4 = 128*initialDegree B x 4*(sampleP x)^3 := by
  constructor <;>
    norm_num [finalDegree,initialDegree,targetSize,sampleP] <;>
    ring_nf <;>
    simp only [scale_pow hx,coeff_scale_mul hx,scale_coeff_mul hx,x_coeff_scale hx,coeff_x_scale hx] <;>
    norm_num

theorem trim_loss_bound {n : ℕ} {H : Hypergraph (Fin n)} {B : ℕ} (hB : 0 < B)
    (hx : 0 < (n : ℝ) ∧ 1 < Real.log (n : ℝ))
    (hdegree : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, (sizeDegree H j v : ℝ) ≤ initialDegree B n j) :
    3*(codegree H 3 ∅ : ℝ)*(sampleP n)^3/finalDegree B n 3 +
      4*(codegree H 4 ∅ : ℝ)*(sampleP n)^4/finalDegree B n 4 ≤ sampleP n*n/16 := by
  have hd₃ := edge_count_degree_bound (by norm_num : 1 ≤ 3) (hdegree 3 (by simp))
  have hd₄ := edge_count_degree_bound (by norm_num : 1 ≤ 4) (hdegree 4 (by simp))
  have hp : 0 < sampleP n := scale_pos hx _ _ _
  have hb : 0 < (B : ℝ) := by exact_mod_cast hB
  have ht : 0 < targetSize n := scale_pos hx _ _ _
  have h₃ : 0 < initialDegree B n 3 := by simp only [initialDegree,ite_true]; positivity
  have h₄ : 0 < initialDegree B n 4 := by norm_num [initialDegree]; exact mul_pos hb hx.1
  obtain ⟨hf₃,hf₄⟩ := final_degree_identity hx B
  rw [hf₃,hf₄]
  calc
    _ ≤ 3*((n : ℝ)*initialDegree B n 3)*(sampleP n)^3/(128*initialDegree B n 3*(sampleP n)^2) +
        4*((n : ℝ)*initialDegree B n 4)*(sampleP n)^4/(128*initialDegree B n 4*(sampleP n)^3) := by
      gcongr
    _ = 7*sampleP n*n/128 := by field_simp; ring
    _ ≤ _ := by have hn := hx.1; nlinarith

theorem target_color_identity {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (B : ℕ) :
    targetSize x * colorEnvelope B x = 12800*(B : ℝ)*sampleP x*x := by
  unfold targetSize colorEnvelope sampleP
  ring_nf
  simp only [coeff_scale_mul hx,scale_coeff_mul hx,x_coeff_scale hx,coeff_x_scale hx]
  norm_num
  rw [mul_assoc,scale_mul_x hx]
  norm_num

theorem degree_above_rank {n r j : ℕ} {H : Hypergraph (Fin n)} (hr : RankBounds H r)
    (hj : r < j) (v : Fin n) : sizeDegree H j v = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hcard,_⟩ := mem_filter.mp he
  have := (hr e he).2
  omega

theorem eventually_geometry (r B : ℕ) : ∀ᶠ x : ℝ in atTop,
    (0 < x ∧ 1 < Real.log x) ∧ 1 ≤ x ∧ 1 ≤ Real.log (Real.log x) ∧ 1 ≤ targetSize x ∧
    max 1 ((2*r : ℕ) : ℝ) ≤ pairThreshold x 3 ∧
    max 1 ((2*r*B : ℕ) : ℝ) ≤ pairThreshold x 4 := by
  have ht : Tendsto targetSize atTop atTop := scale_tendsto_atTop_first (by norm_num)
  have h₃ : Tendsto (fun x => pairThreshold x 3) atTop atTop := by
    simpa only [pairThreshold,ite_true] using scale_tendsto_atTop_first (b:= -1/2) (c:=0) (by norm_num : (0:ℝ)<1/3)
  have h₄ : Tendsto (fun x => pairThreshold x 4) atTop atTop := by
    simpa only [pairThreshold,show (4:ℕ) ≠ 3 by decide,ite_false] using
      scale_tendsto_atTop_first (b:= -1/2) (c:=0) (by norm_num : (0:ℝ)<2/3)
  exact eventually_scale_domain.and ((eventually_ge_atTop 1).and
    (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1).and
    ((ht.eventually_ge_atTop 1).and ((h₃.eventually_ge_atTop _).and (h₄.eventually_ge_atTop _)))))

end KMV
