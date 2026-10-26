module
public import KMV.Parameters
public section
namespace KMV
open Filter Topology Finset

theorem inv_log_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) :
    (Real.log x)⁻¹ = scale 0 (-1) 0 x := by
  simpa only [scale_log,neg_zero] using scale_inv hx 0 1 0

@[expose] noncomputable def entropyRatio (B : ℕ) (x : ℝ) :=
  40*(B : ℝ)*scale 0 (-49/100) (1/3) x + scale 0 (-1) 0 x +
    (1/100)*scale 0 (-1) 1 x

theorem entropy_ratio_identity {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (B : ℕ) :
    (4*graphDegreeEnvelope B x*sampleP x + 1 + Real.log (Real.log x)/100)/Real.log x =
      entropyRatio B x := by
  unfold graphDegreeEnvelope sampleP entropyRatio
  rw [← scale_loglog x]
  simp only [div_eq_mul_inv,inv_log_scale hx]
  ring_nf
  simp only [coeff_scale_mul hx,scale_mul hx]
  norm_num
  <;> ring

theorem log_cap_ratio {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) :
    Real.log (sampleCap x/sampleP x) = Real.log x/30 - Real.log (Real.log x)/100 := by
  rw [sampleCap,sampleP,scale_div hx,log_scale hx]
  ring

theorem entropyRatio_tendsto (B : ℕ) : Tendsto (entropyRatio B) atTop (𝓝 0) := by
  have h₁ := const_scale_zero_second (40*(B : ℝ)) (c:=1/3) (by norm_num : (-49/100:ℝ)<0)
  have h₂ := scale_tendsto_zero_second (c:=0) (by norm_num : (-1:ℝ)<0)
  have h₃ := const_scale_zero_second (1/100) (c:=1) (by norm_num : (-1:ℝ)<0)
  unfold entropyRatio
  simpa only [zero_add] using (h₁.add h₂).add h₃

theorem eventually_sampling_parameters (B : ℕ) : ∀ᶠ x : ℝ in atTop,
    0 < sampleP x ∧ sampleP x < sampleCap x ∧ sampleCap x ≤ 1/2 ∧
    1 < Real.log (sampleCap x/sampleP x) ∧
    2*graphDegreeEnvelope B x*(sampleP x)^2/(Real.log (sampleCap x/sampleP x)-1) ≤ sampleP x/2 := by
  have hβ : Tendsto sampleCap atTop (𝓝 0) := scale_tendsto_zero_first (by norm_num)
  have hratio : Tendsto (fun x => sampleP x/sampleCap x) atTop (𝓝 0) := by
    apply (scale_tendsto_zero_first (b:=1/100) (c:=0) (by norm_num : (-1/30:ℝ)<0)).congr'
    filter_upwards [eventually_scale_domain] with x hx
    simp only [sampleP,sampleCap,scale_div hx]
    norm_num
  filter_upwards [eventually_scale_domain,
    hβ.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    hratio.eventually_lt_const (by norm_num : (0:ℝ)<1),
    (entropyRatio_tendsto B).eventually_lt_const (by norm_num : (0:ℝ)<1/30)] with x hx hb hpb he
  have hp : 0 < sampleP x := scale_pos hx _ _ _
  have hbp : 0 < sampleCap x := scale_pos hx _ _ _
  have hpβ : sampleP x < sampleCap x := by
    have := (div_lt_iff₀ hbp).mp hpb
    simpa only [one_mul] using this
  have hlp : 0 < Real.log x := by linarith [hx.2]
  rw [← entropy_ratio_identity hx B] at he
  have he' := (div_lt_iff₀ hlp).mp he
  have hlog := log_cap_ratio hx
  have hstrong : 4*graphDegreeEnvelope B x*sampleP x + 1 < Real.log (sampleCap x/sampleP x) := by
    linarith
  have hA : 0 ≤ graphDegreeEnvelope B x := by
    have hs := (scale_pos hx (1/3) (1/2) (1/3)).le
    unfold graphDegreeEnvelope
    positivity
  have hl : 1 < Real.log (sampleCap x/sampleP x) := by nlinarith
  refine ⟨hp,hpβ,hb.le,hl,?_⟩
  apply (div_le_iff₀ (by linarith : 0 < Real.log (sampleCap x/sampleP x)-1)).mpr
  have hm := mul_le_mul_of_nonneg_right hstrong.le hp.le
  nlinarith

theorem graph_degree_envelope {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x)
    (hQ : 1 ≤ Real.log (Real.log x)) (B : ℕ) :
    2*degreeEnvelope B x 3/pairThreshold x 3 +
      3*degreeEnvelope B x 4/pairThreshold x 4 ≤ graphDegreeEnvelope B x := by
  have hx0 := hx.1
  have hl : 0 ≤ Real.log x := by linarith [hx.2]
  have hs : scale (1/3) (1/2) 0 x ≤ scale (1/3) (1/2) (1/3) x := by
    have hqpow : 1 ≤ (Real.log (Real.log x))^(1/3:ℝ) := Real.one_le_rpow hQ (by norm_num)
    unfold scale
    rw [Real.rpow_zero,mul_one]
    exact le_mul_of_one_le_right (by positivity) hqpow
  have he : 2*degreeEnvelope B x 3/pairThreshold x 3 +
      3*degreeEnvelope B x 4/pairThreshold x 4 =
      4*(B : ℝ)*scale (1/3) (1/2) (1/3) x + 6*(B : ℝ)*scale (1/3) (1/2) 0 x := by
    norm_num [degreeEnvelope,pairThreshold,targetSize]
    simp only [div_eq_mul_inv,scale_inv hx]
    ring_nf
    simp only [coeff_scale_mul hx,scale_coeff_mul hx,x_coeff_scale hx,coeff_x_scale hx,scale_mul hx]
    norm_num
  unfold graphDegreeEnvelope
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 6*(B : ℝ))
  rw [he]
  nlinarith

end KMV
