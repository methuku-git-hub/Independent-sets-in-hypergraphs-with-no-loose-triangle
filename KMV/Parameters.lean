module
public import KMV.LossEnvelope
public section
namespace KMV
open Filter Topology Finset
open scoped Classical

@[expose] noncomputable def sampleP (x : ℝ) := scale (-1/3) (1/100) 0 x
@[expose] noncomputable def sampleCap (x : ℝ) := scale (-3/10) 0 0 x
@[expose] noncomputable def targetSize (x : ℝ) := scale (2/3) 0 (1/3) x
@[expose] noncomputable def pairThreshold (x : ℝ) (j : ℕ) :=
  if j=3 then scale (1/3) (-1/2) 0 x else scale (2/3) (-1/2) 0 x
@[expose] noncomputable def degreeEnvelope (B : ℕ) (x : ℝ) (j : ℕ) :=
  if j=3 then 2*(B : ℝ)*targetSize x else 2*(B : ℝ)*x
@[expose] noncomputable def pairEnvelope (x : ℝ) (j : ℕ) := 2*pairThreshold x j
@[expose] noncomputable def graphDegreeEnvelope (B : ℕ) (x : ℝ) :=
  10*(B : ℝ)*scale (1/3) (1/2) (1/3) x
@[expose] noncomputable def finalDegree (B : ℕ) (x : ℝ) (j : ℕ) :=
  if j=3 then 128*(B : ℝ)*scale 0 (1/50) (1/3) x else 128*(B : ℝ)*scale 0 (3/100) 0 x
@[expose] noncomputable def colorEnvelope (B : ℕ) (x : ℝ) :=
  12800*(B : ℝ)*scale 0 (1/100) (-1/3) x

theorem scale_mul_x {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c : ℝ) :
    scale a b c x*x = scale (a+1) b c x := by
  simpa only [scale_n,add_zero] using scale_mul hx a b c 1 0 0

theorem x_mul_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (a b c : ℝ) :
    x*scale a b c x = scale (1+a) b c x := by
  simpa only [scale_n,zero_add] using scale_mul hx 1 0 0 a b c

theorem inv_x_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) :
    x⁻¹ = scale (-1) 0 0 x := by
  simpa only [scale_n,neg_zero] using scale_inv hx 1 0 0

theorem coeff_scale_mul {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x)
    (C a b c d e f : ℝ) :
    (C*scale a b c x)*scale d e f x = C*scale (a+d) (b+e) (c+f) x := by
  rw [mul_assoc,scale_mul hx]

theorem scale_coeff_mul {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x)
    (C a b c d e f : ℝ) :
    (scale a b c x*C)*scale d e f x = C*scale (a+d) (b+e) (c+f) x := by
  rw [mul_comm (scale a b c x) C,coeff_scale_mul hx]

theorem x_coeff_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (C a b c : ℝ) :
    x*C*scale a b c x = C*scale (1+a) b c x := by
  rw [mul_comm x C,mul_assoc,x_mul_scale hx]

theorem coeff_x_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (C a b c : ℝ) :
    C*x*scale a b c x = C*scale (1+a) b c x := by
  rw [mul_assoc,x_mul_scale hx]

theorem first_loss_identity {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (B : ℕ) :
    3*x*degreeEnvelope B x 3*pairEnvelope x 3*(sampleP x)^4 / (sampleP x*x) =
      12*(B : ℝ)*scale 0 (-47/100) (1/3) x := by
  simp only [degreeEnvelope,pairEnvelope,pairThreshold,targetSize,sampleP,ite_true]
  simp only [div_eq_mul_inv,mul_inv_rev,scale_inv hx,inv_x_scale hx]
  ring_nf
  simp only [scale_pow hx,coeff_scale_mul hx,x_coeff_scale hx]
  norm_num

theorem x_pow_scale {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (k : ℕ) :
    x^k = scale (k : ℝ) 0 0 x := by
  simpa only [scale_n,one_mul,zero_mul] using scale_pow hx 1 0 0 k

@[expose] noncomputable def normalizedLoss (r B : ℕ) (x : ℝ) : ℝ :=
  12*(B : ℝ)*scale 0 (-47/100) (1/3) x +
  12*(B : ℝ)*scale 0 (-46/100) (1/3) x +
  24*(B : ℝ)*scale 0 (-46/100) 0 x +
  24*(B : ℝ)*scale 0 (-45/100) 0 x +
  8*(B : ℝ)^2*scale (-1/6) (-1/100) 0 x +
  1024*(B : ℝ)^3*scale (-2/15) (-1/100) (2/3) x +
  2048*(B : ℝ)^3*scale (-1/10) (-1/100) (1/3) x +
  1024*(B : ℝ)^3*scale (-1/15) (-1/100) 0 x +
  4096*(B : ℝ)^2*scale (-2/15) (-51/100) (1/3) x +
  4096*(B : ℝ)^2*scale (-1/10) (-51/100) 0 x +
  ∑ j ∈ Finset.Icc 5 r, (((2*r)^(j-2) : ℕ) : ℝ)*
    scale (4/3-(j : ℝ)/3) ((j : ℝ)/100-1/100) 0 x

theorem high_loss_identity {x : ℝ} (hx : 0 < x ∧ 1 < Real.log x) (r j : ℕ) :
    x^2*((2*r)^(j-2) : ℕ)*(sampleP x)^j/(sampleP x*x) =
      (((2*r)^(j-2) : ℕ) : ℝ)*scale (4/3-(j : ℝ)/3) ((j : ℝ)/100-1/100) 0 x := by
  simp only [sampleP,div_eq_mul_inv,mul_inv_rev,scale_inv hx,inv_x_scale hx]
  ring_nf
  simp only [scale_pow hx,x_pow_scale hx,coeff_scale_mul hx,scale_coeff_mul hx,scale_mul hx,x_coeff_scale hx,
    x_mul_scale hx,scale_mul_x hx]
  congr 2 <;> ring

theorem loss_envelope_identity {n : ℕ} (hx : 0 < (n : ℝ) ∧ 1 < Real.log (n : ℝ)) (r B : ℕ) :
    lossEnvelope n r (degreeEnvelope B n) (pairEnvelope n) B (sampleP n) (sampleCap n) /
      (sampleP n*n) = normalizedLoss r B n := by
  have hh : (∑ j ∈ Finset.Icc 5 r, (n : ℝ)^2*((2*r)^(j-2) : ℕ)*(sampleP n)^j) /
      (sampleP n*n) = ∑ j ∈ Finset.Icc 5 r, (((2*r)^(j-2) : ℕ) : ℝ)*
        scale (4/3-(j : ℝ)/3) ((j : ℝ)/100-1/100) 0 n := by
    rw [show (∑ j ∈ Finset.Icc 5 r, (n : ℝ)^2*((2*r)^(j-2) : ℕ)*(sampleP n)^j) /
        (sampleP n*n) = ∑ j ∈ Finset.Icc 5 r, (n : ℝ)^2*((2*r)^(j-2) : ℕ)*(sampleP n)^j /
        (sampleP n*n) by simp only [div_eq_mul_inv,Finset.sum_mul]]
    exact Finset.sum_congr rfl (fun j _ => high_loss_identity hx r j)
  unfold lossEnvelope normalizedLoss
  rw [add_div,hh]
  congr 1
  norm_num [degreeEnvelope,pairEnvelope,pairThreshold,targetSize,sampleP,sampleCap,
    Finset.sum_insert,Finset.sum_singleton,Nat.choose]
  simp only [div_eq_mul_inv,mul_inv_rev,scale_inv hx,inv_x_scale hx]
  ring_nf
  simp only [scale_pow hx,x_pow_scale hx,coeff_scale_mul hx,scale_coeff_mul hx,scale_mul hx,x_coeff_scale hx,
    x_mul_scale hx,scale_mul_x hx]
  norm_num
  norm_num
  <;> ring

theorem const_scale_zero_first (C : ℝ) {a b c : ℝ} (ha : a < 0) :
    Tendsto (fun x => C*scale a b c x) atTop (𝓝 0) := by
  simpa only [mul_zero] using (scale_tendsto_zero_first (b:=b) (c:=c) ha).const_mul C

theorem const_scale_zero_second (C : ℝ) {b c : ℝ} (hb : b < 0) :
    Tendsto (fun x => C*scale 0 b c x) atTop (𝓝 0) := by
  simpa only [mul_zero] using (scale_tendsto_zero_second (c:=c) hb).const_mul C

theorem normalizedLoss_tendsto (r B : ℕ) : Tendsto (normalizedLoss r B) atTop (𝓝 0) := by
  have h₁ := const_scale_zero_second (12*(B : ℝ)) (c:=1/3) (by norm_num : (-47/100:ℝ)<0)
  have h₂ := const_scale_zero_second (12*(B : ℝ)) (c:=1/3) (by norm_num : (-46/100:ℝ)<0)
  have h₃ := const_scale_zero_second (24*(B : ℝ)) (c:=0) (by norm_num : (-46/100:ℝ)<0)
  have h₄ := const_scale_zero_second (24*(B : ℝ)) (c:=0) (by norm_num : (-45/100:ℝ)<0)
  have h₅ := const_scale_zero_first (8*(B : ℝ)^2) (b:= -1/100) (c:=0) (by norm_num : (-1/6:ℝ)<0)
  have h₆ := const_scale_zero_first (1024*(B : ℝ)^3) (b:= -1/100) (c:=2/3) (by norm_num : (-2/15:ℝ)<0)
  have h₇ := const_scale_zero_first (2048*(B : ℝ)^3) (b:= -1/100) (c:=1/3) (by norm_num : (-1/10:ℝ)<0)
  have h₈ := const_scale_zero_first (1024*(B : ℝ)^3) (b:= -1/100) (c:=0) (by norm_num : (-1/15:ℝ)<0)
  have h₉ := const_scale_zero_first (4096*(B : ℝ)^2) (b:= -51/100) (c:=1/3) (by norm_num : (-2/15:ℝ)<0)
  have h₁₀ := const_scale_zero_first (4096*(B : ℝ)^2) (b:= -51/100) (c:=0) (by norm_num : (-1/10:ℝ)<0)
  have hh : Tendsto (fun x => ∑ j ∈ Finset.Icc 5 r, (((2*r)^(j-2) : ℕ) : ℝ)*
      scale (4/3-(j : ℝ)/3) ((j : ℝ)/100-1/100) 0 x) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.Icc 5 r) (a:=fun _ => (0:ℝ)) (fun j hj =>
      const_scale_zero_first (((2*r)^(j-2) : ℕ) : ℝ) (b:=(j : ℝ)/100-1/100) (c:=0)
        (show 4/3-(j : ℝ)/3 < 0 by
          have hjr : (5:ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
          linarith))
    simpa only [Finset.sum_const_zero] using h
  unfold normalizedLoss
  simpa only [zero_add] using
    (((((((((h₁.add h₂).add h₃).add h₄).add h₅).add h₆).add h₇).add h₈).add h₉).add h₁₀).add hh

theorem eventually_loss_envelope (r B : ℕ) :
    ∀ᶠ n : ℕ in atTop, lossEnvelope n r (degreeEnvelope B n) (pairEnvelope n) B
      (sampleP n) (sampleCap n) ≤ sampleP n*n/8 := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdom := hn.eventually eventually_scale_domain
  have hlim := (normalizedLoss_tendsto r B).comp hn
  filter_upwards [hdom,hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/8)] with n hx hcost
  have hp : 0 < sampleP n := scale_pos hx _ _ _
  have hn0 : 0 < (n : ℝ) := hx.1
  change normalizedLoss r B n < 1/8 at hcost
  rw [← loss_envelope_identity hx r B] at hcost
  have h := (div_lt_iff₀ (mul_pos hp hn0)).mp hcost
  linarith

end KMV
