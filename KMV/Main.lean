module
public import KMV.ReducedAssembly
public section
namespace KMV
open Filter Topology Finset
open scoped Classical

/-- Every sufficiently large n-vertex hypergraph with no loose triangle and
edge sizes between 3 and fixed r has an independent set of size at least
c n^(2/3) (log log n)^(1/3), conditional on the stated Li–Postle
vertex-coloring bound for hypergraphs with edges of sizes 3 and 4. -/
theorem main_result (hLP : LiPostle34) : KMVStatement := by
  obtain ⟨C,hC,hcolor⟩ := liPostle34_on_subset hLP
  intro r _hr
  let B := reductionConstant r
  have hB : 0 < B := reductionConstant_pos r
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  let c := min 1 (1/(4*C*(12800*(B : ℝ))))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  have hnlim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hev := (hnlim.eventually (eventually_geometry r B)).and
    ((hnlim.eventually (eventually_sampling_parameters B)).and (eventually_loss_envelope r B))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro n hn H hr hl
  obtain ⟨⟨hx,hn1,hQ,ht1,hL₃,hL₄⟩,⟨hp,hpβ,hβ,hlog,hent⟩,hloss⟩ := hN n hn
  have hnpos : 0 < n := by exact_mod_cast hx.1
  have ht : 0 < targetSize n := scale_pos hx _ _ _
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcb : c ≤ 1/(4*C*(12800*(B : ℝ))) := min_le_right _ _
  suffices ∃ I : Finset (Fin n), Independent H I ∧ c*targetSize n ≤ (I.card : ℝ) by
    simpa only [targetSize,scale,Real.rpow_zero,Real.rpow_eq_pow,mul_one,mul_assoc] using this
  rcases structural_reduction hnpos ht hr hl with hlarge | ⟨K,U₀,hKr,hKl,hKa,hKI,hU₀,hK₃,hK₄,hKtr,hKhigh⟩
  · obtain ⟨I,hI,hsize⟩ := hlarge
    have hct : c*targetSize n ≤ targetSize n := by nlinarith
    exact ⟨I,hI,hct.trans hsize⟩
  have hdegree : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, (sizeDegree K j v : ℝ) ≤ initialDegree B n j := by
    intro j hj v
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with rfl | rfl
    · simpa only [initialDegree,ite_true] using hK₃ v
    · by_cases h4r : 4 ≤ r
      · simpa only [initialDegree,show (4:ℕ) ≠ 3 by decide,ite_false] using hK₄ 4 (by omega) h4r v
      · rw [degree_above_rank hKr (by omega) v]
        norm_num [initialDegree]
        positivity
  obtain ⟨U,hUU₀,hUr,hUt,hUd₃,hUd₄,hUs⟩ := parameter_cleaning hB hKr hKa hKl hU₀
    hdegree hKtr hKhigh hx hn1 hQ ht1 hL₃ hL₄ hp hpβ hβ hlog hent hloss
  have hUpos : 0 < (U.card : ℝ) := lt_of_lt_of_le (by positivity) hUs
  have hUne : U.Nonempty := card_pos.mp (by exact_mod_cast hUpos)
  have hd := final_degree_log_bounds hx hQ hB
  obtain ⟨I,hIU,hI,hIs⟩ := hcolor n K U hUne hUr hUt (finalDegree B n 3) (finalDegree B n 4)
    (hd 3 (by simp)).1 (hd 4 (by simp)).1 hUd₃ hUd₄
  refine ⟨I,hKI I (hIU.trans hUU₀) hI,?_⟩
  let Z := max (Real.rpow (finalDegree B n 3/Real.log (finalDegree B n 3)) (1/2:ℝ))
    (Real.rpow (finalDegree B n 4/Real.log (finalDegree B n 4)) (1/3:ℝ))
  have hZ : Z ≤ colorEnvelope B n := coloring_denominator_bound hx hQ hB
  have hz : 0 < colorEnvelope B n := by
    unfold colorEnvelope
    exact mul_pos (by positivity) (scale_pos hx _ _ _)
  have hqpos : 0 < Real.log (Real.log (n : ℝ))/100 := by positivity
  have hDpos : 0 < finalDegree B n 3 := by have := (hd 3 (by simp)).1; linarith
  have hLDpos : 0 < Real.log (finalDegree B n 3) := hqpos.trans_le (hd 3 (by simp)).2
  have hZpos : 0 < Z := (Real.rpow_pos_of_pos (div_pos hDpos hLDpos) (1/2:ℝ)).trans_le (le_max_left _ _)
  have hid : (1/(4*C*(12800*(B : ℝ))))*targetSize n =
      (sampleP n*n/4)/(C*colorEnvelope B n) := by
    apply (eq_div_iff (mul_ne_zero hC.ne' hz.ne')).mpr
    calc
      _ = (targetSize n*colorEnvelope B n)/(4*(12800*(B : ℝ))) := by field_simp
      _ = _ := by rw [target_color_identity hx B]; field_simp
  calc
    c*targetSize n ≤ (1/(4*C*(12800*(B : ℝ))))*targetSize n := mul_le_mul_of_nonneg_right hcb ht.le
    _ = (sampleP n*n/4)/(C*colorEnvelope B n) := hid
    _ ≤ (U.card : ℝ)/(C*colorEnvelope B n) := div_le_div_of_nonneg_right hUs (mul_pos hC hz).le
    _ ≤ (U.card : ℝ)/(C*Z) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hC hZpos)
      (mul_le_mul_of_nonneg_left hZ hC.le)
    _ ≤ (I.card : ℝ) := hIs

end KMV
