module
public import KMV.SamplingEntropy
public section
namespace KMV.Sampling
open FiniteLaw Finset
variable {n : ℕ}

theorem step_coordinate_past {G : Fin n → Fin n → Prop} {β : ℝ}
    (i v : Fin n) (hv : v.val < i.val) (w : Fin n → ℝ) (f : ℝ → ℝ) :
    (step G β i w).expect (fun w => f (w v)) = f (w v) := by
  classical
  unfold step
  split_ifs <;> simp only [FiniteLaw.expect, next_past hv]
  ring

theorem run_coordinate_after {G : Fin n → Fin n → Prop} {β p : ℝ}
    (v : Fin n) (f : ℝ → ℝ) (t : ℕ) (hv : v.val < t) :
    (run G β p t).expect (fun w => f (w v)) =
      (run G β p (v.val+1)).expect (fun w => f (w v)) := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hvt : v.val < t
    · rw [run]
      split_ifs with ht
      · rw [FiniteLaw.expect_bind]
        simp_rw [step_coordinate_past ⟨t,ht⟩ v hvt]
        exact ih hvt
      · exact ih hvt
    · have he : t = v.val := by omega
      subst t
      rfl

@[expose] noncomputable def lostWeight (β a : ℝ) : ℝ := by
  classical exact if β ≤ a then a else 0

theorem step_selection_identity {G : Fin n → Fin n → Prop} {β : ℝ}
    (i : Fin n) (w : Fin n → ℝ) (hw0 : 0 ≤ w i) (hw1 : w i < 1) :
    (step G β i w).probability (fun w => w i = 1) = w i - lostWeight β (w i) := by
  classical
  by_cases ha : Active β (w i)
  · simp [step, ha, FiniteLaw.probability, FiniteLaw.expect, next, lostWeight,
      not_le.mpr ha.2]
  · by_cases hf : β ≤ w i
    · simp [step, ha, FiniteLaw.probability, FiniteLaw.expect, lostWeight, hf, ne_of_lt hw1]
    · have hz : w i = 0 := by
        have hlt := lt_of_not_ge hf
        by_contra hn
        exact ha ⟨lt_of_le_of_ne hw0 (Ne.symm hn), hlt⟩
      simp [step, Active, FiniteLaw.probability, FiniteLaw.expect, lostWeight, hz]

theorem run_selection_identity {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hβ : β ≤ 1/2) (hp : 0 ≤ p) (hp' : p < 1) (v : Fin n) :
    (run G β p n).probability (fun w => w v = 1) =
      p - (run G β p v.val).expect (fun w => lostWeight β (w v)) := by
  classical
  unfold FiniteLaw.probability
  rw [run_coordinate_after v (fun a => if a=1 then 1 else 0) n v.isLt]
  rw [run, dite_eq_left v.isLt, FiniteLaw.expect_bind]
  have he := FiniteLaw.expect_congr
    (FiniteLaw.all_mono (run_bounded (G:=G) hβ hp hp' v.val v.isLt.le)
      (fun w hw => step_selection_identity (G:=G) (β:=β) v w (hw.1 v).1 (hw.2 v (le_refl _))))
  change (run G β p v.val).expect (fun w => (step G β v w).probability (fun w => w v=1)) = _
  rw [he, FiniteLaw.expect_sub, run_mean hβ]

theorem lostWeight_nonneg {β a : ℝ} (ha : 0 ≤ a) : 0 ≤ lostWeight β a := by
  classical
  unfold lostWeight
  split_ifs <;> linarith

theorem lostWeight_entropy {β p a : ℝ} (hp : 0 < p) (hβ : 0 < β) (ha : 0 ≤ a) :
    lostWeight β a * (Real.log (β/p)-1) ≤ entropy p a := by
  classical
  unfold lostWeight
  split_ifs with hf
  · exact entropy_freezing_bound hp hβ hf
  · simpa using entropy_nonneg hp ha

theorem marginal_bounds {G : Fin n → Fin n → Prop} {β p A : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (htri : ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a))
    (hβ : β ≤ 1/2) (hp : 0 < p) (hpβ : p < β) (hlog : 1 < Real.log (β/p))
    (v : Fin n) (hdeg : ((earlierNeighbors G v n).card : ℝ) ≤ A) :
    p - 2*A*p^2/(Real.log (β/p)-1) ≤ (run G β p n).probability (fun w => w v=1) ∧
      (run G β p n).probability (fun w => w v=1) ≤ p := by
  have hp1 : p < 1 := by linarith
  have hw := run_bounded (G:=G) hβ hp.le hp1 v.val v.isLt.le
  have hn := FiniteLaw.expect_nonneg (run_valid (G:=G) (p:=p) hβ v.val)
    (FiniteLaw.all_mono hw (fun w hw => lostWeight_nonneg (β:=β) (hw.1 v).1))
  have he := FiniteLaw.expect_mono (run_valid (G:=G) (p:=p) hβ v.val)
    (FiniteLaw.all_mono hw (fun w hw => lostWeight_entropy hp (hp.trans hpβ) (hw.1 v).1))
  rw [FiniteLaw.expect_mul_const] at he
  have hb := run_entropy_degree_bound hsym hirr htri hβ hp hp1 v hdeg
  have hden : 0 < Real.log (β/p)-1 := by linarith
  have hloss : (run G β p v.val).expect (fun w => lostWeight β (w v)) ≤
      2*A*p^2/(Real.log (β/p)-1) := (le_div_iff₀ hden).mpr (he.trans hb)
  rw [run_selection_identity hβ hp.le hp1 v]
  constructor <;> linarith

end KMV.Sampling
