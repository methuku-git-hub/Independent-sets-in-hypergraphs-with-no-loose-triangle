module
public import KMV.Entropy
public import KMV.Auxiliary
public section
namespace KMV
namespace Sampling
open FiniteLaw
variable {n : ℕ}

@[expose] def Active (β a : ℝ) : Prop := 0 < a ∧ a < β

/-- Process i. Processed weights are selection indicators, unless the vertex
was frozen; frozen weights are retained. Future weights follow the manuscript. -/
@[expose] noncomputable def next (G : Fin n → Fin n → Prop) (β : ℝ)
    (i : Fin n) (chosen : Bool) (w : Fin n → ℝ) (v : Fin n) : ℝ := by
  classical
  exact if v = i then (if chosen then 1 else 0)
    else if i.val < v.val ∧ G i v ∧ w v < β then
      (if chosen then 0 else w v / (1-w i)) else w v

@[expose] noncomputable def step (G : Fin n → Fin n → Prop) (β : ℝ)
    (i : Fin n) (w : Fin n → ℝ) : FiniteLaw (Fin n → ℝ) := by
  classical
  exact if Active β (w i) then
    .fork (w i) (.pure (next G β i true w)) (.pure (next G β i false w))
    else .pure w

@[expose] def Bounded (t : ℕ) (w : Fin n → ℝ) : Prop :=
  (∀ v, 0 ≤ w v ∧ w v ≤ 1) ∧ (∀ v, t ≤ v.val → w v < 1)

theorem step_valid {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    (i : Fin n) (w : Fin n → ℝ) : (step G β i w).Valid := by
  classical
  unfold step
  split_ifs with ha
  · exact ⟨ha.1.le, by have := ha.2; linarith, trivial, trivial⟩
  · trivial

theorem next_nonneg {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    {i : Fin n} {w : Fin n → ℝ} (ha : Active β (w i))
    (hw : ∀ v, 0 ≤ w v) (b : Bool) (v : Fin n) : 0 ≤ next G β i b w v := by
  classical
  have hden : 0 < 1-w i := by have := ha.2; linarith
  unfold next
  split_ifs <;> first | positivity | exact hw v | exact div_nonneg (hw v) hden.le

theorem next_le_one {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    {i : Fin n} {w : Fin n → ℝ} (ha : Active β (w i))
    (hw : ∀ v, w v ≤ 1) (b : Bool) (v : Fin n) : next G β i b w v ≤ 1 := by
  classical
  have hden : 0 < 1-w i := by have := ha.2; linarith
  unfold next
  split_ifs with hv hb hc hb
  · exact le_refl _
  · norm_num
  · norm_num
  · apply (div_le_iff₀ hden).mpr
    have := hc.2.2
    have := ha.2
    linarith
  · exact hw v

theorem next_future_lt_one {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    {i v : Fin n} {w : Fin n → ℝ} (ha : Active β (w i))
    (hiv : i.val < v.val) (hw : w v < 1) (b : Bool) : next G β i b w v < 1 := by
  classical
  have hvi : v ≠ i := by intro h; subst v; omega
  have hden : 0 < 1-w i := by have := ha.2; linarith
  simp only [next, hvi, ite_false]
  split_ifs with hc hb
  · norm_num
  · apply (div_lt_iff₀ hden).mpr
    have := hc.2.2
    have := ha.2
    linarith
  · exact hw

theorem step_bounded {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    (i : Fin n) {w : Fin n → ℝ} (hw : Bounded i.val w) :
    (step G β i w).All (Bounded (i.val+1)) := by
  classical
  unfold step
  split_ifs with ha
  · have hn : ∀ b : Bool, Bounded (i.val+1) (next G β i b w) := by
      intro b
      refine ⟨fun v => ⟨next_nonneg hβ ha (fun v => (hw.1 v).1) b v,
        next_le_one hβ ha (fun v => (hw.1 v).2) b v⟩, ?_⟩
      intro v hv
      exact next_future_lt_one hβ ha (by omega) (hw.2 v (by omega)) b
    exact ⟨hn true, hn false⟩
  · exact ⟨hw.1, fun v hv => hw.2 v (by omega)⟩

theorem next_past {G : Fin n → Fin n → Prop} {β : ℝ}
    {i v : Fin n} {w : Fin n → ℝ} (hvi : v.val < i.val) (b : Bool) :
    next G β i b w v = w v := by
  classical
  have hn : v ≠ i := by intro h; subst v; omega
  have hn' : ¬ i.val < v.val := by omega
  simp [next, hn, hn']

theorem step_mean {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    (i v : Fin n) (w : Fin n → ℝ) :
    (step G β i w).expect (fun w => w v) = w v := by
  classical
  unfold step
  split_ifs with ha
  · dsimp [FiniteLaw.expect]
    have hden : 1-w i ≠ 0 := by have := ha.2; linarith
    by_cases hvi : v = i
    · subst v; simp [next]
    · by_cases hc : i.val < v.val ∧ G i v ∧ w v < β
      · simpa [next, hvi, hc] using mul_div_cancel₀ (w v) hden
      · simp only [next, hvi, ite_false, hc]
        ring
  · rfl

@[expose] noncomputable def run (G : Fin n → Fin n → Prop) (β p : ℝ) :
    ℕ → FiniteLaw (Fin n → ℝ)
  | 0 => .pure (fun _ => p)
  | t+1 => if ht : t < n then (run G β p t).bind (step G β ⟨t,ht⟩) else run G β p t

theorem run_valid {G : Fin n → Fin n → Prop} {β p : ℝ} (hβ : β ≤ 1/2) (t : ℕ) :
    (run G β p t).Valid := by
  induction t with
  | zero => trivial
  | succ t ih =>
    unfold run
    split_ifs with ht
    · apply FiniteLaw.valid_bind ih
      have hall : (run G β p t).All (fun _ => True) := by
        induction run G β p t with
        | pure w => trivial
        | fork a l r il ir => exact ⟨il, ir⟩
      exact FiniteLaw.all_mono hall (fun w _ => step_valid hβ ⟨t,ht⟩ w)
    · exact ih

theorem run_mean {G : Fin n → Fin n → Prop} {β p : ℝ} (hβ : β ≤ 1/2)
    (t : ℕ) (v : Fin n) : (run G β p t).expect (fun w => w v) = p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold run
    split_ifs with ht
    · rw [FiniteLaw.expect_bind]
      simp_rw [step_mean hβ]
      exact ih
    · exact ih

theorem run_bounded {G : Fin n → Fin n → Prop} {β p : ℝ} (hβ : β ≤ 1/2)
    (hp : 0 ≤ p) (hp' : p < 1) (t : ℕ) (ht : t ≤ n) :
    (run G β p t).All (Bounded t) := by
  induction t with
  | zero => exact ⟨fun _ => ⟨hp, hp'.le⟩, fun _ _ => hp'⟩
  | succ t ih =>
    have htn : t < n := by omega
    rw [run, dite_eq_left htn]
    exact FiniteLaw.all_bind (ih (by omega)) (fun w hw => step_bounded hβ ⟨t,htn⟩ hw)

end Sampling
end KMV
