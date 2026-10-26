module
public import KMV.SamplingProcess
public section
namespace KMV.Sampling
open FiniteLaw
variable {n : ℕ}

@[expose] def Inert (β a : ℝ) : Prop := a = 0 ∨ β ≤ a ∧ a < 1

theorem inert_not_active {β a : ℝ} (h : Inert β a) : ¬ Active β a := by
  intro ha
  rcases h with h | h
  · rw [h] at ha; exact lt_irrefl _ ha.1
  · exact not_lt_of_ge h.1 ha.2

theorem next_inert_eq {G : Fin n → Fin n → Prop} {β : ℝ}
    {i v : Fin n} {w : Fin n → ℝ} (ha : Active β (w i))
    (hv : Inert β (w v)) (b : Bool) : next G β i b w v = w v := by
  classical
  have hvi : v ≠ i := by intro h; subst v; exact inert_not_active hv ha
  rcases hv with hv | hv
  · simp [next, hvi, hv]
  · simp [next, hvi, not_lt.mpr hv.1]

@[expose] def Safe (G : Fin n → Fin n → Prop) (β : ℝ) (t : ℕ)
    (w : Fin n → ℝ) : Prop :=
  ∀ u v, u.val < t → u.val < v.val → w u = 1 → G u v → Inert β (w v)

theorem next_safe {G : Fin n → Fin n → Prop} {β : ℝ}
    {i : Fin n} {w : Fin n → ℝ} (ha : Active β (w i))
    (hw : Bounded i.val w) (hs : Safe G β i.val w) (b : Bool) :
    Safe G β (i.val+1) (next G β i b w) := by
  classical
  intro u v hu huv hus huvG
  by_cases hui : u = i
  · subst u
    have hvi : v ≠ i := by intro h; subst v; omega
    have hb : b = true := by
      cases b
      · simp [next] at hus
      · rfl
    subst b
    by_cases hv : w v < β
    · exact Or.inl (by simp [next, hvi, huv, huvG, hv])
    · exact Or.inr ⟨by simpa [next, hvi, hv] using le_of_not_gt hv,
        by simpa [next, hvi, hv] using hw.2 v (by omega)⟩
  · have hui' : u.val < i.val := by
      have hne : u.val ≠ i.val := fun h => hui (Fin.ext h)
      omega
    rw [next_past hui' b] at hus
    have hv := hs u v hui' huv hus huvG
    rw [next_inert_eq ha hv b]
    exact hv

theorem step_safe {G : Fin n → Fin n → Prop} {β : ℝ}
    (i : Fin n) {w : Fin n → ℝ} (hw : Bounded i.val w)
    (hs : Safe G β i.val w) : (step G β i w).All (Safe G β (i.val+1)) := by
  classical
  unfold step
  split_ifs with ha
  · exact ⟨next_safe ha hw hs true, next_safe ha hw hs false⟩
  · intro u v hu huv hus hG
    have hui : u ≠ i := by
      intro h; subst u
      have hi := hw.2 i (le_refl _)
      rw [hus] at hi
      exact lt_irrefl _ hi
    exact hs u v (by have : u.val ≠ i.val := fun h => hui (Fin.ext h); omega) huv hus hG

theorem run_safe {G : Fin n → Fin n → Prop} {β p : ℝ} (hβ : β ≤ 1/2)
    (hp : 0 ≤ p) (hp' : p < 1) (t : ℕ) (ht : t ≤ n) :
    (run G β p t).All (Safe G β t) := by
  induction t with
  | zero => intro u v hu; omega
  | succ t ih =>
    have htn : t < n := by omega
    rw [run, dite_eq_left htn]
    exact FiniteLaw.all_bind
      (FiniteLaw.all_and (run_bounded hβ hp hp' t (by omega)) (ih (by omega)))
      (fun w h => step_safe ⟨t,htn⟩ h.1 h.2)

@[expose] noncomputable def selected (w : Fin n → ℝ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun v => w v = 1)

theorem run_independent {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (hβ : β ≤ 1/2) (hp : 0 ≤ p) (hp' : p < 1) :
    (run G β p n).All (fun w => ∀ u ∈ selected w, ∀ v ∈ selected w, ¬ G u v) := by
  classical
  apply FiniteLaw.all_mono (run_safe hβ hp hp' n (le_refl _))
  intro w hw u hu v hv hG
  have hu' : w u = 1 := (Finset.mem_filter.mp hu).2
  have hv' : w v = 1 := (Finset.mem_filter.mp hv).2
  have hne : u.val ≠ v.val := by
    intro h; have he := Fin.ext h; subst v; exact hirr u hG
  rcases lt_or_gt_of_ne hne with huv | hvu
  · have hi := hw u v u.isLt huv hu' hG
    rw [hv'] at hi
    rcases hi with hi | hi <;> norm_num at *
  · have hi := hw v u v.isLt hvu hv' (hsym u v hG)
    rw [hu'] at hi
    rcases hi with hi | hi <;> norm_num at *

end KMV.Sampling
