module
public import KMV.Triangles
public import KMV.AuxiliaryDegrees
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

theorem separated_union_of_cross_covered {G : V → V → Prop} {e f g : Finset V}
    (he : Separated G e) (hf : Separated G f) (hg : Separated G g)
    (hc : e \ f ⊆ g) (hc' : f \ e ⊆ g) : Separated G (e ∪ f) := by
  intro x hx y hy hxy
  by_cases hxe : x ∈ e
  · by_cases hye : y ∈ e
    · exact he x hxe y hye hxy
    · have hyf : y ∈ f := (mem_union.mp hy).resolve_left hye
      by_cases hxf : x ∈ f
      · exact hf x hxf y hyf hxy
      · exact hg x (hc (mem_sdiff.mpr ⟨hxe,hxf⟩)) y (hc' (mem_sdiff.mpr ⟨hyf,hye⟩)) hxy
  · have hxf : x ∈ f := (mem_union.mp hx).resolve_left hxe
    by_cases hyf : y ∈ f
    · exact hf x hxf y hyf hxy
    · have hye : y ∈ e := (mem_union.mp hy).resolve_right hyf
      exact hg x (hc' (mem_sdiff.mpr ⟨hxf,hxe⟩)) y (hc (mem_sdiff.mpr ⟨hye,hyf⟩)) hxy

theorem triangle_single_differences_separated {G : V → V → Prop} {e f g : Finset V}
    (he : Separated G e) (hf : Separated G f) (hg : Separated G g)
    (ht : Triangle e f g) (hc : (e \ f).card = 1) (hc' : (f \ e).card = 1) :
    Separated G (e ∪ f) := by
  obtain ⟨a,ha⟩ := card_eq_one.mp hc
  obtain ⟨b,hb⟩ := card_eq_one.mp hc'
  obtain ⟨x,hx⟩ := ht.2.2
  obtain ⟨y,hy⟩ := ht.2.1
  have hxa : x = a := by
    have hh : x ∈ e \ f := mem_sdiff.mpr ⟨(mem_inter.mp (mem_sdiff.mp hx).1).2,(mem_sdiff.mp hx).2⟩
    simpa [ha] using hh
  have hyb : y = b := by
    have hh : y ∈ f \ e := mem_sdiff.mpr ⟨(mem_inter.mp (mem_sdiff.mp hy).1).1,(mem_sdiff.mp hy).2⟩
    simpa [hb] using hh
  apply separated_union_of_cross_covered he hf hg
  · rw [ha]
    exact singleton_subset_iff.mpr (hxa ▸ (mem_inter.mp (mem_sdiff.mp hx).1).1)
  · rw [hb]
    exact singleton_subset_iff.mpr (hyb ▸ (mem_inter.mp (mem_sdiff.mp hy).1).2)

theorem triangle_three_pair_separated {G : V → V → Prop} {e f g : Finset V}
    (he : Separated G e) (hf : Separated G f) (hg : Separated G g)
    (ht : Triangle e f g) (hec : e.card = 3) (hfc : f.card = 3)
    (hef : (e ∩ f).card = 2) : Separated G (e ∪ f) := by
  apply triangle_single_differences_separated he hf hg ht
  · simp [card_sdiff,inter_comm f e,hec,hef]
  · simp [card_sdiff,hfc,hef]

theorem triangle_of_small_intersections {e f g : Finset V} (ht : Triangle e f g)
    (hef : (e ∩ f).card ≤ 1) (hfg : (f ∩ g).card ≤ 1) (hge : (g ∩ e).card ≤ 1) :
    LooseTriangle e f g := by
  have hne : ∀ {a b c : Finset V}, ((a ∩ b) \ c).Nonempty → 0 < (a ∩ b).card := by
    rintro a b c ⟨x,hx⟩
    exact card_pos.mpr ⟨x,(mem_sdiff.mp hx).1⟩
  have hc₁ : (e ∩ f).card = 1 := by have := hne ht.1; omega
  have hc₂ : (f ∩ g).card = 1 := by have := hne ht.2.1; omega
  have hc₃ : (g ∩ e).card = 1 := by have := hne ht.2.2; omega
  obtain ⟨x,hx⟩ := ht.1
  have hzero : e ∩ f ∩ g = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have heq := card_le_one.mp hef x (mem_sdiff.mp hx).1 y (mem_inter.mp hy).1
    exact (mem_sdiff.mp hx).2 (heq.symm ▸ (mem_inter.mp hy).2)
  have hd := triangle_edges_distinct ht
  exact ⟨hd.1,hd.2.1,hd.2.2,hc₁,hc₂,hc₃,hzero⟩

end KMV
