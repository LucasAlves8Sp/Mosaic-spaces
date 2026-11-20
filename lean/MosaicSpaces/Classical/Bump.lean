module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen

/-!
# Boundary bumping (Lemma 5.2)

Let `K` be a compact connected Hausdorff space and `U` an open subset of `K` with `U ≠ K`. Then
every component of `cl U` meets `cl U \ U`. (The article also assumes `U` nonempty; that is only
needed for `cl U` to have a component at all, and is implicit here in the point `x ∈ cl U`.)
-/

@[expose] public section

open Set Topology

namespace MosaicSpaces

/-- **Boundary bumping** (Lemma 5.2). -/
theorem boundary_bumping {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ConnectedSpace K] {U : Set K} (hU : IsOpen U) (hUne : U ≠ univ) {x : K}
    (hx : x ∈ closure U) :
    (connectedComponentIn (closure U) x ∩ (closure U \ U)).Nonempty := by
  classical
  set A := closure U with hAdef
  have hAc : IsClosed A := isClosed_closure
  have : CompactSpace A := isCompact_iff_compactSpace.1 hAc.isCompact
  let x' : A := ⟨x, hx⟩
  rw [connectedComponentIn_eq_image hx]
  by_contra hcon
  -- the component misses the compact set `B = A \ U`
  let B : Set A := (Subtype.val : A → K) ⁻¹' Uᶜ
  have hBc : IsCompact B := (hU.isClosed_compl.preimage continuous_subtype_val).isCompact
  have hdisj : B ∩ ⋂ s : { s : Set A // IsClopen s ∧ x' ∈ s }, s.1 = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    refine eq_empty_of_forall_notMem fun c ⟨hcB, hcC⟩ => hcon ?_
    exact ⟨c, ⟨mem_image_of_mem _ hcC, c.2, hcB⟩⟩
  let ι := { s : Set A // IsClopen s ∧ x' ∈ s }
  obtain ⟨u, hu⟩ := hBc.elim_finite_subfamily_closed (fun s : ι => s.1) (fun s : ι => s.2.1.1)
    (Set.disjoint_iff_inter_eq_empty.2 hdisj)
  let E : Set A := ⋂ s ∈ u, (s : ι).1
  have hE : IsClopen E := isClopen_biInter_finset fun s _ => s.2.1
  have hxE : x' ∈ E := mem_iInter₂.2 fun s _ => s.2.2
  have hEU : ∀ e ∈ E, (e : K) ∈ U := fun e he => by
    by_contra h
    exact Set.disjoint_left.1 hu h he
  -- the image of `E` is clopen in `K`
  let E' : Set K := Subtype.val '' E
  have hE'c : IsClosed E' := hAc.isClosedEmbedding_subtypeVal.isClosedMap _ hE.1
  obtain ⟨W, hW, hWE⟩ := isOpen_induced_iff.1 hE.2
  have hE'o : IsOpen E' := by
    have : E' = W ∩ U := by
      ext y
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨by rw [← hWE] at he; exact he, hEU e he⟩
      · rintro ⟨hyW, hyU⟩
        refine ⟨⟨y, subset_closure hyU⟩, ?_, rfl⟩
        rw [← hWE]; exact hyW
    rw [this]; exact hW.inter hU
  rcases isClopen_iff.1 ⟨hE'c, hE'o⟩ with h | h
  · exact (h ▸ mem_image_of_mem _ hxE : x ∈ (∅ : Set K))
  · refine hUne (eq_univ_of_forall fun y => ?_)
    have : y ∈ E' := h ▸ mem_univ y
    obtain ⟨e, he, rfl⟩ := this
    exact hEU e he

end MosaicSpaces
