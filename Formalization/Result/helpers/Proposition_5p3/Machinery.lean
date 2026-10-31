module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_Gp1
public import Mathlib

public section

namespace Proposition_5p3.Machinery

-- formalizer:machinery-begin
theorem affine_image_hull {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (b : Fin m → ℝ) (S : Set (Fin d → ℝ)) :
    (fun x j => (∑ k, A j k * x k) + b j) '' convexHull ℝ S =
      convexHull ℝ ((fun x j => (∑ k, A j k * x k) + b j) '' S) := by
  let F : (Fin d → ℝ) →ᵃ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x j => (∑ k, A j k * x k) + b j
      linear :=
        { toFun := fun x j => ∑ k, A j k * x k
          map_add' := by intros; ext j; simp [mul_add, Finset.sum_add_distrib]
          map_smul' := by
            intros; ext j
            simp [Finset.mul_sum, mul_left_comm] }
      map_vadd' := by
        intros; ext j
        simp [mul_add, Finset.sum_add_distrib, add_assoc] }
  exact F.image_convexHull S

theorem stage_output_subset {L : ℕ} {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+1 → v i.succ = step i (v i.castSucc)})
    (i : Fin L) (S : Set (Fin (w i.succ) → ℝ)) (hS : Convex ℝ S)
    (hstep : ∀ u ∈ C i.val, step i (u i.castSucc) ∈ S) :
    ∀ v ∈ C (i.val+1), v i.succ ∈ S := by
  have inclusion : {v : (j : Fin (L+1)) → Fin (w j) → ℝ |
      (∃ u ∈ C i.val, ∀ j : Fin (L+1), j.val = i.val → v j = u j) ∧
      ∀ a : Fin L, i.val ≤ a.val → a.val < i.val+1 →
        v a.succ = step a (v a.castSucc)} ⊆ (fun v => v i.succ) ⁻¹' S := by
    rintro v ⟨⟨u, hu, he⟩, hv⟩
    change v i.succ ∈ S
    rw [hv i le_rfl (by omega), he i.castSucc rfl]
    exact hstep u hu
  have hh := convexHull_min inclusion (hS.linear_preimage
    (LinearMap.proj (R := ℝ) (φ := fun j : Fin (L+1) => Fin (w j) → ℝ) i.succ))
  intro v hv
  exact hh ((hsucc i.val ▸ hv).2)

theorem extrema_cover {ι : Type*} [Nonempty ι]
    (S : ι → Set ℝ) (hne : ∀ k, (S k).Nonempty)
    (hc : ∀ k, IsCompact (S k)) (T : Set ℝ) (hT : T = ⋃ k, S k)
    (hTc : IsCompact T) :
    sInf T = sInf (Set.range (fun k => sInf (S k))) ∧
    sSup T = sSup (Set.range (fun k => sSup (S k))) := by
  have hsub : ∀ k, S k ⊆ T := by intro k; rw [hT]; exact Set.subset_iUnion S k
  have htne : T.Nonempty := (hne (Classical.choice ‹Nonempty ι›)).mono (hsub _)
  constructor
  · apply le_antisymm
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact csInf_le_csInf hTc.bddBelow (hne k) (hsub k)
    · apply le_csInf htne
      intro x hx
      rw [hT] at hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      have hb : BddBelow (Set.range (fun k => sInf (S k))) :=
        ⟨sInf T, by rintro _ ⟨k, rfl⟩; exact csInf_le_csInf hTc.bddBelow (hne k) (hsub k)⟩
      exact (csInf_le hb (Set.mem_range_self k)).trans (csInf_le (hc k).bddBelow hk)
  · apply le_antisymm
    · apply csSup_le htne
      intro x hx
      rw [hT] at hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      have hb : BddAbove (Set.range (fun k => sSup (S k))) :=
        ⟨sSup T, by rintro _ ⟨k, rfl⟩; exact csSup_le_csSup hTc.bddAbove (hne k) (hsub k)⟩
      exact (le_csSup (hc k).bddAbove hk).trans (le_csSup hb (Set.mem_range_self k))
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact csSup_le_csSup hTc.bddAbove (hne k) (hsub k)

-- formalizer:machinery-end

end Proposition_5p3.Machinery
