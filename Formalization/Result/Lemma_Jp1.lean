module
public import Formalization.Result.helpers.Lemma_Jp1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Lemma_Jp1

theorem result_J_1 (d : ℕ) (H K : Set (EuclideanSpace ℝ (Fin d)))
    (hH : H.Nonempty) (cH : IsCompact H) (hK : K.Nonempty) (cK : IsCompact K) :
  ∃ cH' : IsCompact (convexHull ℝ H), ∃ cK' : IsCompact (convexHull ℝ K),
  HausdorffDistance d (convexHull ℝ H) (convexHull ℝ K)
    hH.convexHull cH' hK.convexHull cK' ≤
    HausdorffDistance d H K hH cH hK cK := (by
  -- formalizer:proof-begin
  classical
  let cH' := Machinery.compact_convexHull d H cH
  let cK' := Machinery.compact_convexHull d K cK
  refine ⟨cH', cK', ?_⟩
  -- Nonempty compact hulls keep both directed suprema in the finite real domain.
  -- The helper establishes hull compactness by finite-dimensional Carathéodory.
  have directed (A B : Set (EuclideanSpace ℝ (Fin d)))
      (hA : A.Nonempty) (hB : B.Nonempty) (cB : IsCompact B) (r : ℝ)
      (hb : ∀ a ∈ A, Metric.infDist a B ≤ r) :
      sSup ((fun x => sInf ((fun y => ‖x - y‖) '' convexHull ℝ B)) ''
        convexHull ℝ A) ≤ r := by
    apply csSup_le (hA.convexHull.image _)
    rintro _ ⟨x, hx, rfl⟩
    -- J.1: write x as a finite convex combination of vertices in A.
    obtain ⟨ι, inst, w, z, hw, hw1, hz, hzx⟩ :=
      mem_convexHull_iff_exists_fintype.mp hx
    letI := inst
    -- Compactness supplies a nearest point in B for each vertex z_i.
    have nearest (i : ι) := cB.exists_infDist_eq_dist hB (z i)
    choose y hy hdist using nearest
    have hyHull : (∑ i, w i • y i) ∈ convexHull ℝ B :=
      mem_convexHull_of_exists_fintype w y hw hw1 hy rfl
    have hb' (i : ι) : ‖z i - y i‖ ≤ r := by
      rw [← dist_eq_norm, ← hdist i]
      exact hb _ (hz i)
    -- The paper's displayed inequality: norm of the weighted differences
    -- is at most the weighted norms, and their sum is at most r.
    have hn := Machinery.norm_weighted_difference
      d w z y r hw hw1 hb'
    rw [hzx] at hn
    -- Taking the point-to-set infimum, then the supremum over x, preserves the bound.
    dsimp only
    rw [Machinery.inf_norm_eq
      d (convexHull ℝ B) hB.convexHull x]
    exact (Metric.infDist_le_dist_of_mem hyHull).trans (by simpa [dist_eq_norm] using hn)
  have reverse (S : Set (EuclideanSpace ℝ (Fin d))) :
      (fun y => sInf ((fun x => ‖x - y‖) '' S)) =
      (fun y => sInf ((fun x => ‖y - x‖) '' S)) := by
    funext y
    congr 1
    congr 1
    funext x
    exact norm_sub_rev x y
  unfold HausdorffDistance
  rw [reverse H, reverse (convexHull ℝ H)]
  -- Apply the directed argument in both orders and take the maximum.
  apply max_le
  · apply directed H K hH hK cK
    intro a ha
    rw [← Machinery.inf_norm_eq d K hK]
    exact (le_csSup
      (Machinery.directed_bdd d H K cH hK)
      (Set.mem_image_of_mem _ ha)).trans (le_max_left _ _)
  · apply directed K H hK hH cH
    intro a ha
    rw [← Machinery.inf_norm_eq d H hH]
    exact (le_csSup
      (Machinery.directed_bdd d K H cK hH)
      (Set.mem_image_of_mem _ ha)).trans (le_max_right _ _)
  -- formalizer:proof-end
)

end Lemma_Jp1
