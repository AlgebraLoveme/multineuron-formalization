module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Lemma_Jp1.Machinery

-- formalizer:machinery-begin

theorem compact_convexHull (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let N := Module.finrank ℝ E + 2
  let C (n : Fin N) : Set E :=
    (fun p : (Fin n.val → ℝ) × (Fin n.val → E) => ∑ i, p.1 i • p.2 i) ''
      ((stdSimplex ℝ (Fin n.val)) ×ˢ (Set.pi Set.univ (fun _ => S)))
  have hc (n : Fin N) : IsCompact (C n) := by
    apply IsCompact.image ((isCompact_stdSimplex ℝ _).prod
      (isCompact_univ_pi (fun _ => hS)))
    fun_prop
  have heq : convexHull ℝ S = ⋃ n, C n := by
    apply Set.Subset.antisymm
    · intro x hx
      let t := Caratheodory.minCardFinsetOfMemConvexHull hx
      have ht := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
      have hi := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
      have hm := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
      obtain ⟨w, hw, hw1, hwx⟩ := Finset.mem_convexHull'.mp hm
      have hn : Fintype.card t < N := by
        have hb := hi.card_le_finrank_succ
        have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))
        dsimp [N, E, t] at *
        omega
      let n : Fin N := ⟨Fintype.card t, hn⟩
      let e := (Fintype.equivFin t).symm
      have hs (f : E → E) : (∑ i : Fin n.val, f (e i)) = ∑ a ∈ t, f a := by
        exact (e.sum_comp (fun a : t => f a)).trans (Finset.sum_coe_sort t f)
      have hwSum : (∑ i : Fin n.val, w (e i)) = 1 := by
        calc
          _ = ∑ a : t, w a := e.sum_comp (fun a : t => w a)
          _ = 1 := by simpa only [Finset.sum_coe_sort] using hw1
      apply Set.mem_iUnion.mpr
      refine ⟨n, ⟨(fun i => w (e i), fun i => (e i : E)), ?_, ?_⟩⟩
      · exact ⟨⟨fun i => hw _ (e i).property, hwSum⟩,
          fun i _ => ht (e i).property⟩
      · exact (hs (fun a => w a • a)).trans hwx
    · intro x hx
      obtain ⟨n, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (Set.mem_univ i)) rfl
  rw [heq]
  exact isCompact_iUnion hc

theorem inf_norm_eq (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : S.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    sInf ((fun y => ‖x - y‖) '' S) = Metric.infDist x S := by
  simpa only [dist_eq_norm] using (Metric.isGLB_infDist (x := x) hS).csInf_eq (hS.image _)

theorem directed_bdd (d : ℕ) (S T : Set (EuclideanSpace ℝ (Fin d)))
    (cS : IsCompact S) (hT : T.Nonempty) :
    BddAbove ((fun x => sInf ((fun y => ‖x - y‖) '' T)) '' S) := by
  simp_rw [inf_norm_eq d T hT]
  exact cS.bddAbove_image (Metric.continuous_infDist_pt T).continuousOn

theorem norm_weighted_difference (d : ℕ) {ι : Type} [Fintype ι]
    (w : ι → ℝ) (x y : ι → EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hb : ∀ i, ‖x i - y i‖ ≤ r) :
    ‖(∑ i, w i • x i) - ∑ i, w i • y i‖ ≤ r := by
  calc
    _ = ‖∑ i, w i • (x i - y i)‖ := by simp [smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖w i • (x i - y i)‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖x i - y i‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg, hw]
    _ ≤ ∑ i, w i * r := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = r := by rw [← Finset.sum_mul, hw1, one_mul]
-- formalizer:machinery-end

end Lemma_Jp1.Machinery
