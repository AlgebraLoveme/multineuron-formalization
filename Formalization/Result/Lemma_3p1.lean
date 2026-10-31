module
public import Formalization.Result.helpers.Lemma_3p1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Lemma_3p1

theorem result_3_1 :
  let σ : ℝ → ℝ := fun t => max t 0
  let poly : {d : ℕ} → Set (Fin d → ℝ) → Prop := fun {d} X =>
    ∃ V : Finset (Fin d → ℝ), X = convexHull ℝ (↑V : Set _)
  ∀ (L : ℕ) (hL : 0 < L) (w : Fin (L + 1) → ℕ)
    (N : NetworkSemantics σ L w) (X : Set (Fin (w 0) → ℝ)),
    X.Nonempty → poly X → ¬X.Subsingleton →
    ∀ (i : Fin (L + 1)), 1 ≤ i.val → i.val < L →
    let C := relaxation.stages(WindowRelaxation σ L w N X 1 (by omega) hL)
    (fun v => v i) '' C i.val = (fun v => v i) '' C L := (by
  -- formalizer:proof-begin
  classical
  dsimp only
  intro L hL w N X hX hpoly hnonsingle i hi hiL
  let σ : ℝ → ℝ := fun t => max t 0
  let step : (a : Fin L) → (Fin (w a.castSucc) → ℝ) →
      (Fin (w a.succ) → ℝ) := fun a x =>
    match N.val a with
    | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  let C := relaxation.stages(WindowRelaxation σ L w N X 1 (by omega) hL)
  change (fun v => v i) '' C i.val = (fun v => v i) '' C L
  have hzero : C 0 = {v | v 0 ∈ X} := rfl
  have hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ a : Fin L, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)} := fun _ => rfl
  -- Appendix E, Lemma 3.1: earlier constraints involve only the prefix.
  -- The cylinder property also survives taking each graph's convex hull.
  have localC := Machinery.stages_local
    step X C hzero hsucc
  apply Set.Subset.antisymm
  · rintro z ⟨v, hv, hvz⟩
    -- Extend one layer at a time by its exact evaluation. The interface lies
    -- in the current projected domain, so the exact graph lies in its hull.
    have extend : ∀ k, i.val ≤ k → k ≤ L →
        ∃ u ∈ C k, u i = v i := by
      intro k hik hkL
      induction k, hik using Nat.le_induction with
      | base => exact ⟨v, hv, rfl⟩
      | succ k hik ih =>
        obtain ⟨u, hu, hui⟩ := ih (by omega)
        let a : Fin L := ⟨k, by omega⟩
        let u' := Function.update u a.succ (step a (u a.castSucc))
        have same : ∀ j : Fin (L+1), j.val ≤ k → u' j = u j := by
          intro j hj
          have hne : j ≠ a.succ := by intro e; have := congrArg Fin.val e; simp [a] at this; omega
          exact Function.update_of_ne hne _ _
        have hu' : u' ∈ C k := localC k u hu u' same
        refine ⟨u', ?_, (same i hik).trans hui⟩
        rw [hsucc]
        refine ⟨hu', subset_convexHull ℝ _ ?_⟩
        refine ⟨⟨u, hu, fun j hj => same j (by omega)⟩, ?_⟩
        intro b hb hb'
        have hba : b = a := Fin.ext (by simp [a]; omega)
        subst b
        change u' a.succ = step a (u' a.castSucc)
        rw [same a.castSucc (by simp [a])]
        simp [u']
    obtain ⟨u, hu, hui⟩ := extend L (by omega) le_rfl
    exact ⟨u, hu, hui.trans hvz⟩
  · -- Adding the suffix constraints gives the reverse inclusion immediately.
    have decreasing : ∀ k, i.val ≤ k → C k ⊆ C i.val := by
      intro k hik
      induction k, hik using Nat.le_induction with
      | base => exact Set.Subset.rfl
      | succ k hik ih =>
        rw [hsucc]
        exact Set.Subset.trans Set.inter_subset_left ih
    exact Set.image_mono (decreasing L (by omega))
  -- formalizer:proof-end
)

end Lemma_3p1
