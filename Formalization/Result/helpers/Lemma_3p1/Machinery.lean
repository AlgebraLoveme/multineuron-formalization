module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Lemma_3p1.Machinery

-- formalizer:machinery-begin
theorem hull_local {L : ℕ} {w : Fin (L + 1) → ℕ}
    (S : Set ((j : Fin (L + 1)) → Fin (w j) → ℝ)) (k : ℕ)
    (hS : ∀ x ∈ S, ∀ y, (∀ j, j.val ≤ k → y j = x j) → y ∈ S)
    {x} (hx : x ∈ convexHull ℝ S) (y)
    (hy : ∀ j, j.val ≤ k → y j = x j) : y ∈ convexHull ℝ S := by
  classical
  let f : ((j : Fin (L + 1)) → Fin (w j) → ℝ) →ᵃ[ℝ]
      ((j : Fin (L + 1)) → Fin (w j) → ℝ) :=
    { toFun := fun z j => if j.val ≤ k then z j else y j
      linear :=
        { toFun := fun z j => if j.val ≤ k then z j else 0
          map_add' := by intros; ext j t; by_cases h : j.val ≤ k <;> simp [h]
          map_smul' := by intros; ext j t; by_cases h : j.val ≤ k <;> simp [h] }
      map_vadd' := by intros; ext j t; by_cases h : j.val ≤ k <;> simp [h] }
  have hf : f '' S ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hS z hz (f z) (by intro j hj; simp [f, hj])
  have hfx : f x = y := by
    ext j t
    by_cases h : j.val ≤ k
    · simp [f, h, hy j h]
    · simp [f, h]
  rw [← hfx]
  apply convexHull_mono hf
  rw [← f.image_convexHull]
  exact ⟨x, hx, rfl⟩

theorem stages_local {L : ℕ} {w : Fin (L + 1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L + 1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+1 → v i.succ = step i (v i.castSucc)}) :
    ∀ k x, x ∈ C k → ∀ y, (∀ j, j.val ≤ k → y j = x j) → y ∈ C k := by
  intro k
  induction k with
  | zero =>
    intro x hx y hy
    rw [hzero] at hx ⊢
    simpa only [Set.mem_setOf_eq, hy 0 (by simp)] using hx
  | succ k ih =>
    intro x hx y hy
    rw [hsucc] at hx ⊢
    refine ⟨ih x hx.1 y (fun j hj => hy j (by omega)), ?_⟩
    apply hull_local _ (k+1) ?_ hx.2 y hy
    intro a ha b hb
    rcases ha with ⟨⟨u, hu, hau⟩, he⟩
    refine ⟨⟨u, hu, ?_⟩, ?_⟩
    · intro j hj
      rw [hb j (by omega)]
      exact hau j hj
    · intro i hi hi'
      rw [hb i.succ (by simp; omega), hb i.castSucc (by simp; omega)]
      exact he i hi hi'

-- formalizer:machinery-end

end Lemma_3p1.Machinery
