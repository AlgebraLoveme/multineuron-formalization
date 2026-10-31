module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Mathlib

public section

namespace Lemma_Gp1.Machinery

-- formalizer:machinery-begin
theorem exact_mem_stages {L : ℕ} {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+1 → v i.succ = step i (v i.castSucc)})
    (v : (j : Fin (L+1)) → Fin (w j) → ℝ)
    (hx : v 0 ∈ X) (hv : ∀ i, v i.succ = step i (v i.castSucc)) :
    ∀ k, v ∈ C k := by
  intro k
  induction k with
  | zero => simpa [hzero] using hx
  | succ k ih =>
    rw [hsucc]
    exact ⟨ih, subset_convexHull ℝ _ ⟨⟨v, ih, fun _ _ => rfl⟩, fun i _ _ => hv i⟩⟩

-- formalizer:machinery-end

end Lemma_Gp1.Machinery
