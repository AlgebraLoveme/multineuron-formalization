module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Mathlib

public section

namespace Lemma_3p2.Machinery

-- formalizer:machinery-begin
theorem stages_convex {L : ℕ} {w : Fin (L + 1) → ℕ}
    (step : (a : Fin L) → (Fin (w a.castSucc) → ℝ) → (Fin (w a.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ a : Fin L, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)}) (hX : Convex ℝ X) : ∀ k, Convex ℝ (C k) := by
  intro k
  induction k with
  | zero =>
    rw [hzero]
    exact hX.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun j : Fin (L+1) => Fin (w j) → ℝ) 0)
  | succ k ih => rw [hsucc]; exact ih.inter (convex_convexHull ℝ _)

theorem exact_mem_stages {L : ℕ} {w : Fin (L + 1) → ℕ}
    (step : (a : Fin L) → (Fin (w a.castSucc) → ℝ) → (Fin (w a.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ a : Fin L, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)})
    (v : (j : Fin (L+1)) → Fin (w j) → ℝ) (hv : v 0 ∈ X)
    (he : ∀ a, v a.succ = step a (v a.castSucc)) : ∀ k, v ∈ C k := by
  intro k
  induction k with
  | zero => simpa [hzero] using hv
  | succ k ih =>
    rw [hsucc]
    exact ⟨ih, subset_convexHull ℝ _ ⟨⟨v, ih, fun _ _ => rfl⟩, fun a _ _ => he a⟩⟩

theorem continue_suffix {L : ℕ} {w : Fin (L + 1) → ℕ}
    (step : (a : Fin L) → (Fin (w a.castSucc) → ℝ) → (Fin (w a.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ a : Fin L, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)})
    (i : Fin (L+1)) (v : (j : Fin (L+1)) → Fin (w j) → ℝ)
    (hi : v i ∈ (fun u => u i) '' C i.val)
    (he : ∀ a : Fin L, i.val ≤ a.val → v a.succ = step a (v a.castSucc)) :
    ∃ u ∈ C L, u (Fin.last L) = v (Fin.last L) := by
  classical
  obtain ⟨u, hu, hui⟩ := hi
  let q := fun j => if j.val ≤ i.val then u j else v j
  have hqi : q i = v i := by simp [q, hui]
  have hq : q ∈ C i.val :=
    Lemma_3p1.Machinery.stages_local
      step X C hzero hsucc i.val u hu q (by intro j hj; simp only [q, if_pos hj])
  have eqv : ∀ j, i.val ≤ j.val → q j = v j := by
    intro j hj
    by_cases hj' : j.val ≤ i.val
    · have : j = i := Fin.ext (by omega)
      subst j; exact hqi
    · simp only [q, if_neg hj']
  have hmem : ∀ k, i.val ≤ k → q ∈ C k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hq
    | succ k hk ih =>
      rw [hsucc]
      refine ⟨ih, subset_convexHull ℝ _ ⟨⟨q, ih, fun _ _ => rfl⟩, ?_⟩⟩
      intro a ha ha'
      rw [eqv a.succ (by simp; omega), eqv a.castSucc (by simp; omega)]
      exact he a (by omega)
  exact ⟨q, hmem L (by omega), eqv (Fin.last L) (by simp; omega)⟩

theorem compact_envelope {L : ℕ} {w : Fin (L + 1) → ℕ}
    (step : (a : Fin L) → (Fin (w a.castSucc) → ℝ) → (Fin (w a.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ a : Fin L, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)})
    (hX : IsCompact X) (hc : ∀ a, Continuous (step a)) :
    ∀ j : Fin (L+1), ∃ K : Set (Fin (w j) → ℝ), IsCompact K ∧
      (fun v => v j) '' C j.val ⊆ K := by
  intro j
  induction j using Fin.induction with
  | zero => exact ⟨X, hX, by rintro _ ⟨v, hv, rfl⟩; simpa [hzero] using hv⟩
  | succ a ih =>
    obtain ⟨K, hK, hsub⟩ := ih
    let D := convexHull ℝ (step a '' K)
    refine ⟨closure D, (isBounded_convexHull.mpr (hK.image (hc a)).isBounded).isCompact_closure, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    apply subset_closure
    have hvh := (hsucc a.val ▸ hv).2
    have bound : convexHull ℝ {v : (j : Fin (L+1)) → Fin (w j) → ℝ |
        (∃ u ∈ C a.val, ∀ j : Fin (L+1), j.val = a.val → v j = u j) ∧
        ∀ b : Fin L, a.val ≤ b.val → b.val < a.val+1 →
          v b.succ = step b (v b.castSucc)} ⊆
        (fun v => v a.succ) ⁻¹' D := by
      apply convexHull_min
      · intro z hz
        obtain ⟨⟨u, hu, hzu⟩, he⟩ := hz
        change z a.succ ∈ D
        rw [he a le_rfl (by omega)]
        apply subset_convexHull ℝ _
        refine ⟨z a.castSucc, ?_, rfl⟩
        rw [hzu a.castSucc rfl]
        exact hsub ⟨u, hu, rfl⟩
      · exact (convex_convexHull ℝ _).linear_preimage (LinearMap.proj a.succ)
    exact bound hvh

-- formalizer:machinery-end

end Lemma_3p2.Machinery
