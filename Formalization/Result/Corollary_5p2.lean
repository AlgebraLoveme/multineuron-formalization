module
public import Formalization.Result.helpers.Corollary_5p2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Theorem_5p1

open Axioms Definition

public section

namespace Corollary_5p2

theorem result_5_2 :
  let σ : ℝ → ℝ := fun t => max t 0
  let Net : ℕ → ℕ → Type := fun d m =>
    { p : (L : ℕ) × (w : Fin (L + 1) → ℕ) × NetworkSemantics σ L w //
      p.2.1 0 = d ∧ p.2.1 (Fin.last p.1) = m ∧ 0 < p.1 }
  let run : {d m : ℕ} → (f : Net d m) →
      (j : Fin (f.val.1 + 1)) → (Fin (f.val.2.1 0) → ℝ) →
      (Fin (f.val.2.1 j) → ℝ) := fun {_ _} f =>
    Fin.induction (fun x => x) (fun i prev x =>
      match f.val.2.2.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * prev x k) + b j
      | Sum.inr h => fun j => σ (prev x (Fin.cast h.down.symm j)))
  let eval : {d m : ℕ} → Net d m → (Fin d → ℝ) → (Fin m → ℝ) :=
    fun {_ _} f x j => run f (Fin.last f.val.1)
      (fun k => x (Fin.cast f.property.1 k)) (Fin.cast f.property.2.1.symm j)
  let poly : {d : ℕ} → Set (Fin d → ℝ) → Prop := fun {d} X =>
    ∃ V : Finset (Fin d → ℝ), X = convexHull ℝ (↑V : Set _)
  let bounds : {d m : ℕ} → (f : Net d m) → Set (Fin d → ℝ) →
      (r : ℕ) → 1 ≤ r → r ≤ f.val.1 → (Fin m → ℝ) × (Fin m → ℝ) :=
    fun {_ _} f X r hr hL =>
      let R := WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2
        ((fun x k => x (Fin.cast f.property.1 k)) '' X) r hr hL
      ((fun j => R.2.1 (Fin.cast f.property.2.1.symm j)),
       (fun j => R.2.2 (Fin.cast f.property.2.1.symm j)))
  ∀ (d : ℕ), 0 < d → ∀ (h : (Fin d → ℝ) → ℝ), (Continuous h ∧ ∃ (n : ℕ) (k : Fin n → ℕ)
      (A : (i : Fin n) → Fin (k i) → Fin d → ℝ)
      (b : (i : Fin n) → Fin (k i) → ℝ)
      (c : Fin n → Fin d → ℝ) (e : Fin n → ℝ),
      (∀ x : Fin d → ℝ, ∃ i, ∀ j, (∑ t, A i j t * x t) ≤ b i j) ∧
      (∀ i x, (∀ j, (∑ t, A i j t * x t) ≤ b i j) →
        h x = (∑ t, c i t * x t) + e i)) →
    ∀ (X : Set (Fin d → ℝ)), X.Nonempty → poly X → ¬X.Subsingleton →
    ∃ g : Net d 1, (∀ x ∈ X, eval g x 0 = h x) ∧
      let B := bounds g X 1 (by omega) g.property.2.2
      B.1 0 = sInf (h '' X) ∧ B.2 0 = sSup (h '' X) := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d hd h hh X hX hpoly hsingle
  -- Appendix G, equation (1): external representability supplies a ReLU
  -- network equal to the given finite piecewise-linear function everywhere.
  obtain ⟨f, hf, _⟩ := ExternalReLURepresentation d hd h hh
  -- Equation (2): Theorem 5.1 gives agreement on X and exact bounds
  -- for the representing network's scalar image.
  obtain ⟨g, hg, hbounds⟩ := Theorem_5p1.result_5_1 d 1 f X hX hpoly hsingle
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    exact (congrFun (hg x hx) 0).trans (hf x)
  -- Equations (1) and (2) identify the scalar images and both extrema.
  have himage : (fun x => eval f x 0) '' X = h '' X := by
    have heq : (fun x => eval f x 0) = h := funext hf
    rw [heq]
  dsimp only
  rw [← himage]
  exact hbounds 0
  -- formalizer:proof-end
)

end Corollary_5p2
