module
public import Formalization.Definition
public import Mathlib

public section


open Definition

public section

namespace Axioms

/-- Arora et al., Theorem 2.1: the representation direction only. -/
axiom ExternalReLURepresentation (d : ℕ) (hd : 0 < d)
    (h : (Fin d → ℝ) → ℝ) (hh : (Continuous h ∧ ∃ (n : ℕ) (k : Fin n → ℕ)
      (A : (i : Fin n) → Fin (k i) → Fin d → ℝ)
      (b : (i : Fin n) → Fin (k i) → ℝ)
      (c : Fin n → Fin d → ℝ) (e : Fin n → ℝ),
      (∀ x : Fin d → ℝ, ∃ i, ∀ j, (∑ t, A i j t * x t) ≤ b i j) ∧
      (∀ i x, (∀ j, (∑ t, A i j t * x t) ≤ b i j) →
        h x = (∑ t, c i t * x t) + e i))) :
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
  ∃ f : Net d 1, (∀ x, eval f x 0 = h x) ∧
    ∃ i : Fin f.val.1, i.val + 1 = f.val.1 ∧
      ∃ A b, f.val.2.2.val i = Sum.inl (A, b)

/-- Leshno et al., Theorem 1: scalar compact-uniform density with biases
and arbitrary real linear output coefficients. -/
axiom ExternalUniversalApproximation (σ : ℝ → ℝ)
    (hσ : Continuous σ) (hnp : ¬ ∃ p : Polynomial ℝ, ∀ t, σ t = p.eval t)
    (d : ℕ) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (h : (Fin d → ℝ) → ℝ) (hh : ContinuousOn h K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (W : Fin n → Fin d → ℝ)
      (b : Fin n → ℝ) (c : ℝ),
      ∀ x ∈ K, |c + (∑ i, a i * σ ((∑ j, W i j * x j) + b i)) - h x| < ε

end Axioms
