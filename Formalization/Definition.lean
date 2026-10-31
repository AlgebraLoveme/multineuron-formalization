module
public import Mathlib

@[expose] public section

namespace Definition

/-- Architecture data. A layer is either a matrix with bias or a coordinatewise
activation with equal input and output widths. In particular, consecutive affine
identities remain separate layers. Specialize `σ` to `fun t => max t 0` for ReLU.
The activation parameter is retained in the type for a uniform network interface;
its action is interpreted by the trajectory definitions below. -/
def NetworkSemantics (_σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ) : Type :=
  { layers : (i : Fin L) →
      (Matrix (Fin (w i.succ)) (Fin (w i.castSucc)) ℝ ×
        (Fin (w i.succ) → ℝ)) ⊕ PLift (w i.castSucc = w i.succ) //
    ∀ j, 0 < w j }

/-- Sequential ideal window relaxation. The first component gives every
accumulated constraint set (stage zero is input membership); the other two give
coordinate extrema after all windows. The caller supplies `1 ≤ r ≤ L`.
Full trajectory cylinders let every window retain its intermediate variables.
No assertion of polyhedrality is made for general activations. -/
noncomputable def WindowRelaxation (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (r : ℕ) (_hr : 1 ≤ r) (_hL : r ≤ L) :
    (ℕ → Set ((j : Fin (L + 1)) → Fin (w j) → ℝ)) ×
      (Fin (w (Fin.last L)) → ℝ) × (Fin (w (Fin.last L)) → ℝ) :=
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) →
      (Fin (w i.succ) → ℝ) := fun i x =>
    match N.val i with
    | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  let T := (j : Fin (L + 1)) → Fin (w j) → ℝ
  let initial : Set T := {v | v 0 ∈ X}
  let advance : ℕ → Set T → Set T := fun s C =>
    C ∩ convexHull ℝ {v : T |
      (∃ u ∈ C, ∀ j : Fin (L + 1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s + r →
        v i.succ = step i (v i.castSucc)}
  let stages : ℕ → Set T := fun k =>
    Nat.rec initial (fun s C => advance s C) k
  let feasible := stages (L - r + 1)
  (stages,
    (fun j => sInf ((fun v : T => v (Fin.last L) j) '' feasible)),
    (fun j => sSup ((fun v : T => v (Fin.last L) j) '' feasible)))

/-- Definition J.4. Only one nontrivial midpoint identity is required;
continuity, non-polynomiality and injectivity are independent conditions. -/
def AdmissibleActivation (σ : ℝ → ℝ) : Prop :=
  Continuous σ ∧
    (¬ ∃ p : Polynomial ℝ, ∀ t, σ t = p.eval t) ∧
    Function.Injective σ ∧
    ∃ a b : ℝ, a < b ∧ σ ((a + b) / 2) = (σ a + σ b) / 2

/-- Finite real Hausdorff distance on independently nonempty compact Euclidean
sets. The proof parameters explicitly delimit the intended domain. -/
noncomputable def HausdorffDistance (d : ℕ)
    (H K : Set (EuclideanSpace ℝ (Fin d)))
    (_hH : H.Nonempty) (_cH : IsCompact H)
    (_hK : K.Nonempty) (_cK : IsCompact K) : ℝ :=
  max (sSup ((fun x => sInf ((fun y => ‖x - y‖) '' K)) '' H))
      (sSup ((fun y => sInf ((fun x => ‖x - y‖) '' H)) '' K))

/-- Branch-and-bound semantics for ReLU. `multi = false` uses the all-stable
rule; `multi = true` uses convex polytope input and prefix images. The result is
worst-case leaf count together with all terminal outcomes (leaf count, lower
bound, upper bound). Trees are finite prefix-closed sets of Boolean addresses;
false/true denote the nonpositive/nonnegative child. Region membership uses the
original exact trajectory, so nonconvex intermediate regions are permitted.
Distinct addresses are counted even when exact regions overlap. -/
noncomputable def BranchAndBound (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : NetworkSemantics (fun t => max t 0) L w)
    (X : Set (Fin (w 0) → ℝ)) (multi : Bool) :
    ℕ × Set (ℕ × (Fin (w (Fin.last L)) → ℝ) ×
      (Fin (w (Fin.last L)) → ℝ)) := by
  classical
  let T := (j : Fin (L + 1)) → Fin (w j) → ℝ
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) →
      (Fin (w i.succ) → ℝ) := fun i x =>
    match N.val i with
    | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => max (x (Fin.cast h.down.symm j)) 0
  let exact : Set T := {v | v 0 ∈ X ∧
    ∀ i, v i.succ = step i (v i.castSucc)}
  let Neuron := {i : Fin L // ∃ h, N.val i = Sum.inr h}
  let Address := List Bool
  let Label := (i : Neuron) × Fin (w i.val.castSucc)
  let stable (R : Set T) (n : Label) : Prop :=
    (∀ v ∈ R, 0 ≤ v n.1.val.castSucc n.2) ∨
    (∀ v ∈ R, v n.1.val.castSucc n.2 ≤ 0)
  let poly (j : Fin (L + 1)) (S : Set (Fin (w j) → ℝ)) : Prop :=
    ∃ vertices : Finset (Fin (w j) → ℝ), S = convexHull ℝ (↑vertices : Set _)
  let closed (R : Set T) : Prop :=
    if multi then ∀ j, poly j ((fun v : T => v j) '' R)
    else ∀ n, stable R n
  -- Labels are optional globally so networks without activation neurons still
  -- admit the one-leaf execution. An internal node must carry an actual label.
  let outcomes : Set (ℕ × (Fin (w (Fin.last L)) → ℝ) ×
      (Fin (w (Fin.last L)) → ℝ)) := {o |
    ∃ (nodes : Finset Address) (labels : Address → Option Label)
      (regions : Address → Set T),
      [] ∈ nodes ∧ regions [] = exact ∧
      (∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) ∧
      (∀ a ∈ nodes,
        (closed (regions a) ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
        (¬closed (regions a) ∧ ∃ n, labels a = some n ∧
          ¬stable (regions a) n ∧ a ++ [false] ∈ nodes ∧ a ++ [true] ∈ nodes ∧
          regions (a ++ [false]) = {v ∈ regions a | v n.1.val.castSucc n.2 ≤ 0} ∧
          regions (a ++ [true]) = {v ∈ regions a | 0 ≤ v n.1.val.castSucc n.2})) ∧
      let leaves := nodes.filter (fun a => closed (regions a))
      o.1 = leaves.card ∧
      o.2.1 = (fun j => sInf {b : ℝ | ∃ a ∈ leaves,
        b = sInf ((fun v : T => v (Fin.last L) j) '' regions a)}) ∧
      o.2.2 = (fun j => sSup {b : ℝ | ∃ a ∈ leaves,
        b = sSup ((fun v : T => v (Fin.last L) j) '' regions a)})}
  exact (sSup (Prod.fst '' outcomes), outcomes)

end Definition


-- Export-only notation: expands to original projections; no new mathematical declarations.
notation:max "relaxation.stages(" value ")" => value.1


-- Export-only notation: expands to original projections; no new mathematical declarations.
notation:max "WindowRelaxation.stages(" value ")" => value.1
