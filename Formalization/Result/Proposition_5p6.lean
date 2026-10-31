module
public import Formalization.Result.helpers.Proposition_5p6.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Gp1

open Definition

public section

namespace Proposition_5p6

theorem result_5_6 :
  let σ : ℝ → ℝ := fun t => max t 0
  let poly : {d : ℕ} → Set (Fin d → ℝ) → Prop := fun {d} X =>
    ∃ V : Finset (Fin d → ℝ), X = convexHull ℝ (↑V : Set _)
  ∀ (L : ℕ) (w : Fin (L + 1) → ℕ) (N : NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)), X.Nonempty → poly X →
    (BranchAndBound L w N X true).1 ≤ (BranchAndBound L w N X false).1 := (by
  -- formalizer:proof-begin
  classical
  intro σ poly L w N X hX hpoly
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
  let closed (multi : Bool) (R : Set T) : Prop :=
    if multi then ∀ j, poly j ((fun v : T => v j) '' R)
    else ∀ n, stable R n
  -- Labels are optional globally so networks without activation neurons still
  -- admit the one-leaf execution. An internal node must carry an actual label.
  let outcomes (multi : Bool) : Set (ℕ × (Fin (w (Fin.last L)) → ℝ) ×
      (Fin (w (Fin.last L)) → ℝ)) := {o |
    ∃ (nodes : Finset Address) (labels : Address → Option Label)
      (regions : Address → Set T),
      [] ∈ nodes ∧ regions [] = exact ∧
      (∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) ∧
      (∀ a ∈ nodes,
        (closed multi (regions a) ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
        (¬closed multi (regions a) ∧ ∃ n, labels a = some n ∧
          ¬stable (regions a) n ∧ a ++ [false] ∈ nodes ∧ a ++ [true] ∈ nodes ∧
          regions (a ++ [false]) = {v ∈ regions a | v n.1.val.castSucc n.2 ≤ 0} ∧
          regions (a ++ [true]) = {v ∈ regions a | 0 ≤ v n.1.val.castSucc n.2})) ∧
      let leaves := nodes.filter (fun a => closed multi (regions a))
      o.1 = leaves.card ∧
      o.2.1 = (fun j => sInf {b : ℝ | ∃ a ∈ leaves,
        b = sInf ((fun v : T => v (Fin.last L) j) '' regions a)}) ∧
      o.2.2 = (fun j => sSup {b : ℝ | ∃ a ∈ leaves,
        b = sSup ((fun v : T => v (Fin.last L) j) '' regions a)})}
  change sSup (Prod.fst '' outcomes true) ≤ sSup (Prod.fst '' outcomes false)
  let z : Label → T → ℝ := fun n v => v n.1.val.castSucc n.2
  let valid := fun (stop : Set T → Prop) (nodes : Finset Address)
      (labels : Address → Option Label) (regions : Address → Set T) =>
    [] ∈ nodes ∧ (∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) ∧
    (∀ a ∈ nodes,
      (stop (regions a) ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
      (¬stop (regions a) ∧ ∃ n, labels a = some n ∧
        ¬stable (regions a) n ∧ a ++ [false] ∈ nodes ∧ a ++ [true] ∈ nodes ∧
        regions (a ++ [false]) = {v ∈ regions a | z n v ≤ 0} ∧
        regions (a ++ [true]) = {v ∈ regions a | 0 ≤ z n v}))
  -- Appendix G, stable cells: retain every ancestral halfspace. Compatible
  -- ReLU signs make each prefix affine; the converse trajectory argument
  -- identifies the region with X cut by those affine inequalities.
  let cell (R : Set T) : Prop := ∃ H : Finset (T →ᵃ[ℝ] ℝ),
    ∀ v, v ∈ R ↔ v ∈ exact ∧ ∀ f ∈ H, f v ≤ 0
  have root_cell : cell exact := ⟨∅, by simp⟩
  let coordinate : Label → T →ᵃ[ℝ] ℝ := fun n =>
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin (w n.1.val.castSucc) => ℝ) n.2).comp
      (LinearMap.proj (R := ℝ) (φ := fun j : Fin (L+1) => Fin (w j) → ℝ)
        n.1.val.castSucc)).toAffineMap
  have cell_split : ∀ R n, cell R →
      cell {v ∈ R | z n v ≤ 0} ∧ cell {v ∈ R | 0 ≤ z n v} := by
    rintro R n ⟨H, hH⟩
    constructor
    · refine ⟨insert (coordinate n) H, ?_⟩
      intro v
      simp only [Set.mem_setOf_eq, hH, Finset.mem_insert, forall_eq_or_imp]
      change ((v ∈ exact ∧ ∀ f ∈ H, f v ≤ 0) ∧ z n v ≤ 0) ↔
        (v ∈ exact ∧ z n v ≤ 0 ∧ ∀ f ∈ H, f v ≤ 0)
      tauto
    · refine ⟨insert (-coordinate n) H, ?_⟩
      intro v
      simp only [Set.mem_setOf_eq, hH, Finset.mem_insert, forall_eq_or_imp]
      change ((v ∈ exact ∧ ∀ f ∈ H, f v ≤ 0) ∧ 0 ≤ z n v) ↔
        (v ∈ exact ∧ -z n v ≤ 0 ∧ ∀ f ∈ H, f v ≤ 0)
      rw [neg_nonpos]
      tauto
  have stable_closed : ∀ R, cell R → (∀ n, stable R n) → closed true R := by
    rintro R ⟨H, hH⟩ hs
    obtain ⟨V, hV⟩ := hpoly
    apply Machinery.stable_network_cell N step (fun _ _ => rfl) V H R
    · intro v
      rw [hH]
      change ((v 0 ∈ X ∧ ∀ i, v i.succ = step i (v i.castSucc)) ∧ _) ↔ _
      rw [hV]
      tauto
    · intro i hi k
      exact hs ⟨⟨i, hi⟩, k⟩
  have root_nonempty : exact.Nonempty := by
    obtain ⟨x, hx⟩ := hX
    let trajectory : T := Fin.induction x (fun i prev => step i prev)
    refine ⟨trajectory, hx, ?_⟩
    intro i
    exact Fin.induction_succ (motive := fun j => Fin (w j) → ℝ) x (fun i prev => step i prev) i
  -- Every reachable node retains its ancestral constraints and is nonempty:
  -- an unstable preactivation has a strictly negative and a strictly positive
  -- witness, so both weak-sign children contain a trajectory.
  have reachable : ∀ m nodes labels regions,
      valid (closed m) nodes labels regions → regions [] = exact →
      ∀ a ∈ nodes, cell (regions a) ∧ (regions a).Nonempty := by
    intro m nodes labels regions hv hr
    apply Machinery.tree_region_invariant
      (fun R => cell R ∧ R.Nonempty) nodes regions hv.2.1
    · rw [hr]
      exact ⟨root_cell, root_nonempty⟩
    · intro a ha b hb hR
      rcases hv.2.2 a ha with h | h
      · cases b
        · exact False.elim (h.2.1 hb)
        · exact False.elim (h.2.2 hb)
      · obtain ⟨_, n, _, hi, _, _, hf, ht⟩ := h
        have hc := cell_split (regions a) n hR.1
        have hn := Machinery.unstable_children_nonempty z (regions a) n hi
        cases b
        · rw [hf]; exact ⟨hc.1, hn.1⟩
        · rw [ht]; exact ⟨hc.2, hn.2⟩
  -- Stable cells close in P₁. Split-count induction therefore constructs a
  -- complete P₁ execution, stopping earlier whenever its polytope rule holds.
  -- The same construction gives an S execution, including neuron-free networks.
  have nonempty_outcomes : ∀ m, (outcomes m).Nonempty := by
    intro m
    have terminal : ∀ R, cell R → (∀ n, stable R n) → closed m R := by
      intro R hR hs
      cases m
      · exact hs
      · exact stable_closed R hR hs
    obtain ⟨nodes, labels, regions, hn, hr, hp, hv⟩ :=
      Machinery.stopping_tree_exists z cell (closed m) terminal cell_split exact root_cell
    let leaves := nodes.filter (fun a => closed m (regions a))
    refine ⟨(leaves.card,
      (fun j => sInf {b : ℝ | ∃ a ∈ leaves,
        b = sInf ((fun v : T => v (Fin.last L) j) '' regions a)}),
      (fun j => sSup {b : ℝ | ∃ a ∈ leaves,
        b = sSup ((fun v : T => v (Fin.last L) j) '' regions a)})),
      nodes, labels, regions, hn, hr, hp, hv, rfl, rfl, rfl⟩
  have leaf_eq : ∀ stop nodes labels regions, valid stop nodes labels regions →
      nodes.filter (fun a => stop (regions a)) =
      nodes.filter (fun a => a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) := by
    intro stop nodes labels regions hv
    apply Machinery.closed_filter_eq_leaves
    intro a ha
    rcases hv.2.2 a ha with h | h
    · exact Or.inl h
    · obtain ⟨hc, n, _, _, hf, _⟩ := h
      exact Or.inr ⟨hc, hf⟩
  -- Appendix G, termination: a split fixes its selected sign, and restrictions
  -- preserve all earlier fixed signs. Thus depth is bounded by the neuron count.
  -- Finitely many Boolean addresses up to that depth bound every leaf count.
  let addresses :=
    (Machinery.bounded_addresses_finite
      (Fintype.card Label)).toFinset
  have bounded : ∀ m, BddAbove (Prod.fst '' outcomes m) := by
    intro m
    refine ⟨addresses.card, ?_⟩
    rintro _ ⟨o, ho, rfl⟩
    obtain ⟨nodes, labels, regions, hn, hr, hp, hv, ho⟩ := ho
    have depth :=
      Machinery.tree_depth_bound
        z nodes regions hp (by
          intro a ha b hb
          rcases hv a ha with h | h
          · cases b
            · exact False.elim (h.2.1 hb)
            · exact False.elim (h.2.2 hb)
          · obtain ⟨_, n, _, hns, _, _, hf, ht⟩ := h
            refine ⟨n, hns, ?_, ?_⟩
            · cases b
              · rw [hf]; exact fun _ hv => hv.1
              · rw [ht]; exact fun _ hv => hv.1
            · cases b
              · rw [hf]; exact Or.inr (fun _ hv => hv.2)
              · rw [ht]; exact Or.inl (fun _ hv => hv.2))
    have sub : nodes ⊆ addresses := by
      intro a ha
      simpa only [addresses, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using depth a ha
    rw [ho.1]
    exact (Finset.card_filter_le _ _).trans (Finset.card_le_card sub)
  -- Finite depth bounds and nonempty executions make each supremum an
  -- attained maximum. Choose a maximizing P₁ tree before extending its leaves.
  have attained : ∀ m, ∃ o ∈ outcomes m, o.1 = sSup (Prod.fst '' outcomes m) := by
    intro m
    exact Nat.sSup_mem ((nonempty_outcomes m).image Prod.fst) (bounded m)
  obtain ⟨o, ho, hmax⟩ := attained true
  rw [← hmax]
  obtain ⟨nodes, labels, regions, hn, hr, hp, hv, ho⟩ := ho
  have old_valid : valid (closed true) nodes labels regions := ⟨hn, hp, hv⟩
  -- G.1 certifies the prescribed stopping test at every terminal region of
  -- this execution. Nonemptiness and exact trajectories come from reachability;
  -- all prefix polytopes are precisely the P₁ closing condition. For L = 0
  -- there is only the identity prefix, and no relaxation window is required.
  have terminal_bounds : ∀ (hL : 0 < L) a, a ∈ nodes → closed true (regions a) →
      let B := WindowRelaxation σ L w N ((fun v => v 0) '' regions a) 1 (by omega) hL
      ∀ k, B.2.1 k = sInf ((fun v => v (Fin.last L) k) '' regions a) ∧
        B.2.2 k = sSup ((fun v => v (Fin.last L) k) '' regions a) := by
    intro hL a ha hclosed
    obtain ⟨⟨H, hH⟩, hne⟩ := reachable true nodes labels regions old_valid hr a ha
    apply Machinery.closed_region_bounds N hL (regions a) hne
    · intro v hv i
      exact (((hH v).mp hv).1).2 i
    · exact hclosed
  obtain ⟨nodes', labels', regions', hsub, hr', hv'⟩ :=
    Machinery.stable_tree_refinement
      z (closed true) nodes labels regions old_valid
  have new_valid : valid (closed false) nodes' labels' regions' := hv'
  let leaves := nodes'.filter (fun a => closed false (regions' a))
  let out : ℕ × (Fin (w (Fin.last L)) → ℝ) × (Fin (w (Fin.last L)) → ℝ) :=
    (leaves.card,
      (fun j => sInf {b : ℝ | ∃ a ∈ leaves,
        b = sInf ((fun v : T => v (Fin.last L) j) '' regions' a)}),
      (fun j => sSup {b : ℝ | ∃ a ∈ leaves,
        b = sSup ((fun v : T => v (Fin.last L) j) '' regions' a)}))
  have hout : out ∈ outcomes false := by
    exact ⟨nodes', labels', regions', new_valid.1, hr'.trans hr,
      new_valid.2.1, new_valid.2.2, rfl, rfl, rfl⟩
  -- Each original terminal node has a terminal descendant in the extension;
  -- distinct terminal addresses have disjoint descendant sets, even when
  -- their exact input regions overlap. Hence N(T) ≤ N(T_S).
  have count : o.1 ≤ out.1 := by
    rw [ho.1]
    change (nodes.filter (fun a => closed true (regions a))).card ≤ leaves.card
    dsimp only [leaves]
    have hOld := leaf_eq _ _ _ _ old_valid
    have hNew := leaf_eq _ _ _ _ new_valid
    have hcount := Machinery.terminal_count_mono
      nodes nodes' hsub hp
    convert hcount using 1
    · congr 1
      ext a
      simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hOld) a
    · exact congrArg Finset.card hNew
  -- N(T_S) is bounded by the attained worst-case S count. Since T was a
  -- maximizing P₁ execution, this gives Proposition 5.6.
  exact count.trans (le_csSup (bounded false) ⟨out, hout, rfl⟩)
  -- formalizer:proof-end
)

end Proposition_5p6
