module
public import Formalization.Result.helpers.Lemma_Gp1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_3p1

open Definition

public section

namespace Lemma_Gp1

theorem result_G_1 :
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
  ∀ (d m : ℕ) (f : Net d m) (X : Set (Fin d → ℝ)),
    X.Nonempty → poly X →
    (∀ j : Fin (f.val.1 + 1), 1 ≤ j.val →
      poly (run f j '' ((fun x k => x (Fin.cast f.property.1 k)) '' X))) →
    let B := bounds f X 1 (by omega) f.property.2.2
    ∀ j, B.1 j = sInf ((fun x => eval f x j) '' X) ∧
      B.2 j = sSup ((fun x => eval f x j) '' X) := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d m f X hX hpoly hprefix
  let L := f.val.1
  let w := f.val.2.1
  let Y := (fun x k => x (Fin.cast f.property.1 k)) '' X
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ) :=
    fun i x => match (f.val.2.2 : NetworkSemantics σ L w).val i with
    | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  let C := relaxation.stages(WindowRelaxation σ L w f.val.2.2 Y 1 (by omega) f.property.2.2)
  have hzero : C 0 = {v | v 0 ∈ Y} := rfl
  have hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+1 →
        v i.succ = step i (v i.castSucc)} := by
    intro s
    simp only [C, WindowRelaxation]
    congr 2
    ext v
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    cases h : f.val.2.2.val i with
    | inl ab => rcases ab with ⟨A, b⟩; simp [step, h, w, L]
    | inr h => simp [step, h, w, L]
  have run_zero : ∀ x, run f 0 x = x := fun _ => rfl
  have run_succ : ∀ i x, run f i.succ x = step i (run f i.castSucc x) := by
    intro i x
    simp only [run, Fin.induction_succ]
    rfl
  -- G.1: exact trajectories remain feasible at every stage, since each exact
  -- layer graph is contained in its convex hull. This gives S_j ⊆ projection.
  have sound : ∀ x ∈ Y, ∀ k, (fun j => run f j x) ∈ C k := by
    intro x hx
    exact Machinery.exact_mem_stages
      step Y C hzero hsucc (fun j => run f j x) hx (fun i => run_succ i x)
  -- Induct on layers. A graph point projects into S_(j+1); convexity of
  -- S_(j+1) keeps its entire graph hull in that same output cylinder.
  have projected : ∀ j : Fin (L+1), (fun v => v j) '' C j.val = run f j '' Y := by
    intro j
    induction j using Fin.induction with
    | zero =>
      ext z
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v 0, hv, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨fun j => run f j x, sound x hx 0, rfl⟩
    | succ i ih =>
      apply Set.Subset.antisymm
      · rintro z ⟨v, hv, rfl⟩
        have hc : Convex ℝ (run f i.succ '' Y) := by
          obtain ⟨V, hV⟩ := hprefix i.succ (by simp)
          rw [hV]
          exact convex_convexHull ℝ _
        have inclusion : {v : (j : Fin (L+1)) → Fin (w j) → ℝ | (∃ u ∈ C i.val,
            ∀ j : Fin (L+1), j.val = i.val → v j = u j) ∧
            ∀ a : Fin L, i.val ≤ a.val → a.val < i.val+1 →
              v a.succ = step a (v a.castSucc)} ⊆
            (fun v => v i.succ) ⁻¹' (run f i.succ '' Y) := by
          rintro t ⟨⟨u, hu, htu⟩, ht⟩
          have hui : u i.castSucc ∈ run f i.castSucc '' Y := ih ▸ ⟨u, hu, rfl⟩
          obtain ⟨x, hx, he⟩ := hui
          refine ⟨x, hx, ?_⟩
          change run f i.succ x = t i.succ
          rw [run_succ, ht i le_rfl (by omega), htu i.castSucc rfl, he]
        have hh := convexHull_min inclusion (hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun j : Fin (L+1) => Fin (w j) → ℝ) i.succ))
        exact hh ((hsucc i.val ▸ hv).2)
      · rintro z ⟨x, hx, rfl⟩
        exact ⟨fun j => run f j x, sound x hx _, rfl⟩
  -- At the final layer the projection is exactly f(X). Coordinate images
  -- coincide, hence the defining infimum and supremum give both exact bounds.
  have final_projection := projected (Fin.last L)
  intro B j
  have coord : (fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm j)) '' C L =
      (fun x => eval f x j) '' X := by
    have hh := congrArg (fun S : Set (Fin (w (Fin.last L)) → ℝ) =>
      (fun z => z (Fin.cast f.property.2.1.symm j)) '' S) final_projection
    simpa only [Y, eval, Set.image_image] using hh
  change sInf ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm j)) '' C (L-1+1)) = _ ∧
    sSup ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm j)) '' C (L-1+1)) = _
  have hL : L-1+1 = L := by have := f.property.2.2; dsimp [L]; omega
  rw [hL, coord]
  exact ⟨rfl, rfl⟩
  -- formalizer:proof-end
)

end Lemma_Gp1
