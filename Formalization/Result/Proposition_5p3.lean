module
public import Formalization.Result.helpers.Proposition_5p3.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Gp1

open Definition

public section

namespace Proposition_5p3

theorem result_5_3 :
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
  ∀ (d m n : ℕ) (f : Net d m), f.val.1 = 2 * n + 1 →
    (∀ i : Fin f.val.1,
      (Even i.val → ∃ A b, f.val.2.2.val i = Sum.inl (A,b)) ∧
      (Odd i.val → ∃ h, f.val.2.2.val i = Sum.inr h)) →
    ∀ (X : Set (Fin d → ℝ)), X.Nonempty → poly X → ¬X.Subsingleton →
    ∀ (ν : ℕ), 0 < ν → ∀ (H : Fin ν → Set (Fin d → ℝ)),
    (∀ k, (H k).Nonempty ∧ poly (H k) ∧ H k ⊆ X) →
    eval f '' X = ⋃ k, eval f '' H k →
    (∀ (k : Fin ν) (j : Fin (f.val.1 + 1)), 3 ≤ j.val → Odd j.val →
      poly (run f j '' ((fun x t => x (Fin.cast f.property.1 t)) '' H k))) →
    ∀ j,
      sInf ((fun x => eval f x j) '' X) =
        sInf (Set.range (fun k => (bounds f (H k) 1 (by omega) f.property.2.2).1 j)) ∧
      sSup ((fun x => eval f x j) '' X) =
        sSup (Set.range (fun k => (bounds f (H k) 1 (by omega) f.property.2.2).2 j)) := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d m n f hdepth halt X hX hpoly hns ν hν H hH hcover hprefix
  let L := f.val.1
  let w := f.val.2.1
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ) :=
    fun i x => match (f.val.2.2 : NetworkSemantics σ L w).val i with
    | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  have run_succ : ∀ i x, run f i.succ x = step i (run f i.castSucc x) := by
    intro i x
    simp only [run, Fin.induction_succ]
    rfl
  -- Continuity and finite convex hulls make every coordinate extremum finite.
  have continuous_run : ∀ j : Fin (L+1), Continuous (run f j) := by
    intro j
    induction j using Fin.induction with
    | zero => exact continuous_id
    | succ i ih =>
      have he : run f i.succ = fun x => step i (run f i.castSucc x) := funext (run_succ i)
      rw [he]
      cases hh : f.val.2.2.val i with
      | inl ab =>
        rcases ab with ⟨A,b⟩
        simp only [step, hh]
        change Continuous (fun x j => (∑ t, A j t * run f i.castSucc x t) + b j)
        exact continuous_pi fun j => (continuous_finset_sum _ fun t _ =>
          continuous_const.mul ((continuous_apply t).comp ih)).add continuous_const
      | inr h =>
        simp only [step, hh]
        change Continuous (fun x j => max (run f i.castSucc x (Fin.cast h.down.symm j)) 0)
        exact continuous_pi fun j => ((continuous_apply _).comp ih).max continuous_const
  have ceval : Continuous (eval f) := by
    apply continuous_pi
    intro j
    exact ((continuous_apply _).comp (continuous_run (Fin.last L))).comp
      (continuous_pi fun k => continuous_apply _)
  have compact_poly : ∀ {a} {S : Set (Fin a → ℝ)}, poly S → IsCompact S := by
    intro a S ⟨V,hV⟩
    rw [hV]
    exact V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have part_exact : ∀ k j,
      (bounds f (H k) 1 (by omega) f.property.2.2).1 j = sInf ((fun x => eval f x j) '' H k) ∧
      (bounds f (H k) 1 (by omega) f.property.2.2).2 j = sSup ((fun x => eval f x j) '' H k) := by
    intro k
    let L := f.val.1
    let w := f.val.2.1
    let Y := (fun x k => x (Fin.cast f.property.1 k)) '' H k
    let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ) :=
      fun i x => match (f.val.2.2 : NetworkSemantics σ L w).val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
    let C := WindowRelaxation.stages(WindowRelaxation σ L w f.val.2.2 Y 1 (by omega) f.property.2.2)
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
    have convexY : Convex ℝ Y := by
      obtain ⟨V,hV⟩ := (hH k).2.1
      have hc : Convex ℝ (H k) := by
        rw [hV]
        exact convex_convexHull ℝ _
      exact hc.linear_image
        { toFun := fun x t => x (Fin.cast f.property.1 t)
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
    -- The first affine image is convex; later affine-ended images are convex
    -- by the hypothesis of Proposition 5.3 (Proposition 5.3, expanded G.1 induction).
    have checkpoint : ∀ j : Fin (L+1), Odd j.val → Convex ℝ (run f j '' Y) := by
      intro j hj
      by_cases h1 : j.val = 1
      · let i : Fin L := ⟨0, f.property.2.2⟩
        have hj' : j = i.succ := Fin.ext (by simpa [i] using h1)
        rw [hj']
        obtain ⟨A,b,hab⟩ := (halt i).1 (by exact ⟨0, rfl⟩)
        have he : run f i.succ = (fun x t => (∑ a, A t a * x a) + b t) := by
          funext x
          rw [run_succ]
          simp only [step, hab]
          rfl
        rw [he]
        have hh := Machinery.affine_image_hull A b Y
        change (fun x j => (∑ a, A j a * x a) + b j) '' convexHull ℝ Y = _ at hh
        rw [convexY.convexHull_eq] at hh
        rw [hh]
        exact convex_convexHull ℝ _
      · obtain ⟨V,hV⟩ := hprefix k j (by obtain ⟨a,ha⟩ := hj; omega) hj
        rw [hV]
        exact convex_convexHull ℝ _
    -- Exact trajectories belong to every stage because each graph is
    -- contained in its hull; this supplies the reverse projection inclusion.
    have sound : ∀ x ∈ Y, ∀ t, (fun j => run f j x) ∈ C t := by
      intro x hx
      exact Lemma_Gp1.Machinery.exact_mem_stages
        step Y C hzero hsucc (fun j => run f j x) hx (fun i => run_succ i x)
    -- Induct through all layers with a convex-hull enclosure. Affine layers
    -- commute with the hull; ReLU layers receive an exact convex checkpoint.
    have enclosed : ∀ j : Fin (L+1), ∀ v ∈ C j.val,
        v j ∈ convexHull ℝ (run f j '' Y) := by
      intro j
      induction j using Fin.induction with
      | zero =>
        intro v hv
        exact subset_convexHull ℝ _ ⟨v 0, hv, rfl⟩
      | succ i ih =>
        apply Machinery.stage_output_subset
          step C hsucc i _ (convex_convexHull ℝ _)
        intro u hu
        have hi := ih u hu
        rcases Nat.even_or_odd i.val with heven | hodd
        · obtain ⟨A,b,hab⟩ := (halt i).1 heven
          have hs : step i = (fun x t => (∑ a, A t a * x a) + b t) := by
            funext x; simp only [step, hab]; rfl
          have hm : step i (u i.castSucc) ∈ convexHull ℝ (step i '' (run f i.castSucc '' Y)) := by
            rw [hs, ← Machinery.affine_image_hull]
            exact ⟨u i.castSucc, hi, rfl⟩
          have heq : step i '' (run f i.castSucc '' Y) = run f i.succ '' Y := by
            rw [Set.image_image]
            congr 1
          rwa [heq] at hm
        · rw [(checkpoint i.castSucc hodd).convexHull_eq] at hi
          obtain ⟨x,hx,he⟩ := hi
          apply subset_convexHull
          exact ⟨x, hx, by rw [run_succ, he]⟩
    -- At the final affine checkpoint the hull collapses to the actual image,
    -- so the relaxation's coordinate infimum and supremum are exact.
    have finalconv : Convex ℝ (run f (Fin.last L) '' Y) :=
      checkpoint _ (by exact ⟨n, by simp [L, hdepth]⟩)
    have final_projection : (fun v => v (Fin.last L)) '' C L = run f (Fin.last L) '' Y := by
      apply Set.Subset.antisymm
      · rintro _ ⟨v,hv,rfl⟩
        have hh := enclosed (Fin.last L) v hv
        rwa [finalconv.convexHull_eq] at hh
      · rintro _ ⟨x,hx,rfl⟩
        exact ⟨fun j => run f j x, sound x hx L, rfl⟩
    intro j
    have coord : (fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm j)) '' C L =
        (fun x => eval f x j) '' H k := by
      have hh := congrArg (fun S : Set (Fin (w (Fin.last L)) → ℝ) =>
        (fun z => z (Fin.cast f.property.2.1.symm j)) '' S) final_projection
      simpa only [Y, eval, Set.image_image] using hh
    change sInf ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm j)) '' C (L-1+1)) = _ ∧
      sSup ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm j)) '' C (L-1+1)) = _
    have hL : L-1+1 = L := by have := f.property.2.2; dsimp [L]; omega
    rw [hL, coord]
    exact ⟨rfl,rfl⟩
  -- The finite image cover now aggregates the exact bounds on the parts
  -- into the global coordinatewise minimum and maximum.
  intro j
  haveI : Nonempty (Fin ν) := ⟨⟨0,hν⟩⟩
  have cc := (continuous_apply j).comp ceval
  have hc : (fun x => eval f x j) '' X = ⋃ k, (fun x => eval f x j) '' H k := by
    have hh := congrArg (fun S : Set (Fin m → ℝ) => (fun z => z j) '' S) hcover
    simpa only [Set.image_iUnion, Set.image_image] using hh
  have hh := Machinery.extrema_cover
    (fun k => (fun x => eval f x j) '' H k)
    (fun k => (hH k).1.image _) (fun k => (compact_poly (hH k).2.1).image cc)
    _ hc ((compact_poly hpoly).image cc)
  simpa only [(funext fun k => (part_exact k j).1), (funext fun k => (part_exact k j).2)] using hh
  -- formalizer:proof-end
)

end Proposition_5p3
