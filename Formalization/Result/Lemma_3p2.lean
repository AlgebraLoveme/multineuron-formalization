module
public import Formalization.Result.helpers.Lemma_3p2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_3p1

open Definition

public section

namespace Lemma_3p2

theorem result_3_2 :
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
    ∀ (i : Fin (f.val.1 + 1)), 1 ≤ i.val → i.val < f.val.1 →
    let X₀ := (fun x k => x (Fin.cast f.property.1 k)) '' X
    let H := convexHull ℝ (run f i '' X₀)
    let S : Set (Fin m → ℝ) := {y | ∃ v : (j : Fin (f.val.1 + 1)) →
        Fin (f.val.2.1 j) → ℝ,
      v i ∈ H ∧ (∀ j, y j = v (Fin.last f.val.1) (Fin.cast f.property.2.1.symm j)) ∧
      ∀ k : Fin f.val.1, i.val ≤ k.val →
        v k.succ = (match f.val.2.2.val k with
          | Sum.inl (A,b) => fun j => (∑ t, A j t * v k.castSucc t) + b j
          | Sum.inr h => fun j => σ (v k.castSucc (Fin.cast h.down.symm j)))}
    let B := bounds f X 1 (by omega) f.property.2.2
    ∀ j, B.1 j ≤ sInf ((fun y => y j) '' S) ∧
      sSup ((fun y => y j) '' S) ≤ B.2 j := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d m f X hX hp i hi hiL X₀ H S B
  let step : (a : Fin f.val.1) → (Fin (f.val.2.1 a.castSucc) → ℝ) →
      (Fin (f.val.2.1 a.succ) → ℝ) := fun a x =>
    match f.val.2.2.val a with
    | Sum.inl (A,b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  let C := WindowRelaxation.stages(WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2 X₀ 1 (by omega) f.property.2.2)
  have hzero : C 0 = {v | v 0 ∈ X₀} := rfl
  have hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (f.val.1+1), j.val = s → v j = u j) ∧
      ∀ a : Fin f.val.1, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)} := by
    intro s
    simp only [C, WindowRelaxation, step, Nat.rec_add_one]
    congr 1
    congr 1
    ext v
    apply and_congr Iff.rfl
    apply forall_congr'
    intro a
    cases h : f.val.2.2.val a with
    | inl p => rcases p with ⟨A, b⟩; rfl
    | inr h => rfl
  let castInput : (Fin d → ℝ) →ₗ[ℝ] (Fin (f.val.2.1 0) → ℝ) :=
    { toFun := fun x k => x (Fin.cast f.property.1 k)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  obtain ⟨V, hV⟩ := hp
  have cx : Convex ℝ X := by rw [hV]; exact convex_convexHull ℝ _
  have kx : IsCompact X := by rw [hV]; exact V.finite_toSet.isCompact_convexHull ℝ
  have cx₀ : Convex ℝ X₀ := cx.linear_image castInput
  have kx₀ : IsCompact X₀ := kx.image (by fun_prop)
  have nx₀ : X₀.Nonempty := hX.image _
  have runzero : ∀ x, run f 0 x = x := fun _ => rfl
  have runstep : ∀ x a, run f a.succ x = step a (run f a.castSucc x) := by
    intro x a
    simp only [run, Fin.induction_succ]
    rfl
  have sound : ∀ x ∈ X₀, ∀ k, (fun j => run f j x) ∈ C k := by
    intro x hx
    exact Machinery.exact_mem_stages
      step X₀ C hzero hsucc _ (by simpa [runzero] using hx) (runstep x)
  -- Appendix E, Lemma 3.2: the convex, sound prefix projection contains
  -- conv(f₁(X)), because every exact prefix trajectory satisfies its constraints.
  have convexC := Machinery.stages_convex
    step X₀ C hzero hsucc cx₀
  have hullsub : H ⊆ (fun v => v i) '' C i.val := by
    apply convexHull_min
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨fun j => run f j x, sound x hx i.val, rfl⟩
    · exact (convexC i.val).linear_image (LinearMap.proj i)
  -- As in Lemma 3.1, preserve the prefix and append the prescribed exact
  -- suffix. Each exact graph tuple belongs to the next graph hull, so every
  -- output in f₂(conv(f₁(X))) is feasible for the full relaxation.
  have included : ∀ y ∈ S, ∃ u ∈ C f.val.1,
      ∀ j, y j = u (Fin.last f.val.1) (Fin.cast f.property.2.1.symm j) := by
    intro y hy
    obtain ⟨v, hv, hy, he⟩ := hy
    obtain ⟨u, hu, hue⟩ :=
      Machinery.continue_suffix
        step X₀ C hzero hsucc i v (hullsub hv) he
    exact ⟨u, hu, fun j => (hy j).trans (congrFun hue _).symm⟩
  have nonemptyS : S.Nonempty := by
    obtain ⟨x, hx⟩ := nx₀
    refine ⟨fun j => run f (Fin.last f.val.1) x (Fin.cast f.property.2.1.symm j),
      (fun j => run f j x), ?_, (fun _ => rfl), ?_⟩
    · exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩
    · intro a _; exact runstep x a
  -- Compact input and continuous layers provide bounded envelopes at each
  -- stage. Thus the real coordinate infima and suprema obey set inclusion.
  have continuousStep : ∀ a, Continuous (step a) := by
    intro a
    dsimp only [step]
    split <;> fun_prop
  obtain ⟨K, hK, hbound⟩ :=
    Machinery.compact_envelope
      step X₀ C hzero hsucc kx₀ continuousStep (Fin.last f.val.1)
  intro j
  let j' := Fin.cast f.property.2.1.symm j
  let A : Set ℝ := (fun v => v (Fin.last f.val.1) j') '' C f.val.1
  let D : Set ℝ := (fun y => y j) '' S
  have sub : D ⊆ A := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, he⟩ := included y hy
    exact ⟨u, hu, (he j).symm⟩
  have env : A ⊆ (fun z => z j') '' K := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u (Fin.last f.val.1), hbound ⟨u, hu, rfl⟩, rfl⟩
  have below : BddBelow A := (hK.image (continuous_apply j')).bddBelow.mono env
  have above : BddAbove A := (hK.image (continuous_apply j')).bddAbove.mono env
  have nd : D.Nonempty := nonemptyS.image _
  have depth : f.val.1 - 1 + 1 = f.val.1 := by omega
  change sInf ((fun v => v (Fin.last f.val.1) j') '' C (f.val.1 - 1 + 1)) ≤ sInf D ∧
    sSup D ≤ sSup ((fun v => v (Fin.last f.val.1) j') '' C (f.val.1 - 1 + 1))
  rw [depth]
  exact ⟨csInf_le_csInf below nd sub, csSup_le_csSup above nd sub⟩
  -- formalizer:proof-end
)

end Lemma_3p2
