module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_3p2
public import Formalization.Result.Theorem_3p3
public import Formalization.Result.Lemma_Jp1
public import Formalization.Result.Proposition_Jp2
public import Mathlib

public section

namespace Theorem_Jp3.Machinery

-- formalizer:machinery-begin

theorem approximate_scalar (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ t, σ t = p.eval t)
    {d : ℕ} (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (h : (Fin d → ℝ) → ℝ) (hh : ContinuousOn h K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (a : Fin n → ℝ)
      (W : Fin n → Fin d → ℝ) (b : Fin n → ℝ) (β : ℝ),
      ∀ x ∈ K, |β + (∑ i, a i * σ ((∑ j, W i j * x j) + b i)) - h x| < ε := by
  classical
  obtain ⟨n, a, W, b, β, ha⟩ := Axioms.ExternalUniversalApproximation σ hσ hnp d K hK h hh ε hε
  let I := Option (Fin n)
  let e := (Fintype.equivFin I).symm
  let a' : I → ℝ := fun i => i.elim 0 a
  let W' : I → Fin d → ℝ := fun i => i.elim (fun _ => 0) W
  let b' : I → ℝ := fun i => i.elim 0 b
  refine ⟨Fintype.card I, Fintype.card_pos, a' ∘ e, W' ∘ e, b' ∘ e, β, ?_⟩
  intro x hx
  change |β + (∑ i, a' (e i) * σ ((∑ j, W' (e i) j * x j) + b' (e i))) - h x| < ε
  rw [e.sum_comp (fun i => a' i * σ ((∑ j, W' i j * x j) + b' i))]
  simpa [I, a', W', b', Fintype.sum_option] using ha x hx

theorem continuous_relaxation_bounds (σ : ℝ → ℝ) (hσ : Continuous σ) :
  let Net : ℕ → ℕ → Type := fun d m =>
    { p : (L : ℕ) × (w : Fin (L + 1) → ℕ) × Definition.NetworkSemantics σ L w //
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
      let R := Definition.WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2
        ((fun x k => x (Fin.cast f.property.1 k)) '' X) r hr hL
      ((fun j => R.2.1 (Fin.cast f.property.2.1.symm j)),
       (fun j => R.2.2 (Fin.cast f.property.2.1.symm j)))
  ∀ (d m : ℕ) (f : Net d m) (X : Set (Fin d → ℝ)),
    X.Nonempty → poly X → ¬X.Subsingleton →
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
    ∀ y ∈ S, ∀ j, B.1 j ≤ y j ∧ y j ≤ B.2 j := (by
  classical
  intro Net run eval poly bounds d m f X hX hp hn i hi hiL X₀ H S B
  let step : (a : Fin f.val.1) → (Fin (f.val.2.1 a.castSucc) → ℝ) →
      (Fin (f.val.2.1 a.succ) → ℝ) := fun a x =>
    match f.val.2.2.val a with
    | Sum.inl (A,b) => fun j => (∑ k, A j k * x k) + b j
    | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  let C := relaxation.stages(Definition.WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2 X₀ 1 (by omega) f.property.2.2)
  have hzero : C 0 = {v | v 0 ∈ X₀} := rfl
  have hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (f.val.1+1), j.val = s → v j = u j) ∧
      ∀ a : Fin f.val.1, s ≤ a.val → a.val < s+1 →
        v a.succ = step a (v a.castSucc)} := by
    intro s
    simp only [C, Definition.WindowRelaxation, step, Nat.rec_add_one]
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
    exact Lemma_3p2.Machinery.exact_mem_stages
      step X₀ C hzero hsucc _ (by simpa [runzero] using hx) (runstep x)
  -- Appendix E, Lemma 3.2: the convex, sound prefix projection contains
  -- conv(f₁(X)), because every exact prefix trajectory satisfies its constraints.
  have convexC := Lemma_3p2.Machinery.stages_convex
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
      Lemma_3p2.Machinery.continue_suffix
        step X₀ C hzero hsucc i v (hullsub hv) he
    exact ⟨u, hu, fun j => (hy j).trans (congrFun hue _).symm⟩
  -- Compact input and continuous layers provide bounded envelopes at each
  -- stage. Thus the real coordinate infima and suprema obey set inclusion.
  have continuousStep : ∀ a, Continuous (step a) := by
    intro a
    dsimp only [step]
    split <;> fun_prop
  obtain ⟨K, hK, hbound⟩ :=
    Lemma_3p2.Machinery.compact_envelope
      step X₀ C hzero hsucc kx₀ continuousStep (Fin.last f.val.1)
  intro y hy j
  let j' := Fin.cast f.property.2.1.symm j
  let A : Set ℝ := (fun v => v (Fin.last f.val.1) j') '' C f.val.1
  have env : A ⊆ (fun z => z j') '' K := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u (Fin.last f.val.1), hbound ⟨u, hu, rfl⟩, rfl⟩
  have below : BddBelow A := (hK.image (continuous_apply j')).bddBelow.mono env
  have above : BddAbove A := (hK.image (continuous_apply j')).bddAbove.mono env
  obtain ⟨u, hu, he⟩ := included y hy
  have memA : y j ∈ A := ⟨u, hu, (he j).symm⟩
  have depth : f.val.1 - 1 + 1 = f.val.1 := by omega
  change sInf ((fun v => v (Fin.last f.val.1) j') '' C (f.val.1 - 1 + 1)) ≤ y j ∧
    y j ≤ sSup ((fun v => v (Fin.last f.val.1) j') '' C (f.val.1 - 1 + 1))
  rw [depth]
  exact ⟨csInf_le below memA, le_csSup above memA⟩
)

theorem append_scalar_layers (σ : ℝ → ℝ) (hσ : Continuous σ) :
  let Net : ℕ → ℕ → Type := fun d m =>
    { p : (L : ℕ) × (w : Fin (L + 1) → ℕ) × Definition.NetworkSemantics σ L w //
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
      let R := Definition.WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2
        ((fun x k => x (Fin.cast f.property.1 k)) '' X) r hr hL
      ((fun j => R.2.1 (Fin.cast f.property.2.1.symm j)),
       (fun j => R.2.2 (Fin.cast f.property.2.1.symm j)))
  ∀ (d m : ℕ) (q : Net d m) (X : Set (Fin d → ℝ)),
  X.Nonempty → poly X → ¬X.Subsingleton →
  ∀ (n : ℕ), 0 < n → ∀ (a : Fin n → ℝ) (W : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) (β : ℝ) (c : Fin m → ℝ), c ∈ convexHull ℝ (eval q '' X) →
  let p : (Fin m → ℝ) → ℝ := fun z => β + ∑ i, a i * σ ((∑ j, W i j * z j) + b i)
  ∃ f : ℝ → Net d 1,
    (∀ s x, eval (f s) x 0 = s * p (eval q x)) ∧
    (∀ s, (bounds (f s) X 1 (by omega) (f s).property.2.2).1 0 ≤ s * p c ∧
      s * p c ≤ (bounds (f s) X 1 (by omega) (f s).property.2.2).2 0) := by
  classical
  intro Net run eval poly bounds d m q X hX hp hn n hnpos a W b β c hc p
  obtain ⟨V, hV⟩ := hp
  -- Append the affine/activation/affine realization of p to q. The final
  -- sign parameter realizes the paper's output negation in the same architecture.
  let w₁ : Fin (q.val.1 + 2) → ℕ := Fin.lastCases n q.val.2.1
  let w₂ : Fin (q.val.1 + 3) → ℕ := Fin.lastCases n w₁
  let w : Fin (q.val.1 + 4) → ℕ := Fin.lastCases 1 w₂
  let N (s : ℝ) : Definition.NetworkSemantics σ (q.val.1 + 3) w := by
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · have hi : w (Fin.last (q.val.1 + 2)).castSucc = n := by
          simp only [w, w₂, Fin.lastCases_castSucc, Fin.lastCases_last]
        exact Sum.inl (fun _ j => s * a (Fin.cast hi j), fun _ => s * β)
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · have hi : w (Fin.last (q.val.1 + 1)).castSucc.castSucc = n := by
            simp only [w, w₂, w₁, Fin.lastCases_castSucc, Fin.lastCases_last]
          have ho : w (Fin.last (q.val.1 + 1)).castSucc.succ = n := by
            simp only [w, w₂, w₁, Fin.succ_castSucc, Fin.succ_last,
              Fin.lastCases_castSucc, Fin.lastCases_last]
          exact Sum.inr ⟨hi.trans ho.symm⟩
        · refine Fin.lastCases ?_ (fun i => ?_) i
          · have hi : w (Fin.last q.val.1).castSucc.castSucc.castSucc = m := by
              simpa only [w, w₂, w₁, Fin.lastCases_castSucc] using q.property.2.1
            have ho : w (Fin.last q.val.1).castSucc.castSucc.succ = n := by
              simp only [w, w₂, w₁, Fin.succ_castSucc, Fin.succ_last,
                Fin.lastCases_castSucc, Fin.lastCases_last]
            exact Sum.inl (fun j k => W (Fin.cast ho j) (Fin.cast hi k),
              fun j => b (Fin.cast ho j))
          · have hi : w i.castSucc.castSucc.castSucc.castSucc = q.val.2.1 i.castSucc := by
              simp only [w, w₂, w₁, Fin.lastCases_castSucc]
            have ho : w i.castSucc.castSucc.castSucc.succ = q.val.2.1 i.succ := by
              simp only [w, w₂, w₁, Fin.succ_castSucc, Fin.lastCases_castSucc]
            cases q.val.2.2.val i with
            | inl ab =>
              exact Sum.inl (fun j k => ab.1 (Fin.cast ho j) (Fin.cast hi k),
                fun j => ab.2 (Fin.cast ho j))
            | inr h => exact Sum.inr ⟨hi.trans (h.down.trans ho.symm)⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [w]
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa [w, w₂] using hnpos
        · refine Fin.lastCases ?_ (fun j => ?_) j
          · simpa [w, w₂, w₁] using hnpos
          · simpa [w, w₂, w₁] using q.val.2.2.property j
  have hw₀ : w 0 = d := by
    change w (0 : Fin (q.val.1 + 1)).castSucc.castSucc.castSucc = d
    simpa only [w, w₂, w₁, Fin.lastCases_castSucc] using q.property.1
  have hwL : w (Fin.last (q.val.1 + 3)) = 1 := by simp [w]
  let f (s : ℝ) : Net d 1 := ⟨⟨q.val.1 + 3, w, N s⟩, hw₀, hwL, by change 0 < q.val.1 + 3; omega⟩
  have hw (j : Fin (q.val.1 + 1)) :
      w j.castSucc.castSucc.castSucc = q.val.2.1 j := by
    simp only [w, w₂, w₁, Fin.lastCases_castSucc]
  have step_prefix (s : ℝ) (i : Fin q.val.1)
      (u : Fin (w i.castSucc.castSucc.castSucc.castSucc) → ℝ) :
      (fun k => (match (N s).val i.castSucc.castSucc.castSucc with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * u k) + b j
        | Sum.inr h => fun j => σ (u (Fin.cast h.down.symm j)))
        (Fin.cast (hw i.succ).symm k)) =
      (match q.val.2.2.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * u (Fin.cast (hw i.castSucc).symm k)) + b j
        | Sum.inr h => fun j => σ (u (Fin.cast (hw i.castSucc).symm (Fin.cast h.down.symm j)))) := by
    simp only [N, Fin.lastCases_castSucc]
    cases he : q.val.2.2.val i with
    | inl ab =>
      rcases ab with ⟨A, b⟩
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      funext j
      congr 1
      exact (finCongr (hw i.castSucc)).sum_comp (fun k =>
        A j k * u (Fin.cast (hw i.castSucc).symm k))
    | inr h => rfl
  have prefix_eval (s : ℝ) (j : Fin (q.val.1 + 1)) (x : Fin d → ℝ) :
      (fun k => run (f s) j.castSucc.castSucc.castSucc
        (fun k => x (Fin.cast hw₀ k)) (Fin.cast (hw j).symm k)) =
      run q j (fun k => x (Fin.cast q.property.1 k)) := by
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hs := step_prefix s i (run (f s) i.castSucc.castSucc.castSucc.castSucc
        (fun k => x (Fin.cast hw₀ k)))
      have hi := congrArg (fun u : Fin (q.val.2.1 i.castSucc) → ℝ =>
        match q.val.2.2.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * u k) + b j
        | Sum.inr h => fun j => σ (u (Fin.cast h.down.symm j))) ih
      simp only [Fin.castSucc_succ, run, Fin.induction_succ]
      convert hs.trans hi using 1
      · cases he : (N s).val i.castSucc.castSucc.castSucc with
        | inl ab => rcases ab with ⟨A, b⟩; rfl
        | inr h => rfl
  let j₀ : Fin (q.val.1 + 4) := (Fin.last q.val.1).castSucc.castSucc.castSucc
  let j₁ : Fin (q.val.1 + 4) := (Fin.last (q.val.1 + 1)).castSucc.castSucc
  let j₂ : Fin (q.val.1 + 4) := (Fin.last (q.val.1 + 2)).castSucc
  have hwm : w j₀ = m := (hw (Fin.last q.val.1)).trans q.property.2.1
  have hwn₁ : w j₁ = n := by simp only [j₁, w, w₂, w₁, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hwn₂ : w j₂ = n := by simp only [j₂, w, w₂, Fin.lastCases_castSucc, Fin.lastCases_last]
  have suffix_value (s : ℝ) (v : (j : Fin (q.val.1 + 4)) → Fin (w j) → ℝ)
      (he : ∀ i : Fin (q.val.1 + 3), q.val.1 ≤ i.val → v i.succ =
        match (N s).val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
        | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))) :
      v (Fin.last (q.val.1 + 3)) (Fin.cast hwL.symm 0) =
        s * p (fun k => v j₀ (Fin.cast hwm.symm k)) := by
    have h₁ := he (Fin.last q.val.1).castSucc.castSucc (by simp)
    have h₂ := he (Fin.last (q.val.1 + 1)).castSucc (by simp)
    have h₃ := he (Fin.last (q.val.1 + 2)) (by simp)
    simp only [N, Fin.lastCases_castSucc, Fin.lastCases_last] at h₁ h₂ h₃
    have first (k : Fin n) : v j₁ (Fin.cast hwn₁.symm k) =
        (∑ t, W k t * v j₀ (Fin.cast hwm.symm t)) + b k := by
      have hh := congrFun h₁ (Fin.cast hwn₁.symm k)
      change v j₁ (Fin.cast hwn₁.symm k) =
        (∑ t, W k (Fin.cast hwm t) * v j₀ t) + b k at hh
      rw [hh]
      congr 1
      exact (finCongr hwm).sum_comp (fun t => W k t * v j₀ (Fin.cast hwm.symm t))
    have second (k : Fin n) : v j₂ (Fin.cast hwn₂.symm k) =
        σ ((∑ t, W k t * v j₀ (Fin.cast hwm.symm t)) + b k) := by
      have hh := congrFun h₂ (Fin.cast hwn₂.symm k)
      change v j₂ (Fin.cast hwn₂.symm k) = σ (v j₁ (Fin.cast hwn₁.symm k)) at hh
      rw [hh, first]
    have hh := congrFun h₃ (Fin.cast hwL.symm 0)
    change v (Fin.last (q.val.1 + 3)) (Fin.cast hwL.symm 0) =
      (∑ t, (s * a (Fin.cast hwn₂ t)) * v j₂ t) + s * β at hh
    rw [hh]
    rw [show (∑ t, (s * a (Fin.cast hwn₂ t)) * v j₂ t) =
      ∑ k, (s * a k) * v j₂ (Fin.cast hwn₂.symm k) from
      (finCongr hwn₂).sum_comp (fun k => (s * a k) * v j₂ (Fin.cast hwn₂.symm k))]
    simp only [second, p, Finset.mul_sum, mul_assoc, mul_add]
    ring
  have rstep (s : ℝ) (x : Fin (w 0) → ℝ) (i : Fin (q.val.1 + 3)) :
      run (f s) i.succ x =
        match (N s).val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * run (f s) i.castSucc x k) + b j
        | Sum.inr h => fun j => σ (run (f s) i.castSucc x (Fin.cast h.down.symm j)) := by
    simp only [run, Fin.induction_succ, f]
    cases he : (N s).val i with
    | inl ab => rcases ab with ⟨A, b⟩; rfl
    | inr h => rfl
  have eval_prefix (s : ℝ) (x : Fin d → ℝ) :
      (fun k => run (f s) j₀ (fun k => x (Fin.cast hw₀ k))
        (Fin.cast hwm.symm k)) = eval q x := by
    funext k
    exact congrFun (prefix_eval s (Fin.last q.val.1) x) (Fin.cast q.property.2.1.symm k)
  have evaluation (s : ℝ) (x : Fin d → ℝ) : eval (f s) x 0 = s * p (eval q x) := by
    have he := suffix_value s (fun j => run (f s) j (fun k => x (Fin.cast hw₀ k)))
      (fun i _ => rstep s _ i)
    change eval (f s) x 0 = _ at he
    rw [eval_prefix] at he
    exact he
  -- Convexity and soundness place c in the prefix projection. We now
  -- continue it through the three exact suffix layers in the ideal hull.
  let z₁ : Fin n → ℝ := fun k => (∑ t, W k t * c t) + b k
  let z₂ : Fin n → ℝ := fun k => σ (z₁ k)
  let v (s : ℝ) : (j : Fin (q.val.1 + 4)) → Fin (w j) → ℝ := fun j k =>
    if h₀ : j = j₀ then c (Fin.cast ((congrArg w h₀).trans hwm) k)
    else if h₁ : j = j₁ then z₁ (Fin.cast ((congrArg w h₁).trans hwn₁) k)
    else if h₂ : j = j₂ then z₂ (Fin.cast ((congrArg w h₂).trans hwn₂) k)
    else if j = Fin.last (q.val.1 + 3) then s * p c else 0
  have v₀ (s) (k) : v s j₀ k = c (Fin.cast hwm k) := by simp [v]
  have v₁ (s) (k) : v s j₁ k = z₁ (Fin.cast hwn₁ k) := by
    have h : j₁ ≠ j₀ := by intro h; have := congrArg Fin.val h; dsimp [j₀, j₁] at this; omega
    simp [v, h]
  have v₂ (s) (k) : v s j₂ k = z₂ (Fin.cast hwn₂ k) := by
    have h₀ : j₂ ≠ j₀ := by intro h; have := congrArg Fin.val h; dsimp [j₀, j₂] at this; omega
    have h₁ : j₂ ≠ j₁ := by intro h; have := congrArg Fin.val h; dsimp [j₁, j₂] at this; omega
    simp [v, h₀, h₁]
  have v₃ (s) (k) : v s (Fin.last (q.val.1 + 3)) k = s * p c := by
    have h₀ : Fin.last (q.val.1 + 3) ≠ j₀ := by intro h; have := congrArg Fin.val h; dsimp [j₀] at this; omega
    have h₁ : Fin.last (q.val.1 + 3) ≠ j₁ := by intro h; have := congrArg Fin.val h; dsimp [j₁] at this; omega
    have h₂ : Fin.last (q.val.1 + 3) ≠ j₂ := by intro h; have := congrArg Fin.val h; dsimp [j₂] at this; omega
    simp [v, h₀, h₁, h₂]
  have vstep (s : ℝ) (i : Fin (q.val.1 + 3)) (hi : q.val.1 ≤ i.val) :
      v s i.succ =
        match (N s).val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * v s i.castSucc k) + b j
        | Sum.inr h => fun j => σ (v s i.castSucc (Fin.cast h.down.symm j)) := by
    have he : i = (Fin.last q.val.1).castSucc.castSucc ∨
        i = (Fin.last (q.val.1 + 1)).castSucc ∨ i = Fin.last (q.val.1 + 2) := by
      have hv := i.isLt
      have hc : i.val = q.val.1 ∨ i.val = q.val.1 + 1 ∨ i.val = q.val.1 + 2 := by omega
      rcases hc with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases he with rfl | rfl | rfl
    · simp only [N, Fin.lastCases_castSucc, Fin.lastCases_last]
      funext k
      change v s j₁ k = (∑ t, W (Fin.cast hwn₁ k) (Fin.cast hwm t) * v s j₀ t) + b (Fin.cast hwn₁ k)
      rw [v₁]
      simp only [v₀, z₁]
      congr 1
      exact ((finCongr hwm).sum_comp (fun t => W (Fin.cast hwn₁ k) t * c t)).symm
    · simp only [N, Fin.lastCases_castSucc, Fin.lastCases_last]
      funext k
      change v s j₂ k = σ (v s j₁ (Fin.cast (hwn₁.trans hwn₂.symm).symm k))
      simp only [v₂, v₁, z₂, Fin.cast_cast, Fin.cast_eq_self]
    · simp only [N, Fin.lastCases_last]
      funext k
      change v s (Fin.last (q.val.1 + 3)) k =
        (∑ t, (s * a (Fin.cast hwn₂ t)) * v s j₂ t) + s * β
      rw [v₃]
      simp only [v₂]
      calc
        s * p c = (∑ t, (s * a t) * z₂ t) + s * β := by
          simp only [p, z₁, z₂, Finset.mul_sum, mul_assoc, mul_add]
          ring
        _ = _ := congrArg (fun z => z + s * β) ((finCongr hwn₂).sum_comp (fun t => (s * a t) * z₂ t)).symm
  let lin : (Fin m → ℝ) →ₗ[ℝ] (Fin (w j₀) → ℝ) :=
    { toFun := fun z k => z (Fin.cast hwm k)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have runmatch (s : ℝ) (x : Fin d → ℝ) :
      run (f s) j₀ (fun k => x (Fin.cast hw₀ k)) = lin (eval q x) := by
    funext k
    exact congrFun (eval_prefix s x) (Fin.cast hwm k)
  have hull_point (s : ℝ) : v s j₀ ∈ convexHull ℝ
      (run (f s) j₀ '' ((fun x k => x (Fin.cast hw₀ k)) '' X)) := by
    have himage : lin '' (eval q '' X) =
        run (f s) j₀ '' ((fun x k => x (Fin.cast hw₀ k)) '' X) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext x
      exact (runmatch s x).symm
    rw [← himage, ← lin.image_convexHull]
    refine ⟨c, hc, ?_⟩
    funext k
    exact (v₀ s k).symm
  have relaxed (s : ℝ) :
      (bounds (f s) X 1 (by omega) (f s).property.2.2).1 0 ≤ s * p c ∧
      s * p c ≤ (bounds (f s) X 1 (by omega) (f s).property.2.2).2 0 := by
    apply continuous_relaxation_bounds
      σ hσ d 1 (f s) X hX ⟨V, hV⟩ hn j₀
      (by change 1 ≤ q.val.1; have := q.property.2.2; omega)
      (by change q.val.1 < q.val.1 + 3; omega) (fun _ => s * p c) ?_ 0
    refine ⟨v s, hull_point s, ?_, ?_⟩
    · intro j
      exact (v₃ s _).symm
    · intro i hi
      have he := vstep s i hi
      convert he using 1
      cases hN : (N s).val i with
      | inl ab => rcases ab with ⟨A, b⟩; rfl
      | inr h => rfl
  exact ⟨f, evaluation, relaxed⟩

-- formalizer:machinery-end

end Theorem_Jp3.Machinery
