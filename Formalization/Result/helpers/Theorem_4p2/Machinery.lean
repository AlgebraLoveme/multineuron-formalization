module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_3p2
public import Formalization.Result.Theorem_3p3
public import Formalization.Result.Lemma_4p1
public import Mathlib

public section

namespace Theorem_4p2.Machinery

-- formalizer:machinery-begin
lemma cast_affine_layer {a b c d : ℕ} (hin : a = c) (hout : b = d)
    (A : Matrix (Fin c) (Fin d) ℝ) (v : Fin c → ℝ) :
    ∃ A' v', cast (by rw [hin, hout])
      (Sum.inl (A, v) : (Matrix (Fin c) (Fin d) ℝ × (Fin c → ℝ)) ⊕ PLift (d = c)) =
      (Sum.inl (A', v') : (Matrix (Fin a) (Fin b) ℝ × (Fin a → ℝ)) ⊕ PLift (b = a)) := by
  subst c
  subst d
  exact ⟨A, v, rfl⟩

theorem padding_with_depth :
  let σ : ℝ → ℝ := fun t => max t 0
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
  ∀ (d e : ℕ) (f₁ : Net d e) (f₂ : Net e 1)
    (X : Set (Fin d → ℝ)), X.Nonempty → poly X →
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ f : Net d 1, f.val.1 = ⌈max (1 / α)
      (((f₁.val.1 + f₂.val.1 : ℕ) + 1 : ℝ) / (1 - α))⌉₊ ∧
      ((∃ i : Fin f₂.val.1, i.val + 1 = f₂.val.1 ∧ ∃ A b, f₂.val.2.2.val i = Sum.inl (A, b)) →
        ∃ i : Fin f.val.1, i.val + 1 = f.val.1 ∧ ∃ A b, f.val.2.2.val i = Sum.inl (A, b)) ∧
      f₁.val.1 + f₂.val.1 < f.val.1 ∧
      (∀ x ∈ X, eval f x = eval f₂ (eval f₁ x)) ∧
      let r := max 1 ⌊α * (f.val.1 : ℝ)⌋₊
      ∃ hr : 1 ≤ r, ∃ hL : r ≤ f.val.1,
      let B := bounds f X r hr hL
      let S := (fun z => eval f₂ z 0) '' convexHull ℝ (eval f₁ '' X)
      B.1 0 ≤ sInf S ∧ sSup S ≤ B.2 0 := (by
  classical
  intro σ Net run eval poly bounds d e f₁ f₂ X hX hpoly α hα hα'
  -- Equation (L): choose the padded depth so the identity block contains
  -- at least r layers and strictly increases total depth.
  let L := ⌈max (1 / α)
    (((f₁.val.1 + f₂.val.1 : ℕ) + 1 : ℝ) / (1 - α))⌉₊
  have hdepth :=
    Lemma_4p1.Machinery.padding_depth
      α hα hα' (f₁.val.1 + f₂.val.1)
  change f₁.val.1 + f₂.val.1 < L ∧
    1 ≤ max 1 ⌊α * (L : ℝ)⌋₊ ∧
    max 1 ⌊α * (L : ℝ)⌋₊ ≤ L - (f₁.val.1 + f₂.val.1) at hdepth
  let right := L - f₂.val.1
  have htotal := hdepth.1
  have hright : f₁.val.1 < right := by dsimp [right]; omega
  have hrightL : right + f₂.val.1 = L := by dsimp [right]; omega
  let w : Fin (L + 1) → ℕ := fun j =>
    if h : j.val ≤ f₁.val.1 then f₁.val.2.1 ⟨j.val, by omega⟩
    else if j.val ≤ right then e
    else f₂.val.2.1 ⟨j.val - right, by omega⟩
  have hwleft (j : Fin (L + 1)) (hj : j.val ≤ f₁.val.1) :
      w j = f₁.val.2.1 ⟨j.val, by omega⟩ := by simp [w, hj]
  have hwmiddle (j : Fin (L + 1)) (hj : f₁.val.1 ≤ j.val) (hj' : j.val ≤ right) :
      w j = e := by
    by_cases heq : j.val ≤ f₁.val.1
    · rw [hwleft j heq]
      have heq' : (⟨j.val, by omega⟩ : Fin (f₁.val.1 + 1)) = Fin.last f₁.val.1 :=
        Fin.ext (by simp; omega)
      rw [heq']
      exact f₁.property.2.1
    · simp [w, heq, hj']
  have hwright (j : Fin (L + 1)) (hj : right ≤ j.val) :
      w j = f₂.val.2.1 ⟨j.val - right, by omega⟩ := by
    by_cases heq : j.val ≤ right
    · rw [hwmiddle j (by omega) heq]
      have heq' : (⟨j.val - right, by omega⟩ : Fin (f₂.val.1 + 1)) = 0 :=
        Fin.ext (by simp; omega)
      rw [heq']
      exact f₂.property.1.symm
    · simp [w, show ¬j.val ≤ f₁.val.1 by omega, heq]
  have hwpos : ∀ j, 0 < w j := by
    intro j
    by_cases hj : j.val ≤ f₁.val.1
    · rw [hwleft j hj]
      exact f₁.val.2.2.property _
    · by_cases hj' : j.val ≤ right
      · rw [hwmiddle j (by omega) hj']
        rw [← f₁.property.2.1]
        exact f₁.val.2.2.property _
      · rw [hwright j (by omega)]
        exact f₂.val.2.2.property _
  -- Insert individually counted affine identities between the two original
  -- layer lists, as in the paper's pumping construction.
  let layers : (i : Fin L) →
      (Matrix (Fin (w i.succ)) (Fin (w i.castSucc)) ℝ × (Fin (w i.succ) → ℝ)) ⊕
        PLift (w i.castSucc = w i.succ) := fun i => by
    by_cases hi : i.val < f₁.val.1
    · have hwin := hwleft i.castSucc (by simpa using hi.le)
      have hwout := hwleft i.succ (by simp; omega)
      exact cast (by rw [hwin, hwout]; rfl) (f₁.val.2.2.val ⟨i.val, hi⟩)
    · by_cases hi' : i.val < right
      · have hwin := hwmiddle i.castSucc (by simp; omega) (by simp; omega)
        have hwout := hwmiddle i.succ (by simp; omega) (by simp; omega)
        exact cast (by rw [hwin, hwout])
          (Sum.inl (1, 0) : (Matrix (Fin e) (Fin e) ℝ × (Fin e → ℝ)) ⊕ PLift (e = e))
      · have hwin := hwright i.castSucc (by simp; omega)
        have hwout := hwright i.succ (by simp; omega)
        let q : Fin f₂.val.1 := ⟨i.val - right, by omega⟩
        have hs : w i.succ = f₂.val.2.1 q.succ := hwout.trans
          (congrArg f₂.val.2.1 (Fin.ext (by dsimp [q]; omega)))
        exact cast (by rw [hwin, hs]; rfl) (f₂.val.2.2.val q)
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ) :=
    fun i x j => Sum.elim (fun p => (∑ t, p.1 j t * x t) + p.2 j)
      (fun h => σ (x (Fin.cast h.down.symm j))) (layers i)
  have hstepLeft (i : Fin L) (hi : i.val < f₁.val.1)
      (x : Fin (w i.castSucc) → ℝ) (j : Fin (w i.succ)) :
      step i x j = Sum.elim
        (fun p => (∑ t, p.1 (Fin.cast (hwleft i.succ (by simp; omega)) j) t *
          x (Fin.cast (hwleft i.castSucc (by simp; omega)).symm t)) +
          p.2 (Fin.cast (hwleft i.succ (by simp; omega)) j))
        (fun h => σ (x (Fin.cast (hwleft i.castSucc (by simp; omega)).symm
          (Fin.cast h.down.symm (Fin.cast (hwleft i.succ (by simp; omega)) j)))))
        (f₁.val.2.2.val ⟨i.val, hi⟩) := by
    dsimp only [step, layers]
    simp only [dif_pos hi]
    exact Lemma_4p1.Machinery.transported_layer_action
      σ (hwleft i.castSucc (by simp; omega)) (hwleft i.succ (by simp; omega))
      (f₁.val.2.2.val ⟨i.val, hi⟩) x j
  have hstepMiddle (i : Fin L) (hi : f₁.val.1 ≤ i.val) (hi' : i.val < right)
      (x : Fin (w i.castSucc) → ℝ) (j : Fin (w i.succ)) :
      step i x j = x (Fin.cast ((hwmiddle i.castSucc (by simpa using hi) (by simp; omega)).trans
        (hwmiddle i.succ (by simp; omega) (by simp; omega)).symm).symm j) := by
    dsimp only [step, layers]
    simp only [dif_neg (show ¬i.val < f₁.val.1 by omega), dif_pos hi']
    rw [Lemma_4p1.Machinery.transported_layer_action
      σ (hwmiddle i.castSucc (by simpa using hi) (by simp; omega))
      (hwmiddle i.succ (by simp; omega) (by simp; omega))]
    simp [Matrix.one_apply, Fin.cast_cast]
  have hwrightIn (i : Fin L) (q : Fin f₂.val.1) (hi : i.val = right + q.val) :
      w i.castSucc = f₂.val.2.1 q.castSucc :=
    (hwright i.castSucc (by simp; omega)).trans
      (congrArg f₂.val.2.1 (Fin.ext (by simp; omega)))
  have hwrightOut (i : Fin L) (q : Fin f₂.val.1) (hi : i.val = right + q.val) :
      w i.succ = f₂.val.2.1 q.succ :=
    (hwright i.succ (by simp; omega)).trans
      (congrArg f₂.val.2.1 (Fin.ext (by simp; omega)))
  have hstepRight (i : Fin L) (q : Fin f₂.val.1) (hi : i.val = right + q.val)
      (x : Fin (w i.castSucc) → ℝ) (j : Fin (w i.succ)) :
      step i x j = Sum.elim
        (fun p => (∑ t, p.1 (Fin.cast (hwrightOut i q hi) j) t *
          x (Fin.cast (hwrightIn i q hi).symm t)) + p.2 (Fin.cast (hwrightOut i q hi) j))
        (fun h => σ (x (Fin.cast (hwrightIn i q hi).symm
          (Fin.cast h.down.symm (Fin.cast (hwrightOut i q hi) j)))))
        (f₂.val.2.2.val q) := by
    have hq : q = (⟨i.val - right, by
      clear q hi
      have := f₂.property.2.2
      omega⟩ : Fin f₂.val.1) := Fin.ext (by dsimp only; omega)
    subst q
    dsimp only [step, layers]
    simp only [dif_neg (show ¬i.val < f₁.val.1 by omega), dif_neg (show ¬i.val < right by omega)]
    exact Lemma_4p1.Machinery.transported_layer_action
      σ (hwrightIn i _ hi) (hwrightOut i _ hi) _ x j
  have run_succ {a b : ℕ} (g : Net a b) (i : Fin g.val.1)
      (x : Fin (g.val.2.1 0) → ℝ) (j : Fin (g.val.2.1 i.succ)) :
      run g i.succ x j = Sum.elim
        (fun p => (∑ t, p.1 j t * run g i.castSucc x t) + p.2 j)
        (fun h => σ (run g i.castSucc x (Fin.cast h.down.symm j))) (g.val.2.2.val i) := by
    dsimp only [run, Fin.induction_succ]
    rcases g.val.2.2.val i with ⟨A, b⟩ | h <;> rfl
  let N : Definition.NetworkSemantics (fun t => max t 0) L w := ⟨layers, hwpos⟩
  have hwzero : w 0 = d := by
    rw [hwleft 0 (by simp)]
    exact f₁.property.1
  have hwlast : w (Fin.last L) = 1 := by
    rw [hwright (Fin.last L) (by simp; omega)]
    have heq : (⟨(Fin.last L).val - right, by simp; omega⟩ : Fin (f₂.val.1 + 1)) =
        Fin.last f₂.val.1 := Fin.ext (by simp; omega)
    rw [heq]
    exact f₂.property.2.1
  let f := (⟨⟨L, w, N⟩, hwzero, hwlast, lt_of_le_of_lt (Nat.zero_le _) htotal⟩ :
    {p : (L : ℕ) × (w : Fin (L + 1) → ℕ) × Definition.NetworkSemantics (fun t => max t 0) L w //
      p.2.1 0 = d ∧ p.2.1 (Fin.last p.1) = 1 ∧ 0 < p.1})
  let leftIx (j : Fin (f₁.val.1 + 1)) : Fin (L + 1) := ⟨j.val, by omega⟩
  have hrunleft (x : Fin (w 0) → ℝ) (j : Fin (f₁.val.1 + 1)) :
      ∀ k : Fin (f₁.val.2.1 j),
        run f (leftIx j) x (Fin.cast (hwleft (leftIx j) (by dsimp [leftIx]; omega)).symm k) =
        run f₁ j (fun t => x (Fin.cast (hwleft 0 (by simp)).symm t)) k := by
    induction j using Fin.induction with
    | zero => intro k; rfl
    | succ i ih =>
      intro k
      let q : Fin L := ⟨i.val, by omega⟩
      change run f q.succ x (Fin.cast _ k) = _
      rw [run_succ f q]
      change step q (run f q.castSucc x) (Fin.cast _ k) = _
      rw [hstepLeft q (by dsimp [q]; omega)]
      rw [run_succ]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      apply congrArg₂ (fun a b => Sum.elim a b (f₁.val.2.2.val i))
      · funext p
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        exact ih t
      · funext h
        congr 1
        simpa only [Fin.cast_cast] using ih (Fin.cast h.down.symm k)
  have hrunmiddle (x : Fin (w 0) → ℝ) :
      ∀ (j : Fin (L + 1)) (hj : f₁.val.1 ≤ j.val) (hj' : j.val ≤ right) (k : Fin e),
        run f j x (Fin.cast (hwmiddle j hj hj').symm k) =
        run f (leftIx (Fin.last f₁.val.1)) x
          (Fin.cast (hwmiddle (leftIx (Fin.last f₁.val.1)) (by rfl) (by dsimp [leftIx]; omega)).symm k) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro hj _ _
      have := f₁.property.2.2
      simp only [Fin.val_zero] at hj
      omega
    | succ i ih =>
      intro hj hj' k
      by_cases heq : i.succ.val = f₁.val.1
      · have heq' : i.succ = leftIx (Fin.last f₁.val.1) := Fin.ext heq
        exact Lemma_4p1.Machinery.coordinate_cast_congr
          w (fun j => run f j x) heq' (hwmiddle i.succ hj hj')
          (hwmiddle (leftIx (Fin.last f₁.val.1)) (by rfl) (by dsimp [leftIx]; omega)) k
      · have hi : f₁.val.1 ≤ i.val := by simp only [Fin.val_succ] at hj heq; omega
        have hi' : i.val < right := by simp only [Fin.val_succ] at hj'; omega
        rw [run_succ f i]
        change step i (run f i.castSucc x) (Fin.cast _ k) = _
        rw [hstepMiddle i hi hi']
        simpa only [Fin.cast_cast] using ih hi hi'.le k
  let rightIx (j : Fin (f₂.val.1 + 1)) : Fin (L + 1) := ⟨right + j.val, by omega⟩
  have hwrightIx (j : Fin (f₂.val.1 + 1)) : w (rightIx j) = f₂.val.2.1 j := by
    rw [hwright (rightIx j) (by dsimp [rightIx]; omega)]
    apply congrArg f₂.val.2.1
    apply Fin.ext
    simp [rightIx]
  have hrunright (x : Fin (w 0) → ℝ) (j : Fin (f₂.val.1 + 1)) :
      ∀ k : Fin (f₂.val.2.1 j),
        run f (rightIx j) x (Fin.cast (hwrightIx j).symm k) =
        run f₂ j (fun t => run f (rightIx 0) x (Fin.cast (hwrightIx 0).symm t)) k := by
    induction j using Fin.induction with
    | zero => intro k; rfl
    | succ i ih =>
      intro k
      let q : Fin L := ⟨right + i.val, by omega⟩
      change run f q.succ x (Fin.cast _ k) = _
      rw [run_succ f q]
      change step q (run f q.castSucc x) (Fin.cast _ k) = _
      rw [hstepRight q i rfl, run_succ]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      apply congrArg₂ (fun a b => Sum.elim a b (f₂.val.2.2.val i))
      · funext p
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        exact ih t
      · funext h
        congr 1
        simpa only [Fin.cast_cast] using ih (Fin.cast h.down.symm k)
  -- The copied prefix evaluates as f₁, and every affine identity keeps its
  -- output unchanged up to the start of the copied suffix.
  have hinterface (x : Fin d → ℝ) (j : Fin (L + 1))
      (hj : f₁.val.1 ≤ j.val) (hj' : j.val ≤ right) (k : Fin e) :
      run f j (fun t => x (Fin.cast hwzero t)) (Fin.cast (hwmiddle j hj hj').symm k) =
        eval f₁ x k := by
    rw [hrunmiddle _ j hj hj' k]
    have h := hrunleft (fun t => x (Fin.cast hwzero t)) (Fin.last f₁.val.1)
      (Fin.cast f₁.property.2.1.symm k)
    simpa only [eval, Fin.cast_cast] using h
  have hrightLast : rightIx (Fin.last f₂.val.1) = Fin.last L :=
    Fin.ext (by dsimp [rightIx]; omega)
  refine ⟨f, rfl, ?_, hdepth.1, ?_, ?_⟩
  · rintro ⟨q, hq, A, b, hqaff⟩
    let i : Fin L := ⟨right + q.val, by omega⟩
    refine ⟨i, by change right + q.val + 1 = L; omega, ?_⟩
    change ∃ A' b', layers i = Sum.inl (A', b')
    dsimp only [layers]
    rw [dif_neg (show ¬i.val < f₁.val.1 by dsimp [i]; omega),
      dif_neg (show ¬i.val < right by dsimp [i]; omega)]
    have hqi : (⟨i.val - right, by dsimp [i]; omega⟩ : Fin f₂.val.1) = q :=
      Fin.ext (by dsimp [i]; omega)
    obtain ⟨A', b', ha⟩ : ∃ A' b', f₂.val.2.2.val ⟨i.val - right, by dsimp [i]; omega⟩ = Sum.inl (A', b') := by
      rw [hqi]
      exact ⟨A, b, hqaff⟩
    rw [ha]
    apply cast_affine_layer
    · exact hwrightOut i _ (by dsimp [i]; omega)
    · exact hwrightIn i _ (by dsimp [i]; omega)

  · -- The copied suffix begins at f₁(x), hence its final output is f₂(f₁(x)).
    intro x _
    funext k
    have hinput : (fun t => run f (rightIx 0) (fun t => x (Fin.cast hwzero t))
        (Fin.cast (hwrightIx 0).symm t)) =
        (fun t => eval f₁ x (Fin.cast f₂.property.1 t)) := by
      funext t
      simpa only [Fin.cast_cast] using hinterface x (rightIx 0)
        (by dsimp [rightIx]; omega) (by dsimp [rightIx]; omega) (Fin.cast f₂.property.1 t)
    have h := hrunright (fun t => x (Fin.cast hwzero t)) (Fin.last f₂.val.1)
      (Fin.cast f₂.property.2.1.symm k)
    rw [hinput] at h
    have hend :=
      Lemma_4p1.Machinery.coordinate_cast_congr
        w (fun j => run f j (fun t => x (Fin.cast hwzero t))) hrightLast
        ((hwrightIx (Fin.last f₂.val.1)).trans f₂.property.2.1) hwlast k
    change run f (Fin.last L) (fun t => x (Fin.cast hwzero t)) (Fin.cast hwlast.symm k) = _
    rw [← hend]
    simpa only [eval, Fin.cast_cast] using h
  · let r := max 1 ⌊α * (L : ℝ)⌋₊
    have hr : 1 ≤ r := hdepth.2.1
    have hrL : r ≤ L := hdepth.2.2.trans (Nat.sub_le _ _)
    refine ⟨hr, hrL, ?_⟩
    let Y : Set (Fin (w 0) → ℝ) := (fun x k => x (Fin.cast hwzero k)) '' X
    let S := (fun z => eval f₂ z 0) '' convexHull ℝ (eval f₁ '' X)
    let T := (fun v : (j : Fin (L + 1)) → Fin (w j) → ℝ =>
      v (Fin.last L) (Fin.cast hwlast.symm 0)) ''
      relaxation.stages(Definition.WindowRelaxation σ L w N Y r hr hrL) (L - r + 1)
    change sInf T ≤ sInf S ∧ sSup S ≤ sSup T
    have hcompactX : IsCompact X := by
      obtain ⟨V, rfl⟩ := hpoly
      exact V.finite_toSet.isCompact_convexHull ℝ
    have hconvX : Convex ℝ X := by
      obtain ⟨V, rfl⟩ := hpoly
      exact convex_convexHull ℝ _
    have hcompactY : IsCompact Y := hcompactX.image (by fun_prop)
    have hconvY : Convex ℝ Y := by
      rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ c d hc hd hcd
      exact ⟨c • x + d • y, hconvX hx hy hc hd hcd, rfl⟩
    -- Compact input and continuity give bounded layer envelopes; the sequential
    -- window constraints keep every final coordinate in its envelope.
    have hbounded :=
      Lemma_4p1.Machinery.relaxation_output_bounded
        σ (continuous_id.max continuous_const) L w N Y hcompactY hconvY r hr hrL
        (Fin.cast hwlast.symm 0)
    have hS : S.Nonempty := by
      obtain ⟨x, hx⟩ := hX
      exact ⟨eval f₂ (eval f₁ x) 0, eval f₁ x,
        subset_convexHull ℝ _ ⟨x, hx, rfl⟩, rfl⟩
    have hinclusion : S ⊆ T := by
      rintro _ ⟨z, hz, rfl⟩
      let U (x : Fin d → ℝ) (j : Fin (L + 1)) :=
        run f j (fun t => x (Fin.cast hwzero t))
      let H := convexHull ℝ (U '' X)
      have hU (x : Fin d → ℝ) (hx : x ∈ X) (k : ℕ) :
          U x ∈ relaxation.stages(Definition.WindowRelaxation σ L w N Y r hr hrL) k := by
        apply Lemma_4p1.Machinery.relaxation_exact_trajectory
        · exact ⟨x, hx, rfl⟩
        · intro i
          funext t
          rw [show U x i.succ t = run f i.succ (fun t => x (Fin.cast hwzero t)) t from rfl,
            run_succ]
          dsimp only [U, f, N]
          rcases layers i with ⟨A, b⟩ | h <;> rfl
      have hH : ∀ u ∈ H, ∀ k, u ∈ relaxation.stages(Definition.WindowRelaxation σ L w N Y r hr hrL) k := by
        intro u hu k
        apply convexHull_min (s := U '' X) _
          (Lemma_4p1.Machinery.relaxation_stage_convex
            σ L w N Y hconvY r hr hrL k) hu
        rintro _ ⟨x, hx, rfl⟩
        exact hU x hx k
      let c := leftIx (Fin.last f₁.val.1)
      have hc : w c = e := hwmiddle c (by rfl) (by dsimp [c, leftIx]; omega)
      let P : ((j : Fin (L + 1)) → Fin (w j) → ℝ) →ₗ[ℝ] (Fin e → ℝ) :=
        { toFun := fun u k => u c (Fin.cast hc.symm k)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      -- The left family is convex and sound. Its interface projection therefore
      -- contains conv(f₁(X)); identities carry the same value across the block.
      have hproj : eval f₁ '' X ⊆ P '' (U '' X) := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨U x, ⟨x, hx, rfl⟩, ?_⟩
        funext k
        exact hinterface x c (by rfl) (by dsimp [c, leftIx]; omega) k
      have hz' := convexHull_mono hproj hz
      rw [← P.image_convexHull] at hz'
      obtain ⟨u, hu, hpu⟩ := hz'
      have hmiddle : ∀ (j : Fin (L + 1)) (hj : f₁.val.1 ≤ j.val)
          (hj' : j.val ≤ right) (k : Fin e),
          u j (Fin.cast (hwmiddle j hj hj').symm k) = z k := by
        have hC : Convex ℝ {v : (j : Fin (L + 1)) → Fin (w j) → ℝ |
            ∀ (j : Fin (L + 1)) (hj : f₁.val.1 ≤ j.val) (hj' : j.val ≤ right) (k : Fin e),
              v j (Fin.cast (hwmiddle j hj hj').symm k) = P v k} := by
          intro a ha b hb t s ht hs hts j hj hj' k
          change t * a j _ + s * b j _ = t * P a k + s * P b k
          rw [ha j hj hj' k, hb j hj hj' k]
        have huC : u ∈ {v : (j : Fin (L + 1)) → Fin (w j) → ℝ |
            ∀ (j : Fin (L + 1)) (hj : f₁.val.1 ≤ j.val) (hj' : j.val ≤ right) (k : Fin e),
              v j (Fin.cast (hwmiddle j hj hj').symm k) = P v k} := by
          apply convexHull_min _ hC hu
          rintro _ ⟨x, hx, rfl⟩ j hj hj' k
          exact hrunmiddle _ j hj hj' k
        intro j hj hj' k
        exact (huC j hj hj' k).trans (congrFun hpu k)
      -- Preserve the convexified prefix and the repeated interface variables;
      -- after the identity block, take the exact f₂ trajectory starting at z.
      let v : (j : Fin (L + 1)) → Fin (w j) → ℝ := fun j k =>
        if hj : j.val ≤ right then u j k
        else run f₂ ⟨j.val - right, by omega⟩ (fun t => z (Fin.cast f₂.property.1 t))
          (Fin.cast (hwright j (by omega)) k)
      have hvagree (j : Fin (L + 1)) (hj : j.val ≤ right) : v j = u j := by
        funext k
        simp only [v, dif_pos hj]
      have hvrightIx (j : Fin (f₂.val.1 + 1)) (k : Fin (f₂.val.2.1 j)) :
          v (rightIx j) (Fin.cast (hwrightIx j).symm k) =
            run f₂ j (fun t => z (Fin.cast f₂.property.1 t)) k := by
        by_cases hj : j = 0
        · subst j
          rw [hvagree (rightIx 0) (by dsimp [rightIx]; omega)]
          simpa only [run, Fin.induction_zero, Fin.cast_cast] using
            hmiddle (rightIx 0) (by dsimp [rightIx]; omega)
              (by dsimp [rightIx]; omega) (Fin.cast f₂.property.1 k)
        · have hjpos : 0 < j.val := by have := Fin.pos_iff_ne_zero.mpr hj; exact this
          dsimp only [v]
          rw [dif_neg (show ¬(rightIx j).val ≤ right by dsimp [rightIx]; omega)]
          let q : Fin (f₂.val.1 + 1) := ⟨(rightIx j).val - right, by dsimp [rightIx]; omega⟩
          have hq : q = j := Fin.ext (by dsimp [q, rightIx]; omega)
          have hh :=
            Lemma_4p1.Machinery.coordinate_cast_congr
              f₂.val.2.1 (fun j => run f₂ j (fun t => z (Fin.cast f₂.property.1 t)))
              hq (congrArg f₂.val.2.1 hq) rfl k
          simpa only [Fin.cast_cast, Fin.cast_eq_self] using hh
      have hvright (j : Fin (L + 1)) (q : Fin (f₂.val.1 + 1))
          (heq : j = rightIx q) (hw : w j = f₂.val.2.1 q) (k : Fin (w j)) :
          v j k = run f₂ q (fun t => z (Fin.cast f₂.property.1 t)) (Fin.cast hw k) := by
        subst j
        simpa only [Fin.cast_cast, Fin.cast_eq_self] using hvrightIx q (Fin.cast hw k)
      have hvstep : ∀ i : Fin L, f₁.val.1 ≤ i.val → v i.succ = step i (v i.castSucc) := by
        intro i hi
        funext k
        by_cases hi' : i.val < right
        · rw [hstepMiddle i hi hi', hvagree i.succ (by simp; omega),
            hvagree i.castSucc (by simp; omega)]
          have hout := hmiddle i.succ (by simp; omega) (by simp; omega)
            (Fin.cast (hwmiddle i.succ (by simp; omega) (by simp; omega)) k)
          have hin := hmiddle i.castSucc hi hi'.le
            (Fin.cast (hwmiddle i.succ (by simp; omega) (by simp; omega)) k)
          simpa only [Fin.cast_cast, Fin.cast_eq_self] using hout.trans hin.symm
        · let q : Fin f₂.val.1 := ⟨i.val - right, by omega⟩
          have hq : i.val = right + q.val := by dsimp [q]; omega
          have hsucc : i.succ = rightIx q.succ := Fin.ext (by dsimp [rightIx]; omega)
          have hprev : i.castSucc = rightIx q.castSucc := Fin.ext (by dsimp [rightIx]; omega)
          rw [hvright i.succ q.succ hsucc (hwrightOut i q hq) k, run_succ,
            hstepRight i q hq]
          apply congrArg₂ (fun a b => Sum.elim a b (f₂.val.2.2.val q))
          · funext p
            congr 1
            apply Finset.sum_congr rfl
            intro t _
            congr 1
            symm
            simpa only [Fin.cast_cast, Fin.cast_eq_self] using
              hvright i.castSucc q.castSucc hprev (hwrightIn i q hq)
                (Fin.cast (hwrightIn i q hq).symm t)
          · funext h
            congr 1
            symm
            simpa only [Fin.cast_cast, Fin.cast_eq_self] using
              hvright i.castSucc q.castSucc hprev (hwrightIn i q hq)
                (Fin.cast (hwrightIn i q hq).symm
                  (Fin.cast h.down.symm (Fin.cast (hwrightOut i q hq) k)))
      have hvfeasible : v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N Y r hr hrL) (L - r + 1) := by
        -- No window reaches nonidentity layers on both sides. Earlier windows
        -- retain u's prefix; later windows accept this exact continuation.
        apply Lemma_4p1.Machinery.relaxation_splice
          σ L w N Y r hr hrL f₁.val.1 right (by dsimp [r, right]; omega) u v
          (hH u hu) hvagree
        intro i hi
        rw [hvstep i hi]
        funext k
        dsimp only [step, N]
        rcases layers i with ⟨A, b⟩ | h <;> rfl
      refine ⟨v, hvfeasible, ?_⟩
      have hvend := hvright (Fin.last L) (Fin.last f₂.val.1) hrightLast.symm
        (hwlast.trans f₂.property.2.1.symm) (Fin.cast hwlast.symm 0)
      simpa only [eval, Fin.cast_cast] using hvend
    -- The final two inequalities follow from output inclusion and boundedness,
    -- as in the last display of the paper's pumping-lemma proof.
    exact Lemma_4p1.Machinery.scalar_extrema_of_subset
      hS hinclusion hbounded.1 hbounded.2
)

/-- Coordinate changes transport each sequential graph hull, including its
projected starting domain and all overlapping constraints. -/
lemma window_coordinate_change (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N M : Definition.NetworkSemantics σ L w)
    (E : (j : Fin (L + 1)) → (Fin (w j) → ℝ) ≃ₗ[ℝ] (Fin (w j) → ℝ))
    (hzero : ∀ x, E 0 x = x)
    (hstep : ∀ (i : Fin L) x,
      (fun j => Sum.elim (fun p => (∑ k, p.1 j k * E i.castSucc x k) + p.2 j)
        (fun h => σ (E i.castSucc x (Fin.cast h.down.symm j))) (M.val i)) =
      E i.succ (fun j => Sum.elim (fun p => (∑ k, p.1 j k * x k) + p.2 j)
        (fun h => σ (x (Fin.cast h.down.symm j))) (N.val i)))
    (X : Set (Fin (w 0) → ℝ)) (r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) :
    ∀ k, (LinearEquiv.piCongrRight E) ''
      relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hrL) k =
      relaxation.stages(Definition.WindowRelaxation σ L w M X r hr hrL) k := by
  let R := LinearEquiv.piCongrRight E
  let step (P : Definition.NetworkSemantics σ L w) (i : Fin L)
      (x : Fin (w i.castSucc) → ℝ) : Fin (w i.succ) → ℝ :=
    fun j => Sum.elim (fun p => (∑ k, p.1 j k * x k) + p.2 j)
      (fun h => σ (x (Fin.cast h.down.symm j))) (P.val i)
  change ∀ i x, step M i (E i.castSucc x) = E i.succ (step N i x) at hstep
  let C (P : Definition.NetworkSemantics σ L w) (k : ℕ) :=
    relaxation.stages(Definition.WindowRelaxation σ L w P X r hr hrL) k
  have membership {k : ℕ} (hk : R '' C N k = C M k) (v) :
      R v ∈ C M k ↔ v ∈ C N k := by
    rw [← hk]
    exact R.injective.mem_set_image
  intro k
  change R '' C N k = C M k
  induction k with
  | zero =>
    ext v
    obtain ⟨u, rfl⟩ := R.surjective v
    rw [R.injective.mem_set_image]
    change (u 0 ∈ X) ↔ (E 0 (u 0) ∈ X)
    rw [hzero]
  | succ k ih =>
    let G (P : Definition.NetworkSemantics σ L w) :=
      {v : (j : Fin (L + 1)) → Fin (w j) → ℝ |
        (∃ u ∈ C P k, ∀ j : Fin (L + 1), j.val = k → v j = u j) ∧
        ∀ i : Fin L, k ≤ i.val → i.val < k + r → v i.succ = step P i (v i.castSucc)}
    have hG : R '' G N = G M := by
      ext v
      obtain ⟨v, rfl⟩ := R.surjective v
      rw [R.injective.mem_set_image]
      constructor
      · rintro ⟨⟨u, hu, heq⟩, hv⟩
        refine ⟨⟨R u, (membership ih u).mpr hu, ?_⟩, ?_⟩
        · intro j hj
          exact congrArg (E j) (heq j hj)
        · intro i hi hi'
          change E i.succ (v i.succ) = step M i (E i.castSucc (v i.castSucc))
          rw [hstep i, hv i hi hi']
      · rintro ⟨⟨u, hu, heq⟩, hv⟩
        obtain ⟨u, rfl⟩ := R.surjective u
        refine ⟨⟨u, (membership ih u).mp hu, ?_⟩, ?_⟩
        · intro j hj
          exact (E j).injective (heq j hj)
        · intro i hi hi'
          apply (E i.succ).injective
          have hh := hv i hi hi'
          change E i.succ (v i.succ) = step M i (E i.castSucc (v i.castSucc)) at hh
          rw [hstep i] at hh
          exact hh
    have hC (P) : C P (k + 1) = C P k ∩ convexHull ℝ (G P) := by
      apply congrArg (fun S => C P k ∩ convexHull ℝ S)
      ext v
      apply and_congr_right
      intro _
      apply forall_congr'
      intro i
      dsimp only [step]
      rcases P.val i with ⟨A, b⟩ | h <;> rfl
    rw [hC, hC, Set.image_inter R.injective, ih]
    have hh := R.toLinearMap.image_convexHull (G N)
    change R '' convexHull ℝ (G N) = convexHull ℝ (R '' G N) at hh
    rw [hh, hG]

theorem negate_affine_output :
  let σ : ℝ → ℝ := fun t => max t 0
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
  let bounds : {d m : ℕ} → (f : Net d m) → Set (Fin d → ℝ) →
      (r : ℕ) → 1 ≤ r → r ≤ f.val.1 → (Fin m → ℝ) × (Fin m → ℝ) :=
    fun {_ _} f X r hr hL =>
      let R := Definition.WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2
        ((fun x k => x (Fin.cast f.property.1 k)) '' X) r hr hL
      ((fun j => R.2.1 (Fin.cast f.property.2.1.symm j)),
       (fun j => R.2.2 (Fin.cast f.property.2.1.symm j)))
  ∀ (d : ℕ) (f : Net d 1),
    (∃ i : Fin f.val.1, i.val + 1 = f.val.1 ∧ ∃ A b, f.val.2.2.val i = Sum.inl (A, b)) →
    ∃ g : Net d 1, f.val.1 = g.val.1 ∧
      (∀ x, eval g x 0 = -eval f x 0) ∧
      ∀ X r hr hf hg, (bounds g X r hr hg).2 0 = -(bounds f X r hr hf).1 0 := by
  classical
  intro σ Net run eval bounds d f hfinal
  let L := f.val.1
  let w := f.val.2.1
  let N := f.val.2.2
  let M : Definition.NetworkSemantics σ L w :=
    ⟨fun i => if i.val + 1 = L then
      match N.val i with
      | Sum.inl (A, b) => Sum.inl (-A, -b)
      | Sum.inr h => Sum.inr h
      else N.val i, N.property⟩
  let g : Net d 1 := ⟨⟨L, w, M⟩, f.property⟩
  let E (j : Fin (L + 1)) : (Fin (w j) → ℝ) ≃ₗ[ℝ] (Fin (w j) → ℝ) :=
    if j = Fin.last L then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ _
  let step (P : Definition.NetworkSemantics σ L w) (i : Fin L)
      (x : Fin (w i.castSucc) → ℝ) : Fin (w i.succ) → ℝ :=
    fun j => Sum.elim (fun p => (∑ k, p.1 j k * x k) + p.2 j)
      (fun h => σ (x (Fin.cast h.down.symm j))) (P.val i)
  have hzero (x) : E 0 x = x := by
    have hL : 0 < L := f.property.2.2
    simp [E, show (0 : Fin (L + 1)) ≠ Fin.last L by intro h; have := congrArg Fin.val h; simp at this; omega]
  have hstep (i : Fin L) (x) : step M i (E i.castSucc x) = E i.succ (step N i x) := by
    have hin : i.castSucc ≠ Fin.last L := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    by_cases hi : i.val + 1 = L
    · have hout : i.succ = Fin.last L := Fin.ext hi
      obtain ⟨q, hq, A, b, ha⟩ := hfinal
      have hqi : i = q := Fin.ext (by dsimp [L] at hi; omega)
      have haff : ∃ A b, N.val i = Sum.inl (A, b) := by
        subst i
        exact ⟨A, b, ha⟩
      obtain ⟨A, b, ha⟩ := haff
      funext j
      simp [step, M, E, hin, hout, hi, ha, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, add_comm]
    · have hout : i.succ ≠ Fin.last L := by
        intro h
        exact hi (congrArg Fin.val h)
      simp [step, M, E, hin, hout, hi]
  have hrun (j : Fin (L + 1)) (x : Fin (w 0) → ℝ) :
      run g j x = E j (run f j x) := by
    induction j using Fin.induction with
    | zero => exact (hzero x).symm
    | succ i ih =>
      have hg : run g i.succ x = step M i (run g i.castSucc x) := by
        dsimp only [run, Fin.induction_succ, step]
        rcases M.val i with ⟨A, b⟩ | h <;> rfl
      have hf : run f i.succ x = step N i (run f i.castSucc x) := by
        dsimp only [run, Fin.induction_succ, step]
        rcases N.val i with ⟨A, b⟩ | h <;> rfl
      rw [hg, hf, ih, hstep]
  refine ⟨g, rfl, ?_, ?_⟩
  · intro x
    change run g (Fin.last L) (fun k => x (Fin.cast f.property.1 k)) (Fin.cast f.property.2.1.symm 0) = _
    rw [hrun]
    simp only [E, if_pos rfl, LinearEquiv.neg_apply, Pi.neg_apply]
    rfl
  · intro X r hr hf hg
    let Y := (fun x k => x (Fin.cast f.property.1 k)) '' X
    have hstage := window_coordinate_change σ L w N M E hzero hstep Y r hr hf (L - r + 1)
    let S := relaxation.stages(Definition.WindowRelaxation σ L w N Y r hr hf) (L - r + 1)
    change sSup ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm 0)) ''
      relaxation.stages(Definition.WindowRelaxation σ L w M Y r hr hf) (L - r + 1)) =
      -sInf ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm 0)) '' S)
    rw [← hstage, Set.image_image]
    simp only [Function.comp_def, LinearEquiv.piCongrRight_apply, E, ite_true,
      LinearEquiv.neg_apply, Pi.neg_apply]
    have hh := Real.sSup_neg ((fun v => v (Fin.last L) (Fin.cast f.property.2.1.symm 0)) '' S)
    simpa only [← Set.image_neg_eq_neg, Set.image_image, Function.comp_def, Pi.neg_apply] using hh

-- formalizer:machinery-end

end Theorem_4p2.Machinery
