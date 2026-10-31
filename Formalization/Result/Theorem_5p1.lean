module
public import Formalization.Result.helpers.Theorem_5p1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Theorem_5p1

theorem result_5_1 :
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
    X.Nonempty → poly X → ¬X.Subsingleton →
    ∃ g : Net d m, (∀ x ∈ X, eval g x = eval f x) ∧
      let B := bounds g X 1 (by omega) g.property.2.2
      ∀ j, B.1 j = sInf ((fun x => eval f x j) '' X) ∧
        B.2 j = sSup ((fun x => eval f x j) '' X) := (by
  -- formalizer:proof-begin
  classical
  intro σ Net Run eval poly bounds d m f X hX hpoly hnonsingleton
  let run := Run f
  let F : (Fin d → ℝ) → Fin m → ℝ := eval f
  -- Appendix G, Theorem 5.1: compactness and continuity give attained
  -- coordinate extrema; the minimizing points may differ by coordinate.
  have hcompact : IsCompact X := by
    obtain ⟨V, rfl⟩ := hpoly
    exact V.finite_toSet.isCompact_convexHull ℝ
  have hrun (j : Fin (f.val.1 + 1)) : Continuous (run j) := by
    induction j using Fin.induction with
    | zero => exact continuous_id
    | succ i ih =>
      dsimp only [run, Run, Fin.induction_succ, σ]
      split
      · apply continuous_pi
        intro j
        exact (continuous_finset_sum _ (fun k _ =>
          continuous_const.mul ((continuous_apply k).comp ih))).add continuous_const
      · apply continuous_pi
        intro j
        exact (((continuous_apply _).comp ih).max continuous_const)
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    have hpre : Continuous (fun x : Fin d → ℝ =>
        fun k : Fin (f.val.2.1 0) => x (Fin.cast f.property.1 k)) :=
      continuous_pi (fun k => continuous_apply (Fin.cast f.property.1 k))
    exact ((continuous_apply (Fin.cast f.property.2.1.symm j)).comp
      (hrun (Fin.last f.val.1))).comp hpre
  let lo : Fin m → ℝ := fun j => sInf ((fun x => F x j) '' X)
  let hi : Fin m → ℝ := fun j => sSup ((fun x => F x j) '' X)
  have hcoord (j : Fin m) : IsCompact ((fun x => F x j) '' X) :=
    hcompact.image ((continuous_apply j).comp hF)
  have hnonempty (j : Fin m) : ((fun x => F x j) '' X).Nonempty :=
    hX.image _
  have hlo (j : Fin m) : ∃ x ∈ X, F x j = lo j :=
    (hcoord j).sInf_mem (hnonempty j)
  have hhi (j : Fin m) : ∃ x ∈ X, F x j = hi j :=
    (hcoord j).sSup_mem (hnonempty j)
  have hrange (x) (hx : x ∈ X) (j : Fin m) : lo j ≤ F x j ∧ F x j ≤ hi j :=
    ⟨csInf_le (hcoord j).bddBelow ⟨x, hx, rfl⟩,
     le_csSup (hcoord j).bddAbove ⟨x, hx, rfl⟩⟩
  have horder (j : Fin m) : lo j ≤ hi j := by
    obtain ⟨x, hx⟩ := hX
    exact (hrange x hx j).1.trans (hrange x hx j).2
  -- The clipping map c(y) = lo + ρ(y-lo) - ρ(y-hi) fixes f(X)
  -- and sends every input into the same coordinate box, even if lo = hi.
  have hclip_eq (x) (hx : x ∈ X) (j : Fin m) :
      lo j + max (F x j - lo j) 0 - max (F x j - hi j) 0 = F x j :=
    Machinery.clipping_eq
      _ _ _ (hrange x hx j).1 (hrange x hx j).2
  have hclip_bounds (y : Fin m → ℝ) (j : Fin m) :
      lo j ≤ lo j + max (y j - lo j) 0 - max (y j - hi j) 0 ∧
      lo j + max (y j - lo j) 0 - max (y j - hi j) 0 ≤ hi j :=
    Machinery.clipping_bounds
      _ _ _ (horder j)
  -- Realize c by the paper's three layers: paired offsets, a joint ReLU,
  -- then the affine difference plus lo. Retain all original layers of f.
  let o := f.val.2.1 (Fin.last f.val.1)
  have ho : 0 < o := f.val.2.2.property (Fin.last f.val.1)
  let a : Fin o → ℝ := fun j => lo (Fin.cast f.property.2.1 j)
  let b : Fin o → ℝ := fun j => hi (Fin.cast f.property.2.1 j)
  let A : Matrix (Fin (o + o)) (Fin o) ℝ :=
    Fin.addCases (fun j k => if j = k then 1 else 0)
      (fun j k => if j = k then 1 else 0)
  let bias : Fin (o + o) → ℝ := Fin.addCases (fun j => -a j) (fun j => -b j)
  obtain ⟨N1, hp1, hl1⟩ :=
    Machinery.exists_layer_extension
      (fun t : ℝ => max t 0) f.val.1 f.val.2.1 f.val.2.2
      (o + o) (by omega) (Sum.inl (A, bias))
  let W1 : Fin (f.val.1 + 1 + 1) → ℕ := Fin.snoc f.val.2.1 (o + o)
  obtain ⟨N2, hp2, hl2⟩ :=
    Machinery.exists_layer_extension
      (fun t : ℝ => max t 0) (f.val.1 + 1) W1 N1
      (o + o) (by omega) (Sum.inr ⟨by simp [W1]⟩)
  let W2 : Fin (f.val.1 + 1 + 1 + 1) → ℕ := Fin.snoc W1 (o + o)
  let D : Matrix (Fin o) (Fin (o + o)) ℝ := fun j =>
    Fin.addCases (fun k => if j = k then 1 else 0)
      (fun k => if j = k then -1 else 0)
  have hoffset (y : Fin o → ℝ) :
      (fun j => (∑ k, A j k * y k) + bias j) =
        Fin.addCases (fun j => y j - a j) (fun j => y j - b j) :=
    Machinery.offset_matrix_evaluation
      o a b y
  have hrealization (y : Fin o → ℝ) (j : Fin o) :
      (∑ k, D j k * max ((∑ t, A k t * y t) + bias k) 0) + a j =
        a j + max (y j - a j) 0 - max (y j - b j) 0 := by
    rw [Machinery.difference_matrix_evaluation]
    have hp := congr_fun (hoffset y) (Fin.castAdd o j)
    have hq := congr_fun (hoffset y) (Fin.natAdd o j)
    simp only [Fin.addCases_left, Fin.addCases_right] at hp hq
    rw [hp, hq]
  -- The explicit matrices implement the clipping formula, so their
  -- composition fixes every actual output of f on X.
  have hmatrices_fix (x) (hx : x ∈ X) (j : Fin o) :
      let y := fun k : Fin o => F x (Fin.cast f.property.2.1 k)
      (∑ k, D j k * max ((∑ t, A k t * y t) + bias k) 0) + a j = y j := by
    dsimp only
    rw [hrealization]
    exact hclip_eq x hx (Fin.cast f.property.2.1 j)
  let out : (Matrix (Fin o) (Fin (W2 (Fin.last (f.val.1 + 1 + 1)))) ℝ ×
      (Fin o → ℝ)) ⊕ PLift (W2 (Fin.last (f.val.1 + 1 + 1)) = o) :=
    cast (by simp only [W2, Fin.snoc_last]) (Sum.inl (D, a) : (Matrix (Fin o) (Fin (o + o)) ℝ × (Fin o → ℝ)) ⊕ PLift (o + o = o))
  obtain ⟨N3, hp3, hl3⟩ :=
    Machinery.exists_layer_extension
      (fun t : ℝ => max t 0) (f.val.1 + 1 + 1) W2 N2 o ho out
  let W3 : Fin (f.val.1 + 1 + 1 + 1 + 1) → ℕ := Fin.snoc W2 o
  have hg : W3 0 = d ∧ W3 (Fin.last (f.val.1 + 1 + 1 + 1)) = m ∧
      0 < f.val.1 + 1 + 1 + 1 := by
    refine ⟨?_, ?_, by omega⟩
    · simpa only [W3, W2, W1, Fin.snoc_apply_zero] using f.property.1
    · simpa only [W3, Fin.snoc_last, o] using f.property.2.1
  have hoffsets_in_g : HEq
      (N3.val (Fin.last f.val.1).castSucc.castSucc) (Sum.inl (A, bias) :
        (Matrix (Fin (o + o)) (Fin o) ℝ × (Fin (o + o) → ℝ)) ⊕ PLift (o = o + o)) :=
    (hp3 _).trans ((hp2 _).trans hl1)
  have hrelu_in_g : HEq (N3.val (Fin.last (f.val.1 + 1)).castSucc)
      (Sum.inr ⟨show W1 (Fin.last (f.val.1 + 1)) = o + o by simp [W1]⟩ :
        (Matrix (Fin (o + o)) (Fin (W1 (Fin.last (f.val.1 + 1)))) ℝ ×
          (Fin (o + o) → ℝ)) ⊕ PLift (W1 (Fin.last (f.val.1 + 1)) = o + o)) :=
    (hp3 _).trans hl2
  let g1 : Net d (o + o) := ⟨⟨f.val.1 + 1, W1, N1⟩, by
    refine ⟨?_, ?_, Nat.zero_lt_succ _⟩
    · simpa only [W1, Fin.snoc_apply_zero] using f.property.1
    · simp only [W1, Fin.snoc_last]⟩
  let g2 : Net d (o + o) := ⟨⟨f.val.1 + 1 + 1, W2, N2⟩, by
    refine ⟨?_, ?_, Nat.zero_lt_succ _⟩
    · simpa only [W2, W1, Fin.snoc_apply_zero] using f.property.1
    · simp only [W1, W2, Fin.snoc_last]⟩
  let g : Net d m := ⟨⟨f.val.1 + 1 + 1 + 1, W3, N3⟩, hg⟩
  let input {m : ℕ} (q : Net d m) (x : Fin d → ℝ) : Fin (q.val.2.1 0) → ℝ :=
    fun k => x (Fin.cast q.property.1 k)
  have hinput {m : ℕ} (q : Net d m) (x : Fin d → ℝ) : HEq (input q x) x :=
    Machinery.cast_input_heq _ _
  have hstep {m : ℕ} (q : Net d m) (x : Fin d → ℝ) (i : Fin q.val.1) :
      Run q i.succ (input q x) =
        match q.val.2.2.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * Run q i.castSucc (input q x) k) + b j
        | Sum.inr h => fun j => σ (Run q i.castSucc (input q x) (Fin.cast h.down.symm j)) := by
    dsimp only [Run, Fin.induction_succ]
  have hprefix1 (x : Fin d → ℝ) :=
    Machinery.extension_trajectory_prefix
      σ f.val.1 f.val.2.1 f.val.2.2 (o + o) N1 hp1
      (fun j => Run f j (input f x)) (fun j => Run g1 j (input g1 x))
      ((hinput g1 x).trans (hinput f x).symm) (by intro i; have hh := hstep f x i; cases h : f.val.2.2.val i <;> simpa only [h] using hh) (by intro i; have hh := hstep g1 x i; cases h : N1.val i <;> simpa only [h, g1] using hh)
  have hprefix2 (x : Fin d → ℝ) :=
    Machinery.extension_trajectory_prefix
      σ (f.val.1 + 1) W1 N1 (o + o) N2 hp2
      (fun j => Run g1 j (input g1 x)) (fun j => Run g2 j (input g2 x))
      ((hinput g2 x).trans (hinput g1 x).symm) (by intro i; have hh := hstep g1 x i; cases h : N1.val i <;> simpa only [h, g1] using hh) (by intro i; have hh := hstep g2 x i; cases h : N2.val i <;> simpa only [h, g2] using hh)
  have hprefix3 (x : Fin d → ℝ) :=
    Machinery.extension_trajectory_prefix
      σ (f.val.1 + 1 + 1) W2 N2 o N3 hp3
      (fun j => Run g2 j (input g2 x)) (fun j => Run g j (input g x))
      ((hinput g x).trans (hinput g2 x).symm) (by intro i; have hh := hstep g2 x i; cases h : N2.val i <;> simpa only [h, g2] using hh) (by intro i; have hh := hstep g x i; cases h : N3.val i <;> simpa only [h, g] using hh)
  have houtput1 (x : Fin d → ℝ) :=
    Machinery.extension_trajectory_output
      σ f.val.1 f.val.2.1 (o + o) N1 (Sum.inl (A, bias)) hl1
      (fun j => Run g1 j (input g1 x)) (Run f (Fin.last f.val.1) (input f x))
      (hprefix1 x (Fin.last f.val.1)) (by intro i; have hh := hstep g1 x i; cases h : N1.val i <;> simpa only [h, g1] using hh)
  have houtput2 (x : Fin d → ℝ) :=
    Machinery.extension_trajectory_output
      σ (f.val.1 + 1) W1 (o + o) N2 (Sum.inr ⟨by simp [W1]⟩) hl2
      (fun j => Run g2 j (input g2 x)) (Run g1 (Fin.last (f.val.1 + 1)) (input g1 x))
      (hprefix2 x (Fin.last (f.val.1 + 1))) (by intro i; have hh := hstep g2 x i; cases h : N2.val i <;> simpa only [h, g2] using hh)
  have houtput3 (x : Fin d → ℝ) :=
    Machinery.extension_trajectory_output
      σ (f.val.1 + 1 + 1) W2 o N3 out hl3
      (fun j => Run g j (input g x)) (Run g2 (Fin.last (f.val.1 + 1 + 1)) (input g2 x))
      (hprefix3 x (Fin.last (f.val.1 + 1 + 1))) (by intro i; have hh := hstep g x i; cases h : N3.val i <;> simpa only [h, g] using hh)
  have heval1 (x : Fin d → ℝ) (j : Fin (o + o)) : eval g1 x j =
      (∑ k, A j k * Run f (Fin.last f.val.1) (input f x) k) + bias j := by
    exact Machinery.heq_apply_cast
      g1.property.2.1 _ _ (houtput1 x) j
  have heval2 (x : Fin d → ℝ) (j : Fin (o + o)) :
      eval g2 x j = max (eval g1 x j) 0 := by
    exact Machinery.heq_apply_cast
      g2.property.2.1 _ _ (houtput2 x) j
  have heval3 (x : Fin d → ℝ) (j : Fin o) :
      eval g x (Fin.cast f.property.2.1 j) = (∑ k, D j k * eval g2 x k) + a j := by
    have hx2 : HEq (Run g2 (Fin.last g2.val.1) (input g2 x)) (eval g2 x) :=
      (Machinery.cast_input_heq
        g2.property.2.1.symm (Run g2 (Fin.last g2.val.1) (input g2 x))).symm
    have hc := Machinery.layer_application_heq
      σ (show W2 (Fin.last (f.val.1 + 1 + 1)) = o + o by simp [W2]) rfl
      out (Sum.inl (D, a)) (cast_heq _ _) _ _ hx2
    have hout := houtput3 x
    have he : HEq (Run g (Fin.last g.val.1) (input g x))
        (fun j => (∑ k, D j k * eval g2 x k) + a j) := by
      cases hO : out <;> simp only [hO] at hout hc <;> exact hout.trans hc
    have hval := Machinery.heq_apply_cast
      (show W3 (Fin.last (f.val.1 + 1 + 1 + 1)) = o by simp [W3]) _ _ he j
    simpa only [eval, input, g, Fin.cast_cast] using hval
  have hequal (x : Fin d → ℝ) (hx : x ∈ X) : eval g x = eval f x := by
    funext j
    let j0 : Fin o := Fin.cast f.property.2.1.symm j
    have hj : Fin.cast f.property.2.1 j0 = j := by simp [j0]
    rw [← hj, heval3]
    simp_rw [heval2, heval1]
    have hraw (k : Fin o) : Run f (Fin.last f.val.1) (input f x) k =
        F x (Fin.cast f.property.2.1 k) := by
      simp only [F, eval, input, Fin.cast_cast, Fin.cast_refl, id_eq]
    simp_rw [hraw]
    exact hmatrices_fix x hx j0
  let inputSet := (fun x => input g x) '' X
  let C := relaxation.stages(WindowRelaxation σ g.val.1 g.val.2.1 g.val.2.2 inputSet 1
    (by omega) g.property.2.2) g.val.1
  let outputs (j : Fin m) : Set ℝ :=
    (fun v : (q : Fin (g.val.1 + 1)) → Fin (g.val.2.1 q) → ℝ =>
      v (Fin.last g.val.1) (Fin.cast g.property.2.1.symm j)) '' C
  -- Exact trajectories survive every window hull, so the attained extrema
  -- of f remain feasible outputs of g's relaxation (the reverse inequalities).
  have hsound (x : Fin d → ℝ) (hx : x ∈ X) :
      (fun q => Run g q (input g x)) ∈ C := by
    apply Machinery.relaxation_contains_trajectory
      σ g.val.1 g.val.2.1 g.val.2.2 inputSet 1 (by omega) g.property.2.2
      (fun q => Run g q (input g x))
    · exact ⟨x, hx, rfl⟩
    · intro i
      have hh := hstep g x i
      cases h : g.val.2.2.val i <;> simpa only [h] using hh
  have hfeasible (x : Fin d → ℝ) (hx : x ∈ X) (j : Fin m) :
      eval f x j ∈ outputs j := by
    have h : eval g x j ∈ outputs j := ⟨_, hsound x hx, rfl⟩
    rw [hequal x hx] at h
    exact h
  have hlo_feasible (j : Fin m) : lo j ∈ outputs j := by
    obtain ⟨x, hx, he⟩ := hlo j
    rw [← he]
    exact hfeasible x hx j
  have hhi_feasible (j : Fin m) : hi j ∈ outputs j := by
    obtain ⟨x, hx, he⟩ := hhi j
    rw [← he]
    exact hfeasible x hx j
  -- The first affine layer fixes the paired difference at hi-lo. The joint
  -- ReLU hull preserves 0 ≤ p-q ≤ hi-lo; the last affine layer adds lo.
  have hbounded (j : Fin m) : ∀ z ∈ outputs j, lo j ≤ z ∧ z ≤ hi j := by
    let i0 : Fin g.val.1 := (Fin.last f.val.1).castSucc.castSucc
    let i1 : Fin g.val.1 := (Fin.last (f.val.1 + 1)).castSucc
    let i2 : Fin g.val.1 := Fin.last (f.val.1 + 1 + 1)
    have h0in : g.val.2.1 i0.castSucc = o := by
      simp only [g, W3, W2, W1, i0, Fin.snoc_castSucc, o]
    have h0out : g.val.2.1 i0.succ = o + o := by
      simp only [g, W3, W2, W1, i0, ← Fin.castSucc_succ, Fin.succ_last,
        Fin.snoc_castSucc, Fin.snoc_last]
    have h1in : g.val.2.1 i1.castSucc = o + o := by
      simp only [g, W3, W2, W1, i1, Fin.snoc_castSucc, Fin.snoc_last]
    have h1out : g.val.2.1 i1.succ = o + o := by
      simp only [g, W3, W2, i1, ← Fin.castSucc_succ, Fin.succ_last,
        Fin.snoc_castSucc, Fin.snoc_last]
    have h2in : g.val.2.1 i2.castSucc = o + o := by
      simp only [g, W3, W2, i2, Fin.snoc_castSucc, Fin.snoc_last]
    have h2out : g.val.2.1 i2.succ = o := by
      simp only [g, W3, i2, Fin.succ_last, Fin.snoc_last]
    have hfirst := Machinery.relaxation_affine_cast_equation
      σ g.val.1 g.val.2.1 g.val.2.2 inputSet g.property.2.2 i0 i1.val
      (by simp [i0, i1]) o (o + o) h0in h0out A bias hoffsets_in_g
    have hlast := Machinery.relaxation_affine_cast_equation
      σ g.val.1 g.val.2.1 g.val.2.2 inputSet g.property.2.2 i2 g.val.1
      (by simp [i2, g]) (o + o) o h2in h2out D a (hl3.trans (cast_heq _ _))
    have hrelu : g.val.2.2.val i1 = Sum.inr ⟨h1in.trans h1out.symm⟩ := by
      apply Machinery.relu_layer_eq_of_heq h1in h1out
      apply hrelu_in_g.trans
      exact Machinery.relu_layer_heq
        (by simp [W1]) rfl _
    let j0 : Fin o := Fin.cast f.property.2.1.symm j
    let p : Fin (g.val.2.1 i1.succ) := Fin.cast h1out.symm (Fin.castAdd o j0)
    let q : Fin (g.val.2.1 i1.succ) := Fin.cast h1out.symm (Fin.natAdd o j0)
    have hpre : ∀ u ∈ relaxation.stages(WindowRelaxation σ g.val.1 g.val.2.1 g.val.2.2 inputSet 1
        (by omega) g.property.2.2) i1.val,
        0 ≤ u i1.castSucc (Fin.cast (h1in.trans h1out.symm).symm p) -
          u i1.castSucc (Fin.cast (h1in.trans h1out.symm).symm q) ∧
        u i1.castSucc (Fin.cast (h1in.trans h1out.symm).symm p) -
          u i1.castSucc (Fin.cast (h1in.trans h1out.symm).symm q) ≤ b j0 - a j0 := by
      intro u hu
      have hp := hfirst u hu (Fin.castAdd o j0)
      have hq := hfirst u hu (Fin.natAdd o j0)
      have hh := hoffset (fun t => u i0.castSucc (Fin.cast h0in.symm t))
      have hhp := congr_fun hh (Fin.castAdd o j0)
      have hhq := congr_fun hh (Fin.natAdd o j0)
      simp only [Fin.addCases_left, Fin.addCases_right] at hhp hhq
      simp only [p, q, Fin.cast_cast]
      have hab : a j0 ≤ b j0 := horder _
      change 0 ≤ u i0.succ (Fin.cast h0out.symm (Fin.castAdd o j0)) -
          u i0.succ (Fin.cast h0out.symm (Fin.natAdd o j0)) ∧
        u i0.succ (Fin.cast h0out.symm (Fin.castAdd o j0)) -
          u i0.succ (Fin.cast h0out.symm (Fin.natAdd o j0)) ≤ b j0 - a j0
      constructor <;> linarith
    have hdiff := Machinery.relaxation_relu_difference
      g.val.1 g.val.2.1 g.val.2.2 inputSet g.property.2.2 i1 g.val.1
      (by simp [i1, g]) (h1in.trans h1out.symm) hrelu p q (b j0 - a j0) hpre
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hz
    have hd := hdiff v hv
    have hz := hlast v hv j0
    have hm := Machinery.difference_matrix_evaluation
      o a (fun t => v i2.castSucc (Fin.cast h2in.symm t)) j0
    have hlo0 : a j0 = lo j := by simp [a, j0]
    have hhi0 : b j0 = hi j := by simp [b, j0]
    simp only [p, q] at hd
    have houtput : v (Fin.last g.val.1) (Fin.cast g.property.2.1.symm j) =
        a j0 + v i1.succ p - v i1.succ q := by
      simpa only [j0, p, q, i1, i2, Fin.cast_cast] using hz.trans hm
    change lo j ≤ v (Fin.last g.val.1) (Fin.cast g.property.2.1.symm j) ∧
      v (Fin.last g.val.1) (Fin.cast g.property.2.1.symm j) ≤ hi j
    rw [houtput]
    constructor <;> linarith [hd.1, hd.2]

  refine ⟨g, hequal, ?_⟩
  intro B j
  -- Once every relaxed output lies in the box, feasible attained endpoints
  -- force both infimum and supremum to equal the true coordinate extrema.
  have h := Machinery.extrema_of_bounded_set_with_endpoints
    (outputs j) (lo j) (hi j) (hlo_feasible j) (hhi_feasible j) (hbounded j)
  simpa only [B, bounds, WindowRelaxation, outputs, C, inputSet, input, lo, hi, F,
    Nat.sub_add_cancel g.property.2.2] using h
  -- formalizer:proof-end
)

end Theorem_5p1
