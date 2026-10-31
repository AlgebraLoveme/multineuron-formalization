module
public import Formalization.Result.helpers.Theorem_3p3.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_3p2

open Definition

public section

namespace Theorem_3p3

theorem result_3_3 :
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
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)), X.Nonempty → poly X → ¬X.Subsingleton →
  ∀ T : ℝ, 0 < T →
  ∃ (f g : Net d 1),
    let B := bounds f X 1 (by omega) f.property.2.2
    let C := bounds g X 1 (by omega) g.property.2.2
    B.1 0 ≤ sInf ((fun x => eval f x 0) '' X) - T ∧
      sSup ((fun x => eval g x 0) '' X) + T ≤ C.2 0 := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d X hX hp hn T hT
  obtain ⟨V, hV⟩ := hp
  have compactX : IsCompact X := by
    rw [hV]
    exact V.finite_toSet.isCompact_convexHull ℝ
  have convexX : Convex ℝ X := by
    rw [hV]
    exact convex_convexHull ℝ _
  -- Appendix E, Theorem 3.3: a varying coordinate has distinct attained
  -- extrema a < b; normalize that coordinate to the interval [-1,1].
  obtain ⟨k, u, v, hu, hv, huv, hext⟩ :=
    Machinery.coordinate_extrema
      compactX hX hn
  let a := u k
  let b := v k
  let t : (Fin d → ℝ) → ℝ := fun x => 2 * (x k - a) / (b - a) - 1
  have hab : a < b := huv
  have hend :=
    Machinery.normalized_endpoints hab
  have tu : t u = -1 := hend.1
  have tv : t v = 1 := hend.2
  have ht : ∀ x ∈ X, -1 ≤ t x ∧ t x ≤ 1 := by
    intro x hx
    exact Machinery.normalized_bounds
      hab (hext x hx).1 (hext x hx).2
  have hd : 0 < d := Nat.zero_lt_of_lt k.isLt
  let w : Fin 6 → ℕ := ![d, 2, 2, 4, 4, 1]
  let N (e : ℝ) : NetworkSemantics σ 5 w := by
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))))) i
      · exact Sum.inl (fun _ j => if j = k then 2 / (b - a) else 0,
          ![-2 * a / (b - a), -2 * a / (b - a) - 1])
      · exact Sum.inr ⟨rfl⟩
      · exact Sum.inl (!![1, 0; -1, 0; 0, 1; 0, -1], ![-1, 1, -1/2, 1/2])
      · exact Sum.inr ⟨rfl⟩
      · exact Sum.inl (fun _ _ => e * (2 * T), fun _ => 0)
    · intro j
      fin_cases j <;> simp [w, hd]
  let f (e : ℝ) : Net d 1 := ⟨⟨5, w, N e⟩, rfl, rfl, by norm_num⟩
  let q (x : Fin d → ℝ) : Fin 2 → ℝ := ![max (t x + 1) 0, max (t x) 0]
  let z (x : Fin 2 → ℝ) : Fin 4 → ℝ := ![x 0 - 1, 1 - x 0, x 1 - 1/2, 1/2 - x 1]
  let p (x : Fin 2 → ℝ) := 2 * T * (|x 0 - 1| + |x 1 - 1/2|)
  have rstep (e : ℝ) (x : Fin d → ℝ) (i : Fin 5) :
      run (f e) i.succ x =
        match (N e).val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * run (f e) i.castSucc x k) + b j
        | Sum.inr h => fun j => σ (run (f e) i.castSucc x (Fin.cast h.down.symm j)) := by
    simp only [run, f, Fin.induction_succ]
    cases he : (N e).val i with
    | inl ab => rcases ab with ⟨A, b⟩; rfl
    | inr h => rfl
  have rone (e : ℝ) (x : Fin d → ℝ) : run (f e) 1 x = ![t x + 1, t x] := by
    have h := rstep e x (0 : Fin 5)
    change run (f e) 1 x = (fun j =>
      (∑ l, (if l = k then 2 / (b - a) else 0) * x l) +
        (![-2*a/(b-a), -2*a/(b-a)-1] : Fin 2 → ℝ) j) at h
    rw [h]
    ext j
    fin_cases j <;> simp [t] <;> ring
  have rtwo (e : ℝ) (x : Fin d → ℝ) : run (f e) 2 x = q x := by
    have h := rstep e x (1 : Fin 5)
    change run (f e) 2 x = (fun j => max (run (f e) 1 x j) 0) at h
    rw [h, rone]
    ext j
    fin_cases j <;> rfl
  -- The four hidden ReLUs implement |z₁-1| + |z₂-1/2|. The last
  -- affine layer scales by 2T, and its sign e also constructs g = -f.
  have suffix_value (e : ℝ) (v : (j : Fin 6) → Fin (w j) → ℝ)
      (he : ∀ i : Fin 5, 2 ≤ i.val → v i.succ =
        match (N e).val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
        | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))) :
      v 5 (0 : Fin 1) = e * p (v 2) := by
    have h3 := he 2 (by decide)
    change v 3 = (fun j => (∑ l : Fin 2,
      (!![1, 0; -1, 0; 0, 1; 0, -1] : Matrix (Fin 4) (Fin 2) ℝ) j l * v 2 l) +
      (![-1, 1, -1/2, 1/2] : Fin 4 → ℝ) j) at h3
    have v3 : v 3 = z (v 2) := by
      rw [h3]
      ext j
      fin_cases j <;> simp [Fin.sum_univ_succ, z] <;> ring
    have v4 := he 3 (by decide)
    change v 4 = (fun j => max (v 3 j) 0) at v4
    rw [v3] at v4
    have h5 := congrFun (he 4 (by decide)) (0 : Fin 1)
    change v 5 (0 : Fin 1) = (∑ l : Fin 4, e * (2*T) * v 4 l) + 0 at h5
    rw [h5, v4]
    calc
      _ = e * (2*T) * ((max (v 2 (0 : Fin 2) - 1) 0 + max (1 - v 2 (0 : Fin 2)) 0) +
          (max (v 2 (1 : Fin 2) - 1/2) 0 + max (1/2 - v 2 (1 : Fin 2)) 0)) := by
        simp [Fin.sum_univ_succ, z]
        ring
      _ = e * p (v 2) := by
        rw [Machinery.relu_pair,
          Machinery.relu_pair]
        dsimp [p]
        ring
  have evaluation (e : ℝ) (x : Fin d → ℝ) : eval (f e) x 0 = e * p (q x) := by
    have he := suffix_value e (fun j => run (f e) j x) (fun i _ => rstep e x i)
    exact he.trans (congrArg (fun y => e * p y) (rtwo e x))
  have p_nonneg (y : Fin 2 → ℝ) : 0 ≤ p y :=
    mul_nonneg (by positivity) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have gap (x : Fin d → ℝ) : T ≤ p (q x) := by
    exact Machinery.scaled_distance T (t x) hT
  -- The endpoint midpoint c = (1,1/2) lies in conv(q(X)), while the
  -- two-segment distance estimate above gives p(q(x)) ≥ T for every x.
  let c : Fin 2 → ℝ := ![1, 1/2]
  have qu : q u = ![0, 0] := by simp [q, tu]
  have qv : q v = ![2, 1] := by norm_num [q, tv]
  have hc : c ∈ convexHull ℝ (q '' X) := by
    have hm := (convex_convexHull ℝ (q '' X))
      (subset_convexHull ℝ _ ⟨u, hu, rfl⟩)
      (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    convert hm using 1
    ext j
    fin_cases j <;> norm_num [c, qu, qv]
  have pc : p c = 0 := by norm_num [p, c]
  let H (e : ℝ) := convexHull ℝ (run (f e) (2 : Fin 6) ''
    ((fun x k => x (Fin.cast (f e).property.1 k)) '' X))
  have hH (e : ℝ) : H e = convexHull ℝ (q '' X) := by
    apply congrArg (convexHull ℝ)
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (rtwo e x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rtwo e x⟩
  let S (e : ℝ) : Set (Fin 1 → ℝ) := {y | ∃ v : (j : Fin ((f e).val.1 + 1)) →
    Fin ((f e).val.2.1 j) → ℝ,
    v 2 ∈ H e ∧
    (∀ j, y j = v (Fin.last (f e).val.1) (Fin.cast (f e).property.2.1.symm j)) ∧
    ∀ i : Fin (f e).val.1, (2 : Fin 6).val ≤ i.val → v i.succ =
      match (f e).val.2.2.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))}
  have S_value (e : ℝ) (y : Fin 1 → ℝ) (hy : y ∈ S e) :
      ∃ z : Fin 2 → ℝ, y 0 = e * p z := by
    obtain ⟨v, _, hy, he⟩ := hy
    refine ⟨v 2, (hy 0).trans (suffix_value e v ?_)⟩
    intro i hi
    have h := he i hi
    dsimp only [f] at h
    cases hN : (N e).val i with
    | inl ab => rcases ab with ⟨A, b⟩; simpa only [hN] using h
    | inr heq => simpa only [hN] using h
  have zeroS (e : ℝ) : (fun _ : Fin 1 => (0 : ℝ)) ∈ S e := by
    let v : (j : Fin 6) → Fin (w j) → ℝ := by
      intro j
      refine Fin.cases (fun _ => 0) (Fin.cases (fun _ => 0)
        (Fin.cases c (Fin.cases (fun _ => 0) (Fin.cases (fun _ => 0)
          (Fin.cases (fun _ => 0) (fun j => Fin.elim0 j)))))) j
    refine ⟨v, ?_, ?_, ?_⟩
    · change c ∈ H e
      rw [hH]
      exact hc
    · intro j
      rfl
    · intro i hi
      fin_cases i
      · norm_num at hi
      · norm_num at hi
      · change (fun _ : Fin 4 => (0 : ℝ)) =
          (fun j => (∑ l : Fin 2,
            (!![1, 0; -1, 0; 0, 1; 0, -1] : Matrix (Fin 4) (Fin 2) ℝ) j l * c l) +
            (![-1, 1, -1/2, 1/2] : Fin 4 → ℝ) j)
        ext j
        fin_cases j <;> norm_num [Fin.sum_univ_succ, c]
      · change (fun _ : Fin 4 => (0 : ℝ)) = (fun _ => max (0 : ℝ) 0)
        simp
      · change (fun _ : Fin 1 => (0 : ℝ)) = (fun _ => (∑ _ : Fin 4, e * (2*T) * 0) + 0)
        simp
  -- Lemma 3.2 bounds the relaxation by exact suffix continuations of
  -- conv(q(X)). The midpoint continuation has output zero for either sign.
  have relaxed (e : ℝ) := Lemma_3p2.result_3_2 d 1 (f e) X hX ⟨V, hV⟩
    (2 : Fin 6) (by norm_num) (by change 2 < 5; norm_num) (0 : Fin 1)
  have lowerS : BddBelow ((fun y => y (0 : Fin 1)) '' S 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := S_value 1 y hy
    simpa [hz] using p_nonneg z
  have upperS : BddAbove ((fun y => y (0 : Fin 1)) '' S (-1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := S_value (-1) y hy
    change y 0 ≤ 0
    rw [hz]
    nlinarith [p_nonneg z]
  have relaxation_bounds (e : ℝ) :
      (bounds (f e) X 1 (by omega) (f e).property.2.2).1 0 ≤
        sInf ((fun y => y (0 : Fin 1)) '' S e) ∧
      sSup ((fun y => y (0 : Fin 1)) '' S e) ≤
        (bounds (f e) X 1 (by omega) (f e).property.2.2).2 0 := by
    convert relaxed e using 2 <;> congr 2 <;>
      (ext y
       apply exists_congr
       intro v
       apply and_congr Iff.rfl
       apply and_congr Iff.rfl
       apply forall_congr'
       intro i
       apply imp_congr Iff.rfl
       congr 1
       cases hN : (f e).val.2.2.val i with
       | inl ab => rcases ab with ⟨A, b⟩; rfl
       | inr heq => rfl)
  have low' := (relaxation_bounds 1).1
  have high' := (relaxation_bounds (-1)).2
  have lowzero := low'.trans (csInf_le lowerS ⟨_, zeroS 1, rfl⟩)
  have highzero := (le_csSup upperS ⟨_, zeroS (-1), rfl⟩).trans high'
  have exactlow : T ≤ sInf ((fun x => eval (f 1) x 0) '' X) := by
    apply le_csInf (hX.image _)
    rintro _ ⟨x, hx, rfl⟩
    simpa [evaluation] using gap x
  -- Negating the final affine coefficients gives the same zero midpoint
  -- output and negates every exact output, yielding the upper-bound gap.
  have exacthigh : sSup ((fun x => eval (f (-1)) x 0) '' X) ≤ -T := by
    apply csSup_le (hX.image _)
    rintro _ ⟨x, hx, rfl⟩
    have he := evaluation (-1) x
    dsimp only
    nlinarith [gap x]
  -- Convexity supplies the input midpoint, whose normalized coordinate is
  -- zero. Its image is (1,0), so the exact minimum is attained at T.
  let x₀ : Fin d → ℝ := (1/2 : ℝ) • u + (1/2 : ℝ) • v
  have hx₀ : x₀ ∈ X := convexX hu hv (by norm_num) (by norm_num) (by norm_num)
  have tx₀ : t x₀ = 0 := by
    change 2 * ((1/2 * a + 1/2 * b) - a) / (b-a) - 1 = 0
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp
    <;> nlinarith
  have px₀ : p (q x₀) = T := by norm_num [p, q, tx₀]; ring
  have atmin : eval (f 1) x₀ 0 = T := by rw [evaluation, px₀]; ring
  have atmax : eval (f (-1)) x₀ 0 = -T := by rw [evaluation, px₀]; ring
  have minimum : sInf ((fun x => eval (f 1) x 0) '' X) = T := by
    apply le_antisymm _ exactlow
    apply csInf_le (s := (fun x => eval (f 1) x 0) '' X) _ ⟨x₀, hx₀, atmin⟩
    refine ⟨T, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    simpa [evaluation] using gap x
  have maximum : sSup ((fun x => eval (f (-1)) x 0) '' X) = -T := by
    apply le_antisymm exacthigh
    apply le_csSup (s := (fun x => eval (f (-1)) x 0) '' X) _ ⟨x₀, hx₀, atmax⟩
    refine ⟨-T, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    have he := evaluation (-1) x
    dsimp only
    nlinarith [gap x]
  refine ⟨f 1, f (-1), ?_, ?_⟩
  · linarith
  · linarith
  -- formalizer:proof-end
)

end Theorem_3p3
