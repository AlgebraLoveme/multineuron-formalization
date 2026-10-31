module
public import Formalization.Result.helpers.Theorem_4p2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Theorem_3p3
public import Formalization.Result.Lemma_4p1

open Definition

public section

namespace Theorem_4p2

theorem result_4_2 :
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
  ∀ α : ℝ, 0 < α → α < 1 →
  ∀ T : ℝ, 0 < T →
  ∃ (f g : Net d 1),
    f.val.1 = g.val.1 ∧
    let r := max 1 ⌊α * (f.val.1 : ℝ)⌋₊
    ∃ hr : 1 ≤ r, ∃ hf : r ≤ f.val.1,
    ∃ hg : r ≤ g.val.1,
    let B := bounds f X r hr hf
    let C := bounds g X r hr hg
    B.1 0 ≤ sInf ((fun x => eval f x 0) '' X) - T ∧
      sSup ((fun x => eval g x 0) '' X) + T ≤ C.2 0 := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d X hX hp hn α hα hα' T hT
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
    Theorem_3p3.Machinery.coordinate_extrema
      compactX hX hn
  let a := u k
  let b := v k
  let t : (Fin d → ℝ) → ℝ := fun x => 2 * (x k - a) / (b - a) - 1
  have hab : a < b := huv
  have hend :=
    Theorem_3p3.Machinery.normalized_endpoints hab
  have tu : t u = -1 := hend.1
  have tv : t v = 1 := hend.2
  have ht : ∀ x ∈ X, -1 ≤ t x ∧ t x ≤ 1 := by
    intro x hx
    exact Theorem_3p3.Machinery.normalized_bounds
      hab (hext x hx).1 (hext x hx).2
  have hd : 0 < d := Nat.zero_lt_of_lt k.isLt
  -- Reuse the actual prefix q = ρ ∘ W₁ ∘ W₀ ∘ π and the signed
  -- four-ReLU distance suffix from Theorem 3.3.
  let wq : Fin 3 → ℕ := ![d, 2, 2]
  let nq : NetworkSemantics σ 2 wq := by
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
      · exact Sum.inl (fun _ j => if j = k then 2 / (b - a) else 0,
          ![-2 * a / (b - a), -2 * a / (b - a) - 1])
      · exact Sum.inr ⟨rfl⟩
    · intro j
      fin_cases j <;> simp [wq, hd]
  let Q : Net d 2 := ⟨⟨2, wq, nq⟩, rfl, rfl, by norm_num⟩
  let wp : Fin 4 → ℕ := ![2, 4, 4, 1]
  let np (e : ℝ) : NetworkSemantics σ 3 wp := by
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
      · exact Sum.inl (!![1, 0; -1, 0; 0, 1; 0, -1], ![-1, 1, -1/2, 1/2])
      · exact Sum.inr ⟨rfl⟩
      · exact Sum.inl (fun _ _ => e * (2 * T), fun _ => 0)
    · intro j
      fin_cases j <;> simp [wp]
  let P (e : ℝ) : Net 2 1 := ⟨⟨3, wp, np e⟩, rfl, rfl, by norm_num⟩
  let q (x : Fin d → ℝ) : Fin 2 → ℝ := ![max (t x + 1) 0, max (t x) 0]
  let p (x : Fin 2 → ℝ) := 2 * T * (|x 0 - 1| + |x 1 - 1/2|)
  have evalQ (x : Fin d → ℝ) : eval Q x = q x := by
    have h1 : run Q 1 x = ![t x + 1, t x] := by
      change (fun j => (∑ l, (if l = k then 2 / (b - a) else 0) * x l) +
        (![-2*a/(b-a), -2*a/(b-a)-1] : Fin 2 → ℝ) j) = _
      ext j
      fin_cases j <;> simp [t] <;> ring
    change (fun j => max (run Q 1 x j) 0) = q x
    rw [h1]
    ext j
    fin_cases j <;> rfl
  have evalP (e : ℝ) (x : Fin 2 → ℝ) : eval (P e) x 0 = e * p x := by
    change (∑ l : Fin 4, e * (2*T) * max
      ((∑ j : Fin 2, (!![1, 0; -1, 0; 0, 1; 0, -1] : Matrix (Fin 4) (Fin 2) ℝ) l j * x j) +
        (![-1, 1, -1/2, 1/2] : Fin 4 → ℝ) l) 0) + 0 = _
    calc
      _ = e * (2*T) * ((max (x 0 - 1) 0 + max (1 - x 0) 0) +
          (max (x 1 - 1/2) 0 + max (1/2 - x 1) 0)) := by
        simp [Fin.sum_univ_succ]
        congr 1 <;> ring
      _ = e * p x := by
        rw [Theorem_3p3.Machinery.relu_pair,
          Theorem_3p3.Machinery.relu_pair]
        dsimp [p]
        ring
  have p_nonneg (y : Fin 2 → ℝ) : 0 ≤ p y :=
    mul_nonneg (by positivity) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have gap (x : Fin d → ℝ) : T ≤ p (q x) := by
    exact Theorem_3p3.Machinery.scaled_distance T (t x) hT
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
  -- Lemma 4.1 inserts counted affine identities and retains the final
  -- affine layer of the detector. Its overlapping-window construction gives
  -- ell(f) ≤ min p(conv(q(X))) without changing the exact function on X.
  obtain ⟨f, _, hfinalf, _, hevalf, hr, hf, hlo, _⟩ :=
    Machinery.padding_with_depth
      d 2 Q (P 1) X hX ⟨V, hV⟩ α hα hα'
  change ∀ x ∈ X, eval f x = eval (P 1) (eval Q x) at hevalf
  have hq : eval Q '' X = q '' X := by
    congr 1
    funext x
    exact evalQ x
  have lowerS : BddBelow ((fun z => eval (P 1) z 0) '' convexHull ℝ (eval Q '' X)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa [evalP] using p_nonneg z
  have hzero : 0 ∈ (fun z => eval (P 1) z 0) '' convexHull ℝ (eval Q '' X) := by
    refine ⟨c, ?_, ?_⟩
    · rw [hq]; exact hc
    · change eval (P 1) c 0 = 0
      rw [evalP, pc, mul_zero]
  have hull_minimum : sInf ((fun z => eval (P 1) z 0) '' convexHull ℝ (eval Q '' X)) = 0 := by
    apply le_antisymm (csInf_le lowerS hzero)
    apply le_csInf ⟨0, hzero⟩
    rintro _ ⟨z, _, rfl⟩
    simpa [evalP] using p_nonneg z
  have lowzero := hlo.trans hull_minimum.le
  have exactlow : T ≤ sInf ((fun x => eval f x 0) '' X) := by
    apply le_csInf (hX.image _)
    rintro _ ⟨x, hx, rfl⟩
    change T ≤ eval f x 0
    rw [hevalf x hx, evalP, evalQ, one_mul]
    exact gap x
  -- The input midpoint has normalized coordinate zero and output T;
  -- together with the two-segment estimate this gives min f(X) = T.
  let x₀ : Fin d → ℝ := (1/2 : ℝ) • u + (1/2 : ℝ) • v
  have hx₀ : x₀ ∈ X := convexX hu hv (by norm_num) (by norm_num) (by norm_num)
  have tx₀ : t x₀ = 0 := by
    change 2 * ((1/2 * a + 1/2 * b) - a) / (b-a) - 1 = 0
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp
    <;> nlinarith
  have px₀ : p (q x₀) = T := by norm_num [p, q, tx₀]; ring
  have minimum : sInf ((fun x => eval f x 0) '' X) = T := by
    apply le_antisymm _ exactlow
    apply csInf_le (s := (fun x => eval f x 0) '' X)
    · refine ⟨T, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      change T ≤ eval f x 0
      rw [hevalf x hx, evalP, evalQ, one_mul]
      exact gap x
    · refine ⟨x₀, hx₀, ?_⟩
      change eval f x₀ 0 = T
      rw [hevalf x₀ hx₀, evalP, evalQ, one_mul, px₀]
  -- Negate only the final affine layer. The coordinate reflection fixes all
  -- preceding variables and carries each sequential window graph hull and
  -- intersection to its counterpart, giving u(g) = -ell(f) at the same L,r.
  have haff : ∃ i : Fin f.val.1, i.val + 1 = f.val.1 ∧
      ∃ A b, f.val.2.2.val i = Sum.inl (A, b) := by
    apply hfinalf
    exact ⟨2, rfl, _, _, rfl⟩
  obtain ⟨g, same, hevalg, hreflect⟩ :=
    Machinery.negate_affine_output
      d f haff
  have hg : max 1 ⌊α * (f.val.1 : ℝ)⌋₊ ≤ g.val.1 := by rw [← same]; exact hf
  have maximum : sSup ((fun x => eval g x 0) '' X) = -T := by
    have hfun : (fun x => eval g x 0) = fun x => -eval f x 0 := funext hevalg
    rw [hfun, ← minimum]
    simpa only [← Set.image_neg_eq_neg, Set.image_image, Function.comp_def] using
      Real.sSup_neg ((fun x => eval f x 0) '' X)
  -- Corrected Theorem 4.2: ell(f) ≤ 0 = min f(X)-T; reflection
  -- also gives max g(X)+T = 0 ≤ u(g).
  refine ⟨f, g, same, hr, hf, hg, ?_, ?_⟩
  · change (bounds f X _ hr hf).1 0 ≤ sInf ((fun x => eval f x 0) '' X) - T
    rw [minimum, sub_self]
    exact lowzero
  · change sSup ((fun x => eval g x 0) '' X) + T ≤ (bounds g X _ hr hg).2 0
    rw [maximum, hreflect X _ hr hf hg]
    linarith
  -- formalizer:proof-end
)

end Theorem_4p2
