module
public import Formalization.Result.helpers.Theorem_Ip1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_3p2

open Axioms Definition

public section

namespace Theorem_Ip1

theorem result_I_1 :
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
  ∃ f : Net d 1,
    let B := bounds f X 1 (by omega) f.property.2.2
    T * (sSup ((fun x => eval f x 0) '' X) - sInf ((fun x => eval f x 0) '' X)) ≤
      B.2 0 - B.1 0 := (by
  -- formalizer:proof-begin
  classical
  intro σ Net run eval poly bounds d X hX hp hn T hT
  obtain ⟨V, hV⟩ := hp
  have kX : IsCompact X := by
    rw [hV]
    exact V.finite_toSet.isCompact_convexHull ℝ
  -- Appendix I, affine normalization: a varying coordinate has attained,
  -- distinct endpoints, which this affine map sends to -1 and 1.
  obtain ⟨i, a, b, lo, hi, hlo, hhi, elo, ehi, hinterval⟩ :=
    Machinery.normalized_coordinate
      hX kX hn
  let Q : ℝ := max 2 T
  have hQ : 2 ≤ Q := le_max_left _ _
  have hTQ : T ≤ Q := le_max_right _ _
  let q : (Fin d → ℝ) → (Fin 2 → ℝ) := fun x =>
    ![max (a*x i+b) 0, max (1-(a*x i+b)) 0]
  let H := q '' X
  let K := convexHull ℝ H
  let h : (Fin 2 → ℝ) → ℝ := fun v => v 0 * (v 1 + v 0 - 1)
  have cq : Continuous q := by
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [q] <;> fun_prop
  have nK : K.Nonempty := (hX.image q).mono (subset_convexHull ℝ H)
  have ch : Continuous h := by dsimp [h]; fun_prop
  -- The bent curve q(t)=(rho(t),rho(1-t)) lies in the zero set of h.
  -- Its endpoint midpoint (1/2,1) lies in its convex hull and has h=1/4.
  have hz : ∀ x ∈ X, h (q x) = 0 := by
    intro x hx
    exact Machinery.bent_curve_zero
      (hinterval x hx)
  have eql : q lo = ![0, 2] := by norm_num [q, elo]
  have eqh : q hi = ![1, 0] := by simp [q, ehi]
  have midpoint : (![1/2, 1] : Fin 2 → ℝ) ∈ K := by
    have hm := (convex_convexHull ℝ H)
      (subset_convexHull ℝ H ⟨lo, hlo, rfl⟩)
      (subset_convexHull ℝ H ⟨hi, hhi, rfl⟩)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)+1/2=1)
    convert hm using 1
    rw [eql, eqh]
    ext j
    fin_cases j <;> norm_num
  have kK : IsCompact K := by
    let U : Finset (Fin 2 → ℝ) := {![0,2], ![0,1], ![1,0]}
    have cm : Convex ℝ X := by rw [hV]; exact convex_convexHull ℝ _
    let mid : Fin d → ℝ := (1/2 : ℝ) • lo + (1/2 : ℝ) • hi
    have hmid : mid ∈ X := cm hlo hhi (by norm_num) (by norm_num) (by norm_num)
    have emid : a * mid i + b = 0 := by
      dsimp [mid]
      change a * (1/2 * lo i + 1/2 * hi i) + b = 0
      nlinarith [elo, ehi]
    have eqmid : q mid = ![0,1] := by norm_num [q, emid]
    have verts : (↑U : Set (Fin 2 → ℝ)) ⊆ K := by
      intro v hv
      simp only [U, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact subset_convexHull ℝ H ⟨lo, hlo, eql⟩
      · exact subset_convexHull ℝ H ⟨mid, hmid, eqmid⟩
      · exact subset_convexHull ℝ H ⟨hi, hhi, eqh⟩
    have heq : K = convexHull ℝ (↑U : Set _) := by
      apply Set.Subset.antisymm
      · apply convexHull_min
        · rintro _ ⟨x, hx, rfl⟩
          apply Machinery.bent_curve_mem
            (convex_convexHull ℝ _) _ _ _ (hinterval x hx)
          all_goals apply subset_convexHull ℝ _; simp [U]
        · exact convex_convexHull ℝ _
      · exact convexHull_min verts (convex_convexHull ℝ H)
    rw [heq]
    exact U.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨z, hzK, hzmax⟩ := kK.exists_isMaxOn nK ch.continuousOn
  let δ := h z
  have hδ : 0 < δ := by
    have hm := hzmax midpoint
    norm_num [h] at hm
    dsimp [δ]
    linarith
  -- Approximate (2Q/δ)h on the compact hull to accuracy 1/2. The generic
  -- approximation boundary supplies a finite affine/ReLU/affine suffix.
  obtain ⟨n, c, W, β, bias, happ⟩ := ExternalUniversalApproximation σ
    (by dsimp [σ]; fun_prop)
    Machinery.relu_not_polynomial
    2 K kK (fun v => (2*Q/δ)*h v) (by fun_prop) (1/2) (by norm_num)
  let p : (Fin 2 → ℝ) → ℝ := fun v => bias + ∑ j, c j * σ ((∑ k, W j k*v k)+β j)
  have cp : Continuous p := by dsimp [p, σ]; fun_prop
  have psmall : ∀ x ∈ X, -(1/2:ℝ) ≤ p (q x) ∧ p (q x) ≤ 1/2 := by
    intro x hx
    have ha := happ (q x) (subset_convexHull ℝ H ⟨x, hx, rfl⟩)
    rw [hz x hx, mul_zero, sub_zero] at ha
    exact ⟨le_of_lt (abs_lt.mp ha).1, le_of_lt (abs_lt.mp ha).2⟩
  have pbig : 2*Q-1/2 ≤ p z := by
    have ha := (abs_lt.mp (happ z hzK)).1
    have he : (2*Q/δ)*h z = 2*Q := div_mul_cancel₀ _ (ne_of_gt hδ)
    rw [he] at ha
    dsimp [p]
    linarith
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    have hs := (psmall lo hlo).2
    simp [p] at pbig hs
    linarith
  let w : Fin 6 → ℕ := ![d, 2, 2, n, n, 1]
  let N : NetworkSemantics σ 5 w := ⟨(fun j => by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))) j
    · exact Sum.inl ((fun j k => if k = i then (if j = (0 : Fin 2) then a else -a) else 0),
        fun j => if j = (0 : Fin 2) then b else 1-b)
    · exact Sum.inr ⟨rfl⟩
    · exact Sum.inl (W, β)
    · exact Sum.inr ⟨rfl⟩
    · exact Sum.inl ((fun _ k => c k), fun _ => bias)), (by
      intro j
      fin_cases j <;> dsimp [w]
      · exact Nat.zero_lt_of_lt i.isLt
      all_goals omega)⟩
  let f : Net d 1 := ⟨⟨5, w, N⟩, rfl, rfl, by norm_num⟩
  -- Compose the normalized bent-curve prefix with the approximating suffix.
  -- The split after layer two is the interface used in Lemma 3.2.
  have prefix_eq : ∀ x : Fin d → ℝ, run f (2 : Fin 6) x = q x := by
    intro x
    apply funext
    change ∀ j : Fin 2, max ((∑ k : Fin d, (if k = i then (if j = (0 : Fin 2) then a else -a) else 0) * x k)
      + (if j = (0 : Fin 2) then b else 1-b)) 0 = q x j
    intro j
    fin_cases j <;> simp [q, ite_mul]
    congr 1
    ring
  have output : ∀ x, eval f x 0 = p (q x) := by
    intro x
    change (∑ j, c j * σ ((∑ k, W j k * run f (2 : Fin 6) x k) + β j)) + bias = p (q x)
    rw [prefix_eq]
    exact add_comm _ _
  let step : (j : Fin 5) → (Fin (w j.castSucc) → ℝ) → (Fin (w j.succ) → ℝ) :=
    fun j x => match N.val j with
      | Sum.inl (A, b) => fun k => (∑ t, A k t * x t) + b k
      | Sum.inr h => fun k => σ (x (Fin.cast h.down.symm k))
  let S : Set (Fin 1 → ℝ) := {y | ∃ v : (j : Fin 6) → Fin (w j) → ℝ,
    v 2 ∈ K ∧ (∀ j, y j = v 5 j) ∧
      ∀ k : Fin 5, 2 ≤ k.val → v k.succ = step k (v k.castSucc)}
  have suffix_image : S = (fun v => fun _ : Fin 1 => p v) '' K :=
    Machinery.suffix_image
      σ d n c W β bias K step (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  -- Lemma 3.2 preserves every exact suffix continuation from the convexified
  -- prefix. Its bounds therefore enclose p(K), including p(z) and p(q(lo)).
  have hb := Lemma_3p2.result_3_2 d 1 f X hX ⟨V, hV⟩ (2 : Fin 6)
    (by norm_num) (by norm_num) (0 : Fin 1)
  let S₀ : Set (Fin 1 → ℝ) := {y | ∃ v : (j : Fin 6) → Fin (w j) → ℝ,
    v 2 ∈ convexHull ℝ (run f (2 : Fin 6) '' (id '' X)) ∧ (∀ j, y j = v 5 j) ∧
      ∀ k : Fin 5, 2 ≤ k.val → v k.succ = step k (v k.castSucc)}
  dsimp only [f] at hb
  have hb' : (bounds f X 1 (by omega) f.property.2.2).1 0 ≤ sInf ((fun y => y 0) '' S₀) ∧
    sSup ((fun y => y 0) '' S₀) ≤ (bounds f X 1 (by omega) f.property.2.2).2 0 := by
    convert hb using 3 <;>
      (congr 1; ext y; simp only [S₀, run, f, σ, step, w, Fin.cast]; congr! 8; norm_num)
    all_goals
      rename_i k
      cases hNk : N.val k with
      | inl ab => rcases ab with ⟨A, b⟩; rfl
      | inr h => rfl
  have hs : S₀ = S := by
    dsimp only [S₀, S]
    have he : run f (2 : Fin 6) = q := funext prefix_eq
    rw [he, Set.image_id]
    rfl
  rw [hs] at hb'
  have scalar_image : (fun y => y 0) '' S = p '' K := by
    rw [suffix_image, Set.image_image]
  rw [scalar_image] at hb'
  refine ⟨f, ?_⟩
  have true_image : (fun x => eval f x 0) '' X = (fun x => p (q x)) '' X := by
    congr 1
    exact funext output
  dsimp only
  rw [true_image]
  have nt := hX.image (fun x => p (q x))
  have htlo : -(1/2 : ℝ) ≤ sInf ((fun x => p (q x)) '' X) := by
    apply le_csInf nt
    rintro _ ⟨x, hx, rfl⟩
    exact (psmall x hx).1
  have hthi : sSup ((fun x => p (q x)) '' X) ≤ (1/2 : ℝ) := by
    apply csSup_le nt
    rintro _ ⟨x, hx, rfl⟩
    exact (psmall x hx).2
  have kl := kK.image cp
  have hloK : q lo ∈ K := subset_convexHull ℝ H ⟨lo, hlo, rfl⟩
  have hloB := hb'.1.trans (csInf_le kl.bddBelow ⟨q lo, hloK, rfl⟩)
  have hhiB := (le_csSup kl.bddAbove ⟨z, hzK, rfl⟩).trans hb'.2
  -- The true width is at most one, while the relaxed width is at least
  -- 2Q-1. With Q=max(2,T), this implies the printed T-width inequality.
  exact Machinery.approximation_width
    hT hQ hTQ htlo hthi (hloB.trans (psmall lo hlo).2) (pbig.trans hhiB)
  -- formalizer:proof-end
)

end Theorem_Ip1
