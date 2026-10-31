module
public import Formalization.Result.helpers.Theorem_Jp3.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Proposition_Jp2

open Definition

public section

namespace Theorem_Jp3

theorem result_J_3 (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ t, σ t = p.eval t) :
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
  intro Net run eval poly bounds d X hX hp hn T hT
  obtain ⟨V, hV⟩ := hp
  have cX : IsCompact X := by
    rw [hV]
    exact V.finite_toSet.isCompact_convexHull ℝ
  -- J.2 supplies a compact network image strictly smaller than its hull.
  obtain ⟨m, q, hq⟩ := Proposition_Jp2.result_J_2 σ hσ hnp d X hX ⟨V, hV⟩ hn
  have crun (j : Fin (q.val.1 + 1)) : Continuous (run q j) := by
    induction j using Fin.induction with
    | zero => exact continuous_id
    | succ i ih =>
      have hs : run q i.succ = fun x =>
          match q.val.2.2.val i with
          | Sum.inl (A, b) => fun j => (∑ k, A j k * run q i.castSucc x k) + b j
          | Sum.inr h => fun j => σ (run q i.castSucc x (Fin.cast h.down.symm j)) := by
        funext x
        simp only [run, Fin.induction_succ]
        rfl
      rw [hs]
      cases he : q.val.2.2.val i with
      | inl ab => rcases ab with ⟨A, b⟩; fun_prop
      | inr h => fun_prop
  have cq : Continuous (eval q) := by
    dsimp only [eval]
    fun_prop
  obtain ⟨c, hc, hcn⟩ := Set.exists_of_ssubset hq.1
  let E := EuclideanSpace ℝ (Fin m)
  let e := (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm
  let H : Set E := e '' (eval q '' X)
  have hH : H.Nonempty := (hX.image (eval q)).image e
  have cH : IsCompact H := (cX.image cq).image (PiLp.continuous_toLp 2 _)
  have hcH : e c ∉ H := by
    rintro ⟨z, hz, he⟩
    exact hcn (e.injective he ▸ hz)
  let δ := Metric.infDist (e c) H
  have hδ : 0 < δ := (cH.isClosed.notMem_iff_infDist_pos hH).mp hcH
  -- Compactness separates c from H by δ>0. Scale the Euclidean distance
  -- by 2T/δ, as in Appendix J, so it is zero at c and at least 2T on H.
  let p₀ : (Fin m → ℝ) → ℝ := fun z => (2*T/δ) * ‖e z - e c‖
  have cp₀ : Continuous p₀ := by
    dsimp [p₀, e]
    fun_prop
  have pc : p₀ c = 0 := by simp [p₀]
  have pgap (x) (hx : x ∈ X) : 2*T ≤ p₀ (eval q x) := by
    have hd := Metric.infDist_le_dist_of_mem (x := e c)
      (show e (eval q x) ∈ H from ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
    rw [dist_eq_norm, norm_sub_rev] at hd
    have hs : (2*T/δ)*δ = 2*T := div_mul_cancel₀ _ (ne_of_gt hδ)
    calc
      2*T = (2*T/δ)*δ := hs.symm
      _ ≤ p₀ (eval q x) := mul_le_mul_of_nonneg_left hd (by positivity)
  have cK : IsCompact (convexHull ℝ (eval q '' X)) := by
    have ck := Lemma_Jp1.Machinery.compact_convexHull m H cH
    have hi := e.symm.toLinearMap.image_convexHull H
    have he : e.symm '' H = eval q '' X := by
      simp [H, Set.image_image]
    change e.symm '' convexHull ℝ H = convexHull ℝ (e.symm '' H) at hi
    rw [he] at hi
    rw [← hi]
    exact ck.image (PiLp.continuous_ofLp 2 _)
  -- Approximate the scaled distance on the compact hull with ε=T/2.
  obtain ⟨n, hnpos, a, W, b, β, happ⟩ := Machinery.approximate_scalar σ hσ hnp
    (convexHull ℝ (eval q '' X)) cK p₀ cp₀.continuousOn (T/2) (by positivity)
  let p : (Fin m → ℝ) → ℝ := fun z => β + ∑ i, a i * σ ((∑ j, W i j * z j) + b i)
  have psmall : p c ≤ T/2 := by
    have ha := (abs_lt.mp (happ c hc)).2
    change p c - p₀ c < T/2 at ha
    rw [pc] at ha
    linarith
  have plarge (x) (hx : x ∈ X) : 3*T/2 ≤ p (eval q x) := by
    have ha := (abs_lt.mp (happ (eval q x)
      (subset_convexHull ℝ _ ⟨x, hx, rfl⟩))).1
    change -(T/2) < p (eval q x) - p₀ (eval q x) at ha
    linarith [pgap x hx]
  -- Compose p with q, keeping its affine interface. Convexity and soundness
  -- put c in the prefix projection; exact suffix graph tuples extend it to
  -- a feasible ideal P₁ assignment. The helper checks this for continuous σ
  -- and uses compact envelopes to justify the finite relaxation extrema.
  obtain ⟨f, evaluation, relaxed⟩ :=
    Machinery.append_scalar_layers
      σ hσ d m q X hX ⟨V, hV⟩ hn n hnpos a W b β c hc
  change ∀ s x, eval (f s) x 0 = s * p (eval q x) at evaluation
  change ∀ s, (bounds (f s) X 1 (by omega) (f s).property.2.2).1 0 ≤ s * p c ∧
    s * p c ≤ (bounds (f s) X 1 (by omega) (f s).property.2.2).2 0 at relaxed
  -- The ε=T/2 approximation gives min f(X)≥3T/2 and ell(f)≤T/2.
  have exactlow : 3*T/2 ≤ sInf ((fun x => eval (f 1) x 0) '' X) := by
    apply le_csInf (hX.image _)
    rintro _ ⟨x, hx, rfl⟩
    simpa only [evaluation, one_mul] using plarge x hx
  have low := (relaxed 1).1
  simp only [one_mul] at low
  -- Negating the final affine coefficients negates every exact output
  -- and the same feasible continuation. Thus u(g)≥-T/2 and max g(X)≤-3T/2.
  have exacthigh : sSup ((fun x => eval (f (-1)) x 0) '' X) ≤ -(3*T/2) := by
    apply csSup_le (hX.image _)
    rintro _ ⟨x, hx, rfl⟩
    have he := evaluation (-1) x
    dsimp only
    linarith [plarge x hx]
  have high := (relaxed (-1)).2
  refine ⟨f 1, f (-1), ?_, ?_⟩
  · linarith
  · linarith
  -- formalizer:proof-end
)

end Theorem_Jp3
