module
public import Formalization.Result.helpers.Proposition_Jp2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Theorem_3p3
public import Formalization.Result.Lemma_Jp1

open Definition

public section

namespace Proposition_Jp2

theorem result_J_2 (σ : ℝ → ℝ) (hσ : Continuous σ)
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
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)), X.Nonempty → poly X → ¬X.Subsingleton →
    ∃ (m : ℕ) (f : Net d m),
      (eval f '' X ⊂ convexHull ℝ (eval f '' X)) ∧
      -- Retain the affine output of the coordinatewise approximation for J.7.
      ∃ i : Fin f.val.1, i.val + 1 = f.val.1 ∧
        ∃ A b, f.val.2.2.val i = Sum.inl (A, b) := (by
  -- formalizer:proof-begin
  classical
  intro Net run eval poly d X hX hp hn
  obtain ⟨V, hV⟩ := hp
  have cX : IsCompact X := by
    rw [hV]
    exact V.finite_toSet.isCompact_convexHull ℝ
  -- Theorem 3.3's prefix: normalize a varying coordinate at its attained extrema.
  obtain ⟨k, u, v, hu, hv, huv, hext⟩ := Theorem_3p3.Machinery.coordinate_extrema cX hX hn
  let t : (Fin d → ℝ) → ℝ := fun x => 2 * (x k - u k) / (v k - u k) - 1
  have hend := Theorem_3p3.Machinery.normalized_endpoints huv
  have tu : t u = -1 := hend.1
  have tv : t v = 1 := hend.2
  let q : (Fin d → ℝ) → Fin 2 → ℝ := fun x => ![max (t x + 1) 0, max (t x) 0]
  have cq : Continuous q := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun x => max (t x + 1) 0)
      unfold t
      fun_prop
    · change Continuous (fun x => max (t x) 0)
      unfold t
      fun_prop
  let Q : (Fin d → ℝ) → EuclideanSpace ℝ (Fin 2) := fun x => WithLp.toLp 2 (q x)
  have cQ : Continuous Q := (PiLp.continuous_toLp 2 _).comp cq
  let H := Q '' X
  have hH : H.Nonempty := hX.image Q
  have cH : IsCompact H := cX.image cQ
  have cCH := Lemma_Jp1.Machinery.compact_convexHull 2 H cH
  let c : EuclideanSpace ℝ (Fin 2) := !₂[1, 1/2]
  -- The endpoint midpoint c=(1,1/2) lies in the hull but off both segments.
  have hcHull : c ∈ convexHull ℝ H := by
    have hh := (convex_convexHull ℝ H)
      (subset_convexHull ℝ H (Set.mem_image_of_mem Q hu))
      (subset_convexHull ℝ H (Set.mem_image_of_mem Q hv))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) + 1/2 = 1)
    convert hh using 1
    ext j
    fin_cases j <;> simp [c, Q, q, tu, tv] <;> norm_num
  have hcNot : c ∉ H := by
    rintro ⟨x, hx, he⟩
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) he
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) he
    change max (t x + 1) 0 = 1 at h0
    change max (t x) 0 = 1/2 at h1
    have hd := Theorem_3p3.Machinery.two_segment_distance (t x)
    rw [h0, h1] at hd
    norm_num at hd
  let Δ := HausdorffDistance 2 (convexHull ℝ H) H hH.convexHull cCH hH cH
  have hΔ : 0 < Δ :=
    (cH.isClosed.notMem_iff_infDist_pos hH).mp hcNot |>.trans_le
      (Machinery.point_le_hausdorff _ _ _ _ _ _ hcHull)
  let ε := Δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  -- J.2: scalar density on compact X, with coordinate error ε/2,
  -- gives Euclidean error at most ε after combining the hidden units.
  obtain ⟨n, hnpos, A, W, b, bias, happ⟩ := Machinery.approximate_pair σ hσ hnp X cX q cq
    (ε / 2) (by positivity)
  have hd : 0 < d := Nat.zero_lt_of_lt k.isLt
  let w : Fin 4 → ℕ := ![d, n, n, 2]
  let N : NetworkSemantics σ 3 w := by
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
      · exact Sum.inl (W, b)
      · exact Sum.inr ⟨rfl⟩
      · exact Sum.inl (A, bias)
    · intro j
      fin_cases j <;> simp [w, hd, hnpos]
  let f : Net d 2 := ⟨⟨3, w, N⟩, rfl, rfl, by norm_num⟩
  have rstep (x : Fin d → ℝ) (i : Fin 3) :
      run f i.succ x =
        match N.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * run f i.castSucc x k) + b j
        | Sum.inr h => fun j => σ (run f i.castSucc x (Fin.cast h.down.symm j)) := by
    simp only [run, f, Fin.induction_succ]
    cases he : N.val i with
    | inl ab => rcases ab with ⟨A, b⟩; rfl
    | inr h => rfl
  have rone (x : Fin d → ℝ) : run f 1 x = fun i => (∑ k, W i k * x k) + b i := by
    exact rstep x 0
  have rtwo (x : Fin d → ℝ) : run f 2 x = fun i => σ ((∑ k, W i k * x k) + b i) := by
    have h := rstep x 1
    change run f 2 x = (fun i => σ (run f 1 x i)) at h
    rw [h, rone]
    rfl
  have ef (x : Fin d → ℝ) : eval f x =
      fun j => bias j + ∑ i, A j i * σ ((∑ k, W i k * x k) + b i) := by
    have h := rstep x 2
    change run f 3 x = (fun j => (∑ i, A j i * run f 2 x i) + bias j) at h
    change run f 3 x = _
    rw [h, rtwo]
    simp [add_comm]
  have cf : Continuous (eval f) := by
    have he : eval f = fun x j => bias j + ∑ i, A j i * σ ((∑ k, W i k * x k) + b i) := funext ef
    rw [he]
    fun_prop
  let F : (Fin d → ℝ) → EuclideanSpace ℝ (Fin 2) := fun x => WithLp.toLp 2 (eval f x)
  have cF : Continuous F := (PiLp.continuous_toLp 2 _).comp cf
  let H' := F '' X
  have hH' : H'.Nonempty := hX.image F
  have cH' : IsCompact H' := cX.image cF
  have error (x) (hx : x ∈ X) : dist (Q x) (F x) ≤ ε := by
    have ha (j : Fin 2) : |(Q x - F x) j| < ε / 2 := by
      change |q x j - eval f x j| < ε / 2
      rw [abs_sub_comm, ef x]
      exact happ x hx j
    rw [dist_eq_norm]
    exact Machinery.pair_norm_bound
      (Q x - F x) ε hε ha
  -- Matching points at the same input bounds both directed Hausdorff distances.
  have hclose : HausdorffDistance 2 H H' hH cH hH' cH' ≤ ε := by
    apply Machinery.hausdorff_le
    · rintro _ ⟨x, hx, rfl⟩
      exact (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem F hx)).trans (error x hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem Q hx)).trans
        (by rw [dist_comm]; exact error x hx)
  -- J.1 applies to independently nonempty compact images and their compact hulls.
  obtain ⟨cCH₀, cCH', hHull⟩ := Lemma_Jp1.result_J_1 2 H H' hH cH hH' cH'
  -- Two nearest-point triangle bounds give Δ ≤ 2ε + D(conv(H'),H').
  have htri₁ := Machinery.hausdorff_triangle (convexHull ℝ H) (convexHull ℝ H') H
    hH.convexHull cCH hH'.convexHull cCH' hH cH
  have htri₂ := Machinery.hausdorff_triangle (convexHull ℝ H') H' H
    hH'.convexHull cCH' hH' cH' hH cH
  have hrev := Machinery.hausdorff_symm H' H hH' cH' hH cH
  have hgap : 0 < HausdorffDistance 2 (convexHull ℝ H') H' hH'.convexHull cCH' hH' cH' := by
    exact Machinery.positive_gap
      Δ _ _ _ _ _ hΔ htri₁ htri₂ hHull hclose hrev
  -- ε=Δ/4 leaves a positive gap; equality of the image and its hull is impossible.
  -- The coordinatewise approximant ends with the affine output (A, bias).
  have hlast : ∃ i : Fin f.val.1, i.val + 1 = f.val.1 ∧
      ∃ A b, f.val.2.2.val i = Sum.inl (A, b) := by
    exact ⟨2, rfl, A, bias, rfl⟩
  refine ⟨2, f, Set.ssubset_iff_subset_ne.mpr ⟨subset_convexHull ℝ _, ?_⟩, hlast⟩
  intro heq
  have heHull : convexHull ℝ H' = H' := by
    let e := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm
    have hh := e.toLinearMap.image_convexHull (eval f '' X)
    change e '' convexHull ℝ (eval f '' X) = convexHull ℝ (e '' (eval f '' X)) at hh
    rw [← heq] at hh
    have hi : e '' (eval f '' X) = H' := by
      rw [Set.image_image]
      rfl
    rw [hi] at hh
    exact hh.symm
  have hz := Machinery.hausdorff_self_le H' hH' cH'
  have hnonpos : HausdorffDistance 2 (convexHull ℝ H') H' hH'.convexHull cCH' hH' cH' ≤ 0 := by
    simpa only [heHull] using hz
  exact (not_lt_of_ge hnonpos) hgap
  -- formalizer:proof-end
)

end Proposition_Jp2
