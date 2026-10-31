module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_3p2
public import Formalization.Result.Theorem_3p3
public import Formalization.Result.Lemma_Jp1
public import Mathlib

public section

namespace Proposition_Jp2.Machinery

-- formalizer:machinery-begin

theorem hausdorff_formula {d : ℕ} (A B : Set (EuclideanSpace ℝ (Fin d)))
    (ha : A.Nonempty) (ca : IsCompact A) (hb : B.Nonempty) (cb : IsCompact B) :
    Definition.HausdorffDistance d A B ha ca hb cb =
      max (sSup ((fun x => Metric.infDist x B) '' A))
          (sSup ((fun x => Metric.infDist x A) '' B)) := by
  unfold Definition.HausdorffDistance
  congr 1
  · simp_rw [Lemma_Jp1.Machinery.inf_norm_eq d B hb]
  · have rev (y : EuclideanSpace ℝ (Fin d)) :
        (fun x => ‖x - y‖) = (fun x => ‖y - x‖) := funext (fun x => norm_sub_rev x y)
    simp_rw [rev, Lemma_Jp1.Machinery.inf_norm_eq d A ha]

theorem point_le_hausdorff {d : ℕ} (A B : Set (EuclideanSpace ℝ (Fin d)))
    (ha : A.Nonempty) (ca : IsCompact A) (hb : B.Nonempty) (cb : IsCompact B)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ A) :
    Metric.infDist x B ≤ Definition.HausdorffDistance d A B ha ca hb cb := by
  rw [hausdorff_formula]
  exact (le_csSup (ca.bddAbove_image (Metric.continuous_infDist_pt B).continuousOn)
    (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)

theorem hausdorff_symm {d : ℕ} (A B : Set (EuclideanSpace ℝ (Fin d)))
    (ha : A.Nonempty) (ca : IsCompact A) (hb : B.Nonempty) (cb : IsCompact B) :
    Definition.HausdorffDistance d A B ha ca hb cb = Definition.HausdorffDistance d B A hb cb ha ca := by
  rw [hausdorff_formula, hausdorff_formula, max_comm]

theorem hausdorff_le {d : ℕ} (A B : Set (EuclideanSpace ℝ (Fin d)))
    (ha : A.Nonempty) (ca : IsCompact A) (hb : B.Nonempty) (cb : IsCompact B)
    (r : ℝ) (hAB : ∀ x ∈ A, Metric.infDist x B ≤ r)
    (hBA : ∀ x ∈ B, Metric.infDist x A ≤ r) :
    Definition.HausdorffDistance d A B ha ca hb cb ≤ r := by
  rw [hausdorff_formula]
  apply max_le
  · exact csSup_le (ha.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hAB x hx)
  · exact csSup_le (hb.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hBA x hx)

theorem hausdorff_triangle {d : ℕ} (A B C : Set (EuclideanSpace ℝ (Fin d)))
    (ha : A.Nonempty) (ca : IsCompact A) (hb : B.Nonempty) (cb : IsCompact B)
    (hc : C.Nonempty) (cc : IsCompact C) :
    Definition.HausdorffDistance d A C ha ca hc cc ≤
      Definition.HausdorffDistance d A B ha ca hb cb + Definition.HausdorffDistance d B C hb cb hc cc := by
  have directed (S T U : Set (EuclideanSpace ℝ (Fin d)))
      (hs : S.Nonempty) (cs : IsCompact S) (ht : T.Nonempty) (ct : IsCompact T)
      (hu : U.Nonempty) (cu : IsCompact U) (x) (hx : x ∈ S) :
      Metric.infDist x U ≤ Definition.HausdorffDistance d S T hs cs ht ct +
        Definition.HausdorffDistance d T U ht ct hu cu := by
    obtain ⟨y, hy, hxy⟩ := ct.exists_infDist_eq_dist ht x
    obtain ⟨z, hz, hyz⟩ := cu.exists_infDist_eq_dist hu y
    calc
      Metric.infDist x U ≤ dist x z := Metric.infDist_le_dist_of_mem hz
      _ ≤ dist x y + dist y z := dist_triangle _ _ _
      _ ≤ _ := by
        rw [← hxy, ← hyz]
        exact add_le_add (point_le_hausdorff S T hs cs ht ct hx)
          (point_le_hausdorff T U ht ct hu cu hy)
  apply hausdorff_le
  · exact directed A B C ha ca hb cb hc cc
  · intro x hx
    have h := directed C B A hc cc hb cb ha ca x hx
    rw [hausdorff_symm C B, hausdorff_symm B A] at h
    linarith

theorem hausdorff_self_le {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d)))
    (ha : A.Nonempty) (ca : IsCompact A) :
    Definition.HausdorffDistance d A A ha ca ha ca ≤ 0 := by
  apply hausdorff_le <;> intro x hx <;> simp [Metric.infDist_zero_of_mem hx]


theorem approximate_pair (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ t, σ t = p.eval t)
    {d : ℕ} (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (q : (Fin d → ℝ) → Fin 2 → ℝ) (hq : Continuous q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (A : Fin 2 → Fin n → ℝ)
      (W : Fin n → Fin d → ℝ) (b : Fin n → ℝ) (c : Fin 2 → ℝ),
      ∀ x ∈ K, ∀ j, |c j + (∑ i, A j i * σ ((∑ k, W i k * x k) + b i)) - q x j| < ε := by
  classical
  obtain ⟨n₀, a₀, W₀, b₀, c₀, h₀⟩ := Axioms.ExternalUniversalApproximation
    σ hσ hnp d K hK (fun x => q x 0) ((continuous_apply 0).comp hq).continuousOn ε hε
  obtain ⟨n₁, a₁, W₁, b₁, c₁, h₁⟩ := Axioms.ExternalUniversalApproximation
    σ hσ hnp d K hK (fun x => q x 1) ((continuous_apply 1).comp hq).continuousOn ε hε
  let I := Option (Fin n₀ ⊕ Fin n₁)
  let e := (Fintype.equivFin I).symm
  let A : Fin 2 → I → ℝ := fun j i => match i with
    | none => 0
    | some (Sum.inl k) => if j = 0 then a₀ k else 0
    | some (Sum.inr k) => if j = 1 then a₁ k else 0
  let W : I → Fin d → ℝ := fun i => match i with
    | none => fun _ => 0
    | some (Sum.inl k) => W₀ k
    | some (Sum.inr k) => W₁ k
  let b : I → ℝ := fun i => match i with
    | none => 0
    | some (Sum.inl k) => b₀ k
    | some (Sum.inr k) => b₁ k
  refine ⟨Fintype.card I, Fintype.card_pos, fun j i => A j (e i),
    fun i => W (e i), fun i => b (e i), ![c₀, c₁], ?_⟩
  intro x hx j
  rw [e.sum_comp (fun i => A j i * σ ((∑ k, W i k * x k) + b i))]
  fin_cases j
  · simpa [I, A, W, b, Fintype.sum_option, Fintype.sum_sum_type] using h₀ x hx
  · simpa [I, A, W, b, Fintype.sum_option, Fintype.sum_sum_type] using h₁ x hx


theorem pair_norm_bound (z : EuclideanSpace ℝ (Fin 2)) (ε : ℝ)
    (he : 0 < ε) (h : ∀ j, |z j| < ε / 2) : ‖z‖ ≤ ε := by
  have hs := EuclideanSpace.norm_sq_eq z
  simp only [Fin.sum_univ_two, Real.norm_eq_abs] at hs
  have h0 := mul_self_le_mul_self (abs_nonneg (z 0)) (h 0).le
  have h1 := mul_self_le_mul_self (abs_nonneg (z 1)) (h 1).le
  nlinarith only [hs, h0, h1, he, norm_nonneg z]

theorem positive_gap (D a b c e r : ℝ) (hD : 0 < D)
    (h₁ : D ≤ a + b) (h₂ : b ≤ c + r) (ha : a ≤ e)
    (he : e ≤ D / 4) (hr : r = e) : 0 < c := by
  linarith

-- formalizer:machinery-end

end Proposition_Jp2.Machinery
