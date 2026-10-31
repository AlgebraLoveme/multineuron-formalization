module
public import Formalization.Result.helpers.Lemma_Jp6.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Lemma_Jp6

theorem result_J_6 (σ : ℝ → ℝ) (hσ : AdmissibleActivation σ) :
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
  ∀ (d M : ℕ), 0 < d → 0 < M →
    ∀ (S : Set (Fin d → ℝ)), IsCompact S → ¬Convex ℝ S →
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ B : Net d d,
      M ≤ B.val.1 ∧
      -- The source bridge is A followed by k copies of activation then R.
      (∃ k : ℕ, 0 < k ∧ B.val.1 = 2 * k + 1) ∧
      (∀ j : Fin (B.val.1 + 1), B.val.2.1 j = d) ∧
      (∀ i : Fin B.val.1,
        (Even i.val → ∃ A b, B.val.2.2.val i = Sum.inl (A, b)) ∧
        (Odd i.val → ∃ h, B.val.2.2.val i = Sum.inr h)) ∧
      let prefixEval : (j : Fin (B.val.1 + 1)) → (Fin d → ℝ) →
          (Fin (B.val.2.1 j) → ℝ) := fun j x =>
        run B j (fun k => x (Fin.cast B.property.1 k))
      ∀ j : Fin (B.val.1 + 1), 1 ≤ j.val →
        prefixEval j (fun k => (x₁ k + x₂ k) / 2) =
          (fun k => (prefixEval j x₁ k + prefixEval j x₂ k) / 2) ∧
        prefixEval j (fun k => (x₁ k + x₂ k) / 2) ∉ prefixEval j '' S := (by
  -- formalizer:proof-begin
  classical
  let Net := fun d m =>
    { p : (L : ℕ) × (w : Fin (L + 1) → ℕ) × NetworkSemantics σ L w //
      p.2.1 0 = d ∧ p.2.1 (Fin.last p.1) = m ∧ 0 < p.1 }
  dsimp only
  intro d M hd hM S hS hn
  -- Closedness and dyadic interpolation give a midpoint missing from S (J.6).
  obtain ⟨x₁, hx₁, x₂, hx₂, hz⟩ :=
    Machinery.missing_midpoint S hS hn
  let z : Fin d → ℝ := fun i => (x₁ i + x₂ i) / 2
  have hne : x₂ - x₁ ≠ 0 := by
    intro he
    have he' : x₂ = x₁ := sub_eq_zero.mp he
    apply hz
    simpa [he'] using hx₁
  obtain ⟨a, b, hab, hm⟩ := hσ.2.2.2
  let m := (a + b) / 2
  have hv : (fun _ : Fin d => b - a) ≠ 0 := by
    intro he
    have := congrFun he ⟨0, hd⟩
    simp only [Pi.zero_apply] at this
    linarith
  -- Extend the two nonzero vectors to bases to obtain W(x₂-x₁)=(b-a)1.
  obtain ⟨W, hW⟩ :=
    Machinery.linear_equiv_nonzero
      (x₂ - x₁) (fun _ => b - a) hne hv
  let A : (Fin d → ℝ) → (Fin d → ℝ) := fun x i => W (x - x₁) i + a
  have hAi : Function.Injective A := by
    intro x y he
    have he' : W (x - x₁) = W (y - x₁) := by
      ext i
      have := congrFun he i
      dsimp [A] at this
      linarith
    exact sub_left_injective (W.injective he')
  have hA₁ : A x₁ = fun _ => a := by ext i; simp [A]
  have hA₂ : A x₂ = fun _ => b := by
    ext i
    change W (x₂ - x₁) i + a = b
    rw [hW]
    ring
  have hAz : A z = fun _ => m := by
    have he : z - x₁ = (1 / 2 : ℝ) • (x₂ - x₁) := by ext i; simp [z]; ring
    ext i
    change W (z - x₁) i + a = m
    rw [he, map_smul, hW]
    simp only [Pi.smul_apply, smul_eq_mul, m]
    ring
  -- The reset R(v)=m1+γ(v-σ(m)1) is injective and restores the selected triple.
  have hs : σ b - σ a ≠ 0 := sub_ne_zero.mpr (fun he => (ne_of_gt hab) (hσ.2.2.1 he))
  let γ := (b - a) / (σ b - σ a)
  have hγ : γ ≠ 0 := div_ne_zero (sub_ne_zero.mpr (ne_of_gt hab)) hs
  let R : (Fin d → ℝ) → (Fin d → ℝ) := fun v i => m + γ * (v i - σ m)
  have hRi : Function.Injective R := by
    intro x y he
    ext i
    have hh := congrFun he i
    dsimp [R] at hh
    exact sub_left_injective (mul_left_cancel₀ hγ (add_left_cancel hh))
  have hRa : R (fun _ => σ a) = fun _ => a := by
    ext i
    dsimp [R, γ]
    rw [show σ m = (σ a + σ b) / 2 from hm]
    dsimp [m]
    field_simp
    <;> ring
  have hRb : R (fun _ => σ b) = fun _ => b := by
    ext i
    dsimp [R, γ]
    rw [show σ m = (σ a + σ b) / 2 from hm]
    dsimp [m]
    field_simp
    <;> ring
  have hRm : R (fun _ => σ m) = fun _ => m := by ext i; simp [R]
  -- Take k=M, so the alternating bridge has N=2M+1 individual layers.
  let N := 2 * M + 1
  let C := LinearMap.toMatrix' W.toLinearMap
  let D : Matrix (Fin d) (Fin d) ℝ := fun i k => if i = k then γ else 0
  let layers : Fin N → (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)) ⊕ PLift (d = d) :=
    fun i => if i.val = 0 then Sum.inl (C, fun j => a - W x₁ j)
      else if i.val % 2 = 1 then Sum.inr ⟨rfl⟩
      else Sum.inl (D, fun _ => m - γ * σ m)
  let B : Net d d := ⟨⟨N, fun _ => d, ⟨layers, fun _ => hd⟩⟩, rfl, rfl, by dsimp [N]; omega⟩
  let F : Fin (N + 1) → (Fin d → ℝ) → (Fin d → ℝ) :=
    Fin.induction (fun x => x) (fun i prev x =>
      match layers i with
      | Sum.inl (C, c) => fun j => (∑ k, C j k * prev x k) + c j
      | Sum.inr h => fun j => σ (prev x (Fin.cast h.down.symm j)))
  let T : (Fin d → ℝ) → (Fin d → ℝ) := fun x j => σ (x j)
  have h0 : F 0 = id := by simp only [F, Fin.induction_zero]; rfl
  have hsF : ∀ i : Fin N, F i.succ =
      if i.val = 0 then A else if i.val % 2 = 1 then T ∘ F i.castSucc else R ∘ F i.castSucc := by
    intro i
    have he : F i.succ = fun x =>
      match layers i with
      | Sum.inl (C, c) => fun j => (∑ k, C j k * F i.castSucc x k) + c j
      | Sum.inr h => fun j => σ (F i.castSucc x (Fin.cast h.down.symm j)) := by
        simp only [F, Fin.induction_succ]
    rw [he]
    by_cases hi : i.val = 0
    · have hi0 : i.castSucc = 0 := Fin.ext hi
      simp only [layers, hi, if_pos, hi0, h0, id_eq]
      ext x j
      have hc := congrFun (LinearMap.toMatrix'_mulVec W.toLinearMap x) j
      change (∑ k, C j k * x k) = W x j at hc
      rw [hc]
      simp [A, map_sub]
      ring
    · by_cases hp : i.val % 2 = 1
      · simp only [layers, if_neg hi, if_pos hp, T, Function.comp_def, Fin.cast_eq_self]
      · simp only [layers, hi, if_false, hp, Function.comp_apply]
        ext x j
        simp [D, R]
        ring
  -- Prefix induction alternates the triples (a,b,m) and (σ(a),σ(b),σ(m)).
  have horbit := Machinery.alternating_orbit
    F A T R hsF
  have hfa := horbit x₁ (fun _ => a) hA₁ hRa
  have hfb := horbit x₂ (fun _ => b) hA₂ hRb
  have hfm := horbit z (fun _ => m) hAz hRm
  -- Every layer, and consequently every prefix, is injective.
  have hTi : Function.Injective T := by
    intro x y he
    ext i
    exact hσ.2.2.1 (congrFun he i)
  have hFi := Machinery.alternating_injective
    F A T R h0 hsF hAi hTi hRi
  have hfinal : ∀ j : Fin (N + 1), 1 ≤ j.val →
      F j z = (fun k => (F j x₁ k + F j x₂ k) / 2) ∧ F j z ∉ F j '' S := by
    intro j hj
    constructor
    · rw [hfa j hj, hfb j hj, hfm j hj]
      split_ifs <;> funext k
      · rfl
      · exact hm
    · -- An image witness would force the missing midpoint z back into S.
      rintro ⟨x, hx, he⟩
      have hzx : z ∈ S := (hFi j he) ▸ hx
      exact hz hzx
  refine ⟨x₁, hx₁, x₂, hx₂, B, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [B, N]; omega
  -- The constructed bridge has constant width d and exactly the source layout:
  -- affine layers at even zero-based indices, activations at odd indices.
  · exact ⟨M, hM, rfl⟩
  · intro j; rfl
  · intro i
    constructor
    · intro he
      have hp : i.val % 2 ≠ 1 := by
        have hh := Nat.mod_eq_zero_of_dvd he.two_dvd
        omega
      by_cases hi : i.val = 0
      · exact ⟨C, (fun j => a - W x₁ j), by simp only [B, layers, if_pos hi]⟩
      · exact ⟨D, (fun _ => m - γ * σ m), by simp only [B, layers, if_neg hi, if_neg hp]⟩
    · intro ho
      have hp := Nat.odd_iff.mp ho
      have hi : i.val ≠ 0 := by omega
      exact ⟨⟨rfl⟩, by simp only [B, layers, if_neg hi, if_pos hp]⟩
  · simp only [B, F, z, Fin.cast_eq_self] at hfinal ⊢
    convert hfinal using 1 <;> congr! 12 <;>
      unfold result_J_6.match_1 result_J_6.match_1_2 <;> rfl
  -- formalizer:proof-end
)

end Lemma_Jp6
