module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Lemma_Jp6.Machinery

-- formalizer:machinery-begin
theorem dyadic_mem {d : ℕ} {S : Set (Fin d → ℝ)}
    (hm : ∀ x ∈ S, ∀ y ∈ S, (fun i => (x i + y i) / 2) ∈ S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    ∀ n m : ℕ, m ≤ 2 ^ n →
      (fun i => (1 - (m : ℝ) / 2 ^ n) * x i + ((m : ℝ) / 2 ^ n) * y i) ∈ S := by
  intro n
  induction n with
  | zero =>
    intro m h
    have : m = 0 ∨ m = 1 := by simp only [pow_zero] at h; omega
    rcases this with rfl | rfl
    · simpa using hx
    · simpa using hy
  | succ n ih =>
    intro m h
    have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    by_cases hm' : m ≤ 2 ^ n
    · have hh := hm x hx _ (ih m hm')
      convert hh using 1
      ext i
      simp only [pow_succ]
      field_simp
      <;> ring
    · have hle : m - 2 ^ n ≤ 2 ^ n := by rw [pow_succ] at h; omega
      have hh := hm _ (ih (m - 2 ^ n) hle) y hy
      convert hh using 1
      ext i
      rw [Nat.cast_sub (by omega : 2 ^ n ≤ m)]
      simp only [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      <;> ring

theorem missing_midpoint {d : ℕ} (S : Set (Fin d → ℝ))
    (hc : IsCompact S) (hn : ¬ Convex ℝ S) :
    ∃ x ∈ S, ∃ y ∈ S, (fun i => (x i + y i) / 2) ∉ S := by
  by_contra h
  push_neg at h
  apply hn
  intro x hx y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hseq := (tendsto_nat_floor_mul_div_atTop hb).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlim : Filter.Tendsto
      (fun n : ℕ => fun i : Fin d =>
        (1 - (⌊b * 2 ^ n⌋₊ : ℝ) / 2 ^ n) * x i +
          ((⌊b * 2 ^ n⌋₊ : ℝ) / 2 ^ n) * y i)
      Filter.atTop (nhds (a • x + b • y)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have he : a = 1 - b := by linarith
    simpa [he] using ((tendsto_const_nhds.sub hseq).mul_const (x i)).add
      (hseq.mul_const (y i))
  apply hc.isClosed.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  apply dyadic_mem h hx hy
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_of_le_one_left (by positivity) hb1

theorem linear_equiv_nonzero {d : ℕ} (u v : Fin d → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ W : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ), W u = v := by
  classical
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℝ hu
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℝ hv
  obtain ⟨s, b, i, hi, _⟩ := exists_basis_of_pairing_ne_zero hf
  obtain ⟨t, c, j, hj, _⟩ := exists_basis_of_pairing_ne_zero hg
  letI := FiniteDimensional.fintypeBasisIndex b
  letI := FiniteDimensional.fintypeBasisIndex c
  have hc : Fintype.card s = Fintype.card t :=
    (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis c)
  let e := Fintype.equivOfCardEq hc
  refine ⟨b.equiv c (e.trans (Equiv.swap (e i) j)), ?_⟩
  rw [hi, Module.Basis.equiv_apply]
  simpa using hj.symm

theorem alternating_injective {E : Type*} {N : ℕ}
    (F : Fin (N + 1) → E → E) (A T R : E → E)
    (h0 : F 0 = id)
    (hs : ∀ i : Fin N, F i.succ =
      if i.val = 0 then A else if i.val % 2 = 1 then T ∘ F i.castSucc else R ∘ F i.castSucc)
    (hA : Function.Injective A) (hT : Function.Injective T) (hR : Function.Injective R) :
    ∀ j, Function.Injective (F j) := by
  intro j
  induction j using Fin.induction with
  | zero => rw [h0]; exact Function.injective_id
  | succ i ih =>
    rw [hs]
    split
    · exact hA
    · split
      · exact hT.comp ih
      · exact hR.comp ih

theorem alternating_orbit {E : Type*} {N : ℕ}
    (F : Fin (N + 1) → E → E) (A T R : E → E)
    (hs : ∀ i : Fin N, F i.succ =
      if i.val = 0 then A else if i.val % 2 = 1 then T ∘ F i.castSucc else R ∘ F i.castSucc)
    (x v : E) (ha : A x = v) (hr : R (T v) = v) :
    ∀ j, 1 ≤ j.val → F j x = if j.val % 2 = 1 then v else T v := by
  intro j
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
    intro hj
    rw [hs]
    by_cases hi : i.val = 0
    · simp [hi, ha]
    · have hip : 1 ≤ i.castSucc.val := by simpa using (Nat.one_le_iff_ne_zero.mpr hi)
      have ho := ih hip
      by_cases hp : i.val % 2 = 1
      · have hp' : (i.val + 1) % 2 ≠ 1 := by omega
        simpa [hi, hp, hp', Function.comp_apply] using congrArg T ho
      · have hp' : (i.val + 1) % 2 = 1 := by omega
        simp only [Fin.val_castSucc, if_neg hp] at ho
        simpa [hi, hp, hp', Function.comp_apply] using (congrArg R ho).trans hr

-- formalizer:machinery-end

end Lemma_Jp6.Machinery
