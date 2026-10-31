module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_3p2
public import Mathlib

public section

namespace Theorem_Ip1.Machinery

-- formalizer:machinery-begin
theorem normalized_coordinate {d : ℕ} {X : Set (Fin d → ℝ)}
    (hX : X.Nonempty) (kX : IsCompact X) (hn : ¬ X.Subsingleton) :
    ∃ (i : Fin d) (a b : ℝ) (lo hi : Fin d → ℝ),
      lo ∈ X ∧ hi ∈ X ∧ a * lo i + b = -1 ∧ a * hi i + b = 1 ∧
      ∀ x ∈ X, a * x i + b ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hn
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    ext i
    simpa using not_exists.mp h i
  obtain ⟨lo, hlo, hmin⟩ := kX.exists_isMinOn hX (continuous_apply i).continuousOn
  obtain ⟨up, hup, hmax⟩ := kX.exists_isMaxOn hX (continuous_apply i).continuousOn
  have hlt : lo i < up i := by
    have h₁ := hmin hx
    have h₂ := hmin hy
    have h₃ := hmax hx
    have h₄ := hmax hy
    dsimp at h₁ h₂ h₃ h₄
    rcases lt_or_gt_of_ne hi with h | h <;> linarith
  have hd : 0 < up i - lo i := sub_pos.mpr hlt
  refine ⟨i, 2 / (up i - lo i), -1 - (2 / (up i - lo i)) * lo i,
    lo, up, hlo, hup, by ring, ?_, ?_⟩
  · field_simp
    <;> nlinarith
  · intro z hz
    have h₁ := hmin hz
    have h₂ := hmax hz
    have hpos : 0 ≤ 2 / (up i - lo i) := le_of_lt (div_pos (by norm_num) hd)
    have he : 2 / (up i - lo i) * (up i - lo i) = 2 := div_mul_cancel₀ _ (ne_of_gt hd)
    constructor <;> dsimp at * <;> nlinarith

theorem relu_not_polynomial :
    ¬ ∃ p : Polynomial ℝ, ∀ t, max t 0 = p.eval t := by
  rintro ⟨p, hp⟩
  have hz : p = 0 := p.eq_zero_of_infinite_isRoot
    ((Set.Iio_infinite (0 : ℝ)).mono (by
      intro t ht
      change p.eval t = 0
      rw [← hp]
      exact max_eq_right (le_of_lt ht)))
  have h := hp 1
  simp [hz] at h

theorem bent_curve_zero {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    max t 0 * (max (1-t) 0 + max t 0 - 1) = 0 := by
  rw [max_eq_left (by linarith [ht.2] : 0 ≤ 1-t)]
  rcases le_total t 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h]; ring

theorem approximation_width {T Q low high infimum supremum : ℝ}
    (hT : 0 < T) (hQ : 2 ≤ Q) (hTQ : T ≤ Q)
    (hl : -(1/2 : ℝ) ≤ infimum) (hu : supremum ≤ 1/2)
    (hlo : low ≤ 1/2) (hhi : 2*Q-1/2 ≤ high) :
    T * (supremum - infimum) ≤ high - low := by
  have hw : supremum - infimum ≤ 1 := by linarith
  have := mul_le_mul_of_nonneg_left hw (le_of_lt hT)
  nlinarith

theorem bent_curve_mem {S : Set (Fin 2 → ℝ)} (hS : Convex ℝ S)
    (hl : ![0, 2] ∈ S) (hm : ![0, 1] ∈ S) (hr : ![1, 0] ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ![max t 0, max (1-t) 0] ∈ S := by
  rw [max_eq_left (by linarith [ht.2] : 0 ≤ 1-t)]
  rcases le_total t 0 with hn | hp
  · rw [max_eq_right hn]
    convert hS hl hm (by linarith : 0 ≤ -t) (by linarith [ht.1] : 0 ≤ 1+t)
      (by ring : -t+(1+t)=1) using 1
    ext j
    fin_cases j <;> simp <;> ring
  · rw [max_eq_left hp]
    convert hS hm hr (by linarith [ht.2] : 0 ≤ 1-t) hp
      (by ring : 1-t+t=1) using 1
    ext j
    fin_cases j <;> simp <;> ring

theorem suffix_image (σ : ℝ → ℝ) (d n : ℕ) (c : Fin n → ℝ)
    (W : Fin n → Fin 2 → ℝ) (β : Fin n → ℝ) (bias : ℝ) (K : Set (Fin 2 → ℝ)) :
    let w : Fin 6 → ℕ := ![d, 2, 2, n, n, 1]
    let p : (Fin 2 → ℝ) → ℝ := fun u => bias + ∑ j, c j * σ ((∑ k, W j k*u k)+β j)
    ∀ step : (j : Fin 5) → (Fin (w j.castSucc) → ℝ) → (Fin (w j.succ) → ℝ),
      (∀ x, step (2 : Fin 5) x = fun j => (∑ k, W j k*x k)+β j) →
      (∀ x, step (3 : Fin 5) x = fun j => σ (x j)) →
      (∀ x, step (4 : Fin 5) x = fun _ => (∑ k, c k*x k)+bias) →
      {y : Fin 1 → ℝ | ∃ v : (j : Fin 6) → Fin (w j) → ℝ,
        v 2 ∈ K ∧ (∀ j, y j = v 5 j) ∧
        ∀ k : Fin 5, 2 ≤ k.val → v k.succ = step k (v k.castSucc)} =
      (fun v => fun _ : Fin 1 => p v) '' K := by
  intro w p step e3 e4 e5
  ext y
  constructor
  · rintro ⟨v, hv, hy, he⟩
    have hv3 := (he (2 : Fin 5) (by norm_num)).trans (e3 _)
    have hv4 := (he (3 : Fin 5) (by norm_num)).trans (e4 _)
    have hv5 := (he (4 : Fin 5) (by norm_num)).trans (e5 _)
    change v 3 = (fun j => (∑ k, W j k * v 2 k) + β j) at hv3
    change v 4 = (fun j => σ (v 3 j)) at hv4
    change v 5 = (fun _ => (∑ k, c k * v 4 k) + bias) at hv5
    refine ⟨v 2, hv, ?_⟩
    ext j
    rw [hy j]
    change p (v 2) = v 5 j
    rw [hv5, hv4, hv3]
    exact add_comm _ _
  · rintro ⟨u, hu, rfl⟩
    let v : (j : Fin 6) → Fin (w j) → ℝ := fun j => by
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
        (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))))) j
      · exact fun _ => 0
      · exact fun _ => 0
      · exact u
      · exact fun j => (∑ k, W j k * u k) + β j
      · exact fun j => σ ((∑ k, W j k * u k) + β j)
      · exact fun _ => p u
    refine ⟨v, hu, (fun _ => rfl), ?_⟩
    intro k hk
    fin_cases k <;> norm_num at hk
    · exact (e3 _).symm
    · exact (e4 _).symm
    · change (fun _ : Fin 1 => p u) = step (4 : Fin 5)
        (fun j => σ ((∑ k, W j k * u k) + β j))
      rw [e5]
      ext j
      exact add_comm _ _

-- formalizer:machinery-end

end Theorem_Ip1.Machinery
