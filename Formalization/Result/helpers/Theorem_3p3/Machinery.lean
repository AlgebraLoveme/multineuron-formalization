module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_3p2
public import Mathlib

public section

namespace Theorem_3p3.Machinery

-- formalizer:machinery-begin
theorem coordinate_extrema {d : ℕ} {X : Set (Fin d → ℝ)}
    (hc : IsCompact X) (hn : X.Nonempty) (hnt : ¬X.Subsingleton) :
    ∃ (k : Fin d) (u v : Fin d → ℝ), u ∈ X ∧ v ∈ X ∧ u k < v k ∧
      ∀ x ∈ X, u k ≤ x k ∧ x k ≤ v k := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hnt
  have hd : ∃ k, x k ≠ y k := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨k, hk⟩ := hd
  obtain ⟨u, hu, hmin⟩ := hc.exists_isMinOn hn (continuous_apply k).continuousOn
  obtain ⟨v, hv, hmax⟩ := hc.exists_isMaxOn hn (continuous_apply k).continuousOn
  refine ⟨k, u, v, hu, hv, ?_, fun z hz => ⟨hmin hz, hmax hz⟩⟩
  have hux := hmin hx
  have huy := hmin hy
  have hxv := hmax hx
  have hyv := hmax hy
  dsimp at hux huy hxv hyv
  rcases lt_or_gt_of_ne hk with h | h <;> linarith

theorem normalized_endpoints {a b : ℝ} (hab : a < b) :
    2 * (a - a) / (b - a) - 1 = -1 ∧
    2 * (b - a) / (b - a) - 1 = 1 := by
  have h : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  constructor
  · ring
  · field_simp; ring

theorem normalized_bounds {a b t : ℝ} (hab : a < b)
    (ha : a ≤ t) (hb : t ≤ b) :
    -1 ≤ 2 * (t - a) / (b - a) - 1 ∧
    2 * (t - a) / (b - a) - 1 ≤ 1 := by
  have h : 0 < b - a := sub_pos.mpr hab
  constructor
  · have := div_nonneg (by linarith : 0 ≤ 2 * (t - a)) h.le
    linarith
  · have : 2 * (t - a) / (b - a) ≤ 2 := (div_le_iff₀ h).mpr (by linarith)
    linarith

theorem two_segment_distance (t : ℝ) :
    (1 / 2 : ℝ) ≤ |max (t + 1) 0 - 1| + |max t 0 - 1 / 2| := by
  by_cases ht : t ≤ 0
  · rw [max_eq_right ht]
    norm_num
  · have ht : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [max_eq_left ht, max_eq_left (by linarith : 0 ≤ t + 1)]
    have h := neg_le_abs (t - 1 / 2)
    rw [show t + 1 - 1 = t by ring, abs_of_nonneg ht]
    linarith

theorem scaled_distance (T t : ℝ) (hT : 0 < T) :
    T ≤ 2 * T * (|max (t + 1) 0 - 1| + |max t 0 - 1 / 2|) := by
  have := two_segment_distance t
  nlinarith

theorem relu_pair (a b : ℝ) : max (a - b) 0 + max (b - a) 0 = |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h),
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
      abs_of_nonneg (sub_nonneg.mpr h)]
    ring

-- formalizer:machinery-end

end Theorem_3p3.Machinery
