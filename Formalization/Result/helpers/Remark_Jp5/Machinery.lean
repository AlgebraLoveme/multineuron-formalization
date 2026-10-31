module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Remark_Jp5.Machinery

-- formalizer:machinery-begin

theorem bounded_strictMono_nonpolynomial {f : ℝ → ℝ} (hf : StrictMono f)
    (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    ¬ ∃ p : Polynomial ℝ, ∀ x, f x = p.eval x := by
  rintro ⟨p, hp⟩
  have hd : p.degree ≤ 0 := p.isBoundedUnder_abs_atTop_iff.mp
    ⟨M, Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun x => by rw [← hp x]; exact hb x))⟩
  have he : f 0 = f 1 := by rw [hp 0, hp 1, p.eq_C_of_degree_le_zero hd]; simp
  exact (ne_of_lt (hf (by norm_num : (0 : ℝ) < 1))) he

theorem sigmoid_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 / (1 + Real.exp (-t)))
      (Real.exp (-x) / (1 + Real.exp (-x)) ^ 2) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div
    (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).const_add 1)
    (by positivity : 1 + Real.exp (-x) ≠ 0) using 1 <;> simp only [Function.comp_apply, id_eq] <;> ring

theorem tanh_derivative (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · exact funext (fun t => (Real.tanh_eq_sinh_div_cosh (x := t)))
  · congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem softsign_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ => t / (1 + |t|)) (1 / (1 + |x|) ^ 2) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · convert (hasDerivAt_id x).div ((hasDerivAt_abs_neg hx).const_add 1)
      (by positivity : 1 + |x| ≠ 0) using 1
    simp only [abs_of_neg hx, id_eq]
    ring
  · subst x
    rw [hasDerivAt_iff_tendsto_slope]
    have hc : Continuous (fun t : ℝ => 1 / (1 + |t|)) :=
      continuous_const.div (continuous_const.add continuous_abs) (fun t => by positivity)
    have ht := (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    have he : slope (fun t : ℝ => t / (1 + |t|)) 0 =ᶠ[nhdsWithin 0 {0}ᶜ]
        (fun t : ℝ => 1 / (1 + |t|)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hn : t ≠ 0 := by simpa using ht
      simp [slope, hn, div_eq_mul_inv, mul_comm, mul_left_comm]
    simpa using ht.congr' he.symm
  · convert (hasDerivAt_id x).div ((hasDerivAt_abs_pos hx).const_add 1)
      (by positivity : 1 + |x| ≠ 0) using 1
    simp only [abs_of_pos hx, id_eq]
    ring

-- formalizer:machinery-end

end Remark_Jp5.Machinery
