module
public import Formalization.Result.helpers.Remark_Jp5.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Remark_Jp5

theorem result_J_5 :
  AdmissibleActivation (fun t => 1 / (1 + Real.exp (-t))) ∧
  AdmissibleActivation Real.tanh ∧
  AdmissibleActivation Real.arctan ∧
  AdmissibleActivation (fun t => t / (1 + |t|)) := (by
  -- formalizer:proof-begin
  let ds := Machinery.sigmoid_derivative
  let dt := Machinery.tanh_derivative
  let du := Machinery.softsign_derivative
  -- Remark J.5: the displayed positive derivatives give strict increase,
  -- injectivity, and continuity; softsign at zero uses its difference quotient.
  have hs := strictMono_of_hasDerivAt_pos ds (fun x => by positivity)
  have ht := strictMono_of_hasDerivAt_pos dt
    (fun x => div_pos zero_lt_one (sq_pos_of_pos (Real.cosh_pos x)))
  have ha := strictMono_of_hasDerivAt_pos Real.hasDerivAt_arctan
    (fun x => by positivity)
  have hu := strictMono_of_hasDerivAt_pos du (fun x => by positivity)
  -- Boundedness excludes positive-degree polynomials; strict increase excludes
  -- constants. These supply Definition J.4's non-polynomial requirement.
  have bs : ∀ x : ℝ, |1 / (1 + Real.exp (-x))| ≤ 1 := by
    intro x
    rw [abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).mpr
    linarith [Real.exp_pos (-x)]
  have ba : ∀ x : ℝ, |Real.arctan x| ≤ Real.pi / 2 := by
    intro x
    exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan x,
      Real.arctan_lt_pi_div_two x⟩).le
  have bu : ∀ x : ℝ, |x / (1 + |x|)| ≤ 1 := by
    intro x
    rw [abs_div, abs_of_pos (by positivity : 0 < 1 + |x|)]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have ns := Machinery.bounded_strictMono_nonpolynomial hs 1 bs
  have nt := Machinery.bounded_strictMono_nonpolynomial ht 1
    (fun x => (Real.abs_tanh_lt_one x).le)
  have na := Machinery.bounded_strictMono_nonpolynomial ha (Real.pi / 2) ba
  have nu := Machinery.bounded_strictMono_nonpolynomial hu 1 bu
  refine ⟨⟨continuous_iff_continuousAt.mpr (fun x => (ds x).continuousAt), ns, hs.injective, ?_⟩,
    ⟨continuous_iff_continuousAt.mpr (fun x => (dt x).continuousAt), nt, ht.injective, ?_⟩,
    ⟨Real.continuous_arctan, na, ha.injective, ?_⟩,
    ⟨continuous_iff_continuousAt.mpr (fun x => (du x).continuousAt), nu, hu.injective, ?_⟩⟩
  -- Choose a = -1 and b = 1. Sigmoid's reflection identity gives midpoint
  -- value 1/2; oddness gives midpoint value zero for the other three examples.
  · refine ⟨-1, 1, by norm_num, ?_⟩
    simp only [neg_add_cancel, zero_div, neg_zero, Real.exp_zero, neg_neg]
    rw [Real.exp_neg]
    have he := Real.exp_pos 1
    field_simp
    <;> ring
  · exact ⟨-1, 1, by norm_num, by simp [Real.tanh_neg]⟩
  · exact ⟨-1, 1, by norm_num, by simp [Real.arctan_neg]⟩
  · exact ⟨-1, 1, by norm_num, by norm_num⟩
  -- formalizer:proof-end
)

end Remark_Jp5
