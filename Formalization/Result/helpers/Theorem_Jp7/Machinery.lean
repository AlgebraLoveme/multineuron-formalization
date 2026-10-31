module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_3p2
public import Formalization.Result.Theorem_3p3
public import Formalization.Result.Lemma_Jp1
public import Formalization.Result.Proposition_Jp2
public import Formalization.Result.Lemma_Jp6
public import Mathlib

public section

namespace Theorem_Jp7.Machinery

-- formalizer:machinery-begin

/-- True trajectories survive every sequential window constraint. -/
theorem exact_mem_windows {L r : ℕ} {w : Fin (L + 1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r →
        v i.succ = step i (v i.castSucc)})
    (v : (j : Fin (L+1)) → Fin (w j) → ℝ) (hv : v 0 ∈ X)
    (he : ∀ i, v i.succ = step i (v i.castSucc)) : ∀ k, v ∈ C k := by
  intro k
  induction k with
  | zero => simpa [hzero] using hv
  | succ k ih =>
    rw [hsucc]
    exact ⟨ih, subset_convexHull ℝ _ ⟨⟨v, ih, fun _ _ => rfl⟩, fun i _ _ => he i⟩⟩

/-- One assignment uses midpoint windows before a cut and exact continuations
afterwards. Coordinates outside each window remain free. -/
theorem midpoint_then_exact_mem_windows {L r cut : ℕ} {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r →
        v i.succ = step i (v i.castSucc)})
    (v a b : (j : Fin (L+1)) → Fin (w j) → ℝ)
    (hv : v 0 ∈ X) (ha : a 0 ∈ X) (hb : b 0 ∈ X)
    (hea : ∀ i, a i.succ = step i (a i.castSucc))
    (heb : ∀ i, b i.succ = step i (b i.castSucc))
    (hm : ∀ s, s < cut → ∀ j, s ≤ j.val → j.val ≤ s+r →
      v j = fun t => (a j t + b j t) / 2)
    (he : ∀ i, cut ≤ i.val → v i.succ = step i (v i.castSucc)) :
    ∀ k, v ∈ C k := by
  classical
  have hA := exact_mem_windows step X C hzero hsucc a ha hea
  have hB := exact_mem_windows step X C hzero hsucc b hb heb
  intro k
  induction k with
  | zero => simpa [hzero] using hv
  | succ s ih =>
    rw [hsucc]
    refine ⟨ih, ?_⟩
    by_cases hs : s < cut
    · let a' := fun j => if s ≤ j.val ∧ j.val ≤ s+r then a j else v j
      let b' := fun j => if s ≤ j.val ∧ j.val ≤ s+r then b j else v j
      have ha' : a' ∈ {q : (j : Fin (L+1)) → Fin (w j) → ℝ |
          (∃ u ∈ C s, ∀ j, j.val = s → q j = u j) ∧
          ∀ i : Fin L, s ≤ i.val → i.val < s+r →
            q i.succ = step i (q i.castSucc)} := by
        refine ⟨⟨a, hA s, ?_⟩, ?_⟩
        · intro j hj; simp [a', hj]
        · intro i hi hi'
          simpa [a', show s ≤ i.val + 1 ∧ i.val + 1 ≤ s+r by omega,
            show s ≤ i.val ∧ i.val ≤ s+r by omega] using hea i
      have hb' : b' ∈ {q : (j : Fin (L+1)) → Fin (w j) → ℝ |
          (∃ u ∈ C s, ∀ j, j.val = s → q j = u j) ∧
          ∀ i : Fin L, s ≤ i.val → i.val < s+r →
            q i.succ = step i (q i.castSucc)} := by
        refine ⟨⟨b, hB s, ?_⟩, ?_⟩
        · intro j hj; simp [b', hj]
        · intro i hi hi'
          simpa [b', show s ≤ i.val + 1 ∧ i.val + 1 ≤ s+r by omega,
            show s ≤ i.val ∧ i.val ≤ s+r by omega] using heb i
      have hmid := (convex_convexHull ℝ _) (subset_convexHull ℝ _ ha')
        (subset_convexHull ℝ _ hb') (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
      have hvab : (1/2:ℝ) • a' + (1/2:ℝ) • b' = v := by
        ext j t
        by_cases hj : s ≤ j.val ∧ j.val ≤ s+r
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, a', b', if_pos hj]
          rw [hm s hs j hj.1 hj.2]
          ring
        · simp [a', b', hj]; ring
      exact hvab ▸ hmid
    · exact subset_convexHull ℝ _ ⟨⟨v, ih, fun _ _ => rfl⟩,
        fun i hi _ => he i (by omega)⟩

/-- Archimedean choice of the bridge length in J.7. -/
theorem bridge_length (α : ℝ) (hα : α < 1) (L₀ : ℕ) :
    ∃ M : ℕ, 3 ≤ M ∧ α * (L₀ + M + 1) ≤ M - 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((α * (L₀ + 1) + 1) / (1 - α))
  let M := max 3 n
  have hnM : (n : ℝ) ≤ M := by exact_mod_cast (le_max_right 3 n)
  have hden : 0 < 1 - α := by linarith
  have hquot : (α * (L₀ + 1) + 1) / (1 - α) < M := lt_of_lt_of_le hn hnM
  have hmul := (div_lt_iff₀ hden).mp hquot
  refine ⟨M, le_max_left _ _, ?_⟩
  nlinarith

/-- Increasing bridge length preserves the fractional-window bound. -/
theorem window_length_bound (α : ℝ) (hα : α < 1) (L₀ M N : ℕ)
    (hM : 3 ≤ M) (hMN : M ≤ N)
    (hchoice : α * (L₀ + M + 1) ≤ M - 1) :
    max 1 ⌊α * ((L₀ + N + 1 : ℕ) : ℝ)⌋₊ ≤ N - 1 := by
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hN : 1 ≤ N := by omega
  have hbound : α * ((L₀ + N + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hN]
    push_cast
    nlinarith
  exact max_le (by omega) (Nat.floor_le_of_le hbound)

/-- Continuity of every prefix of a network with continuous activation. -/
theorem continuous_prefix (σ : ℝ → ℝ) (hσ : Continuous σ)
    {L : ℕ} {w : Fin (L+1) → ℕ} (N : Definition.NetworkSemantics σ L w) :
    let run : (j : Fin (L+1)) → (Fin (w 0) → ℝ) → (Fin (w j) → ℝ) := Fin.induction (fun x : Fin (w 0) → ℝ => x)
      (fun i prev x => match N.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * prev x k) + b j
        | Sum.inr h => fun j => σ (prev x (Fin.cast h.down.symm j)))
    ∀ j, Continuous (run j) := by
  intro run j
  induction j using Fin.induction with
  | zero => exact continuous_id
  | succ i ih =>
    change Continuous (fun x => match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * run i.castSucc x k) + b j
      | Sum.inr h => fun j => σ (run i.castSucc x (Fin.cast h.down.symm j)))
    cases N.val i with
    | inl ab =>
      apply continuous_pi
      intro j
      exact (continuous_finset_sum _ (fun k _ => continuous_const.mul
        ((continuous_apply k).comp ih))).add continuous_const
    | inr h =>
      apply continuous_pi
      intro j
      exact hσ.comp ((continuous_apply _).comp ih)

/-- Compactness gives a strictly positive attained Euclidean separation. -/
theorem separated_compact {d : ℕ} (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (hne : K.Nonempty) (p : Fin d → ℝ) (hp : p ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      δ ≤ ‖WithLp.toLp 2 (x - p)‖ := by
  let distance := fun x : Fin d → ℝ => ‖WithLp.toLp 2 (x - p)‖
  have hc : Continuous distance := by
    exact continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp
      (continuous_id.sub continuous_const))
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  refine ⟨distance x, ?_, fun y hy => hmin hy⟩
  apply norm_pos_iff.mpr
  intro he
  have hxp : x - p = 0 := by
    exact congrArg (WithLp.ofLp) he
  exact hp ((sub_eq_zero.mp hxp) ▸ hx)

/-- Transfer the compact-uniform approximation error to the detector bounds.
The target is the squared Euclidean distance used in J.7. -/
theorem detector_parameters (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ t, σ t = q.eval t)
    {d : ℕ} (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (p : Fin d → ℝ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hsep : ∀ x ∈ K, δ ≤ ‖WithLp.toLp 2 (x-p)‖) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (W : Fin n → Fin d → ℝ)
      (b : Fin n → ℝ) (c : ℝ),
      c + (∑ i, a i * σ ((∑ j, W i j * p j) + b i)) ≤ T/2 ∧
      ∀ x ∈ K, 3*T/2 ≤ c + (∑ i, a i * σ ((∑ j, W i j * x j) + b i)) := by
  let target := fun x : Fin d → ℝ => (2*T / δ^2) * ‖WithLp.toLp 2 (x-p)‖^2
  have hc : Continuous target := by
    apply Continuous.const_mul
    apply Continuous.pow
    exact continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp
      (continuous_id.sub continuous_const))
  have hcompact : IsCompact (convexHull ℝ (insert p K)) :=
    by
      let e := WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
      have hh := Lemma_Jp1.Machinery.compact_convexHull
        d (e.symm '' insert p K) ((hK.insert p).image (PiLp.continuous_toLp 2 _))
      have hi := hh.image (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
      change IsCompact (e.toLinearMap '' convexHull ℝ (e.symm '' insert p K)) at hi
      rw [LinearMap.image_convexHull] at hi
      simpa only [LinearMap.coe_coe, LinearEquiv.coe_coe, Set.image_image,
        e.apply_symm_apply, Function.comp_def, Set.image_id'] using hi
  obtain ⟨n, a, W, b, c, happ⟩ := Axioms.ExternalUniversalApproximation
    σ hσ hnp d (convexHull ℝ (insert p K)) hcompact target hc.continuousOn
      (T/2) (by positivity)
  refine ⟨n, a, W, b, c, ?_, ?_⟩
  · have h := (abs_lt.mp (happ p (subset_convexHull ℝ _ (Set.mem_insert p K)))).2
    simpa [target] using h.le
  · intro x hx
    have h := (abs_lt.mp (happ x (subset_convexHull ℝ _ (Set.mem_insert_of_mem p hx)))).1
    have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
    have hnorm := hsep x hx
    have hsq : δ^2 ≤ ‖WithLp.toLp 2 (x-p)‖^2 := by nlinarith [norm_nonneg (WithLp.toLp 2 (x-p))]
    have hmul : 2*T ≤ target x := by
      have hdiv : 0 < 2*T/δ^2 := by positivity
      have hprod := mul_le_mul_of_nonneg_left hsq hdiv.le
      have he : (2*T/δ^2)*δ^2 = 2*T := div_mul_cancel₀ _ (ne_of_gt hδ2)
      rw [he] at hprod
      exact hprod
    linarith


/-- Propagate a coordinate invariant through one exact window graph. -/
theorem window_graph_invariant {L : ℕ} {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (Q : (j : Fin (L+1)) → Set (Fin (w j) → ℝ))
    (hstep : ∀ (i : Fin L) (x : Fin (w i.castSucc) → ℝ), x ∈ Q i.castSucc → step i x ∈ Q i.succ)
    (s r : ℕ) (v : (j : Fin (L+1)) → Fin (w j) → ℝ)
    (hstart : ∀ j, j.val = s → v j ∈ Q j)
    (he : ∀ i : Fin L, s ≤ i.val → i.val < s+r →
      v i.succ = step i (v i.castSucc)) :
    ∀ j, s ≤ j.val → j.val ≤ s+r → v j ∈ Q j := by
  intro j
  induction j using Fin.induction with
  | zero => intro hs _; exact hstart 0 (by simp at hs ⊢; omega)
  | succ i ih =>
    intro hs hj
    by_cases hi : i.val + 1 = s
    · exact hstart i.succ hi
    · rw [he i (by simp at hs; omega) (by simp at hj; omega)]
      exact hstep i _ (ih (by simp at hs; simp; omega) (by simp at hj; simp; omega))

/-- Convex coordinate envelopes bound every coordinate reached by the windows.
The sets are only envelopes: the relaxation itself retains all tuple constraints. -/
theorem windows_enclosed {L r : ℕ} (hr : 1 ≤ r) {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (X : Set (Fin (w 0) → ℝ))
    (Q : (j : Fin (L+1)) → Set (Fin (w j) → ℝ))
    (hQ : ∀ j, Convex ℝ (Q j)) (hX : X ⊆ Q 0)
    (hstep : ∀ (i : Fin L) (x : Fin (w i.castSucc) → ℝ), x ∈ Q i.castSucc → step i x ∈ Q i.succ)
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r →
        v i.succ = step i (v i.castSucc)}) :
    ∀ s v, v ∈ C s → ∀ j, j.val ≤ (if s = 0 then 0 else s+r-1) → v j ∈ Q j := by
  intro s
  induction s with
  | zero =>
    intro v hv j hj
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst j
    exact hX (by simpa [hzero] using hv)
  | succ s ih =>
    intro v hv j hj
    rw [hsucc] at hv
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false] at hj
    by_cases hjs : j.val < s
    · exact ih v hv.1 j (by split_ifs <;> omega)
    · have hsub : convexHull ℝ {q : (j : Fin (L+1)) → Fin (w j) → ℝ |
          (∃ u ∈ C s, ∀ k, k.val = s → q k = u k) ∧
          ∀ i : Fin L, s ≤ i.val → i.val < s+r →
            q i.succ = step i (q i.castSucc)} ⊆
          (fun q => q j) ⁻¹' Q j := by
        apply convexHull_min
        · intro q hq
          obtain ⟨⟨u, hu, hqu⟩, he⟩ := hq
          exact window_graph_invariant step Q hstep s r q
            (fun k hk => by
              rw [hqu k hk]
              exact ih u hu k (by rw [hk]; split_ifs <;> omega))
            he j (by omega) (by omega)
        · exact (hQ j).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun j : Fin (L+1) => Fin (w j) → ℝ) j)
      exact hsub hv.2

/-- Compact hull transport from Euclidean coordinates to the network's Pi type. -/
theorem compact_hull {d : ℕ} (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  let e := WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
  have hh := Lemma_Jp1.Machinery.compact_convexHull
    d (e.symm '' K) (hK.image (PiLp.continuous_toLp 2 _))
  have hi := hh.image (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  change IsCompact (e.toLinearMap '' convexHull ℝ (e.symm '' K)) at hi
  rw [LinearMap.image_convexHull] at hi
  simpa only [LinearMap.coe_coe, LinearEquiv.coe_coe, Set.image_image,
    e.apply_symm_apply, Function.comp_def, Set.image_id'] using hi

/-- Iterated compact graph-image hulls supply envelopes for every coordinate. -/
theorem compact_coordinate_envelopes {L : ℕ} {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (hc : ∀ i, Continuous (step i))
    (X : Set (Fin (w 0) → ℝ)) (hX : IsCompact X) :
    ∃ Q : (j : Fin (L+1)) → Set (Fin (w j) → ℝ),
      (∀ j, IsCompact (Q j)) ∧ (∀ j, Convex ℝ (Q j)) ∧ X ⊆ Q 0 ∧
      ∀ (i : Fin L) (x : Fin (w i.castSucc) → ℝ), x ∈ Q i.castSucc → step i x ∈ Q i.succ := by
  let Q : (j : Fin (L+1)) → Set (Fin (w j) → ℝ) :=
    Fin.induction (convexHull ℝ X) (fun i prev => convexHull ℝ (step i '' prev))
  have hQ0 : Q 0 = convexHull ℝ X := by simp [Q]
  have hQs : ∀ i : Fin L, Q i.succ = convexHull ℝ (step i '' Q i.castSucc) := by
    intro i; simp only [Q, Fin.induction_succ]
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro j
    induction j using Fin.induction with
    | zero => rw [hQ0]; exact compact_hull X hX
    | succ i ih => rw [hQs]; exact compact_hull _ (ih.image (hc i))
  · intro j
    induction j using Fin.induction with
    | zero => rw [hQ0]; exact convex_convexHull ℝ X
    | succ i ih => rw [hQs]; exact convex_convexHull ℝ _
  · rw [hQ0]; exact subset_convexHull ℝ X
  · intro i x hx
    rw [hQs]
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩


/-- Every final relaxed coordinate has finite upper and lower bounds. -/
theorem window_output_bounded {L r : ℕ} (hr : 1 ≤ r) (hrL : r ≤ L)
    {w : Fin (L+1) → ℕ}
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (hc : ∀ i, Continuous (step i))
    (X : Set (Fin (w 0) → ℝ)) (hX : IsCompact X)
    (C : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hzero : C 0 = {v | v 0 ∈ X})
    (hsucc : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r →
        v i.succ = step i (v i.castSucc)})
    (t : Fin (w (Fin.last L))) :
    BddBelow ((fun v => v (Fin.last L) t) '' C (L-r+1)) ∧
      BddAbove ((fun v => v (Fin.last L) t) '' C (L-r+1)) := by
  obtain ⟨Q, hQc, hQv, hXQ, hstep⟩ := compact_coordinate_envelopes step hc X hX
  have hbound := windows_enclosed hr step X Q hQv hXQ hstep C hzero hsucc
  have hcompact := (hQc (Fin.last L)).image (continuous_apply t)
  have hsub : ((fun v => v (Fin.last L) t) '' C (L-r+1)) ⊆
      (fun x => x t) '' Q (Fin.last L) := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v (Fin.last L), hbound _ _ hv _ ?_, rfl⟩
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Fin.val_last]
    omega
  exact ⟨hcompact.bddBelow.mono hsub, hcompact.bddAbove.mono hsub⟩


/-- Coordinatewise linear changes of variables carry full window graph hulls
onto the transformed hulls, including all intermediate coordinates. -/
theorem window_graph_conjugate {L : ℕ} {w : Fin (L+1) → ℕ}
    (step step' : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (e : (j : Fin (L+1)) → (Fin (w j) → ℝ) ≃ₗ[ℝ] (Fin (w j) → ℝ))
    (hcomm : ∀ i x, e i.succ (step i x) = step' i (e i.castSucc x))
    (s r : ℕ) (C : Set ((j : Fin (L+1)) → Fin (w j) → ℝ)) :
    let E := LinearEquiv.piCongrRight e
    E '' {v : (j : Fin (L+1)) → Fin (w j) → ℝ |
      (∃ u ∈ C, ∀ j, j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = step i (v i.castSucc)} =
    {v : (j : Fin (L+1)) → Fin (w j) → ℝ |
      (∃ u ∈ E '' C, ∀ j, j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = step' i (v i.castSucc)} := by
  intro E
  apply Set.Subset.antisymm
  · rintro _ ⟨v, ⟨⟨u, hu, hvu⟩, he⟩, rfl⟩
    refine ⟨⟨E u, ⟨u, hu, rfl⟩, ?_⟩, ?_⟩
    · intro j hj; exact congrArg (e j) (hvu j hj)
    · intro i hi hi'
      change e i.succ (v i.succ) = step' i (e i.castSucc (v i.castSucc))
      rw [he i hi hi', hcomm]
  · rintro v ⟨⟨_, ⟨u, hu, rfl⟩, hvu⟩, he⟩
    refine ⟨E.symm v, ⟨⟨u, hu, ?_⟩, ?_⟩, E.apply_symm_apply v⟩
    · intro j hj
      change (e j).symm (v j) = u j
      apply (e j).injective
      simpa using hvu j hj
    · intro i hi hi'
      change (e i.succ).symm (v i.succ) = step i ((e i.castSucc).symm (v i.castSucc))
      apply (e i.succ).injective
      rw [hcomm]
      simpa using he i hi hi'

/-- The sequential relaxation commutes with coordinatewise linear equivalences.
Output negation is the instance which reflects only the last coordinate. -/
theorem windows_conjugate {L r : ℕ} {w : Fin (L+1) → ℕ}
    (step step' : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (e : (j : Fin (L+1)) → (Fin (w j) → ℝ) ≃ₗ[ℝ] (Fin (w j) → ℝ))
    (hcomm : ∀ i x, e i.succ (step i x) = step' i (e i.castSucc x))
    (X : Set (Fin (w 0) → ℝ))
    (C D : ℕ → Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hC0 : C 0 = {v | v 0 ∈ X})
    (hD0 : D 0 = {v | v 0 ∈ e 0 '' X})
    (hCs : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v |
      (∃ u ∈ C s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = step i (v i.castSucc)})
    (hDs : ∀ s, D (s+1) = D s ∩ convexHull ℝ {v |
      (∃ u ∈ D s, ∀ j : Fin (L+1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = step' i (v i.castSucc)}) :
    ∀ k, (LinearEquiv.piCongrRight e) '' C k = D k := by
  let E := LinearEquiv.piCongrRight e
  intro k
  induction k with
  | zero =>
    rw [hC0, hD0]
    apply Set.Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v 0, hv, rfl⟩
    · rintro v ⟨x, hx, hxe⟩
      refine ⟨E.symm v, ?_, E.apply_symm_apply v⟩
      change (e 0).symm (v 0) ∈ X
      rw [← hxe, LinearEquiv.symm_apply_apply]
      exact hx
  | succ s ih =>
    rw [hCs, hDs, Set.image_inter E.injective]
    have hh := E.toLinearMap.image_convexHull {v : (j : Fin (L+1)) → Fin (w j) → ℝ |
      (∃ u ∈ C s, ∀ j, j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = step i (v i.castSucc)}
    change E '' convexHull ℝ _ = convexHull ℝ (E '' _) at hh
    rw [hh, window_graph_conjugate step step' e hcomm s r (C s), ih]


/-- Matrix/bias formula for merging two counted affine layers. -/
theorem affine_composition {a b c : ℕ}
    (A : Matrix (Fin b) (Fin a) ℝ) (u : Fin b → ℝ)
    (P : Matrix (Fin c) (Fin b) ℝ) (q : Fin c → ℝ) (x : Fin a → ℝ) :
    (fun j => (∑ k, (∑ t, P j t * A t k) * x k) +
      ((∑ t, P j t * u t) + q j)) =
    (fun j => (∑ t, P j t * ((∑ k, A t k * x k) + u t)) + q j) := by
  ext j
  simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc, add_assoc]

/-- Replacing one layer preserves every earlier prefix, independently of how
that layer acts. This also applies to negating the final affine output. -/
theorem evolution_agrees_before {L : ℕ} {w : Fin (L+1) → ℕ}
    (step step' : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (F G : (j : Fin (L+1)) → (Fin (w 0) → ℝ) → (Fin (w j) → ℝ))
    (hzero : F 0 = G 0)
    (hF : ∀ i x, F i.succ x = step i (F i.castSucc x))
    (hG : ∀ i x, G i.succ x = step' i (G i.castSucc x))
    (cut : ℕ) (hs : ∀ i : Fin L, i.val < cut → step i = step' i) :
    ∀ j, j.val ≤ cut → F j = G j := by
  intro j
  induction j using Fin.induction with
  | zero => intro _; exact hzero
  | succ i ih =>
    intro hj
    funext x
    rw [hF, hG, hs i (by simp at hj; omega), ih (by simp at hj; simp; omega)]

/-- Any affine layer preserves the selected midpoint. -/
theorem affine_midpoint {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ)
    (u : Fin b → ℝ) (x y : Fin a → ℝ) :
    (fun j => (∑ k, A j k * ((x k + y k)/2)) + u j) =
    (fun j => (((∑ k, A j k * x k) + u j) +
      ((∑ k, A j k * y k) + u j))/2) := by
  ext j
  simp only [div_eq_mul_inv, ← mul_assoc, add_mul, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  ring

/-- Evaluation of a dependent trajectory is unchanged by transporting its index. -/
theorem coordinate_cast {I : Type*} (w : I → ℕ)
    (v : (i : I) → Fin (w i) → ℝ) {i j : I} (h : i = j) (k : Fin (w i)) :
    v i k = v j (Fin.cast (congrArg w h) k) := by
  cases h
  rfl

-- formalizer:machinery-end

end Theorem_Jp7.Machinery
