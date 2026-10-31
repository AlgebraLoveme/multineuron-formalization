module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Theorem_5p1.Machinery

-- formalizer:machinery-begin

lemma relu_difference_bounds (a b : ℝ) (h : b ≤ a) :
    0 ≤ max a 0 - max b 0 ∧ max a 0 - max b 0 ≤ a - b := by
  constructor
  · exact sub_nonneg.mpr (max_le_max h le_rfl)
  · rcases le_total 0 b with hb | hb
    · rw [max_eq_left hb, max_eq_left (hb.trans h)]
    · rw [max_eq_right hb]
      rcases le_total 0 a with ha | ha
      · rw [max_eq_left ha]; linarith
      · rw [max_eq_right ha]; linarith

lemma clipping_bounds (m n y : ℝ) (hmn : m ≤ n) :
    m ≤ m + max (y - m) 0 - max (y - n) 0 ∧
    m + max (y - m) 0 - max (y - n) 0 ≤ n := by
  have h := relu_difference_bounds (y - m) (y - n) (by linarith)
  constructor <;> linarith [h.1, h.2]

lemma clipping_eq (m n y : ℝ) (hm : m ≤ y) (hn : y ≤ n) :
    m + max (y - m) 0 - max (y - n) 0 = y := by
  rw [max_eq_left (sub_nonneg.mpr hm), max_eq_right (sub_nonpos.mpr hn)]
  ring

lemma linear_bounds_on_hull {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set E) (l : E →ₗ[ℝ] ℝ) (a b : ℝ)
    (h : ∀ x ∈ S, a ≤ l x ∧ l x ≤ b) :
    ∀ x ∈ convexHull ℝ S, a ≤ l x ∧ l x ≤ b := by
  apply convexHull_min h
  intro x hx y hy u v hu hv huv
  change a ≤ l (u • x + v • y) ∧ l (u • x + v • y) ≤ b
  simp only [map_add, map_smul, smul_eq_mul]
  constructor
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hx.1),
      mul_nonneg hv (sub_nonneg.mpr hy.1),
      congrArg (fun t : ℝ => t * a) huv]
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hx.2),
      mul_nonneg hv (sub_nonneg.mpr hy.2),
      congrArg (fun t : ℝ => t * b) huv]

lemma relaxation_contains_trajectory
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (X : Set (Fin (w 0) → ℝ))
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L)
    (v : (j : Fin (L + 1)) → Fin (w j) → ℝ) (hx : v 0 ∈ X)
    (hv : ∀ i : Fin L, v i.succ =
      match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))) :
    ∀ k, v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih =>
    refine ⟨ih, subset_convexHull ℝ _ ?_⟩
    exact ⟨⟨v, ih, fun _ _ => rfl⟩, fun i _ _ => hv i⟩

lemma continuous_run
    (σ : ℝ → ℝ) (hσ : Continuous σ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w) :
    ∀ j : Fin (L + 1), Continuous
      (Fin.induction (motive := fun j => (Fin (w 0) → ℝ) → (Fin (w j) → ℝ))
        (fun x : Fin (w 0) → ℝ => x)
        (fun i prev x => match N.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * prev x k) + b j
        | Sum.inr h => fun j => σ (prev x (Fin.cast h.down.symm j))) j) := by
  intro j
  induction j using Fin.induction with
  | zero => exact continuous_id
  | succ i ih =>
    simp only [Fin.induction_succ]
    split
    · apply continuous_pi
      intro j
      exact (continuous_finset_sum _ (fun k _ =>
        continuous_const.mul ((continuous_apply k).comp ih))).add continuous_const
    · apply continuous_pi
      intro j
      exact hσ.comp ((continuous_apply _).comp ih)

lemma relaxation_stages_antitone
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (X : Set (Fin (w 0) → ℝ))
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L) :
    Antitone relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) := by
  apply antitone_nat_of_succ_le
  intro k v hv
  exact hv.1

lemma relaxation_layer_linear_bounds
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (X : Set (Fin (w 0) → ℝ))
    (hL : 1 ≤ L) (i : Fin L) (k : ℕ) (hik : i.val + 1 ≤ k)
    (l : ((j : Fin (L + 1)) → Fin (w j) → ℝ) →ₗ[ℝ] ℝ)
    (a b : ℝ)
    (hgraph : ∀ v : (j : Fin (L + 1)) → Fin (w j) → ℝ,
      (∃ u ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X 1 (by omega) hL) i.val,
        v i.castSucc = u i.castSucc) →
      (v i.succ = match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))) →
      a ≤ l v ∧ l v ≤ b) :
    ∀ v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X 1 (by omega) hL) k,
      a ≤ l v ∧ l v ≤ b := by
  intro v hv
  have hstage := relaxation_stages_antitone σ L w N X 1 (by omega) hL
    hik hv
  apply linear_bounds_on_hull _ l a b _ v hstage.2
  intro z hz
  apply hgraph z
  · obtain ⟨u, hu, heq⟩ := hz.1
    exact ⟨u, hu, heq i.castSucc rfl⟩
  · exact hz.2 i (by omega) (by omega)

lemma extrema_of_bounded_set_with_endpoints (S : Set ℝ) (a b : ℝ)
    (ha : a ∈ S) (hb : b ∈ S) (h : ∀ z ∈ S, a ≤ z ∧ z ≤ b) :
    sInf S = a ∧ sSup S = b := by
  have hne : S.Nonempty := ⟨a, ha⟩
  have hlo : BddBelow S := ⟨a, fun z hz => (h z hz).1⟩
  have hhi : BddAbove S := ⟨b, fun z hz => (h z hz).2⟩
  exact ⟨le_antisymm (csInf_le hlo ha) (le_csInf hne (fun z hz => (h z hz).1)),
    le_antisymm (csSup_le hne (fun z hz => (h z hz).2)) (le_csSup hhi hb)⟩

lemma exists_layer_extension
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (n : ℕ) (hn : 0 < n)
    (layer : (Matrix (Fin n) (Fin (w (Fin.last L))) ℝ × (Fin n → ℝ)) ⊕
      PLift (w (Fin.last L) = n)) :
    ∃ N' : Definition.NetworkSemantics σ (L + 1) (Fin.snoc w n),
      (∀ i : Fin L, HEq (N'.val i.castSucc) (N.val i)) ∧
      HEq (N'.val (Fin.last L)) layer := by
  let W : Fin (L + 1 + 1) → ℕ := Fin.snoc w n
  let before (i : Fin L) :
      (Matrix (Fin (W i.castSucc.succ)) (Fin (W i.castSucc.castSucc)) ℝ ×
        (Fin (W i.castSucc.succ) → ℝ)) ⊕
        PLift (W i.castSucc.castSucc = W i.castSucc.succ) :=
    cast (by simp only [W, ← Fin.castSucc_succ, Fin.snoc_castSucc]) (N.val i)
  let after :
      (Matrix (Fin (W (Fin.last L).succ)) (Fin (W (Fin.last L).castSucc)) ℝ ×
        (Fin (W (Fin.last L).succ) → ℝ)) ⊕
        PLift (W (Fin.last L).castSucc = W (Fin.last L).succ) :=
    cast (by simp only [W, Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]) layer
  let N' : Definition.NetworkSemantics σ (L + 1) W :=
    ⟨Fin.lastCases after before, by
      intro j
      cases j using Fin.lastCases with
      | last => simpa only [W, Fin.snoc_last] using hn
      | cast j => simpa only [W, Fin.snoc_castSucc] using N.property j⟩
  refine ⟨N', ?_, ?_⟩
  · intro i
    dsimp only [N']
    simp only [Fin.lastCases_castSucc]
    exact cast_heq _ _
  · dsimp only [N']
    simp only [Fin.lastCases_last]
    exact cast_heq _ _

lemma layer_application_heq (σ : ℝ → ℝ)
    {a b c d : ℕ} (ha : a = c) (hb : b = d)
    (P : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a = b))
    (Q : (Matrix (Fin d) (Fin c) ℝ × (Fin d → ℝ)) ⊕ PLift (c = d))
    (hPQ : HEq P Q) (x : Fin a → ℝ) (y : Fin c → ℝ) (hxy : HEq x y) :
    HEq (match P with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j)))
      (match Q with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * y k) + b j
      | Sum.inr h => fun j => σ (y (Fin.cast h.down.symm j))) := by
  subst c d
  cases hPQ
  cases hxy
  rfl

lemma extension_trajectory_prefix
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (n : ℕ)
    (N' : Definition.NetworkSemantics σ (L + 1) (Fin.snoc w n))
    (hp : ∀ i : Fin L, HEq (N'.val i.castSucc) (N.val i))
    (v : (j : Fin (L + 1)) → Fin (w j) → ℝ)
    (v' : (j : Fin (L + 1 + 1)) → Fin (Fin.snoc (α := fun _ => ℕ) w n j) → ℝ)
    (hz : HEq (v' 0) (v 0))
    (hv : ∀ i : Fin L, v i.succ =
      match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j)))
    (hv' : ∀ i : Fin (L + 1), v' i.succ =
      match N'.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v' i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v' i.castSucc (Fin.cast h.down.symm j))) :
    ∀ j : Fin (L + 1), HEq (v' j.castSucc) (v j) := by
  intro j
  induction j using Fin.induction with
  | zero => exact hz
  | succ i ih =>
    rw [Fin.castSucc_succ, hv', hv]
    have hh := layer_application_heq σ (Fin.snoc_castSucc _ _ _)
      (by simp only [← Fin.castSucc_succ, Fin.snoc_castSucc])
      _ _ (hp i) _ _ ih
    cases hP : N'.val i.castSucc <;> cases hQ : N.val i <;>
      simpa only [hP, hQ] using hh

lemma relaxation_affine_equation
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (X : Set (Fin (w 0) → ℝ))
    (hL : 1 ≤ L) (i : Fin L) (k : ℕ) (hik : i.val + 1 ≤ k)
    (A : Matrix (Fin (w i.succ)) (Fin (w i.castSucc)) ℝ)
    (b : Fin (w i.succ) → ℝ) (hi : N.val i = Sum.inl (A, b)) :
    ∀ v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X 1 (by omega) hL) k,
      v i.succ = fun j => (∑ t, A j t * v i.castSucc t) + b j := by
  intro v hv
  funext j
  let ev (q : Fin (L + 1)) (t : Fin (w q)) :
      ((j : Fin (L + 1)) → Fin (w j) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => z q t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l := ev i.succ j - ∑ t, A j t • ev i.castSucc t
  have hl (z : (j : Fin (L + 1)) → Fin (w j) → ℝ) :
      l z = z i.succ j - ∑ t, A j t * z i.castSucc t := by
    simp [l, ev]
  have hbound := relaxation_layer_linear_bounds σ L w N X hL i k hik l (b j) (b j)
    (by
      intro z _ hz
      rw [hi] at hz
      have he := congr_fun hz j
      rw [hl]
      constructor <;> linarith) v hv
  rw [hl] at hbound
  linarith [hbound.1, hbound.2]

lemma extension_run_prefix
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (n : ℕ)
    (N' : Definition.NetworkSemantics σ (L + 1) (Fin.snoc w n))
    (hp : ∀ i : Fin L, HEq (N'.val i.castSucc) (N.val i)) :
    let R := Fin.induction
      (motive := fun j => (Fin (w 0) → ℝ) → Fin (w j) → ℝ)
      (fun x => x) (fun i prev x => match N.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * prev x k) + b j
        | Sum.inr h => fun j => σ (prev x (Fin.cast h.down.symm j)))
    let W : Fin (L + 1 + 1) → ℕ := Fin.snoc w n
    let R' := Fin.induction
      (motive := fun j => (Fin (W 0) → ℝ) → Fin (W j) → ℝ)
      (fun x => x) (fun i prev x => match N'.val i with
        | Sum.inl (A, b) => fun j => (∑ k, A j k * prev x k) + b j
        | Sum.inr h => fun j => σ (prev x (Fin.cast h.down.symm j)))
    ∀ (x : Fin (w 0) → ℝ) (x' : Fin (W 0) → ℝ), HEq x' x →
      ∀ j : Fin (L + 1), HEq (R' j.castSucc x') (R j x) := by
  intro R W R' x x' hx
  apply extension_trajectory_prefix σ L w N n N' hp
    (fun j => R j x) (fun j => R' j x') hx
  · intro i
    dsimp only [R, Fin.induction_succ]
  · intro i
    dsimp only [R', Fin.induction_succ]

lemma relaxation_relu_difference
    (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics (fun t => max t 0) L w)
    (X : Set (Fin (w 0) → ℝ)) (hL : 1 ≤ L)
    (i : Fin L) (k : ℕ) (hik : i.val + 1 ≤ k)
    (h : w i.castSucc = w i.succ) (hi : N.val i = Sum.inr ⟨h⟩)
    (p q : Fin (w i.succ)) (d : ℝ)
    (hpre : ∀ u ∈ relaxation.stages(Definition.WindowRelaxation (fun t => max t 0) L w N X 1
        (by omega) hL) i.val,
      0 ≤ u i.castSucc (Fin.cast h.symm p) - u i.castSucc (Fin.cast h.symm q) ∧
      u i.castSucc (Fin.cast h.symm p) - u i.castSucc (Fin.cast h.symm q) ≤ d) :
    ∀ v ∈ relaxation.stages(Definition.WindowRelaxation (fun t => max t 0) L w N X 1
        (by omega) hL) k,
      0 ≤ v i.succ p - v i.succ q ∧ v i.succ p - v i.succ q ≤ d := by
  let l : ((j : Fin (L + 1)) → Fin (w j) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => v i.succ p - v i.succ q
      map_add' := by intros; simp only [Pi.add_apply]; ring
      map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  apply relaxation_layer_linear_bounds (fun t => max t 0) L w N X hL i k hik l 0 d
  intro z hproj hz
  obtain ⟨u, hu, hzu⟩ := hproj
  have hdiff := hpre u hu
  rw [hi] at hz
  have hp := congr_fun hz p
  have hq := congr_fun hz q
  have hzp := congr_fun hzu (Fin.cast h.symm p)
  have hzq := congr_fun hzu (Fin.cast h.symm q)
  dsimp at hp hq
  have hb := relu_difference_bounds
    (z i.castSucc (Fin.cast h.symm p)) (z i.castSucc (Fin.cast h.symm q)) (by linarith [hdiff.1])
  change 0 ≤ z i.succ p - z i.succ q ∧ z i.succ p - z i.succ q ≤ d
  constructor <;> linarith [hb.1, hb.2, hdiff.2]

lemma offset_matrix_evaluation (n : ℕ) (a b x : Fin n → ℝ) :
    (fun j : Fin (n + n) =>
      (∑ k, (Fin.addCases (motive := fun _ => Fin n → ℝ) (fun j k => if j = k then (1 : ℝ) else 0)
        (fun j k => if j = k then (1 : ℝ) else 0) j) k * x k) +
      Fin.addCases (fun j => -a j) (fun j => -b j) j) =
    Fin.addCases (fun j => x j - a j) (fun j => x j - b j) := by
  classical
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp [sub_eq_add_neg]
  · intro j
    simp only [Fin.addCases_right]
    simp [sub_eq_add_neg]

lemma difference_matrix_evaluation (n : ℕ) (a : Fin n → ℝ)
    (x : Fin (n + n) → ℝ) (j : Fin n) :
    (∑ k, (Fin.addCases (fun k => if j = k then (1 : ℝ) else 0)
      (fun k => if j = k then (-1 : ℝ) else 0) k) * x k) + a j =
    a j + x (Fin.castAdd n j) - x (Fin.natAdd n j) := by
  classical
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  simp [sub_eq_add_neg]
  ring

lemma cast_input_heq {a b : ℕ} (h : a = b) (x : Fin b → ℝ) :
    HEq (fun k : Fin a => x (Fin.cast h k)) x := by
  subst b
  rfl

lemma extension_trajectory_output
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (n : ℕ) (N' : Definition.NetworkSemantics σ (L + 1) (Fin.snoc w n))
    (layer : (Matrix (Fin n) (Fin (w (Fin.last L))) ℝ × (Fin n → ℝ)) ⊕
      PLift (w (Fin.last L) = n))
    (hl : HEq (N'.val (Fin.last L)) layer)
    (v : (j : Fin (L + 1 + 1)) → Fin (Fin.snoc (α := fun _ => ℕ) w n j) → ℝ)
    (x : Fin (w (Fin.last L)) → ℝ)
    (hx : HEq (v (Fin.last L).castSucc) x)
    (hv : ∀ i : Fin (L + 1), v i.succ =
      match N'.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))) :
    HEq (v (Fin.last (L + 1)))
      (match layer with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))) := by
  rw [← Fin.succ_last, hv]
  have hh := layer_application_heq σ (Fin.snoc_castSucc _ _ _)
    (by simp only [Fin.succ_last, Fin.snoc_last]) _ _ hl _ _ hx
  cases hP : N'.val (Fin.last L) <;> cases hQ : layer <;>
    simpa only [hP, hQ] using hh

lemma heq_apply_cast {a b : ℕ} (h : a = b)
    (f : Fin a → ℝ) (g : Fin b → ℝ) (hfg : HEq f g) (j : Fin b) :
    f (Fin.cast h.symm j) = g j := by
  subst b
  cases hfg
  rfl

lemma relaxation_affine_cast_equation
    (σ : ℝ → ℝ) (L : ℕ) (w : Fin (L + 1) → ℕ)
    (N : Definition.NetworkSemantics σ L w) (X : Set (Fin (w 0) → ℝ))
    (hL : 1 ≤ L) (i : Fin L) (k : ℕ) (hik : i.val + 1 ≤ k)
    (a b : ℕ) (ha : w i.castSucc = a) (hb : w i.succ = b)
    (A : Matrix (Fin b) (Fin a) ℝ) (bias : Fin b → ℝ)
    (hi : HEq (N.val i) (Sum.inl (A, bias) :
      (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a = b))) :
    ∀ v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X 1 (by omega) hL) k,
      ∀ j : Fin b, v i.succ (Fin.cast hb.symm j) =
        (∑ t, A j t * v i.castSucc (Fin.cast ha.symm t)) + bias j := by
  intro v hv j
  let ev (q : Fin (L + 1)) (t : Fin (w q)) :
      ((j : Fin (L + 1)) → Fin (w j) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => z q t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l := ev i.succ (Fin.cast hb.symm j) -
    ∑ t, A j t • ev i.castSucc (Fin.cast ha.symm t)
  have hl (z : (j : Fin (L + 1)) → Fin (w j) → ℝ) :
      l z = z i.succ (Fin.cast hb.symm j) -
        ∑ t, A j t * z i.castSucc (Fin.cast ha.symm t) := by simp [l, ev]
  have hbound := relaxation_layer_linear_bounds σ L w N X hL i k hik l (bias j) (bias j)
    (by
      intro z _ hz
      have hh := layer_application_heq σ ha hb _ _ hi (z i.castSucc)
        (fun t => z i.castSucc (Fin.cast ha.symm t))
        (cast_input_heq ha.symm (z i.castSucc)).symm
      have he : HEq (z i.succ)
          (fun j => (∑ t, A j t * z i.castSucc (Fin.cast ha.symm t)) + bias j) := by
        cases hP : N.val i <;> simp only [hP] at hz hh <;> exact hz ▸ hh
      have hj := heq_apply_cast hb _ _ he j
      rw [hl]
      constructor <;> linarith) v hv
  rw [hl] at hbound
  linarith [hbound.1, hbound.2]

lemma relu_layer_eq_of_heq {a b n : ℕ} (ha : a = n) (hb : b = n)
    (P : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a = b))
    (hP : HEq P (Sum.inr ⟨rfl⟩ :
      (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) ⊕ PLift (n = n))) :
    P = Sum.inr ⟨ha.trans hb.symm⟩ := by
  subst a b
  exact eq_of_heq hP

lemma relu_layer_heq {a b n : ℕ} (ha : a = n) (hb : b = n) (h : a = b) :
    HEq (Sum.inr ⟨h⟩ : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a = b))
      (Sum.inr ⟨rfl⟩ : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) ⊕ PLift (n = n)) := by
  subst a b
  rfl

-- formalizer:machinery-end

end Theorem_5p1.Machinery
