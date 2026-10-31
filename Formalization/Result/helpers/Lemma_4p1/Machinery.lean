module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Lemma_4p1.Machinery

-- formalizer:machinery-begin

lemma padding_depth (a : ℝ) (ha : 0 < a) (ha' : a < 1) (n : ℕ) :
    let L := ⌈max (1 / a) (((n : ℝ) + 1) / (1 - a))⌉₊
    n < L ∧ 1 ≤ max 1 ⌊a * (L : ℝ)⌋₊ ∧
      max 1 ⌊a * (L : ℝ)⌋₊ ≤ L - n := by
  dsimp
  let L := ⌈max (1 / a) (((n : ℝ) + 1) / (1 - a))⌉₊
  change n < L ∧ 1 ≤ max 1 ⌊a * (L : ℝ)⌋₊ ∧
    max 1 ⌊a * (L : ℝ)⌋₊ ≤ L - n
  have hceil := Nat.le_ceil (max (1 / a) (((n : ℝ) + 1) / (1 - a)))
  have hquot : ((n : ℝ) + 1) / (1 - a) ≤ (L : ℝ) :=
    (le_max_right _ _).trans hceil
  have hmul := (div_le_iff₀ (by linarith : 0 < 1 - a)).mp hquot
  have hnonneg : 0 ≤ a * (L : ℝ) := mul_nonneg ha.le (Nat.cast_nonneg _)
  have hnreal : (n : ℝ) < (L : ℝ) := by nlinarith
  have hn : n < L := by exact_mod_cast hnreal
  have hfloor := Nat.floor_le hnonneg
  have hf : ⌊a * (L : ℝ)⌋₊ + n ≤ L := by
    have : (⌊a * (L : ℝ)⌋₊ : ℝ) + (n : ℝ) ≤ (L : ℝ) := by nlinarith
    exact_mod_cast this
  exact ⟨hn, le_max_left _ _, max_le (by omega) (by omega)⟩

lemma window_does_not_cross (left right r s : ℕ)
    (hgap : left + r ≤ right) : s + r ≤ right ∨ left ≤ s := by
  omega

lemma relaxation_stage_convex (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (hX : Convex ℝ X)
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L) (k : ℕ) :
    Convex ℝ (relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k) := by
  unfold Definition.WindowRelaxation
  dsimp only
  induction k with
  | zero =>
    intro x hx y hy a b ha hb hab
    exact hX hx hy ha hb hab
  | succ k ih =>
    exact ih.inter (convex_convexHull ℝ _)

lemma relaxation_exact_trajectory (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ))
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L)
    (v : (j : Fin (L + 1)) → Fin (w j) → ℝ) (hv : v 0 ∈ X)
    (hstep : ∀ i : Fin L, v i.succ =
      match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j)))
    (k : ℕ) : v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k := by
  unfold Definition.WindowRelaxation
  dsimp only
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact ⟨ih, subset_convexHull ℝ _ ⟨⟨v, ih, fun _ _ => rfl⟩,
      fun i _ _ => hstep i⟩⟩

lemma relaxation_stage_antitone (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ))
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L) :
    Antitone relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) := by
  apply antitone_nat_of_succ_le
  intro k
  exact Set.inter_subset_left

lemma convexHull_coordinate_replacement
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (p : ι → Prop) [DecidablePred p] (S : Set ((i : ι) → E i))
    (hS : ∀ v ∈ S, ∀ z, (∀ i, p i → z i = v i) → z ∈ S)
    (v : (i : ι) → E i) (hv : v ∈ convexHull ℝ S) (z : (i : ι) → E i)
    (hz : ∀ i, p i → z i = v i) : z ∈ convexHull ℝ S := by
  let F : ((i : ι) → E i) →ᵃ[ℝ] ((i : ι) → E i) :=
    { toFun := fun u i => if p i then u i else z i
      linear :=
        { toFun := fun u i => if p i then u i else 0
          map_add' := by intros; funext i; by_cases hi : p i <;> simp [hi]
          map_smul' := by intros; funext i; by_cases hi : p i <;> simp [hi] }
      map_vadd' := by intros; funext i; by_cases hi : p i <;> simp [hi] }
  have hF : F '' S ⊆ S := by
    rintro _ ⟨u, hu, rfl⟩
    apply hS u hu
    intro i hi
    simp [F, hi]
  have hFv : F v = z := by
    funext i
    by_cases hi : p i
    · simpa [F, hi] using (hz i hi).symm
    · simp [F, hi]
  have him : F v ∈ F '' convexHull ℝ S := ⟨v, ‹v ∈ convexHull ℝ S›, rfl⟩
  rw [F.image_convexHull] at him
  exact hFv ▸ convexHull_mono hF him

lemma relaxation_hull_exact (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (hX : Convex ℝ X)
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L) (k : ℕ) :
    convexHull ℝ {v : (j : Fin (L + 1)) → Fin (w j) → ℝ |
      v 0 ∈ X ∧ ∀ i : Fin L, v i.succ =
        match N.val i with
        | Sum.inl (A, b) => fun j => (∑ t, A j t * v i.castSucc t) + b j
        | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j))} ⊆
      relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k := by
  apply convexHull_min
  · rintro v ⟨hv, hstep⟩
    exact relaxation_exact_trajectory σ L w N X r hr hL v hv hstep k
  · exact relaxation_stage_convex σ L w N X hX r hr hL k

lemma window_hull_replacement (L : ℕ) (w : Fin (L + 1) → ℕ)
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (C : Set ((j : Fin (L + 1)) → Fin (w j) → ℝ)) (s r : ℕ)
    (v z : (j : Fin (L + 1)) → Fin (w j) → ℝ)
    (hv : v ∈ convexHull ℝ {v | (∃ u ∈ C,
      ∀ j : Fin (L + 1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s + r → v i.succ = step i (v i.castSucc)})
    (hz : ∀ j : Fin (L + 1), s ≤ j.val → j.val ≤ s + r → z j = v j) :
    z ∈ convexHull ℝ {v | (∃ u ∈ C,
      ∀ j : Fin (L + 1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s + r → v i.succ = step i (v i.castSucc)} := by
  apply convexHull_coordinate_replacement (fun j => s ≤ j.val ∧ j.val ≤ s + r) _ _
    v hv z (fun j hj => hz j hj.1 hj.2)
  rintro u ⟨⟨a, ha, hau⟩, hu⟩ b hb
  constructor
  · refine ⟨a, ha, ?_⟩
    intro j hj
    rw [hb j (by omega)]
    exact hau j hj
  · intro i hi hi'
    rw [hb i.succ (by simp only [Fin.val_succ]; omega),
      hb i.castSucc (by simp only [Fin.val_castSucc]; omega)]
    exact hu i hi hi'

lemma relaxation_prefix_replacement (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L)
    (k : ℕ) (v z : (j : Fin (L + 1)) → Fin (w j) → ℝ)
    (hv : v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k)
    (hz : ∀ j : Fin (L + 1), j.val < k + r → z j = v j) :
    z ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k := by
  induction k with
  | zero =>
    change z 0 ∈ X
    change v 0 ∈ X at hv
    rw [hz 0 (by simp; omega)]
    exact hv
  | succ k ih =>
    change v ∈ _ ∩ _ at hv
    change z ∈ _ ∩ _
    constructor
    · apply ih hv.1
      intro j hj
      exact hz j (by omega)
    · apply window_hull_replacement L w
        (fun i x => match N.val i with
          | Sum.inl (A, b) => fun j => (∑ t, A j t * x t) + b j
          | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j)))
        (relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k) k r v z hv.2
      intro j _ hj
      exact hz j (by omega)

lemma relaxation_splice (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L)
    (left right : ℕ) (hgap : left + r ≤ right)
    (u v : (j : Fin (L + 1)) → Fin (w j) → ℝ)
    (hu : ∀ k, u ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k)
    (hagree : ∀ j : Fin (L + 1), j.val ≤ right → v j = u j)
    (hstep : ∀ i : Fin L, left ≤ i.val → v i.succ =
      match N.val i with
      | Sum.inl (A, b) => fun j => (∑ t, A j t * v i.castSucc t) + b j
      | Sum.inr h => fun j => σ (v i.castSucc (Fin.cast h.down.symm j)))
    (k : ℕ) : v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k := by
  induction k with
  | zero =>
    change v 0 ∈ X
    rw [hagree 0 (by simp)]
    exact hu 0
  | succ k ih =>
    by_cases hearly : k + r ≤ right
    · apply relaxation_prefix_replacement σ L w N X r hr hL (k + 1) u v (hu (k + 1))
      intro j hj
      exact hagree j (by omega)
    · change v ∈ _ ∩ _
      refine ⟨ih, subset_convexHull ℝ _ ⟨⟨v, ih, fun _ _ => rfl⟩, ?_⟩⟩
      intro i hi _
      exact hstep i (by omega)

lemma scalar_extrema_of_subset {S T : Set ℝ} (hS : S.Nonempty)
    (hsub : S ⊆ T) (hbelow : BddBelow T) (habove : BddAbove T) :
    sInf T ≤ sInf S ∧ sSup S ≤ sSup T := by
  exact ⟨csInf_le_csInf hbelow hS hsub, csSup_le_csSup habove hS hsub⟩

lemma continuous_layer (σ : ℝ → ℝ) (hσ : Continuous σ)
    (a b : ℕ) (layer : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a = b)) :
    Continuous (fun x : Fin a → ℝ => match layer with
      | Sum.inl (A, c) => fun j => (∑ t, A j t * x t) + c j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))) := by
  rcases layer with ⟨A, c⟩ | h
  · dsimp only
    fun_prop
  · dsimp only
    fun_prop

lemma compact_convex_enclosure {a b : ℕ} (S : Set (Fin a → ℝ))
    (hS : IsCompact S) (f : (Fin a → ℝ) → (Fin b → ℝ)) (hf : Continuous f) :
    ∃ K : Set (Fin b → ℝ), IsCompact K ∧ Convex ℝ K ∧ f '' S ⊆ K := by
  obtain ⟨R, hR⟩ := (hS.image hf).isBounded.subset_closedBall 0
  exact ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, convex_closedBall _ _, hR⟩

lemma compact_convex_envelopes (L : ℕ) (w : Fin (L + 1) → ℕ)
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (hc : ∀ i, Continuous (step i)) (X : Set (Fin (w 0) → ℝ))
    (hX : IsCompact X) (hconv : Convex ℝ X) :
    ∃ K : (j : Fin (L + 1)) → Set (Fin (w j) → ℝ),
      K 0 = X ∧ (∀ j, IsCompact (K j) ∧ Convex ℝ (K j)) ∧
      ∀ i, step i '' K i.castSucc ⊆ K i.succ := by
  classical
  let grow (i : Fin L)
      (S : {S : Set (Fin (w i.castSucc) → ℝ) // IsCompact S ∧ Convex ℝ S}) :
      {K : Set (Fin (w i.succ) → ℝ) // IsCompact K ∧ Convex ℝ K} :=
    ⟨(compact_convex_enclosure S.val S.property.1 (step i) (hc i)).choose,
      (compact_convex_enclosure S.val S.property.1 (step i) (hc i)).choose_spec.1,
      (compact_convex_enclosure S.val S.property.1 (step i) (hc i)).choose_spec.2.1⟩
  let K : (j : Fin (L + 1)) →
      {S : Set (Fin (w j) → ℝ) // IsCompact S ∧ Convex ℝ S} :=
    Fin.induction ⟨X, hX, hconv⟩ grow
  refine ⟨fun j => (K j).val, rfl, fun j => (K j).property, ?_⟩
  intro i
  exact (compact_convex_enclosure (K i.castSucc).val (K i.castSucc).property.1
    (step i) (hc i)).choose_spec.2.2

lemma window_in_envelope (L : ℕ) (w : Fin (L + 1) → ℕ)
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (K : (j : Fin (L + 1)) → Set (Fin (w j) → ℝ))
    (hstepK : ∀ i, step i '' K i.castSucc ⊆ K i.succ)
    (C : Set ((j : Fin (L + 1)) → Fin (w j) → ℝ)) (s r : ℕ)
    (hC : ∀ u ∈ C, ∀ j : Fin (L + 1), j.val = s → u j ∈ K j)
    (v : (j : Fin (L + 1)) → Fin (w j) → ℝ)
    (hv : (∃ u ∈ C, ∀ j : Fin (L + 1), j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s + r → v i.succ = step i (v i.castSucc)) :
    ∀ j : Fin (L + 1), s ≤ j.val → j.val ≤ s + r → v j ∈ K j := by
  have hbase : ∀ j : Fin (L + 1), j.val = s → v j ∈ K j := by
    intro j hj
    obtain ⟨u, hu, heq⟩ := hv.1
    rw [heq j hj]
    exact hC u hu j hj
  intro j
  induction j using Fin.induction with
  | zero =>
    intro hs _
    exact hbase 0 (by simp at hs ⊢; omega)
  | succ i ih =>
    intro hs hj
    by_cases heq : i.succ.val = s
    · exact hbase _ heq
    · have hs' : s ≤ i.val := by simp only [Fin.val_succ] at hs heq; omega
      have hi' : i.val < s + r := by simp only [Fin.val_succ] at hj; omega
      rw [hv.2 i hs' hi']
      apply hstepK i
      exact ⟨v i.castSucc, ih hs' (by simpa using hi'.le), rfl⟩

lemma relaxation_stage_envelope (σ : ℝ → ℝ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L)
    (K : (j : Fin (L + 1)) → Set (Fin (w j) → ℝ))
    (hX : X ⊆ K 0) (hconv : ∀ j, Convex ℝ (K j))
    (hstepK : ∀ i : Fin L, (fun x => match N.val i with
      | Sum.inl (A, b) => fun j => (∑ t, A j t * x t) + b j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))) ''
        K i.castSucc ⊆ K i.succ) (k : ℕ) :
    ∀ v ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k,
      ∀ j : Fin (L + 1), j.val = 0 ∨ (0 < k ∧ j.val < k + r) → v j ∈ K j := by
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ) :=
    fun i x => match N.val i with
      | Sum.inl (A, b) => fun j => (∑ t, A j t * x t) + b j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  induction k with
  | zero =>
    intro v hv j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    exact hX hv
  | succ k ih =>
    intro v hv j hj
    change v ∈ _ ∩ _ at hv
    by_cases hearly : j.val = 0 ∨ (0 < k ∧ j.val < k + r)
    · exact ih v hv.1 j hearly
    · have hstart : k ≤ j.val := by omega
      have hend : j.val ≤ k + r := by omega
      have hC : ∀ u ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k,
          ∀ t : Fin (L + 1), t.val = k → u t ∈ K t := by
        intro u hu t ht
        apply ih u hu t
        omega
      have hsubset :
          {v : (t : Fin (L + 1)) → Fin (w t) → ℝ | (∃ u ∈ relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) k,
            ∀ t : Fin (L + 1), t.val = k → v t = u t) ∧
            ∀ i : Fin L, k ≤ i.val → i.val < k + r →
              v i.succ = step i (v i.castSucc)} ⊆ {v | v j ∈ K j} := by
        intro u hu
        exact window_in_envelope L w step K hstepK _ k r hC u hu j hstart hend
      have hc : Convex ℝ {v : (t : Fin (L + 1)) → Fin (w t) → ℝ | v j ∈ K j} := by
        intro a ha b hb c d hc hd hcd
        exact hconv j ha hb hc hd hcd
      exact convexHull_min hsubset hc hv.2

lemma relaxation_output_bounded (σ : ℝ → ℝ) (hσ : Continuous σ) (L : ℕ)
    (w : Fin (L + 1) → ℕ) (N : Definition.NetworkSemantics σ L w)
    (X : Set (Fin (w 0) → ℝ)) (hX : IsCompact X) (hconv : Convex ℝ X)
    (r : ℕ) (hr : 1 ≤ r) (hL : r ≤ L) (j : Fin (w (Fin.last L))) :
    let S := (fun v : (t : Fin (L + 1)) → Fin (w t) → ℝ => v (Fin.last L) j) ''
      relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) (L - r + 1)
    BddBelow S ∧ BddAbove S := by
  let step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ) :=
    fun i x => match N.val i with
      | Sum.inl (A, b) => fun j => (∑ t, A j t * x t) + b j
      | Sum.inr h => fun j => σ (x (Fin.cast h.down.symm j))
  obtain ⟨K, hzero, hK, hstepK⟩ := compact_convex_envelopes L w step
    (by
      intro i
      dsimp only [step]
      cases heq : N.val i with
      | inl p =>
        rcases p with ⟨A, b⟩
        dsimp only
        fun_prop
      | inr h =>
        dsimp only
        fun_prop) X hX hconv
  have hsub :
      (fun v : (t : Fin (L + 1)) → Fin (w t) → ℝ => v (Fin.last L) j) ''
        relaxation.stages(Definition.WindowRelaxation σ L w N X r hr hL) (L - r + 1) ⊆
      (fun x : Fin (w (Fin.last L)) → ℝ => x j) '' K (Fin.last L) := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v (Fin.last L), ?_, rfl⟩
    apply relaxation_stage_envelope σ L w N X r hr hL K
      (by rw [hzero]) (fun t => (hK t).2) hstepK (L - r + 1) v hv (Fin.last L)
    right
    simp only [Fin.val_last]
    omega
  have hc := (hK (Fin.last L)).1.image (continuous_apply j)
  exact ⟨hc.bddBelow.mono hsub, hc.bddAbove.mono hsub⟩

lemma transported_layer_action (σ : ℝ → ℝ) {a b c d : ℕ}
    (ha : c = a) (hb : d = b)
    (layer : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a = b))
    (x : Fin c → ℝ) (j : Fin d) :
    Sum.elim (fun p => (∑ t, p.1 j t * x t) + p.2 j)
      (fun h => σ (x (Fin.cast h.down.symm j)))
      (cast (by rw [ha, hb]) layer :
        (Matrix (Fin d) (Fin c) ℝ × (Fin d → ℝ)) ⊕ PLift (c = d)) =
    Sum.elim (fun p => (∑ t, p.1 (Fin.cast hb j) t * x (Fin.cast ha.symm t)) +
      p.2 (Fin.cast hb j))
      (fun h => σ (x (Fin.cast ha.symm (Fin.cast h.down.symm (Fin.cast hb j))))) layer := by
  subst c
  subst d
  rfl

lemma trajectory_unique (L : ℕ) (w : Fin (L + 1) → ℕ)
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (v : (j : Fin (L + 1)) → Fin (w j) → ℝ)
    (x : Fin (w 0) → ℝ) (hzero : v 0 = x)
    (hstep : ∀ i, v i.succ = step i (v i.castSucc)) :
    ∀ j, Fin.induction x (fun i prev => step i prev) j = v j := by
  intro j
  induction j using Fin.induction with
  | zero => exact hzero.symm
  | succ i ih => simpa only [Fin.induction_succ, ih] using (hstep i).symm

lemma coordinate_cast_congr {ι : Type*} (w : ι → ℕ)
    (v : (j : ι) → Fin (w j) → ℝ) {i j : ι} (h : i = j)
    {e : ℕ} (hi : w i = e) (hj : w j = e) (k : Fin e) :
    v i (Fin.cast hi.symm k) = v j (Fin.cast hj.symm k) := by
  subst j
  rfl

-- formalizer:machinery-end

end Lemma_4p1.Machinery
