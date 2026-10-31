module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p1
public import Formalization.Result.Lemma_Gp1
public import Mathlib

public section

namespace Proposition_5p6.Machinery

-- formalizer:machinery-begin

/-- Once a preactivation has a fixed sign, restricting the region preserves it. -/
theorem stable_on_subset {T I : Type*} (z : I → T → ℝ)
    {R S : Set T} (hSR : S ⊆ R) (i : I)
    (h : (∀ v ∈ R, 0 ≤ z i v) ∨ (∀ v ∈ R, z i v ≤ 0)) :
    (∀ v ∈ S, 0 ≤ z i v) ∨ (∀ v ∈ S, z i v ≤ 0) := by
  rcases h with h | h
  · exact Or.inl (fun v hv => h v (hSR hv))
  · exact Or.inr (fun v hv => h v (hSR hv))

/-- Genuine instability gives a witness in each child, even with boundary overlap. -/
theorem unstable_children_nonempty {T I : Type*} (z : I → T → ℝ)
    (R : Set T) (i : I)
    (h : ¬ ((∀ v ∈ R, 0 ≤ z i v) ∨ (∀ v ∈ R, z i v ≤ 0))) :
    {v ∈ R | z i v ≤ 0}.Nonempty ∧ {v ∈ R | 0 ≤ z i v}.Nonempty := by
  classical
  have hn : ¬ ∀ v ∈ R, 0 ≤ z i v := fun hn => h (Or.inl hn)
  have hp : ¬ ∀ v ∈ R, z i v ≤ 0 := fun hp => h (Or.inr hp)
  push Not at hn hp
  obtain ⟨v, hv, hzv⟩ := hn
  obtain ⟨u, hu, hzu⟩ := hp
  exact ⟨⟨v, hv, le_of_lt hzv⟩, ⟨u, hu, le_of_lt hzu⟩⟩

/-- A split removes its label from the finite set of unstable preactivations.
Previously fixed signs cannot become unstable in either child. -/
theorem unstable_count_decreases {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (R : Set T) (i : I)
    (h : ¬ ((∀ v ∈ R, 0 ≤ z i v) ∨ (∀ v ∈ R, z i v ≤ 0))) :
    let unstable : Set T → Finset I := fun S => by
      classical
      exact Finset.univ.filter
        (fun n => ¬ ((∀ v ∈ S, 0 ≤ z n v) ∨ (∀ v ∈ S, z n v ≤ 0)))
    (unstable {v ∈ R | z i v ≤ 0}).card < (unstable R).card ∧
    (unstable {v ∈ R | 0 ≤ z i v}).card < (unstable R).card := by
  classical
  intro unstable
  have decrease : ∀ S : Set T, S ⊆ R →
      ((∀ v ∈ S, 0 ≤ z i v) ∨ (∀ v ∈ S, z i v ≤ 0)) →
      (unstable S).card < (unstable R).card := by
    intro S hSR hi
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro n hn
      simp only [unstable, Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
      exact fun hstable => hn (stable_on_subset z hSR n hstable)
    · intro heq
      have hmem : i ∈ unstable R := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [← heq] at hmem
      exact (Finset.mem_filter.mp hmem).2 hi
  exact ⟨decrease _ (fun _ hv => hv.1) (Or.inr (fun _ hv => hv.2)),
    decrease _ (fun _ hv => hv.1) (Or.inl (fun _ hv => hv.2))⟩

/-- Induction following the paper's split-until-stable construction. -/
theorem sign_split_induction {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (P : Set T → Prop)
    (terminal : ∀ R, (∀ i, (∀ v ∈ R, 0 ≤ z i v) ∨
      (∀ v ∈ R, z i v ≤ 0)) → P R)
    (split : ∀ R i, ¬ ((∀ v ∈ R, 0 ≤ z i v) ∨
      (∀ v ∈ R, z i v ≤ 0)) →
      P {v ∈ R | z i v ≤ 0} → P {v ∈ R | 0 ≤ z i v} → P R) :
    ∀ R, P R := by
  classical
  let unstable := fun S : Set T => Finset.univ.filter
    (fun n => ¬ ((∀ v ∈ S, 0 ≤ z n v) ∨ (∀ v ∈ S, z n v ≤ 0)))
  have aux : ∀ k R, (unstable R).card = k → P R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hcard
      by_cases hs : ∀ i, (∀ v ∈ R, 0 ≤ z i v) ∨ (∀ v ∈ R, z i v ≤ 0)
      · exact terminal R hs
      · obtain ⟨i, hi⟩ := not_forall.mp hs
        have hd := unstable_count_decreases z R i hi
        apply split R i hi
        · apply ih (unstable {v ∈ R | z i v ≤ 0}).card
            (by simpa only [← hcard] using hd.1) _ rfl
        · apply ih (unstable {v ∈ R | 0 ≤ z i v}).card
            (by simpa only [← hcard] using hd.2) _ rfl
  intro R
  exact aux _ R rfl

/-- Every region admits a finite execution ending with all signs stable.
The witnesses use exactly the address/label/region representation of BaB. -/
theorem stable_tree_exists {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (R : Set T) :
    let stable := fun S i => (∀ v ∈ S, 0 ≤ z i v) ∨ (∀ v ∈ S, z i v ≤ 0)
    ∃ (nodes : Finset (List Bool)) (labels : List Bool → Option I)
      (regions : List Bool → Set T),
      [] ∈ nodes ∧ regions [] = R ∧
      (∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) ∧
      (∀ a ∈ nodes,
        ((∀ i, stable (regions a) i) ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
        ((¬ ∀ i, stable (regions a) i) ∧ ∃ i, labels a = some i ∧
          ¬ stable (regions a) i ∧ a ++ [false] ∈ nodes ∧ a ++ [true] ∈ nodes ∧
          regions (a ++ [false]) = {v ∈ regions a | z i v ≤ 0} ∧
          regions (a ++ [true]) = {v ∈ regions a | 0 ≤ z i v})) := by
  classical
  intro stable
  induction R using sign_split_induction z with
  | terminal R hs =>
    refine ⟨{[]}, fun _ => none, fun _ => R, by simp, rfl, ?_, ?_⟩
    · intro a ha p hp
      have ha' : a = [] := by simpa using ha
      subst a
      have : p = [] := List.prefix_nil.mp hp
      simp [this]
    · intro a ha
      have ha' : a = [] := by simpa using ha
      subst a
      exact Or.inl ⟨hs, by simp, by simp⟩
  | split R i hi ih₀ ih₁ =>
    obtain ⟨n₀, l₀, r₀, hn₀, hr₀, hp₀, hv₀⟩ := ih₀
    obtain ⟨n₁, l₁, r₁, hn₁, hr₁, hp₁, hv₁⟩ := ih₁
    let nodes := insert []
      ((n₀.image (List.cons false)) ∪ (n₁.image (List.cons true)))
    let labels : List Bool → Option I := fun a => match a with
      | [] => some i
      | false :: b => l₀ b
      | true :: b => l₁ b
    let regions : List Bool → Set T := fun a => match a with
      | [] => R
      | false :: b => r₀ b
      | true :: b => r₁ b
    have mem₀ : ∀ a, false :: a ∈ nodes ↔ a ∈ n₀ := by
      intro a
      simp [nodes]
    have mem₁ : ∀ a, true :: a ∈ nodes ↔ a ∈ n₁ := by
      intro a
      simp [nodes]
    refine ⟨nodes, labels, regions, by simp [nodes], rfl, ?_, ?_⟩
    · intro a ha p hp
      cases p with
      | nil => simp [nodes]
      | cons b p =>
        cases a with
        | nil => exact False.elim (by simpa using hp)
        | cons c a =>
          obtain ⟨hbc, hpa⟩ := List.cons_prefix_cons.mp hp
          subst c
          cases b with
          | false => exact (mem₀ p).mpr (hp₀ a ((mem₀ a).mp ha) p hpa)
          | true => exact (mem₁ p).mpr (hp₁ a ((mem₁ a).mp ha) p hpa)
    · intro a ha
      cases a with
      | nil =>
        refine Or.inr ⟨?_, i, rfl, hi, ?_, ?_, hr₀, hr₁⟩
        · exact fun hs => hi (hs i)
        · exact (mem₀ []).mpr hn₀
        · exact (mem₁ []).mpr hn₁
      | cons b a =>
        cases b with
        | false =>
          have hv := hv₀ a ((mem₀ a).mp ha)
          simpa only [List.cons_append, regions, labels, mem₀] using hv
        | true =>
          have hv := hv₁ a ((mem₁ a).mp ha)
          simpa only [List.cons_append, regions, labels, mem₁] using hv

/-- A sign fixed at a split remains fixed below it, so the number of unstable
labels plus the address length cannot increase along a branch. -/
theorem tree_depth_bound {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (nodes : Finset (List Bool))
    (regions : List Bool → Set T)
    (hprefix : ∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes)
    (split : ∀ a ∈ nodes, ∀ b, a ++ [b] ∈ nodes → ∃ i,
      ¬ ((∀ v ∈ regions a, 0 ≤ z i v) ∨ (∀ v ∈ regions a, z i v ≤ 0)) ∧
      regions (a ++ [b]) ⊆ regions a ∧
      ((∀ v ∈ regions (a ++ [b]), 0 ≤ z i v) ∨
        (∀ v ∈ regions (a ++ [b]), z i v ≤ 0))) :
    ∀ a ∈ nodes, a.length ≤ Fintype.card I := by
  classical
  let unstable := fun S : Set T => Finset.univ.filter
    (fun n => ¬ ((∀ v ∈ S, 0 ≤ z n v) ∨ (∀ v ∈ S, z n v ≤ 0)))
  have step : ∀ a ∈ nodes, ∀ b, a ++ [b] ∈ nodes →
      (unstable (regions (a ++ [b]))).card < (unstable (regions a)).card := by
    intro a ha b hab
    obtain ⟨i, hi, hsub, hstable⟩ := split a ha b hab
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro n hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h =>
        (Finset.mem_filter.mp hn).2 (stable_on_subset z hsub n h)⟩
    · intro heq
      have hm : i ∈ unstable (regions a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [← heq] at hm
      exact (Finset.mem_filter.mp hm).2 hstable
  have quantitative : ∀ a ∈ nodes,
      (unstable (regions a)).card + a.length ≤ (unstable (regions [])).card := by
    intro a
    induction a using List.reverseRecOn with
    | nil => simp
    | append_singleton a b ih =>
      intro hab
      have ha := hprefix (a ++ [b]) hab a ⟨[b], rfl⟩
      have hprev := ih ha
      have hnext := step a ha b hab
      simp only [List.length_append, List.length_singleton]
      omega
  intro a ha
  have hq := quantitative a ha
  have hc : (unstable (regions [])).card ≤ Fintype.card I :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- There are finitely many Boolean addresses up to a fixed depth. -/
theorem bounded_addresses_finite (k : ℕ) :
    {a : List Bool | a.length ≤ k}.Finite := by
  induction k with
  | zero =>
    have heq : {a : List Bool | a.length ≤ 0} = {[]} := by ext a; simp
    rw [heq]
    exact Set.finite_singleton _
  | succ k ih =>
    apply Set.Finite.subset
      ((Set.finite_singleton ([] : List Bool)).union
        ((ih.image (List.cons false)).union (ih.image (List.cons true))))
    intro a ha
    cases a with
    | nil => exact Or.inl rfl
    | cons b a =>
      have hlen : a.length ≤ k := by simpa using ha
      cases b with
      | false => exact Or.inr (Or.inl ⟨a, hlen, rfl⟩)
      | true => exact Or.inr (Or.inr ⟨a, hlen, rfl⟩)

/-- A prefix-closed address tree whose root has no children is a singleton. -/
theorem terminal_root_nodes (nodes : Finset (List Bool))
    (hroot : [] ∈ nodes)
    (hp : ∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes)
    (hfalse : [false] ∉ nodes) (htrue : [true] ∉ nodes) :
    nodes = {[]} := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    cases a with
    | nil => simp
    | cons b a =>
      have hb := hp (b :: a) ha [b] ⟨a, rfl⟩
      cases b
      · exact False.elim (hfalse hb)
      · exact False.elim (htrue hb)
  · intro ha
    have heq := Finset.mem_singleton.mp ha
    simpa only [heq] using hroot

/-- Finite strict descent allows the next unstable label to be prescribed. -/
theorem sign_split_strong_induction {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (P : Set T → Prop)
    (step : ∀ R,
      (∀ i, ¬ ((∀ v ∈ R, 0 ≤ z i v) ∨ (∀ v ∈ R, z i v ≤ 0)) →
        P {v ∈ R | z i v ≤ 0} ∧ P {v ∈ R | 0 ≤ z i v}) → P R) :
    ∀ R, P R := by
  classical
  let unstable := fun S : Set T => Finset.univ.filter
    (fun n => ¬ ((∀ v ∈ S, 0 ≤ z n v) ∨ (∀ v ∈ S, z n v ≤ 0)))
  have aux : ∀ k R, (unstable R).card = k → P R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hk
      apply step R
      intro i hi
      have hd := unstable_count_decreases z R i hi
      exact ⟨ih _ (by simpa only [← hk] using hd.1) _ rfl,
        ih _ (by simpa only [← hk] using hd.2) _ rfl⟩
  intro R
  exact aux _ R rfl

/-- Reproduce every prescribed unstable split, and complete each old leaf.
The larger finite tree retains every address of the original execution. -/
theorem stable_tree_refinement {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (closed : Set T → Prop) :
    let stable := fun S i => (∀ v ∈ S, 0 ≤ z i v) ∨ (∀ v ∈ S, z i v ≤ 0)
    let valid := fun (stop : Set T → Prop) (nodes : Finset (List Bool))
      (labels : List Bool → Option I) (regions : List Bool → Set T) =>
      [] ∈ nodes ∧ (∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) ∧
      (∀ a ∈ nodes,
        (stop (regions a) ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
        (¬ stop (regions a) ∧ ∃ i, labels a = some i ∧
          ¬ stable (regions a) i ∧ a ++ [false] ∈ nodes ∧ a ++ [true] ∈ nodes ∧
          regions (a ++ [false]) = {v ∈ regions a | z i v ≤ 0} ∧
          regions (a ++ [true]) = {v ∈ regions a | 0 ≤ z i v}))
    ∀ nodes labels regions, valid closed nodes labels regions →
      ∃ nodes' labels' regions', nodes ⊆ nodes' ∧ regions' [] = regions [] ∧
        valid (fun S => ∀ i, stable S i) nodes' labels' regions' := by
  classical
  intro stable valid
  have aux : ∀ R, ∀ nodes labels regions, regions [] = R →
      valid closed nodes labels regions →
      ∃ nodes' labels' regions', nodes ⊆ nodes' ∧ regions' [] = R ∧
        valid (fun S => ∀ i, stable S i) nodes' labels' regions' := by
    apply sign_split_strong_induction z
    intro R ih nodes labels regions hr hv
    obtain ⟨hroot, hp, hv⟩ := hv
    rcases hv [] hroot with hstop | hsplit
    · have hn := terminal_root_nodes nodes hroot hp hstop.2.1 hstop.2.2
      obtain ⟨n, l, r, hnroot, hrroot, hnp, hnv⟩ := stable_tree_exists z R
      refine ⟨n, l, r, ?_, hrroot, hnroot, hnp, hnv⟩
      rw [hn]
      exact Finset.singleton_subset_iff.mpr hnroot
    · obtain ⟨_, i, hlabel, hi, hfalse, htrue, hrfalse, hrtrue⟩ := hsplit
      have hiR : ¬ stable R i := by simpa only [hr] using hi
      obtain ⟨ih₀, ih₁⟩ := ih i hiR
      let child := fun b => nodes.preimage (List.cons b) (by
        intro a _ c _ h; exact List.cons.inj h |>.2)
      have child_mem : ∀ b a, a ∈ child b ↔ b :: a ∈ nodes := by
        intros; simp [child]
      have child_valid : ∀ b, valid closed (child b)
          (fun a => labels (b :: a)) (fun a => regions (b :: a)) := by
        intro b
        refine ⟨?_, ?_, ?_⟩
        · apply (child_mem b []).mpr
          cases b
          · exact hfalse
          · exact htrue
        · intro a ha p hpa
          apply (child_mem b p).mpr
          exact hp (b :: a) ((child_mem b a).mp ha) (b :: p)
            (List.cons_prefix_cons.mpr ⟨rfl, hpa⟩)
        · intro a ha
          have h := hv (b :: a) ((child_mem b a).mp ha)
          simpa only [List.cons_append, child_mem] using h
      have hr₀ : regions [false] = {v ∈ R | z i v ≤ 0} := by
        simpa only [List.nil_append, hr] using hrfalse
      have hr₁ : regions [true] = {v ∈ R | 0 ≤ z i v} := by
        simpa only [List.nil_append, hr] using hrtrue
      obtain ⟨n₀, l₀, r₀, hn₀, hr₀, hv₀⟩ :=
        ih₀ _ _ _ hr₀ (child_valid false)
      obtain ⟨n₁, l₁, r₁, hn₁, hr₁, hv₁⟩ :=
        ih₁ _ _ _ hr₁ (child_valid true)
      let n := insert [] ((n₀.image (List.cons false)) ∪ (n₁.image (List.cons true)))
      let l : List Bool → Option I := fun a => match a with
        | [] => some i
        | false :: a => l₀ a
        | true :: a => l₁ a
      let r : List Bool → Set T := fun a => match a with
        | [] => R
        | false :: a => r₀ a
        | true :: a => r₁ a
      have mem₀ : ∀ a, false :: a ∈ n ↔ a ∈ n₀ := by intro a; simp [n]
      have mem₁ : ∀ a, true :: a ∈ n ↔ a ∈ n₁ := by intro a; simp [n]
      refine ⟨n, l, r, ?_, rfl, by simp [n], ?_, ?_⟩
      · intro a ha
        cases a with
        | nil => simp [n]
        | cons b a =>
          cases b with
          | false => exact (mem₀ a).mpr (hn₀ ((child_mem false a).mpr ha))
          | true => exact (mem₁ a).mpr (hn₁ ((child_mem true a).mpr ha))
      · intro a ha p hpa
        cases p with
        | nil => simp [n]
        | cons b p =>
          cases a with
          | nil => exact False.elim (by simpa using hpa)
          | cons c a =>
            obtain ⟨hbc, htail⟩ := List.cons_prefix_cons.mp hpa
            subst c
            cases b with
            | false => exact (mem₀ p).mpr (hv₀.2.1 a ((mem₀ a).mp ha) p htail)
            | true => exact (mem₁ p).mpr (hv₁.2.1 a ((mem₁ a).mp ha) p htail)
      · intro a ha
        cases a with
        | nil =>
          exact Or.inr ⟨fun hs => hiR (hs i), i, rfl, hiR,
            (mem₀ []).mpr hv₀.1, (mem₁ []).mpr hv₁.1, hr₀, hr₁⟩
        | cons b a =>
          cases b with
          | false =>
            have h := hv₀.2.2 a ((mem₀ a).mp ha)
            simpa only [List.cons_append, r, l, mem₀] using h
          | true =>
            have h := hv₁.2.2 a ((mem₁ a).mp ha)
            simpa only [List.cons_append, r, l, mem₁] using h
  intro nodes labels regions hv
  exact aux (regions []) nodes labels regions rfl hv

/-- Every node in a finite address tree has a terminal descendant. -/
theorem terminal_descendant (nodes : Finset (List Bool)) (a : List Bool)
    (ha : a ∈ nodes) : ∃ b ∈ nodes, a <+: b ∧
      b ++ [false] ∉ nodes ∧ b ++ [true] ∉ nodes := by
  classical
  let descendants := nodes.filter (fun b => a <+: b)
  have hne : descendants.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, List.prefix_rfl⟩⟩
  obtain ⟨b, hb, hmax⟩ := descendants.exists_max_image List.length hne
  obtain ⟨hbnode, hab⟩ := Finset.mem_filter.mp hb
  have hterminal : ∀ c : Bool, b ++ [c] ∉ nodes := by
    intro c hc
    have hmem : b ++ [c] ∈ descendants :=
      Finset.mem_filter.mpr ⟨hc, hab.trans ⟨[c], rfl⟩⟩
    have hlen := hmax _ hmem
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  exact ⟨b, hbnode, hab, hterminal false, hterminal true⟩

/-- Extending a prefix-closed tree cannot decrease its terminal-node count.
Different original terminal nodes have disjoint sets of descendants. -/
theorem terminal_count_mono (nodes nodes' : Finset (List Bool))
    (hsub : nodes ⊆ nodes')
    (hp : ∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) :
    (nodes.filter (fun a => a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes)).card ≤
    (nodes'.filter (fun a => a ++ [false] ∉ nodes' ∧ a ++ [true] ∉ nodes')).card := by
  classical
  let leaves := nodes.filter (fun a => a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes)
  let leaves' := nodes'.filter (fun a => a ++ [false] ∉ nodes' ∧ a ++ [true] ∉ nodes')
  have descendant : ∀ a ∈ leaves, ∃ b ∈ leaves', a <+: b := by
    intro a ha
    obtain ⟨b, hb, hab, hf, ht⟩ := terminal_descendant nodes' a
      (hsub (Finset.mem_filter.mp ha).1)
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hf, ht⟩, hab⟩
  have leaf_prefix : ∀ a ∈ leaves, ∀ b ∈ nodes, a <+: b → a = b := by
    intro a ha b hb hab
    obtain ⟨tail, rfl⟩ := hab
    cases tail with
    | nil => simp
    | cons c tail =>
      have hc : a ++ [c] ∈ nodes := hp _ hb _ ⟨tail, by simp⟩
      obtain ⟨_, hf, ht⟩ := Finset.mem_filter.mp ha
      cases c
      · exact False.elim (hf hc)
      · exact False.elim (ht hc)
  choose f hf hprefix using descendant
  let g : List Bool → List Bool := fun a => if ha : a ∈ leaves then f a ha else []
  change leaves.card ≤ leaves'.card
  apply Finset.card_le_card_of_injOn g
  · intro a ha
    change a ∈ leaves at ha
    simpa only [g, dif_pos ha] using hf a ha
  · intro a ha b hb heq
    change a ∈ leaves at ha
    change b ∈ leaves at hb
    have hpa : a <+: g a := by simpa only [g, dif_pos ha] using hprefix a ha
    have hpb : b <+: g a := by simpa only [heq, g, dif_pos hb] using hprefix b hb
    rcases List.prefix_or_prefix_of_prefix hpa hpb with hab | hba
    · exact leaf_prefix a ha b (Finset.mem_filter.mp hb).1 hab
    · exact (leaf_prefix b hb a (Finset.mem_filter.mp ha).1 hba).symm

/-- For an admissible execution, closed nodes are exactly terminal addresses. -/
theorem closed_filter_eq_leaves (nodes : Finset (List Bool)) (stop : List Bool → Prop)
    [DecidablePred stop]
    (rule : ∀ a ∈ nodes,
      (stop a ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
      (¬ stop a ∧ a ++ [false] ∈ nodes)) :
    nodes.filter stop = nodes.filter
      (fun a => a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, hs⟩
    rcases rule a ha with h | h
    · exact ⟨ha, h.2⟩
    · exact False.elim (h.1 hs)
  · rintro ⟨ha, hf, ht⟩
    rcases rule a ha with h | h
    · exact ⟨ha, h.1⟩
    · exact False.elim (hf h.2)

/-- An extreme point of finitely many affine inequalities is determined by
which inequalities are active. This supplies finite vertices for stable cells. -/
theorem extreme_eq_of_active {E I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] (f : I → E →ᵃ[ℝ] ℝ) (x y : E)
    (hx : x ∈ {v | ∀ i, f i v ≤ 0}.extremePoints ℝ)
    (hy : ∀ i, f i y ≤ 0)
    (hactive : ∀ i, f i x = 0 ↔ f i y = 0) : x = y := by
  classical
  let d := y - x
  have hlin : ∀ i, (f i).linear d = f i y - f i x := by
    intro i
    exact (f i).linearMap_vsub y x
  have hev : ∀ i, ∀ᶠ t : ℝ in nhds 0,
      f i (t • d + x) ≤ 0 ∧ f i ((-t) • d + x) ≤ 0 := by
    intro i
    have eqn : ∀ t : ℝ, f i (t • d + x) = t * (f i).linear d + f i x := by
      intro t
      simpa using (f i).map_vadd x (t • d)
    by_cases hi : f i x = 0
    · have hd : (f i).linear d = 0 := by rw [hlin, hi, (hactive i).mp hi]; ring
      exact Filter.Eventually.of_forall (fun t => by rw [eqn, eqn, hi, hd]; simp)
    · have hneg : f i x < 0 := lt_of_le_of_ne (hx.1 i) hi
      have hc₁ : Continuous (fun t : ℝ => t * (f i).linear d + f i x) := by fun_prop
      have hc₂ : Continuous (fun t : ℝ => -t * (f i).linear d + f i x) := by fun_prop
      have h₁ := (hc₁.continuousAt (x := 0)).eventually_lt_const (by simpa using hneg)
      have h₂ := (hc₂.continuousAt (x := 0)).eventually_lt_const (by simpa using hneg)
      filter_upwards [h₁, h₂] with t ht₁ ht₂
      exact ⟨by rw [eqn]; exact ht₁.le, by rw [eqn]; exact ht₂.le⟩
  have hall : ∀ᶠ t : ℝ in nhds 0, ∀ i,
      f i (t • d + x) ≤ 0 ∧ f i ((-t) • d + x) ≤ 0 :=
    Filter.eventually_all.mpr hev
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hall
  have ht := he (y := ε / 2) (by simpa [Real.dist_eq, abs_of_pos hε] using half_lt_self hε)
  have heq := hx.2 (fun i => (ht i).1) (fun i => (ht i).2)
    (by simpa only [neg_smul, sub_eq_add_neg, add_comm] using
      (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • d)))
  have hz : (ε / 2) • d = 0 := add_right_cancel (heq.trans (zero_add x).symm)
  have hd : d = 0 := (smul_eq_zero.mp hz).resolve_left (ne_of_gt (half_pos hε))
  exact (sub_eq_zero.mp hd).symm

/-- A compact intersection of finitely many affine halfspaces has finitely
many vertices. The active constraints distinguish its extreme points. -/
theorem compact_affine_halfspaces_polytope {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype I] (f : I → E →ᵃ[ℝ] ℝ)
    (hc : IsCompact {v | ∀ i, f i v ≤ 0}) :
    ∃ V : Finset E, {v | ∀ i, f i v ≤ 0} = convexHull ℝ (↑V : Set E) := by
  classical
  let S : Set E := {v | ∀ i, f i v ≤ 0}
  let active : S.extremePoints ℝ → Finset I := fun x =>
    Finset.univ.filter (fun i => f i x.val = 0)
  have hinj : Function.Injective active := by
    intro x y h
    apply Subtype.ext
    apply extreme_eq_of_active f x.val y.val x.property y.property.1
    intro i
    have hi := Finset.ext_iff.mp h i
    simpa [active] using hi
  have hfin : (S.extremePoints ℝ).Finite :=
    by
      letI : Finite (S.extremePoints ℝ) := Finite.of_injective active hinj
      exact Set.toFinite _
  have hconv : Convex ℝ S := by
    have heq : S = ⋂ i, (f i) ⁻¹' Set.Iic 0 := by ext; simp [S]
    rw [heq]
    exact convex_iInter (fun i => (convex_Iic (0 : ℝ)).affine_preimage (f i))
  refine ⟨hfin.toFinset, ?_⟩
  have hkm := closure_convexHull_extremePoints hc hconv
  rw [(hfin.isCompact_convexHull ℝ).isClosed.closure_eq] at hkm
  simpa using hkm.symm

/-- Cutting a finite convex hull by finitely many affine halfspaces retains
finite generation. Coefficients in the standard simplex retain the original hull. -/
theorem polytope_affine_halfspaces {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype I] (V : Finset E) (f : I → E →ᵃ[ℝ] ℝ) :
    ∃ W : Finset E,
      {x ∈ convexHull ℝ (↑V : Set E) | ∀ i, f i x ≤ 0} =
        convexHull ℝ (↑W : Set E) := by
  classical
  letI : Fintype (↑V : Set E) := V.finite_toSet.fintype
  let A : (V → ℝ) →ₗ[ℝ] E := ∑ x : V, (LinearMap.proj x).smulRight x.val
  let total : (V → ℝ) →ᵃ[ℝ] ℝ := (∑ x : V, LinearMap.proj (R := ℝ) x).toAffineMap
  let one : (V → ℝ) →ᵃ[ℝ] ℝ := AffineMap.const ℝ _ 1
  let g : I ⊕ (V ⊕ Bool) → (V → ℝ) →ᵃ[ℝ] ℝ := fun i => match i with
    | Sum.inl i => (f i).comp A.toAffineMap
    | Sum.inr (Sum.inl x) => -(LinearMap.proj x).toAffineMap
    | Sum.inr (Sum.inr false) => total - one
    | Sum.inr (Sum.inr true) => one - total
  have hg : ∀ c, (∀ i, g i c ≤ 0) ↔
      c ∈ stdSimplex ℝ V ∧ ∀ i, f i (A c) ≤ 0 := by
    intro c
    simp only [Sum.forall, Bool.forall_bool, g, AffineMap.comp_apply,
      LinearMap.coe_toAffineMap, AffineMap.coe_neg, Pi.neg_apply, LinearMap.proj_apply,
      AffineMap.coe_sub, Pi.sub_apply, total, one, AffineMap.const_apply,
      LinearMap.coe_toAffineMap, LinearMap.sum_apply, stdSimplex, Set.mem_setOf_eq, LinearMap.proj_apply]
    constructor
    · rintro ⟨h, hn, hl, hu⟩
      exact ⟨⟨fun x => by linarith [hn x], by linarith⟩, h⟩
    · rintro ⟨⟨hn, he⟩, h⟩
      exact ⟨h, (fun x => by linarith [hn x]), by linarith, by linarith⟩
  have hc : IsCompact {c | ∀ i, g i c ≤ 0} := by
    apply (isCompact_stdSimplex ℝ V).of_isClosed_subset
    · have he : {c | ∀ i, g i c ≤ 0} = ⋂ i, {c | g i c ≤ 0} := by ext; simp
      rw [he]
      apply isClosed_iInter
      intro i
      apply isClosed_le _ continuous_const
      exact AffineMap.continuous_linear_iff.mp (g i).linear.continuous_of_finiteDimensional
    · intro c hc
      exact ((hg c).mp hc).1
  obtain ⟨W, hW⟩ := compact_affine_halfspaces_polytope g hc
  refine ⟨W.image A, ?_⟩
  have hHull : convexHull ℝ (↑V : Set E) = A '' stdSimplex ℝ V :=
    by simpa only [A] using (V.finite_toSet.convexHull_eq_image (R := ℝ))
  have he : {x ∈ convexHull ℝ (↑V : Set E) | ∀ i, f i x ≤ 0} =
      A '' {c | ∀ i, g i c ≤ 0} := by
    rw [hHull]
    ext x
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, hf⟩
      exact ⟨c, (hg c).mpr ⟨hc, hf⟩, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, ((hg c).mp hc).1, rfl⟩, ((hg c).mp hc).2⟩
  rw [he, hW, A.image_convexHull]
  simp

/-- On a compatible sign cell, affine layer continuations identify the exact
trajectory region with an affine image of the original polytope cut by all
retained halfspaces. The converse direction keeps the ancestral constraints. -/
theorem affine_trajectory_cell {L : ℕ} {w : Fin (L+1) → ℕ} {I : Type*} [Fintype I]
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (a : (i : Fin L) → (Fin (w i.castSucc) → ℝ) →ᵃ[ℝ] (Fin (w i.succ) → ℝ))
    (V : Finset (Fin (w 0) → ℝ))
    (cuts : I → ((j : Fin (L+1)) → Fin (w j) → ℝ) →ᵃ[ℝ] ℝ)
    (R : Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hR : ∀ v, v ∈ R ↔ v 0 ∈ convexHull ℝ (↑V : Set _) ∧
      (∀ i, v i.succ = step i (v i.castSucc)) ∧ (∀ k, cuts k v ≤ 0))
    (ha : ∀ v, (∀ k, cuts k v ≤ 0) → ∀ i, step i (v i.castSucc) = a i (v i.castSucc)) :
    ∀ j, ∃ W : Finset (Fin (w j) → ℝ),
      (fun v => v j) '' R = convexHull ℝ (↑W : Set _) := by
  classical
  let run : (j : Fin (L+1)) → (Fin (w 0) → ℝ) →ᵃ[ℝ] (Fin (w j) → ℝ) :=
    Fin.induction (AffineMap.id ℝ _) (fun i prev => (a i).comp prev)
  let F := AffineMap.pi run
  have zero : ∀ x, F x 0 = x := fun _ => rfl
  have succ : ∀ i x, F x i.succ = a i (F x i.castSucc) := by
    intro i x
    simp only [F, AffineMap.pi_apply, run, Fin.induction_succ, AffineMap.comp_apply]
  have forward : ∀ v ∈ R, F (v 0) = v := by
    intro v hv
    have hr := (hR v).mp hv
    funext j
    induction j using Fin.induction with
    | zero => exact zero _
    | succ i ih => rw [succ, ih, ← ha v hr.2.2 i, ← hr.2.1 i]
  let D := {x ∈ convexHull ℝ (↑V : Set _) | ∀ k, cuts k (F x) ≤ 0}
  have region : F '' D = R := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (hR _).mpr
      refine ⟨?_, ?_, hx.2⟩
      · simpa only [zero] using hx.1
      · intro i
        rw [succ, ha _ hx.2 i]
    · intro hv
      refine ⟨v 0, ?_, forward v hv⟩
      exact ⟨((hR v).mp hv).1, by rw [forward v hv]; exact ((hR v).mp hv).2.2⟩
  obtain ⟨W, hW⟩ := polytope_affine_halfspaces V (fun k => (cuts k).comp F)
  have hD : D = convexHull ℝ (↑W : Set _) := hW
  intro j
  refine ⟨W.image (run j), ?_⟩
  rw [← region, Set.image_image]
  change (run j) '' D = _
  rw [hD, (run j).image_convexHull]
  simp

/-- Compatible ReLU signs make every layer affine. Adding those signs to the
retained ancestral halfspaces does not change an all-stable branch region. -/
theorem stable_network_cell {L : ℕ} {w : Fin (L+1) → ℕ}
    (N : Definition.NetworkSemantics (fun t => max t 0) L w)
    (step : (i : Fin L) → (Fin (w i.castSucc) → ℝ) → (Fin (w i.succ) → ℝ))
    (hstep : ∀ i x, step i x = match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * x k) + b j
      | Sum.inr h => fun j => max (x (Fin.cast h.down.symm j)) 0)
    (V : Finset (Fin (w 0) → ℝ))
    (H : Finset (((j : Fin (L+1)) → Fin (w j) → ℝ) →ᵃ[ℝ] ℝ))
    (R : Set ((j : Fin (L+1)) → Fin (w j) → ℝ))
    (hR : ∀ v, v ∈ R ↔ v 0 ∈ convexHull ℝ (↑V : Set _) ∧
      (∀ i, v i.succ = step i (v i.castSucc)) ∧ (∀ f ∈ H, f v ≤ 0))
    (hs : ∀ (i : Fin L), (∃ h, N.val i = Sum.inr h) → ∀ k,
      (∀ v ∈ R, 0 ≤ v i.castSucc k) ∨ (∀ v ∈ R, v i.castSucc k ≤ 0)) :
    ∀ j, ∃ W : Finset (Fin (w j) → ℝ),
      (fun v => v j) '' R = convexHull ℝ (↑W : Set _) := by
  classical
  let T := (j : Fin (L+1)) → Fin (w j) → ℝ
  let Label := (i : {i : Fin L // ∃ h, N.val i = Sum.inr h}) × Fin (w i.val.castSucc)
  let pos := fun (i : Fin L) (k : Fin (w i.castSucc)) => ∀ v ∈ R, 0 ≤ v i.castSucc k
  let coord : Label → T →ᵃ[ℝ] ℝ := fun n =>
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin (w n.1.val.castSucc) => ℝ) n.2).comp
      (LinearMap.proj (R := ℝ) (φ := fun j : Fin (L+1) => Fin (w j) → ℝ) n.1.val.castSucc)).toAffineMap
  let guard := fun n : Label => if pos n.1.val n.2 then -coord n else coord n
  let cuts : H ⊕ Label → T →ᵃ[ℝ] ℝ := Sum.elim Subtype.val guard
  let a : (i : Fin L) → (Fin (w i.castSucc) → ℝ) →ᵃ[ℝ] (Fin (w i.succ) → ℝ) :=
    fun i => match N.val i with
    | Sum.inl (A, b) => AffineMap.pi (fun j =>
      (∑ k, A j k • LinearMap.proj k).toAffineMap + AffineMap.const ℝ _ (b j))
    | Sum.inr h => AffineMap.pi (fun j =>
      if pos i (Fin.cast h.down.symm j) then
        (LinearMap.proj (Fin.cast h.down.symm j)).toAffineMap else 0)
  have guard_mem : ∀ v ∈ R, ∀ n, guard n v ≤ 0 := by
    intro v hv n
    dsimp only [guard]
    split_ifs with hp
    · change -v n.1.val.castSucc n.2 ≤ 0
      exact neg_nonpos.mpr (hp v hv)
    · change v n.1.val.castSucc n.2 ≤ 0
      exact ((hs n.1.val n.1.property n.2).resolve_left hp) v hv
  apply affine_trajectory_cell step a V cuts R
  · intro v
    constructor
    · intro hv
      obtain ⟨hx, he, hh⟩ := (hR v).mp hv
      refine ⟨hx, he, ?_⟩
      intro k
      cases k with
      | inl f => exact hh f.val f.property
      | inr n => exact guard_mem v hv n
    · rintro ⟨hx, he, hh⟩
      exact (hR v).mpr ⟨hx, he, fun f hf => hh (Sum.inl ⟨f, hf⟩)⟩
  · intro v hv i
    rw [hstep]
    cases hi : N.val i with
    | inl ab =>
      rcases ab with ⟨A, b⟩
      ext j
      simp [a, hi, AffineMap.coe_add]
    | inr h =>
      ext j
      let k := Fin.cast h.down.symm j
      let n : Label := ⟨⟨i, ⟨h, hi⟩⟩, k⟩
      have hg := hv (Sum.inr n)
      change guard n v ≤ 0 at hg
      by_cases hp : pos i k
      · have hz : 0 ≤ v i.castSucc k := by
          simpa [guard, n, hp, coord] using hg
        simpa [a, hi, hp, k] using max_eq_left hz
      · have hz : v i.castSucc k ≤ 0 := by
          simpa [guard, n, hp, coord] using hg
        simpa [a, hi, hp, k] using max_eq_right hz

/-- Stop early when permitted, or split until the stable stopping condition holds. -/
theorem stopping_tree_exists {T I : Type*} [Fintype I]
    (z : I → T → ℝ) (Q stop : Set T → Prop)
    (terminal : ∀ R, Q R → (∀ i, (∀ v ∈ R, 0 ≤ z i v) ∨
      (∀ v ∈ R, z i v ≤ 0)) → stop R)
    (preserved : ∀ R i, Q R →
      Q {v ∈ R | z i v ≤ 0} ∧ Q {v ∈ R | 0 ≤ z i v}) (R : Set T) :
    let stable := fun S i => (∀ v ∈ S, 0 ≤ z i v) ∨ (∀ v ∈ S, z i v ≤ 0)
    Q R → ∃ (nodes : Finset (List Bool)) (labels : List Bool → Option I)
      (regions : List Bool → Set T),
      [] ∈ nodes ∧ regions [] = R ∧
      (∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes) ∧
      (∀ a ∈ nodes,
        (stop (regions a) ∧ a ++ [false] ∉ nodes ∧ a ++ [true] ∉ nodes) ∨
        ((¬ stop (regions a)) ∧ ∃ i, labels a = some i ∧
          ¬ stable (regions a) i ∧ a ++ [false] ∈ nodes ∧ a ++ [true] ∈ nodes ∧
          regions (a ++ [false]) = {v ∈ regions a | z i v ≤ 0} ∧
          regions (a ++ [true]) = {v ∈ regions a | 0 ≤ z i v})) := by
  classical
  intro stable
  induction R using sign_split_induction z with
  | terminal R hs =>
    intro hQ
    have hs := terminal R hQ hs
    refine ⟨{[]}, fun _ => none, fun _ => R, by simp, rfl, ?_, ?_⟩
    · intro a ha p hp
      have ha' : a = [] := by simpa using ha
      subst a
      have : p = [] := List.prefix_nil.mp hp
      simp [this]
    · intro a ha
      have ha' : a = [] := by simpa using ha
      subst a
      exact Or.inl ⟨hs, by simp, by simp⟩
  | split R i hi ih₀ ih₁ =>
    intro hQ
    by_cases hs : stop R
    ·
      refine ⟨{[]}, fun _ => none, fun _ => R, by simp, rfl, ?_, ?_⟩
      · intro a ha p hp
        have ha' : a = [] := by simpa using ha
        subst a
        have : p = [] := List.prefix_nil.mp hp
        simp [this]
      · intro a ha
        have ha' : a = [] := by simpa using ha
        subst a
        exact Or.inl ⟨hs, by simp, by simp⟩
    ·
      obtain ⟨n₀, l₀, r₀, hn₀, hr₀, hp₀, hv₀⟩ := ih₀ (preserved R i hQ).1
      obtain ⟨n₁, l₁, r₁, hn₁, hr₁, hp₁, hv₁⟩ := ih₁ (preserved R i hQ).2
      let nodes := insert []
        ((n₀.image (List.cons false)) ∪ (n₁.image (List.cons true)))
      let labels : List Bool → Option I := fun a => match a with
        | [] => some i
        | false :: b => l₀ b
        | true :: b => l₁ b
      let regions : List Bool → Set T := fun a => match a with
        | [] => R
        | false :: b => r₀ b
        | true :: b => r₁ b
      have mem₀ : ∀ a, false :: a ∈ nodes ↔ a ∈ n₀ := by
        intro a
        simp [nodes]
      have mem₁ : ∀ a, true :: a ∈ nodes ↔ a ∈ n₁ := by
        intro a
        simp [nodes]
      refine ⟨nodes, labels, regions, by simp [nodes], rfl, ?_, ?_⟩
      · intro a ha p hp
        cases p with
        | nil => simp [nodes]
        | cons b p =>
          cases a with
          | nil => exact False.elim (by simpa using hp)
          | cons c a =>
            obtain ⟨hbc, hpa⟩ := List.cons_prefix_cons.mp hp
            subst c
            cases b with
            | false => exact (mem₀ p).mpr (hp₀ a ((mem₀ a).mp ha) p hpa)
            | true => exact (mem₁ p).mpr (hp₁ a ((mem₁ a).mp ha) p hpa)
      · intro a ha
        cases a with
        | nil =>
          refine Or.inr ⟨?_, i, rfl, hi, ?_, ?_, hr₀, hr₁⟩
          · exact hs
          · exact (mem₀ []).mpr hn₀
          · exact (mem₁ []).mpr hn₁
        | cons b a =>
          cases b with
          | false =>
            have hv := hv₀ a ((mem₀ a).mp ha)
            simpa only [List.cons_append, regions, labels, mem₀] using hv
          | true =>
            have hv := hv₁ a ((mem₁ a).mp ha)
            simpa only [List.cons_append, regions, labels, mem₁] using hv

/-- The G.1 stopping certificate on a nonempty region of exact trajectories.
Deterministic evaluation identifies every prefix image of its input projection. -/
theorem closed_region_bounds {L : ℕ} {w : Fin (L+1) → ℕ}
    (N : Definition.NetworkSemantics (fun t => max t 0) L w) (hL : 0 < L)
    (R : Set ((j : Fin (L+1)) → Fin (w j) → ℝ)) (hne : R.Nonempty)
    (hr : ∀ v ∈ R, ∀ i : Fin L, v i.succ =
      match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * v i.castSucc k) + b j
      | Sum.inr h => fun j => max (v i.castSucc (Fin.cast h.down.symm j)) 0)
    (hp : ∀ j, ∃ V : Finset (Fin (w j) → ℝ),
      (fun v => v j) '' R = convexHull ℝ (↑V : Set _)) :
    let B := Definition.WindowRelaxation (fun t => max t 0) L w N
      ((fun v => v 0) '' R) 1 (by omega) hL
    ∀ k, B.2.1 k = sInf ((fun v => v (Fin.last L) k) '' R) ∧
      B.2.2 k = sSup ((fun v => v (Fin.last L) k) '' R) := by
  classical
  let f : {p : (L : ℕ) × (w : Fin (L+1) → ℕ) ×
      Definition.NetworkSemantics (fun t => max t 0) L w //
      p.2.1 0 = w 0 ∧ p.2.1 (Fin.last p.1) = w (Fin.last L) ∧ 0 < p.1} :=
    ⟨⟨L, w, N⟩, rfl, rfl, hL⟩
  let run : (j : Fin (L+1)) → (Fin (w 0) → ℝ) → Fin (w j) → ℝ :=
    Fin.induction (fun x => x) (fun i prev x =>
      match N.val i with
      | Sum.inl (A, b) => fun j => (∑ k, A j k * prev x k) + b j
      | Sum.inr h => fun j => max (prev x (Fin.cast h.down.symm j)) 0)
  have heval : ∀ v ∈ R, ∀ j, run j (v 0) = v j := by
    intro v hv j
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [hr v hv i]
      simp only [run, Fin.induction_succ]
      change (match N.val i with
        | Sum.inl (A,b) => fun j => (∑ k, A j k * run i.castSucc (v 0) k) + b j
        | Sum.inr h => fun j => max (run i.castSucc (v 0) (Fin.cast h.down.symm j)) 0) = _
      rw [ih]
  have image : ∀ j, run j '' ((fun v => v 0) '' R) = (fun v => v j) '' R := by
    intro j
    rw [Set.image_image]
    exact Set.image_congr (fun v hv => heval v hv j)
  have h := Lemma_Gp1.result_G_1 (w 0) (w (Fin.last L)) f
    ((fun v => v 0) '' R) (hne.image _) (hp 0) (by
      intro j hj
      dsimp only [f]
      simp only [Fin.cast_refl, id_eq, Set.image_id']
      obtain ⟨V, hV⟩ := hp j
      refine ⟨V, ?_⟩
      convert (image j).trans hV using 1 <;> dsimp only [run] <;> congr! <;> unfold Lemma_Gp1.result_G_1.match_1 stable_network_cell.match_1 <;> rfl)
  intro B k
  have hk := h k
  dsimp only [f] at hk
  simp only [Fin.cast_refl, id_eq, Set.image_id'] at hk
  have hc : (fun x => run (Fin.last L) x k) '' ((fun v => v 0) '' R) =
      (fun v => v (Fin.last L) k) '' R := by
    rw [Set.image_image]
    exact Set.image_congr (fun v hv => congrFun (heval v hv _) k)
  have hk' : B.2.1 k = sInf ((fun x => run (Fin.last L) x k) '' ((fun v => v 0) '' R)) ∧
      B.2.2 k = sSup ((fun x => run (Fin.last L) x k) '' ((fun v => v 0) '' R)) := by
    convert hk using 1 <;> dsimp only [B, run] <;> congr! <;> unfold Lemma_Gp1.result_G_1.match_1 stable_network_cell.match_1 <;> rfl
  simpa only [hc] using hk'

/-- Any invariant propagated to both children holds throughout a finite
prefix-closed execution tree. -/
theorem tree_region_invariant {T : Type*} (P : Set T → Prop)
    (nodes : Finset (List Bool)) (regions : List Bool → Set T)
    (hp : ∀ a ∈ nodes, ∀ p, p <+: a → p ∈ nodes)
    (hroot : P (regions []))
    (hchild : ∀ a ∈ nodes, ∀ b, a ++ [b] ∈ nodes →
      P (regions a) → P (regions (a ++ [b]))) :
    ∀ a ∈ nodes, P (regions a) := by
  intro a
  induction a using List.reverseRecOn with
  | nil => exact fun _ => hroot
  | append_singleton a b ih =>
    intro hab
    have ha := hp _ hab a ⟨[b], rfl⟩
    exact hchild a ha b hab (ih ha)

-- formalizer:machinery-end

end Proposition_5p6.Machinery
