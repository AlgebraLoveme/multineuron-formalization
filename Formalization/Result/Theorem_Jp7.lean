module
public import Formalization.Result.helpers.Theorem_Jp7.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Proposition_Jp2
public import Formalization.Result.Lemma_Jp6

open Definition

public section

namespace Theorem_Jp7

theorem result_J_7 (σ : ℝ → ℝ) (hσ : AdmissibleActivation σ) :
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
  let poly : {d : ℕ} → Set (Fin d → ℝ) → Prop := fun {d} X =>
    ∃ V : Finset (Fin d → ℝ), X = convexHull ℝ (↑V : Set _)
  let bounds : {d m : ℕ} → (f : Net d m) → Set (Fin d → ℝ) →
      (r : ℕ) → 1 ≤ r → r ≤ f.val.1 → (Fin m → ℝ) × (Fin m → ℝ) :=
    fun {_ _} f X r hr hL =>
      let R := WindowRelaxation σ f.val.1 f.val.2.1 f.val.2.2
        ((fun x k => x (Fin.cast f.property.1 k)) '' X) r hr hL
      ((fun j => R.2.1 (Fin.cast f.property.2.1.symm j)),
       (fun j => R.2.2 (Fin.cast f.property.2.1.symm j)))
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)), X.Nonempty → poly X → ¬X.Subsingleton →
  ∀ α : ℝ, 0 < α → α < 1 →
  ∀ T : ℝ, 0 < T →
  ∃ (f g : Net d 1),
    f.val.1 = g.val.1 ∧
    let r := max 1 ⌊α * (f.val.1 : ℝ)⌋₊
    ∃ hr : 1 ≤ r, ∃ hf : r ≤ f.val.1,
    ∃ hg : r ≤ g.val.1,
    let B := bounds f X r hr hf
    let C := bounds g X r hr hg
    B.1 0 ≤ sInf ((fun x => eval f x 0) '' X) - T ∧
      sSup ((fun x => eval g x 0) '' X) + T ≤ C.2 0 := (by
  -- formalizer:proof-begin
  classical
  intro Net run eval poly bounds d X hX hp hn α hα hα1 T hT
  -- J.7: the polytope is compact, and J.2 supplies a nonconvex image H(X).
  obtain ⟨V, hV⟩ := hp
  have cX : IsCompact X := by
    rw [hV]
    exact V.finite_toSet.isCompact_convexHull ℝ
  have hfront := Proposition_Jp2.result_J_2 σ hσ.1 hσ.2.1 d X hX ⟨V, hV⟩ hn
  change ∃ (m : ℕ) (H : Net d m),
    (eval H '' X ⊂ convexHull ℝ (eval H '' X)) ∧
      ∃ i : Fin H.val.1, i.val + 1 = H.val.1 ∧
        ∃ A b, H.val.2.2.val i = Sum.inl (A, b) at hfront
  obtain ⟨m, H, hH, iH, hiH, AH, bH, hlastH⟩ := hfront
  have crun {a b : ℕ} (f : Net a b) : ∀ j, Continuous (run f j) := by
    intro j
    induction j using Fin.induction with
    | zero => exact continuous_id
    | succ i ih =>
      dsimp only [run, Fin.induction_succ]
      dsimp only [run] at ih
      cases hstep : f.val.2.2.val i with
      | inl ab =>
        simp only [hstep]
        apply continuous_pi
        intro t
        exact (continuous_finset_sum _ (fun k _ => continuous_const.mul
          ((continuous_apply k).comp ih))).add continuous_const
      | inr h =>
        simp only [hstep]
        apply continuous_pi
        intro t
        exact hσ.1.comp ((continuous_apply _).comp ih)
  have cm : Continuous (eval H) := by
    apply continuous_pi
    intro j
    exact (continuous_apply (Fin.cast H.property.2.1.symm j)).comp
      ((crun H (Fin.last H.val.1)).comp
        (continuous_pi (fun k => continuous_apply (Fin.cast H.property.1 k))))
  let S := eval H '' X
  have cS : IsCompact S := cX.image cm
  have neS : S.Nonempty := hX.image _
  have ncS : ¬Convex ℝ S := by
    intro hc
    exact hH.ne hc.convexHull_eq.symm
  have hm : 0 < m := by
    rw [← H.property.2.1]
    exact H.val.2.2.property _
  -- Choose M so that the fractional window fits inside the eventual bridge.
  obtain ⟨M, hM, hchoice⟩ :=
    Machinery.bridge_length α hα1 H.val.1
  -- J.6 preserves the selected midpoint and excludes it from every prefix image.
  have hbridge := Lemma_Jp6.result_J_6 σ hσ m M hm (by omega) S cS ncS
  change ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ B : Net m m,
    M ≤ B.val.1 ∧
    (∃ k : ℕ, 0 < k ∧ B.val.1 = 2*k+1) ∧
    (∀ j : Fin (B.val.1+1), B.val.2.1 j = m) ∧
    (∀ i : Fin B.val.1,
      (Even i.val → ∃ A b, B.val.2.2.val i = Sum.inl (A,b)) ∧
      (Odd i.val → ∃ h, B.val.2.2.val i = Sum.inr h)) ∧
    ∀ j : Fin (B.val.1+1), 1 ≤ j.val →
      run B j (fun k => ((x₁ (Fin.cast B.property.1 k) + x₂ (Fin.cast B.property.1 k))/2)) =
        (fun k => (run B j (fun t => x₁ (Fin.cast B.property.1 t)) k +
          run B j (fun t => x₂ (Fin.cast B.property.1 t)) k)/2) ∧
      run B j (fun k => ((x₁ (Fin.cast B.property.1 k) + x₂ (Fin.cast B.property.1 k))/2)) ∉
        (fun x => run B j (fun k => x (Fin.cast B.property.1 k))) '' S at hbridge
  obtain ⟨s₁, hs₁, s₂, hs₂, B, hMB, ⟨kB, hkB, hdepthB⟩, hwidthB, hlayersB, hprefix⟩ := hbridge
  let firstB : Fin B.val.1 := ⟨0, B.property.2.2⟩
  obtain ⟨AB, bB, hfirstB⟩ := (hlayersB firstB).1 (by exact ⟨0, rfl⟩)
  let j : Fin (B.val.1+1) := ⟨B.val.1-1, by omega⟩
  have hj : 1 ≤ j.val := by dsimp [j]; omega
  let pre :=  fun x : Fin m → ℝ => run B j (fun k => x (Fin.cast B.property.1 k))
  let z : Fin m → ℝ := fun k => (s₁ k + s₂ k)/2
  let K := pre '' S
  let p := pre z
  have hbinput : Continuous (fun (x : Fin m → ℝ) (k : Fin (B.val.2.1 0)) =>
      x (Fin.cast B.property.1 k)) := continuous_pi (fun k => continuous_apply _)
  have cp : Continuous pre := (crun B j).comp hbinput
  have cK : IsCompact K := cS.image cp
  have neK : K.Nonempty := neS.image _
  have hpK : p ∉ K := (hprefix j hj).2
  -- Removing the bridge's final layer leaves a compact image separated from p.
  obtain ⟨δ, hδ, hsep⟩ :=
    Machinery.separated_compact
      K cK neK p hpK
  -- Approximate 2T‖h-p‖₂²/δ² on conv(K∪{p}) with error T/2;
  -- the three-layer detector has D(p) ≤ T/2 and D(K) ≥ 3T/2.
  obtain ⟨n, a, W, b, c, hDp, hDK⟩ :=
    Machinery.detector_parameters
      σ hσ.1 hσ.2.1 K cK p δ T hδ hT hsep
  have hrBound :=
    Machinery.window_length_bound
      α hα1 H.val.1 M B.val.1 hM hMB hchoice
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    obtain ⟨x, hx⟩ := neK
    have hDx := hDK x hx
    simp only [Fin.sum_univ_zero, add_zero] at hDp hDx
    linarith
  -- Realize the approximating detector with exactly affine/activation/affine layers.
  let wd : Fin 4 → ℕ := ![B.val.2.1 j, n, n, 1]
  let Nd : NetworkSemantics σ 3 wd := by
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
      · exact Sum.inl (W, b)
      · exact Sum.inr ⟨rfl⟩
      · exact Sum.inl ((fun _ k => a k), fun _ => c)
    · intro i
      fin_cases i <;> simp [wd, hnpos, B.val.2.2.property j]
  let D : Net (B.val.2.1 j) 1 := ⟨⟨3, wd, Nd⟩, rfl, rfl, by norm_num⟩
  have dstep (x : Fin (B.val.2.1 j) → ℝ) (i : Fin 3) :
      run D i.succ x =
        match Nd.val i with
        | Sum.inl (A, b) => fun t => (∑ k, A t k * run D i.castSucc x k) + b t
        | Sum.inr h => fun t => σ (run D i.castSucc x (Fin.cast h.down.symm t)) := by
    simp only [run, D, Fin.induction_succ]
    cases Nd.val i with
    | inl ab => rcases ab with ⟨A, b⟩; rfl
    | inr h => rfl
  have done (x : Fin (B.val.2.1 j) → ℝ) :
      run D 1 x = fun t => (∑ k, W t k * x k) + b t := dstep x 0
  have dtwo (x : Fin (B.val.2.1 j) → ℝ) :
      run D 2 x = fun t => σ ((∑ k, W t k * x k) + b t) := by
    have h := dstep x 1
    change run D 2 x = (fun t => σ (run D 1 x t)) at h
    rw [h, done]
    rfl
  have dval (x : Fin (B.val.2.1 j) → ℝ) :
      eval D x 0 = c + ∑ i, a i * σ ((∑ k, W i k * x k) + b i) := by
    have h := dstep x 2
    change run D 3 x = (fun _ => (∑ i, a i * run D 2 x i) + c) at h
    change run D 3 x (0 : Fin 1) = _
    rw [h, dtwo]
    exact add_comm _ _
  have hDp' : eval D p 0 ≤ T/2 := by rw [dval]; exact hDp
  have hDK' : ∀ x ∈ K, 3*T/2 ≤ eval D x 0 := by
    intro x hx; rw [dval]; exact hDK x hx
  -- The true detector image lies above 3T/2, whereas its value at p is at most T/2.
  have hDmin : 3*T/2 ≤ sInf ((fun x => eval D x 0) '' K) := by
    apply le_csInf (neK.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact hDK' x hx
  have hDgap : eval D p 0 ≤ sInf ((fun x => eval D x 0) '' K) - T := by
    linarith
  have hImage : ((fun x => eval D (pre (eval H x)) 0) '' X) =
      (fun x => eval D x 0) '' K := by
    simp only [K, S, Set.image_image, Function.comp_def]
  -- J.7 merges B's first affine map into H's affine output, keeping depth L₀.
  have hiHlast : iH.succ = Fin.last H.val.1 := Fin.ext hiH
  have hHout : H.val.2.1 iH.succ = m := by rw [hiHlast]; exact H.property.2.1
  let P : Matrix (Fin (H.val.2.1 iH.succ)) (Fin (H.val.2.1 iH.succ)) ℝ :=
    fun u v => AB (Fin.cast (hHout.trans (hwidthB firstB.succ).symm) u)
      (Fin.cast (hHout.trans (hwidthB firstB.castSucc).symm) v)
  let q : Fin (H.val.2.1 iH.succ) → ℝ :=
    fun u => bB (Fin.cast (hHout.trans (hwidthB firstB.succ).symm) u)
  let mergedA : Matrix (Fin (H.val.2.1 iH.succ)) (Fin (H.val.2.1 iH.castSucc)) ℝ :=
    fun u v => ∑ t, P u t * AH t v
  let mergedb : Fin (H.val.2.1 iH.succ) → ℝ := fun u => (∑ t, P u t * bH t) + q u
  let Nt : NetworkSemantics σ H.val.1 H.val.2.1 :=
    ⟨fun i => if he : i = iH then he ▸ Sum.inl (mergedA, mergedb) else H.val.2.2.val i,
      H.val.2.2.property⟩
  let Ht : Net d m := ⟨⟨H.val.1, H.val.2.1, Nt⟩, H.property⟩
  have hNt (i : Fin H.val.1) (hi : i ≠ iH) : Nt.val i = H.val.2.2.val i := by
    simp only [Nt, dif_neg hi]
  have hNtlast : Nt.val iH = Sum.inl (mergedA, mergedb) := by simp [Nt]
  have hpre : ∀ j : Fin (H.val.1+1), j.val ≤ iH.val → run Ht j = run H j := by
    intro j
    induction j using Fin.induction with
    | zero => intro _; rfl
    | succ i ih =>
      intro hj
      have hi : i ≠ iH := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ] at hj
        omega
      have hprev := ih (by simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢; omega)
      simp only [run, Fin.induction_succ, Ht]
      dsimp only [run, Ht] at hprev
      rw [hNt i hi, hprev]
      cases H.val.2.2.val i <;> rfl
  have merged_action (x : Fin (H.val.2.1 0) → ℝ) :
      run Ht iH.succ x = fun t => (∑ k, P t k * run H iH.succ x k) + q t := by
    have ht : run Ht iH.succ x =
        fun t => (∑ k, mergedA t k * run Ht iH.castSucc x k) + mergedb t := by
      simp only [run, Fin.induction_succ, Ht]
      rw [hNtlast]
    have hh : run H iH.succ x =
        fun t => (∑ k, AH t k * run H iH.castSucc x k) + bH t := by
      simp only [run, Fin.induction_succ]
      rw [hlastH]
    rw [ht, hpre iH.castSucc (by rfl), hh]
    exact Machinery.affine_composition
      AH bH P q (run H iH.castSucc x)
  have first_action (x : Fin m → ℝ) :
      run B firstB.succ (fun k => x (Fin.cast B.property.1 k)) =
        fun t => (∑ k, AB t k * x (Fin.cast (hwidthB firstB.castSucc) k)) + bB t := by
    simp only [run, Fin.induction_succ]
    rw [hfirstB]
    rfl
  have merged_eval (x : Fin d → ℝ) (t : Fin m) :
      eval Ht x t =
        run B firstB.succ (fun k => eval H x (Fin.cast B.property.1 k))
          (Fin.cast (hwidthB firstB.succ).symm t) := by
    have he := congrFun (merged_action (fun k => x (Fin.cast H.property.1 k)))
      (Fin.cast hHout.symm t)
    have heval : eval Ht x t =
        (∑ k, P (Fin.cast hHout.symm t) k *
          run H iH.succ (fun k => x (Fin.cast H.property.1 k)) k) +
          q (Fin.cast hHout.symm t) := by
      convert he using 1
      exact (Machinery.coordinate_cast
        H.val.2.1 (fun j => run Ht j (fun k => x (Fin.cast H.property.1 k)))
        hiHlast (Fin.cast hHout.symm t)).symm
    rw [heval, first_action]
    dsimp only [P, q]
    simp only [Fin.cast_trans, Fin.cast_eq_self]
    congr 1
    have hs := (finCongr (hHout.trans (hwidthB firstB.castSucc).symm)).sum_comp
      (fun k => AB (Fin.cast (hwidthB firstB.succ).symm t) k *
        eval H x (Fin.cast (hwidthB firstB.castSucc) k))
    rw [← hs]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    simp only [finCongr_apply, Fin.cast_trans, eval]
    exact Machinery.coordinate_cast
      H.val.2.1 (fun j => run H j (fun k => x (Fin.cast H.property.1 k))) hiHlast k
  -- Splice the remaining N−2 bridge layers and the three detector layers.
  have hHL := H.property.2.2
  let cut := H.val.1 + B.val.1 - 2
  let L := H.val.1 + B.val.1 + 1
  have hcut : cut + 3 = L := by dsimp [cut, L]; omega
  let embH (u : Fin (H.val.1+1)) : Fin (L+1) := ⟨u.val, by dsimp [L]; omega⟩
  let embB (u : Fin (B.val.1+1)) : Fin (L+1) :=
    ⟨H.val.1 - 1 + u.val, by dsimp [L]; omega⟩
  let embD (u : Fin 4) : Fin (L+1) := ⟨cut + u.val, by omega⟩
  let wf : Fin (L+1) → ℕ := fun u =>
    if hu : u.val ≤ H.val.1 then H.val.2.1 ⟨u.val, by omega⟩
    else if hb : u.val ≤ cut then B.val.2.1 ⟨u.val-H.val.1+1, by dsimp [cut] at hb; omega⟩
    else wd ⟨u.val-cut, by omega⟩
  have hwH (u : Fin (H.val.1+1)) : wf (embH u) = H.val.2.1 u := by
    simp only [wf, embH, show u.val ≤ H.val.1 by omega, dite_true]
  have hwB (u : Fin (B.val.1+1)) (hu : 1 ≤ u.val) (huN : u.val ≤ B.val.1-1) :
      wf (embB u) = B.val.2.1 u := by
    by_cases h1 : u.val = 1
    · have he : embB u = embH (Fin.last H.val.1) := Fin.ext (by dsimp [embB, embH]; omega)
      rw [he, hwH, H.property.2.1, hwidthB]
    · have hfront : ¬H.val.1 - 1 + u.val ≤ H.val.1 := by omega
      have hbridge : H.val.1 - 1 + u.val ≤ cut := by dsimp [cut]; omega
      simp only [wf, embB, hfront, dite_false, hbridge, dite_true]
      apply congrArg B.val.2.1
      apply Fin.ext
      dsimp
      omega
  have hwD (u : Fin 4) : wf (embD u) = wd u := by
    by_cases h0 : u.val = 0
    · have hu0 : u = 0 := Fin.ext h0
      subst u
      have he : embD 0 = embB j := Fin.ext (by dsimp [embD, embB, j, cut]; omega)
      rw [he, hwB j hj (by dsimp [j]; omega)]
      rfl
    · have hfront : ¬cut + u.val ≤ H.val.1 := by dsimp [cut]; omega
      have hdet : ¬cut + u.val ≤ cut := by omega
      simp only [wf, embD, hfront, dite_false, hdet]
      congr 1
      apply Fin.ext
      simp
  have hwpos : ∀ u, 0 < wf u := by
    intro u
    dsimp only [wf]
    split_ifs
    · exact H.val.2.2.property _
    · exact B.val.2.2.property _
    · exact Nd.property _
  let recode {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
      (layer : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a=b)) :
      (Matrix (Fin b') (Fin a') ℝ × (Fin b' → ℝ)) ⊕ PLift (a'=b') := by
    subst a'; subst b'; exact layer
  let Nf : NetworkSemantics σ L wf := by
    refine ⟨fun i => ?_, hwpos⟩
    by_cases hi : i.val < H.val.1
    · let u : Fin H.val.1 := ⟨i.val, hi⟩
      have hin : wf i.castSucc = H.val.2.1 u.castSucc := hwH u.castSucc
      have hout : wf i.succ = H.val.2.1 u.succ := hwH u.succ
      exact recode hin.symm hout.symm (Nt.val u)
    · by_cases hb : i.val < cut
      · let u : Fin B.val.1 := ⟨i.val-H.val.1+1, by dsimp [cut] at hb; omega⟩
        have hu : 1 ≤ u.val := by dsimp [u]; omega
        have huN : u.val+1 ≤ B.val.1-1 := by dsimp [u, cut] at *; omega
        have ein : embB u.castSucc = i.castSucc := Fin.ext (by dsimp [embB, u]; omega)
        have eout : embB u.succ = i.succ := Fin.ext (by dsimp [embB, u]; omega)
        have hin := hwB u.castSucc hu (by simp; omega)
        have hout := hwB u.succ (by simp only [Fin.val_succ]; omega) (by simpa using huN)
        rw [ein] at hin
        rw [eout] at hout
        exact recode hin.symm hout.symm (B.val.2.2.val u)
      · let u : Fin 3 := ⟨i.val-cut, by have := i.isLt; omega⟩
        have ein : embD u.castSucc = i.castSucc := Fin.ext (by dsimp [embD,u]; omega)
        have eout : embD u.succ = i.succ := Fin.ext (by dsimp [embD,u]; omega)
        have hin := hwD u.castSucc
        have hout := hwD u.succ
        rw [ein] at hin
        rw [eout] at hout
        exact recode hin.symm hout.symm (Nd.val u)
  have hw0 : wf 0 = d := (hwH 0).trans H.property.1
  have hwlast : wf (Fin.last L) = 1 := by
    have he : embD 3 = Fin.last L := Fin.ext (by dsimp [embD]; simpa using hcut)
    rw [← he, hwD]
    rfl
  let f : Net d 1 := ⟨⟨L, wf, Nf⟩, hw0, hwlast, by dsimp [L]; omega⟩
  have hdepthf : f.val.1 = H.val.1+B.val.1+1 := rfl
  have hrf : max 1 ⌊α * (f.val.1 : ℝ)⌋₊ ≤ B.val.1-1 := hrBound
  let act {a b : ℕ}
      (layer : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a=b))
      (x : Fin a → ℝ) : Fin b → ℝ :=
    match layer with
    | Sum.inl (A,b) => fun t => (∑ k, A t k * x k) + b t
    | Sum.inr h => fun t => σ (x (Fin.cast h.down.symm t))
  have act_recode {a b a' b' : ℕ} (ha : a=a') (hb : b=b')
      (layer : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a=b))
      (x : Fin a' → ℝ) (t : Fin b') :
      act (recode ha hb layer) x t =
        act layer (fun k => x (Fin.cast ha k)) (Fin.cast hb.symm t) := by
    subst a'; subst b'; rfl
  have run_step {a b : ℕ} (F : Net a b) (i : Fin F.val.1)
      (x : Fin (F.val.2.1 0) → ℝ) :
      run F i.succ x = act (F.val.2.2.val i) (run F i.castSucc x) := by
    simp only [run, Fin.induction_succ]
    cases F.val.2.2.val i <;> rfl
  have layerH (i : Fin H.val.1) :
      Nf.val ⟨i.val, by dsimp [L]; omega⟩ =
        recode (hwH i.castSucc).symm (hwH i.succ).symm (Nt.val i) := by
    simp only [Nf, dif_pos i.isLt]
    rfl
  have rfH (x : Fin d → ℝ) : ∀ u : Fin (H.val.1+1),
      run f (embH u) (fun k => x (Fin.cast hw0 k)) =
        fun t => run Ht u (fun k => x (Fin.cast H.property.1 k)) (Fin.cast (hwH u) t) := by
    intro u
    induction u using Fin.induction with
    | zero => rfl
    | succ i ih =>
      let v : Fin L := ⟨i.val, by dsimp [L]; omega⟩
      have hp : (fun k => run f (embH i.castSucc) (fun k => x (Fin.cast hw0 k))
          (Fin.cast (hwH i.castSucc).symm k)) =
          run Ht i.castSucc (fun k => x (Fin.cast H.property.1 k)) := by
        funext k
        rw [ih]
        simp only [Fin.cast_cast, Fin.cast_eq_self]
      funext t
      change run f v.succ _ t = _
      rw [run_step]
      change act (Nf.val v) _ t = _
      rw [layerH i]
      erw [act_recode]
      change act (Nt.val i)
        (fun k => run f (embH i.castSucc) (fun k => x (Fin.cast hw0 k))
          (Fin.cast (hwH i.castSucc).symm k)) (Fin.cast (hwH i.succ) t) = _
      rw [hp, run_step]
  have recode_index {I : Type} {a b : I → ℕ}
      (layers : (i : I) → (Matrix (Fin (b i)) (Fin (a i)) ℝ × (Fin (b i) → ℝ)) ⊕ PLift (a i=b i))
      {i j : I} (he : i=j) {c d : ℕ}
      (hi : a i=c) (hi' : b i=d) (hj : a j=c) (hj' : b j=d) :
      recode hi hi' (layers i) = recode hj hj' (layers j) := by
    cases he
    rfl
  have layerB (i : Fin B.val.1) (hi : 1 ≤ i.val) (hiN : i.val+1 ≤ B.val.1-1) :
      Nf.val ⟨H.val.1-1+i.val, by dsimp [L]; omega⟩ =
        recode (hwB i.castSucc hi (by simp only [Fin.val_castSucc]; omega)).symm
          (hwB i.succ (by simp only [Fin.val_succ]; omega) hiN).symm (B.val.2.2.val i) := by
    have hfront : ¬H.val.1-1+i.val < H.val.1 := by omega
    have hbridge : H.val.1-1+i.val < cut := by dsimp [cut]; omega
    have hind : H.val.1-1+i.val-H.val.1+1 = i.val := by omega
    simp only [Nf, dif_neg hfront, dif_pos hbridge]
    exact recode_index B.val.2.2.val (Fin.ext hind) _ _ _ _
  have layerD (i : Fin 3) :
      Nf.val ⟨cut+i.val, by omega⟩ =
        recode (hwD i.castSucc).symm (hwD i.succ).symm (Nd.val i) := by
    have hfront : ¬cut+i.val < H.val.1 := by dsimp [cut]; omega
    have hdet : ¬cut+i.val < cut := by omega
    simp only [Nf, dif_neg hfront, dif_neg hdet]
    exact recode_index Nd.val (Fin.ext (by simp)) _ _ _ _
  have rfB (x : Fin d → ℝ) : ∀ u : Fin (B.val.1+1),
      ∀ hu : 1 ≤ u.val, ∀ huN : u.val ≤ B.val.1-1,
      run f (embB u) (fun k => x (Fin.cast hw0 k)) =
        fun t => run B u (fun k => eval H x (Fin.cast B.property.1 k))
          (Fin.cast (hwB u hu huN) t) := by
    intro u
    induction u using Fin.induction with
    | zero => intro hu; simp at hu
    | succ i ih =>
      intro hu huN
      by_cases hi0 : i.val = 0
      · have he : i = firstB := Fin.ext hi0
        subst i
        have hemb : embB firstB.succ = embH (Fin.last H.val.1) :=
          Fin.ext (by dsimp [embB, embH, firstB]; omega)
        funext t
        have hf := congrFun (rfH x (Fin.last H.val.1))
          (Fin.cast (congrArg wf hemb) t)
        have hh := Machinery.coordinate_cast
          wf (fun u => run f u (fun k => x (Fin.cast hw0 k))) hemb t
        rw [hh, hf]
        have hm := merged_eval x
          (Fin.cast H.property.2.1 (Fin.cast (hwH (Fin.last H.val.1)) (Fin.cast (congrArg wf hemb) t)))
        simpa only [eval, Ht, Fin.cast_cast, Fin.cast_eq_self] using hm
      · have hi : 1 ≤ i.val := by omega
        have hin : i.val ≤ B.val.1-1 := by simp only [Fin.val_succ] at huN; omega
        have hprev := ih hi hin
        let v : Fin L := ⟨H.val.1-1+i.val, by dsimp [L]; omega⟩
        have hp : (fun k => run f (embB i.castSucc) (fun k => x (Fin.cast hw0 k))
            (Fin.cast (hwB i.castSucc hi hin).symm k)) =
            run B i.castSucc (fun k => eval H x (Fin.cast B.property.1 k)) := by
          funext k
          rw [hprev]
          simp only [Fin.cast_cast, Fin.cast_eq_self]
        funext t
        change run f v.succ _ t = _
        rw [run_step]
        change act (Nf.val v) _ t = _
        rw [layerB i hi huN]
        erw [act_recode]
        change act (B.val.2.2.val i)
          (fun k => run f (embB i.castSucc) (fun k => x (Fin.cast hw0 k))
            (Fin.cast (hwB i.castSucc hi hin).symm k)) (Fin.cast (hwB i.succ hu huN) t) = _
        rw [hp, run_step]
  have bridge_continue (v : (u : Fin (L+1)) → Fin (wf u) → ℝ) (y : Fin m → ℝ)
      (vstep : ∀ i : Fin L, H.val.1 ≤ i.val → v i.succ = act (Nf.val i) (v i.castSucc))
      (vfirst : v (embB firstB.succ) = fun t =>
        run B firstB.succ (fun k => y (Fin.cast B.property.1 k))
          (Fin.cast (hwB firstB.succ (by dsimp [firstB]; omega) (by dsimp [firstB]; omega)) t)) :
      ∀ u : Fin (B.val.1+1), ∀ hu : 1 ≤ u.val, ∀ huN : u.val ≤ B.val.1-1,
      v (embB u) = fun t => run B u (fun k => y (Fin.cast B.property.1 k))
        (Fin.cast (hwB u hu huN) t) := by
    intro u
    induction u using Fin.induction with
    | zero => intro hu; simp at hu
    | succ i ih =>
      intro hu huN
      by_cases hi0 : i.val = 0
      · have he : i = firstB := Fin.ext hi0
        subst i
        exact vfirst
      · have hi : 1 ≤ i.val := by omega
        have hin : i.val ≤ B.val.1-1 := by simp only [Fin.val_succ] at huN; omega
        have hprev := ih hi hin
        let a : Fin L := ⟨H.val.1-1+i.val, by dsimp [L]; omega⟩
        have hp : (fun k => v (embB i.castSucc) (Fin.cast (hwB i.castSucc hi hin).symm k)) =
            run B i.castSucc (fun k => y (Fin.cast B.property.1 k)) := by
          funext k
          rw [hprev]
          simp only [Fin.cast_cast, Fin.cast_eq_self]
        funext t
        change v a.succ t = _
        rw [vstep a (by dsimp [a]; omega), layerB i hi huN]
        erw [act_recode]
        change act (B.val.2.2.val i)
          (fun k => v (embB i.castSucc) (Fin.cast (hwB i.castSucc hi hin).symm k))
          (Fin.cast (hwB i.succ hu huN) t) = _
        rw [hp, run_step]
  have detector_continue (v : (u : Fin (L+1)) → Fin (wf u) → ℝ)
      (y : Fin (B.val.2.1 j) → ℝ)
      (vstep : ∀ i : Fin L, cut ≤ i.val → v i.succ = act (Nf.val i) (v i.castSucc))
      (vstart : v (embD 0) = fun t => y (Fin.cast (hwD 0) t)) :
      ∀ u : Fin 4, v (embD u) = fun t => run D u y (Fin.cast (hwD u) t) := by
    intro u
    induction u using Fin.induction with
    | zero => exact vstart
    | succ i ih =>
      let a : Fin L := ⟨cut+i.val, by omega⟩
      have hp : (fun k => v (embD i.castSucc) (Fin.cast (hwD i.castSucc).symm k)) =
          run D i.castSucc y := by
        funext k
        rw [ih]
        simp only [Fin.cast_cast, Fin.cast_eq_self]
      funext t
      change v a.succ t = _
      rw [vstep a (by dsimp [a]; omega), layerD i]
      erw [act_recode]
      change act (Nd.val i) (fun k => v (embD i.castSucc) (Fin.cast (hwD i.castSucc).symm k))
        (Fin.cast (hwD i.succ) t) = _
      rw [hp, run_step]
  have hembD : embD 0 = embB j := Fin.ext (by dsimp [embD, embB, j, cut]; omega)
  have rfD (x : Fin d → ℝ) : ∀ u : Fin 4,
      run f (embD u) (fun k => x (Fin.cast hw0 k)) =
        fun t => run D u (pre (eval H x)) (Fin.cast (hwD u) t) := by
    apply detector_continue (fun u => run f u (fun k => x (Fin.cast hw0 k))) (pre (eval H x))
    · intro i _; exact run_step f i _
    · funext t
      rw [Machinery.coordinate_cast
        wf (fun u => run f u (fun k => x (Fin.cast hw0 k))) hembD t, rfB x j hj (by dsimp [j]; omega)]
      rfl
  have hembLast : embD 3 = Fin.last L := Fin.ext (by dsimp [embD]; simpa using hcut)
  have ef (x : Fin d → ℝ) : eval f x 0 = eval D (pre (eval H x)) 0 := by
    have hh := congrFun (rfD x 3) (Fin.cast (hwD 3).symm (0 : Fin 1))
    have hc := Machinery.coordinate_cast
      wf (fun u => run f u (fun k => x (Fin.cast hw0 k))) hembLast
        (Fin.cast (hwD 3).symm (0 : Fin 1))
    rw [hc] at hh
    exact hh
  -- Use one midpoint assignment through the front, then exact continuation.
  obtain ⟨x₁, hx₁, ex₁⟩ := hs₁
  obtain ⟨x₂, hx₂, ex₂⟩ := hs₂
  let traj (x : Fin d → ℝ) := fun u => run f u (fun k => x (Fin.cast hw0 k))
  let v : (u : Fin (L+1)) → Fin (wf u) → ℝ :=
    Fin.induction (fun t => (traj x₁ 0 t + traj x₂ 0 t)/2)
      (fun i prev => if i.val < H.val.1 then
        fun t => (traj x₁ i.succ t + traj x₂ i.succ t)/2 else act (Nf.val i) prev)
  have hvmid : ∀ u : Fin (L+1), u.val ≤ H.val.1 →
      v u = fun t => (traj x₁ u t + traj x₂ u t)/2 := by
    intro u
    induction u using Fin.induction with
    | zero => intro _; rfl
    | succ i ih =>
      intro hu
      simp only [v, Fin.induction_succ, if_pos (show i.val < H.val.1 by simp at hu; omega)]
      rfl
  have hve : ∀ i : Fin L, H.val.1 ≤ i.val → v i.succ = act (Nf.val i) (v i.castSucc) := by
    intro i hi
    simp only [v, Fin.induction_succ, if_neg (show ¬i.val < H.val.1 by omega)]
  have vfirst : v (embB firstB.succ) = fun t =>
      run B firstB.succ (fun k => z (Fin.cast B.property.1 k))
        (Fin.cast (hwB firstB.succ (by dsimp [firstB]; omega) (by dsimp [firstB]; omega)) t) := by
    rw [hvmid (embB firstB.succ) (by dsimp [embB, firstB]; omega)]
    funext t
    dsimp only [traj]
    rw [rfB x₁ firstB.succ (by dsimp [firstB]; omega) (by dsimp [firstB]; omega),
      rfB x₂ firstB.succ (by dsimp [firstB]; omega) (by dsimp [firstB]; omega), ex₁, ex₂]
    exact (congrFun (hprefix firstB.succ (by dsimp [firstB]; omega)).1 _).symm
  have vB := bridge_continue v z hve vfirst
  have vD : ∀ u : Fin 4, v (embD u) = fun t => run D u p (Fin.cast (hwD u) t) := by
    apply detector_continue v p
    · intro i hi; apply hve i; dsimp [cut] at hi; omega
    · funext t
      rw [Machinery.coordinate_cast
        wf v hembD t, vB j hj (by dsimp [j]; omega)]
      rfl
  have vout : v (Fin.last L) (Fin.cast hwlast.symm (0 : Fin 1)) = eval D p 0 := by
    have hh := congrFun (vD 3) (Fin.cast (hwD 3).symm (0 : Fin 1))
    rw [Machinery.coordinate_cast
      wf v hembLast (Fin.cast (hwD 3).symm (0 : Fin 1))] at hh
    exact hh
  -- J.6 supplies the midpoint identities at every individual bridge prefix.
  have hvmid_all (u : Fin (L+1)) (hu : u.val ≤ cut) :
      v u = fun t => (traj x₁ u t + traj x₂ u t)/2 := by
    by_cases hfront : u.val ≤ H.val.1
    · exact hvmid u hfront
    · let a : Fin (B.val.1+1) := ⟨u.val-H.val.1+1, by dsimp [cut] at hu; omega⟩
      have ha : 1 ≤ a.val := by dsimp [a]; omega
      have haN : a.val ≤ B.val.1-1 := by dsimp [a, cut] at *; omega
      have hemb : embB a = u := Fin.ext (by dsimp [embB,a]; omega)
      rw [← hemb, vB a ha haN]
      dsimp only [traj]
      rw [rfB x₁ a ha haN, rfB x₂ a ha haN, ex₁, ex₂]
      funext t
      exact congrFun (hprefix a ha).1 _
  let r := max 1 ⌊α * (f.val.1 : ℝ)⌋₊
  have hr : 1 ≤ r := le_max_left _ _
  have hrL : r ≤ L := by change r ≤ B.val.1-1 at hrf; dsimp [L]; omega
  let Xin := (fun (x : Fin d → ℝ) k => x (Fin.cast hw0 k)) '' X
  have cvX : Convex ℝ X := by rw [hV]; exact convex_convexHull ℝ _
  have hv0 : v 0 ∈ Xin := by
    have hmid := cvX hx₁ hx₂ (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    refine ⟨(1/2:ℝ) • x₁ + (1/2:ℝ) • x₂, hmid, ?_⟩
    funext t
    change (1/2)*x₁ (Fin.cast hw0 t) + (1/2)*x₂ (Fin.cast hw0 t) =
      (x₁ (Fin.cast hw0 t) + x₂ (Fin.cast hw0 t))/2
    ring
  let C := WindowRelaxation.stages(WindowRelaxation σ L wf Nf Xin r hr hrL)
  have hC0 : C 0 = {v | v 0 ∈ Xin} := rfl
  have hCs : ∀ s, C (s+1) = C s ∩ convexHull ℝ {v : (u : Fin (L+1)) → Fin (wf u) → ℝ |
      (∃ u ∈ C s, ∀ j, j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = act (Nf.val i) (v i.castSucc)} := by
    intro s
    change C s ∩ convexHull ℝ _ = C s ∩ convexHull ℝ _
    apply congrArg (fun S => C s ∩ S)
    apply congrArg (convexHull ℝ)
    ext q
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    cases h : Nf.val i with
    | inl ab => cases ab; simp only [h]; rfl
    | inr hh => simp only [h]; rfl
  -- Front windows end before D; later windows contain exact continuations.
  have hvfeasible := Machinery.midpoint_then_exact_mem_windows
    (cut := H.val.1) (fun i => act (Nf.val i)) Xin C hC0 hCs v (traj x₁) (traj x₂)
    hv0 ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩
    (fun i => run_step f i _) (fun i => run_step f i _)
    (fun s hs u _ hu => hvmid_all u (by dsimp [cut]; change r ≤ B.val.1-1 at hrf; omega)) hve
    (L-r+1)
  have cXin : IsCompact Xin := cX.image (continuous_pi (fun _ => continuous_apply _))
  have continuous_act {a b : ℕ}
      (layer : (Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)) ⊕ PLift (a=b)) :
      Continuous (act layer) := by
    cases layer with
    | inl ab =>
      apply continuous_pi; intro t
      exact (continuous_finset_sum _ (fun k _ => continuous_const.mul (continuous_apply k))).add continuous_const
    | inr h => exact continuous_pi (fun t => hσ.1.comp (continuous_apply _))
  have hbdd := Machinery.window_output_bounded
    hr hrL (fun i => act (Nf.val i)) (fun i => continuous_act _) Xin cXin C hC0 hCs
    (Fin.cast hwlast.symm (0 : Fin 1))
  have hlower : (bounds f X r hr hrL).1 0 ≤ eval D p 0 := by
    change sInf ((fun q => q (Fin.last L) (Fin.cast hwlast.symm 0)) '' C (L-r+1)) ≤ _
    rw [← vout]
    exact csInf_le hbdd.1 ⟨v, hvfeasible, rfl⟩
  have lowergap : (bounds f X r hr hrL).1 0 ≤ sInf ((fun x => eval f x 0) '' X) - T := by
    simp only [ef, hImage]
    exact hlower.trans hDgap
  -- Reflect only the final affine output; the depth and window length stay fixed.
  let lastI : Fin L := ⟨cut+2, by omega⟩
  have last_succ : lastI.succ = Fin.last L := Fin.ext (by dsimp [lastI]; omega)
  have last_affine : ∃ A b, Nf.val lastI = Sum.inl (A,b) := by
    have hh := layerD (2 : Fin 3)
    change Nf.val lastI = _ at hh
    rw [hh]
    have recode_affine {a b a' b' : ℕ} (ha : a=a') (hb : b=b')
        (A : Matrix (Fin b) (Fin a) ℝ) (q : Fin b → ℝ) :
        ∃ A' q', recode ha hb (Sum.inl (A,q)) = Sum.inl (A',q') := by
      subst a'; subst b'; exact ⟨A,q,rfl⟩
    exact recode_affine _ _ _ _
  obtain ⟨Af, bf, hAf⟩ := last_affine
  let Ng : NetworkSemantics σ L wf := ⟨fun i =>
    if h : i = lastI then h ▸ Sum.inl (-Af,-bf) else Nf.val i, hwpos⟩
  let g : Net d 1 := ⟨⟨L,wf,Ng⟩,hw0,hwlast,by dsimp [L]; omega⟩
  let e : (u : Fin (L+1)) → (Fin (wf u) → ℝ) ≃ₗ[ℝ] (Fin (wf u) → ℝ) :=
    fun u => if u = Fin.last L then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ _
  have ein (i : Fin L) : e i.castSucc = LinearEquiv.refl ℝ _ := by
    apply if_neg
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  have e0 : e 0 = LinearEquiv.refl ℝ _ := by
    apply if_neg
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_zero, Fin.val_last] at this
    dsimp [L] at this
    omega
  have elast : e (Fin.last L) = LinearEquiv.neg ℝ := if_pos rfl
  have comm : ∀ i x, e i.succ (act (Nf.val i) x) = act (Ng.val i) (e i.castSucc x) := by
    intro i x
    rw [ein]
    by_cases hi : i = lastI
    · subst i
      have he : e lastI.succ = LinearEquiv.neg ℝ := if_pos last_succ
      rw [he]
      simp only [Ng, dif_pos rfl, hAf, act, LinearEquiv.refl_apply, LinearEquiv.neg_apply,
        Pi.neg_apply, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
      funext t
      simp [add_comm]
    · have ho : i.succ ≠ Fin.last L := by
        intro hh
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val hh
        dsimp [lastI]
        simp only [Fin.val_succ, Fin.val_last] at hv
        omega
      simp only [e, if_neg ho, Ng, dif_neg hi, LinearEquiv.refl_apply]
  have runs_reflect (x : Fin d → ℝ) : ∀ u,
      run g u (fun k => x (Fin.cast hw0 k)) = e u (traj x u) := by
    intro u
    induction u using Fin.induction with
    | zero => rw [e0]; rfl
    | succ i ih =>
      rw [run_step g, ih, ← comm]
      congr 1
      exact (run_step f i _).symm
  have eg (x : Fin d → ℝ) : eval g x 0 = -eval f x 0 := by
    have hh := congrFun (runs_reflect x (Fin.last L)) (Fin.cast hwlast.symm 0)
    rw [elast] at hh
    exact hh
  let Cg := WindowRelaxation.stages(WindowRelaxation σ L wf Ng Xin r hr hrL)
  have hCg0 : Cg 0 = {v | v 0 ∈ Xin} := rfl
  have hCgs : ∀ s, Cg (s+1) = Cg s ∩ convexHull ℝ {v : (u : Fin (L+1)) → Fin (wf u) → ℝ |
      (∃ u ∈ Cg s, ∀ j, j.val = s → v j = u j) ∧
      ∀ i : Fin L, s ≤ i.val → i.val < s+r → v i.succ = act (Ng.val i) (v i.castSucc)} := by
    intro s
    change Cg s ∩ convexHull ℝ _ = Cg s ∩ convexHull ℝ _
    apply congrArg (fun S => Cg s ∩ S)
    apply congrArg (convexHull ℝ)
    ext q
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    cases h : Ng.val i with
    | inl ab => cases ab; simp only [h]; rfl
    | inr hh => simp only [h]; rfl
  -- Coordinate reflection carries every graph hull and intersection to g's relaxation.
  have hcgj := Machinery.windows_conjugate
    (fun i => act (Nf.val i)) (fun i => act (Ng.val i)) e comm Xin C Cg hC0
    (by simpa [e0] using hCg0) hCs hCgs (L-r+1)
  have hvg : (LinearEquiv.piCongrRight e) v ∈ Cg (L-r+1) := by
    rw [← hcgj]
    exact ⟨v,hvfeasible,rfl⟩
  have hgbdd := Machinery.window_output_bounded
    hr hrL (fun i => act (Ng.val i)) (fun i => continuous_act _) Xin cXin Cg hCg0 hCgs
    (Fin.cast hwlast.symm (0 : Fin 1))
  have hupper : -eval D p 0 ≤ (bounds g X r hr hrL).2 0 := by
    have hh := le_csSup hgbdd.2 (Set.mem_image_of_mem
      (fun q => q (Fin.last L) (Fin.cast hwlast.symm (0 : Fin 1))) hvg)
    change e (Fin.last L) (v (Fin.last L)) (Fin.cast hwlast.symm 0) ≤ _ at hh
    simpa only [elast, LinearEquiv.neg_apply, Pi.neg_apply, vout] using hh
  have hgmax : sSup ((fun x => eval g x 0) '' X) ≤ -(3*T/2) := by
    apply csSup_le (hX.image _)
    rintro _ ⟨x,hx,rfl⟩
    change eval g x 0 ≤ -(3*T/2)
    erw [eg, ef]
    exact neg_le_neg (hDK' _ ⟨eval H x, ⟨x,hx,rfl⟩, rfl⟩)
  refine ⟨f,g,rfl,hr,hrL,hrL,lowergap,?_⟩
  change sSup ((fun x => eval g x 0) '' X) + T ≤ (bounds g X r hr hrL).2 0
  linarith
  -- formalizer:proof-end
)

end Theorem_Jp7
