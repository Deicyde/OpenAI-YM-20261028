import YM.Next.MULTISOURCE.Ledger
import YM.Next.MULTISOURCE.Surface


/-! The uniform mixed transfer theorem from the unmarked-response gate.
    Build the paid vacuum derivatives without any additional assumption about transferring multi-marker coefficients,
    using actual scalar maps and root/scale pricing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice MeasureTheory Filter Finset MvPolynomial Desk Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G}

private lemma scratches {n : Side} {P : Rep G n} {k κ : ℝ} {X : Support n} (o : Site n) (D : Pulse G n)
    (he : Credit P.p 0 κ X D k) (hh : o∈X) (hx : 2≤ X.card) : ∃ f, Scratch P.p D o k κ f ∧
      (∀ i, X ⊆ f i) ∧ (∀ i, D.2 i ≠ 0 → X ⊆ i.zone) := by
  obtain ⟨-,-,-,hk,⟨i,F,ht,hH,-,W,H,t,hW,hw,hf⟩,g,hg,hG⟩ := he
  refine ⟨W,⟨hk,⟨H,t,fun i => ⟨(hW i).1 hh,(hW i).2.1,(hW i).2.2.2 o hh⟩,?_,fun U => ?_⟩,
    g,?_,fun i => ⟨(hG i).1,fun hv => (hG i).2.1 hv hh,(hG i).2.2⟩⟩,fun i => (hW i).1,fun i => (hG i).2.1⟩
  · simpa only [burn_zero] using hw
  · simp only [ht,hH hx,zero_add]; exact hf U
  simpa only [burn_zero] using hg

theorem hydrated (H : C.Makes) (d j : ℕ) (ht : Stability C d j) : Adjoining C d j := by
  intro N p he V _ _ R o hx
  dsimp only; intro v D k hv hK
  let A := C.path.levels
  let M := A.clock.op j p
  let P := C.path.rep N p j
  let Q := C.path.rep N p (j+1)
  let b := neighboring C j
  have hb : 1 ≤ b := Real.one_le_exp (by positivity)
  have hB := inv_pos.mpr (zero_lt_one.trans_le hb)
  let κ := money A j
  let k' := money A (j+1)
  have ho := hx.injective (A.budget j).B_pos
  let Y x := M.ratio.embed (o x)
  have hY : Function.Injective Y := by exact (show Function.LeftInverse M.ratio.parent M.ratio.embed from M.ratio.embed_parent).injective.comp ho
  let e (x : Hot R) := x.property.choose
  have hx' x : e x∈ x.sites := x.property.choose_spec
  let f (x : Hot R) := o (e x)
  have hf (x) : e (Hot.one R x)=x := mem_singleton.mp (hx' (Hot.one R x))
  have hh (x) : f (Hot.one R x)=o x := by unfold f; rw [hf]
  let ref (x : Hot R) := if x.sites.card=1 then some (v (e x)) else none
  have hJ x : ref (Hot.one R x)=some (v x) := by simp [ref,hf]
  let X (x : Hot R) := x.sites.image Y
  have hh' (x : Hot R) (he : ref x ≠ none) : ∃ i, Hot.one R i=x := by
    apply Hot.one_of_card; by_contra hb; simp [ref,hb] at he
  have hX (x : Hot R) : ∃ W, ref x=none → Scratch Q.p (D x) (M.ratio.embed (f x)) (k x) k' W ∧
      (∀ i, X x ⊆ W i) ∧ (∀ i, (D x).2 i ≠ 0 → X x ⊆ i.zone) := by
    by_cases H : ref x=none
    · have hh : 2≤(X x).card := by
        have hp : 0 < x.sites.card := Finset.card_pos.mpr x.property
        unfold X; rw [card_image_of_injective _ hY]; by_contra hk
        have he : x.sites.card=1 := by omega
        simp [ref,he] at H
      obtain ⟨t,he⟩ := scratches (P:=Q) (Y (e x)) (D x) (hv x)
        (mem_image_of_mem Y (hx' _)) hh
      exact ⟨t,fun _ => he⟩
    exact ⟨fun _ => ∅,fun hh => False.elim (H hh)⟩
  choose F hF using hX
  have hi : Set.InjOn f {i | (ref i).isSome} := by
    intro i hi j hj h
    obtain ⟨x,rfl⟩ := hh' _ (Option.isSome_iff_ne_none.mp hi)
    obtain ⟨y,rfl⟩ := hh' _ (Option.isSome_iff_ne_none.mp hj)
    rw [hh,hh] at h; exact ho h ▸ rfl
  have hk i (w : C.label d) (h' : ref i=some w) : D i=Single.one C N w (M.ratio.embed (f i)) ∧
      k i=Single.tariff C N p (j+1) w ∧ Credit Q.p 0 k' {M.ratio.embed (f i)} (D i) (k i) := by
    obtain ⟨x,rfl⟩ := hh' i (by simp [h']); rw [hJ, Option.some.injEq] at h'
    subst w; rw [hh]; refine ⟨(hK x).1,(hK x).2,?_⟩
    simpa only [Hot.sites_one,image_singleton] using hv (Hot.one R x)
  obtain ⟨T,H',HR,hy,hT,hu⟩ := ht N p he (Hot R) D k f ref F hi (fun i h => (hF i h).1) hk
  let W (x : Hot R) := x.sites.image o
  let Z (x : Hot (parts R)) := T.taste (power x.sites)
  have hhK i : 0 ≤ k i := (hv i).2.2.2.1
  refine ⟨Z,fun i => ?_,fun q hq => ?_⟩
  · have he := hT _ _ (hJ i); rw [hh] at he; exact he
  obtain ⟨r,hr,hR⟩ := permits f k _ hhK hB
  refine ⟨?_,?_⟩
  · funext U
    have he' := serialize T (parts R) (H.wilson.represents N p (j+1) he).good D (fun i => (hv i).integrand) U
      H' (A.transition_mass ..) hr hR hu q.val
    change (many P (parts R) Z U).part q.val=_ at he'
    rw [jet_account P Z (H.wilson.represents N p j he.le).good.labels q] at he'
    unfold defect; rw [← he',add_sub_cancel_right]
  have hf : Set.InjOn e q.sites := by
    intro i hi j hj h; by_contra hh
    exact Finset.disjoint_left.mp (parts_wise q.val hi hj hh) (hx' i) (h.symm ▸ hx' j)
  have hy' : W (unionOfHot q)=q.sites.biUnion W := by unfold W; rw [show (unionOfHot q).sites=q.sites.biUnion Hot.sites from rfl]; rw [Finset.biUnion_image]
  have hs := pawns T f k _ hhK hB H' HR W q.sites (money_accepted A j).1 (fun i hi j hj he => hf hi hj (ho he))
    (hy' ▸ (unionOfHot q).property.image o) (fun i _ V hi => ?_) ?_
  · rw [← hy'] at hs
    apply Credit.expand hs
    have hW : q.sites.card ≤ (unionOfHot q).sites.card := by
      rw [← Finset.card_image_of_injOn hf]
      apply Finset.card_le_card; intro i hi
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hi; exact mem_biUnion.mpr ⟨x,hx,hx' _⟩
    simp only [inv_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hW) (prod_nonneg fun i _ => hhK i)
  · by_cases h : ref i=none
    · have hb := (hF i h).2
      have he (u : Support _) (h : X i ⊆ u) : W i ⊆ u.image M.ratio.parent := by
        intro x hx; obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨_,h (mem_image_of_mem _ hz), M.ratio.embed_parent _⟩
      rw [if_pos h] at hi; obtain ⟨i',H⟩|⟨v,hv,ht⟩:=hi
      · exact subset_trans (he _ (hb.1 i')) H
      exact subset_trans (he _ (hb.2 _ hv)) ht
    rw [if_neg h] at hi; obtain ⟨j,rfl⟩ := hh' _ h
    rw [hh] at hi; simpa [W] using hi
  rw [← print_coeff (parts R) _ q.val, staves_print (parts R)]
  rw [lambda,Poly.part_sum]; refine sum_eq_zero fun i _ => ?_
  rw [Poly.part_send]; split <;> rename_i h
  · apply hy; by_contra hh; obtain ⟨j,rfl⟩ := hh' _ hh
    rw [show q=Hot.one _ _ from Subtype.ext h, unionOfHot_one] at hq; simp at hq
  rfl
lemma Stability.exports (H : C.Makes) (d) (he : Stable C d) : Responsive C d :=
  he.mono (fun _ hp => hydrated H d _ hp)
end YM.Multi
