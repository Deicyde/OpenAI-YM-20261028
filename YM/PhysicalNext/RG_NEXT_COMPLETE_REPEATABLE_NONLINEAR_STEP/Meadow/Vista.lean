import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Mantel
/-! # Proof governed Oak for Spark BOTH directions. Exact large-to-small ratio on
   foliage includes base price Lebesgue conditions; nothing injective on bigger grows.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
section grey
variable {X Y: Type} (u:X→Support C) (v:Y→Support c)
lemma capitates (p:Finset X) (q: Finset Y) (Φ: ↥p≃ ↥q) (h:∀ i j:↥p, Ac.meets u i.val (u j.val)↔Ac.meets v (Φ i).val (v (Φ j).val)) : Ac.Spark u p ↔ Ac.Spark v q:= by
  have H {X Y:Type} {c C: Side} {u:X→Support c} {v:Y→Support C} {p:Finset X} {q:Finset Y} (Φ: ↥p≃ ↥q) (h:∀ i j:↥p, Ac.meets u i.val (u j.val) →Ac.meets v (Φ i).val (v (Φ j).val)) (hf:Ac.Spark u p): Ac.Spark v q:= by
    obtain ⟨x,hx⟩:= hf.1; let f:= extend (Subtype.val : ↥p → X) (Subtype.val ∘ Φ) (fun _=> (Φ ⟨x,hx⟩).val); have hh i: f (i:↥p).val=(Φ i).val:= Subtype.val_injective.extend_apply ..
    refine ⟨⟨_,(Φ ⟨x,hx⟩).property⟩,fun i hi j hj=>?_⟩; let a:=Φ.symm ⟨i,hi⟩; let b:=Φ.symm ⟨j,hj⟩; have hu:f a.val=i:= Eq.trans (hh a) (congr_arg Subtype.val (Φ.apply_symm_apply _)); have hv:f b.val=j:=(hh b).trans (congr_arg Subtype.val (Φ.apply_symm_apply _))
    rw [← hu, ← hv]; refine Relation.ReflTransGen.lift f ?_ _ _ (hf.2 _ a.property _ b.property); intro i j hG; obtain ⟨h1,h2,h3⟩:=hG; change Ac.bonds v q (f i) (f j); rw [show f i=_ from hh ⟨i,h1⟩, show f j=_ from hh ⟨j,h2⟩]; exact ⟨(Φ _).2,(Φ _).2,h ⟨j,h2⟩ ⟨i,h1⟩ h3⟩
  exact ⟨H Φ (fun i j=> (h i j).1), H Φ.symm (fun i j hij=> (h (Φ.symm i) (Φ.symm j)).2 (by rw [Φ.apply_symm_apply,Φ.apply_symm_apply]; exact hij))⟩
lemma sparkling (f: X→ Y) (u:Y→ Support c) (b:Finset X) (he:Set.InjOn f b): Ac.Spark (u ∘ f) b↔ Ac.Spark u (b.image f):= by
  let p:=Equiv.ofBijective (fun i:↥b=> show ↥(b.image f) from ⟨f i.val,mem_image_of_mem f i.property⟩) (And.intro (fun a b h => Subtype.ext (he a.property b.property (congr_arg Subtype.val h))) (by
    intro y; obtain ⟨v,hv,hx⟩:=mem_image.mp y.2; exact ⟨⟨_,hv⟩,Subtype.ext hx⟩))
  apply capitates _ _ _ _ p fun i j=> Iff.rfl
lemma preheated (f: X→ Y) (u:X→Support C) (v:Y→Support c) (x:Finset X) (s:Site C→ Site c) (he:∀ i,v (f i)=(u i).image s)
    (hz:Set.InjOn f x) (hx:Set.InjOn s (x.biUnion u)):
    Ac.Spark u x↔Ac.Spark v (x.image f):= by
  apply Iff.trans _ (sparkling f v x hz)
  refine capitates _ _ _ _ (Equiv.refl _) (fun i j=> ?_); unfold Ac.meets; simp only [Function.comp_apply,Equiv.refl_apply,he, Finset.exists_mem_image]
  constructor
  · rintro ⟨k,hk,ht⟩; exact ⟨k,hk,mem_image_of_mem _ ht⟩
  rintro ⟨k,hk,ht⟩; obtain ⟨l,hl,hL⟩:=mem_image.mp ht; exact ⟨k,hk,(hx (show l∈x.biUnion u from mem_biUnion.mpr ⟨_,i.2,hl⟩) (show k∈ x.biUnion u from mem_biUnion.mpr ⟨_,j.2,hk⟩) hL) ▸ hl⟩
end grey

variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
-- includes length/ground but not val bills
local notation "B" => radiusB p
lemma footland (p:Park C F) : Meadow.ground I' p=p.biUnion (I'.supportP ∘ Mint.disc (Y)):= by
  unfold Meadow.ground Cash.unionP hatch
  ext i; constructor
  · intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:=mem_map.mp hk; exact mem_biUnion.mpr ⟨_,hj,hx⟩
  intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map_of_mem _ hk,hx⟩
variable (hp : R'.path= R.path)
include hC he hp I I'
lemma contempt (i:Music C F) : verse R'.path i=verse R.path (verse_down (L) i) ∧ I.supportP (Mint.disc (S) (verse_down (L) i))=(I'.supportP (Mint.disc (Y) i)).image ((L).low.cut):= by
  have hc:= I.laws.data.room.buys; have hh: c.val ≤ f.val:= by rw [h]; exact Nat.le_mul_of_pos_right _ P.L.property
  exact Stellar.voy (he:=he) (hC:=hC) (T:=T) (T':=T') i X.halo (B) hp (by omega)
lemma pitched (i:Park C F): Meadow.ground I (wrappers (L) i)= (Meadow.ground I' i).image (L).low.cut:= by
  have heq j : I.supportP (Mint.disc (S) (verse_down (L) j))=_:= (contempt (I:=I) (I':=I') hC he hp j).2
  rw [footland,footland]; unfold wrappers; ext x; constructor
  · intro h; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj',rfl⟩:= mem_image.mp hj; dsimp only [Function.comp_apply] at hx; rw [heq] at hx; obtain ⟨i,hv,rfl⟩:= mem_image.mp hx; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj',hv⟩)
  intro h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; obtain ⟨z,hz,hv⟩:=mem_biUnion.mp hx; refine mem_biUnion.mpr ⟨_,mem_image_of_mem _ hz,?_⟩; dsimp only [Function.comp_apply]; rw [heq]; exact mem_image_of_mem _ hv
lemma seed_order (p:Park C F) (heq:Set.InjOn (verse_down (L)) p) (hh:Set.InjOn ((L).low.cut) (Meadow.ground I' p)) : Seed I' p ↔ Seed I (wrappers (L) p):= by
  have he' := preheated (verse_down (L)) (I'.supportP ∘ disc (Y)) (I.supportP ∘ disc (S)) p (L).low.cut (fun i=> (contempt hC he (I:=I) (I':=I') hp i).2) heq (by rw [footland] at hh; exact hh)
  have ht := card_image_of_injOn heq
  have hf {c f'} {W₁:StepData c f'} (p: Finset (Music c f')) (g: Head W₁→Support c): Ac.Spark g (hatch W₁ p) ↔Ac.Spark (g ∘ disc W₁) p:= by
    unfold hatch; rw [Finset.map_eq_image]; exact (sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
  have ha : Ac.Spark I'.supportP (hatch _ p) ↔Ac.Spark I.supportP (hatch _ (wrappers (L) p)):= (hf p _).trans ((show Ac.Spark (I'.supportP ∘ disc (Y)) p ↔ Ac.Spark (I.supportP ∘ disc (S)) (wrappers (L) p) from (by convert! he' using 2; unfold wrappers; congr; exact Subsingleton.elim _ _)).trans (hf (wrappers (L) p) I.supportP).symm)
  constructor
  · intro h; refine ⟨ha.1 h.hot,ht ▸ h.sizes,fun i hi=>?_⟩; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; exact (contempt hC he hp (I:=I) (I':=I') i).1 ▸ h.earns _ (by assumption)
  intro h; refine ⟨ha.2 h.hot,ht ▸ h.sizes,fun i hi=> (contempt hC he hp (I:=I) (I':=I') i).1.trans_le (h.earns _ (mem_image_of_mem _ hi))⟩
end YM.PhysicalNext.Repeat.Meadow
