import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Dolls
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Revival
/-! # Marker-independent unmarked R.K. Hand back on full probe stencil exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S} {O : Orchard S}
    {P : Teller G} {W V ι κ α β υ ρ : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site c} {v : V→Site c}

-- across occupied and holes. Unite the two marker dictionaries exactly.
section
variable (F : ι ≃ κ) (b : Config G c →Config G c)
    (X : Equiv.Perm (Site c))
structure Holy (K : ι→Inner G u) (J : κ→Inner G v) : Prop where
  stages i : (J (F i)).extent=(K i).extent.map X.toEmbedding
  values i V : (J (F i)).value V=(K i).value (b V)
end
section
variable [Fintype ι] [Fintype κ] (X : ι→Support c) (Y : κ→Support c) (F : ι ≃ κ) (b : Equiv.Perm (Site c))
lemma roofGas (h : ∀ i,Y (F i)=(X i).map b.toEmbedding) (w : ι→ℝ) (r : κ→ℝ) (hr : ∀ i,w i=r (F i)) (p : Support c) :
    ReLog.fumes X w p=ReLog.fumes Y r (b.finsetCongr p):=by
  unfold ReLog.fumes; rw [tsum_fintype,tsum_fintype]; apply Fintype.sum_equiv F.finsetCongr; intro s
  let u:=s.map F.toEmbedding; let Q:=p.map b.toEmbedding
  have ht : ReLog.allowed X p s ↔ ReLog.allowed Y Q u:= by
    unfold ReLog.allowed; rw [ReLog.accepts,ReLog.accepts]; unfold ReLog.stays; simp only [subset_refl,true_and]
    refine and_congr ?_ (migration_disjoint b X Y F h s)
    constructor
    · intro hp i hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp hi; change Y (F j) ⊆ _; rw [h]; exact Finset.map_subset_map.mpr (hp j hj)
    intro hp i hi; have hz:= hp (F i) (mem_map.mpr ⟨_,hi,rfl⟩); rw [h] at hz; exact Finset.map_subset_map.mp hz
  unfold ReLog.note; refine if_congr ht ?_ rfl; change _=∏ i∈s.map F.toEmbedding,_
  rw [prod_map]; exact prod_congr rfl fun i _=> hr i
lemma walks_log (h : ∀ i,Y (F i)=(X i).map b.toEmbedding) (w : ι→ℝ) (r : κ→ℝ) (hr : ∀ i,w i=r (F i)) (p : Support c) :
    ReLog.locker (ReLog.fumes X w) p=ReLog.locker (ReLog.fumes Y r) (b.finsetCongr p):= by
  unfold ReLog.locker
  let f := ReLog.pieces fun A => -Real.log (ReLog.fumes X w A)
  let g := ReLog.pieces fun A=> -Real.log (ReLog.fumes Y r A)
  have hm (q : Support c) : (q.map b.toEmbedding).powerset=(q.powerset.map b.finsetCongr.toEmbedding):= by
    ext i; obtain ⟨i,rfl⟩:= b.finsetCongr.surjective i; rw [Finset.mem_map_equiv, Equiv.symm_apply_apply,mem_powerset,mem_powerset]; exact map_subset_map
  symm; change (g ∘ b.finsetCongr) p=f p
  refine ReLog.from_shed (f:=g ∘ b.finsetCongr) ?_
  intro v _
  have hS : ReLog.shed g (b.finsetCongr v)= -Real.log (ReLog.fumes Y r (b.finsetCongr v)):= ReLog.enact ..; rw [← roofGas X Y F b h w r hr] at hS
  refine Eq.trans ?_ hS; unfold ReLog.shed; change _=∑ i∈ (v.map b.toEmbedding).powerset,g i; rw [hm,Finset.sum_map]; rfl
end
section
variable {F : ι≃κ} {b : Config G c→Config G c} (E : Equiv.Perm (Site c))
def garden : Equiv.Perm (Glade c) := Equiv.subtypeEquiv E.finsetCongr (fun _=>map_nonempty.symm)
variable {E} {K : ι→Inner G u} {J : κ→Inner G v} [Fintype ι] [Fintype κ]
lemma Holy.locked (h : Holy F b E K J) (t : BudgetPoint) (ht : ∀ U,flags t.threshold U=(flags t.threshold (b U)).map E.toEmbedding) :
    Changing b E (garden E) (τ:=t.threshold) (fun i=> Sum.inl (scroll K i)) (fun i=>Sum.inl (scroll J i)) := by
  -- actually through `measureH`: Fill types
  refine ⟨fun _=>rfl,fun i U=>?_,fun _=>rfl,fun _=>rfl⟩
  change masked _ i.val _ _=masked _ (E.finsetCongr i.val) _ _
  have hv : Healthy t.threshold i.val (b U)↔Healthy t.threshold (E.finsetCongr i.val) U:= by unfold Healthy; rw [ht U]; exact (Finset.disjoint_map _).symm
  by_cases hs : Healthy t.threshold i.val (b U)
  · rw [masked_eq _ _ _ _ hs,masked_eq _ _ _ _ (hv.mp hs)]
    exact congr_arg (fun p:ℝ=> (↑(Real.exp p - 1):ℂ)) (walks_log _ _ F E h.stages (fun i=> ((K i).value (b U)).re) (fun i=> ((J i).value U).re) (fun i=> congr_arg _ (h.values i U).symm) i.val)
  rw [masked_ne _ _ _ _ hs,masked_ne _ _ _ _ (mt hv.mpr hs)]
lemma Holy.root (h : Holy F id (Equiv.refl _) K J) (b : BudgetPoint) (U) D : realGas K b D U=realGas J b D U:= by
  have hx i:(J (F i)).extent=(K i).extent:=by rw [h.stages]; ext; simp
  refine (roofGas _ _ F (Equiv.refl _) h.stages (ReLog.herald _ b _ _) (ReLog.herald _ b _ _) ?_ _).trans (congr_arg (ReLog.fumes (fun i=>(J i).extent) _) (by ext; simp))
  intro i; unfold ReLog.herald; simp_rw [hx,h.values];rfl
end
section unchanged
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (ht : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
  {o m Λ δ η o' m' Λ' δ' η' : ℝ} (hR : R.Lawful o m Λ δ η)
  {θ : W→Site f} {θ' : V→Site f} (hx : u=S.ratio.parent ∘ θ) (hy : v=S.ratio.parent ∘ θ')
local notation "Q0"=> unmarked R R' p ht hs hx hR
lemma callsQuiet (i) : (Q0 i).hues=quiet W:= by rcases i with (i|i)|i; rfl; rfl; exact i.elim
variable (hR' : R.Lawful o' m' Λ' δ' η')
local notation "Z"=> unmarked R R' p ht hs hy hR'
lemma regatta : Across Q0 Z (Equiv.refl _) (Equiv.refl _) (Equiv.refl _):= by
  constructor
  iterate 6
    · intro i; simp only [Equiv.refl_apply]; rw [show (Equiv.refl _).toEmbedding=Embedding.refl _ from rfl,map_refl]; rcases i with (i|i)|i <;> first| rfl| exact i.elim
  exact fun i=> callsQuiet ..; exact fun i=> callsQuiet ..
local notation "A"=> regatta R R' p ht hs hR hx hy hR'
lemma unchanged_value (i:Club Q0) U : letter Q0 (T:=T) i U=letter Z (T:=T) ((A).crosses i) U:= by
  let F:=A; let N:=F.crosses i; unfold letter
  have hV a:(Q0 a).permit=(Z a).permit ∧ (Q0 a).lamp=(Z a).lamp:= by rcases a with (j|j)|j; exact ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩; exact j.elim
  change glance _ _ _ _=glance _ (stage Z N.val) (glow Z N.val) U
  have hh : N.val=i.val:= by ext; change _∈(i.val.map (Equiv.refl _).toEmbedding) ↔ _; simp
  have h : stage Q0 i.val=stage Z N.val:= by rw [hh]; unfold stage; simp_rw [fun i=> (hV i).2]
  rw [h,hh]; unfold glow; simp_rw [fun i=> (hV i).1]
lemma growth : Holy (A).exe id (Equiv.refl _) (germ Q0 ht) (germ Z ht) := ⟨fun i=> (A).zone_covers i.val, fun i U=> (unchanged_value R R' p ht hs hR hx hy hR' i.val U).symm⟩
lemma arrested : Waking id (Equiv.refl _) (A).inn (gruel Q0 ht (fun _=>callsQuiet ..)) (gruel Z ht (fun _=>callsQuiet ..)):= by
  let P:=A
  refine ⟨fun i=>P.zone_covers i.val,fun i=> P.ticket_covers i.val,fun i U=> ?_,fun i=> Across.rises P.shade i.val.val,fun i=> Across.rises P.shaded ((P).inn.symm i |> fun _=>i.val.val)⟩
  unfold gruel; simp only [foundering]
  have hz: validArea Q0 i.val U↔ validArea Z (P.crosses i.val) U:= by
    unfold validArea; rw [P.zone_covers,P.ticket_covers]; exact mark_pass _ _ _ _ _ (by ext; simp)
  exact if_congr hz (unchanged_value ..) rfl
end unchanged
end YM.PhysicalNext.InteractingRank.Display.Sew
