import YM.RG08.Calendar.Way
import YM.RG08.Canon.Roses
/-!
 # Same witness can pay the Need list

 Assembly via uv_wishes (paid floor/delay over prefix) as in the
 `Oasis.Hall/Fruition` constructors. No reproof of its actual analytic inputs.
 This selects once; not to be conjoined with guarantees on different Cs.
 Further adjacencies/colors already on its Builds; takes penalty literally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Admission
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash YM.MergeProof MergeProof.Accent UVExtension UVExtension.Harvest

private lemma via (C:Family G)(h:G.Simple)(hT: C.Makes)(hC:Spec.Calibrated C)(hF:Oasis.Floral (hG:=h) C)(hX:Acme.Aroma C)
   (W:∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)
   (H:∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin) : ∃ f T, Nonempty (Spec.Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧ Oasis.Floral (hG:=h) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧ ∀ d k:ℕ,∀ᶠ p in atTop,∀ n (v:Fin n→ C.book.Token), (∀ i,(v i).1 ≤ d)→ ∃ g,Poppy.Margins C n p k v g := by
   let f:= Extraction.Order.full
   obtain ⟨g,A,L,R,T,E,hA,s,_⟩:= H f
   obtain ⟨hs,hG⟩:= W (f.refine g) s.copies
   obtain ⟨M,I,-,p⟩:= Acme.emanate (W:=E) hX h hs hG s hA.clean.ready hA.clean.tilt
   have hZ:= Acme.glistens hC hA.clean.ready hA.clean.tilt p
   exact ⟨_,_,hZ,hT,hC,hF, Reports.useFull hF hZ,Poppy.bravo (Oasis.appears hF)⟩
private lemma on_meadow {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{R:Factor A}{hG:G.Simple}{S:Spire.Uses R hG}{T:Org.Bolt A}{K:ℕ→ℝ} {a:Bid.Worth}{Q:Bandage R K a}{t:ℕ→ℕ}(L:Mast.Cellar S t Q) (h:Upland.Arc R S T) : Canon.TruePath (H:=(Mast.Cellar.yard (Mast.roseA S) L).path) (A.B.kin):= by
    refine ⟨fun N i p hi =>?_⟩
    let v:= Mast.roseA S; have hp:= Reports.offset_tests L v N p i hi; dsimp only at hp
    let W:= Oasis.spring h; let b:=(v N p).val; have he:b=0:=rfl
    have hs:= W.actual i p N hi b (by rw [he,abs_zero]; exact W.open_at)
    exact ⟨(congr_arg RG.Rep.path hp.2.2.2.1).trans hs.1, (congr_arg RG.Rep.clip hp.2.2.2.1).trans hs.2.1⟩

structure Bindage (C:Family G) : Prop where
    fonts : C.labels=Labels.frames G
    parcel : C.params=hol G
    stencil : HEq C.localSection (Next.Foundations.localSection G)
    chart : ∃ (s:Sheet G)(P:Rolls s)(Q:PostCost P)(H:Horizon C.path.levels)(F: Kin H (Next.Foundations.chart G)), Kin.Planned F Q ∧ Canon.TruePath (H:=C.path) F
    pw : ∀ i,∃ p:ℕ,(C.S.block i).val=3^p

variable {I:Type}[Encodable I](hG:G.Simple)
include hG
-- drop v flexibility? keep
set_option maxRecDepth 8000 in
set_option linter.unusedVariables false in
lemma oneC (K:KernelChoices)(hK:∀ P:Patch,P.Branches K G)(v:Orders)(hp:Draft v)(hz:∀ i,100≤v.supportExp i)
     (u:I→Need): ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book), Nonempty (Spec.Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧ Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧ (∀ d k:ℕ,∀ᶠ p in atTop,∀ n (v:Fin n→ C.book.Token), (∀ i,(v i).1 ≤ d)→ ∃ g,Poppy.Margins C n p k v g) ∧
     C.path.levels.clock.kernel=K ∧ Bindage C ∧ ∀ i:I,∀ n, Encodable.encode i ≤ C.path.levels.clock.J n → Affords (u i) C.path.levels n:= by
   obtain ⟨s,T,Y,K',hS,-,τ,-,Hτ⟩:= uv_wishes hG hK hp (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hz
   let t:= τ ⊔ prePay u; let M:=Case.provider s T t
   obtain ⟨P,hP⟩:= selects M.p hG
   obtain ⟨w,H⟩:= (Hτ t le_sup_left).2 P
   obtain ⟨Y,hY⟩:= H w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> ⟨0,0,1,1,1,0,0,by norm_num⟩)
   obtain ⟨θ,-,hF⟩:= hY _ fun _=>one_pos
   let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
   obtain ⟨T₀,-,hQ⟩:= hF Q (fun _ _=>⟨40,1,1,le_rfl⟩) ⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
   obtain ⟨T₁,hT₀,hT₁⟩:= minDelay u (fun i=> le_trans (show prePay u i ≤ M.p.floorL i from le_max_right ..) (P.large i).need) T₀
   obtain ⟨β₀,-⟩:= Bar.exists_above T₁ 2; let I':Wait β₀:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
   obtain ⟨W,-,HW⟩:= hQ T₁ hT₀ β₀ I'; obtain ⟨a,ha,hp⟩:= Wait.engine W hG
   obtain ⟨V,B,hB,R,W',c,T,r,S,Hx,Hk,hT,hq,hu,hD,hL,hR,⟨h',hH,hP',hQ⟩,hE⟩:= HW W le_rfl le_rfl le_rfl a ha hp
   let V₀:= Mast.centerB S Hx; let Z:=Mast.cellar S c Hx r Hk; let Y':= Mast.Cellar.gate (Mast.roseA S) Z
   let C:= Family.mk (Issue.trail V₀) (hol G) (Labels.frames G) (localSection G) r Y'
   have hF:= Oasis.survives Z Hx hD
   obtain ⟨hc,hF',hx,hU,hW,B₀,-,-,K₀,F₀,L,-,H'⟩:=hT.reception
   have hp:Ribbons.Created C:= ⟨_,r,Y',rfl⟩
   have hV:Acme.Aroma C:= ⟨Ribbons.laurelE C hG hU hu hq hp hF',hq, Ribbons.fugacious C hG hu⟩
   obtain ⟨i,T',hp',hM,hC,hF,H,hY'⟩:= via C hG hF' hc (hF hx h' hH (hB.symm ▸ hP') hQ hL hR hT hu) hV (fun f hf=>⟨grilled C hF' hU hq hf,hE f⟩) (fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:=H' f; exact ⟨g,A,L,R,T,E,hp⟩)
   -- literal
   refine ⟨C,i,T',hp',hM,hC,hF,H,hY',B.valid.kernel.trans hS,⟨rfl,rfl,HEq.rfl,⟨_,P,Y,B.M,B.kin,B.support,on_meadow Z Hx⟩,?_⟩,hT₁ T₁ β₀ W B.a (DelayLe.refl _) B.valid⟩
   intro i
   let x:= B.a
   change ∃ p:ℕ,(x.S.block i).val=3^p
   change ∃ p:ℕ,(B.a.clock.schedule.block i).val=3^p
   rw [← B.a.fits.sameFactor,B.valid.lengths]; exact hP _
end YM.RG08.Admission
