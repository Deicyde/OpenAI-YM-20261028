import YM.FullVolume.Nectar.Regalia
import YM.FullVolume.Nectar.Ritz
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat Greenbelt Lotus Merge Merge.Switch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open FullVolume.Ray FullVolume.Ray.Weigh MergeProof MergeProof.Accent GridApprox.Nil Marker
open Jams
variable {V I J Y : Type} [DecidableEq V]{B: Marker.Census V} {G:Gauge}{n:Side}{b:ℕ}
variable {X:I →Support n}{Z:J→Support n}{w:V→ℝ} {q d p C :ℝ}{F:sun→I→Y→Poly B}
-- buoys: Θ along sun.All ℓ.Finset prices explicitly.
def Buoya (w:V→ℝ)(q:ℝ)(F:sun→Y→ Poly B)(a:ℝ):Prop:=1≤q∧∃ v: GridApprox.Nil.Sheet B, 0 ≤ v ∧ (∀ i U, Scout q (phraseS fun t=>(F t U).part i) (v i)) ∧ wordsPrice w v ≤ a
structure Ankh (w:V→ℝ)(q:ℝ)(F:sun→I→Y→Poly B)(b:ℕ)(X:I→Support n)(p C:ℝ):Prop where
    beam:∃ a:I→ℝ,Summable a∧ Ac.Hit X b a p C ∧∀ i,Buoya w q (fun t=>F t i) (a i)
namespace Buoya
variable {A:sun→Y→Poly B} {K:Type}[Fintype K]
lemma ticket (h: Buoya w q A d)(s:sun): Loci w (A s) d:=by
   obtain ⟨_,v,hv,hh,hP⟩:=h; exact ⟨v,hv,fun U i=>by have h:=(hh i U).held s.property; rw [phrased] at h; exact h,hP⟩
lemma stocked {f:Trail Y K}(h:Strung f q p)(he:∀ i,0<w i)(r:K→Poly B) (hz:∀ i,Poly.price w (r i) ≤1): Buoya w q (fun t x=>sound r (f t x)) p:=by
   obtain ⟨ha,u,hU,hP,hH,h⟩:=h; let R(j:Finset K):= ∏ i∈j,r i; have hf(x): Poly.price w (R x)≤1:= (Poly.multiple he x r).trans (Finset.prod_le_one (fun i _=> Poly.nonnegative he (r i)) (fun i _=> hz i)); let g (i:B.Mode)(x:Finset K):= u x * ‖(R x).part i‖
   refine ⟨ha,fun i=> ∑ x,g i x,fun i=>sum_nonneg fun x _=>mul_nonneg (hU _) (norm_nonneg _),fun i y=> ?_,?_⟩
   · unfold phraseS sound; simp_rw [Switch.mapScores_apply, Poly.part_sum, Poly.part_smul];exact Scout.pieces univ _ _ ha fun x _=> Luna.mult (goes_complex (h x y)) (Scout.still ha _)
   unfold wordsPrice g; simp_rw [Finset.mul_sum,mul_left_comm (Poly.toll ..) (u _)]; rw [sum_comm]; exact (Finset.sum_le_sum (g:=u) fun i _=> by rw [← mul_sum]; exact mul_le_of_le_one_right (hU i) (hf i)).trans hP
lemma plank {j:I→J}[Nonempty Y](hp:1≤q)(h:Ankh w q F b (Z∘j) p C) (hw:∀ i,0<w i): Ankh w q (fun t=>tally j (F t)) b Z p C:=by
   obtain ⟨a,ha,hx,h⟩:=h.beam
   choose v hv hY hB using fun i=> (h i).2
   let A(r):= cram j a r
   have he(i:B.Mode):Summable (fun j=> v j i):= by
       apply (summable_mul_left_iff (Poly.worth hw i).ne').mp; refine ha.of_nonneg_of_le (fun j=> mul_nonneg (Poly.worth hw i).le (hv j _)) (fun j=> ?_); exact (single_le_sum (f:=fun i=> Poly.toll w i*v j i) (fun i _=> mul_nonneg (Poly.worth hw i).le (hv _ _)) (mem_univ _)).trans (hB j)
   refine ⟨A,(heavy j ha).summable,fun u=> ?_,fun r=> ?_⟩
   · let t(i):= if u∈ Z (j i) then a i*Real.exp (p*coverNumber b (Z (j i))) else 0
     have h₁:= heavy j (f:=t) (hx u).2.1; change SumBudget (fun r=>if u∈Z r then _ else 0) C
     rw [show (fun r=>if u∈Z r then A r*Real.exp (p*coverNumber b (Z r)) else 0)=cram j t from funext fun i=>?_]; exact ⟨fun i=> tsum_nonneg (fun k=> (hx u).1 k.val),h₁.summable,h₁.tsum_eq.trans_le (hx u).2.2⟩
     unfold cram; by_cases h:u∈Z i
     · rw [if_pos h];unfold A cram; rw [← tsum_mul_right]; exact tsum_congr fun q=> by unfold t; rw [q.property,if_pos h]
     rw [if_neg h];symm; refine (tsum_congr ?_).trans tsum_zero; intro q; unfold t; rw [q.property,if_neg h]
   let t (i:B.Mode):=cram j (fun j=>v j i) r
   refine ⟨hp,t,fun p=>tsum_nonneg (fun i=> hv i.val _),fun i U=> ?_,?_⟩
   · have ht s:Summable (fun x:{i//j i=r}=>F s x.val U):=((Towed.repair (s:=Z∘j) (show Towed _ _ _ _ _ _ from ⟨a,ha,hx,fun i=> ticket (h i) s⟩) hw U).2).comp_injective Subtype.val_injective -- metas S
     unfold Accent.tally; simp_rw [fun s=> Poly.share (ht s)]; exact Scout.infinite (a:=fun x:{i//j i=r}=>v x.val i) ⟨fun _=>hv ..,(he i).comp_injective Subtype.val_injective,le_rfl⟩ hp (fun x=> hY x.val _ U)
   have ht: Summable (fun x=>wordsPrice w (v x)):= ha.of_nonneg_of_le (fun i=>sum_nonneg (fun i' _=>mul_nonneg (Poly.worth hw i').le (hv i _))) hB
   refine le_trans ?_ ((ht.comp_injective (i:=Subtype.val (p:=fun i=>j i=r)) Subtype.val_injective).tsum_le_tsum (fun i=>hB i.val) (ha.comp_injective Subtype.val_injective));unfold wordsPrice t cram; simp_rw [← tsum_mul_left]; apply le_of_eq; rw [Summable.tsum_finsetSum]; intro i _; exact ((he i).comp_injective Subtype.val_injective).mul_left _
-- from h coupons can read even before regroup.Without anchor.Bank.A.
lemma receives (h:Ankh w q F b X p C) (s:sun) : Towed w X (F s) b p C:=by obtain ⟨a,ha,hx,h⟩:= h.beam; exact ⟨a,ha,hx,fun i=> Buoya.ticket (h i) s⟩
end Buoya
end YM.PhysicalNext.Repeat.Luna
