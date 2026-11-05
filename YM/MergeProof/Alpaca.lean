import YM.Further.DENSE_MIXED_KERNELS.AtWork
import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.MergeProof.Tongue
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p : ℕ)
variable {n:Side}
private abbrev glass (A:Activities G n) := { A with forced:=fun i=> {A.forced i with extraTest:=fun _ => True} }
private abbrev glassPlate (R:Rep G n):Rep G n:={R with activities:=glass R.activities}
private def bar {R:Rep G n} (K:Guard.Keeper R.p R.activities)(h:∀ s,R.activities.K (K.code s)=0): Shelf (glassPlate R).activities:=⟨K.code,K.support,K.inventory,fun _ _=> trivial,h⟩
-- actual flags exact. sums not estimated here. price supplement unres. need global later.
def booster (B:SectionData F)(R:Rep G n)(o:Site n)(v:F.Coeff): MergeProof.Response G n:= Pi.single (B.footprint o) (supplement B R o v)
section calf
variable {A:Hol G}{R:Rep G n}(S:Shelf R.activities)(q:ℕ)(v:F.Coeff)(o: Site n)
private def packet (T:Support n)(s: Attach.Cluster R T): Pack R.activities T:= ⟨s.val,s.property.1,s.property.2.1,fun i hi=>fun h=> s.property.2.2 i hi h.symm⟩
private def resolve (T:Support n)(s: Pack R.activities T):Attach.Cluster R T:= ⟨s.val,s.property.1,s.property.2,fun i hi=> fun h=> s.property.hits i hi h.symm⟩
lemma cash (h:Dominated ((born B R o S q v).forced)) : profile R.activities (born B R o S q v).forced= hook R.activities R.p.threshold (booster B R o v):=by
   let p := B.footprint o; let X:Unit→Support n:= fun _=>p; let c:= supplement B R o v; let f:Unit→ Config G n→ℂ:= fun _=> c
   let Z(s: Letters R.activities X):Attach.Cluster R p:= resolve p s.2
   let Z'(s: Attach.Cluster R p):Letters R.activities X:= ⟨(),packet p s⟩
   have hh s:Z (Z' s)=s:=rfl; have hp:LeftInverse Z' Z:= by rintro ⟨⟨⟩,i⟩; rfl
   let e:Letters R.activities X↪ℕ:= (⟨Z,hp.injective⟩:Letters R.activities X↪Attach.Cluster R p).trans (Attach.stamp R p S q)
   have hx:clipSum X f= booster B R o v:=by funext i U;unfold clipSum booster; rw [expand_eq,tsum_fintype]; by_cases hi:i=B.footprint o <;> simp [X,hi,p,f,c,Pi.single_eq_of_ne, eq_comm] -- check
   rw [← hx]; apply toll (e:=e) (fun i=> Prod.ext (Attach.stamp_x R p S q (Z i)) (Attach.stamp_i R p S q (Z i))) (fun i U=> ?_) (fun i h=> ?_) h
   · rcases i with ⟨u,b⟩; let b': Letters R.activities X:= ⟨u,b⟩; change Attach.line R p S q c _ _= _; rw [show e _= Attach.stamp R p S q (Z b') from rfl,Attach.line_stamp]
     unfold Attach.chunk; let s:Pack R.activities p:= b
     have ht: grasp R.activities R.p.threshold (X u) b.val (fusionBox R.activities (X u) b.val) U= if Attach.span R p (Z b')∩flags R.p.threshold U= Attach.debts R p (Z b') then ∏ i∈b.val, (R.activities.K i U:ℂ) else 0:=by
         rw [grasp_pack R.activities R.p.threshold b]; simp only [true_and]; rfl -- fusion proof Packs symmetrical
     change _= c U*grasp _ _ (X u) b.val (fusionBox _ (X u) b.val) _; rw [ht];split_ifs; rfl;rw [mul_zero]
   apply Attach.line_empty;rintro ⟨b,hb⟩;exact h ⟨Z' b,hb⟩
end calf
variable (K:Keeper ((H.rep N p N).p) (H.rep N p N).activities)(h: ∀ s,(H.rep N p N).activities.K (K.code s)=0)(q:ℕ)
local notation "R"=> H.rep N p N
local notation "V"=> Guard.summit F B H N p K h q
lemma onRise (v:F.Coeff)(hh:Dominated (((V).plays v).forced)): profile (R).activities ((V).plays v).forced= hook (R).activities (R).p.threshold (booster B R 0 v):=by
   have hp:= (cash B (bar K h) q v (0:Site (H.S.side N p)) hh)
   convert hp using 1
   · rfl
   funext i U; unfold hook; apply Finset.sum_congr rfl
   intro p' hv; congr 1
   unfold portion; refine tsum_congr fun K=>?_
   unfold grasp; split_ifs with h h'
   · rfl
   · exact (h' ⟨⟨h.1.1,h.1.2,h.1.3⟩,h.2⟩).elim
   · rename_i h';exact (h ⟨⟨h'.1.1,h'.1.2,h'.1.3⟩,h'.2⟩).elim
   rfl -- hook.grasp.Decidable may fail
end YM.MergeProof
