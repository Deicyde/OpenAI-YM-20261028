import YM.FullVolume.Spiral.Chrome
import YM.FullVolume.Gables.Major
/- exact top Voice line and angular cut.Capture. Fixed gaskets and passports.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Bale
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna Tower
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn Extra.Histories.Attach
open UniformSpace FullVolume.Amp
open Beam PaidBeam
variable {R R':Rep G n}
-- local replica exact Stove.F.Free
open Progress.DirectedRecipe
variable {W:Support n}
def fond (R:Rep G n):Rep G n:= { R with activities:= {R.activities with forced:= fun i=> {R.activities.forced i with extraTest:=fun _=>True} } }
def coat (h:HasSlots R.p R.activities) : Shelf (fond R).activities:= let K:=Keeper.sufficient h; ⟨K.code,K.support,K.inventory,fun _ _=>trivial,Keeper.blank h⟩
-- token allocations orientation. `friendly` transport & Eq.Evidence. canonical.I.O plus dimension.
def badge (W:Support n)(q:ℕ)(h:HasSlots R.p R.activities) : Attach.Cluster R W ↪ ℕ:= Attach.stamp (fond R) W (coat h) q
lemma badge_geom (q:ℕ)(h:HasSlots R.p R.activities) (t:Attach.Cluster R W): (R.activities.forced (badge W q h t)).support=Attach.span R W t:= Attach.stamp_x (fond R) W (coat h) q (show Attach.Cluster (fond R) W from t)
lemma there (h:Along R R')(t:Attach.Cluster R W):∃ q':Attach.Cluster R' W,q'.val=t.val:=by
   have hv i: Attach.X R' i= Attach.X R i:=by unfold Attach.X; rw [h.force] -- no goals
   have hp:Attach.coherent R' t.val:=by unfold coherent; simp_rw [hv]; exact t.property.2.1
   exact ⟨⟨t.val,t.property.1,hp,fun i hi=>(hv i).symm ▸ t.property.2.2 i hi⟩,rfl⟩
variable (hS:Along R R') (c: Attach.Cluster R W) (q': Attach.Cluster R' W) (h:q'.val=c.val)
include h hS
lemma markings : Attach.span R W c = Attach.span R' W q' ∧ Attach.debts R W c= Attach.debts R' W q':=by
    have hx: Attach.X R= Attach.X R' :=by unfold Attach.X;rw [hS.force]
    have hs: Attach.I R= Attach.I R':=by unfold Attach.I; rw [hS.force]
    exact ⟨congr_arg (W ∪ ·) (congr_arg₂ Finset.biUnion h.symm hx),congr_arg₂ Finset.biUnion h.symm hs⟩
lemma numbering (hr:HasSlots R.p R.activities)(ht:HasSlots R'.p R'.activities)(k:ℕ): badge W k hr c=badge W k ht q':=by
    let x:Attach.Cluster (fond R) W:=c; let y:Attach.Cluster (fond R') W:=q'
    have h' :=markings hS c q' h; let u:=(coat hr).name; let v:=(coat ht).name
    change u (codeId (fond R) W k x) = v (codeId (fond R') W k y); rw [show u=v from rfl]; apply congr_arg v; unfold codeId; congr 1; · exact Subtype.ext (Prod.ext h'.1 h'.2)
    congr 2; exact h.symm
omit hS h
variable (F)
abbrev TopY (S:SectionData F)(R:Rep G n)(H:HasSlots R.p R.activities) (k:ℕ) := born S (fond R) (0:Site n) (coat H) k
lemma bingo (S:SectionData F)(H:History G)(N p:ℕ)(h:HasSlots (H.rep N p N).p (H.rep N p N).activities)(k:ℕ): (Guard.summit F S H N p _ (Keeper.blank h) k).plays = TopY F S (H.rep N p N) h k:= rfl
lemma tube2 (S:SectionData F)(R:Rep G n)(H:HasSlots R.p R.activities)(t:F.Coeff)(k:ℕ)(c:Attach.Cluster R (S.footprint (0:Site n))): (TopY F S R H k t).forced (badge _ k H c)= Attach.chunk R _ c (supplement S R 0 t):= by exact line_stamp (fond R) _ (coat H) k _ _ -- type mismatch
lemma blank1 (S:SectionData F)(R:Rep G n)(H:HasSlots R.p R.activities)(k:ℕ)(t:F.Coeff)(j:ℕ)(hx:j∉ Set.range (badge (S.footprint (0:Site n)) k H)) : (TopY F S R H k t).forced j=0:= by exact line_empty (fond R) _ (coat H) _ _ hx
section multi
lemma tint {v:ℝ}{z:sun→ℝ}(h:PaidBeam z v): PaidBeam (fun i:sun=> (z i:ℂ)) v:= by simpa using (transit _ (map_sub Complex.ofRealCLM) zero_le_one (fun i=> (Complex.norm_real i).le.trans_eq (one_mul _).symm) z h)
lemma strum {p q:sun→ ℂ} (h:PaidBeam p v)(hv:PaidBeam q s): PaidBeam (fun i=> p i*q i) (v*s):=by
   obtain ⟨P,hp,hq⟩:=h.arrives; obtain ⟨Q,hZ,hX⟩:=hv.arrives; let A:= ContinuousLinearMap.mul ℝ ℂ; refine ⟨brave A P Q,(braveN ..).trans ((mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (ContinuousLinearMap.opNorm_mul_le ..)).trans (mul_le_mul hp hZ (norm_nonneg _) (PaidBeam.price h))),fun i=>?_⟩
   rw [harp,hq,hX]; exact rfl
lemma funds {ι:Type}(T:Finset ι)(f:ι→ sun→ℂ)(x:ι→ℝ)(hf:∀ i,PaidBeam (f i) (x i)): PaidBeam (fun j=>∏ i∈T, f i j) (∏ i∈T, x i):=by
    induction T using Finset.induction_on with
    | empty => simpa using static (1:ℂ)
    | insert i T hi ih=> simp_rw [prod_insert hi]; exact strum (hf i) ih
-- combined newsletter.Y Stam.
end multi
end YM.FullVolume.Paint.Bale
