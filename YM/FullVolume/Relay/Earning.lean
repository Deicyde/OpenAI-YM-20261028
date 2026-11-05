import YM.FullVolume.Relay.Coffers
/-!
 # budgets in terms of denominators, stage-local currency conditions

 Define currencies exactly. All Radius params affordable in a histogram to
 be paid separately. No hidden poly estimates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign.Face
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I] (d:I→ℕ)(x:(i:I)→((Labels.frames G).level (d i)).Coeff)
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ)
variable (m N p :ℕ)
-- check implicit θ order
namespace Economics
open Marker
variable {b:ℕ} (B:Marker.Census I)(o:∀ i,I→Site (R.alloy.B.a.S.side i p))
variable (h: Economics T Θ v d x b m)
local notation "Bt"=> (R.alloy.B.a.budget m).B
local notation "t_"=> timeEntry R
local notation "Y"=> fundsY R b
local notation "P₀"=> (mintOut R m)⁻¹
local notation "ψ"=> mintOut R m
open Budget
variable (hp: Economics T Θ v d x b (m+1))(hq:Extra.Multi.Occupancy (o m) 1)
variable (hw:((R.alloy.B.a.clock.op m p).ratio.parent ∘ o (m+1))=o m)
variable (j:ℕ) (hj:m ≤  j) (hm:m<N)
local notation "P₁"=> kernelW R b
local notation "Pμ"=>kernelU R b
lemma pilot_le i: kernelU R b j m (i:I)  ≤  fundsY R b (j+1)^2:=by unfold kernelU; rw [pow_two]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (one_fund ..)); rw [div_le_iff₀ (zero_lt_one.trans_le (one_fund ..))]; exact le_mul_of_one_le_right (zero_le_one.trans (one_fund ..)) (one_fund ..)
include hj hp
lemma pilot_wins (i:I): kernelW R b j i * kernelU R b j m i  ≤  creditP (timeEntry R (m+1)):= by
     refine (mul_le_mul_of_nonneg_left (pilot_le m j i) (wt j i|>.le)).trans (Budget.forest (h:=time_ge T d x Θ v _ hp) (hp:=one_fund ..) ?_); exact hp.upBound.trans (lighter _ (by omega))
omit hj
include hw h hm hq
lemma thumb : Crossing T N p Θ v B d x o (energyW R b) (heightP R) (kernelW R b m) (kernelU R b m) m hm:=by
     obtain ⟨a,ha⟩:=h.ability N p hm; have hW(i:I): kernelW R b m i  ≤  energyW R b (m+1) i:= pow_le_pow_of_le_one (a:=((fundsY R b (m+1))⁻¹)) (by exact inv_nonneg.mpr (zero_le_one.trans (one_fund ..))) ((inv_le_one₀ (zero_lt_one.trans_le (one_fund ..))).mpr (one_fund ..)) (by decide)
     have ht :Repegs (o (m+1)) (R.alloy.B.a.budget (m+1)).B (energyW R b (m+1)) (kernelW R b m) 0 1 B:=by
        intro i hi X hX; rw [zero_mul,Real.exp_zero,mul_one,one_mul]; exact Finset.prod_le_prod (fun i _=> wt _ i|>.le) (fun i _=>hW i)
     refine ⟨a,_,⟨ha,hq, hw,wv m m⟩,ht,?_⟩
     refine fareMerge (wt m) (wv m m) (fun i=>?_) (pilot_wins T d x Θ v m hp m le_rfl) hp.big
     unfold kernelU; rw [div_self (zero_lt_one.trans_le (one_fund ..)).ne',mul_one]; exact h.fundsE i
include hj
lemma down (hD:Drake B (R.alloy.B.a.budget (m+1)).B (o (m+1))): Underway T N p Θ B o (heightP R) (kernelW R b j) (kernelU R b j) m hm:=by
     obtain ⟨a,ha⟩:= h.ability N p hm; refine ⟨a,_,_,⟨ha,hq,hw,wv m j⟩,noSwap T d x Θ v _ p B o hp _ (wt j) hD, inv_nonneg.mpr (Real.exp_pos _).le,hp.height,hp.heights,?_⟩
     let Yj:= fundsY R b (j+1)
     intro L
     refine fareMerge (wt j) (wv m j) (fun i=> (hp.doubles _ (wv (m+1) j i)).trans_eq ?_) (pilot_wins T d x Θ v m hp j hj) hp.big
     unfold kernelU; rw [changeling b (m+1)]
     have he : changeA R b (m+1)≠ 0:= (zero_lt_one.trans_le (one_change ..)).ne'
     field_simp
omit hw hm hq
include h
lemma tributeEnd (hX : Economics T Θ v d x b j): ∑ i:I,kernelW R b j i * (quoteUnit T j (d i) ‖x i‖+tariffLog T Θ m (Fintype.card I) (kernelU R b j m i))  ≤  1:=by
    let Yj:=fundsY R b (j+1); have hp:1 ≤ Yj:=one_fund ..
    have he:0<Yj:=zero_lt_one.trans_le hp
    let u:= Yj⁻¹ ^6; have hz:0<u:=pow_pos (inv_pos.mpr he) _; let c0:= Fintype.card I; let W':= civic c0
    have h₀ : kernelW R b j=fun _:I=> u:=rfl
    have ht:u*Yj  ≤  1:=by
       unfold u; rw [pow_succ,mul_assoc,inv_mul_cancel₀ he.ne',mul_one]; exact pow_le_one₀ (inv_nonneg.mpr he.le) ((inv_le_one₀ he).mpr hp)
    have hk:u*(Yj*(Yj^2))  ≤  1:=by
       unfold u; field_simp; nlinarith only [hp,pow_pos he 2,pow_pos he 4,pow_pos he 3] -- check
    have hG :changeA R b m  ≤  Yj:=le_trans (b:=fundsY R b (m+1)) (by rw [changeling]; exact le_mul_of_one_le_left (zero_le_one.trans (one_change ..)) (one_fund ..)) (lighter b (by omega : m+1  ≤  j+1))
    simp_rw [mul_add,Finset.sum_add_distrib]; apply le_trans (b:=((c0:ℝ)/W'*1)+((c0:ℝ)/W'*1)) _ ?_ -- goal ordering
    · apply add_le_add (fareGroup (wt j) hX.fundsU (fun _=>ht))
      exact fareGroup (wt j) (fun i=> le_trans (h.spends _ (wv m j i)) (mul_le_mul hG (pilot_le m j i) (wv m j i|>.le) he.le)) (fun _=>hk)
    simp only [mul_one]; have hh:(c0:ℝ)/W'  ≤  1/128:= eighth; linarith
end Economics
-- geometry.E. needs across levels only.View scaffolding.
local notation "Bv"=> R.alloy.B.a.budget
variable (B:Marker.Census I)(o:∀ i,I→Site (R.alloy.B.a.S.side i p))
structure Course (j:ℕ):Prop where
   populated i : m  ≤  i → i ≤ N→ Extra.Multi.Occupancy (o i) 1
   price i : m  ≤  i → i  ≤  N → Drake B (R.alloy.B.a.budget i).B (o i)
   map_region i:j+1  ≤  i→ i <N→∀ a:I,o (i+1) a=(R.alloy.B.a.clock.op i p).ratio.embed (o i a)
   along i : m  ≤  i→i  ≤  j→ ((R.alloy.B.a.clock.op i p).ratio.parent ∘ o (i+1))=o i
open Economics
variable (b:ℕ)
set_option maxHeartbeats 380000 in
lemma permitsTour (h: ∀ i:ℕ,m  ≤  i→ Economics T Θ v d x b i)(j:ℕ)(hp:m  ≤  j)(hj:j<N)(hF:Course m N p B o j):
    Ride T Θ v B d x (energyW R b) (heightP R) (kernelW R b j) (kernelU R b j) N p o m j hj ∧ ∑ i:I,kernelW R b j i*(quoteUnit T j (d i) ‖x i‖+tariffLog T Θ m (Fintype.card I) (kernelU R b j m i))  ≤  1:=by
    have ht : m<N:=hp.trans_lt hj
    refine ⟨⟨fun _ _ _=>wk _,hF.map_region, ⟨_,_, speakTop T d x Θ v N p B o (h N ht.le) (hF.price N ht.le le_rfl)⟩,fun i hi hh=> ?_, wt j, thumb T d x Θ v j N p B o (h j hp) (h (j+1) (hp.trans j.le_succ)) (hF.populated _ hp hj.le) (hF.along j hp le_rfl) hj,fun i hq hV=>?_⟩,tributeEnd T d x Θ v m (h m le_rfl) (h (m+1) m.le_succ) j hp (h j hp)⟩
    · have hp': m ≤ i:= by omega
      exact Economics.next T d x Θ v i N p B o (h i hp') (h (i+1) (hp'.trans i.le_succ)) hh (hF.price i hp' hh.le) (hF.populated i hp' hh.le)
    exact down T d x Θ v i N p B o (h i hq) (h (i+1) (hq.trans i.le_succ)) (hF.populated i hq (hV.trans hj).le) (hF.along _ hq hV.le) _ hV.le (hV.trans hj) (hF.price _ (hq.trans i.le_succ) ((show i+1  ≤  j from hV).trans hj.le))
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.permitsTour
