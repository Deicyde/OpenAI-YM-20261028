import YM.FullVolume.Relay.Budget
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
lemma wk m i: 0 < energyW R b m (i:I):=pow_pos (inv_pos.mpr (zero_lt_one.trans_le (one_fund ..))) _
lemma wt (j:ℕ)(i:I): 0 < kernelW R b j i:= pow_pos (inv_pos.mpr (zero_lt_one.trans_le (one_fund ..))) _
lemma wv (j:ℕ)(i:I):0< kernelU R b j m i:=by unfold kernelU; exact mul_pos (zero_lt_one.trans_le (one_fund ..)) (div_pos (zero_lt_one.trans_le (one_fund ..)) (zero_lt_one.trans_le (one_fund ..)))
include h
lemma time_ge : 1 ≤ timeEntry R m:= le_trans (by norm_num) h.big
lemma payS (w w':I→ℝ)(hw:∀ i,0<w i)(hw':∀ i,0<w' i)(ht:∀ i,w' i≤w i*ψ) (hq:Drake B (R.alloy.B.a.budget m|>.B) (o m)): Repegs (o m) (R.alloy.B.a.budget m|>.B) w w' 2 (mintOut R m)⁻¹ B:=by
    let b:ℕ:=Bt; let p':=(1:ℝ)/2
    have hp:= hq.palms ht hw' hw h.support
    intro i hi X hX; let y:= Poly.toll w i; let C0:=coverNumber b X
    have hV : (b:ℝ)*i.val.card ≤ 64*(coverNumber b X:ℝ):= by exact_mod_cast Work.I01.answer _ _ (o m) _ h.support _ (hq.spread i hi) hi X hX
    refine (hp i hi X hX).trans ?_
    rw [one_mul]; change y*Real.exp _ ≤ (Real.exp ((b:ℝ)/128))⁻¹*y*Real.exp (2* (C0:ℝ))
    rw [mul_comm _ y,mul_assoc,← Real.exp_neg,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (Poly.worth hw i).le; apply Real.exp_monotone
    have hz:(2:ℝ) ≤ i.val.card:= by exact_mod_cast hi
    change p'*(C0:ℝ)≤ -((b:ℝ)/128)+2*(C0:ℝ); change (b:ℝ)*i.val.card≤64*(C0:ℝ) at hV; unfold p'; linarith only [hV, mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg b)]
local notation "WC"=> civic (Fintype.card I)
lemma noSwap (w:I→ℝ)(hw:∀ i,0<w i)(hq:Drake B (R.alloy.B.a.budget m).B (o m)): Repegs (o m) (R.alloy.B.a.budget m).B w w 2 (mintOut R m)⁻¹ B:=by
    apply payS T d x Θ v m p B o h w w hw hw (fun i=>?_) hq -- argument order test
    exact le_mul_of_one_le_right (hw i|>.le) ((one_le_pow₀ (one_change b m)).trans h.more)
lemma changeSwap (hq:Drake B (R.alloy.B.a.budget m|>.B) (o m)): Repegs (o m) (R.alloy.B.a.budget m|>.B) (energyW R b (m+1)) (energyW R b m) 2 P₀ B:=by
    apply payS T d x Θ v m p B o h _ _ (wk (m+1)) (wk m) (fun i=>?_) hq
    apply le_trans _ (mul_le_mul_of_nonneg_left h.more (wk (m+1) i|>.le)); unfold energyW; rw [changeling]
    have ht := zero_lt_one.trans_le (one_change (R:=R) b m); rw [mul_inv_rev, mul_pow]; field_simp; rfl
open Budget
lemma speakTop (hD:Drake B (R.alloy.B.a.budget m).B (o m)): CloseCap T m p B d x o (energyW R b m) (creditP (timeEntry R m)) (heightP R m) (mintOut R m)⁻¹ :=by
    have h1 : 1 ≤ timeEntry R m:= time_ge T d x Θ v m h; have hH:0<timeEntry R m:= zero_lt_one.trans_le h1
    refine ⟨?_, h.covered, inv_nonneg.mpr (Real.exp_pos _).le, noSwap T d x Θ v m p B o h _ (wk m) hD, pow_nonneg (inv_nonneg.mpr hH.le) _, h.crowned, sub_nonneg.mpr h.expQ⟩
    apply le_trans (fareGroup (wk m) h.fundsT (fun i=> economy h1 (one_fund ..) h.upBound))
    exact mul_le_of_le_one_left (by unfold creditP; positivity) ((eighth (I:=I)).trans (by norm_num))
lemma next (hp: Economics T Θ v d x b (m+1))(hm : m<N)(hD:Drake B (R.alloy.B.a.budget m).B (o m))(hQ:Extra.Multi.Occupancy (o m) 1):∃ s s' c V, AlignedStep T N p Θ v B d x o (energyW R b) (heightP R) m hm s s' c V:=by
    obtain ⟨u,hU⟩:= h.ability N p hm; have he := h.upBound; have hw :1 ≤ timeEntry R (m+1):=le_trans (by norm_num) hp.big; have hw':0<timeEntry R m:= lt_of_lt_of_le (by norm_num) h.big; let Yp:=Y (m+1); let X' i:= energyW R b (m+1) (i:I); let ht :∀ i,0<X' i:= wk _
    have hL(i): X' i*Yp ≤ creditP (timeEntry R (m+1)):= economy hw (one_fund ..) hp.upBound
    have hC: creditP (t_ (m+1)) ≤ creditP (t_ m):= pow_le_pow_left₀ (inv_nonneg.mpr (zero_le_one.trans hw)) (inv_anti₀ hw' h.monotoneB) _
    let k:=Fintype.card I; have hh (i:I):0<Yp:= zero_lt_one.trans_le (one_fund ..)
    refine ⟨_,_,_,fun _=>Yp,⟨hU,hh,hQ, fareMerge ht hh h.fundsE hL hp.big, ⟨_,?_,h.capital,h.height,h.issued⟩,inv_nonneg.mpr (Real.exp_pos _).le,changeSwap T d x Θ v m p B o h hD⟩⟩
    exact (fareGroup ht h.fundsK (fun i=>hL i|>.trans hC)).trans (mul_le_of_le_one_left (sq_nonneg _) ((eighth (I:=I)).trans (by norm_num)))
end Economics
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Economics.next
