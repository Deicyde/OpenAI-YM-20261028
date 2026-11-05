import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
import YM.TraceExtension.Cask.Common
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function
open scoped Topology BigOperators Classical ContDiff
variable {V I:Type}[DecidableEq I]{G:Gauge}{n:Side}
abbrev Fleece:= High ⊕ ℕ
def rowD : Fleece→ℕ := Sum.elim High.arity (fun _=>2)
def tooth (R:Rep G n): (d:Fleece)→ Atom G (rowD d) := Sum.rec (High.term R.path) R.path.loop
abbrev Barley := Low ⊕ Fleece
abbrev Badge (n:Side):= (Seat n × Barley) ⊕ ℕ
def wake (R:Rep G n) : Barley→ ℝ := Sum.elim (fun _=>R.beta) (Sum.elim (fun _=>R.beta) (fun _=>1))
def fort (R:Rep G n) : Barley → Support n:= Sum.elim (fun a=> a.home R.path R.p 0) (fun d=> (tooth R d).footprint 0)
def coal (R:Rep G n):Barley→ Config G n→ℝ:=Sum.elim (fun a=> a.live R.path R.clip R.p 0) (fun d U=> (tooth R d).placed R.p U 0)
def chore (R:Rep G n)(t:Barley)(U:Config G n):ℝ:= wake R t * coal R t U
def boothC (R:Rep G n) : Badge n→ Support n:= Sum.elim (fun i=>i.1.spread (fort R i.2)) (fun i=> (R.activities.reg i).support)
def pieceC (R:Rep G n) : Badge n → Config G n→ℝ:= Sum.elim (fun i U=> - VerifiedReset.factor * chore R i.2 (i.1.view U)) (fun i U=> - R.activities.regularOccurrence R.p i U)
variable (R:Rep G n) {σ A u v e:ℝ} (hp:R.Lawful σ A u v e)(h: VerifiedReset.Geo.Width R.p R.clip σ)
local notation "P!"=> R.p
local notation "C!"=>R.path
local notation "y"=>R.p.threshold
local notation "U!"=>R.activities
lemma all_loop (U : Config G n): layer (fun i : ℕ => coal R (.inr (.inr i))) U= R.path.inChannels R.clip R.p 0 U :=by
    unfold layer PathData.inChannels PathData.principal; simp only[zero_mul,zero_add,Fintype.sum_prod_type]; apply congr_arg (VerifiedReset.factor * ·); apply sum_congr rfl; intro i _
    rw [← Equiv.sum_comp i.actEquiv.toEquiv]; apply sum_congr rfl; intro b _
    have hv: Seat.view (i,i.act b) U= Lattice.translate b (pull i 0 U):=by rw [← pull_one,pull_pull]; simp only [mul_one,affine,add_zero]; rfl
    apply tsum_congr; intro j; let T:=R.path.loop j; change T.placed P! (Seat.view (i,i.act b) U) 0 = T.placed P! _ b; rw[hv]
    unfold Atom.placed; rw [← pull_one,Push.Local.masked_pull,show (T.footprint 0).image (Push.Local.turnSites 1 b)=T.footprint b from ?_]; swap
    · unfold Atom.footprint; simp [Finset.image_image,comp_def,show ⇑(Push.Local.turnSites 1 b) = affine 1 b from rfl,affine]
    apply congr_arg (fun f=> masked R.p.threshold _ f _); funext V; simp [comp_apply,pull_one,Atom.unmasked,Slot.atSite,Push.Local.expand_translate]
include hp h
lemma lowCast (U:Config G n): Summable (fun i:Low=>coal R (.inl i) U):=by
    -- low certificate
    exact Low.live_sum hp.paths h ..
lemma felt (U:Config G n): Summable fun i:Fleece=> (wake R (.inr i))* coal R (.inr i) U:=by
    apply Summable.sum
    · exact (summit_sum hp.paths _ _ 0).mul_left _
    let f(i):= (R.path.loop i).placed P! U 0; have hx: Summable f:=(PathData.atom_dominated R.path.loop R.p 0 hp.paths.width hp.paths.two).summable _
    exact hx.mul_left _
lemma songE (U:Config G n): Summable (fun i=>pieceC R i U):=by
   apply Summable.sum
   · refine (Summable.mul_left (-VerifiedReset.factor) (f:=fun i:Seat n × Barley=>chore R i.2 (i.1.view U)) (Summable.of_norm ((summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr ⟨fun i=>(Summable.norm ?_), Summable.of_finite⟩)))
     exact Summable.sum (fun t:Barley=>chore R t (i.view U)) ((lowCast R hp h _).mul_left _) (felt R hp h _)
   exact ((Activities.ESeries hp.labels).summable U).neg
lemma seedE (U:Config G n): R.exponent U= R.v* Fintype.card (Site n)+(∑' i,pieceC R i U):=by
    have hi := true_base hp.paths h U
    have hq:=songE R hp h U; rw [Summable.tsum_sum (f:=fun i=>pieceC R i U) (hq.comp_injective Sum.inl_injective) (hq.comp_injective Sum.inr_injective)]
    have hh(x:Seat n): (∑' i:Barley,chore R i (x.view U))=(R.beta*( (∑' i:Low, Low.live R.path R.clip i R.p 0 (x.view U)) + (∑' i:High,summit R.path R.p i 0 (x.view U)))) + (∑' i:ℕ, (R.path.loop i).placed R.p (x.view U) 0):=by
       let v:=x.view U; rw [Summable.tsum_sum (f:=fun t=>chore R t (x.view U)) ((lowCast R hp h v).mul_left _) (felt R hp h v),Summable.tsum_sum (f:=fun i:Fleece=>chore R (.inr i) v) ((felt R hp h v).comp_injective Sum.inl_injective) ((felt R hp h v).comp_injective Sum.inr_injective)]; change _+((∑' i:High,R.beta*summit R.path R.p i 0 v)+∑' i:ℕ,1*(_:ℝ))= _; change (∑' i:Low,R.beta*Low.live _ _ _ _ _ _)+_=_; simp only [tsum_mul_left,one_mul]; dsimp only[v]; change _= _; unfold coal; unfold summit; rw [mul_add,add_assoc]; rfl
    let f i:= R.activities.regularOccurrence R.p i U
    change R.exponent U= _+((∑' i: Seat n × Barley,- VerifiedReset.factor * chore R i.2 (i.1.view U))+∑' i,- f i);
    simp only [neg_mul,tsum_neg]; rw [← layer_total, Rep.exponent, Push.BetaTransport.channels_split, ← hi,← all_loop]
    · unfold layer; simp_rw [hh]; simp only[Finset.sum_add_distrib,← Finset.mul_sum];change _ - R.activities.additive R.p U= _+( -(VerifiedReset.factor * (R.beta * ((_:ℝ)+(_ : ℝ)) + (∑ i:Seat n,∑' j:ℕ, coal R (.inr (.inr j)) (i.view U)))) + - (R.activities.additive R.p U)); ring
    intro W; exact Summable.sum _ ((lowCast R hp h _).mul_left _) (felt R hp h _)
end YM.Trace.Shepherd
