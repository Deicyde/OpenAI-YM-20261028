import YM.Next.MULTISOURCE.Ends
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Urb
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt
import YM.Push.LOCAL_SPLITTING.Response
/-! # Budgetary pitch: translation and inverse weighting through Seat.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {χ : Chi} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
section sym
abbrev spin (v:Seat c): Equiv.Perm (Site c):= StepData.sendSites v.1 v.2
def atlas (S: Site c→ Config G c→ℝ) (s:Site c) (V:Config G c):= Pond.likely (fun θ:Seat c=> S ((spin θ).symm s) (θ.view V))
lemma astrolabe (S: Site c→ Config G c→ℝ) (s:Site c) (V:Config G c) (θ:Seat c): atlas S s (θ.view V)=atlas S (spin θ s) V:= by
  symm; apply likely_congr (Seat.move θ.1 θ.2); intro i; congr 1
  · let q:= Seat.move θ.1 θ.2 i; apply (Meadow.spin q|>.symm_apply_eq).2
    have h x : spin q x=spin θ (spin i x):= by change Lattice.affine (θ.1*i.1) (Lattice.affine θ.1 θ.2 i.2) x=_; change _=Lattice.affine θ.1 θ.2 _; change _= θ.1.act (i.1.act x+i.2)+θ.2; unfold Lattice.affine; simp only [Signed.act_mul,Signed.act_add,add_assoc]
    rw [h,Equiv.apply_symm_apply]
  exact congr_fun (Seat.view_move i θ.1 θ.2) V
variable (hC : C.val=c.val*M) (U:Config G c) (Y:PathData G) (y:Clip) (β γ:ℝ)
local notation "x'" => (Macrame.splitter (Deck.divides hC))
local notation "L" => normal (Deck.divides hC) hC

def pinch (θ:Seat C):Seat c:=(θ.1,x' θ.2)
lemma charts (θ:Seat C) (x:Site C) : x' (spin θ x)=spin (pinch hC θ) (x' x):= by change x' (θ.1.act x+ θ.2)=_+_; rw [map_add,← usual]; rfl
lemma inverts (θ:Seat C) (x : Site C): x' ((spin θ).symm x) = (spin (pinch hC θ)).symm (x' x):= by
  rw [Equiv.eq_symm_apply]; rw [← charts, Equiv.apply_symm_apply]
lemma estuary (θ:Seat C): θ.view ((L).links U)= (L).links ((pinch hC θ).view U) := by
  funext i; unfold Seat.view Lattice.pull; unfold Macrame.Window.links; dsimp only
  change (Lattice.Step.read _ ((L).links U) _) = _; rw [Macrame.Window.read]; rw [show (L).cut (Lattice.affine θ.1 θ.2 i.1)=_ from charts hC θ i.1]; rfl
lemma nest_sound (s:Signed) (i:Rags) (x:Site C): Meadow.spurs Y y β γ s i x ((L).links U)=Meadow.spurs Y y β γ s i (x' x) U:= by
  let a:Seat C:=(s,x); let q:=a.view ((L).links U); let v:=(pinch hC a).view U; have hx:q= (L).links v:= estuary hC U a
  have he P : Slot.atSite P q 0=Slot.atSite P v 0:= by rw [hx]; unfold Slot.atSite; rw [(L).expansion, show (L).cut 0=0 from map_zero (x')]
  have hE (n:ℕ) (s: ℕ→Atom G n) (t:ℝ) (i:ℕ): tuneAtom s t (a,i) ((L).links U)=tuneAtom s t (Meadow.pinch hC a,i) U:= congr_arg (fun x=>VerifiedReset.factor*t* x) (congr_arg (Atom.poly (s i)) (funext (fun j=> he ((s i).leg j))))
  rcases i with i|i|i|i
  · apply congr_arg (fun t:ℝ=> VerifiedReset.factor*(-γ)*(i.mark Y y*t)) -- multiplication defeq tuneLow ??
    unfold Low.plain; cases e : i.2
    · refine congr_arg G.price ?_; change faceValue q _= _; rw [hx]; exact Eq.trans (mirror (divides hC) hC ..) (congr_arg (faceValue v) (Prod.ext (map_zero x') rfl))
    exact congr_arg₂ (fun a b:G.Color=>inner ℝ a b/2) (he _) (he _)
  · exact hE _ Y.cubic _ i
  · exact hE _ Y.quartic _ i
  exact hE _ Y.loop _ i
lemma garner_pack (n k:ℕ) (x:Site C): Meadow.garner Y y β γ n k x ((L).links U)=Meadow.garner Y y β γ n k (x' x) U:= by unfold garner; simp_rw [nest_sound]

lemma revolving (f : Seat c→ℝ) : likely (fun θ=> f (pinch hC θ))=likely f:= by
  have hv : 0 < M := by have he:= C.property; change 0<C.val at he; rw [hC] at he; exact Nat.pos_of_mul_pos_left he
  unfold likely pinch; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; dsimp only; rw [Fintype.card_prod,Fintype.card_prod]
  have he k : (∑ i : Site C,f (k,x' i))=(M^4) • ∑ i : Site c,f (k,i):= Shingle.multiplied (x') (basefold _ hC) (fun i=> f (k,i))
  simp_rw [he,nsmul_eq_mul,← mul_sum]; rw [site_card,site_card,hC]; push_cast; field_simp
end sym
end YM.PhysicalNext.Repeat.Meadow
