import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MergeProof.North.Menu
import YM.MergeProof.Plaza
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Gala

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}{S:StepData c f}
variable {v:V}{P:V→Motion}{E:V→Site c}{B:V→Equiv.Perm V}
local notation "X"=> Aged V
variable {o:Name V→ Site f}{b:Name V→Site c}
    {L:Name V→ Config G f→ℂ}{K:Name V→ Res G f}{H:Name V→ Res G c}{a t:Bool→ℝ}{g:Name V→ℂ}
    {N:ℕ} {d e u x φ ψ c':ℝ}{w:Name V→ℝ}
    {Y: Config G f→Poly (Aged V)}
local notation "r"=> fun i=> S.ratio.embed (E i)
set_option quotPrecheck false
variable (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o b L K H g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i)))(hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:Bool,w (i,j)=w (v,j)) (hp:∀ i:Bool, let y:Name V:=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (b y) 1 (L y) (K y) (H y) (g y) (a i) (t i) D) (hP:Occupancy o N)(hd:0 ≤ d)(he:u+1 ≤ R.p.supportExponent)(ha:∀ i:Name V,2*w i*a i.snd ≤ d)(hK:∀ i:Name V,w i*t i.snd ≤ x)(hY:e+1 ≤ A.p.supportExponent+2)
variable {σ ι δ p q k:ℝ}(hg:R.Lawful σ δ q p k)(hh: Serves R L K Y v P (fun i=> S.ratio.embed (E i)) B o w u c') (hb:0≤ u)
include hg hh hb hD hs hx π hw hy hp hP hd he ha hK hY
lemma propels (hq: Arsenal R):
    let T:=N*siteFactor R.p.B*d+4*c'
    ∃ (I:Type) (_: Fintype I) (M:I→Hat (Aged V) R), Cohere v P (fun i=> S.ratio.embed (E i)) B π M ∧ Offer o M w R.p.B u (T+Real.exp T*T) ∧ ∃ ψ:Name V→Response G c, Garnish A.p b ψ w e x ∧ relates v P E ψ ∧ (∀ i U, H i U=fun a'=>∑ j,owl (M j) D i U a'+hook A.activities A.p.threshold (ψ i) U a')∧ ∀ U,Y U=Poly.pass (Mach (Aged V) g)*Expense M w S U:=by
   intro τ
   obtain ⟨F,Z,hZ,hF,hB,hz,h0⟩:=hh
   obtain ⟨I,hI,M,ht,hM,θ,hθ,hT,hG,hU,hW⟩:= pool hD hs hx π hw hy hp hP hd he ha hK hY
   obtain ⟨J,hJ,P0,h₂,hH,hP,htP,hA⟩:= dryUp hZ hz hF hB hw hq π hy
   let z:=Sum.elim M P0; let A0:= heap z; have hd0: Offer o z w R.p.B u τ:= hM.cross hP
   have he₀(U): roll z U=Mach X (fun i=>L i U-g i)+∑ i,F i U:=by rw [perfumes,Fintype.sum_sum_type]; exact congr_arg₂ _ (hU U) (htP U)
   have htU(U x): board z x U=Mach X (fun i=>K i x U)+Z x U:=by rw [patron,Fintype.sum_sum_type];exact congr_arg₂ _ (hW ..) (hA ..)
   refine ⟨_,inferInstance,A0,Cohere.cling _ (Cohere.sum _ _ ht h₂), counts z w o R.p.B hw hd0 hb,θ,hθ,hT,fun i U=> ?_,fun U=>?_⟩
   · funext x; rw [show A0=heap z from rfl,freeze,Fintype.sum_sum_type]
     have hp(b):owl (P0 b) D i U x=0:= by unfold owl; apply if_neg; intro h; have hp:=hH b; rw [h] at hp; simp [Census.fire] at hp
     have hh : ∑ b:J,owl (z (Sum.inr b)) D i U x=0:=sum_eq_zero (fun b _=> hp b); rw [hh, show ∑ j:I,owl (z (.inl j)) D i U x=_ from hG i x U,add_zero, sub_add_cancel]
   let s:= Mach X g
   unfold Expense A0; rw [passIn (heap z) S hg hw U, Menu.golden, banded];
   have hW: (roll z U).part (X).quiet=0:=by unfold roll;simp [Poly.part_sum,still z _ U]
   rw [h0]; unfold restore; rw [mul_smul_comm]; let p i:= bar R.activities X U i+board z i U
   rw [← mul_assoc,← Extra.Trajectories.pass_add (x:=s) (y:=roll z U) (mute X g) hW]
   have hy : s+roll z U=Mach X (fun i=>L i U)+∑ i,F i U:=by rw [he₀,← add_assoc]; congr 1; unfold s Mach; rw [← sum_add_distrib]; refine sum_congr rfl fun i _=> ?_; rw [← Extra.Trajectories.send_add,add_sub_cancel]
   rw [hy]; refine congr_arg _ (congr_arg (_*·) (congr_arg (fun l=> field l _) (funext ?_))); intro i; rw [htU]; ring
end YM.MergeProof.Ribbons
