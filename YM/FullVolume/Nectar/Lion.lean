import YM.FullVolume.Nectar.Sable
import YM.FullVolume.Nectar.Keys
import YM.FullVolume.Nectar.Bower
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 360000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V] {W Z:Type} [SeminormedAddCommGroup W][NormedSpace ℝ W]
open Luna Frets Empire Imago
local notation "𝒬" => Board (A:=A) N m n T
open MergeProof.Menu Extra.Trajectories Lotus
open FullVolume.Ray
section swap
variable {B:Marker.Census V} {J:Type} [Fintype J] {f c:Side} {R:Rep G f}
variable (d:I≃J) (x:I→Hat B R) (y:J→ Hat B R) (hy:∀ i,x i=y (d i))
private lemma spending' {σ C κ χ ψ :ℝ}(hp: R.Lawful σ C κ χ ψ)(p:StepData c f)(w:V→ℝ)(hv:∀ i,0<w i) (h:∀ i,x i=y (d i)): Expense x w p=Expense y w p:=by
   funext U
   have he i:rush x i U=rush y i U:=by unfold Menu.rush; simp_rw [h]; exact d.sum_comp (fun j=>if WKey (y j)=i then amount (y j) U else 0)
   have hh:logDeck x=logDeck y:=by
      ext i; rw [cams,cams]; simp_rw [h]; exact Equiv.exists_congr_right (q:=fun j=> WKey (y j)=Wing.logKey i) d
   unfold Expense; rw [passIn x p hp hv, passIn y p hp hv]; let j x:= Real.exp x
   unfold Menu.jets board; simp_rw [hh,he]
end swap
namespace Orchard
variable {B: Marker.Census V}(Xk:Orchard N m n T B I W) (x p: Board (A:=A) N m n T)
local notation "X₀"=> Xk.hat p 0
local notation "T!" => Xk.colony p
local notation "S'"=> Q
variable {t v:ℝ}{w:V→ℝ}{b:V→ℝ}{o:V→Site (A.B.a.S.side (m+1) n)}
variable (hw:∀ i,0<w i)(hp:Xk.Ensues w o t b)
include hp hw
lemma reins (he:0 ≤ (A.B.a.budget (m+1)).supportExponent-4) (hs:t+Real.exp t*t≤ v): (Xk.colony p).Ensues w o v b:=by
    refine ⟨?_,?_,?_⟩
    · intro r q x; let f' (t:sun) i:=(Xk.colony p).orbit x (r+t.val • q) i; refine ⟨fun y i=>Xk.colony p|>.serial ..,fun i U=> ?_⟩
      rcases i with i|⟨k,t'⟩; exact (hp.tape (x:=x)).habit i U
      let V: Castor Xk p:= Sum.inr ⟨k,t'⟩
      have hz(V' t : W):= Xk.post x V' p k t';
      let J:=t'.val.val
      have h(t:sun): (f' t V).ingredient U=∏j∈J,(Xk.orbit x (r+t.val • q) j).ingredient U:=by change (((Xk.toast p x (r+t.val • q) (.inr _)).M).ingredient U)= _; rw [hz _ r];rfl
      have hi : ((T!).mode V).val.card=∑ j∈J,(Xk.mode j).val.card:=by
          change ((toast Xk p p 0 V).s).val.card = _; unfold V; rw [Xk.post p 0]; exact Finset.card_biUnion t'.val.property.2.2.1
      change Nail ((T!|>.mode V).val.card) _; rw [hi]
      change Nail _ (fun t=>(f' t V).ingredient _); simp_rw [h];exact Nail.all J _ _ (fun j _=> (hp.tape (x:=x)).habit j U)
    · intro s x hi; let a':= Xk.hat x s; let v0:= Castor Xk p; let E:= jumpX Xk x s p; let q:= heap a'
      have hO(i): (Xk.colony p).hat x s i=q (E i):= Xk.keeps x s p i
      have ht:= counts a' w o _ hw (hp.fee s x hi) he
      rw [show _=q ∘ E from funext hO]; refine ⟨fun i=> ht.sites (E i),fun i=> budget_loosen ?_ hs⟩; exact Cost.equiv E (ht.budget i) -- find
    intro a v hv hr; let x':=T!; let F:= Xk.hat a v; let e:=jumpX Xk a v p; let i(v':Castor Xk p):= v'
    have ht:= hp.bars a v hv hr; unfold Orchard.spend; change ∑ i, ‖((_ :ℝ):ℂ)*_‖* MergeProof.load _≤ _
    let f' x:= if (F x).s=B.fire hv then ‖(F x).charge‖ * MergeProof.load (F x).M else 0; let w₁ (i'):= ‖((x'.vitality w i':ℝ):ℂ)*(x'.qB w i' |>.part (B.fire hv))‖*MergeProof.load (x'.orbit a v i')
    change (∑ i: I ⊕ (Σ k:↥(logDeck (Xk.hat p (0:W))),Xk.flex p k.val),w₁ i) ≤ _; rw [Fintype.sum_sum_type,sum_eq_zero (f:=fun i': Σ k:↥(logDeck (Xk.hat p (0:W))),Xk.flex p k.val=>w₁ (.inr i')) (s:=univ) ?_,add_zero]; exact ht
    intro i _; unfold w₁ qB; simp_rw [Poly.part_send];
    have hh:=Menu.large (Xk.hat p (0:W)) (Wing.logKey i.fst.val) i.snd.val i.snd.property;
    have hx:(x'.mode (.inr i)).val.card ≥2:=by
       rcases i with ⟨j,l⟩; change 2≤ (Xk.toast p p 0 (.inr ⟨j,l⟩)|>.s.val.card); rw [post]; exact Menu.large _ _ _ l.property
    rw [if_neg (by intro hh; rw [← hh] at hx; simp [Census.fire] at hx),mul_zero,norm_zero,zero_mul]
omit hp
variable {σ C κ χ ψ :ℝ}
lemma festival (s:W)(hy:x.val.val.val.Lawful σ C κ χ ψ): let X':= Xk.hat x s
    Expense ((Xk.colony p).hat x s) w (A.B.a.clock.op m n)= Expense (Menu.heap X') w (A.B.a.clock.op m n):= spending' _ _ _ hy _ w hw (Xk.keeps x s p)
omit hw in
lemma owlSum (s:W)(D':GaugeDoor x.val.val.val (H.moment x.val.val)) (j:V)(z:Box (A.B.a.S.side m n))(u:Config G (A.B.a.S.side m n)): ∑ i : Castor Xk p,Menu.owl ((T!).hat x s i) D' j z u= ∑ i:I,Menu.owl (Xk.hat x s i) D' j z u:=by
    rw [← Menu.freeze D' (Xk.hat x s) _ _ _]; simp_rw [keeps];exact (jumpX Xk x s p).sum_comp (fun i=> owl (heap (Xk.hat x s) i) D' j z u)
end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil
