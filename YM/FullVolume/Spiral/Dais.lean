import YM.FullVolume.Spiral.Brace
import YM.FullVolume.Spiral.Erode
import YM.FullVolume.Spiral.Rent
import YM.FullVolume.Spiral.Saffron
import YM.FullVolume.Spiral.Stone
/- angle true anchors. IF chart present. top rests later. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
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
variable {q v d t t':ℝ}{N n m k:ℕ}{L:Lyrics R t t}
open UniformSpace FullVolume Paint Paint.Tower
open Luna MergeProof MergeProof.Matric Legato Legato.Bandage.Boutique Next.Foundations Extra.Histories Planned.GuardedAtom Guard
set_option maxHeartbeats 490000
set_option synthInstance.maxHeartbeats 155000
open Graces Circlet Mallow Legato.Bandage Legato.Bandage.Branch
variable (g:G.Simple)(Φ :Plato L q v d t') (T:Tableau q 300)(h:PaysW R.shape v A.delay) (hz:Spire T R.shape (costP X.p D) A.delay) {W: Bid.Worth}{c₁:ℕ→ℝ}(b:Legato.Bandage R c₁ W) {i l r:ℕ} (hr:l ≤ i)(hs:k+3 ≤ A.B.a.clock.J i)
local notation "P!"=> stageP A.B.a (m+1) n
set_option quotPrecheck false
local notation "m'"=> A.B.a.S.side m n
local notation "n'"=> A.B.a.S.side (m+1) n
local notation "W!"=> (Labels.frames G).level k
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "A!"=> Ticket A N m n
local notation "J_"=> A.B.a.clock.J (m+1)
local notation "L_"=> D.L J_
local notation "p_"=> localSection G k
local notation "y_"=> Next.Foundations.hol G
local notation "vT"=> c₁ J_
local notation "η"=> Doors.rate (L_)
variable {Nt:Bolt A}(hT:Nest R Nt) {H:∀ m, Desk G (A.B.a.S.side m n)}(hH:∀ m,Feeling A m n (H m))
open YM.Source
variable {S:sun→ℕ→∀ p,Shoot.Trail A.B.a p}(U:∀ s:sun,Branch R (S s) N n l) (M:∀ s:sun, TransferData ((Labels.frames G).level k) (A.B.bake.make (S s)) N n)
variable (F:sun→ Contest N n L)(O:Ops L N n)
local notation "Y'"=> A.B.a
local notation "Y"=> Next.Foundations.hol G
--
set_option quotPrecheck false
variable (hm:∀ s h, Piano b (U s) hH hr hs (M s) h)(hK:i ≤ N) (hU: ∀ s m,∀ h:i ≤ m,∀ ht:m<N,Flavor L ((U s).steps m (hr.trans h) ht))
variable (hV: ∀ (s:sun) (m:ℕ), i ≤ m → m≤N→ (F s).trail m=(S s) N n m)
open Contest
variable {a:ℝ}(ha:a∈sun)(hf:∀ x, (F x).bonusB=Contest.ask A.B.a (slash a ha x).val)
variable {r':ℕ→ℕ→ℝ} (hy:Tower.Sav G X.p.profile c₁ T r' D.L)
local notation "Q'"=> fun s:sun=> cargo b hH hr hs (U s) (M s) (hm s)
local notation "X0"=> fun m:ℕ=> Completion (Coin W! (Y) (H m))
local notation "w'"=> (Φ)
-- Muse. Fields on narrower of pose. same Gram certificates.Seer. no β dependence within ξ. From `Cost phases pre-L`. easy shifted.U.Score scaling.
include g Φ T h hz b hr hs hH U M F O hm hK hU hV ha hf hy hT
private def gradientX (a:Levels G) (i j:ℕ)(q:ℝ):ℝ:= q* Real.exp (a.S.scale j-a.S.scale i)
local notation "D!"=> Muse.verso
local notation "M'"=> fun t:sun=> M (Muse.verso t)
local notation "foot"=> A.B.a.clock.J
local notation "σ"=> fun m:ℕ=> r' k (foot m)
-- hP anchor top Pose all.H.Crafts.N.Control.Root
lemma linked (m:ℕ)(ht:i ≤ m)(hR:m<N)(hx:∀ x:(Labels.frames G|>.level k|>.Coeff),PaidBeam (fun s:sun=> ((((U (verso s)).cargo b hH hr hs (M (verso s)) (hm (verso s)) (m+1)).g x):Completion (Coin (Labels.frames G|>.level k) (Next.Foundations.hol G) (H (m+1))))) (r' k (A.B.a.clock.J (m+1))*‖x‖)) :
   (∀ x:(W!).Coeff, PaidBeam (fun s:sun=> (((Q' (verso s) m).g x):X0 m)) (r' k (foot m)*‖x‖))∧∀ (x:sun→(W!).Coeff)(t:ℝ), PaidBeam (fun s:sun=> ((M' s).entries m (x s)).x) t → PaidBeam (fun s:sun=> ((M' s).entries (m+1) (x s)).x) (((A.B.a.S.block m).val:ℝ)*t):=by
   let v:= F∘verso; let A0:= fun s:sun=> U (verso s); have hP(i'):(v i').bonusB= ask A.B.a (slash (1/2*a) (h:=show 1/2*a∈sun from by obtain ⟨h,hx⟩:= ha; constructor <;> linarith) i'|>.val):=by
        unfold v; rw [Function.comp_apply,hf]; apply congr_arg; change i'.val*(1/2)*a=i'.val*(1/2*a); ring
   let j:= Fin.mk m hR; have hk:i ≤ m+1:= ht.trans m.le_succ
   have he(i':sun): HasSlots (stageP A.B.a (m+1) n|>.p) (observe (O.plan (m+1) hR) (Contest.chair Φ O (v i') j.succ)):= by
        have hx:= (v i').home_observe Φ O (m+1) hR
        change HasSlots (A.B.a.budget (m+1)) (observe (O.plan (m+1) hR) (homeP Φ O (v i') (m+1) hR)); rw [hx]
        change HasSlots _ ((F (verso i')).trail (m+1)).activities; rw [hV (verso i') (m+1) hk hR]; exact (((A0 i'|>.choice).represents _ _ (m+1) hR).vac ▸ (A0 i'|>.slots _ (hr.trans hk) hR)) -- macro
   obtain ⟨B,hB,hG⟩ := gloaming Φ O v _ hP j.succ he
   have h'σ : 0 ≤ σ (m+1):=(by exact le_trans (mul_nonneg zero_le_two (Nat.cast_nonneg (Fintype.card (W!).Index))) (hy.zero _ _))
   obtain ⟨hL,hLY,hLn,hLU⟩:= hy.gets (step_paid A.B.a m) (hs.trans (A.B.a.fits.mono ht))
   have h' : Local.turnCost (H m).orient.p.order (H m).orient.p.power=Local.turnCost (X.p.profile (A.B.a.clock.J m)).order (X.p.profile (A.B.a.clock.J m)).power:=by rw [ (hH m).healthy,Rain.jersey (A:=A) (m:=m)|>.1,Rain.jersey (A:=A) (m:=m)|>.2.1]
   rw [← h'] at hLY
   obtain ⟨hv,hp⟩:= Veil.destination g Φ T h hz b hr hs hT hH A0 M' (fun i=>hm (verso i)) ht hR (fun i' => hU _ m ht hR) O v (fun i' => hV (verso i') _ hk hR) (hues Φ O v j.succ he) (fun _=> rfl) B hB hG h'σ hx hL hLY
   refine ⟨hv,fun x t hu=>?_⟩ -- syntax
   refine (hp x t hu).larger ?_; rw [PriceCompiler.block_eq A.B.valid]; exact mul_le_mul_of_nonneg_right hLn hu.price
-- track FULL
lemma tackle (m:ℕ)(hx:i ≤ m)(ht:m ≤ N) (x:(W!).Coeff): PaidBeam (fun s:sun=>(((Q' (verso s) m).g x):Completion (Coin W! Y (H m)))) (σ m *‖x‖):=by
   induction ht using Nat.decreasingInduction generalizing x with
   | self =>
     obtain ⟨B,hB,hp⟩:= terrace Φ O F ha hf (Fin.last N); have hz:= aim Φ b hr hs hH U M hm hK (O:=O) (F:=F) B hB hp (fun s=>(hV s _ hK le_rfl).symm) x; exact hz.larger (mul_le_mul_of_nonneg_right (hy.zero k (A.B.a.clock.J N)) (norm_nonneg _))
   | of_succ k hk ih=> exact (linked g Φ T h hz b hr hs hT hH U M F O hm hK hU hV ha hf hy k hx hk (fun x=> ih (hx.trans k.le_succ) x)|>.1 x) -- supply
variable (X₀:sun→(Labels.frames G|>.level k|>.Coeff))
local notation "τ"=> fun j (q:ℝ)=> q*Real.exp (A.B.a.S.scale j-A.B.a.S.scale i)
lemma limbs (m:ℕ)(hm':i≤ m)(ht:m ≤ N) (q':ℝ)(hp:PaidBeam (fun s:sun=> ((M (verso s)).entries i (X₀ s)).x) q'): PaidBeam (fun s:sun=> ((M (Muse.verso s)).entries m (X₀ s)).x) (q'*Real.exp (A.B.a.S.scale m-A.B.a.S.scale i)):=by
    induction hm' with
    | refl=> simpa only [sub_self, Real.exp_zero,mul_one] using hp
    | @step m hk ih=>
      have hh:= (linked g Φ T h hz b hr hs hT hH U M F O hm hK hU hV ha hf hy m hk ht (tackle g Φ T h hz b hr hs hT hH U M F O hm hK hU hV ha hf hy (m+1) (Nat.le_trans hk (Nat.le_succ m)) ht)).2 X₀ (q'*Real.exp (A.B.a.S.scale m-A.B.a.S.scale i)) (ih (Nat.le_of_succ_le ht))
      apply hh.larger; apply le_of_eq; rw [Schedule.scale_succ, add_sub_right_comm,Real.exp_add,Real.exp_log (show 0<((A.B.a.S.block m).val:ℝ) from by positivity)]; ring
end YM.PhysicalNext.Repeat.Muse.Veil
