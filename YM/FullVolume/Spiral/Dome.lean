import YM.FullVolume.Spiral.Beret
import YM.FullVolume.Spiral.Quartz
import YM.FullVolume.Amp.Lacey
/- Matrix fares before applying graph transform.Lift via Real beam in R.Space. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 400000
open Forum
open Extra.Histories.InputColumn
open UniformSpace FullVolume.Amp
local notation "I"=> Extra.Histories.InputColumn.Listing
variable {Z:sun→ Plate F m n}{P:Desk G n}{Q:Desk G m}
variable (K:Keeper Q.orient.p Q.orient.activities)
variable (L:Keeper P.orient.p P.orient.activities)
variable (V:∀ z:Motion,P.orient.activities.Moves z.1 0)(Y:Hol G)(w:F.Coeff)
abbrev press (Y:Hol G)(f:Coefficient F n)(L:Keeper P.orient.p P.orient.activities): Completion (Coin F Y P):= ↑(alb f Y P L)
structure Chart (Z:sun→ Plate F m n)(K:Keeper Q.orient.p Q.orient.activities)(L:Keeper P.orient.p P.orient.activities)(V:∀ z:Motion,P.orient.activities.Moves z.1 0)(Y:Hol G)(E:Heading F)(W:Side)(w:F.Coeff)(u t r s:ℝ): Prop where
  stage : ∀ t:sun,Seer (Z t) K V Y w
  aa : ∃ p:Beam F.Coeff,‖p‖≤u ∧∀ t:sun,(pagesP (Z t) V w).x-E.leads W w=Beam.read _ t p
  stream : ∃ p:Beam (Completion (Coin F Y P)),‖p‖≤t ∧∀ t:sun,press Y (pagesP (Z t) V w) L=Beam.read _ t p
  ja : ∀ f:F.Index→ Coin F Y Q,∃ p:Beam F.Coeff,‖p‖≤ r*‖f‖∧∀ t:sun,(pagesS (Z t) K V f w).x=Beam.read _ t p
  sty : ∀ f:F.Index→ Coin F Y Q,∃ p:Beam (Completion (Coin F Y P)),‖p‖≤ s*‖f‖∧∀ t:sun,press Y (pagesS (Z t) K V f w) L=Beam.read _ t p
structure PaidBeam {X:Type}[NormedAddCommGroup X] [NormedSpace ℝ X][CompleteSpace X](f:sun→ X)(a:ℝ) : Prop where
   arrives : ∃ P:Beam X, ‖P‖≤a ∧ ∀ s:sun,f s=Beam.read X s P
namespace PaidBeam
section
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X] {f g:sun→ X}
lemma larger (h:PaidBeam f a)(he:a ≤ b):PaidBeam f b:=by obtain ⟨p,hp,hV⟩:=h.arrives; exact ⟨p,hp.trans he,hV⟩
lemma stamp (h:PaidBeam f a) (hp:∀ s,g s=f s): PaidBeam g a:=by rw [funext hp]; exact h
lemma price (h:PaidBeam f a) : 0≤a:= (norm_nonneg _).trans (h.arrives.choose_spec.1)
lemma plus (h:PaidBeam f a)(he:PaidBeam g b):PaidBeam (fun t=>f t+g t) (a+b):= by obtain ⟨p,hp,hV⟩:=h.arrives; obtain ⟨q,hq,h⟩:=he.arrives; exact ⟨p+q,(norm_add_le ..).trans (add_le_add hp hq),fun i=>by rw [map_add,hV,h]⟩
end
end PaidBeam
variable {R: SectionData F}(hR:R.Sound Y)(hn:2 ≤ n.val)
variable {η :ℝ}{E:Heading F}{R':sun→Rep G n}{Q':sun→ Rep G m}{W:Side}
variable {u t r s:ℝ}
variable (hU:∀ i:sun,Along P.orient (R' i))(hQ:∀ i:sun, Along Q.orient (Q' i))(h:∀ i:sun,Elastic (Z i) Y (R' i) (Q' i))
variable (hY:Chart Z K L V Y E W w u t r s)(hr:0 ≤ r)(hs:0 ≤ s)
variable (z: sun → F.Index→ Coin F Y Q)(l:F.Index→ℝ) (hp:∀ i,PaidBeam (fun v:sun=> ((z v i):Completion (Coin F Y Q))) (l i))
local notation "fh"=> fun t:sun=> fullF (Z t) K V (z t) w
include hR hn hU h hQ hp hY hr hs
lemma splitK (X:sun→ Coin F Y P)(hx:∀ t:sun, Coin.uses (X t)= capture (fh t) L)(hd:∀ t,Hein (fh t) Y P): let v:=∑ i,l i
   PaidBeam (fun t:sun=>(fh t).x-E.leads W w) (u+r*v) ∧ PaidBeam (fun t:sun=> ((X t):Completion (Coin F Y P))) (t+s*v):=by
   intro v; let a t f:= pagesS (P:=P) (Q:=Q) (Y:=Y) (Z t) K V f w
   let A:=(Completion.toComplL (E:=Coin F Y Q) (𝕜:=ℝ)); have he:Isometry A:= Completion.coe_isometry; have hD:DenseRange A:= Completion.denseRange_coe
   obtain ⟨π,H,hq,hπ⟩:= Beam.podium (ι:=F.Index) A he hD
   choose p ht hS using fun i=> (hp i).arrives; let T:= Beam.lineup p; have hT: ‖T‖≤ v:= (Beam.lineupN p).trans (sum_le_sum fun i _=> ht i); have heq(i):π (z i)=Beam.read _ i T:=funext fun j=>by rw [hπ, show A (z i j)= _ from hS j i]; exact (Beam.lineupL ..).symm
   have h₁(s:sun) (f g:F.Index→ Coin F Y Q) := Tower.portal K L R V (hQ s) (hU s) (h s) w (hY.stage s) hR hn f g
   obtain ⟨B,hB,hB'⟩:= Beam.listen π H hq (fun i f=>(a i f).x) (fun i f g=>(h₁ i f g|>.1.symm)) hr hY.ja T z heq
   obtain ⟨C,hC,hC'⟩:= Beam.listen π H hq (fun i f=>press Y (a i f) L) (fun i f g=>(h₁ i f g|>.2.symm)) hs hY.sty T z heq
   have he(i):= Tower.stripes K L V w (hY.stage i) (z i) (X i) (hx i) (hd i)
   have hu:PaidBeam (fun i:sun=>(pagesP (Z i) V w).x-E.leads W w) u:= ⟨hY.aa⟩
   have hh:PaidBeam (fun i:sun=>press Y (pagesP (Z i) V w) L) t:= ⟨hY.stream⟩
   refine ⟨(hu.plus (g:=fun i=>(a i (z i)).x) ⟨B,hB.trans (mul_le_mul_of_nonneg_left hT hr), hB'⟩).stamp ?_ , (hh.plus (g:=fun i=> press Y (a i (z i)) L) ⟨C,hC.trans (mul_le_mul_of_nonneg_left hT hs), hC'⟩).stamp ?_⟩
   · intro i; let ℓ:=fh i; change (fullF (Z i) K V (z i) w).x-_= _; rw [he i|>.1]; unfold a; abel
   intro i; rw [he i|>.2,add_comm, Completion.coe_add]
end YM.FullVolume.Paint.Tower
