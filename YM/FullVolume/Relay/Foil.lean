import YM.FullVolume.Relay.Halo
/- Freeze the physical field seeds. Actual multilevel density on ancestral
 and non-ancestral paths; the latter after the aligned observation level,
 without unlicensed singleton identification. -/
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
variable {R:Run G} (T:Campaign R) (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch
open Boutique Guard
open Extraction Extraction.Lease
variable (N p m:ℕ)
open UniformSpace
variable {a:ℝ}(ha:a∈ Ray.sun)
variable (F:Ray.sun→ Face T W)(hF:∀ s:Ray.sun, Face.evalV T W (F s) p N= ask R.alloy.B.a (slash a ha s).val)
open Veil.Splint Roof.Chord Jams
local notation "Vt"=>T.gains
local notation "Φ"=> R.alloy.B.a.clock
local notation "Z₁"=>fun s:Ray.sun=> (F (Muse.verso s)).score
local notation "Xo"=>fun s:Ray.sun=> (F (Muse.verso s)).owns
local notation "Wν"=> (R.tuning.receipts)
local notation "P"=>R.alloy.B.a.budget
local notation "R₁"=> arena T W N p F
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (H:1 ≤ m)(hN:m<N)
local notation "h_"=> (T.L.prim N m p hN)
variable {I:Type}[Fintype I] [DecidableEq I](B: Marker.Census I)
open Marker
variable (d:I→ℕ)(x: (i:I)→ ((Labels.frames G).level (d i)).Coeff)(ℓ:I→Motion)
local notation "Xc"=>fun s:Ray.sun=>(F (Muse.verso s)).score
local notation "ζ"=> fun s:Ray.sun=> (F (Muse.verso s)).owns
local notation "C"=> fun s:Ray.sun=> R.alloy.B.bake.make (Xc s|>.q)
local notation "S"=> R.alloy.B.a.S
variable (o: ∀ m:ℕ,I→ Site (R.alloy.B.a.S.side m p))
abbrev fieldLog (j)(s:Ray.sun) (i:I) : Config G (R.alloy.B.a.S.side j p)→ℂ:=frmE T W (d i) N p F (x i) (ℓ i) j (o j i) s
abbrev fieldForce (j)(s:Ray.sun) (i:I) : Box (R.alloy.B.a.S.side j p)→ Config G (R.alloy.B.a.S.side j p)→ℂ:= frmK T W (d i) N p F (x i) (ℓ i) j (o j i) s
abbrev fieldDensity (j)(s:Ray.sun) (i:I) : Config G (R.alloy.B.a.S.side j p)→ℂ:=frmD T W (d i) N p F (x i) (ℓ i) j (o j i) s
abbrev seeds (s:Ray.sun) (i:I): Config G (R.alloy.B.a.S.side N p)→ℂ:=item ((F (Muse.verso s)).V T W) (d i) N p (x i) (fun j=>o j i) (ℓ i)
open MergeProof.Accent
abbrev topFoil (s:Ray.sun): Config G (R.alloy.B.a.S.side N p)→Poly B:= Accent.birth B (arena T W N p F N s) (seeds T W N p F d x ℓ o s)
local notation "FT"=> topFoil T W N p F B d x ℓ o
abbrev foils (j:ℕ)(hj:j ≤ N)(s:Ray.sun): Config G (R.alloy.B.a.S.side j p)→ Poly B:= gust (C s) N p N (topFoil T W N p F B d x ℓ o s) j hj
local notation "Fo"=> foils T W N p F B d x ℓ o
lemma foilO : foils T W N p F B d x ℓ o N le_rfl=topFoil T W N p F B d x ℓ o:=funext fun s=> gust_base ..
lemma foilLife (j:ℕ)(hj:j≤N)(s:Ray.sun): Integrable (foils T W N p F B d x ℓ o j hj s) (prior G _):=by
    let z:= FT s; let A':= C s; let H(s':Ray.sun):= (F (Muse.verso s')).V T W; let x':= H s; let hp:= ((F (Muse.verso s)).score.mat N p).choice; apply gust_live (A:=A') (N:=N) _ _ _ _ _
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    unfold topFoil Accent.birth; have hx i:Continuous (seeds T W N p F d x ℓ o s i):=by unfold seeds item stepUp Motion.scalar; split; exact ((x'.continuousO ..).comp (continuous_pull ..)).star; exact (x'.continuousO ..).comp (continuous_pull ..)
    have hz: Continuous (arena T W N p F N s).eval:=by rw [show (arena T W N p F N s).eval=_ from ((Xc s).mat N p).choice.starts N p|>.2]; exact bare_cont _ -- pipe syntax
    exact (Complex.continuous_ofReal.comp hz).smul (Poly.pass_cont.comp (continuous_finsetSum _ fun i _=> (Sever.smeasure _).comp (hx i)))
variable {w:ℕ→ I→ℝ}{U v₀:ℕ→ℝ}
lemma foilStep (s:Ray.sun) (hm:m<N): Fo m hm.le s=((Φ).op m p).push ((arena T W N p F (m+1) s).beta) (Fo (m+1) hm s):= gust_step _ _ _ _ _ hm
lemma foilSum (s:Ray.sun) (h:m ≤ N): (∫ u, Fo m h s u ∂prior G _)=(∫ u, topFoil T W N p F B d x ℓ o s u ∂prior G _):=by
     apply gust_sum (C s) N p N _ _ h; exact congr_fun (foilO T W N p F B d x ℓ o) s ▸ foilLife T W N p F B d x ℓ o N le_rfl s
-- only authorizes `Aligned` until index m. require at least m+1 at launch. (N≥m observation for aligned; if N=m still require m>refs).
variable (j:ℕ)(hj : j ≤ N)(ht:∀ i, R.t (d i)<j)
variable (hU:∀ i:ℕ,j ≤ i→ i<N→∀ a:I, o (i+1) a = ((R.alloy.B.a.clock.op i p).ratio.embed (o i a)))
include hj ht hU
-- continuity.Canonical receipts._Input all true.Pay from real curves.
set_option maxHeartbeats 430000 in
lemma foilFire (m:ℕ)(hv:j ≤ m)(hn:m ≤ N)(s:Ray.sun) (i:I): (fun U=> (foils T W N p F B d x ℓ o m hn s U).part (B.fire i))=fieldDensity T W N p F d x ℓ o m s i:=by
    let H:= F (Muse.verso s); let b:= R.t (d i)
    let A:= H.score.mat N p
    induction hn using Nat.decreasingInduction with
    | self=>
       rw [foilO T W N p F B d x ℓ o]; let R':= R₁ N s; funext U; change (Accent.birth B R' _ U).part (B.fire i)=_
       rw [Accent.boot]; have h:= billed T W (d i) N p b F ((ht i).trans_le hv) le_rfl (fun _=>x i) (ℓ i) s (o N i); exact (congr_fun h U).symm
    | of_succ m hm IH=>
       let g:= Fo (m+1) hm s; let t:=((Φ).op m p); have hp:(∀ U,Fo m hm.le s U=t.push ((arena T W N p F (m+1) s).beta) g U):=fun U=>congr_fun (foilStep T W N p m F B d x ℓ o s hm) U
       simp_rw [hp]; have ht0 : t.IsKernel (R₁ (m+1) s|>.beta) G:=R.alloy.B.a.transition_mass ..; rw [push_get ht0 (foilLife T W N p F B d x ℓ o (m+1) hm s)]; let y:=x i
       rw [show (fun U=>(g U).part (B.fire i))= _ from IH (hv.trans m.le_succ)]; unfold fieldDensity frmD; rw [hU m hv hm]; exact buds T W _ _ _ _ F hm ((ht i|>.le).trans hv) (fun _=>x i) (ℓ i) (o m i) s
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.foilFire
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.foilSum
