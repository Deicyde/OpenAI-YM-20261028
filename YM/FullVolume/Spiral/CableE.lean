import YM.FullVolume.Spiral.Fell
import YM.FullVolume.Panel.Cable
import YM.FullVolume.Panel.Strap
import YM.FullVolume.Panel.Spokes
import YM.FullVolume.Panel.Dress
import YM.FullVolume.Panel.Port
import YM.MergeProof.Tanger
/-!
# Specific formulas for the canonical color compactors.

Work even for ghost Motion stability provided underlying step on same camera. `Text` carries real profile & Church. Choices in Tint and Ink only pay real fares; the installed canon will be linked in steps with ANY F estimate.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces MergeProof MergeProof.Matric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{B:Factor A}
variable {m N n d:ℕ} (hm:m<N)
set_option quotPrecheck false
local notation "cc"=> A.B.a
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
variable {K:In A.B.a m n} {meshT:ℕ→∀ p, Trail A.B.a p} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
local notation "Ω"=> K z
local notation "H!"=> A.B.bake.make meshT
local notation "φ"=> (D.L J)
variable (hC:Mallow.Arrives B.shape A.delay)(g:G.Simple)
    (he : (A.B.bake.make meshT).rep N n m=H.result z.val) (ht: (A.B.bake.make meshT).rep N n (m+1)=K z.val)
    {E:ℕ→ℝ} {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
    (choice : (A.B.bake.make meshT).Selected)(hs: HasSlots ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities)(hr : HasSlots (K z).p (K z).activities)
private lemma regSub0 {R:Rep G (A.B.a.S.side (m+1) n)} {s:Support (A.B.a.S.side (m+1) n)} {f g:Config G (A.B.a.S.side (m+1) n)→ℂ}(hf: RegFit R 0 d (hol G) s f) (hg:RegFit R 0 d (hol G) s g): RegFit R 0 d (hol G) s (f-g):=by
    let h:=Reads (hol G) 0 s (0:Labels.Label G d); have hh:= reads_sub ((reads_null_iff ..).mpr ⟨hf.unit_null,hf.proj⟩) ((reads_null_iff ..).mpr ⟨hg.unit_null,hg.proj⟩); rw [sub_zero] at hh
    obtain ⟨ha,hb⟩:= (reads_null_iff ..).mp hh
    exact ⟨regular_sub hf.smooth hg.smooth,hf.anchor,ha,hb⟩
variable (hw : Graces.Moms B.prices M.K B.span M.p.floorL)(hW: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay)(hd:d+3≤ A.B.a.clock.J m)
include choice g hm he ht hY hκ hC hw hW hd
set_option maxHeartbeats 360000 in
lemma steamE (j:ℕ)(f f':Config G (A.B.a.S.side (m+1) n)→ℂ){a a':ℝ}(hf: RegFit (K z) 0 d (hol G) (mapSeat j) f)(hg: RegFit (K z) 0 d (hol G) (mapSeat j) f')(hc:(K z).p.supBounds 0 (mapSeat j) f a)(hx:(K z).p.supBounds 0 (mapSeat j) f' a'):let A₀ b:= Cub.cologne H z hs hr j b (d:=d); let P:= (A.B.bake.make meshT).rep N n m -- macro A collision
   (Matric.tell (A₀ f-A₀ f')).Format 0 (hol G) P ∧ Matric.Rune (A₀ f-A₀ f') (A₀ (f-f')) P.p:=by
    intro A' P
    let s:= mapSeat (n:=n₁) j; let q:= f-f'
    have hp :=regSub0 hf hg; have hP:= Next.Foundations.bound_sub hf.smooth hg.smooth hc hx
    have hX(r:Config G n₁→ℂ)(t:ℝ)(hf:RegFit (K z) 0 d (hol G) s r)(hr':(K z).p.supBounds 0 s r t):∃ c:ℝ,∃ h': (K z).p.supBounds 0 s r c, let U:=float (K z) 0 s (spot _ _) r c hf.smooth h' hr; A' r=prepare H z hs U∧ Tyne H z meshT U d:=by
        obtain ⟨c,hc,hV,hQ⟩:= grave H z hs hr j r hf hr'; obtain ⟨a,b,x,hx,hK,hT,-⟩:= regularJ g hm hs hC hw hW hd hY hκ H z ht he hr s c r hf hV; exact ⟨c,hV,hQ,hx.1,a,b,x,hT⟩
    obtain ⟨x,hx',h₁,h₄⟩:= hX f a hf hc; obtain ⟨w,hy',h₂,h₅⟩:=hX f' a' hg hx; obtain ⟨v,hv,h₃,h₆⟩:=hX q (a+a') hp hP
    let X:= float (K z) 0 s (spot _ _) f x hf.smooth hx' hr; let W:= float (K z) 0 s (spot _ _) f' w hg.smooth hy' hr; let Q:= float (K z) 0 s (spot _ _) q v hp.smooth hv hr; let M:Bool→Cloud (K z):= fun i=> if i then X else W
    let F':Bool→ℝ:=fun i=> if i then 1 else -1
    have hG : Merge.Grouped Q.live F' (fun i=>(M i).live):=by
       have hi: (fun i=>(M i).live)=fun i:Bool=> if i then X.live else W.live:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       have hh:= congr_fun (map_sub (Local.maskLinear (K z|>.p.threshold) s) f f') j; exact (congr_arg Complex.reCLM hh).trans (map_sub Complex.reCLM _ _)
    have hG' : Merge.Grouped Q.pale F' (fun i=>(M i).pale):=by
       have hi: (fun i=>(M i).pale)=fun i:Bool=> if i then X.pale else W.pale:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       have hh:= congr_fun (map_sub (Local.maskLinear (K z|>.p.threshold) s) f f') j; exact (congr_arg Complex.imCLM hh).trans (map_sub Complex.imCLM _ _)
    have hy:∑ i,(F' i:ℂ) • prepare H z hs (M i) (d:=d)=A' f-A' f':=by rw [Fintype.sum_bool,h₁,h₂]; simp only [F',if_true,Bool.false_eq_true,if_false,Complex.ofReal_neg,Complex.ofReal_one,one_smul,neg_smul]; simp [sub_eq_add_neg,M,X,W]; rfl
    rw [← hy,show A' (f-f')= _ from h₃]; exact movedWell hm H z hC he hY choice hs F' ((Nat.le_add_right d 3).trans hd) hG hG' h₆ (fun i=>by cases i; exact h₅; exact h₄)
end YM.PhysicalNext.Repeat.Cub
