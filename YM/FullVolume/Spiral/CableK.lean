import YM.FullVolume.Spiral.CableE
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
variable (hw : Graces.Moms B.prices M.K B.span M.p.floorL)(hW: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay)(hd:d+3≤ A.B.a.clock.J m)
include choice g hm he ht hY hκ hC hw hW hd
omit hw hW in
lemma steamK (j:ℕ)(f f':Config G (A.B.a.S.side (m+1) n)→ℂ){a a':ℝ}(hf: SlotFit (K z) 0 j f)(hg: SlotFit (K z) 0 j f')(hc:∀ U,‖f U‖ ≤ a)(hx:∀ U,‖f' U‖ ≤ a'):let A₀ b:= Cub.trick H z hs j b (d:=d); let P:= (A.B.bake.make meshT).rep N n m
   (Matric.tell (A₀ f-A₀ f')).Format 0 (hol G) P ∧ Matric.Rune (A₀ f-A₀ f') (A₀ (f-f')) P.p:=by
    intro A' P
    let q:= f-f'; have h0: d ≤ A.B.a.clock.J m:=(Nat.le_add_right d 3).trans hd
    have hp :=slotSub hf hg; have hP(s):‖q s‖ ≤ a+a':=(norm_sub_le ..).trans (add_le_add (hc s) (hx s))
    have hX(r:Config G n₁→ℂ)(t:ℝ)(hp:r≠0)(hf:SlotFit (K z) 0 j r)(hr:∀ U,‖r U‖ ≤ t):∃ c:ℝ,∃ h': ∀ U,‖r U‖ ≤ c, let U:=fan (K z) 0 j r c h' hf; A' r=prepare H z hs U∧ Tyne H z meshT U d:=by
        obtain ⟨c,hc,hV,hQ⟩:= haunted H z hs j r hp hf hr (d:=d); exact ⟨c,hV,hQ, Graces.savvy g hm hs choice hC H z he ht hY hκ h0 j r c hp hf hV⟩
    have hZ : A' 0=0:=by unfold A' Cub.trick; rw [dif_neg (fun ⟨_,hx,_⟩=> hx rfl)] -- def proof
    by_cases hh : f=f'
    · rw [hh,sub_self,sub_self,hZ]; have heq:=spanNone (localSection G d) (A.B.bake.make meshT) N n m (hol G) (Set.univ:Set Lotus.Wing) (duet _ _ _ _ he ht (sandboxK H z)) (t:=0) le_rfl (le_refl (0:ℝ)); exact ⟨heq.earns.format,rfl,rfl,fun _ _ _=> EventuallyEq.rfl⟩
    obtain ⟨v,hv,h₃,h₆⟩:=hX q (a+a') (sub_ne_zero.mpr hh) hp hP
    let Q:= fan (K z) 0 j q v hv hp
    by_cases hy:f'=0
    · rw [hy,hZ,sub_zero,sub_zero]; rw [show A' f=A' q from congr_arg _ (by simp [q,hy]),h₃]
      -- avoid
      obtain ⟨hf,a,b,p,hts⟩:=h₆
      have ht':Push.Local.Readable (hol G) (localSection G d) P.p n₀ (authors cc m):= (choice.represents N n m hm.le|>.vac.symm) ▸ (livelyCard hY h0 (n:=n))
      exact ⟨invest _ _ (Guard.usage _ hf (choice.represents N n m hm.le).good ht'),rfl,rfl,fun _ _ _=> EventuallyEq.rfl⟩ -- rfl infer notation
    obtain ⟨w,hy',h₂,h₅⟩:=hX f' a' hy hg hx
    let W:= fan (K z) 0 j f' w hy' hg; let M':Unit → Cloud (K z):= fun _=> W
    by_cases hr:f=0
    · let F':Unit→ℝ:=fun _=>-1
      have he'(j:ℂ→L[ℝ]ℝ)(t): j (q t)= -1 * j (f' t):=by simp [q,hr]
      have hx'(p p':Lotus.Leaf (K z))(h:p'.turn=p.turn)(he:∀ V,p.ingredient V=-1 * p'.ingredient V): Merge.Grouped p F' (fun _=>p'):=⟨fun _=> h,Summable.of_finite,fun V=> by simpa only [F',he,Fintype.sum_unique] using hasSum_fintype (fun _:Unit => -1*p'.ingredient V)⟩
      have hM: Merge.Grouped Q.live F' (fun i=>(M' i).live):= hx' _ _ rfl (fun V=>he' Complex.reCLM V)
      have hM': Merge.Grouped Q.pale F' (fun i=>(M' i).pale):= hx' _ _ rfl (fun V=>he' Complex.imCLM V)
      have hy:∑ i,(F' i:ℂ) • prepare H z hs (M' i) (d:=d)=A' f-A' f':=by rw [hr,hZ,h₂]; simp [F',M',W,sub_eq_add_neg]; rfl
      rw [← hy,show A' (f-f')= _ from h₃]; exact movedWell hm H z hC he hY choice hs F' h0 hM hM' h₆ (fun i=>h₅)
    obtain ⟨x,hx',h₁,h₄⟩:= hX f a hr hf hc
    let X:= fan (K z) 0 j f x hx' hf; let M:Bool→Cloud (K z):= fun i=> if i then X else W
    let F':Bool→ℝ:=fun i=> if i then 1 else -1
    have hG : Merge.Grouped Q.live F' (fun i=>(M i).live):=by
       have hi: (fun i=>(M i).live)=fun i:Bool=> if i then X.live else W.live:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       exact map_sub Complex.reCLM _ _
    have hG' : Merge.Grouped Q.pale F' (fun i=>(M i).pale):=by
       have hi: (fun i=>(M i).pale)=fun i:Bool=> if i then X.pale else W.pale:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       exact map_sub Complex.imCLM _ _
    have hy:∑ i,(F' i:ℂ) • prepare H z hs (M i) (d:=d)=A' f-A' f':=by rw [Fintype.sum_bool,h₁,h₂]; simp only [F',if_true,Bool.false_eq_true,if_false,Complex.ofReal_neg,Complex.ofReal_one,one_smul,neg_smul]; simp [sub_eq_add_neg,M,X,W]; rfl
    rw [← hy,show A' (f-f')= _ from h₃]; exact movedWell hm H z hC he hY choice hs F' ((Nat.le_add_right d 3).trans hd) hG hG' h₆ (fun i=>by cases i; exact h₅; exact h₄)
end YM.PhysicalNext.Repeat.Cub
