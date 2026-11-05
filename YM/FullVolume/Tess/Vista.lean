import YM.FullVolume.Tess.Treat
import YM.FullVolume.Tess.Scope
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
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
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
namespace Fan
variable (F:Fan T W p){n:ℕ}(V₀:Fin n→ R.family.book.Token)
local notation "δ"=> intervalClock R
variable (l:List (MotionIndex n))
open Tess
local notation "S!"=>R.family.S
local notation "C"=> Beam ℂ
open Tess Tess.Scroll
variable {w:sun}{K:Set (Points n)}
namespace Bows
variable {U:ℕ→Positions n→ Beam ℂ}{P:Points n→ Beam ℂ}(h:Bows F V₀ w K l U P)
include h
lemma sycamore:Tess.Scroll R.family.S K U P:=⟨h.landed,h.part⟩
lemma shrinks (z:sun): Bows F V₀ (scaleSun z w) K l (fun N x=> Amp.Beam.fit z (U N x)) (fun x=> Amp.Beam.fit z (P x)):=by
    refine ⟨?_,?_,(incline z).comp_continuousOn h.landed⟩
    · filter_upwards [h.song] with N h y hy s; erw [fitL,h _ hy _]; exact congr_arg (fun v:sun=> kFilm F V₀ l N v y) (px ..)
    intro ε he; filter_upwards [h.part ε he] with i h y hy; rw [dist_eq_norm,← fitD]; exact (fitN ..).trans_lt ((dist_eq_norm ..).symm.trans_lt (h y hy))
variable {V':MotionIndex n→ℕ→Positions n→ Beam ℂ}{v':MotionIndex n→Points n→Beam ℂ}(hp:∀ i:MotionIndex n,Bows F V₀ w K (i::l) (V' i) (v' i))
include hp
private lemma cinema :∀ᶠ i in atTop,∀ (x:Positions n) (j:MotionIndex n),tag ((S!).a i) x∈ K→tag ((S!).a i) (x+drive j)∈K→ U i (x+ drive j)-U i x=(S!).a i • V' j i x:=by
     filter_upwards [h.song,eventually_all.mpr (fun i=> (hp i).song)] with i hx hP x j he hv; let g:=V' j i x
     apply soul; intro s
     change Amp.Beam.read ℂ _ _=Amp.Beam.read ℂ _ _; rw [map_sub,map_smul,hx _ hv,hx _ he,hP _ _ he]; let Y':=kFilm F V₀ l i (scaleSun w s); exact unique_units Y' (R.family.S.a_pos _) j x
lemma slopes {z:ℂ}(hv:z∈ optics): ∀ x∈ interior K, HasFDerivAt (fun y=> heartX (P y) z) (stretch (fun i=>heartX (v' i x) z)) x:=by
    have ht:= (sycamore F V₀ l h).hatch hv; intro x hx
    refine ht.vivify (P:=fun i j p=> heartX (V' i j p) z) (fun i=> (sycamore F V₀ (i::l) (hp i)).hatch hv) ?_ hx
    filter_upwards [cinema F V₀ l h hp] with i h x j hx hp; simp_rw [← halos _ hv]
    rw [← map_sub,h _ _ hx hp]
    exact (haloC hv|>.restrictScalars ℝ).map_smul _ _
end Bows
namespace ArcPays
abbrev ExL (w:sun)(K:Set (Points n))(l:List (MotionIndex n)):=∃ U P,Bows F V₀ w K l U P
lemma deeper {v:sun}(hv:0 < v.val)(ht: v.val ≤ w.val) (he:ExL F V₀ w K l): ExL F V₀ v K l:=by
    have h: 0 < w.val:= lt_of_lt_of_le hv ht; let z :sun:= ⟨v.val/w.val,⟨(by apply le_trans (b:=0) (by norm_num); positivity), (div_le_one h).mpr ht⟩⟩; obtain ⟨U,P,hP⟩:= he; rw [show v=scaleSun z w from Subtype.ext (by change v.val=w.val*(v.val/w.val); field_simp) ]; exact ⟨_,_,hP.shrinks F V₀ l z⟩
private def herd (n:ℕ): ℕ→ Finset (List (MotionIndex n))
   | 0=> {[]}
   | i+1=> {[]} ∪ Finset.univ.biUnion (fun a:MotionIndex n=> (herd n i).image (List.cons a))
private lemma near (d:ℕ) (l:List (MotionIndex n))(h:l.length ≤ d): l∈ herd n d:=by
    induction d generalizing l with
    | zero=> simp only [Nat.le_zero,List.length_eq_zero_iff] at h; simp [h,herd]
    | succ i ih=> cases l with
      | nil=> simp only [herd,Finset.mem_union,Finset.mem_singleton, true_or]
      | cons j l=>
        refine Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,Finset.mem_image.mpr ⟨l,ih l (by simp only [List.length_cons,Nat.add_le_add_iff_right] at h; exact h),rfl⟩⟩))
variable {k:ℕ} (h:∀ l: List (MotionIndex n),∃ w:sun,0<w.val∧ ExL F V₀ w K l)
include h
lemma enlist (P:Finset (List (MotionIndex n))): ∃ w:sun,0<w.val∧ ∀ l∈P, ExL F V₀ w K l:=by
    induction P using Finset.induction_on with
    | empty=> exact ⟨noon,zero_lt_one,by simp⟩
    | insert j q hj ih=>
        obtain ⟨v,hv,h⟩:= h j; obtain ⟨w,hw,hW⟩:= ih; rcases le_total v.val w.val with hX|hX
        · exact ⟨v,hv,(Finset.forall_mem_insert _ _ _).mpr ⟨h,fun i hi=> deeper _ _ _ hv hX (hW i hi)⟩⟩
        exact ⟨w,hw,(Finset.forall_mem_insert _ _ _).mpr ⟨deeper _ _ _ hw hX h,hW⟩⟩
lemma voyage (k:ℕ):∃ (w:sun) (U:List (MotionIndex n)→ℕ→Positions n→Beam ℂ)(P:List (MotionIndex n)→ Points n→ Beam ℂ),0 < (w:sun).val∧∀ l, l.length ≤ k → Bows F V₀ w K l (U l) (P l):=by
    obtain ⟨w,hw,H⟩:= enlist F V₀ h (herd n k)
    choose! P U hU using fun l (h: l∈herd n k)=> (H l h)
    exact ⟨w,P,U,hw,fun l h=> hU l (near _ l h)⟩
end ArcPays
variable {k:ℕ}{U:List (MotionIndex n)→ℕ→Positions n→ Beam ℂ}{P: List (MotionIndex n)→ Points n→ Beam ℂ}(hV:∀ l:List (MotionIndex n), l.length ≤ k→ Bows F V₀ w K l (U l) (P l))
open Scroll
include hV
set_option maxHeartbeats 440000
set_option synthInstance.maxHeartbeats 260000
lemma genealogy {z:ℂ} (h:z∈optics):∀ l:List (MotionIndex n), l.length ≤ k→EqOn (fun x=>heartX (P l x) z) (derive (fun x=>heartX (P [] x) z) l) (interior K):=by
    haveI : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
    let D:= interior K; let g(l)(x):=heartX (P l x) z; intro l hl
    induction l with
    | nil=> exact fun _ _=>rfl
    | cons i l ih=>
       have hp(j:MotionIndex n):=hV (j::l) (by exact hl.trans_eq rfl)
       have ht:l.length ≤ k:=by simp only [List.length_cons] at hl; omega
       have hv(x)(hx:x∈D): HasFDerivAt (g l) (stretch (fun j=>heartX (P (j::l) x) z)) x:= (hV l ht).slopes F V₀ _ hp h _ hx
       intro x hx; have he:(g l) =ᶠ[𝓝 x] derive (g []) l:= (ih ht).eventuallyEq_of_mem (isOpen_interior.mem_nhds hx)
       have hh:= he.fderiv_eq (𝕜:=ℝ) -- fix
       unfold derive
       have hR:fderiv ℝ (derive (g []) l) x=stretch (fun j=> g (j::l) x):= hh.symm.trans ((hv x hx).fderiv)
       rw [hR]; exact (FullVolume.loyal (fun j => g (j::l) x) i).symm
-- ContDiff thru paid order.
omit hV in
private lemma trilead (n:ℕ): ∃ L : (MotionIndex n→ℂ)→L[ℝ] (Points n→L[ℝ] ℂ),∀ v,L v=stretch v:=by
  let Q : (MotionIndex n→ℂ)→ₗ[ℝ] (Points n→L[ℝ] ℂ):=
    { toFun := stretch
      map_add' := by
        intro x y; ext1 j; change ∑ i:MotionIndex n, j i.1 i.2 • (x i+y i)= (∑ i:MotionIndex n, j i.1 i.2 • x i) + (∑ i:MotionIndex n, j i.1 i.2 • y i); simp_rw [smul_add]; exact Finset.sum_add_distrib
      map_smul' := by
        intro r x; ext1 j; change ∑ i:MotionIndex n, j i.1 i.2 • (r • x i)= r • ∑ i:MotionIndex n, j i.1 i.2 • x i; rw [Finset.smul_sum]; simp [mul_left_comm] }
  exact ⟨Q.toContinuousLinearMap,fun _=>rfl⟩
lemma galaxyX {z:ℂ}(h:z∈optics) : ContDiffOn ℝ k (fun x=>heartX (P [] x) z) (interior K):=by
    haveI : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
    let D:= interior K; let g(l)(x):=heartX (P l x) z
    have hx (k':ℕ):∀ l:List (MotionIndex n),l.length+k' ≤ k→ ContDiffOn ℝ k' (g l) D:=by
      induction k' with
      | zero=>intro l hl; exact contDiffOn_zero.mpr (((hV l (by omega)).sycamore F V₀ l).hatch h|>.land.mono interior_subset)
      | succ m ih=>
        intro l hl
        have hL:l.length ≤ k:= by omega
        let H(x:Points n)(i:MotionIndex n):= g (i::l) x
        have ha : ContDiffOn ℝ m H D:=contDiffOn_pi.mpr fun i=> ih _ (by change (i::l).length + _≤ _; simp only [List.length_cons]; omega)
        have hp(j:MotionIndex n):=hV (j::l) (by simp only [List.length_cons];omega)
        obtain ⟨A,hA⟩:= trilead n
        have he: UniqueDiffOn ℝ D:= (show IsOpen (interior K) from isOpen_interior)|>.uniqueDiffOn
        rw [Nat.cast_add_one]; apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn he).2
        refine ⟨by simp,A∘ H,A.contDiff.comp_contDiffOn ha, fun x hx=>?_⟩; rw [Function.comp_apply,hA]; exact ((hV l hL).slopes F V₀ _ hp h _ hx).hasFDerivWithinAt
    exact hx k [] (by simp)
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.ArcPays.voyage
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.galaxyX
