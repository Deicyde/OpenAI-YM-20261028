import YM.FullVolume.Tess.Bars
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
local notation "P"=> R.alloy.B.a
local notation "X"=> R.kit
local notation "D"=> R.rolls
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "C"=> R.family
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
structure Fan (T:Campaign R)(W:Pillars R T)(p:ℕ) where
    spin: sun -- times beamWidth
    hp:0 < spin.val
    film:sun→Face T W
    presents (N:ℕ)(s:sun): evalV T W (film s) p N= ask R.alloy.B.a (scaleSun spin s).val
namespace Fan
variable (F:Fan T W p) {n:ℕ} (x:sun)
lemma resize (x:sun) (hx:0<x.val): ∃ V:Fan T W p,V.film= F.film ∘ scaleSun x∧∀ i:sun,F.spin.val*x.val = V.spin.val:=by
     let U:Fan T W p:= ⟨scaleSun x F.spin,mul_pos F.hp hx,F.film ∘ scaleSun x,fun N s=>by simp only [Function.comp_apply]; rw [F.presents, px]⟩; exact ⟨U,rfl,fun _=>rfl⟩
lemma amenable (x:ℝ)(hp:0<x): ∃ v:sun,0<v.val ∧ ∀ N s,|evalV T W (F.film (scaleSun v s)) p N-R.alloy.B.a.clock.bar| ≤ x:=by
    let u:= beamWidth (P); have hv:0<u:= Contest.raise T.gains
    let w:= min 1 (x/u)
    have ht:0<w:= lt_min zero_lt_one (by positivity); let v:sun:=⟨w,⟨by linarith only [ht],min_le_left ..⟩⟩
    refine ⟨v,ht,fun N s=>?_⟩; rw [F.presents]; unfold Contest.ask; rw [add_sub_cancel_left, abs_mul,abs_of_pos hv]
    have he : |F.spin.val|≤1:= abs_le.mpr F.spin.property; have hz:|s.val|≤1:=abs_le.mpr s.property
    change |s.val * w* F.spin.val| *u ≤ x
    have hh: |s.val * w* F.spin.val| ≤ w:= by simp only [abs_mul]; rw [abs_of_pos ht]; exact (mul_le_of_le_one_right (by positivity) he).trans (mul_le_of_le_one_left ht.le hz)
    exact (mul_le_mul_of_nonneg_right hh hv.le).trans ((le_div_iff₀ hv).mp (min_le_right ..))
-- kernel ↑ y
variable (V₀:Fin n→R.family.book.Token)
abbrev plainK (N:ℕ)(s:sun): Positions n→ℂ:= Extraction.lifted ((F.film s).V T W) N p V₀
abbrev swellK (v: sun) (j N:ℕ)(h:j≤ N)(l:List (MotionIndex n))(s:sun)(y: Positions n):ℂ:= FullVolume.terrace (R.alloy.B.a.S) p h l (plainK F V₀ N (scaleSun v s)) y
local notation "P!"=>R.family.S
local notation "d!"=>intervalClock R
local notation "h!"=> R.family.S.a
variable {K:Set (Points n)} (hV:IsCompact K) (h: K⊆ NoHit R.alloy.B.a.S p n)
variable {v:ℕ→ℕ→ℝ} {Θ:Luna.Tableau T.width 300} (hk:Sky R T Θ v)
include hk hV h
-- all g Kernel starting. at ∀ past scalars.G.
lemma pricedT :∃ (b:ℕ)(B:ℝ)(v:sun),0<v.val ∧ 0≤ B ∧ ∀ᶠ j:ℕ in atTop,∀ N:ℕ,∀ (ht:j ≤ N)(x:Positions n), tag (h! j) x∈ K→ PaidBeam (fun s:sun=>swellK F V₀ v j N ht [] s x) (B*d! j^b):=by
   obtain ⟨r,hr,hS⟩:= Gaps.some _ p hV h
   obtain ⟨b,m,B,c,hc,hX,hb,hP⟩:= financed T Θ v hk W V₀ p r hr
   let a:sun:=⟨1/2,by norm_num [sun]⟩; let u:= scaleSun ⟨c,hc⟩ a; refine ⟨b,B,u,mul_pos (by norm_num [a]) hX, hb,?_⟩
   filter_upwards [eventually_gt_atTop m] with j hj N ht x h
   cases j with
   | zero=> omega
   | succ i=>
      let y := wrap ((S).side (i+1) p) ∘ x
      have hz:= hP i N (by omega) (by omega) F.spin F.spin.property F.film (F.presents N) y (fun a b he=> Gaps.gridSeparation _ _ rfl (hS _ h) _ _ he.symm)
      apply hz.stamp; intro s
      rw [show Muse.verso (slash c hc s)= scaleSun u s from Amp.Beam.px a ⟨c,hc⟩ s]; change _ = ((F.film (scaleSun u s)).V T W).numeric N p V₀ _; unfold swellK plainK; change ((F.film _).V T W).numeric N p V₀ _= _ ; congr 1
      exact wraps (S) p ht x -- orientation
set_option maxHeartbeats 420000 in
lemma pricedB(l:List (MotionIndex n)):∃ (b:ℕ)(B:ℝ)(v:sun),0<v.val ∧ 0≤B ∧ ∀ᶠ j:ℕ in atTop,∀ N:ℕ,∀ (ht:j ≤ N)(x:Positions n), tag (R.family.S.a j) x∈ K→ PaidBeam (fun s:sun=>swellK F V₀ v j N ht l s x) (B* intervalClock R j^b):=by
    induction l generalizing K with
    | nil=> exact pricedT F V₀ hV h hk
    | cons i l ih=>
       obtain ⟨t,ht,hT⟩:= hV.exists_cthickening_subset_open (nohitOpen (S) p n) h
       obtain ⟨b,B,w,hw,hB,hP⟩:= ih hV.cthickening hT
       refine ⟨b+1,2*B,w,hw,by positivity,?_⟩; filter_upwards [hP,(S).shrinks.eventually (ge_mem_nhds ht)] with j hj hv N hx x hz
       let a:= (S).a j; let y:= x+drive i
       let g(z:Positions n)(s:sun) := swellK F V₀ w j N hx l s z
       have hδ: dist (tag a y) (tag a x)= a:=by simpa only [one_smul,Nat.cast_one,one_mul] using! paidDist x a ((S).a_pos j) i 1
       have hh: tag a y∈ _:= mem_cthickening_of_dist_le _ _ _ _ hz (hδ.trans_le hv)
       obtain ⟨P',h,hQ⟩:= hj N hx x (mem_cthickening_of_dist_le _ _ _ _ hz ((dist_self _).trans_le ht.le))|>.arrives
       obtain ⟨U,hu,hU⟩:= (hj N hx y hh).arrives
       refine ⟨a⁻¹ • (U-P'),?_,fun s=>?_⟩
       · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (show 0≤a from ((S).a_pos j).le)),show a⁻¹=d! j from inv_inv _]
         exact (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hu h)) (zero_le_one.trans (one_clock j))).trans_eq (by ring)
       change (a:ℂ)⁻¹*(g y s-g x s)=_; rw [map_smul,map_sub,← hU,← hQ]; rw [Complex.real_smul]; simp only [Complex.ofReal_inv]; rfl
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.pricedB
