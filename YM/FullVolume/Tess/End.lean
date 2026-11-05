import YM.FullVolume.Tess.Fare
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
open Tess
local notation "S!"=>R.family.S
local notation "C"=> Beam ℂ
open Tess Tess.Scroll
/-- analytic UV spatial derivatives, real tests, uniform grids. Disk is `scaleSun w F.spin` at p; sequence convergence only on paid thresholds even at fixed p. `shiftH` with real Family and ℓ.N ≤ A.Shows`. Includes interpolation and sampled values. For multiple finite requests can use compacts and h+witness radius chosen jointly here over l.ALL.
-/
structure Renewal (K:Set (Points n))(h:ℕ):Prop where
    work : ∃ (w:sun)(Ω:Set (Points n))(D:ℂ→Points n→ℂ),0 < (w:sun).val∧IsOpen Ω∧ K⊆ Ω∧ Ω⊆ NoHit (S!) p n∧(∀ z∈ optics,ContDiffOn ℝ h (D z) Ω) ∧(∀ x∈K,AnalyticOnNhd ℂ (fun z=>D z x) optics)∧∀ l:List (Reach n), l.length ≤ h→ Polar F V₀ w K l D
variable {k:ℕ} {v:ℕ→ℕ→ℝ}{Θ:Luna.Tableau T.width 300} (H:T.Winter) (h':Jams.Wild R.kit.shape R.alloy.delay) (hk:Sky R T Θ v)
include H h' hk
lemma renewed {K:Set (Points n)} (h:IsCompact K)(hp:K ⊆ NoHit R.family.S p n) : Renewal F V₀ K k:=by
    obtain ⟨t,ht,hT⟩:=h.exists_cthickening_subset_open (nohitOpen ..) hp; let V:=cthickening t K
    have he:IsCompact V:= h.cthickening; have hh:K⊆ interior V:=by
       intro x hx; rw [mem_interior_iff_mem_nhds]; exact Filter.mem_of_superset (closedBall_mem_nhds _ ht) (fun y hy=>mem_cthickening_of_dist_le _ _ _ _ hx (mem_closedBall.mp hy))
    obtain ⟨w,U,P,hΩ,hX⟩:= ArcPays.voyage F V₀ (fun l=> by obtain ⟨w,u,g,hv,H⟩:= charted F V₀ l he hT H h' hk; exact ⟨w,hv,u,g,H⟩) k
    let D(z:ℂ)(x):=heartX (P [] x) z; refine ⟨w,interior V,D,hΩ,isOpen_interior,hh,interior_subset.trans hT,fun z hz=> galaxyX F V₀ hX hz,fun x _=> hearts _,fun l hl=>?_⟩
    let l':= l.map Reach.where_; have heq : l'.length ≤ k:=by simpa [l'] using hl
    obtain ⟨X,hK,hU,hB⟩:= exists_compact_between h (isOpen_interior) hh; have hx := polaris F V₀ l (hX l' heq) hK hB
    exact peaking F V₀ l h hK hU D (fun z hz y hy=>genealogy F V₀ hX hz l' heq (hh hy)) hx.1 hx.2
omit H h' hk
-- existence of witnessing arc simultaneous real cutoffs on fixed p.
abbrev nucleus:sun:=⟨0,⟨by norm_num,by norm_num⟩⟩
lemma buys :∃ F: Fan T W p,F.film nucleus=centerF T W:=by
   let b:= outing T p; let v:= beamWidth (P!)
   have ht:0<b:= allowed T p; have hv:0<v:= Contest.raise T.gains
   let w := min (b/v) 1
   have hw:0<w:= lt_min (by positivity) zero_lt_one; have hx:w≤1:= min_le_right ..; let V:sun:=⟨w,abs_le.mp (by simpa only [abs_of_pos hw] using hx)⟩
   let x(s:sun):= ask R.alloy.B.a (scaleSun V s|>.val)
   have h(s): x s∈ nearby P!:= Contest.onLine T.gains _
   have hC(s): |x s-R.alloy.B.a.clock.bar|≤ outing T p:=by
       unfold x Contest.ask; rw [add_sub_cancel_left]; change |s.val*w*v|≤ _; rw [abs_mul,abs_mul,abs_of_pos hv,abs_of_pos hw]; exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hw.le (abs_le.mpr s.2)) hv.le).trans ((le_div_iff₀ hv).mp (min_le_left ..))
   have hx : x nucleus=R.alloy.B.a.clock.bar:=by unfold x Contest.ask scaleSun Muse.slash; dsimp only; change _+ 0*w*_=_; ring
   choose F hf hΩ using fun s:sun=> show ∃ F:Face T W,(∀ N,evalV T W F p N=x s)∧ (s=nucleus → F=centerF T W) from (by
       by_cases hs:s=nucleus
       · exact ⟨centerF T W,fun N=> by rw [Face.unit,hs,hx],fun _=>rfl⟩
       choose P hP using fun N:ℕ=> Contest.born (n:=p) (N:=N) T.gains (h s)
       let U(j N:ℕ):Contest N j T.L:=if he:p=j then he ▸ P N else T.center N j
       have he(N):U p N=P N:=by unfold U; rw [dif_pos rfl]
       have hz (q N:ℕ):|(U q N).bonusB-R.alloy.B.a.clock.bar|≤ outing T q:=by
           rcases eq_or_ne p q with h|h; subst q; rw [he,hP]; exact hC s
           unfold U; rw [dif_neg h]; change |evalV T W (centerF T W) q N- _|≤ _; rw [Face.unit,sub_self,abs_zero]; exact (allowed ..).le
       obtain ⟨B⟩:= cant T U hz; exact ⟨⟨U,B,Classical.choice (hasRecord T W B)⟩,fun N=> by change (U p N).bonusB= _; rw [he,hP],fun h=> (hs h).elim⟩)
   exact ⟨⟨V,hw,F,fun N s=> hf s N⟩, hΩ nucleus rfl⟩
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.renewed
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.buys
