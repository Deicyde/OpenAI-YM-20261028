import YM.FullVolume.Finale.Real
/-
 Crucial: the auxiliary real extension used to enroll an orbit of origins was not a calibrated history below them. Here transfer the (same literal) charts to the TRUE recursion. Do not change the Kin or support calendars.H. Recipe deterministic for trials.
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
variable (Z:Face T W)
-- Certificates fix field *literal* irrespective of discretion in presenting Based with Piano charts. Use analytic price for all picks on real line.
variable (F:Fan T W p)
variable {v:ℕ→ℕ→ℝ}{Θ:Luna.Tableau T.width 300} (hk:Campaign.Sky R T Θ v)
private lemma analytic_punch {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] [NormedSpace ℂ Y][IsScalarTower ℝ ℂ Y] (X Z: Beam Y) (s:sun)(h: |s.val|<1)(hp:∀ v:sun,v≠s→ read Y v X=read Y v Z): read Y s X=read Y s Z:=by
    let f : Y→L[ℝ] Y:= ContinuousLinearMap.id ℝ _
    let g:ℝ→ℂ:= Complex.ofRealCLM
    have hv: ‖g s‖<1:= by simpa [g,Real.norm_eq_abs] using h -- reverse
    have he(T:Beam Y)(r:sun): shine f T (g r)=read Y r T:= Amp.opening f T r
    have hC(T:Beam Y):ContinuousAt ((shine f T) ∘ g) s.val:= ((Amp.hol f T _ hv).continuousAt).comp Complex.continuous_ofReal.continuousAt
    let L:=𝓝[≠] s.val; have hx:Tendsto (shine f X ∘ g) L (𝓝 (read Y s X)):=(he X s) ▸ (hC X).continuousWithinAt (s:={s.val}ᶜ)
    have hz:Tendsto (shine f Z ∘ g) L (𝓝 (read Y s Z)):=(he Z s) ▸ (hC Z).continuousWithinAt (s:={s.val}ᶜ)
    refine tendsto_nhds_unique (hx.congr' ?_) hz
    have ht:∀ᶠ t :ℝ in L, |t|<1:= nhdsWithin_le_nhds (continuous_abs.continuousAt.tendsto.eventually (gt_mem_nhds h))
    filter_upwards [ht, show ∀ᶠ t in L, t∈ ({s.val}:Set ℝ)ᶜ from self_mem_nhdsWithin] with i hi hz
    let s':sun:=⟨i,abs_le.mp hi.le⟩; exact (he X s').trans ((hp s' (fun v=> hz ((by exact congr_arg Subtype.val v)))).trans (he Z s'|>.symm))
include hk Z
lemma wagesArc (d N:ℕ)(h:R.family.ref d ≤ N)(s:sun)(hs: |s.val|<1)(he:evalV T W (F.film (Muse.verso s)) p N=evalV T W Z p N): (Z.novel.factory d N p).terminal=((F.film (Muse.verso s)|>.novel).factory d N p).terminal:=by
    let Y:= update F.film (Muse.verso s) Z
    have hw r: evalV T W (Y r) p N= ask R.alloy.B.a (scaleSun F.spin r).val:= by rcases eq_or_ne r (Muse.verso s) with h|h; subst r; rw [show Y (Muse.verso s)=_ from update_self ..]; exact he.symm.trans (F.presents ..); rw [show Y r = _ from update_of_ne h ..]; exact F.presents ..
    let L:= Labels.frames G|>.level d; let U:=L.Coeff
    let a:=F.spin.val; let V:= F.film (Muse.verso s)
    let H (X:sun→Face T W)(r:sun)(x:U):U:= ((X (Muse.verso r)).owns.record d N p).terminal.symm x
    have hp (X:sun→Face T W)(he:∀ r,evalV T W (X r) p N=ask R.alloy.B.a (scaleSun F.spin r).val)(x:U): PaidBeam (fun r=> H X r x) (‖x‖* Real.exp (R.family.S.scale N-R.family.S.scale (R.family.ref d))) :=by
       have ht:Prestige R T v:= ⟨Θ,hk.paid,hk.spire,hk.sav⟩
       refine (Face.incomePhase T W ht d N p N F.spin.property X he (fun _=>x) (PaidBeam.static x) h le_rfl).1.stamp (fun s=> ?_)
       exact (((X (Muse.verso _)|>.owns).priced d N p h).bare_coord _).symm
    have hh : (Z.owns.record d N p).terminal.symm = (V.owns.record d N p).terminal.symm :=by
       ext1 x
       obtain ⟨A,hA,hx⟩:=(hp Y hw x).arrives; obtain ⟨B,hB,hb⟩:= (hp F.film (fun v=> F.presents N v) x).arrives
       have h_:Injective Muse.verso:=by intro u v h; apply Subtype.ext; have hv:= congr_arg Subtype.val h; change u.val*(1/2:ℝ)=v.val*(1/2:ℝ) at hv; linarith
       have hh:= analytic_punch A B s hs (fun v hv=>by
          rw [← hx, ← hb]; unfold H Y; rw [update_of_ne (fun he=>hv (h_ he))])
       rw [← hx,← hb] at hh; unfold H Y at hh; rw [update_self] at hh; exact hh
    exact congr_arg (fun x:U≃ₗ[ℂ] U=>x.symm) hh
lemma radiation (d N:ℕ)(h:R.family.ref d≤ N) (s u:sun) (hu:0≤ u.val) (hU:u.val ≤1/4)(hp: evalV T W (F.film (scaleSun u s)) p N=evalV T W Z p N):Z.novel.O N p (d:=d)=(F.film (scaleSun u s)).novel.O N p (d:=d):=by
    let b := s.val*u.val
    have hh:|b|≤1/4:= by unfold b; rw [abs_mul,abs_of_nonneg hu]; exact (mul_le_of_le_one_left hu (abs_le.mpr s.property)).trans hU
    have hx: |2*b|<1:=by rw [abs_mul,abs_of_pos zero_lt_two]; linarith
    let y:sun:=⟨2*b,abs_le.mp hx.le⟩; have he : scaleSun u s = Muse.verso y:=Subtype.ext (by change b=(2*b)*(1/2); ring)
    rw [he] at hp ⊢; have hv:= wagesArc Z F hk d N h y hx hp
    ext1 x; unfold Family.O TransferData.cylinder; rw [hv]; rfl
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.radiation
