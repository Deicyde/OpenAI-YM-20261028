import YM.UVExtension.Oasis.Birch
import YM.UVExtension.Beach.Under
import YM.UVExtension.Reports.Torus
import YM.UVExtension.Poppy.Summit
/-!
 # Fixed-volume full-sequence achievements for the COARSE reference.
 One family of fitted, charged recursion witnesses, storage addresses and
 supply certificates, all cutoffs, all periods, no extra hypothesis of
 converging path data/sources after fitting. `Success` is the
 specified startup/step recursion with **scalar bands**, cf. Birch.

 `Shoal` evaluates the actual fields of the output on the given period
 (also on moving offsets around bar). Literal normalization and probes,
 `Numeric` in that orbit. Conclusion allows different disks per finite family;
 strict uniformity in convergence on separated compacts. `Nutrition`
 explicitly records admission through one higher derivative -- obtained
 for all sufficiently large periods for ANY announced order/demand.
 `Stamp.converges` via .roles.loop / .roles.wand.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Oasis
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Progress.DirectedRecipe MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest Extraction Fallow Poppy Beach Upland
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
local notation "φ"=> A.B.a
set_option quotPrecheck false
open Cellar
local notation "V0"=> Cellar.yard (roseA S) L
-- explicitly receipts; matching *real* representations include the same
-- dictionaries on all choices. Tuning data exclude Rep.scalar by design.
structure Spring (S: Uses Q hG) : Prop where
    open_at : 0 < Arc.radius S
    actual (m n N)(h:m≤N)(b : ℝ)(hp: |b| < Arc.radius S): let R:= S.realBeat b N n m
        R.path=A.B.kin.path N m ∧ R.clip=((A.B.a.params m)).clip ∧ R.p=A.B.a.budget m ∧ R.activities.reg=(drawer G _).reg ∧ R.activities.forced=Ovens.Pipes.addr (folio G _) (A.B.a.budget m) ∧ Arc.betaK S m n N (b:ℂ)=Complex.ofReal R.beta ∧
          Arc.view S m n N (b:ℂ)= Tabernacle.tuning (A.B.a.budget m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) (R.activities.E,R.activities.K)
    here (N p : ℕ)(b:ℝ)(h:|b| < Arc.radius S): (∃! β:ℝ,S.Success b N p β) ∧ RG.Shoot.Competes A.B.bake p N 0 (S.realBeat b N p) ∧ (S.realBeat b N p 0).beta=A.B.a.clock.bar+b ∧ (∀ β:ℝ,S.Success b N p β → Arc.betaK S N p N (b:ℂ)=Complex.ofReal β)
    paths : Reward.Ends A.B.a A.B.kin.path A.B.kin.alpha
    has_fin (m n N)(h:m≤N): AnalyticOnNhd ℂ (Arc.betaK S m n N) (ball (0:ℂ) (Arc.radius S))∧AnalyticOnNhd ℂ (Arc.view S m n N) (ball (0:ℂ) (Arc.radius S))
    forever(m n:ℕ): Camp.SummitUV (Arc.radius S) (Arc.betaK S m n) ∧ Camp.SummitUV (Arc.radius S) (Arc.view S m n)

lemma spring {Y: Org.Bolt A}(h:Upland.Arc Q S Y):Oasis.Spring S:=by
    refine ⟨flat_pos _,fun m n N ht b hp=> Arc.real _ _ _ _ ht b (mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt hp)),fun N p b hp=> ?_,h.fields,fun m n N hp=>⟨(Arc.finiteCut S _ _ _ hp).1,(Arc.finiteCut S _ _ _ hp).2.2.1⟩, h.uv⟩
    simpa only [S.genuine] using! (Arc.exists_trial h N p b hp)

def Floral (C : Family G) : Prop :=
    ∃ (M : Metals G) (P : Rolls M.p) (A : Alloy M P)
      (R : Roost.Factor A) (S : Uses R hG) (T : Bolt A)
      (t : ℕ → ℕ) (K : ℕ → ℝ) (w : Bid.Worth)
      (Q : Bandage R K w) (L : Cellar S t Q),
        Arc R S T ∧ C = Cellar.yard (roseA S) L ∧ Oasis.Spring S ∧
        (∃ (hA : Arc R S T), let p := Mast.roseA S; Chateau Q (fun _ => 1) (centerB S hA) t
          (Cellar.gate p L) (Orchard.roof S p)) ∧
        Harvest.Barn S Q (fun _ => 1) L ∧
        Velour (Cellar.yard (Mast.roseA S) L) (Bandage.renal A.B.a)
          (Bandage.mutt A.B.a (fun _ => 1)) (Orchard.roof S (Mast.roseA S)) ∧
        (∃ a:ℝ,0 < a ∧ Metric.ball (0:ℂ) a ⊆ Broad A.B.a ∧
            ∀ d N p,t d ≤ N → Nonempty (Gale.Circuit S d N p Q L a)) ∧
        ∀ d m:ℕ, ∀ᶠ p:ℕ in atTop, ∃ r:ℝ, Nutrition L d (m+1) p r ∧
            ∀ (n:ℕ) (u:Fin n → (Hearth.roster L).Token), (∀ i,(u i).1 ≤ d) →
              ∃ b:ℝ, ∃ _hb:0 < b, ∃ hp:Metric.ball (0:ℂ) b ⊆ Broad A.B.a, ∃ W f,
                Beach.Shoal L p n u b hp W f m ∧ Beach.Realizes L p n u W b

lemma appears {C':Family G} (h: Floral (hG:=hG) C') : Getup hG C':= by
    obtain ⟨M,P,A,R,S,T,t,K,w,Q,L,h,hC,-,H,hQ,hV,h',h''⟩:= h; exact ⟨M,P,A,R,T,S,h,t,K,w,Q,L,hC,hQ,H,hV⟩
-- include the finite prefixes for physical (all fit levels on the disk).
variable {Lu:Org.Bolt A}(h:Arc Q S Lu)
variable (hp: Harvest.Barn S R (fun _=>1) L) (he:Mix.paidL (Cellar.yard (roseA S) L)) (v:ℝ)(hv:0 < v)(hV:ball (0:ℂ) v ⊆ Broad A.B.a) (hQ:∀ d N p,t d ≤ N→ Nonempty (Gale.Circuit S d N p R L v))(hS :Cloud.Leases C Q.shape A.delay) (hR:∀ i j,(Q.target i j).rate ≤ -(7/16:ℝ))
variable (hs: Chateau R (fun _=>1) (centerB S h) t (Cellar.gate (Mast.roseA S) L) (Orchard.roof S (Mast.roseA S)))
    (hg:Velour (Cellar.yard (Mast.roseA S) L) (Bandage.renal A.B.a) (Bandage.mutt A.B.a (fun _=>1)) (Orchard.roof S (Mast.roseA S)))
include h hp he hv hV hQ hS hR hs hg
lemma survives : Oasis.Floral (hG:=hG) (Cellar.yard (Mast.roseA S) L):=by
   refine ⟨X,D,A,Q,S,_,t,C,w,R,L,h,rfl,spring h,⟨h,hs⟩,hp,hg,⟨v,hv,hV,hQ⟩,fun d m=> ?_⟩
   filter_upwards [nourishing h hp d (m+1)] with p ⟨r,hr⟩
   refine ⟨r,hr,fun n u hu=>?_⟩
   obtain ⟨a₁,hv0,hA,V,y,hr'⟩:= sparksP L p n m d hv hV (fun _=>1) hp he u (fun d N=> hQ d N p) hS hR hr hu h
   obtain ⟨b,hb,hB,W,hK,hc⟩:= Beach.keep_prefix L p n hv0 hA u hv hV (fun d N=>hQ d N p) hr'
   exact ⟨b,hb,hB,W,y,hK,hc⟩
end YM.UVExtension.Oasis
