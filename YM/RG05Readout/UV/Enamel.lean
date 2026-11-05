import YM.RG05Readout.Grants.Price
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout
open YM.UVExtension UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Bid Planned.GuardedAtom Guard Motion Address Native
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Roost.Factor A}
    (S:Uses X hG) (v:Keys S) {C:ℕ→ℝ}{W:Worth}(R:Legato.Bandage X C W)
set_option quotPrecheck false
/-!
# Cursor and graph supply across entire UV tape
-/
namespace UV
open Copper
-- export ink
structure Lacquer (X:Family G)(D:∀ N p m:ℕ,m<N→ GaugeDoor (X.path.rep N p (m+1)) (X.path.rep N p m)):Prop where
   currency :∃ f:ℕ→ℕ→ℝ,(∀ d m,(X.path.levels.params m).columns ≤ f d m)∧∀ d,∀ᶠ m in atTop,∀ p N:ℕ,∀ h:m<N,SignedPrice X m p d N (D N p m h) (f d (m+1)) (f d m)

variable {t:ℕ→ℕ} {J:Org.Bolt A} (a:Upland.Arc X S J) (ha:Lisle t A.B.a)(hx:Cub.Moved R)
local notation "W₀"=> Mast.cellar S R a t ha
local notation "F"=> Mast.Cellar.yard v W₀
local notation "V"=> M.p.profile
local notation "Ω"=> A.B.a
-- omit hG
-- bound stalls reused from Comply and support hatted trajectory
include R
lemma stalls (m:ℕ): Push.Local.hitWidth ((Ω).budget m)* Real.sqrt ((Ω).clock.forcedAllowance m) ≤ 1:=by
    rw [Blush.glyph_eq]; exact (R.stamp _ _ (step_paid A.B.a m) 0 (Nat.zero_le _) _ (A.B.valid.pays m)).2 A.B.a m  (params_eq A.B.valid m) rfl
include hx hG
lemma under (hF:(F).Makes) (he:∀ i j d:ℕ,j ≤ i →  d≤ j →  Crossed d i (P.L i) (M.p.profile i) (C i) (optics G (M.p.profile j) d) (ash G d i M.p.profile C) (ash G d j M.p.profile C) (inverseFuel G d (C i) (M.p.profile j)) (swing G (M.p.profile i))):
     Lacquer F (Orchard.roof S v):=by
    let f d i:= ash G d ((Ω).clock.J i) M.p.profile C
    let K:= (F)
    have hf(i):K.path.levels.params i=V ((Ω).clock.J i):= params_eq A.B.valid i
    refine ⟨f, fun d m=> (show (F).path.levels.params m= _ from hf m) ▸ ((cash_fill G d ((Ω).clock.J m) (V) C).choose_spec.2.1),fun d=>?_⟩
    filter_upwards [A.B.a.fits.deep.eventually_ge_atTop (d+3), wraps K hG d] with m hm ht p N h
    let z' :=K.path.rep N p; have hp':0 ≤ Push.Local.kappa (F).path (m+1):= Real.sqrt_nonneg _
    have hs:Push.Local.hitWidth ((Ω).budget m)* Push.Local.kappa (F).path m ≤ 1:= stalls R m
    have hQ: Push.Local.hitWidth (z' m).p* Push.Local.kappa (F).path m ≤ 1:= (hF.wilson.represents N p m h.le|>.vac).symm ▸ hs
    have hB: Push.Local.kappa (F).path (m+1) ≤ 1:= (le_mul_of_one_le_left hp' (Push.Local.width_one_le ((Ω).budget (m+1)))).trans (stalls R (m+1))
    obtain ⟨T,hT⟩:= Copper.expended S v R d m N p h hm hx a ha hQ hB
    let i:=(Ω).clock.J (m+1); let j:=(Ω).clock.J m; let T0:= (M.p.profile j); have h' : (Ω).params m=T0:= params_eq A.B.valid m; let Q:= inverseFuel G d (C i) T0
    apply enamel hF h hT (Q:=Q)
    · let p1:= step_paid A.B.a m
      change Crossed d i ((Ω).S.block m) ((Ω).params (m+1)) (C i) (optics G ((Ω).params m) d) (f d (m+1)) (f d m) Q (swing G ((Ω).params (m+1)))
      rw [params_eq A.B.valid,h',Push.PriceCompiler.block_eq A.B.valid]; exact he i j d p1.1 (le_trans (Nat.le_add_right d 3) hm)
    · exact zero_le_one.trans (le_max_left ..)
    · unfold Q; rw [h']; exact le_max_right ..
    · rw [h']; exact ((cash_fill G d j (V) C).choose_spec.2.2 i ((Ω).fits.stepSlow m))
    · exact (cash_fill G d i (V) C).choose_spec.1
    · exact (cash_fill G d j (V) C).choose_spec.1
    let y k:=K.path.rep N p k; let H₁:=(hF.wilson.represents N p m h.le).vac
    let H₂:=(hF.wilson.represents N p (m+1) h).vac
    rw [H₁,H₂]; exact max_le (ht p).1 (ht p).2
end UV
end YM.RG05Readout
