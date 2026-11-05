import YM.RG05Readout.Grants.Hike
import YM.RG05Readout.UV.Positions
/-!
# Incomes per-stage in the actual UV schedule

No already fixed rolls assumed to satisfy new invoices.

Must repurchase the
constructor.
-/
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
namespace Copper
-- coefficients on sheet's stage profile
variable (G)
def lumens (t:Stage):= Next.Foundations.price G (max t.order t.power)
def swing (t:Stage):ℝ:= 2*(Real.exp t.supportExponent* lumens G t)
theorem k_found (g : Stage) (d:ℕ) :
      ∃ C≥(1:ℝ),(∀ p q:ℕ,q≤ p → p≤ d →  upgradeCost (hol G) (localSection G p) (localSection G q) (lumens G g) (lumens G g) g.supportExponent ≤ C) ∧
         (∀ p q:ℕ,q≤ p → p≤ d →  (horizon_cost_price ((Labels.frames G).level q) ((Labels.frames G).level p)).choose ≤ C)∧
        (∀ i:Native.Letter d,Native.Cap (d+2) (Native.line i) C)∧ pulseFee d ≤ C:=by
    let f(p q:Fin (d+1)):=upgradeCost (hol G) (localSection G p.val) (localSection G q.val) (lumens G g) (lumens G g) g.supportExponent
    let h(p q:Fin (d+1)):=(horizon_cost_price ((Labels.frames G).level q.val) ((Labels.frames G).level p.val)).choose
    choose c hC hl using fun i:Native.Letter d=> Native.Cap.cost (Native.line i) (d+2)
    suffices hv:∀ᶠ s:ℝ in atTop,1 ≤ s ∧ (∀ p q:Fin (d+1),f p q≤ s)∧(∀ p q:Fin (d+1),h p q≤ s)∧(∀ i,c i ≤ s)∧ pulseFee d ≤ s by
        obtain ⟨s,hs,hf,hq,hr,he⟩:=hv.exists
        exact ⟨s,hs,fun p q h hy=>hf ⟨p,by omega⟩ ⟨q,by omega⟩,fun p q h hy=>hq ⟨p,by omega⟩ ⟨q,by omega⟩,fun i=> (hl i).increase (hr i),he⟩
    simp only [eventually_and,eventually_all];exact ⟨eventually_ge_atTop _,fun i j=>eventually_ge_atTop _,fun i j=>eventually_ge_atTop _,fun i=>eventually_ge_atTop _, eventually_ge_atTop _⟩

def optics (t:Stage) (d:ℕ):=(k_found G t d).choose
abbrev marks (G:Gauge)(d:ℕ):= (i:Native.Letter d) × ((Labels.frames G).level (kept i)).Index

def inverseFuel (d:ℕ)(p:ℝ)(g:Stage):= max 1 (clipPrice (Fintype.card (marks G d)) d (beamCost d p (optics G g d)) p)
lemma cash_fill (d:ℕ) (z:ℕ) (s:ℕ→Stage) (c:ℕ→ℝ): ∃ b:ℝ,1 ≤ b∧ (s z).columns ≤ b ∧
    ∀ j:ℕ,j ≤ z+1 → ahead (optics G (s z) d) (c j) d*(2*inverseFuel G d (c j) (s z)) ≤ b:=by
   let B(j):= ahead (optics G (s z) d) (c j) d*(2*inverseFuel G d (c j) (s z));
   let y (i:Fin (z+1+1)):= B i.val
   obtain ⟨b,h⟩:= Finite.exists_max y; let p:=(s z).columns; refine ⟨max p (y b),(le_trans (Stage.columns_ge _) (le_max_left ..)),le_max_left ..,fun i hi=> ?_⟩; exact ((h ⟨i,by omega⟩)).trans (le_max_right ..)
variable (d:ℕ)
def ash (z:ℕ)(s:ℕ→Stage)(c:ℕ→ℝ):=(cash_fill G d z s c).choose

lemma upfront (s:ℕ→Stage)(C:ℕ→ℝ):∃ b:ℕ→ℕ, ∀ p q d:ℕ,q≤ p → d≤ q→ ∀ L:Side,b p≤ L.val→
    Crossed d p L (s p) (C p) (optics G (s q) d) (ash G d p s C) (ash G d q s C) (inverseFuel G d (C p) (s q)) (swing G (s p)):=by
   choose l hl using fun p q d=> eventual d p (s p) (C p) (optics G (s q) d) (ash G d p s C) (ash G d q s C) (inverseFuel G d (C p) (s q)) (swing G (s p))
   let b(p):=((Finset.range (p+1)).product (Finset.range (p+1))).sup (fun j=> l p j.1 j.2);
   exact ⟨b,fun p q d h hz L hL=> hl p q d L (le_trans (show l p q d ≤ b p from Finset.le_sup (b:=(q,d)) (f:=fun i=> l p i.1 i.2) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h),Finset.mem_range.mpr (show d<p+1 from by omega)⟩)) hL)⟩ -- test arg
variable {G}

local notation "Φ!"=> (A.B.a)
local notation "Y"=> Orchard.Path S v
-- Produce cursor. Must verify same family S...
variable (m N p:ℕ)(hm:m<N)(hd:d+3≤ A.B.a.clock.J m)
local notation "t"=> (Φ!).params m
local notation "b"=> (Φ!).params (m+1)
local notation "J"=> (Φ!).clock.J (m+1)
local notation "s₀"=> lumens G t
variable (hX:Cub.Moved R) {f:ℕ→ℕ} {U:Org.Bolt A} (a:Upland.Arc X S U) (hα: Lisle f A.B.a)
local notation "u"=>Mast.Cellar.yard v (Mast.cellar S R a f hα)
local notation "D"=> Orchard.roof S v N p m hm
-- κ from Nest current fees
include hX hd
lemma expended (hV: Push.Local.hitWidth ((Y).rep N p m).p*Push.Local.kappa Y m ≤ 1) (hK:Push.Local.kappa Y (m+1) ≤1) :∃ T:∀ i:Native.Letter d,Heading ((u).labels.level (kept i)),
    Address.Plot D s₀ (optics G t d) (C J) (Doors.rate ((Φ!).S.block m)) (swing G b) T:=by
    have h(d':ℕ)(hh:d'≤d): ∃ (T:Heading ((u).labels.level d'))(a':ℝ),Pricing ((u).localSection d') (u).path N p m (u).params (D) T a' (C J) (Doors.rate ((Φ!).S.block m)) (swing G b) ∧ Push.Local.triangularPrice ((u).labels.level d') a' ≤ C J:=by
       obtain ⟨T,hV,hq,hA⟩:= RG05Readout.UV.positions S v R d' N m p hm (by omega) hX
       let Y':= (Y); have hp: ((Y').rep N p (m+1)).p =(Φ!).budget (m+1):=(Orchard.selected S v).represents _ _ _ hm|>.vac
       rw [hp] at hq; exact ⟨T,_,hq,hA⟩
    choose T y hT using fun i:Native.Letter d=> h (kept i) (Nat.sub_le ..)
    obtain ⟨Y',Q,H,HT⟩:= h 0 (Nat.zero_le _)
    let K:= optics G t d
    obtain ⟨hk,ho,hp₁,hF,hS⟩:= (k_found G t d).choose_spec
    have hz: ∀ z≤d, Push.Local.Readable (u).params ((u).localSection z) ((u).path.rep N p m).p ((u).S.side m p) s₀:=by
       intro z hi; let a:=(Φ!); have hc : z ≤ a.clock.J m:=by dsimp [a]; omega
       have hs:= Doors.Latch.lengths (R.clock.sequences m z hc) p
       have hq:= R.clock.stage m; have he:=Push.Local.foundation_readable G z (B:=a.budget m) hs (hc.trans hq.1) (hc.trans hq.2)
       exact (Orchard.selected S v|>.represents N p m hm.le|>.vac).symm ▸ he -- align
    have hη:((u).path.rep N p m).p.supportExponent=(t).supportExponent:=by
        change ((Y).rep N p m).p.supportExponent=(t).supportExponent;rw [(Orchard.selected S v|>.represents N p m hm.le|>.vac)];rfl
    refine ⟨T,⟨hz,?_,hp₁,hF,hk,hS,?_,hV⟩,  (H.lower.price.trans ((triangle_cost1 _ H.lower.price).trans HT)), (Doors.rate_pos _).le,?_,fun i=>⟨y i,hT i⟩, ⟨Y',Q,H⟩,H.soundD,hK⟩
    · rw [hη]; exact ho
    · apply Nonempty.intro; apply Keeper.sufficient; rw [show (u).path.rep N p m=(ray S N p m (v N p) hm).body.result beam0 from ponds S N p m (v N p) hm]; exact slots0 S N m p (v N p) hm
    unfold swing lumens; exact mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Next.Foundations.price_one_le ..)))
end Copper
end YM.RG05Readout
