import YM.UVExtension.Gale.Scud
import YM.UVExtension.Gale.Ivy
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{n m:Side}{P Q:BudgetPoint}
local notation "L'"=> RoutesF F n m P Q A
local notation "E₁"=> Cow G m P d A
local notation "E₀"=> Cow G n Q d A
local notation "N!"=> Bucket F Q A n
variable (S:Set ℂ)(L:ℂ→RoutesF F n m P Q A)
set_option synthInstance.maxHeartbeats 90000
variable {S L} {r t u w s e c:ℝ}{z:ℂ} (hn: 2≤ n.val) (U:F.Coeff→ₗ[ℂ] Cow G n Q d A) (V:Lacing.RoutesF F n m P Q A) (x:Bucket F Q A n)
-- latch ships. real at tone.Leg. source minus paint re-entry after raw. Pay down.
noncomputable def spool (F:Frame G d)(A:Hol G)(n:Side)(Q:BudgetPoint)(U:F.Coeff→ₗ[ℂ] Cow G n Q d A)(x: Bucket F Q A n):Bucket F Q A n := ∑ i:Bool, rooms n F A Q (aisleN (code Bool) i) (Relay.twain x (-x.1,U (-x.1)) i)
lemma charge (w e:ℝ)(hw:1 ≤ w)(hu:Length F U w)(hp:0 ≤ e)(hr:F.coeffSize x.1≤ e)(ht: ‖x.2‖≤ e): ‖(spool F A n Q U x).2‖ ≤ 2*w*e:= by
    let P(i:Bool):=Relay.twain x (-x.1,U (-x.1)) i; let Qx(i:Bool):=rooms n F A Q (aisleN (code Bool) i) (P i)
    have hA(i): ‖(Qx i).2‖≤ w*e:=by
       apply le_trans (Tips.deal _ _); cases i
       · change ‖U (-x.1)‖≤ w*e; have hg:= (size_core F (-x.1)); rw [show F.coeffSize (-x.1)=F.coeffSize x.1 from by simp [Frame.coeffSize] ] at hg; exact (hu _).trans (mul_le_mul_of_nonneg_left (hg.trans hr) (zero_le_one.trans hw))
       exact ht.trans (le_mul_of_one_le_left hp hw)
    rw [spool,Fintype.sum_bool]; exact (norm_add_le (Qx true|>.2) (Qx false|>.2)).trans ((add_le_add (hA _) (hA _)).trans_eq (show w*e+w*e=2*w*e from (by ring)))
variable {l:Side}{T:Heading F}{U}
include V
lemma charges (Y:Cow G m P d A)(h:Tips V l T u t)(he:‖Y‖≤ s*e)(hw: Length F U w)(hP:1≤w)(hs:1≤ s)(hp:0≤e): let x:=V.rain Y none; let a:=2*u*(s*e)
    F.coeffSize x.1 ≤ a∧ ‖(spool F A n Q U x).2‖≤ 2*w*a:=by
    intro x a; have h': x= V.Pillow Y:= by unfold x;rw [h.counts.rains,h.hush,map_zero,zero_add]
    have he' : (2*u)*‖Y‖≤ a:=mul_le_mul_of_nonneg_left he (mul_nonneg zero_le_two h.counts.calm)
    rw [h']; have ht' := (le_mul_of_one_le_left (size_nonneg ..) (orbitCost_one_le F)).trans ((h.counts.altX Y).trans he'); exact ⟨ht',charge U _ w a hP hw ((size_nonneg ..).trans ht') ht' (((le_max_right ..).trans (h.counts.serves Y).2).trans he')⟩
end YM.UVExtension.Gale
