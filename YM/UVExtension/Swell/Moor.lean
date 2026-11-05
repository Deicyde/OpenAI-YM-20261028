import YM.UVExtension.Swell.Too
import YM.UVExtension.Gale.Flange
import YM.UVExtension.Hearth.Tureen
/-! # Two field lookups now kept under uniform a,B^ bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Swell
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a z:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
local notation "T"=> A.B.a.S
local notation "P"=> A.B.a.budget N
local notation "R0"=> desk a ha
local notation "ℍ"=> Row a
open Cellar
set_option quotPrecheck false
local notation "F"=> (frames G).level d
local notation "l"=> localSection G d
local notation "J"=> (F).Index
variable (Y:Circuit S d N n R L a)(x:((frames G).level d).Coeff)
local notation "q"=> (T).a N
-- absolute prices
local notation "Z"=> ball (0:ℂ) a
open Gale.Circuit
variable (v:ℕ→ℕ→Rose S)
local notation "S0"=> L.yard v
-- scaled unmasked and lens fields at origin m. use Vintage.Find only where necessary. SAME definitions for ALL schedules.
section fixed
local notation "V"=> L.yard (fun _ _=>rose0 S)
-- evaluate at reference.Birth.
private lemma draft (X:Family G) {n m:ℕ}{d:ℕ}(f:X.label d): candidate X m n d f=∑ j, f j • candidate X m n d (Extra.Histories.Size.axis (X.labels.level d) j):=by
    let F':= X.labels.level d; let L:= X.localSection d; let r:= X.path.levels.clock.threshold m; let A:=((X.S.a m:ℂ)^d)⁻¹; let g:F'.Coeff→ Config G (X.side m n)→ℂ:= fun x=> A • L.places (F'.scaled r⁻¹ x) 0
    have ht: IsLinearMap ℂ g:=by
       refine ⟨fun i j=>funext fun U=> ?_,fun t j=>funext fun U=>?_⟩
       · unfold g SectionData.places; simp only [map_add,Pi.smul_apply,Pi.add_apply,L.eval_linear.map_add,smul_add]
       unfold g SectionData.places; simp only [map_smul,Pi.smul_apply,L.eval_linear.map_smul]; rw [smul_comm]
    let p:= IsLinearMap.mk' _ ht; change p f= ∑ j, f j • p (Extra.Histories.Size.axis F' j); rw [← coeff_sum X f, map_sum]; refine Finset.sum_congr rfl (fun i _=>?_); rw [coeff_sum,map_smul]; rfl -- Size alias check args
def beamP (T':Levels G)(m n d:ℕ)(L: ((frames G).level d).Coeff): Config G (T'.S.side m n)→ℂ:=
    ((T'.S.a m:ℂ)^d)⁻¹ • (localSection G d).places (((frames G).level d).scaled (T'.budget m).threshold⁻¹ L) 0

def lampP (T':Levels G)(m n d:ℕ)(L: ((frames G).level d).Coeff)(U:Config G (T'.S.side m n)):= ((T'.S.a m:ℂ)^d)⁻¹* L 0 + masked (T'.budget m).threshold ((localSection G d).footprint (0:Site (T'.S.side m n))) (beamP T' m n d (((frames G).level d).core L)) U

lemma bit (v:Keys S) (x: (F).Coeff): candidate (yard v L) m n d x=beamP A.B.a m n d x:= rfl
lemma spear (he:m ≤ N)(v:Keys S)(x: (F).Coeff): lens (yard v L) N m n d x= lampP A.B.a m n d x:= by
    rw [Vintage.YM.MergeProof.Accent.scopes (yard v L) N m n d x (L.intakeV v) he]; rfl
lemma topBirth (v:Keys S)(he:(↑(v N n).val:ℂ) ∈ Metric.ball (0:ℂ) a):
    (L.yard v).O N n (d:=d) x 0= ∑ i:J, Gale.Circuit.primary S d N n R L Y x ((v N n).val:ℂ) i • beamP A.B.a N n d (Extra.Histories.Size.axis (F) i) := by
      let U:= L.yard v; let Q':= Gale.Circuit.primary S d N n R L Y x ((v N n).val:ℂ); have ht1:= Y.blazes S d N n R L x|>.2.2
      have hV: U.O N n (d:=d) x 0= candidate U N n d Q':=by unfold Q'; rw [ht1 v he]; rfl
      change U.O N n x _= _; rw [hV, draft U]; rfl
lemma parser (he:m ≤ N)(v:Keys S)(x: (F).Coeff): science (L.yard v) m N n d x= ∑ i:J,x i • lampP A.B.a m n d (Extra.Histories.Size.axis (F) i) :=by
   unfold Hearth.science; exact Finset.sum_congr rfl (fun i _=>congr_arg (fun Q':Config G (A.B.a.S.side m n)→ℂ=> x i • Q') (spear L _ _ _ _ he v _))
-- HP_W uses full complex points and roots. shrink for layouts. real weights on desk.
include ha
lemma skew (i:J): Sail R0 (fun d':Row a=> primary _ _ _ _ _ _ Y x ( (d'.val:ℂ)) i) ((A.B.a.S.a N)⁻¹* (F).coeffSize x):=by
    let f:= primary S d N n R L Y x; obtain ⟨hf,hF,-⟩:= Y.blazes S d N n R L x; exact ⟨fun z=> f z i,bumps _ (fun z=> f z i) (fun z hz=> differentiableWithinAt_pi.mp (hf z hz) i),fun _=>rfl,fun z hz=> ((norm_le_pi_norm (f z) i).trans (show ‖f z‖≤ _ from Local.norm_le_size ..)).trans (hF _ hz)⟩
lemma fried (hx:t d ≤ m) (hm:m≤N) (i:J): Sail R0 (fun d':Row a=> fetch _ _ _ _ _ _ Y x m hx ((d'.val:ℂ)) i) ((A.B.a.S.a m)⁻¹*(2*(F).coeffSize x)) :=by
   let f:= fetch S d N n R L Y x m hx; obtain ⟨hf,hF⟩:= Y.bites S d N n R L x m hx hm; exact ⟨fun z=> f z i,bumps _ (fun z=> f z i) (fun z hz=> differentiableWithinAt_pi.mp (hf z hz) i),fun _=>rfl,fun z hz=> ((norm_le_pi_norm (f z) i).trans (show ‖f z‖ ≤ _ from Local.norm_le_size ..)).trans (hF _ hz)⟩
omit ha
-- width r(d).
local notation "r"=> lensScope V d
lemma pkern (i:J): Interior (window (0:Site (A.B.a.S.side N n)) (lensScope (L.yard (fun _ _=> rose0 S)) d)) (beamP A.B.a N n d (Extra.Histories.Size.axis (F) i)):=
    (Vintage.YM.Push.GridApprox.candidate_fits (L.yard (fun _ _=> rose0 S)) (L.intakeV _) N n d _).enlarges (window_large (Nat.le_add_right ..))
lemma pmark (i:J): Interior (window (0:Site (A.B.a.S.side N n)) r) (lampP A.B.a N n d (Extra.Histories.Size.axis (F) i)):=by
    let v':= fun _ _:ℕ=>rose0 S; rw [← spear L _ _ _ _ le_rfl v']; exact Vintage.YM.MergeProof.Accent.visible _ _ _ _ _ _ (L.intakeV _) le_rfl
end fixed
end YM.UVExtension.Swell
