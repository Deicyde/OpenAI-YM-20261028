import YM.UVExtension.Hearth.Palms
import YM.UVExtension.Hearth.Dine
import YM.UVExtension.Mast.Theme
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory Push GridApprox Mast Steady
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
open Relay Mast.Cellar Steady Push GridApprox Accent Cells
local notation "Φ"=> A.B.a
variable {t:ℕ→ℕ}{S v R} (U:Cellar S t R) (K:ℕ→ℕ)(h:Scrim (U.yard v) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a) (J k:ℕ)(w:ℝ)(hw:0<w)(hz:Stock.Tabs.opens A.B.a 1 J m)
local notation "C0"=> yard v U
local notation "F"=> (C0|>.labels.level d)
local notation "K0"=> lensScope C0 d
local notation "o!"=> (0:Site ((C0).side k n))
local notation "T!"=> A.B.a.S

-- explicitly keep lenses/data for later continuation in β.
def science (C:Family G)(k N n d:ℕ)(f:C.label d): Config G (C.side k n)→ℂ:= ∑ i: (C.labels.level d).Index,f i • lens C N k n d (Size.axis (C.labels.level d) i)

lemma solidT (C:Family G)(N d k n:ℕ)(x: (C.labels.level d).Index) (h:Vintage.YM.Family.Makes C)(hk:k≤N): lens C k k n d (Size.axis (C.labels.level d) x)= lens C N k n d (Size.axis (C.labels.level d) x):=by
   rw [Vintage.YM.MergeProof.Accent.scopes _ _ _ _ _ _ h le_rfl,Vintage.YM.MergeProof.Accent.scopes _ _ _ _ _ _ h hk] -- scopes
lemma tuneV (C:Family G)(p k d:ℕ)(h:Vintage.YM.Family.Makes C) (f:ℕ→ C.label d)(hf: UVExtension.Arrives f): Tune atTop (fun N=> science C k N p d (f N)):=by
   let L i:= lens C k k p d (Size.axis (C.labels.level d) i); let A (i:(C.labels.level d).Index)(N:ℕ):= (f N i) • L i
   obtain ⟨b,hb⟩:=hf; have hx i:Tune atTop (A i):= mulT (Tune.constant (fun n=>f n i) _ ((continuous_apply i).continuousAt.tendsto.comp hb)) (envelopeT (cylinder_env (Vintage.YM.MergeProof.Accent.visible _ _ _ _ _ _ h le_rfl)))
   apply (Tune.term Finset.univ A (fun i _=> hx i)).switch; filter_upwards [eventually_ge_atTop k] with N hN; funext k; rw [science,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; unfold A L; rw [solidT C N d _ p i h hN] -- k shadow
lemma repays (C:Family G)(N d k p J:ℕ)(t:C.label d)(L: (C.labels.level d).Index→ C.label d) {x:C.label d}(h:Vintage.YM.Family.Makes C)(hp:J ≤ k)(hn:k≤N)(hx:x=∑ i,t i • L i){q g:ℝ}(hh: (C.labels.level d).coeffSize t ≤ g)(hq:0≤q)(he:∀ i,LatchUp C k J N p d (hp.trans hn) hn q i (L i))(hc:GridApprox.room C.path.levels J k (lensScope C d))(hz:∀ v:C.label d,Interior ((tilesAt C.S p (hp.trans hn)).chamber 0) (C.O N p v 0)) :
     let B:= science C k N p d t
     Interior (GridApprox.window (0:Site (C.side k p)) (lensScope C d)) B∧ (tilesAt C.S p (hp.trans hn)).rootTest (C.beta N p) (GridApprox.backTo C.path N p hn B-C.O N p x 0) ≤ g*q:=by
   intro B
   let T:=tilesAt C.S p (hp.trans hn); let Z:= C.labels.level d; let A i:= lens C N k p d (Size.axis Z i)
   let Q i:= C.O N p (L i) 0; let G i:= backTo C.path N p hn (A i)
   let S i:= G i-Q i
   have hL i: Interior (GridApprox.window (0:Site (C.side k p)) (lensScope C d)) (A i):=(he i).covers
   refine ⟨inSum _ _ _ (fun i _=> (hL i).scale _),?_⟩
   have ht:= Vintage.YM.Cells.seamless h N p
   have e(i): T.rootTest (C.beta N p) (S i)≤q:=(he i).gets _
   rw [show C.O N p x 0=∑ i,t i • Q i from by
         rw [hx]; let A₀:= (C.linearO N p d 0).mk' _; change A₀ (∑ i,t i • _)=_; rw [map_sum]; simp_rw [map_smul]; rfl, show backTo C.path N p hn B-(∑ i,t i • Q i)=∑ i, t i • S i from by
                rw [show B=∑ i,t i • A i from rfl, backTo_sum _ hn (fun i=> t i • A i) Finset.univ (fun i _=> cylinder_env ((hL i).scale (t i)))]; simp_rw [behind,S,smul_sub,Finset.sum_sub_distrib]; rfl]
   apply (Next.UVStress.root_sum T (C.beta N p) Finset.univ S t (fun i _=> Next.UVStress.minus (whereBack C.path hn hp (lensScope C d) (hL i) hc) (hz _)) ht).2.trans
   exact (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=> mul_le_mul_of_nonneg_left (e i) (norm_nonneg (t i)))).trans ((Finset.sum_mul _ _ _).symm.trans_le (mul_le_mul_of_nonneg_right hh hq))

local notation "L!"=> t d
include hK h hw hz hv
lemma peeling (f:C0|>.label d) (hd:L! ≤ m)(hk:m ≤ k)(hc:GridApprox.room A.B.a J k (lensScope (U.yard v) d))(hg:w*‖alto (Orchard.Path S v) m d‖*(4*(1+(A.B.a.params k).columns)/Bid.gainChart (Orchard.Path S v) k m) ≤ Legato.Bandage.fly A.B.a d m/2) : ∃ g:ℕ→ Config G ((yard v U).side k n)→ℂ, Tune atTop g ∧∀ᶠ N in atTop,∃ hN:k≤ N, Interior (GridApprox.window (0:Site ((yard v U).side k n)) (lensScope (yard v U) d)) (g N) ∧ (tilesAt A.B.a.S n (hz.1.trans (hk.trans hN))).rootTest ((yard v U).beta N n) (GridApprox.backTo (C0).path N n hN (g N) - (yard v U).O N n (d:=d) f 0) ≤ stockK (yard v U) k d f*(stakes (yard v U) J m/w) :=by
   obtain ⟨g,s,hP,hq,hX⟩:= lensM (v:=v) d m n U x hv K h hK J k hz w hw hd hk hg hc f
   let V':= intakeV v U
   refine ⟨_, tuneV C0 n k d V' g hP,?_⟩; filter_upwards [eventually_gt_atTop k, Vintage.YM.Stock.clear_interior C0 V' J d] with i hi hL; obtain ⟨hn,hG⟩:= hL; obtain ⟨ho,hQ,hS⟩:= hX i hi
   exact ⟨hi.le, repays C0 i d k n J (g i) (fun j=>s j i) V' (hz.1.trans hk) hi.le hQ hS (div_nonneg (Real.exp_pos _).le hw.le) ho hc (hG n 0)⟩
end YM.UVExtension.Hearth
