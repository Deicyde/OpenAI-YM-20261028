import YM.UVExtension.Swell.Boat
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
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a z b:ℝ}(ha:0<a)(hb:0<b)(he:b≤a)(hp:Metric.ball (0:ℂ) b ⊆ Camp.Broad A.B.a)
open Cellar Gale.Circuit
local notation "T"=> A.B.a.S
local notation "φ"=> A.B.a
local notation "P"=> A.B.a.budget m
local notation "R0"=> desk b hb
local notation "ℍ"=> Row b
set_option quotPrecheck false
variable (u:Fin k→ (roster L).Token) (W:(i:Fin k) → Gale.Circuit S (u i).1 N n R L a)
local notation "F"=> fun i=> (frames G).level ((u i).1)
local notation "Υ"=> (fun i=>(F i).Index)
local notation "A'"=> ((i: Fin k)→ (F i).Index)
-- Width
private def windows (i:Fin k):ℕ:= lensScope (yard (fun _ _=> rose0 S) L) (u i).1
-- gauge choice S.W.Vol
local notation "ξ0"=> A.B.a.clock
private def bill (i:Fin k):= ((T|>.a m)⁻¹ * (2*(F i).coeffSize ((u i).2)))
local notation "billT"=> bill L m k u
private def cheq (z:ℝ):= (∑ e:A', (∏ i,bill L m k u i)* reward A.B.a k (windows L k u) (z*((T|>.a m)⁻¹)^3) (∏ i,costP A.B.a m (u i).1 (e i)) m)

variable (hx: UVExtension.Cloud.Leases C Q.shape A.delay)
include hx
lemma verdant (z:ℝ):PolyB A.B.a.S (fun m=>cheq L m k u z):=by
    let v j:= ((T).a j)⁻¹; have hp:= PolyB.inverse A.B.a.S; have he(i):PolyB (T) (fun j=>bill L j k u i):= hp.mul (PolyB.const ..)
    refine PolyB.sum Finset.univ _ (fun i _=>?_); exact (PolyB.waves Finset.univ _ (fun i _=> he i)).mul (((PolyB.const _ z).mul (hp.pow 3)).mul ((((taxes Q hx).pow _).mul (PolyB.waves Finset.univ _ (fun j _=> holds (d:=(u j).1) _ (i j)))).mul (PolyB.const ..)))
omit hx
variable (hn:Harbour (desk b hb) k (A.B.a.budget N) (fun d:Row b=> S.realBeat d.val N n N) (z*(A.B.a.S.a N)⁻¹^3))
variable (hz:0 ≤ z)
include ha hb he hp hz hn W
lemma presto (q:Fin k→ Site (A.B.a.S.side N n)) : Sail (desk b hb) (fun d:Row b=> served N n L (roseK S hb hp d) k u q) (cheq L N k u z):=by
    let t'(i:Fin k):=u i|>.1; let R'(d:Row b):= S.realBeat d.val N n N; let x(i):= u i|>.2; let K:= windows L k u; let y:= bill L N k u; let v(d:Row b): Keys S:=fun _ _=> roseK S hb hp d; let C d:= L.yard (v d)
    let Y(i:Fin k)(j:Υ i):= beamP A.B.a N n (u i).1 (Size.axis (F i) j); let Z(i:Fin k)(j:Υ i):= costP A.B.a N (u i).1 j; let X(i:Fin k)(j:Υ i)(z:ℝ):= Gale.Circuit.primary S (u i).1 N n R L (W i) (x i) (z:ℂ) j
    have hh(i j):Interior (GridApprox.window 0 (K i)) (Y i j):= pkern L N n (u i).1 j; have hy i j U: ‖Y i j U‖≤ Z i j:= (pricing n N (t' i) _ j U).1
    let S'(d:Row b) (i:Fin k):= ∑ j,X i j d.val • Y i j
    have hv(i j): Sail (desk b hb) (fun d:Row b=> X i j d.val) (y i):=by
        refine (Sail.shrink ha (f:=X i j) (skew L N n _ ha (W i) (u i).2 j) hb he).mono (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (WilsonStartup.Mark.coeff_nn _) one_le_two) (inv_nonneg.mpr ((T).a_pos _).le)) -- f names
    let f(d:Row b):= cargo k q (S' d); have h(d i): (C d).seen (u i) (0:Site (A.B.a.S.side N n))= S' d i:= topBirth L N n (t' i) _ (u i).2 (v d) (ball_subset_ball he (desk b hb|>.within d)) -- α point infer
    have hX(d:Row b): (C d).numeric N n u q=moment (R' d).beta (f d):=by
       apply congr_arg (moment (R' d).beta ·)
       change (fun U=> ∏ i,(C d).seen (u i) (q i) U) = _; funext U; refine Finset.prod_congr rfl (fun i _=> ?_)
       rw [← h d i]; let hQ:= (C d).translation 0 (q i) (d:=t' i) (u i).2 U; rw [zero_add] at hQ; exact hQ.symm
    have hl(d:Row b): served N n L (roseK S hb hp d) k u q=tasting (R' d) (f d):=by
       let G:= (C d); let h':Vintage.YM.Family.Makes G:= Cellar.intakeV _ L
       have hf: Envelope (f d):= cylinder_env (loaded k q K (S' d) (fun i=> Hearth.inSum _ _ _ (fun j _=> (hh i j).scale _)))
       have ht := Hearth.scaledK ((C d).path) (selected S (v d)) N N n le_rfl hf; rw [GridApprox.backTo_self] at ht
       exact (cordial N n L (v d) k u (fun j=> (W j).token) q).symm.trans ((hX d).trans ht)
    simp_rw [hl]; exact paces S N n N k hb hp le_rfl K Y (fun i j (d:Row b)=> X i j d.val) (fun i _=> y i) Z hv hh hy q hn (mul_nonneg hz (pow_nonneg (inv_nonneg.mpr ((T).a_pos _).le) _))
omit hn W ha hb he hp hz
variable (hv:Harbour (desk b hb) k (A.B.a.budget m) (fun d:Row b=> S.realBeat d.val N n m) (z*(A.B.a.S.a m)⁻¹^3))
    (hu:∀ i,t (u i).1≤ m)
local notation "C₀"=> L.yard (fun _ _=> rose0 S)
def crew (x:ℝ) (i:Fin k): Config G (A.B.a.S.side m n)→ℂ := science (C₀) m m n (u i).1 (fetch _ _ _ _ _ _ (W i) (u i).2 m (hu i) (x:ℂ))
def fancy (q:Fin k→Site (A.B.a.S.side m n))(x:ℝ):= tasting (S.realBeat x N n m) (cargo k q (crew L N n m k u W hu x))
-- k any cutoff above. no need rosters available perBeta.Fitted.
include hv W ha hb he hp hz
lemma full (hm:m≤N)(q:Fin k→ Site (A.B.a.S.side m n)) : Sail (desk b hb) (fun d:Row b=> fancy L N n m k u W hu q d.val) (cheq L m k u z):=by
    let t'(i:Fin k):=u i|>.1; let x(i):= u i|>.2; let K:= windows L k u; let y:= bill L m k u; let V':Keys S:=fun _ _=> rose0 S; let C:= L.yard V'
    let Y(i:Fin k)(j:Υ i):= lampP A.B.a m n (u i).1 (Size.axis (F i) j); let Z(i:Fin k)(j:Υ i):= costP A.B.a m (u i).1 j; let X(i:Fin k)(j:Υ i)(z:ℝ):= Gale.Circuit.fetch S (u i).1 N n R L (W i) (x i) m (hu i) (z:ℂ) j
    have hh(i j):Interior (GridApprox.window 0 (K i)) (Y i j):= pmark L m n (u i).1 j; have hy i j U: ‖Y i j U‖≤ Z i j:= (pricing n m (t' i) _ j U).2
    have hp'(i j): Sail (desk b hb) (fun d:Row b=> X i j d.val) (y i):= Sail.shrink ha (f:=X i j) (fried L N n m _ ha (W i) (u i).2 (hu i) hm j) hb he
    let S'(d:Row b) (i:Fin k):= ∑ j,X i j d.val • Y i j; let f(d:Row b):= cargo k q (S' d); have he' d' : crew L N n m k u W hu (d':Row b).val=S' d':=by funext i; exact parser L m n m (u i).1 le_rfl V' _
    change Sail _ (fun d:Row b=> tasting _ (cargo k q (crew L N n m k u W hu d.val))) _; simp_rw [he']; exact paces S N n m k hb hp hm K Y (fun i j (d:Row b)=> X i j d.val) (fun i _=> y i) Z hp' hh hy q hv (mul_nonneg hz (pow_nonneg (inv_nonneg.mpr ((T).a_pos _).le) _))
omit hv W hb he hp hz
-- ∃ strict period disk.Crude poly.MESH cutoff independent. analytics bounded both births and any intermediate candidate from chosen Circuits; may choose separated compacts later.
variable (hr:∀ i j,(Q.target i j).rate ≤ -(7/16:ℝ))(h:ball (0:ℂ) a⊆Camp.Broad A.B.a)
include h R hr hx
lemma upper : ∃ B v,∃ hv:0< v, ∃ hl:v≤a, 0<B ∧∀ᶠ m in atTop, ∀ N,m≤N→ (∀ q:Fin k→ Site (A.B.a.S.side N n), (∀ i,t (u i).1 ≤ N)→ (∀ i,Nonempty (Gale.Circuit S (u i).1 N n R L a))→ Sail (desk v hv) (fun d:Row v=> Hearth.served N n L (roseK S hv ((ball_subset_ball hl).trans h) d) k u q) (expS A.B.a.S B N)) ∧ ∀ (W:(i:Fin k)→ Circuit S (u i).1 N n R L a)(q:Fin k→ Site (A.B.a.S.side m n))(hQ:∀ i,t (u i).1≤ m), Sail (desk v hv) (fun d:Row v=> fancy L N n m k u W hQ q d.val) (expS A.B.a.S B m):=by
   obtain ⟨m,s,y,hs,h₁,h₂,hP⟩:= Pier.boot S n k ha h R hr hx
   obtain ⟨B,hB,hK⟩:= verdant L k u hx y
   obtain ⟨b,hb⟩:=eventually_atTop.mp hK
   refine ⟨B,s,hs,h₁,hB,eventually_atTop.mpr ⟨max m b,fun i hi N hN=>?_⟩⟩
   have hQ : ball (0:ℂ) s ⊆ Broad A.B.a:= (ball_subset_ball h₁).trans h; obtain ⟨hp₁,hp₂⟩:= max_le_iff.mp hi; constructor
   · intro q hq hp'; let W j:= Classical.choice (hp' j); exact (presto L N n k ha hs h₁ hQ u W (hP N N (hp₁.trans hN) le_rfl) h₂ q).mono ((le_abs_self _).trans (hb _ (hp₂.trans hN)))
   intro W q h'; exact (full L N n i k ha hs h₁ hQ u W h₂ (hP i N hp₁ hN) h' hN q).mono ((le_abs_self _).trans (hb _ hp₂))
end YM.UVExtension.Swell
