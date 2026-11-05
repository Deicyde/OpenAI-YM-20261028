import YM.UVExtension.Pier.Heath
import YM.UVExtension.Pier.Tan
/-! # Full scalar coefficient insertion for crude bounds. ANY translated layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Local Planned.GuardedAtom Guard
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} (S: Uses R hG)
    (N n m k:ℕ) {a z p:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a) (hm:m≤N)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "Y"=> Row a
local notation "V0"=> fun (b:Row a) => S.realBeat b.val N n m
local notation "P"=> A.B.a.budget m
local notation "T₀"=> A.B.a.S
local notation "Z"=> ball (0:ℂ) a
local notation "n₀"=> A.B.a.S.side m n
local notation "W"=> A.B.a.clock.forcedAllowance m
variable {o:Side}
-- algebraic at representatives
lemma servedP (R:Rep G o) (i:ℕ)(F:Config G o→ℂ): Hearth.tasting R F=hit R (.logKey i) F:=by
    rw [hitStrip]; unfold tasting; congr! 1; congr! 1; ext x; unfold faded stripped; change ( ((_*R.eval _ :ℝ):ℂ)* _)=_*_; rw [Complex.ofReal_mul]; rfl
lemma packed {p:BudgetPoint}(L:Rep G o) (F:Config G o→ℂ)(q:ℕ→ Config G o→ℂ){a b c u d:ℝ}(hA:L.Lawful a b c u d)(ht:L.p=p)(hh:Dominated q)(he:∀ i,Held p (.gasKey i) (q i))(hk:∀ U, HasSum (fun i=>gasMark p L.activities U i q) (F U*(L.activities.gas p U:ℂ))): ∑' i, hit L (.gasKey i) (q i)=Hearth.tasting L F:=by
    rw [(stored Wing.gasKey L hA q hh (fun i=>(he i).mesh)).tsum_eq, servedP L 0]; unfold hit; congr! 1; ext x; rw [carded L hA q hh]; unfold salaryP; rw [ht,(hk x).tsum_eq]; change _=( (Real.exp _ * L.activities.gas L.p _:ℝ):ℂ)*_; rw [ht,Complex.ofReal_mul]; ring
lemma combine (R:Rep G o){α C Λ δ v:ℝ}(hr:R.Lawful α C Λ δ v){f g:Config G o→ℂ}(h:Envelope f)(hp:Envelope g): Hearth.tasting R (f+g)=Hearth.tasting R f + Hearth.tasting R g:=by
   simp only [servedP R 0]; unfold hit; rw [mul_add]; exact sums R ((portEnv _ R hr|>.mulC h).integrableC _) ((portEnv _ R hr|>.mulC hp).integrableC _)

variable {v':ℝ}
include ha hm hp
lemma juggle (X:Support (A.B.a.S.side m n))(ho:(0:Site (A.B.a.S.side m n)) ∈ X) (F: Config G (A.B.a.S.side m n)→ℂ) (hf: Attaches ((A.B.a.budget m).threshold) X F)(hv:∀ U,‖F U‖≤v')(h:Harbour (desk a ha) k P (fun b:Row a=> S.realBeat b.val N n m) z)(h₁:0 ≤ z): Sail T (fun b:Y=> Hearth.tasting (V0 b) F) (z*(Copse.worth k (P).B (P).supportExponent X*v'*(Real.exp ((X.card:ℝ)*W) - 1))):= by
    let P':=P; let Y₁:= S.realBeat 0 N n m; let G':= Y₁.activities; have hs:HasSlots P' G':=poss S N n m (rose0 S) hm
    let t:=(Keeper.sufficient hs).supply (fun _:Unit=>X)
    let V (b:Y):= (V0 b).activities; have he b: (V b).forced=G'.forced:= (poss S N n m (roseK S ha hp b) hm|>.forced).trans hs.forced.symm  -- might burn!
    have hl(b):=(liveR S N n m (roseK S ha hp b) hm)
    have hp₁:= Gale.strongK S N n ha hp m hm
    obtain ⟨y,hY,hP⟩:= crate T P k X G' t F hf ho hv V he (fun i=> hl i|>.labels) hp₁
    let V₀:=V0; let g:= Wing.gasKey; let f(b:Y):= ∑' i, hit (V₀ b) (g i) (y b i); let c:=Copse.worth k P'.B P'.supportExponent X*v'*(Real.exp ((X.card:ℝ)*W)-1)
    have ht: Stalk (nose (G:=G) (land G n₀ P ∘ g) k P'.B P'.supportExponent) T y c:= hY
    have hu i:=accounted T k y g ht i; have hA(i:Y)(j):Held P' (.gasKey j) (y i j):= by
        obtain ⟨w,-,hw⟩:=hu i; exact heldK (V₀ i) P' rfl (poss S N n m (roseK S ha hp i) hm) _ ((hP i).1) j (w j) (hw j)
    have hc:0≤c:=mul_nonneg (mul_nonneg (Real.exp_pos _|>.le) ((norm_nonneg _).trans (hv 1))) (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (fundedP m A.B.a|>.2.le))))
    have hx:Sail T f (z*c):=traders T V0 (fun i=> hl i) k y g h h₁ ht hc (fun i=> Pier.gas (P) i) hA
    refine (show f= _ from funext fun b=> packed _ _ _ (hl b) rfl (hu b) (hA b) (hP b).2) ▸ hx

lemma insertP (X:Support (A.B.a.S.side m n))(ho:(0:Site (A.B.a.S.side m n)) ∈ X) (F: Config G (A.B.a.S.side m n)→ℂ) (hf: LocalOn X F) (hg: GaugeInvariant F)(he: Measurable F) (hv:∀ U,‖F U‖≤v')(h:Harbour (desk a ha) k P (fun b:Row a=> S.realBeat b.val N n m) z)(h₁:0 ≤ z) : Sail T (fun b:Y=> Hearth.tasting (V0 b) F) (z*(Copse.worth k (P).B (P).supportExponent X*v'*Real.exp ((X.card:ℝ)*W))):=by
   let A':=P; let v:= (A').threshold; let t:= A.B.a.clock.forcedAllowance m; let e:= masked v X F; let b:= F-e;
   have hv₀: 0 ≤ v':= (norm_nonneg _).trans (hv 1); have he₀ U: ‖e U‖ ≤ v'∧ ‖b U‖ ≤ v':=by
       by_cases hx: Healthy v X U
       · rw [show b U=F U-e U from rfl, show e U=F U from masked_eq _ _ _ _ hx,sub_self,norm_zero]; exact ⟨hv U,hv₀⟩
       rw [show b U=F U-e U from rfl, show e U=0 from masked_ne _ _ _ _ hx,sub_zero,norm_zero]; exact ⟨hv₀,hv U⟩ -- align
   have hE: Envelope e:=⟨masked_measurable _ _ F he,v',fun i=> he₀ i|>.1⟩; have hB:Envelope b:= ⟨he.sub hE.meas, v',fun i=> he₀ i|>.2⟩
   have hh: Attaches v X b:= by
       refine ⟨fun U V ht hx=> congr_arg₂ (·-·) (hf U V ht) (Local.uses_mask v hf U V ht hx),fun t i=> congr_arg₂ (·-·) (hg t i) (Local.invariant_mask hg v X t i),hB.meas,fun U hx=>?_⟩; exact by change F _-_=0; rw [show e U= F U from masked_eq _ _ _ _ hx,sub_self]
   have hp' := juggle S N n m k ha hp hm X ho b hh (fun i=> he₀ i|>.2) h h₁; let k':= Blush.found 0 X ho; let j:= Wing.logKey k'
   let M:PoleC (G:=G) A' j:= ⟨e, heldE X ho (S.realBeat 0 N n m) P rfl (poss S N n m (rose0 S) hm) F hf hg he v' (fun i=>he₀ i|>.1)⟩
   let q:= Copse.worth k A'.B A'.supportExponent X; let f(d:Y):= V0 d; have hx: Sail T (fun d=> Hearth.tasting (f d) e) (z*(q*v')):=by
       simp_rw [servedP _ k']; let p:=h j (Pier.letter (P) X ho) M; have hm' : land G n₀ A' j=X:= stamp X ho (Q:=S.realBeat 0 N n m) (B:=A') rfl (poss S N n m (rose0 S) hm); rw [hm'] at p; rw [←mul_assoc]; exact p.mono (mul_le_mul_of_nonneg_left ((charged A' j M).2 (fun i=>he₀ i|>.1)) (mul_nonneg h₁ (Real.exp_pos _|>.le)))
   have hL: (fun d:Y=>Hearth.tasting (V0 d) F) = fun d=> Hearth.tasting (f d) e+Hearth.tasting (V0 d) b:=funext fun d=> by
       refine (congr_arg (Hearth.tasting (V0 d)) (show F=e+b by unfold b; abel)).trans (combine (f d) (liveR S N n m (roseK S ha hp d) hm) hE hB)
   rw [hL]; refine (hx.plus hp').mono (le_of_eq ?_); change z*(q*v')+z*(q*v'*(_ - 1))=_; unfold q; ring
end YM.UVExtension.Pier
