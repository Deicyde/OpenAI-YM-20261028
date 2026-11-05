import YM.TraceExtension.Terrace.Knell
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source Pressure
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Legato Malachite
open Mallow Lotus Planned.PrimaryIntegral295 PPX
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Bid Labels Extra.Iteration.Scales
open Trace Trace.Terrace
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{K:ℕ→ℝ}{W:Worth}(b:Bandage X K W)(Z:Bolt A)
local notation "T"=> Issue.trail Z
local notation "V"=> A.B.a
local notation "J"=> A.B.a.clock.J
variable {t:ℕ→ℕ}{Xf : ∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail Z) N p}
set_option quotPrecheck false
local notation "C"=> Family.mk (Issue.trail Z) (hol G) (Labels.frames G) (localSection G) t Xf
set_option maxHeartbeats 800000 in
lemma attain (h:Nest X Z)(hG:G.Simple)(hp:Skill b (bear W))(he:Ordeal A.B.a) (H:(C).Makes): Sceptre C W :=by
    refine ⟨fun d m hd hm=>?_,fun d k hk=> (ascend b Z h hp hG he (d:=d) (m:=t d) (H.stages d|>.1) hk)⟩
    let Y:= V; let L:= A.B.a.S.block m; let c:= (Y.budget m).threshold; let f:= (Y.budget (m+1)).threshold; let B:= (Y.params m).columns; let U:= (Y.params (m+1)).columns; have ht:= (Y.params m).columns_ge; have hU : 1≤U:= (Y.params _).columns_ge
    have hK : d+3 ≤ J m:= (H.stages d).1.trans (A.B.a.fits.mono hm); let k:= K (J (m+1)); have hx:1 ≤ k:= (tillP b Z hK).1; let ℓ:ℝ:=L.val; have hl:0<ℓ:= Nat.cast_pos.mpr L.property
    let r:= Doors.rate L; have hr:0 < r:=Doors.rate_pos _; let a:= gear Y m; have ha:0 < a:=gear_pos Y m
    let P:= B*(U*ℓ^d)+k*ℓ^d+r*U; have hz:0<P:=by unfold P B; positivity
    let u:= (a/2)/P; have hu: 0<u:=div_pos (half_pos ha) hz
    filter_upwards [rideE b Z h hG hp hK (bear_pos ..) u hu] with n hw N hN v
    obtain ⟨h₁,h₂,hB,hw⟩ := hw N hN
    let F:= (Labels.frames G).level d; let S:=(C).factory d N n; let V':= S.entries m (S.terminal.symm v); let K':=S.entries (m+1) (S.terminal.symm v); have hH := (H.calibrated d N n (hm.trans hN.le))
    let z:= F.coeffSize (F.core K'.x); let y:= F.coeffSize (F.core V'.x)
    let W':= Warehouse.flight T N m
    obtain hW:=hw V' K' (B*y) (U*z) (hH.format m hm hN.le _) (hH.format (m+1) (hm.trans m.le_succ) hN _) (hH.cap m hm hN.le _) (hH.cap (m+1) (hm.trans m.le_succ) hN _) (hH.unnormalized m hm hN _)
    let V'' := Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos h₁ (Next.Foundations.valuation G d) W' h₂ hB
    let s:=sprite G (A.B.a.clock.hatBeta m) L (bear W (J (m+1)) (J m))
    have hw:y ≤ U*ℓ^d*z:= cleared C H hm hN v (p:=n); have ht':F.coeffSize (vowel F L (F.core K'.x)) ≤ ℓ^d*z:= (Work.G08.size_vowel F L _).2; have hA: V''.leads L K'.x= F.scaled (c/f) (vowel F L K'.x):=by
        change V''.map (vowel F L K'.x)=_
        unfold c f
        exact eve_cols («T»:=localSection G d) (h:=sound G d) W' M.p.kernel.penalty_pos h₂ h₁ (Next.Foundations.valuation G d) hd hG hB (vowel F L K'.x)
    have hz':0 ≤ z:=Work.G08.size_nonneg ..
    have hS:s*(z+U*z) ≤ (a/2)*z:=by
       let w := bear W (J (m+1)) (J m); have he:w≤ 1:=by unfold w bear; have hx:= W.prices (A.B.a.clock.J (m+1)); apply inv_le_one_of_one_le₀; linarith only [hx]
       have hs : s=w/cameo Y (m+1):=by unfold s sprite; unfold L w; rw [Push.PriceCompiler.block_eq A.B.valid m,show cameo Y (m+1)=_ from cameo_next (A:=A) m]
       have hc:= cameo_pos Y (m+1); rw[hs]; have h:0 ≤ z+U*z:=by have :=hU; positivity
       exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right he hc.le) h).trans_eq (by unfold a gear; change _=2*(1+U)/_/_*_; ring)
    refine ⟨hB.backed,?_⟩; change F.coeffSize (V'.x-F.scaled (c/f) (vowel F L K'.x)) ≤ a*z; rw [← hA]
    apply hW.trans; have hh : B*y+(k* F.coeffSize (vowel F L (F.core K'.x))+r*(U*z)) ≤ P*z:= by
       unfold P; linarith only [mul_le_mul_of_nonneg_left hw (zero_le_one.trans ht),mul_le_mul_of_nonneg_left ht' (zero_le_one.trans hx)]
    have hΦ: u*(P*z)=(a/2)*z:=by unfold u; field_simp
    exact (add_le_add hS ((mul_le_mul_of_nonneg_left hh hu.le).trans_eq hΦ)).trans_eq (by change a/2*z+_=a*z; ring)
end YM.PhysicalNext.Repeat.Quince
#print axioms YM.PhysicalNext.Repeat.Quince.attain
