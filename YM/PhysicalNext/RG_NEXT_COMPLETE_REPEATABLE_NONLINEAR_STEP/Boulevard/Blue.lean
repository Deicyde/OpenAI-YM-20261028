import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Dawn
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir
/-!
 # PURE logical posts Loft to E comparison. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Boulevard
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane
open Push.PriceCompiler ThroughLaunch Height Opera
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {c f : Side} {i j m n N:ℕ}
variable {C : Targets X.p X.K} {Z : Expenses C} {p : Return.Wages} {v : ℕ→ℝ} (R : Register D Z p v) (A : Alloy X D)
local notation "a" => A.B.a
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "x" => A.B.a.clock.hatBeta m
variable (H : f.val=c.val*(A.B.a.S.block m).val) {u : RG.Rep G f}
local notation "T" => Pane.orchestra A N H
local notation "U" => (X.p.profile I)
local notation "B" => (A.B.a.budget m)
local notation "e" => (Z J I)
local notation "P'" => (C J I)
local notation "β" => (A.B.a.budget (m+1))
abbrev Chartlet (N m:ℕ) (H : f.val=c.val*(A.B.a.S.block m).val) (u : RG.Rep G f) :=
    let i:= A.B.a.clock.J m; let j:=A.B.a.clock.J (m+1)
    Cash (p j i) (A.B.a.clock.hatBeta m) (R.μ j i) (D.L j) (C j i) (R.o j i) (R.c j i) (Pane.orchestra A N H) u
abbrev SeekR (N m:ℕ) (H : f.val=c.val*(A.B.a.S.block m).val) {u : RG.Rep G f} (Y:Chartlet R A N m H u) :=
    let k:= Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
    Cash.Renewed k.degrees k.earn k.one k.two Y
section appointment
variable {a₀ b₀ : ℝ} {v' : RG.Rep G f} {Y : Chartlet R A N m H u} {Y': Chartlet R A N m H v'} (X' : Match.Alliance Y' Y 1 0)
    (ht : Pollened D R A.delay) (hm: m < N) (hT:Tenement R A.delay) (hr : ∀ N m n,m≤N→ Bid.Sworn (A.B.M.H N m) n G)
   (hG : (X.p.profile (A.B.a.clock.J m)).supportExponent+3≤ (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn)
    (hp: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
local notation "γ" => (A.B.kin.alpha N m)
local notation "o" => plusone Y' X' Chi.canonical γ
local notation "s" => (gold G L x)
include ht hm hT hr hG hp Y X'
lemma lays (he: SeekR R A N m H Y) (F:Forest (panel A m H).ratio) :
    Collection.Local (posting B Y') B (o) (turnFee B*(betaF G x L ^ (Z J I).wanting + betaF G x L ^ (-(7/16):ℝ))) (Cash.armK (P') L (R.μ J I) x 0 (e).degrees) ∧
     ∀ V,(panel A m H).push u.beta u.eval V=earlyValue (posting B Y') (T).down (T).low B (o) u.beta (weighty Y Chi.canonical F) γ V:= by
  let k:=step_paid a m; let v:=A.B.valid.pays m
  have hH:= hT J x v I k; obtain ⟨C,d,r,g,b,t,z,Y'',q,l,i,⟨N',hv⟩,hK,hp'⟩:= hH.2 _ _ _ T Y.laws.data.funds (Pane.ovation A N H hm hr) u Y
  have hσ := params_eq A.B.valid m; have hS:(B).supportExponent=(U).supportExponent:= congr_arg RG.Stage.supportExponent hσ; have ho:(B).order=(U).order:= congr_arg RG.Stage.order hσ; have hV:(B).power=(U).power:= congr_arg RG.Stage.power hσ
  have h₀ := suns R A ht hm H Y; have hf:(T).down.Bounds (T).low ((a).params m).width ((a).params m).paths ((a).clock.loopCap m):= A.B.support.cap _ _ hm.le -- notation a??
  have hh : preExponent B ≤ (Z J I).earn:= by unfold preExponent; rw [hS]; exact hG
  have hl:= (A.B.a.params m).width_pos
  have hx:= Song.loaded B Y' X' Chi.canonical γ N' rfl ho.le rfl hf he hh hK hV.le hp (h₀.1.trans (show _/4≤(A.B.a.params m).width/2 by linarith))
  obtain ⟨c,hc,hV⟩:=hx.cheap
  exact ⟨{ hx with cheap:= ⟨c,hc,fun i=> budget_loosen (hV i) (mul_le_mul_of_nonneg_left (add_le_add hp' h₀.2.1) (turnFee_pos _|>.le))⟩},fun V=> (Song.forward (B) Y' X' Chi.canonical γ N' F rfl ho.le hf he V).symm⟩
variable (h : Rich R b₀ A.delay)
include h
lemma vested (hX : X'.units=Equiv.refl _) (hz : ∀ i k, u.activities.E i k=0) (ha:u.path=v'.path) (hα:v'.activities.reg=u.activities.reg) (hk:v'.activities.forced=u.activities.forced):
    Meadow.Budget B (Beam.marquee Y' B).reg (choir (Meadow.tower X' (χ:=Chi.canonical) γ) ∘pennant Y') (turnFee B*(s+s)):= by
  let k:=step_paid a m; let v:=A.B.valid.pays m
  have hH:= hT J x v I k; obtain ⟨C,d,r,g,b,t,z,Y'',q,l,i,⟨N',hv⟩,hK,hp'⟩:= hH.2 _ _ _ T Y.laws.data.funds (Pane.ovation A N H hm hr) u Y
  obtain ⟨hH',hh,hY,hK'⟩:=h.large J I k x v; obtain ⟨hv',ht',he'⟩:= hK' Y'' l i hK N'.balance hp'
  have hσ:= params_eq A.B.valid m; have hS:(B).supportExponent=(U).supportExponent:= congr_arg RG.Stage.supportExponent hσ; have ho:(B).order=(U).order:= congr_arg RG.Stage.order hσ; have hV:(B).power=(U).power:= congr_arg RG.Stage.power hσ
  have h' : preExponent B ≤ (Z J I).earn:= by unfold preExponent; rw [hS]; exact hG
  obtain ⟨-,_,hQ,_⟩:= ht J x v I k; have hω:=hQ Y'' l i hK N'.balance hp'
  have hψ:= Meadow.vintageB X' hX ha hα hk (B) rfl rfl N' ho.le hV.le h' (fun i=> budget_loosen ((Height.completed N' hH' hv _ hv' hh hH.1 hY ht') i) hω)
  have h₀:= suns R A ht hm H Y
  exact Meadow.soared B _ (Meadow.tone X' B rfl s s γ (A.B.support.cap N _ hm.le) hp h₀.1 h₀.2.2 (Meadow.emptyFree _ _ hψ _ (Meadow.suppressed X' hX ha hα hk γ hz)))
end appointment
end YM.PhysicalNext.Repeat.Boulevard
