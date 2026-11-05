import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Dart
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Echo


/-!
 # Harvest templates. Abstract for mask syntax; cashier on SAME Data via
 running V histories with Exact Witness on Chartlet posts in Boulevard.
 Using all Placets across both Banks. Price budget in ∑ extracted separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {c f C' F:Side} {j i m n N w r:ℕ} {B : BudgetPoint} {Y:Stars→Side}
-- Coupling classifier template
abbrev Offer (G : Gauge) (n : Side) := Site n→ Config G n→ℝ
variable (f₀:Offer G c) (fa:∀ i:Stars,Offer G (Y i))
def Mirrors {c : Side} (f:Offer G c) := ∀ (x: Site c) (s: Signed) (b:Site c) (V:Config G c), f x (pull s b V)=f (affine s b x) V

def Compatible {c C : Side} (f:Offer G c) (g:Offer G C) (B : BudgetPoint) (r:ℕ):= ∀ x y U V, flags B.threshold U=∅→ flags B.threshold V=∅→ Agrees (Lattice.box r) (expandAt x U) (expandAt y V)→ f x U=g y V
structure CompatibleP (B : BudgetPoint) (r:ℕ) {c : Side} (f₀:Offer G c) {Y:Stars→Side} (fa:∀ i:Stars,Offer G (Y i)) : Prop where
  moves (i:Stars) : Mirrors (fa i)
  pace i j : Trio.Compatible (fa i) (fa j) B r
  forks i : Trio.Compatible (fa i) f₀ B r
  visitL (x) : LocalOn (neighbors r x) (f₀ x)
-- use for rebates
section grain
variable {u : RG.Rep G f} {C : Targets X.p X.K} {Z : Expenses C} {p : Return.Wages} {v : ℕ→ℝ} (R : Register D Z p v) (A : Alloy X D)
variable (H : f.val=c.val*(A.B.a.S.block m).val)
    {t : ℝ} {F:Stars→Side} {V₀ V : ℝ} (hq : ∀ i,(F i).val = (Y i).val*(A.B.a.S.block m).val)
    {M : Chartlet R A N m H u} {U : RG.Rep G f} {M': Chartlet R A N m H U} (ha:Match.Alliance M' M 1 0)
    (a : ∀ i, Chartlet R A N m (hq i) (Pane.virgin (Pane.orchestra A N (hq i)) (A.B.a.budget (m+1)) u.beta))
    (he : u.beta∈ band A.B.a (m+1)) (hu : u.path=A.B.kin.path N (m+1)) (hM:u.p=A.B.a.budget (m+1))
    (ht : Pollened D R A.delay) (hk : v≤ A.delay.betaEntry)
    (hm: m < N) (hT:Tenement R A.delay) (hr : ∀ N m n,m≤N→ Bid.Sworn (A.B.M.H N m) n G)
   (hG : (X.p.profile (A.B.a.clock.J m)).supportExponent+3≤ (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn)
    (hp: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
local notation "B₀" => (A.B.a.budget m)
local notation "x" => (A.B.a.clock.hatBeta m)
local notation "k₀" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "D₀" => Meadow.studio (C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB x)
include hq ha a he hu hM ht hk hm hT hr hG hp
lemma caged (hc : 4*D₀+16≤ c.val) (hC : ∀ i,(4*D₀+16)≤ (Y i).val) (hF : Collection.Local (posting B₀ M') B₀ (plusone M' ha O k₀) V V₀) (hW:U.path=u.path) (hH:M'.supportP=M.supportP) (hY:ha.units=Equiv.refl _): Trio.CompatibleP (B₀) (D₀) (Meadow.barony M O n k₀) (fun i=>Meadow.barony (a i) O n k₀) := by
  refine ⟨fun i s b j V=> (Meadow.rotates ..).symm, fun i j t t' U W h hs hz=> ?_,fun i t t' V U hf hh hg=>?_,fun i=> ?_⟩
  · exact Slide.parses R A (hq j) (hq i) (a j) (a i) rfl rfl rfl rfl he rfl ht hk hm hT hr hG hp (hC j) (hC i) t' t U W hs h hz -- V order
  · exact Slide.parses R A H (hq i) M (a i) hu.symm hM.symm rfl rfl he rfl ht hk hm hT hr hG hp hc (hC i) t' t V U hh hf hg
  exact Meadow.regularY ha n i hF rfl hH hW hY|>.sites
end grain
lemma trimmed {n : Side} {f:Offer G n} (h: Mirrors f): Mirrors fun i=>stillA (f i):= by
  intro x s b V
  have hk : pull s b (1:Config G n)=1:=by funext i; simp [Lattice.pull,Lattice.Step.read]
  exact congr_arg₂ (·-·) (h x s b V) ((congr_arg (f x) hk.symm).trans (h x s b 1))
lemma tinted (h : Trio.CompatibleP B r f₀ fa) : Trio.CompatibleP B r (fun i=> Boulevard.stillA (f₀ i)) (fun i j=> Boulevard.stillA (fa i j)):= by
  have ht {c:Side}:flags B.threshold (1:Config G c)=∅:= smoky (P:=B) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using B.threshold_pos)
  refine ⟨fun i=> trimmed (h.moves i), fun i j k l U V hg he ht'=> congr_arg₂ (·-·) (h.pace i j k l U V hg he ht') (h.pace i j k l 1 1 ht ht (fun _ _ _=>rfl)),fun i j k u v hu hv he=>?_ ,fun x U V hu=> congr_arg₂ (·-·) (h.visitL x U V hu) rfl⟩
  exact congr_arg₂ (·-·) (h.forks i j k u v hu hv he) (h.forks i j k 1 1 ht ht (fun _ _ _=>rfl))
end YM.PhysicalNext.Repeat.Trio
