import YM.RemainderComparison.Profile.Sponsor

/-!
 # Numerical program of synchronized analytic probes. No opaque oracle
 to infer estimates on strengthened history. AFTER selecting L and receipts
 but BEFORE specifying common UV lengths; purchases AW clock reading.

 Program supports arbitrary fixed joint order & tolerances and all geometry
 growth used by the projection bounds here. Representation alignment data
 determines GWish BEFORE delay. In particular the cost slots for chart and
 real amplitude AP may use P chosen in the pilot weather and wick length.
 Absorptions here spend exactly this eps once for a pack; summation/ownership
 budgets across their use must allocate an aggregate owner threshold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Profile
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} {L : Side} {K:KernelChoices} {j n r : ℕ}
variable {q o w : ℝ→ℝ}

structure Wish (G : Gauge) (L : Side) where
  r : ℕ
  extraOrder : ℕ -- additional PHY.Pilot order beyond minimal for Weather
  gaussianMoments : ℕ
  halo : ℝ→ℕ
  lobe : ℕ -- assume halo x ≤ lobe*radiusB
  volume : ℝ → ℝ
  haloCap : Reserve G L (fun x=>(halo x:ℝ))
  volumeCap : Lantern.Bolt G L volume
  payload (d:ℝ) (radius cost:ℝ→ℝ) : ℝ→ℝ
  thanks (d) (f w) : 0<d → Reserve G L f→ Reserve G L w → Reserve G L (payload d f w)
  full : ℝ→ℝ
  βCost : ℝ
  full_bound : Rate G L βCost full
  frame : ℝ→ℝ -- additional tolerance at output for spatial/canonical error on pad before taxes
  push : Reserve G L frame
  weight : ℝ -- output support exponent, can request greater than P order for same APS if supplied
  eps : ℝ -- tolerance in g-units
  eps_pos : 0 < eps

namespace Wish
variable (h : Wish G L)
abbrev orders (s : ℕ) := s+(h.r+1)+h.r+2+h.extraOrder
structure Terms where
    wick : ℝ
    radius : ℝ→ℝ -- allow axial R, AMP W=2R
    gap : ℝ
    charge : ℝ→ℝ -- CAP for Pilot chart
    purse : ℝ→ℝ -- CAP for Quote
-- auxiliary per Terms `g^-eps` for monetary slot + pad.Price from any leg
variable (i j :ℕ) (w : ℝ → ℝ)
end Wish

-- T may be rolled from X and actual patch differs but desugared via equality at provider
variable {p : Patch} {Q Q' : RG.Stage} (T : ConnectedActivityE6.Target G P) {u a : ℝ} (S : ConnectedActivityE6.Target.Order G u)

namespace Wish
variable (K : KernelChoices) (p : Patch) (Q Q' : RG.Stage) (a : ℝ)
variable (h : Wish G p.L) (w : Terms)
local notation "J" => Q'.order
local notation "Vn" => h.orders Q'.order
local notation "Θ" => T.table

def gross (h : Wish G p.L) (w : Terms) (Q' : RG.Stage) (x : ℝ) :=
  (w.purse x+w.purse x+h.frame x)*Arc.landed Q'.order Q'.power h.lobe (h.halo x) (w.radius x) h.weight

structure Receives (x:ℝ):Prop where
  one : Real.exp 1 ≤ x
  window : Arc.Stimulus G p.L x (w.radius x) (J) (h.halo x)
  eps_per (β :ℝ) : inBand (betaF G x p.L) β → (gStep β)^(h.r+1) * |w.purse x| ≤ (gStep β)^(((h.r+1:ℕ):ℝ)-h.eps)
  eps_frame (β:ℝ) : inBand (betaF G x p.L) β → (gStep β)^(h.r+1) * |gross (p:=p) h w Q' x| ≤ (gStep β)^(((h.r+1:ℕ):ℝ)-h.eps)
  locator : ∀ (c f:Side)(S':StepData c f)(V:Tube G S')(F:Forest S'.ratio),S'.patch=p→S'.kernel=K→
      Quilt V F (h.volume x) → V.high=Q.clip → V.low=Q'.clip → V.up.Bounds Q.clip Q.width Q.paths (ConnectedActivityE6.loopBill G p.L x) →∀ Λ', V.down.Bounds Q'.clip Q'.width Q'.paths Λ' →
      ∀ r a₀ a' a'' Ω α, Critical F V.high V.up r→ClassicalMatch F V.high V.low V.up V.down r → FiniteBound F V.up V.down V.high V.low α Ω r a₀ a' a'' →
      ∃ ρ:Bid.Dir G c→ AxisChart G F,ClassicalMatch F V.high V.low V.up V.down ρ ∧ Critical F V.high V.up ρ ∧
      ∀ (A B:BudgetPoint)(η β:ℝ), Cash u x a p.L T S η V (Pane.virgin V A β)→ B.threshold=Pressure.temp x→∀ y:Positions (Uniform.Primary c G), ‖y‖≤w.radius x → flags B.threshold (Arc.route G β y)=∅ →∀ k:S'.Choices,
        Weather V F T.table k ρ A β w.wick x w.gap (h.volume x) (2*w.radius x) (w.charge x) K P (h.orders J) y p.L
  offers : ∀ (c f:Side)(S':StepData c f)(V:Tube G S')(F:Forest S'.ratio)(k:S'.Choices)(ρ:Bid.Dir G c→ AxisChart G F)(A:BudgetPoint)(β:ℝ)(θ:Positions (Uniform.Primary c G)), Weather V F T.table k ρ A β w.wick x w.gap (h.volume x) (2*w.radius x) (w.charge x) K P (h.orders J) θ p.L →
    let Y:= Poll.Body (Precision.Key F G); let Z:= Positions (Uniform.Primary c G); let r:= 2*w.radius x; let s:= h.payload w.wick w.radius w.charge x; let D := Sienna.wick G p.L w.wick x; let v:= Access.apron G p.L x; let b:= furl G p.L x
    ∀ (A':Config G f→ℝ) (U:ℝ×Z→Y→ℝ), Playing F ρ β U A' θ D b r v s (h.full x) (h.orders J) h.gaussianMoments→ (∀ y, ‖y‖< r → ∀ z, U (0,y) z=1)→
       Council V F T.table k ρ A β A' U v r D b (w.purse x) θ h.r J (h.orders J) h.gaussianMoments s (h.full x)

lemma ledger (he:0<a):
    ∃ w:Terms, 0<w.wick ∧ Reserve G p.L w.radius ∧ Reserve G p.L w.charge ∧ Reserve G p.L w.purse ∧ ∀ᶠ x in atTop, Receives T S K p Q Q' a h w x := by
  obtain ⟨R,hR,h₁⟩:= Arc.finance G p.L h.halo h.haloCap J
  obtain ⟨E⟩:= Uniform.pre_order G Q.width Q.paths p.J K (n:=Vn+3) (by omega)
  let A:= Classical.choice (Planned.JetPort.purchase Θ T.table_exists ((Vn+3)+1)); let C:=Classical.choice (BareRates.offered G Q'.width Q'.paths (Vn+3))
  let f:= h.volume
  let t x:=pam Vn Θ Q.clip p E (f x) (f x) A (ConnectedActivityE6.loopBill G p.L x)
  let F:= E.tables Q.clip p
  have hv:Reserve G p.L t:= Aux.rents T p E Q.clip f h.volumeCap A -- args
  obtain ⟨d,hd,hD⟩:= observation T S p E Q.clip Q'.clip f A R (h₁.mono fun x hx=>⟨hx.rich,hx.light.2⟩) h.volumeCap hR he C (by unfold orders; omega)
  -- amplitude AP claims only under ready Weather (which implies ghost gap positive)
  have hH:∃ q:ℝ→ℝ, Reserve G p.L q ∧ ∀ᶠ x in atTop,
      let w:Terms:=⟨d,R,F.gap,t,q⟩
      ∀ (c f:Side)(S':StepData c f)(V:Tube G S')(F:Forest S'.ratio)(k:S'.Choices)(ρ:Bid.Dir G c→AxisChart G F)(A:BudgetPoint)(β:ℝ)(θ:Positions (Uniform.Primary c G)), Weather V F T.table k ρ A β w.wick x w.gap (h.volume x) (2*w.radius x) (w.charge x) K P (h.orders J) θ p.L →
    let Y:= Poll.Body (Precision.Key F G); let Z:= Positions (Uniform.Primary c G); let r:=2*w.radius x; let s:=h.payload w.wick w.radius w.charge x; let D:= Sienna.wick G p.L w.wick x; let v:=Access.apron G p.L x; let b:= furl G p.L x
    ∀ (A':Config G f→ℝ) (U:ℝ×Z→Y→ℝ), Playing F ρ β U A' θ D b r v s (h.full x) (h.orders J) h.gaussianMoments→ (∀ y, ‖y‖<r→ ∀ z,U (0,y) z=1) →
        Council V F T.table k ρ A β A' U v r D b (w.purse x) θ h.r J (h.orders J) h.gaussianMoments s (h.full x):= by
    by_cases hp: 0<F.gap
    · obtain ⟨q,hq,hH⟩:= Aux.horizon G p.L K hp hd f t (fun x=>2*R x) (h.payload d R t) h.full h.volumeCap hv (Reserve.mul (Reserve.const _) hR) (h.thanks d R t hd hR hv) h.full_bound (show J+(h.r+1)+h.r+2 ≤ Vn from Nat.le_add_right ..) h.gaussianMoments
      refine ⟨q,hq,hH.mono ?_⟩; intro x hx w c f S' V F' k ρ A β θ hy M N r' s D v b A' U hX hY -- lets
      exact hx _ _ S' V F' T.table k ρ A β _ P hy A' U hX hY -- edit
    exact ⟨_, Reserve.const 1, Eventually.of_forall fun _ c f S' V F' k ρ A β θ hy=> (hp hy.paint.gap).elim⟩
  obtain ⟨q',hq,hQ⟩:= hH
  let w:Terms:=⟨d,R,F.gap,t,q'⟩
  have hZ:Reserve G p.L (gross (p:=p) h w Q'):= ((hq.add hq).add h.push).mul (Arc.landed_every J Q'.power h.lobe h.weight hR h.haloCap)
  refine ⟨w,hd,hR,hv,hq,?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1), h₁,hD,hQ,Access.pay h.eps h.eps_pos hq (h.r+1),Access.pay h.eps h.eps_pos hZ (h.r+1)] with x hx ht h₀ he hK hp
  refine ⟨hx,ht,hK,hp,fun c f S' V F h hh hQ hk hd hr Λ' hl r a b y Ω α hc he hM=> ?_, he⟩
  obtain ⟨ρ,hρ,h'₁,hF⟩:=h₀ c f S' V F h hh hQ hk hd hr Λ' hl r a b y Ω α hc he hM
  exact ⟨ρ,h'₁,hρ.critical,hF⟩
end Wish
end YM.RemainderComparison.Profile
