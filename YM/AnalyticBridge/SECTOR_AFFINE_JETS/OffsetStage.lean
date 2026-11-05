import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Center
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Directed


/-!
# Use the authorization-specific covariance & mean estimates together

Useful also to purchase even when order or χ may vary through levels.
Take `Cosmos` or derive one downstream of `Ringing`. Consume the gauges
at the realized data using exactly the same covariance and shift as
in `Client.use`; e.g. can use V extension IN the intact integrand since
in other cases these terms will vanish by actual flags. No estimate or
expansion of marked Hessians, of b chains or normalized remainders here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Client.WorkOrder
open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure YM.Push.SectorMeasure.Presented
open YM.FreeResolvent.TestD Matrix MeasureTheory
open YM.Bid YM.Next YM.Input RG.Supply RG.Shoot Scheduling
open YM.Pressure.Testing
open Offset
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {Z : ChartRatio G} (K : MapPrices) {s : Sheet G} (D : Rolls s) {Θ : Protection D}

def Office (j i n : ℕ) (q : Chi) (a x : ℝ) :=
    ∃ r d d' v η l C M : ℝ, 0<r ∧ 0<d ∧ 0<d' ∧ 0<v ∧ 0<η ∧ 0<l ∧ 0<C ∧ 0<M ∧
    ∀ y : ℝ, x≤y → 0<temp y ∧ temp y ≤ 1 ∧ temp y≤ 2*fiery G y (D.L j) ∧
    120 ≤ radiusB y ∧ ∀ (c f : Side) (S : StepData c f), S.patch.J = j → S.patch.L=D.L j →
      100*(1+radiusB y) ≤ c.val → ∀ T : Tube G S, (query s K j i).Funds S T →
    ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), V∈eligible A G y →
    ∀ k : S.Choices,
      (∀ z : PriceCoords G _, ‖z‖≤r → Estimate n d v η l M A F T y V k z) ∧
      Offset.Shift n y d' v (a*fiery G y S.patch.L) C T F A V k q

private lemma buy {j i n : ℕ} {a : ℝ} (q : Chi) (ha : 0<a) (H : 4 ≤ j) : ∃ x, Office K D j i n q a x := by
  let P := query s K j i
  let S : Patch := ⟨D.L j,j,H,(D.large j).size,(D.large j).odd⟩
  obtain ⟨r,d,d',v,M,N,η,l,hr,hd,hd',hv,hM,hN,hη,hl,h⟩ := Offset.prices G S P a ha q n (s.has S)
  obtain ⟨x,hx⟩ := eventually_atTop.mp (h.and (monitors G (D.L j)))
  refine ⟨x,r,d',d,v,η,l,M,N,hr,hd',hd,hv,hη,hl,hM,hN,fun y hy => ?_⟩
  obtain ⟨⟨hh,he⟩,hw,ha,hb⟩ := hx y hy
  refine ⟨hw,ha,hb,hh,fun c f T h ht hg U hu F A V hA k => ?_⟩
  refine he T U ?_ hg hu A F V hA k
  rcases e : T.patch with ⟨L,J,H,h₁,h₂⟩; rw [e] at h ht
  change L = D.L j at ht; change J = j at h; subst_vars; rfl

variable {D}

def Ready (W : Delays Θ) (a : ℕ→ℕ→ℝ) (n : ℕ→ℕ→ℕ) (q : ℕ→ℕ→Chi) :=
  ∀ j i, Adj j i → s.first ≤ i → Office K D j i (n j i) (q j i) (a j i) (W.betaEntry j)

variable {K} {W : Delays Θ} {w a E : ℕ → ℕ → ℝ} {n : ℕ → ℕ → ℕ} {q : ℕ → ℕ → Chi}



/-- Can always buy after Cosmos (same a), and buy Cosmos after
Ringing using `issue_cosmos`. -/
theorem ready (n : ℕ → ℕ → ℕ) (q : ℕ → ℕ → Chi) (h : Cosmos Z K W w a E) :
    ∃ W' : Delays Θ, Boost W W' ∧ Cosmos Z K W' w a E ∧ Ready K W' a n q ∧
      (Ringing K w W → Ringing K w W') := by
  have he j i : ∃ x : ℝ, Adj j i → s.first ≤ i → Office K D j i (n j i) (q j i) (a j i) x := by
    by_cases hh : Adj j i ∧ s.first ≤ i
    · obtain ⟨x,hx⟩ := buy K D (j:=j) (i:=i) (n:=n j i) (q j i) (h j i hh.1 hh.2).door (s.cut.trans (hh.2.trans hh.1.1))
      exact ⟨x,fun _ _ => hx⟩
    exact ⟨0,fun u v => False.elim (hh ⟨u,v⟩)⟩
  choose x hx using he
  let W' : Delays Θ := { W with betaEntry := fun i => max (W.betaEntry i) (max (x i i) (x i (i-1))) }
  have hb : Boost W W' := ⟨fun i => le_max_left ..,le_rfl,le_rfl,le_rfl⟩
  refine ⟨W',hb,cosmos_holds hb h,?_,fun h => Bid.recheck hb.beta h⟩
  intro j i he hf
  obtain ⟨r,d,d',v,η,l,C,M,hr,hd,h,hv,hη,hl,hC,hM,H⟩ := hx j i he hf
  have hB : x j i ≤ W'.betaEntry j := by
    rcases he.cases_back with e|e <;> subst i
    · exact (le_max_left ..).trans (le_max_right ..)
    exact (le_max_right ..).trans (le_max_right ..)
  exact ⟨r,d,d',v,η,l,C,M,hr,hd,h,hv,hη,hl,hC,hM,fun y hy => H y (hB.trans hy)⟩

variable {Y : Bar W} {I : Wait Y} {P : PostCost D}
    (F : Directed G I Z K P)




end YM.AnalyticBridge.SectorAffine.Client.WorkOrder
