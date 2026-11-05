import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Chalet
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Currency
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Roof
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Amend
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Push.CUTOFF_PROJECTORS.Along




set_option warningAsError false

/-! Late stamps can be purchased alongside the rest BEFORE the scheduling
regime is realized. These don't assume a Directed with particular costs.
Care also purchases cover reach margins at this height, before application
on that horizon. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Sale
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented  YM.Next.SectorChange
open Wisps Tier Schur LocalJet Input RG.Supply RG.Shoot Scheduling
open YM.Pressure.Testing
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {T : Protection D}

/-- Carries both presentations of the price if needed. -/
structure Tab where
  r : ℝ
  C : ℝ
  σ : ℝ
  b : ℝ
  η : ℝ
  g : ℝ
  M : ℝ
  d : ℝ
  t : ℝ
  p : ℝ
  q : ℝ
  deriving Inhabited

def truth (c : Tab) := 0 < c.r ∧ 0<c.C ∧ 0<c.σ ∧ 0<c.b ∧ 0<c.η ∧ 0<c.g ∧ 0<c.M ∧ 0<c.d ∧ 0<c.t ∧ 0<c.p ∧ 0<c.q

def Realm (P : Patch) (p : Teller G) (k : ℕ) (b : Tab) (x : ℝ) :=
    Cash G P.L x ∧ Sky G p P x b.C b.r k b.σ b.b b.η b.g ∧ Deck G p P x b.M b.r k b.d b.t b.p b.q ∧
    Terrain.lengthA P x+10 ≤ radiusB x/100 ∧ Terrain.chargeR P x+10 ≤ radiusB x ∧
      Terrain.chargeD P x+10 ≤ 11*radiusB x ∧ Terrain.productR P x ≤ radiusB x

lemma stage (P : Patch) (p : Teller G) (hp : P.Branches p.bind G) (k : ℕ) :
    ∃ b : Tab, truth b ∧ ∀ᶠ x : ℝ in atTop, Realm P p k b x := by
  obtain ⟨r,hr,C,M,σ,d,b,t,η,ε,g,v,hc,hm,hs,hd,hb,ht,hη,hε,hg,hv,h⟩ := coverall P G p hp k
  refine ⟨⟨r,C,σ,b,η,g,M,d,t,ε,v⟩,⟨hr,hc,hs,hb,hη,hg,hm,hd,ht,hε,hv⟩,?_⟩
  filter_upwards [earning G P.L,h,Terrain.reasonably P] with x hx hz hi; exact ⟨hx,hz.1,hz.2,hi⟩

/-- No choice of P passed post-hoc. -/
def Tabled (D : Rolls s) (K : MapPrices) (k j i : ℕ) (b : Tab) (x : ℝ) :=
    ∀ P : Patch, P.L=D.L j → P.J=j → ∀ y:ℝ,x≤y → Realm P (query s K j i) k b y

def Enrolled (W : Delays T) (K : MapPrices) (k : ℕ → ℕ → ℕ) (b : ℕ → ℕ → Tab) :=
    ∀ j i, Adj j i → s.first ≤ i → truth (b j i) ∧ Tabled D K (k j i) j i (b j i) (W.betaEntry j)

lemma next_table (W : Delays T) (K : MapPrices) (k : ℕ → ℕ → ℕ) :
    ∃ X : Delays T, Boost W X ∧ ∃ b, Enrolled X K k b := by
  have he (j i : ℕ) : ∃ x b, Adj j i → s.first ≤ i → truth b ∧ Tabled D K (k j i) j i b x := by
    by_cases he : Adj j i ∧ s.first ≤ i
    swap; · exact ⟨0,default,fun u v => False.elim (he ⟨u,v⟩)⟩
    let P : Patch := ⟨D.L j,j,s.cut.trans (he.2.trans he.1.1),(D.large j).size,(D.large j).odd⟩
    obtain ⟨b,hb,hz⟩ := stage P (query s K j i) (s.has P) (k j i)
    obtain ⟨x,hx⟩ := eventually_atTop.mp hz
    refine ⟨x,b,fun _ _ => ⟨hb,fun Q h h' y hy => ?_⟩⟩
    rw [show Q=P from ?_]; exact hx y hy
    rcases Q with ⟨L,n,a,h1,h2⟩; unfold P
    change L=D.L j at h; change n=j at h'; subst_vars; rfl
  choose x b h using he
  let X : Delays T := { W with betaEntry := fun j => max (W.betaEntry j) (max (x j j) (x j (j-1))) }
  refine ⟨X,⟨fun j => le_max_left ..,le_rfl,le_rfl,le_rfl⟩,b,fun j i ha hb => ⟨(h j i ha hb).1,?_⟩⟩
  intro P hz hp y hy; apply (h j i ha hb).2 _ hz hp y ((le_max_of_le_right ?_).trans hy)
  rcases ha.cases_back with e|e <;> subst i
  · exact le_max_left ..
  exact le_max_right ..



variable {W : Delays T} {Y : Bar W} {I : Wait Y} {P : PostCost D} {Z : ChartRatio G} {K : MapPrices}
    (F : Directed G I Z K P) {k : ℕ → ℕ → ℕ} {b : ℕ → ℕ → Tab}


end YM.AnalyticBridge.Covariance.Sale
