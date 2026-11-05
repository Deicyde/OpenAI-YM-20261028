import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Directions
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Licensed
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff

/-!
# Downstream at an actual Directed step

Pre-requisites bought as extra **post-L** prices. Can boost `Delays`,
preserving existing Ringing and Cosmos costs. Need actually run the later
schedule after this gate (no retroactive coverage of arbitrary runs). When
specializing get the *same* heights, V contour, fields, covariance and
integral as in `committed`. Consumer demonstrates using also in V jets at
these same prices and sectors. Don't infer a normalized physical multiplier
with Haar Jacobian or advance a program from this. No price of the affine
mean is needed/claimed by these calls.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Client

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure YM.Push.SectorMeasure.Presented
open YM.FreeResolvent.TestD Matrix MeasureTheory
open YM.Bid YM.Next YM.Input RG.Supply RG.Shoot Scheduling
open YM.Pressure.Testing
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {Z : ChartRatio G} (K : MapPrices) {s : Sheet G} (D : Rolls s)
variable {Θ : Protection D}

/-- Keep all post-L estimates under the committed trajectory's V hat height.
Need no failure checks or re-issuance of K at a realized period. -/
def EnvelopeBill (j i : ℕ) (n : ℕ) (x : ℝ) :=
    ∃ r d v η l M : ℝ, 0<r ∧ 0<d ∧ 0<v ∧ 0<η ∧ 0<l ∧ 0<M ∧
    ∀ y : ℝ, x≤y → 0<temp y ∧ temp y ≤ 1 ∧ temp y≤ 2*fiery G y (D.L j) ∧
    120 ≤ radiusB y ∧
    ∀ (c f : Side) (S : StepData c f), S.patch.J = j → S.patch.L=D.L j →
      100*(1+radiusB y) ≤ c.val → ∀ T : Tube G S, (query s K j i).Funds S T →
        ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), V∈eligible A G y →
          ∀ (k : S.Choices) (b : PriceCoords G c), ‖b‖≤r → Estimate n d v η l M A F T y V k b

lemma buying {j i : ℕ} (n : ℕ) (H : 4≤j) : ∃ x : ℝ, EnvelopeBill K D j i n x := by
  let P : Teller G := query s K j i
  let S : Patch := ⟨D.L j,j,H,(D.large j).size,(D.large j).odd⟩
  obtain ⟨r,d,v,η,l,M,hr,hd,hv,hη,hl,hM,h⟩ := estimates G S P (s.has S) n
  obtain ⟨x,hx⟩ := eventually_atTop.mp (h.and (monitors G (D.L j)))
  refine ⟨x,r,d,v,η,l,M,hr,hd,hv,hη,hl,hM,?_⟩
  intro y hy
  obtain ⟨⟨hh,he⟩,hw,h₁,h₂⟩ := hx y hy
  refine ⟨hw,h₁,h₂,hh,fun c f T h ht hg U hu F A V ha k b hb => ?_⟩
  refine he T U ?_ hg hu A F V ha k b hb
  rcases e : T.patch with ⟨L,J,H,h₃,h₄⟩; rw [e] at h ht
  change L = D.L j at ht; change J = j at h; subst_vars; rfl

variable {D}

/-- One height for every used transition. -/
def Issued (W : Delays Θ) (n : ℕ → ℕ → ℕ) :=
  ∀ j i, Adj j i → s.first ≤ i → EnvelopeBill K D j i (n j i) (W.betaEntry j)

lemma issue (W : Delays Θ) (n : ℕ → ℕ → ℕ) : ∃ W' : Delays Θ, Boost W W' ∧ Issued K W' n := by
  have H (j i : ℕ) : ∃ x : ℝ, Adj j i → s.first ≤ i → EnvelopeBill K D j i (n j i) x := by
    by_cases hb : Adj j i ∧ s.first ≤ i
    · obtain ⟨x,hx⟩ := buying K D (i:=i) (n j i) (s.cut.trans (hb.2.trans hb.1.1))
      exact ⟨x,fun _ _ => hx⟩
    exact ⟨0,fun u v => False.elim (hb ⟨u,v⟩)⟩
  choose x hx using H
  let Y : Delays Θ := { W with betaEntry := fun j => max (W.betaEntry j) (max (x j j) (x j (j-1))) }
  refine ⟨Y,⟨fun j => le_max_left ..,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro j i he hf
  obtain ⟨r,d,v,η,l,M,hr,hd,hv,hη,hl,hM,h⟩ := hx j i he hf
  have H : x j i ≤ Y.betaEntry j := by
    rcases he.cases_back with e|e <;> subst i
    · exact (le_max_left ..).trans (le_max_right ..)
    exact (le_max_right ..).trans (le_max_right ..)
  exact ⟨r,d,v,η,l,M,hr,hd,hv,hη,hl,hM,fun y hy => h y (H.trans hy)⟩

variable {K}

lemma cosmos_holds {W V : Delays Θ} (h : Boost W V) {w a E : ℕ → ℕ → ℝ} (hx : Cosmos Z K W w a E) :
    Cosmos Z K V w a E := by
  intro j i ha hf
  obtain ⟨h₁,h₂,H⟩ := hx j i ha hf
  exact ⟨h₁,h₂,fun y hy => H y ((h.beta j).trans hy)⟩



variable {W : Delays Θ} {Y : Bar W} {I : Wait Y} {P : PostCost D}
variable (F : Directed G I Z K P) {n : ℕ → ℕ → ℕ} {g a E : ℕ → ℕ → ℝ}


end YM.AnalyticBridge.SectorAffine.Client
