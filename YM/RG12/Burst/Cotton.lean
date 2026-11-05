import YM.RG12.Burst.Wardrobe
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.RG12
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}
open Daisy.Charity.RG12
-- Accounting manual for later Conv.Wait customers. Consumes sticker proofs.
variable (Δ:Decal G)
def First (s:Sheet G)(K:MapPrices)(X:Targets s K)(p:Expenses X)(M:ℕ→ℕ):Prop:= ∀ j i,StepStages j i →∀ L:Side,M j ≤ L.val→∀ W μ o, (p j i).wanting ≤ -(7/16:ℝ)→ 0 < W → 0 < μ→∀ᶠ z in atTop, Δ.rub (query s K j i) (X j i) (p j i) L W μ o (s.profile i) j z
lemma lint (X:Targets s K)(p:Expenses X):∃ M,First Δ s K X p M:=by
  choose n hn using (fun j i=> Δ.good _ (X j i) (p j i))
  exact ⟨fromMax n,fun j i hj L h W μ o=>hn j i L ((le_fromMax n hj).trans h) W μ o _ j⟩
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
def Earned (R:Register D p u l)(Z:Delays Θ):Prop:=∀ j x,Z.betaEntry j ≤ x →∀ i, StepStages j i → Δ.rub (query s K j i) (X j i) (p j i) (D.L j) (u j i) (R.μ j i) (R.o j i) (s.profile i) j x
lemma board (R:Register D p u l) {k:ℕ→ℕ}(h:First Δ s K X p k)(he : ∀ j,k j ≤ (D.L j).val)(hf:∀ j i,StepStages j i → (p j i).wanting≤-(7/16:ℝ))(V : Delays Θ) : ∃ W : Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ, DelayLe W Y → Earned Δ R Y:=by
  obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi=> h j i hi (D.L j) (he j) (u j i) (R.μ j i) (R.o j i) (hf j i hi) (R.consumes j i hi).1 (R.consumes j i hi).2.1))
  refine ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩, fun Y hy j z hx i hi=>?_⟩; exact H j z ((hy.beta j).trans hx) i hi
end YM.PhysicalNext.Repeat.Mallow.RG12
