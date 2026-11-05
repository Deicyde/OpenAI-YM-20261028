import YM.RemainderComparison.Lobby.Staging

/-!
# Price raw tails after selection. Still see old support. No pointwise alpha
 cancellations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lobby
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open Progress.DirectedRecipe
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {ι β I J J':Type} {α:Type*} {c f:Side} [DecidableEq β] {Jm:Marker.Census β} {Y: Stars→Side}
variable (O:Manor G c ι α I) (T:Manor G c ι α J) (P:BudgetPoint) (root:ι→ Support c) (A : Set I) (Z:Set ι)
variable (W : Flues.Yard ι α G c) (p:ℕ) (a:α)(z:ι→Marker.Poly Jm)
open Mosaic Serif Manor Flues
local notation "Dʼ" => mural O T A
variable {r w k d m:ℕ} {v v' σ η γ D₁ D₂ u u' e e' L K' p' q b:ℝ} {ϕ : β→ℝ}
local notation "Pʼ" => (A⊕J)
set_option quotPrecheck false
variable {root}
variable (s:Finset (A⊕J)){Ω:Set (A⊕J)} (X:Quarry (mural O T A) Ω J' root r)
local notation "Sʼ" => walls Dʼ X
local notation "Sˮ" => ((((s : Finset (A ⊕ J)):Set (A⊕J))∪walls Dʼ X):Set (A⊕J))
variable {K : Set ((↥A)⊕J)}

structure Absorbs (R:Set I)(F:Set J):Prop where
    winds : ∀ j:A,j.val∈R→ Sum.inl j∈ K
    reads : ∀ i∈F,Sum.inr i∈ K

def night (Z : Set ι): Set I:= {i|Mosaic.Verse.load Z (O.marks i)=0}
lemma preservation {R:Set I}{F:Set J} (hp:Absorbs A (K:=K) R F) (hv: Spinal O (A\R) root P σ v) (ht: Spinal T (Fᶜ) root P σ v') :
    Manor.Spinal Dʼ (Kᶜ) root P σ (v+v'):=by
   let V:Set A:= {i|i.val ∈ A\R}
   have hz := Lobby.sumPays (Lobby.peel O A) (signed T) P V Fᶜ (Lobby.spinalize T P Fᶜ ht) (Lobby.peeled O P A hv (fun i hi=>hi))
   apply hz.skim ?_ le_rfl le_rfl; intro i hi; rcases i with i|i
   · exact (show i.val∈A\R from ⟨i.prop,fun h=>hi (hp.winds i h)⟩)
   exact (show i∈Fᶜ from fun h=>hi (hp.reads i h))
lemma sanctified {R:Set I}{F:Set J} (hp: Absorbs A (K:=K) R F) (hv: Templary O ((A∩night O Z)\R) root P σ v) (ht: Templary T (Fᶜ ∩ night T Z) root P σ v') :
    Manor.Templary Dʼ ((Kᶜ)∩ night Dʼ Z) root P σ (v+v') :=by
   let V:Set A:= {i|i.val ∈ (A∩ night O Z) \ R}
   let t':=Fᶜ∩ night T Z; have hz:= Lobby.sumAnch (Lobby.peel O A) (signed T) P V t' (Lobby.templarySign T P t' ht) (Lobby.templaryPeel O P A hv (fun i hi=>hi))
   apply hz.skim ?_ le_rfl le_rfl
   rintro (i|i) ⟨hi,h⟩
   · exact (show i∈V from ⟨⟨i.prop,h⟩,fun h=>hi (hp.winds i h)⟩)
   exact (show i∈ t' from ⟨fun h=>hi (hp.reads i h),h⟩)

-- Skyline (∀ cofinite request is reached by financed structural comps). Any ε. Both/single charged smaller.
lemma pair_air (V V₀ V' V'':Set I) (hf:V⊆V') (hu:V₀⊆V) (hp:Spinal O V' root P σ v) (hh:Spinal O (V\ V'') root P σ u)
    (hv: Templary O (V₀\ V'') root P σ u')(hx : 0 < b) :
       ∀ᶠ s : Finset I in atTop, ∀ t:Set I, (↑s ∩ V'') ⊆ t→ Manor.Spinal O (V\ t) root P σ (u+b) ∧ Manor.Templary O (V₀\ t) root P σ (u'+b) :=by
    filter_upwards [Breeze.Cut.rest P hp b hx] with s hs t ht
    constructor
    · apply (hh.swell hs).skim ?_ le_rfl le_rfl; rintro i ⟨hi,h⟩; by_cases h': i∈ V''
      · exact Or.inr ⟨hf hi,fun he=>h (ht ⟨he,h'⟩)⟩
      exact Or.inl ⟨hi,h'⟩
    apply (hv.swell hs.templary).skim ?_ le_rfl le_rfl; rintro i ⟨hi,h⟩; by_cases h': i∈ V''
    · exact Or.inr ⟨hf (hu hi),fun he=>h (ht ⟨he,h'⟩)⟩
    exact Or.inl ⟨hi,h'⟩
end YM.RemainderComparison.Lobby
