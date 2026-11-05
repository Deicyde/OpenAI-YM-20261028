import YM.RemainderComparison.Portal.Count
import YM.RemainderComparison.Arc.Witness
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Portal
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x





open Marker Next.Rank.Glyph Next.Rank.Exponential Sleet
local notation "Yv" => veil ι
local notation "cardboard" => Stock.census ι
/-!
 # Short-field receipts at the auxiliary port

 Accepts LocalCoefficientIdentification as JMatch (only coefficients at b=0,
 *normalized* unmarked scalar convention at this exact same torus).
 If using an exponentially close packet rendering from the unwrapping step,
 KEEP that tail contract. Doesn't hypothesize the actual Taylor error,
 in particular `Script` contains no reference to actual projection or
 poly-input (beyond the implicit common basis conventions/coupling).
 Needs AP budgets and Weather wired in. Epochs must pay THIS portal.
 Per ordinary jet convention this includes all assignment overlaps, FOREST
 law and same tags before output quotient. If using other diagram algebra,
 must prove identification with these explicit coefficients.
-/
open Aux Fare Lapis Sienna Boulevard Exchange Push.Uniform Lantern
variable (V:BudgetPoint)(E:modes ι→ Config G f →ℝ)
variable (k':S.Choices) (ρ: Bid.Dir G c→ AxisChart G F) (B':BudgetPoint)
local notation "Vc" => Positions (Uniform.Primary c G)
local notation "Σ₀" => Poll.Body (Precision.Key F G)
local notation "g'" => gStep R.beta
local notation "E₀" => E (quiet ι)
local notation "Σu" => (Arc.route (c:=c) G R.beta)
variable (U:modes ι→ (ℝ×Positions (Uniform.Primary c G))→ Poll.Body (Precision.Key F G) →ℝ)
local notation "W'" => U (quiet ι)
variable {j' n' r' l' K:ℕ} {B₀ f₀ c₀ R₀ D v' u' ε e' x' C₁ C₂:ℝ} {K₁ : KernelChoices}

/-- operations in Sg space. Keep `Ω` and Θ.W.V semantics separate -/
def ideal (b:BudgetPoint)(X:Config G c →ℝ)(i:modes ι) (y:Config G c) := X y-if i=quiet ι then baser T R b y else 0
def chronos (c:ℝ)(i:modes ι):= if i=quiet ι then c else 0

def orchestra (p:ℕ)(x:ℝ×Positions (Uniform.Primary c G)) : Cabinet ι := fun i=> merchant T F Q.table k' ρ (U (quiet ι)) p (U i) x

def offer (p:ℕ)(i:modes ι) (x:ℝ× Positions (Uniform.Primary c G)) :ℝ:=
   if i=quiet ι then Aux.trial T F Q.table k' ρ W' p x else sWard (orchestra (Q:=Q) (T:=T) k' ρ U p x) i


-- RG02 full formal reference & render, budget not in physical terms.
-- c₀ common across V (may choose HUGE scalar to align). Pert germ includes ALL
-- step evaluation (Actual overhead uses the FULL kinetic BASE at R.beta). Nonlinear stencil
-- completions contribute here; Statement draws ℝ values around b≠0 too
-- from the actual V chart. Doesn't require analytic P curvature beyond specified generation.
structure Script (V:BudgetPoint)(R:Rep G f)(T:Tube G S) (Ψ: Config G c→ℝ) (Ϝ:ℝ × Positions (Uniform.Primary c G)→ℝ)(c₀:ℝ)(i:modes ι)
        (p: Positions (Uniform.Primary c G)) (n:ℕ) (v u C:ℝ):Prop where
   account (y) : y∈Germ.patch (Positions (Uniform.Primary c G)) v u→ Brush n C 1 Ϝ y
   chart : ∀ᶠ y:Positions (Uniform.Primary c G) in 𝓝 p,
       ideal (T:=T) (R:=R) V Ψ i (Arc.route G R.beta y) + chronos c₀ i= Ϝ (gStep R.beta,y)

-- approximation receipt for periodized corrections/order truncation, BEFORE
-- powering/truncating. Don't use arbitrary estimate on full-width at b=g.
structure JMatch {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (f g : ℝ×E→ℝ) (p:E) (k j:ℕ) (q:ℝ):Prop where
    matchCoeffs (i:ℕ) : i≤k → Brush j q 1 (fun x=> Trace.coefficient f i x- Trace.coefficient g i x) p
namespace JMatch
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f g:ℝ×E→ℝ} {z:E}
lemma warms (h:JMatch f g z k j q)(b:ℝ)(hb:0≤b)(hp:b≤1) :
     Brush j (((k:ℝ)+1)*q) 1 (fun x=> Trace.trunc k f (b,x)- Trace.trunc k g (b,x)) z:= by
   unfold Trace.trunc Trace.polyeval
   simp_rw [← Finset.sum_sub_distrib,← smul_sub]; have he:= (Brush.spree (Finset.range (k+1)) (fun i y=>b^i • (Trace.coefficient f i y-Trace.coefficient g i y)) (fun _=>q) zero_le_one fun i hi=> by
     let H:=h.matchCoeffs i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)); apply (H.smul _).climb _ le_rfl
     rw [Real.norm_of_nonneg (by positivity : 0 ≤ b^i)]; exact mul_le_of_le_one_left H.nonneg (pow_le_one₀ hb hp))
   simpa only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using! he
end JMatch

section estimates
variable {v₀ y₀ z₀:ℝ}
variable (pP : Positions (Uniform.Primary c G))
variable (hC: Council T F Q.table k' ρ B' R.beta (E (quiet ι)) (U (quiet ι)) v' u' D v₀ C₁ pP r' V.order n' l' B₀ f₀)
-- all finite Marker algebra up to cap. No #port in final error.
include hC
def entrant (x : Positions (Uniform.Primary c G)) : Cabinet ι:= fun i=> divideAux T B' R.beta (E (quiet ι)) (E i) x

def exact_l (i:modes ι) (x:Positions (Uniform.Primary c G)) :=
    if i=quiet ι then reserve_l T F Q.table k' ρ B' R.beta E₀ x else sWard (entrant (T:=T) (R:=R) E B' x) i

variable (hK:Fintype.card ι ≤ K)(hβ:gStep R.beta≤1)
include hC hK hβ
lemma Quanta (hp : ∀ i,Playing F ρ R.beta (U i) (E i) pP D v₀ u' v' B₀ f₀ n' l') (i:modes ι) : Queue (offer (Q:=Q) (T:=T) k' ρ U r' i) (exact_l (Q:=Q) (R:=R) (T:=T) E k' ρ B' i)
       g' pP v' u' V.order r' (C₁+ rehearsal V.order r' K C₁):=by
   let f := orchestra (Q:=Q) (T:=T) k' ρ U r'; let e₀:=entrant (T:=T) (R:=R) E B'
   have hv : May f e₀ g' pP v' u' V.order r' C₁:= fun i=> hC.nearby ℝ _ _ (hp i)
   have ht:= played hv hβ hK i
   unfold offer exact_l; split
   · exact hC.balance.grows (le_add_of_nonneg_right ht.cost)
   exact ht.grows (le_add_of_nonneg_left hC.plain.cost)
end estimates
end YM.RemainderComparison.Portal
