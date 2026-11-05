import YM.RemainderComparison.Orbits.Ever
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Nursery
open Funk
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι δ : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Aux Mosaic Verse Muse Apo Marker Push.Uniform Lapis Sienna Fare Boulevard Herbal WickReps Lyric Typeface
open Trio Next.Rank.Glyph Next.Rank.Exponential
variable (Q:ConnectedActivityE6.Target G P) (Ω:KernelChoices)
open Lobby Portal
open Pier Slide
variable {β:ℝ}{χ:Chi}{ιa ιb δa δb:Type}(P': BudgetPoint)
open WickReps Manor Flues Serif
open Seedlings BoxOf
variable (H:Cash W x μ L Q o C T R)(M:ι→Portrait R α)(y:α)(l:ι→ℝ)(Z:Set ι)(v:ℝ) (D:BoxOf H)
variable {r' k:ℕ}(o':ι→Site c)(Wc:Breeze.Careers ι δ c o' r' k)(wP:ι→ℝ)
local notation "Mʼ"=> Creek.theater H χ M y l Z v
local notation "Aʼ"=> Creek.Academy H χ M y l Z v k
local notation "Fʼ"=> Sleet.Staff (Typeface.brand M y) H
local notation "Sx"=> Wc.pocket
local notation "St"=> Wc.o'
open Creek
/- Input analytic exposures, already after coefficient render
 on this SAME STEP. These are input promises; no estimate on unknown e
 inside a germ. e kernels use Halo.Presents in the original trajectory.
 log length t≥ ℓ strong moments.Winding.Core.Age.S.Check.
 Forced paint consumes budgets from same assembled K, no length exponent used in their analysis.
-/
variable (E:Set ℕ)(ℓ:ℕ→ℕ)
open Sleet
variable {χ₀ γ b V B' :ℝ}
variable (χ₀ :ℝ)
def oldest (U:Set ℕ) (x:ℝ): Set ℕ:= {i| i ∉ U ∧ Pressure.Stores.till x ≤ ℓ i}
structure Kraft (Y:ℕ)(τ v:ℝ) : Prop where
    far : ∀ i∉E, Sleet.cloudy R Y i → Pressure.Stores.till x≤ ℓ i
    earns : ∃ f:ℕ→ℝ, (∀ i,0≤ f i) ∧ (∀ i,i∉ E→ R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (f i)) ∧
         Footprint.Anchored (fun i => (R.activities.reg i).site) (fun i=> f i*Real.exp (τ*ℓ i)) (Raw.regularExtra R) R.p.supportExponent v
variable {n:ℕ}(h: Kraft (R:=R) (x:=x) E ℓ n χ₀ V)
-- implicit arguments order
include h
lemma slate : ridge R n E⊆ oldest ℓ E x:=fun i hi=> ⟨hi.1,h.far i hi.1 hi.2⟩
lemma cakes (hp:0≤χ₀) : ∃ w:ℕ→ℝ,Halo.Presents R (oldest ℓ E x) w (Sleet.pigment χ₀ x * V):=by
     obtain ⟨f,h,hF,hC⟩:= h.earns; let g i:= f i * Real.exp (χ₀*ℓ i); let P:= pigment χ₀ x; have he:0≤P:= Real.exp_nonneg _
     let w i:= if i∈oldest ℓ E x then P*g i else 0
     refine ⟨w,fun i hi=>?_,fun i hi=> if_neg hi,fun x=>?_⟩
     · apply Manor.Stem (hF i hi.1)
       rw [show w i=P*g i from if_pos hi]; unfold g; rw [mul_left_comm]; exact le_mul_of_one_le_right (h i) (Breeze.cooled hp hi.2)
     refine budget_mono (budget_scale he (hC x)) (fun i=> ?_) (fun i=>?_)
     · split; next=> apply mul_nonneg _ (Real.exp_nonneg _); unfold w; split; exact mul_nonneg he (mul_nonneg (h i) (Real.exp_nonneg _)); exact le_rfl
       next=>exact le_rfl
     split; next=> unfold w; split; exact le_of_eq (mul_assoc ..); exact (mul_nonneg he (mul_nonneg (mul_nonneg (h i) (Real.exp_nonneg _)) (Real.exp_nonneg _))) |>.trans_eq' (zero_mul _).symm
     next=> rw [mul_zero]
omit h
-- paint: rapid on log only. Symbol.Nature.Preserve Books
variable (μv:ι→ℕ) (Y:ℕ)
def deepest (x:ℝ): Set ι:= {i| ∃ j:ℕ,(M i).wing=Wing.logKey j ∧ Pressure.Stores.till x ≤ μv i}
structure Charters (Y k:ℕ)(τ V b:ℝ) : Prop where
   signs i : 0 ≤ l i
   budget : 0 ≤ b
   gas i j : (M i).wing=Wing.gasKey j → μv i=0
   log i j : (M i).wing=Wing.logKey j→ Sleet.cloudy R Y j→ Pressure.Stores.till x ≤ μv i
   grants : ∃ (U:Type) (_:Fintype U) (D:U→ Site f) (Ψ:ι→Finset U), (∀ i, 0< Palette.wages (brand M y) l i → ∃ j∈ Ψ i,D j∈ (brand M y i).crest) ∧ Extra.Multi.Occupancy (S.ratio.parent ∘ D) k∧ Extra.Multi.Rooted Ψ (fun i=>(brand M y i).crest) R.p.B V (fun i=>Palette.wages (brand M y) l i * Real.exp (τ*μv i)) b
variable (Hu: Charters (x:=x) (S:=S) M y l μv n k χ₀ V b)
include Hu
lemma pipes (i:ι)(j:ℕ)(he:(M i).wing=Wing.logKey j) (ht:Sleet.cloudy R n j): i∈ deepest M μv x:=⟨j,he,Hu.log _ _ he ht⟩
lemma past (hp:0≤χ₀) : ∃ (U:Type) (_:Fintype U) (D:U→ Site f)(Ψ:ι→ Finset U), Lyric.Scale D Ψ (Typeface.brand M y) (Creek.rage (deepest M μv x) (Sleet.pigment χ₀ x) l) k V b S ∧ Lyric.Scale D Ψ (Typeface.brand M y) l k V b S:=by
    let u := deepest M μv x; let δ:= pigment χ₀ x; let c := Verse.marked u δ⁻¹; let g:= Typeface.brand M y; let L':=Creek.rage u δ l; let w:= Palette.wages g l; have hd: 0<δ:= Real.exp_pos _
    have hc i : 0<c i := by unfold c Verse.marked; split; positivity; norm_num
    have hP i : Palette.wages g L' i=c i * w i:= by unfold Palette.wages w; apply mul_assoc
    have hx i : c i ≤ Real.exp (χ₀*μv i):=by
        unfold c Verse.marked; split; next H=> obtain ⟨j,-,hP⟩:=H; exact (inv_le_iff_one_le_mul₀ hd).2 (by rw [mul_comm]; exact Breeze.cooled hp hP)
        next=> exact Real.one_le_exp (mul_nonneg hp (Nat.cast_nonneg _))
    have hw i : 0≤ w i:= mul_nonneg (Hu.signs _) ((g _).profit)
    obtain ⟨U,hU,D,I,hD,hh,hY⟩:= Hu.grants
    have ht i : Palette.wages g L' i≤w i*Real.exp (χ₀*μv i):= by rw [hP,mul_comm]; exact mul_le_mul_of_nonneg_left (hx i) (hw i)
    refine ⟨U,hU,D,I,⟨fun i=> mul_nonneg (hc i).le (Hu.signs i),fun i hi=> hD i ?_,fun i=>?_,Hu.budget,hh⟩,⟨Hu.signs,hD,fun i=>?_,Hu.budget,hh⟩⟩
    · exact pos_of_mul_pos_right ((hP i) ▸ hi) (hc i).le -- verify direction
    · apply budget_mono (hY i) (fun i=>?_) (fun j=>?_); · split; exact mul_nonneg (Real.exp_nonneg _) ((hP i).symm ▸ mul_nonneg (hc i).le (hw i)); exact le_rfl
      split; exact mul_le_mul_of_nonneg_left (ht j) (Real.exp_nonneg _); exact le_rfl
    refine budget_mono (hY i) (fun j=>?_) (fun j=>?_); · split; exact mul_nonneg (Real.exp_nonneg _) (hw _); exact le_rfl
    split; next=> exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (hw j) (Real.one_le_exp (mul_nonneg hp (Nat.cast_nonneg _)))) (Real.exp_nonneg _)
    next=> exact le_rfl
end YM.RemainderComparison.Nursery
