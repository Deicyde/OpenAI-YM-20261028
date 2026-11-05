import YM.RemainderComparison.Seedlings.Kernel
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seedlings
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics Funk Cargo Slide
variable {G : Gauge} {c f C F L:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable (Q: KernelChoices)(P:Patch){S : StepData c f} {S': StepData C F}
variable {T : Tube G S} {T':Tube G S'} {p :ℝ} {R:RG.Rep G f} {R': RG.Rep G F}
variable {N:Site C}{n:ℕ} {a W v β : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (H: Cash W p a L J o v T R)
variable (χ:Chi){ι δ:Type}{α:Type*}(X:ι→Portrait R α) (y:α)(I:BoxOf H) (b:Finset ι)
variable {Y:Stars→Side}(r n:ℕ)
variable (l:ι→ℝ)(Z:Set ι)(b₁:ℝ)
namespace BoxOf
-- interfaces for RG03. Payment at every auxiliary.C but no orbit cost included.
-- define Warm assm universal again no loop.Price beyond.B.
variable (V:∀ i:Stars,Pier (Y i) G W p a L J o v β χ α)(M:∀ i:Stars,BoxOf (V i).reader)
local notation "F₁"=> BoxOf.flagsCollected X y H (∅:Finset ι) I r n χ l Z b₁
def flash (u:α)(i:Stars) := BoxOf.flagsCollected (V i).pose (V i).starts (V i).reader ∅ (M i) r n χ (V i).pay Set.univ 0 u
-- require pure registrations Light.Meta. Cast shape uses y global. Equal Cong via nond
-- need χ argument binder
structure Valley : Prop where
    uniform i : (V i).starts=y
    stamp i : SliceRows.Stamp (V i).dataP
    real : SliceRows.Stamp T
    rotating (i:Stars) (x:Site (Y i))(sd:Signed)(j:Site (Y i)) : ∃ w:(V i).rep.activities.Moves sd ((V i).stepP.ratio.embed j), Shifting (V i).pose (V i).starts (V i).reader (∅:Finset (V i).τ) (M i) x r n (V i).pose ∅ (M i) w (Equiv.refl _)
    market (x:Site c)(i:Stars)(x':Site (Y i)) : ShapeP P Q H (V i).reader X (V i).pose y I (M i) ∅ ∅ x' r n l (V i).pay Z Set.univ b₁ 0 x 1
    exchange i j x x' : ShapeP P Q (V i).reader (V j).reader (V i).pose (V j).pose y (M i) (M j) ∅ ∅ x' r n (V i).pay (V j).pay Set.univ Set.univ 0 0 x 1

variable (P':BudgetPoint)(h : BoxOf.Valley Q P H χ X y I r n l Z b₁ V M)
variable (hh : Enlightened Q P K J o p a L χ) (hB: Bloom H χ)(hH:∀ i,Bloom (V i).reader χ)(hp:P'.threshold=Pressure.temp p)
variable (u:α)
include h hh hB hH hp
lemma beams : WickReps.Sensible P' r (F₁ u) (BoxOf.flash χ r n V M u):=by
    refine ⟨fun i sd b x U he=>?_,fun i j x y' U U' he he' hX=>?_,fun i x x' U U' he he' hX=>?_,fun x=>?_⟩
    · obtain ⟨w,hz⟩:=h.rotating i x sd b; rw [hp] at he; simpa only [BoxOf.flash,one_mul] using (BoxOf.season _ _ _ _ _ _ _ _ _ _ sd b w _ _ hz _ _ _ _ u (V i).pay Set.univ 0 _ (d:=1) he (by rw [one_mul]) (hH i)).2 -- edits
    · have h₁ : Agrees (Lattice.box r) (expandAt y' U') (expandAt x U):=fun i h ht=>(hX i h ht).symm
      have hz:= fuel P Q _ _ χ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P' (h.exchange i j x y') hh (h.stamp j) (h.stamp i) hp U' U he' he h₁ u
      simp_rw [one_mul] at hz; unfold flash; rw [h.uniform i,h.uniform j]; exact hz.2
    · have hz:= (fuel P Q _ _ χ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P' (h.market x' i x) hh (h.stamp i) h.real hp _ _ he he' hX u).2
      simp_rw [one_mul] at hz; unfold BoxOf.flash; rw [h.uniform i]; exact hz.symm
    · rw [BoxOf.bound]; exact BoxOf.applause _ _ _ _ _ _ _ _ _ _ _ _ _ hB
-- counterparts on ANY mark
variable {δ' : Side} (U:Pier C G W p a L J o v β χ α)(F':BoxOf U.reader)(x:Site c)(d:ℝ)
structure Launch : Prop where
   start : U.starts=y
   stamp : SliceRows.Stamp U.dataP
   real : SliceRows.Stamp T
   body : ShapeP P Q H U.reader X U.pose y I F' b U.goal.val (WickReps.home C r) r n l U.pay Z Set.univ b₁ 0 x d
variable (hv:BoxOf.Launch Q P H χ X y I b r n l Z b₁ U F' x d)
omit h hH
include hv
lemma starlight : WickReps.Matches (pool X y H b I x r n χ l Z b₁ u) (pool U.pose U.starts U.reader U.goal.val F' (WickReps.home C r) r n χ U.pay Set.univ 0 u) P' r x d:=by
   refine ⟨BoxOf.polar X y H b I x r n χ l Z b₁ u hB,fun V V' h h' he=>?_⟩
   have hX: Agrees (Lattice.box r) (expandAt (WickReps.home C r) V') (expandAt x V):=fun i hi a=> (he i hi a).symm
   rw [hv.start]; exact (fuel P Q _ _ χ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P' hv.body hh hv.stamp hv.real hp _ _ h' h hX u).1
end BoxOf
end YM.RemainderComparison.Seedlings
