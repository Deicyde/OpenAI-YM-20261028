import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Breath
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Iron

/-!
# Background vertices of the first integration activity

Select each at most once. Remember L and fine flag footprints even where
seed/cuff/E choices may suppress a test. Chart protector multiplied into
h not the starting factor. Relative probability under same actual Tag
reference; never decide a branch on V instead of U. Fixed B halo for
rarity argument even larger than physically minimal. Cohabitation of many
calls needed in purchasing these (see next).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Jewels
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

/-- Patch all reads with the actual fixed record (fields may leave
all other constraints). PrCore uses broad not these ψ; this is for optional
hard, short residual F. -/
def robe (Y : Mint T F A x) (I : Finset (Bond f)) (a : ArrayR G f) :=
    ∏ i ∈ I∩activeB A F (radiusB x), ψ x S.patch Y.q (lie a i)

lemma robe_le (Y : Mint T F A x) (I : Finset (Bond f)) (a : ArrayR G f) : |robe Y I a| ≤ 1 := by
  unfold robe; rw [abs_prod]; apply prod_le_one
  · exact fun _ _ => abs_nonneg _
  intro i _; unfold ψ Chi.innerShare; rw [abs_of_nonneg (Y.q.range _).1]; exact (Y.q.range _).2

-- track where reading physical values; projection tags H. `BG` members:
-- fine-profile, coarse-noise profile, frame tag, bond tag, q, gamma.
abbrev Bg (_S : StepData c f) := Cell f ⊕ Bond c ⊕ Site c ⊕ Bond c ⊕ Site f ⊕ Bond f

def seat (S : StepData c f) : Bg S → Site c :=
    Sum.elim (S.ratio.parent ∘ Prod.fst) (Sum.elim Prod.fst
      (Sum.elim id (Sum.elim Prod.fst (Sum.elim S.ratio.parent (home S)))))

def keptBack (F : Forest S.ratio) (A : Stores S) (B : ℕ) : Bg S → Prop
  | .inl p => p∉padF A (300*B)
  | .inr (.inl b) => b∉padI A (300*B)
  | .inr (.inr (.inl x)) => x∉A.dome (300*B)
  | .inr (.inr (.inr (.inl b))) => b∉padI A (300*B)
  | .inr (.inr (.inr (.inr (.inl i)))) => i∉scenes A (300*B)
  | .inr (.inr (.inr (.inr (.inr e)))) => e∈activeB A F B ∧ e∉ padB A (304*B)

def gammaOnly (S : StepData c f) : Bg S → Bool
  | .inr (.inr (.inr (.inr (.inr _)))) => true
  | _ => false

def tooth (Y : Mint T F A x) (R : Activities G f) (L : Finset ℕ) (W : ℝ) (a : ArrayR G f) : Bg S → ℝ
  | .inl p => fine A Y.q x (Y.build a) p
  | .inr (.inl b) => wireMask A Y.q W x (Y.build a) Y.k Y.V b
  | .inr (.inr (.inl i)) => αSite (Y.build a) i Y.k
  | .inr (.inr (.inr (.inl b))) => αBond (Y.build a) b Y.k
  | .inr (.inr (.inr (.inr (.inl i)))) => edgeBan R L (Y.build a) (fiery G x S.patch.L) i
  | .inr (.inr (.inr (.inr (.inr i)))) => broad x S.patch Y.q (lie a i)

def chip (Y : Mint T F A x) (R : Activities G f) (L : Finset ℕ) (W : ℝ) (a : ArrayR G f) (i : Bg S) :=
    if keptBack F A (radiusB x) i then
      (if gammaOnly S i then 1 else robe Y (pulls S (2*radiusB x) (seat S i)) a)*(tooth Y R L W a i-1) else 0





-- post-L universal bound
def attrition (D : Patch) : ℝ := 2+Fintype.card D.FrameTag+Fintype.card D.Points

lemma attrition_nn (D : Patch) : 0 ≤ attrition D := by unfold attrition; positivity


end YM.AnalyticNext.ConnectedActivity.Jewels
