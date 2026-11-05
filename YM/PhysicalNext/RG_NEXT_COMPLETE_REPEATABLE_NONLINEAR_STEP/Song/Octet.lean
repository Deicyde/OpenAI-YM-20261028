import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armada
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Match
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Litho

/-!
# Regular repertoire along a career. Same Addressing.
 Tilt from old support H over all seats: no V/π-dependent/evaluating-payment
 choices for the labels. Incoming labels permutation π only used to PROVE same
 masked total. Downstream Price hit on actual support & the forecast α.
 Collection includes path piece billing unapologetically, therefore its Local
 budget is NOT yet the one required. Includes receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Song
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Geo
open ConnectedActivityE6.Blaze Blaze.March Captain
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n : ℕ} {F : Tree.Forest S.ratio}
variable (p : BudgetPoint) (H : Cash W s μ L Q o α T I) {J : Cash W s μ L Q o α T R}
variable (X : Match.Alliance H J 1 0) (χ : Chi)

abbrev perf (p : H.fragrances) := unionOf H.smallAt p.2
lemma crest (p : H.fragrances) : (perf H p).Nonempty := Finset.Nonempty.mono (subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ none)) (p.2 none).2.1
def locate (p : H.fragrances) : RegularAddress c := ⟨Classical.choose (crest H p),perf H p,Classical.choose_spec (crest H p)⟩
def sequence (p : H.fragrances) : Config G c→ℝ := (-1:ℝ) • (fun V=>stream J χ V (X.furrow p))

abbrev Magazine := H.fragrances ⊕ Songbook c
def scaleT : Magazine H → RegularAddress c := Sum.elim (locate H) (strings T.down p)
def opus (γ : ℝ) : Magazine H → Config G c→ℝ := Sum.elim (sequence H X χ) (sounding T.down T.low R.beta γ)

variable (N : Captain J j C' d v Y A b r B q k χ) (hp : p.threshold=Pressure.temp s) (hP : p.order ≤ j)
    (hB : p.B=radiusB s)

lemma reconnects (t : H.fragrances) : perf H t=perf J (X.furrow t) := by
  symm; have hh: J.bookFoot (.inr (X.furrow t))=(H.bookFoot (.inr t)).image (Lattice.affine 1 0) := X.alcove (.inr t)
  rw [show Lattice.affine 1 (0:Site c)=id from funext fun u=> by simp [Lattice.affine],image_id] at hh; exact hh

include hp hP N
lemma valueDue (z : H.fragrances) (V : Config G c) : masked p.threshold (locate H z).support (sequence H X χ z) V= -J.trainedPool χ V (X.furrow z) := by
  have hx : J.trainedPool χ V (X.furrow z)=masked p.threshold (perf J (X.furrow z)) (fun w=> stream J χ w (X.furrow z)) V := congr_fun (N.gloryBudget (X.furrow z) p hp hP).1 V
  let g(w):=stream J χ w (X.furrow z)
  rw [hx,← reconnects H X z]; change masked _ (perf H z) _ V=_; rw [show masked p.threshold _ (sequence H X χ z) V=_ from mask_mul (perf H z) _ (-1) V g, neg_one_mul]
lemma pocketScore (n : ℕ) (hn : p.power ≤ n) (z : H.fragrances) : p.Regular (locate H z).support (sequence H X χ z) ∧
    p.supBounds (locate H z).site (locate H z).support (sequence H X χ z) (N.markΦ (X.furrow z) n) := by
  have hr : (locate H z).support=perf J (X.furrow z) := reconnects H X _
  have hk := N.gloryBudget (X.furrow z) p hp hP
  rw [hr]; refine ⟨CouplingShape.reg_scale _ hk.2.1,?_⟩
  have hh := CouplingShape.sup_scale (-1) (hk.2.2 n hn (locate H z).site (show _ ∈perf J (X.furrow z) from hr ▸ (locate H z).anchor))
  rw [abs_neg,abs_one,one_mul] at hh; exact hh
include hB
lemma postage (hn : p.power ≤ n) (a : ℝ) (ha : preExponent p ≤ a) (hX : Armada Q L μ a s i B j k) : Quotes.early p (locate H) (fun z=> N.markΦ (X.furrow z) n)
    (collars G i s j n*(salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  have hv := hX.applies N n 0; simp only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] at hv
  intro y
  refine budget_mono (budget_pull X.furrow X.furrow.injective (hv y)) ?_ ?_
  · intro z; split
    · exact mul_nonneg (pocketScore p H X χ N hp hP n hn z).2.1 (Real.exp_pos _).le
    exact le_rfl
  intro z; dsimp only; split
  next hz => rw [if_pos (show y∈ reachability (X.furrow z) from show y ∈ perf J (X.furrow z) from reconnects H X z ▸ (show y ∈ perf H z from hz ▸ (locate H z).anchor)), show (locate H z).support= _ from reconnects H X z,hB]
             exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (pocketScore p H X χ N hp hP n hn z).2.1
  exact (budget_pull X.furrow X.furrow.injective (hv y)).1 _
omit hB
lemma summon (u : Cash.Renewed n a δ e J) (V : Config G c) : HasSum (fun i=> masked p.threshold (locate H i).support (sequence H X χ i) V) (-(Real.log (J.homesteadPool χ V))) := by
  have hh := price_log J.seam _ J.hardH J.smallAt (radiusB s) J.testS (add_nonneg u.full u.post.le) (J.first_logsPool χ V u)
  have hv := hh.2.1.2.1.of_norm
  simp_rw [valueDue p H X χ N hp hP, (J.threshold_logPool χ V u).1]; apply HasSum.neg
  exact X.furrow.hasSum_iff.mpr hv.hasSum
lemma language (γ : ℝ) (u : Cash.Renewed n a δ e J) {σ C Λ : ℝ} (hx : T.down.Bounds T.low σ C Λ) (V : Config G c) : HasSum (fun i=> masked p.threshold (scaleT p H i).support (opus H X χ γ i) V)
    (-(Real.log (J.homesteadPool χ V)) + (-(γ*Collection.receipt T.down T.low p V+(R.beta*(billOf p T.down.cubic V+billOf p T.down.quartic V)+billOf p T.down.loop V)))) :=
  HasSum.sum (summon p H X χ N hp hP u V) (literalScore T.down T.low p V R.beta γ hx)

include hB
lemma books (γ : ℝ) (ha : Quotes.preExponent p ≤ a) (hX : Armada Q L μ a s i B j k) (hn : p.power≤ n)
    (hd : WilsonStartup.Decent T.low p) {σ C Λ : ℝ} (ht : T.down.Bounds T.low σ C Λ) (hw : preExponent p / p.B ≤ σ/2) :
      ∃ u, Quotes.early p (scaleT p H) u ((collars G i s j n*(salary Q L μ B s j k*(1-1/2)⁻¹))+
        octaveNeed G p T.low σ C Λ R.beta γ) ∧ ∀ l, p.Regular (scaleT p H l).support (opus H X χ γ l) ∧
          p.supBounds (scaleT p H l).site (scaleT p H l).support (opus H X χ γ l) (u l) := by
  obtain ⟨f,h,hF⟩ := stanzaReady (n:=c) T.down T.low p R.beta γ ht hd hw
  exact ⟨Sum.elim (fun z=> N.markΦ (X.furrow z) n) f,fun y=> Cost.sum (postage p H X χ N hp hP hB hn a ha hX y) (h y),fun i => by
    rcases i with i|i
    · exact pocketScore p H X χ N hp hP n hn i
    exact hF i⟩
end YM.PhysicalNext.Repeat.Song
