import YM.Further.STRONG_STARTUP_CREDIT.Launch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Oculus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Dome
import YM.Planned.RECIPE_STARTUP_PORT.Horizon


/-! # Pinned posting for actual E inheritance. Reset after this Choice's
 calculations not during Local supply. Pins only site: cover/exponent and
 repertoire retained. Compatible pruning of births in ANY Packet world.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Beam
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    (H : Cash W s μ L Q o α T I) (p : BudgetPoint) {J : Cash W s μ L Q o α T R} (χ : Chi)
    (X : Alliance H J 1 0)

lemma icon_inj : Injective (icon H) := by
  intro i j h
  injection h with h h
  have hh:= congr_fun h none; have hv:= congr_arg Subtype.val hh
  change { Opacity.key S i}=({Opacity.key S j}: Molecule S) at hv; simpa [Opacity.key] using hv

def dashboard (z:H.fragrances) := Function.extend (icon H) (plate H) (locate H) z
lemma impact (i : ℕ) : dashboard H (icon H i)=plate H i := (icon_inj H).extend_apply _ _ i
lemma see (z) : (dashboard H z).support=perf H z := by
  by_cases he : z∈ Set.range (icon H)
  · obtain ⟨i,rfl⟩:= he; rw [impact]; exact (sites_icon H i).symm
  exact congr_arg RegularAddress.support (extend_apply' _ _ _ he)

def contents : Magazine H → RegularAddress c := Sum.elim (dashboard H) (strings T.down p)
lemma patch (i : Magazine H) : (contents H p i).support=(scaleT p H i).support := by
  cases i with
  | inl i=> exact see H _
  | inr i=> exact rfl

def marquee : Listing G c := {Song.posting p H with reg := Song.revolve (contents H p) ∘ Song.pennant H}
lemma rewrite_rule (i : ℕ) : ((marquee H p).reg i).support=((posting p H).reg i).support := by
  let q:=pennant H i
  change q.1.spread (contents H p q.2).support=q.1.spread (scaleT p H q.2).support; rw [patch H p]

-- okay even for off curve input fields. Portal movement checked separately
lemma travels (W : Collection.Source G c) (z α d : ℝ) (V : Config G c) :
    earlyValue (marquee H p) T.down T.low p W z α d V=earlyValue (posting p H) T.down T.low p W z α d V := by
  let f i:=((marquee H p).read W).regularOccurrence p i V
  have he : ∀ i, f i=((posting p H).read W).regularOccurrence p i V := fun i=> by
    change masked _ ((marquee H p).reg i).support _ _=masked _ _ _ _; rw [rewrite_rule]; rfl
  suffices hh : ((marquee H p).read W).additive p V=((posting p H).read W).additive p V by
    unfold earlyValue Rep.eval Rep.exponent; simp only [Collection.frozen]; rw [hh]; rfl
  exact congr_arg tsum (funext he) -- edit

lemma moves (s : Signed) (t : Site c) (f : Magazine H→ Config G c→ℝ) :
    let a:= read H X χ (marquee H p).reg (choir f ∘ pennant H)
    Nonempty (a.Moves s t) := by
  intro a; obtain ⟨π⟩:= J.laws.intake.cap.labels.moves s (S.ratio.embed t); obtain ⟨η,hη⟩:=settles H X χ s t π
  let e:=Song.whirl (ι:=Magazine H) s t; let a:=pennant H; let k:=badge H
  have hk i : k (congo k η i)=_ := perch k η i; have ha i : a (congo a e i)=_ := perch a e i
  let h x:= spirit (contents H p) f s t x
  refine ⟨⟨congo a e,congo k η,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩⟩
  · change (revolve _ (a (congo a e i))).site=_; rw [ha]; exact (h _).1
  · change (revolve _ (a (congo a e i))).support=_; rw [ha]; exact (h _).2.1
  · change (reserve H (k (congo k η i))).support=_; rw [hk]; exact (hη _).1
  · change (reserve H (k (congo k η i))).inventory=_; rw [hk]; exact (hη _).2.1
  · change (reserve H (k (congo k η i))).extraTest V ↔ _; rw [hk]; exact ((hη (k i)).2.2 V).1
  · change choir f (a (congo a e i)) V=_; rw [ha]; exact congr_fun (h (a i)).2.2 V
  change fuse H X χ (k (congo k η i)) V=_; rw [hk]; exact ((hη (k i)).2.2 V).2

lemma mimics (hp : X.units=Equiv.refl _) (i : ℕ) : X.furrow (icon H i)=icon J i := by
  suffices he: X.bearing (once H i)=once J i by
    change Sigma.mk 0 _=Sigma.mk 0 _; congr 1; funext j; exact he
  apply Subtype.ext; change X.units _=_; rw [hp]; rfl
end YM.PhysicalNext.Repeat.Beam
