import YM.Extra.ITERATION_NO_LOSS.TermNorm
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Voice
import YM.Push.LOCAL_SPLITTING.Orientation



/-!
Whole path addresses (actual Slot.stencil, not endpoint distance; this
convention overcounts possible mask reads for the long labels). The
`PathData.kept` definition looks at all plaquettes, but payment height
proves every failure is in B-ball, which suffices for extensional
locality of the positive and negative answer. A receipt `LaneCounts`
for this in Map.Aperture. Don't introduce a global-good-field premise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Voice
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo 
variable {G : Gauge} {c f : Side} {S : StepData c f} (d : AnalyticBridge.LocalGaussian.Desk G S)

section ancestry
variable {n m : Side} {r : ℕ} {F : PathData G} (σ : Signed) (P : BudgetPoint)
    (Q : Atom G r)

def turn (n : Side) (s : Signed) (X : Support n) := X.image (Push.Local.turnSites s 0)


def catalog (x : Site n) := turn n σ (inspected (Q.footprint x))

private lemma masking {X : Type*} [Zero X] {Y : Support n} {t : ℝ} {Z : Config G n → X} (h : LocalOn Y Z) :
    LocalOn (inspected Y) (masked t Y Z) := by
  intro u v hu
  have hv : Healthy t Y u ↔ Healthy t Y v := by
    have he := flags_agree t u v Y hu
    simp only [Healthy, disjoint_iff_inf_le,Finset.inf_eq_inter,he]
  by_cases he : Healthy t Y u
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (hv.mp he)]
    apply h; apply agrees_mono hu
    intro i hi; exact Finset.mem_union_left _ hi
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (mt hv.mpr he)]



def lot (x : Site n) (i : Slot) := i.stencil.image (fun z => wrap n z+x)

def spool (p : Cell n) (u : ℕ×ℕ) := lot p.1 (F.row p.2 u.1).2 ∪ lot p.1 (F.row p.2 u.2).2

lemma inside (i : Slot) (x : Site n) : LocalOn (lot x i) (fun V : Config G n => i.atSite V x) := by
  intro U V hv
  apply i.covered
  -- or expandAt
  intro e he hf
  apply hv (wrap n e.1+x,e.2) ((Finset.mem_image_of_mem _ (show e.1∈i.stencil from he)))
  have hg : e.1+step e.2 ∈ i.stencil:=hf
  have hh := Finset.mem_image_of_mem (fun z => wrap n z+x) hg
  simpa [lot, add_right_comm] using! hh

-- Needed even for long tail kept decisions at their *physical
-- anchor* in the transformed orientation.
lemma keeper (p : Site n → Site m) (hp : ∀ x i, separation (p x) (p (x+step i)) ≤ 1) {G' : Gauge} (L : PathData G') (x t : ℝ)
    (A : Clip) (R : ℕ) (o : Site n)
    {e : ℝ} (h : Bid.LaneCounts L x t A e R p) (hb : 120≤radiusB x) (U V : Config G' n)
    (hv : AgreeNear p (p o) (radiusB x) U V) : PathData.kept A t o U ↔ PathData.kept A t o V := by
  have he (U V : Config G' n) (hv : AgreeNear p (p o) (radiusB x) U V) :
      PathData.kept A t o U → PathData.kept A t o V := by
    intro hw i; by_contra! hh
    have hf := h.dropped V o i hh
    rw [← face_near hp i U V (hv.shrink (by omega))] at hh
    exact hh.not_ge (hw i)
  exact ⟨he U V hv, he V U fun i hi => (hv i hi).symm⟩

lemma spooled {U V : Config G n} (a : Clip) (P' : BudgetPoint) (i : Cell n) (u : ℕ×ℕ) (k r : ℕ)
    (h : Agrees (spool (F:=F) i u) U V) (ht : PathData.kept a P'.threshold i.1 U ↔ PathData.kept a P'.threshold i.1 V) :
    labelPath k r F a U i P' u=labelPath k r F a V i P' u := by
  have he (j : ℕ) (hj : lot i.1 (F.row i.2 j).2 ⊆ spool (F:=F) i u) : F.ellTerms i j U=F.ellTerms i j V := by
    unfold PathData.ellTerms; exact congr_arg ((F.row i.2 j).1 • ·) (inside (G:=G) (F.row i.2 j).2 i.1 U V (agrees_mono h (fun i h=> hj h)))
  have hc:=he u.1 Finset.subset_union_left; have hh:=he u.2 Finset.subset_union_right
  unfold labelPath; rw [ht,hc,hh]; unfold shortenTerm; rw [hc,hh]

lemma spooled_meas (k r : ℕ) (F : PathData G) (a : Clip) (i : Cell n) (P : BudgetPoint) (j : ℕ×ℕ) :
    Measurable (fun U => labelPath k r F a U i P j) := by
  unfold labelPath; apply Measurable.ite (PathData.kept_closed ..).measurableSet _ measurable_const
  have hf (j : ℕ) : Continuous (fun U => F.ellTerms i j U) := by unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
  apply Continuous.measurable
  unfold shortenTerm
  split_ifs <;> fun_prop
end ancestry

local notation "M" => till d.betaHat
local notation "P" => d.tube
local notation "x₀" => d.betaHat
local notation "B" => radiusB d.betaHat

def chaperone : Spot.BasePosts c f → Support c
  | .inl (σ,.inl (i,u)) => insert (σ.act (S.ratio.parent i.1)) ((turn f σ (spool (F:=d.input.path) i u)).image S.ratio.parent)
  | .inl (σ,.inr (y,l)) => match l with
    | .inl i => (catalog σ (d.input.path.cubic i) y).image S.ratio.parent
    | .inr (.inl i) => (catalog σ (d.input.path.quartic i) y).image S.ratio.parent
    | .inr (.inr i) => (catalog σ (d.input.path.loop i) y).image S.ratio.parent
  | .inr (s,i,l) => insert (s.act i.1) (turn c s (spool (F:=(P).down) i l))

def cart (i : Spot.BasePosts c f) : Formula G S ℝ := fun F A b k V l => match i with
  | .inl (σ,i) => (Fintype.card Signed:ℝ)⁻¹ * (-old (d:=d) i (pull σ 0 (skin d F A b k V l)))
  | .inr (σ,i,j) => d.input.beta * ((Fintype.card Signed:ℝ)⁻¹ * labelPath M S.patch.L.val (P).down (P).low (pull σ 0 V) i d.out j)

lemma supplied (h : Route.Badge.App d) (i : Spot.BasePosts c f) : Care d (chaperone d i) (cart d i) := by
  obtain ⟨D,hP⟩:=h.valid.funds
  have hm (σ : Signed) (F : Forest S.ratio) (A : Stores S) (b : Finset ℕ) (k : S.Choices) :
      Measurable (fun y : Config G c × Refs G f=> pull σ 0 (skin d F A b k y.1 y.2)) := (continuous_pull σ 0).measurable.comp
        (Print.printed_meas P x₀ d.broadCut d.radius d.g hP k A F h.valid.positive h.enough)
  constructor
  · intro F A b k
    have hr := hm
    have hl {r} (σ) (q : Atom G r) (y : Site f) : Measurable (fun p : Config G c × Refs G f=> q.placed d.input.p (pull σ 0 (skin d F A b k p.1 p.2)) y) :=
      (masked_measurable _ _ _ (q.unmasked_cont y).measurable).comp (hr σ F A b k)
    rcases i with ⟨σ,i|i⟩|⟨σ,i,j⟩
    · exact measurable_const.mul (measurable_const.mul ((spooled_meas M 1 d.input.path d.input.clip i.1 d.input.p i.2).comp (hr σ F A b k))).neg
    · rcases i with ⟨z,l|l|l⟩
      · exact measurable_const.mul (measurable_const.mul (hl σ (d.input.path.cubic l) z)).neg
      · exact measurable_const.mul (measurable_const.mul (hl σ (d.input.path.quartic l) z)).neg
      exact measurable_const.mul (hl σ (d.input.path.loop l) z).neg
    exact measurable_const.mul (measurable_const.mul ((spooled_meas M S.patch.L.val (P).down (P).low i d.out j).comp
      ((continuous_pull σ 0).measurable.comp measurable_fst)))
  intro F F' A A' b b' k k' V V' p p' H
  let U:=skin d F A b k V p; let U':=skin d F' A' b' k' V' p'
  let Y:=chaperone d i
  -- Keep both pullbacks of actual paths. For X⊆Y, X rotated is
  -- already in our projection, no distance-to-seam test.
  have hu (σ : Signed) (X : Support f) (hb : (turn f σ X).image S.ratio.parent ⊆ Y) : Agrees X (pull σ 0 U) (pull σ 0 U') :=
    Push.Local.agrees_pull σ 0 (ink d h H hb)
  have hv (σ : Signed) (X : Support c) (hb : turn c σ X ⊆ Y) : Agrees X (pull σ 0 V) (pull σ 0 V') :=
    Push.Local.agrees_pull σ 0 (agrees_mono H.fields.configuration (fun i hi => halo_subset _ _ (hb (show i∈turn c σ X from hi))))
  have hf (σ : Signed) (q : Site c) (hY : σ.act q∈Y) := read_turn σ q (radiusB d.betaHat) V V'
    (Geo.Reads.visit H.fields ((covers_shield (40*B) hY).shrink (by have ht:=h.aperture.scale; omega)))
  have hz (σ : Signed) (q : Site f) (hY : σ.act (S.ratio.parent q)∈Y) : AgreeNear S.ratio.parent (S.ratio.parent q) B (pull σ 0 U) (pull σ 0 U') :=
    pulled_near U U' σ (S.ratio.parent q) B (anchored (daily d h H _ hY) (by have ht:=h.aperture.scale; omega))
  have hy {r} (q : Atom G r) (z : Site f) (σ : Signed) (hl : (catalog σ q z).image S.ratio.parent ⊆ Y) :
      q.placed d.input.p (pull σ 0 U) z=q.placed d.input.p (pull σ 0 U') z := masking (Extra.Iteration.Derivs.atom_local q z) _ _ (hu σ _ hl)
  unfold cart; rcases i with ⟨σ,⟨i,u⟩|⟨i,l⟩⟩|⟨σ,i,l⟩
  · unfold old; dsimp only
    obtain ⟨C,hL⟩:=h.aperture.fine
    rw [h.valid.same.path,h.valid.same.clip]
    have hE:=keeper S.ratio.parent (Work.E03.parent_step S) (P).up x₀ (fiery ..) (P).high 1 i.1 hL h.aperture.scale _ _
        (hz σ i.1 (Finset.mem_insert_self ..))
    have he := spooled (U:=pull σ 0 U) (P).high (d.input.p) i u M 1
      (hu σ (spool (F:=(P).up) i u) ?_) ?_
    swap
    · unfold Y chaperone; dsimp only; rw [h.valid.same.path]; exact Finset.subset_insert _ _
    swap
    · rw [h.valid.same.temp]; exact hE
    rw [show labelPath M 1 (P).up (P).high (pull σ 0 (skin d F A b k V p)) i d.input.p u=_ from he]
  · cases l with
    | inl j =>
      exact congr_arg (fun y : ℝ => (Fintype.card Signed:ℝ)⁻¹ * -(d.input.beta*y)) (hy _ i σ (show (catalog σ (d.input.path.cubic j) i).image _ ⊆ _ from Finset.Subset.refl _))
    | inr j =>
      cases j with
      | inl j => exact congr_arg (fun y : ℝ => (Fintype.card Signed:ℝ)⁻¹ * -(d.input.beta*y)) (hy _ i σ (show (catalog σ (d.input.path.quartic j) i).image _ ⊆ _ from Finset.Subset.refl _))
      | inr j => exact congr_arg (fun y : ℝ => (Fintype.card Signed:ℝ)⁻¹ * -y) (hy _ i σ (show (catalog σ (d.input.path.loop j) i).image _ ⊆ _ from Finset.Subset.refl _))
  obtain ⟨C,hL⟩:=h.aperture.coarse
  dsimp only
  rw [spooled (F:=(P).down) (P).low d.out i l M _ (hv σ _ (Finset.subset_insert ..)) (by
    rw [h.valid.coarse]; exact keeper id Work.E03.sep_step (P).down x₀ (temp x₀) (P).low S.patch.L.val i.1 hL h.aperture.scale _ _
      (hf σ i.1 (Finset.mem_insert_self ..))) ]
end YM.PhysicalNext.Dictionary.Voice
