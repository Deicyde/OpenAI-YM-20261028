import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Geometry
import YM.Bid.Craft
import YM.Push.ABSOLUTE_SUMS.Path

/-!
# Compulsory purchase on extendible stencils

Energy E credit is per seed. Retain every mask and likelihood through
this (bigger) halo in all such products, also where some default
elsewhere has been dropped! Works *under the true tag likelihoods per
site/bond in probability units*. Do not pay those separately on every
path that visits a site. Uses the actual grant (no hypothesis of other
energy transfers on a product tree).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Tags
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure  Oriented Channel
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

section probabilities
def siteMass (U : Config G f) (k : S.Choices) (x : Site c) :=
    (Fintype.card S.patch.FrameTag:ℝ) * S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) (k.1 x)

def pinMass (U : Config G f) (k : S.Choices) (i : Bond c) :=
    (Fintype.card S.patch.Points:ℝ) * S.patch.predictorMass S.kernel (S.connector U k.1 i) (k.2 i)

lemma site_nn (U : Config G f) (k : S.Choices) (x : Site c) : 0 ≤ siteMass U k x := by
  apply mul_nonneg (Nat.cast_nonneg _); unfold Patch.frameMass; split <;> positivity

lemma pin_nn (U : Config G f) (k : S.Choices) (x : Bond c) : 0 ≤ pinMass U k x := by
  apply mul_nonneg (Nat.cast_nonneg _); unfold Patch.predictorMass; split <;> first | positivity | exact S.patch.weight_nonneg _

lemma site_cap (U : Config G f) (k : S.Choices) (x : Site c) : siteMass U k x ≤ Fintype.card S.patch.FrameTag := by
  refine mul_le_of_le_one_right (Nat.cast_nonneg _) ?_; unfold Patch.frameMass; split
  · apply inv_le_one_of_one_le₀; exact_mod_cast Fintype.card_pos
  split
  next h => apply inv_le_one_of_one_le₀; exact_mod_cast Finset.card_pos.mpr ⟨_,h⟩
  next h => exact zero_le_one

lemma pin_cap (U : Config G f) (k : S.Choices) (x : Bond c) : pinMass U k x ≤ Fintype.card S.patch.Points := by
  refine mul_le_of_le_one_right (Nat.cast_nonneg _) ?_; unfold Patch.predictorMass; split
  · apply inv_le_one_of_one_le₀; exact_mod_cast Fintype.card_pos
  · rw [← S.patch.weight_sum]; exact single_le_sum (fun i _ => S.patch.weight_nonneg i) (mem_univ _)

/-- All remaining k summations with UNIFORM AVERAGE (including cases
with no reference branching). -/
lemma likelihood_all (U : Config G f) (k : S.Choices) :
    S.likelihood U k = (Fintype.card S.Choices:ℝ)⁻¹ * ((∏ i, siteMass U k i) * ∏ b, pinMass U k b) := by
  let A : ℝ := Fintype.card S.patch.FrameTag
  let P : ℝ := Fintype.card S.patch.Points
  have ha : 0 < A := by unfold A; exact_mod_cast Fintype.card_pos
  have hp : 0 < P := by unfold P; exact_mod_cast Fintype.card_pos
  have hf : (Fintype.card S.Choices:ℝ) = A^(Fintype.card (Site c)) * P^(Fintype.card (Bond c)) := by
    unfold StepData.Choices A P StepData.BondChoice StepData.SitesChoice
    simp [Bond]
  rw [hf]; unfold StepData.likelihood siteMass pinMass
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const,card_univ]
  change _ = _ * ( (A^_ * _) * (P^(Fintype.card (Bond c))*_))
  field_simp

lemma turns_site {s : Signed} (x : Site c) (h : S.patch.Branches S.kernel G) (k : S.Choices) (U : Config G f) :
    siteMass (pull s 0 U) (choice s k) x = siteMass U k (s.act x) := by
  let m := choice s k
  have hh : S.withinSites s 0 m.1 = k.1 := congr_arg Prod.fst ((S.withinChoice s 0).apply_symm_apply k)
  have he : m.1 x = (choice s k).1 x := rfl
  unfold siteMass
  rw [← he,← hh,← affine0 s x,S.port_site, ← (S.ratio.root.map_zero)]
  change _*S.patch.frameMass _ (expandAt _ (pull _ (S.ratio.embed _) U)) _ = _
  rw [expandAt_pull,S.port]; exact congr_arg _ (S.patch.frames_channel h s _ _).1
end probabilities

/-- Local hypotheses from factors kept together in a single
component, not testing fine realizability outside it. θ=1/4. -/
structure Wide (A : Stores S) (d : ℕ) (U : Config G f) (k : S.Choices) (V : Config G c) (x W : ℝ) : Prop where
  line (i : Site c) : i∈A.dome d → 0<siteMass U k i
  s (p : Cell f) : ¬Disjoint (A.dome d) (startPos S p) →
    ((p∈A.costs → fiery G x S.patch.L/4 ≤ toll U p) ∧ (p∉A.costs → toll U p ≤ fiery G x S.patch.L/2))
  n (b : Bond c) : ¬Disjoint (A.dome d) (pinPos b) →
    ((b∈A.aisles → W*fiery G x S.patch.L ≤ wire (S.prediction U k) V b) ∧
       (b∉A.aisles → wire (S.prediction U k) V b ≤ 2*W*fiery G x S.patch.L))
  flags (i : Site c) : i∈A.dome d → (i∈A.flags ↔ i∈RG.flags (temp x) V)

namespace Wide
variable {A : Stores S} {d : ℕ} {U : Config G f} {k : S.Choices} {V : Config G c} {x W : ℝ}

lemma frame_active (h : Wide A d U k V x W) (i : Site c) (he : i∈A.dome d) :
    0<S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i) :=
  pos_of_mul_pos_right (h.line i he) (Nat.cast_nonneg _)

lemma shrink (h : Wide A d U k V x W) {d' : ℕ} (hd : d' ≤ d) : Wide A d' U k V x W := by
  have he : A.dome d' ⊆ A.dome d := Lattice.Corona.halo_mono hd (Finset.Subset.refl _)
  exact ⟨fun i hi => h.line i (he hi), fun p hh => h.s p fun hz => hh (hz.mono_left he),
    fun p hh => h.n p fun hz => hh (hz.mono_left he), fun i hi => h.flags i (he hi)⟩

lemma plot (h : Wide A d U k V x W) (he : 5*radiusB x ≤ d) : Stores.Plot A U k V x W := by
  have hv := h.shrink he
  exact ⟨hv.s,hv.n,hv.flags,hv.frame_active⟩

lemma rotate (h : Wide A d U k V x W) (s : Signed) (he : S.patch.Branches S.kernel G) :
    Wide (turnStore s A) d (pull s 0 U) (Oriented.choice s k) (pull s 0 V) x W := by
  constructor
  · intro i hi; rw [turns_site _ he]; apply h.line _ ((rotates_dome ..).mp hi)
  · intro p hp
    replace hp := Finset.not_disjoint_iff.mp hp
    obtain ⟨y,hy,hv⟩ := hp
    have hh : toll (pull s 0 U) p=toll U (Oriented.faces s f p) :=
      Face.send_price U p s 0 G.chord G.chord_inv fun k g => G.chord_conj g k
    rw [hh,show p∈(turnStore s A).costs ↔ Oriented.faces s f p∈A.costs by simp [turnStore]]
    exact h.s _ (Finset.not_disjoint_iff.mpr ⟨s.act y,(rotates_dome ..).mp hy,(site_face ..).mp hv⟩)
  · intro b hb
    replace hb := Finset.not_disjoint_iff.mp hb
    obtain ⟨y,hy,hv⟩ := hb
    rw [(carry _ he ..).2,wire_pulled]
    rw [show b∈(turnStore s A).aisles ↔ (StepData.sendBonds s 0 b)∈A.aisles by simp [turnStore]]
    exact h.n (edge s b) (Finset.not_disjoint_iff.mpr ⟨s.act y,(rotates_dome ..).mp hy,(endpoints s b y).mp hv⟩)
  · intro i hi
    have hs : StepData.sendSites s 0 i=s.act i := affine0 ..
    have h₀ : i ∈ (turnStore s A).flags ↔ s.act i ∈ A.flags := by rw [← hs]; unfold turnStore; simp only [mem_map_equiv, Equiv.symm_symm]
    rw [h₀, h.flags _ ((rotates_dome ..).mp hi),← Work.H03.flags_send s 0 (temp x) V]
    have he : s.act i=affine s 0 i := (affine0 ..).symm
    rw [he]; simp only [Finset.mem_image]; constructor
    · rintro ⟨b,hb,h⟩; exact (StepData.sendSites s (0:Site c)).injective h ▸ hb
    intro h; exact ⟨i,h,rfl⟩

lemma bought {T : Tube G S} {κ : ℝ} (h : Wide A d U k V x W) (hB : 5*radiusB x≤d)
    (he : S.patch.Branches S.kernel G) (F : Forest S.ratio) (hf : Stores.SliceSet S F U)
    (hp : PointCharge T x W κ) : κ*(fiery G x S.patch.L)^2*A.shares ≤ meanEnergy A T x U k V := by
  rw [← av_const (κ*(fiery G x S.patch.L)^2*A.shares)]
  refine av_mono fun s => ?_
  have hu := hp (turnForest s F) _ _ _ _ (turn_sliced s F U hf) ((h.rotate s he).plot hB)
  rw [same_price] at hu; exact hu


end Wide
end YM.ConnectedActivityE6.Tags
