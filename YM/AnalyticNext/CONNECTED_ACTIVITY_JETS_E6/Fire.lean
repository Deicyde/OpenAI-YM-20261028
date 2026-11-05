import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Threshold

/-!
# Second estimates and excursions

Use actual charged labels. Ready mark/r restoration incl complete masks and
D volume. No normalization by dividing gas on punctured set. All addr signed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C a' δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)

abbrev seam (D : Cash W α μ L Q o C T R) := blocked D.smallAt
structure Renewed (j : ℕ) (a δ δ' : ℝ) (H : Cash W α μ L Q o C T R) : Prop where
  full : 0 ≤ a
  shift : Ready H.smallAt (radiusB α) (H.thinPay j) (a+δ') (Q.overture L μ α j) δ (1/2)
  marks : Ac.Hit H.largeAt (radiusB α) (H.broadPay j) (a+δ') (Q.quantum L μ α 0 j 1 0)
  tree : degreePrice (radiusB α) (Q.mergeScale L μ α j) δ' ≤ 1/2
  paid : Q.mergeScale L μ α j ≤ 1/2
  post : 0<δ'
  sits : a+δ'+δ≤Q.exp

lemma anew (Q : YM.ConnectedActivityE6.Target G P) (L : Side) {μ W : ℝ} (o : Target.Order G W) (C : ℝ) (hμ : 0<μ)
    (j : ℕ) {a δ δ' : ℝ} (ha : 0 ≤ a) (he : 0<δ) (ht : 0<δ') (hp : a+δ'+δ ≤ Q.exp) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), ∀ H : Cash W x μ L Q o C T R,
    Renewed j a δ δ' H := by
  filter_upwards [Q.certify L hμ j _ _ he ht] with x hx c f S T R H
  exact ⟨ha,⟨hx.1,he,hx.2.2.2.1,by norm_num,fun _=>H.ours_pos ..,H.goods 0 j 0 0 hp⟩,H.gross 0 j 1 0
    ((le_add_of_nonneg_right he.le).trans hp), hx.2.2.2.2,hx.2.2.1,ht,hp⟩

variable (p : Renewed j a δ e H)
def trained (X : Coat T F) (c : Clusters H.ThinP) := Gas.term H.seam (H.entries X) c
-- outputs
lemma hardH : Hard H.seam := ⟨fun _=>Or.inl rfl, fun _ _=> blocked_back H.smallAt⟩
lemma testS : Tests H.seam H.smallAt := literal_test _ fun i=> i.2.1
include he hk p



end YM.ConnectedActivityE6.Cash
