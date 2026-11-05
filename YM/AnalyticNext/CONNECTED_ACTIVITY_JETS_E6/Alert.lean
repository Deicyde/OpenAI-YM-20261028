import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Caps
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Eligibility

/-!
# Trigger factors/dictionary

Each one per-address; including override where assignment decision compulsory.
Keep all outputs even when value zero. Patches extend all U reads.
For h's requiring likelihood, use actual evaluated Q including its
choice at ZERO likelihood, because numerical formulas still refer there.
Reference k probability uniform. `unpaid` only uses Dot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- display separate partitions, likelihood tags and actual fine q. Does NOT
include gamma complement; include for rarity later. -/
abbrev Panic (c f : Side) := Cell f ⊕ Bond c ⊕ Bond c ⊕ Site c ⊕ Site f
abbrev WarningAt (c f : Side) := Panic c f ⊕ Bond f

namespace Coat
variable (X : Coat T F)

def focus_alarms (S : StepData c f) : Panic c f → Site c := Sum.elim (S.ratio.parent∘Prod.fst)
    (Sum.elim Prod.fst (Sum.elim Prod.fst (Sum.elim id S.ratio.parent)))

def districts (S : StepData c f) : Panic c f → Support c := Sum.elim (startPos S)
    (Sum.elim pinPos (Sum.elim pinPos (Sum.elim singleton (fun i=>{S.ratio.parent i}))))
def shouting (S : StepData c f) : WarningAt c f → Site c := Sum.elim (focus_alarms S) (atEdge S)
def field_support (S : StepData c f) (B l : ℕ) : WarningAt c f → Support c :=
    Sum.elim (fun i => halo (l*B) (districts S i)) (town S B l)

lemma home_storm (S : StepData c f) (k : Panic c f) : focus_alarms S k∈districts S k := by
  rcases k with k|k|k|k|k
  · exact Packets.contains S (.inl k)
  · exact mem_insert_self ..
  · exact mem_insert_self ..
  · exact mem_singleton_self k
  exact mem_singleton_self _
lemma sigh (S : StepData c f) (k : WarningAt c f) (z : Site c) (B l : ℕ) (h : z∈field_support S B l k) :
    separation (shouting S k) z ≤ l*B+1 := by
  rcases k with k|b
  swap; · exact checking S l B b z h
  obtain ⟨x,hx,he⟩ := halo_spec.mp h
  apply ((separation_triangle _ x _).trans (Nat.add_le_add_left he _)).trans
  suffices hh : separation (focus_alarms S k) x ≤ 1 by change separation (focus_alarms S k) x+ _ ≤ _; omega
  rcases k with k|k|k|k|k
  · exact Packets.price_one S (.inl k) x hx
  · exact Packets.price_one S (.inr (.inl k)) x hx
  · exact Packets.price_one S (.inr (.inl k)) x hx
  · rw [mem_singleton.mp hx,show focus_alarms S _=k from rfl]; simp
  rw [mem_singleton.mp hx,show focus_alarms S _=S.ratio.parent k from rfl]; simp
lemma crucial (S : StepData c f) (k : WarningAt c f) (B l : ℕ) : shouting S k∈field_support S B l k := by
  rcases k with k|k
  · exact halo_subset _ (districts S k) (home_storm S k)
  exact city ..

def mandatory (A : Stores S) (B : ℕ) (p : Panic c f) := ¬Disjoint (A.dome (300*B)) (districts S p)

/-- One untouched detect factor. -/
def rawStorm (u : Directions G f) (W : ℝ) (A : Stores S) (R : Rep G f) (l : Finset ℕ) : Panic c f → ℝ :=
    let U := X.input u
    Sum.elim (fun p => Mask.fine A X.χ p X.t U) (Sum.elim (fun p=> Mask.noise A X.χ p X.t W U X.k X.V)
    (Sum.elim (Tags.pinMass U X.k) (Sum.elim (Tags.siteMass U X.k) (Contract.charges R l U))))

def mayor (u : Directions G f) (W a : ℝ) (R : Rep G f) (l : Finset ℕ) (i : Panic c f) :=
    if mandatory X.seeds X.B i then 0 else
      X.enforce (2*a) u (X.plaza (halo X.B (districts S i))) * (X.rawStorm u W X.seeds R l i-1)

def aura (u : Directions G f) (a : ℝ) (i : Bond f) :=
    if X.Hot i ∧ i∉X.plaza (X.seeds.dome (304*X.B)) then X.cone a u i-1 else 0
def detect (u : Directions G f) (W a : ℝ) (R : Rep G f) (l : Finset ℕ) : WarningAt c f → ℝ :=
    Sum.elim (X.mayor u W a R l) (X.aura u a)

def topStorm (D : Patch) := 1+(Fintype.card D.FrameTag:ℝ)+(Fintype.card D.Points:ℝ)
lemma topStorm_one (D : Patch) : 1 ≤ topStorm D := by unfold topStorm; exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

lemma inspected (u : Directions G f) (W : ℝ) (R : Rep G f) (l : Finset ℕ) (A : Stores S) (p : Panic c f) :
    X.rawStorm u W A R l p∈Set.Icc 0 (topStorm S.patch) := by
  rcases p with p|p|p|p|p
  · exact ⟨(Mask.fine_range ..).1,(Mask.fine_range ..).2.trans (topStorm_one _)⟩
  · exact ⟨(Mask.noise_range ..).1,(Mask.noise_range ..).2.trans (topStorm_one _)⟩
  · exact ⟨Tags.pin_nn ..,(Tags.pin_cap ..).trans (by unfold topStorm; apply le_add_of_nonneg_left; positivity)⟩
  · refine ⟨Tags.site_nn ..,(Tags.site_cap ..).trans ((le_add_of_nonneg_left zero_le_one).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _)))⟩
  change Contract.charges _ _ _ _ ∈ _; rcases Contract.ordinary R l (X.input u) p with h|h <;>
    simp [h,topStorm_one,show 0≤topStorm S.patch from zero_le_one.trans (topStorm_one _)]

lemma fires_at (u : Directions G f) (W a : ℝ) (R : Rep G f) (l : Finset ℕ) (i : WarningAt c f) :
    |X.detect u W a R l i| ≤ topStorm S.patch := by
  have ht := topStorm_one S.patch
  rcases i with i|i
  · unfold detect mayor; dsimp only [Sum.elim]; split
    next h => rw [abs_zero]; linarith
    next h =>
      rw [abs_mul,abs_of_nonneg (X.conserve ..).1]; apply (mul_le_of_le_one_left (abs_nonneg _) (X.conserve ..).2).trans
      obtain ⟨hh,hk⟩ := X.inspected u W R l X.seeds i; apply abs_le.mpr; constructor <;> linarith
  change |X.aura u a i| ≤ _
  unfold aura; split
  next hz => obtain ⟨hy,h⟩ := X.booked a u i; apply abs_le.mpr; constructor <;> linarith
  next hu => rw [abs_zero]; linarith

end Coat
end YM.ConnectedActivityE6
