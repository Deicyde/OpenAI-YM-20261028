import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StampCost

/-!
# Per-vertex receipts for determinant chain letters

Value, keep for paths with marks. Applies after imposing any θ/p prices
and interest (but not hitting exponent so large it varies with delay).
Expanding a scalar via Mayer uses once-per-label on the actual log terms
not on principal traces separated by color. Boundary estimates later. Does
not include the local principal logs (a gap part handles their differences).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse.Itinerary
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {η r Q : ℝ}

lemma out (P : Teller G) (L : Side) (i u : ℕ) (A ε : ℝ) (hA : 0 ≤ A) (hi : 4 ≤ i) {b d : ℝ} (hd : d < 0)
    (Y κ : ℝ → ℝ) (h : Rate G L b Y) (hk : Rate G L d κ) :
    ∃ Z : ℝ → ℝ, Rate G L b Z ∧ ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch.L=L → Room P S T x → 0≤Y x → 0≤κ x →
        Sales (radiusB x) A ε (receipt S (radiusB x) i u) (fun p => cap S (radiusB x) u p (Y x) (κ x))
          Sigma.fst (Z x) := by
  have h1 : Rate G L 0 (fun x => abundance L (3*radiusB x)) := (Census.width_rate G L 3 2).mul_right _
  have h2 : Rate G L 0 (fun x => expoHead L i (radiusB x) (3*radiusB x) u A) := by
    have hp (x : ℝ) := Nat.mul_add (u+1) (i*radiusB x) 1
    have hx := (((Census.width_rate G L ((u+1)*i) (u+1)).mul_right (density L)).mul (h1.pow u)).mul_right
      (Real.exp (A*((u:ℝ)+1)*steady i))
    simp only [zero_mul,add_zero] at hx; refine hx.congr (Eventually.of_forall ?_); intro x
    unfold expoHead; dsimp only; rw [hp x,← Nat.mul_assoc,Nat.mul_one]
  let Z (x : ℝ) := 2*(expoHead L i (radiusB x) (3*radiusB x) u A*Y x)
  refine ⟨Z,by simpa only [zero_add] using! (h2.mul h).mul_left 2,?_⟩
  have hh := hk.mul ((h1.mul_left 16).mul_right (Real.exp (A*steady i+2*ε)))
  filter_upwards [hh.below (by linarith) (1/2) (by norm_num)] with x hx c f S T hS hr hv hu
  have hb : 100 ≤ radiusB x := hr.sight.1
  unfold Z; rw [← hS]
  refine scalar S _ i (3*radiusB x) u A ε _ ?_ hv hu (fun _=>le_rfl) (by nlinarith only [hb,hi]) (by omega) hA ?_
  · intro j; unfold cap; split <;> positivity
  rw [hS]; exact (le_abs_self _).trans hx

/-- Attach ONE uniform beta cost left on every vertex for log/determinant
correction; all labels actual on the same θ,V,k even for a recombined/dropped packet.
User chooses halo `i` once (use enough for actual reads). Both `Z` nonnegative when
`X` exists. -/
theorem quoted (P : Teller G) (L : Side) (h : Torch η r Q) (i : ℕ) (hi : 4 ≤ i) (A ε b Y : ℝ) (hA : 0 ≤ A) :
    ∃ E F : ℝ → ℝ, Rate G L b E ∧ Rate G L b F ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (H : Forest S.ratio) (X : Coat T H),
      X.x=x → S.patch.L=L → Rotator P L η r Q Y X →
      let m := Census.tubularPrice G L
      let B := X.B
      Sales B A ε (receipt S B i 3) (capA G S η r Q m B) Sigma.fst (E x) ∧
      Sales B A ε (receipt S B i 1) (capS G S η r Q m B) Sigma.fst (F x) ∧
        (∀ j, |ArmA X.shutter X.plate j| ≤ capA G S η r Q m B j) ∧
        (∀ j, |ArmS X.shutter X.plate j| ≤ capS G S η r Q m B j) := by
  let m := Census.tubularPrice G L
  obtain ⟨E,hE,H⟩ := out P L i 3 A ε hA hi (show (-1:ℝ)<0 by norm_num) _ _
    ((h.physical G L b m).mul_left (flagP (G:=G)^4*((Q+1)*payE η r Q m))) ((h.physical G L (-1) m).mul_left (flagP (G:=G)))
  have hs v := ((h.physical G L v m).mul_left (payE η r Q m)).mul_left Q
  obtain ⟨Z,hZ,hG⟩ := out P L i 1 A ε hA hi (show (-1:ℝ)<0 by norm_num) _ _
    ((hs b).mul_left (flagP (G:=G)^2)) ((hs (-1)).mul_left (flagP (G:=G)))
  refine ⟨E,Z,hE,hZ,?_⟩
  filter_upwards [H,hG] with x hx hz c f S T F X hg hS hr
  subst x; intro m' B
  have hn : 0 ≤ flagP (G:=G) := by unfold flagP; positivity
  have hk := hr.scale
  have he : 0 ≤ payE η r Q m := hk.disc
  have ht : 0 ≤ scraps η r Q m (radiusB X.x) := hk.heap _
  have hh : 0 < Q := hk.fuel
  have hb : 4 ≤ X.B := le_trans (by norm_num) hr.room.sight.1
  exact ⟨hx c f S T hS hr.room (by positivity) (by positivity),hz c f S T hS hr.room (by positivity)
    (by positivity), first _ _ hk h (X.span hr.room) hb, next_cost _ _ hk (X.span hr.room) hb⟩
end YM.ConnectedActivityE6.Pulse.Itinerary
