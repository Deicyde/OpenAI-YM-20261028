import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rod
import YM.Work.F05.Actions

/-!
# Axial carriers in the physical orientation/channel of a row

D under sector rotations is a linear action on the SAME input. Reads an axial
carrier only through the numerical range of the row (larger full query halos
still needed). Does not permute independently the branch outcomes nor choose
a fresh stencil when a row value is zero. Reversal of a link in the input uses
the V-dependent orientation change; rows are kept as *whole channel rows*,
not equated componentwise between channels. This is a variation from E's
Qderivative at a curved patch; note at no point is the nonlinear row replaced
in the actual energy -- price is for identity test adding/subtracting squares.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix Laurent
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- In-channel coordinate-order path between output sites. -/
def carriage (x y : Site c) := route 0 (lift (y-x)) 1

def carrier (x : Site c) (V : Config G c) (y : Site c) := travel V x (carriage x y)

lemma deposits (x y : Site c) : stop x (carriage x y)=y := by
  simpa [carriage] using Work.E03.stop_route x 0 (lift (y-x))

lemma mileage (x y : Site c) : (carriage x y).length ≤ 4*separation x y := by
  have hm (p q : Cover) : (route p q 1).length = size (q-p) := by
    have ha : allAxes 1 = [0,1,2,3] := by decide
    simp [route, axisRoute, ha, size, Fin.sum_univ_succ, straight, Axis]
  unfold carriage; rw [hm, sub_zero, separation_comm x y]; unfold size
  exact ((sum_le_sum (f:=fun i : Axis => ((lift (y-x)) i).natAbs) (fun i _ => component_le (y-x) i))).trans_eq
    (by simp [Axis]; rfl)

lemma trivial (w : Walk) (x : Site c) : travel (1:Config G c) x w = 1 := by
  induction w generalizing x <;> simp_all [travel,Step.read]

def spinRow (S : StepData c f) (z : Site c → G.El) (u : Directions G f) : Directions G f := fun i =>
    G.adjoint (z (atEdge S i)) (u i)

def straightened (T : Tube G S) (R : ℕ) (V : Config G c) (u : Directions G f) (p : Rod c f) :=
    barField T R (spinRow S (carrier (focus S p) V) u) p

def orientedRow (T : Tube G S) (R : ℕ) (s : Signed) (p : Rod c f) (V : Config G c) (u : Directions G f) :=
    straightened T R (pull s 0 V) (displacement s u (replica S.ratio V)) p

lemma turns_here (T : Tube G S) (R : ℕ) (p : Rod c f) (V : Config G c) (u : Directions G f) :
    orientedRow T R 1 p V u=straightened T R V u p := by
  unfold orientedRow; rw [pull_id]
  have he : displacement 1 u (replica S.ratio V) = u := by
    funext i; unfold displacement; dsimp only; rw [if_neg (by simp)]
    rw [show edge 1 i=i from by rw [positive _ _ (by simp)]; simp]
  rw [he]

lemma flat_strip (T : Tube G S) (R : ℕ) (p : Rod c f) (u : Directions G f) :
    straightened T R 1 u p=barField T R u p := by unfold straightened spinRow carrier; simp_rw [trivial,G.adjoint_one]

lemma rotated_input (V : Config G c) (s : Signed) (z : Site c → G.El) (u : Directions G f) :
    displacement s (spinRow S z u) (replica S.ratio (gauge z V)) =
      spinRow S (z ∘ s.act) (displacement s u (replica S.ratio V)) := by
  funext i
  rw [← copied S.ratio S.patch.odd_side V z]
  let w := constantGauge z S.ratio
  change displacement s (fun j => G.adjoint (w j.1) (u j)) _ i = _
  rw [gauge_displacement]; unfold w constantGauge Function.comp spinRow atEdge
  rw [Ratio.parent_signed S.ratio S.patch.odd_side]

lemma under (T : Tube G S) {Q : Clip} {σ C Λ : ℝ} (h : T.up.Bounds Q σ C Λ)
    (R : ℕ) (z : Site c → G.El) (V : Config G c) (u : Directions G f) (p : Rod c f) :
    straightened T R (gauge z V) (spinRow S z u) p = G.adjoint (z (focus S p)) (straightened T R V u p) := by
  unfold straightened; rw [← recolor T h R]
  have he : spinRow S (carrier (focus S p) (gauge z V)) (spinRow S z u) =
      fun i => G.adjoint (z (focus S p)) (spinRow S (carrier (focus S p) V) u i) := by
    funext i; simp only [spinRow,carrier, travel_gauge,deposits,← G.adjoint_mul, inv_mul_cancel_right]
  rw [he]

lemma oriented_under (T : Tube G S) {Q : Clip} {σ C Λ : ℝ} (h : T.up.Bounds Q σ C Λ)
    (R : ℕ) (z : Site c → G.El) (s : Signed) (V : Config G c) (u : Directions G f) (p : Rod c f) :
    orientedRow T R s p (gauge z V) (spinRow S z u) = G.adjoint (z (s.act (focus S p))) (orientedRow T R s p V u) := by
  unfold orientedRow; rw [rotated_input,Work.F05.pull_gauge_zero]
  simp only [affine0]
  exact under T h R (z ∘ s.act) _ _ _

lemma linear (T : Tube G S) (R : ℕ) {Q : Clip} {σ C Λ : ℝ} (h : T.up.Bounds Q σ C Λ) (s : Signed)
    (i : Rod c f) (V : Config G c) : ∃ F : (Directions G f) →L[ℝ] G.Color, ∀ u,
      F u = orientedRow T R s i V u := by
  let N u := spinRow S (carrier (focus S i) (pull s 0 V)) (displacement s u (replica S.ratio V))
  have he (x y) : N (x+y)=N x+N y := by
    funext b; dsimp only [N, spinRow, displacement]; split
    next hs => simp only [Pi.add_apply,map_add,neg_add,map_neg,spinRow,displacement,if_pos hs]
    next hn => simp only [Pi.add_apply,map_add,spinRow,displacement]; simp only [if_neg hn]
  have hu (b : ℝ) (x) : N (b • x)=b • N x := by
    funext e; dsimp only [N,spinRow,displacement]; split
    next hz => simp [Pi.smul_apply,spinRow,displacement,hz]
    next hn => simp [Pi.smul_apply,spinRow,displacement,hn]
  let F : Directions G f →ₗ[ℝ] G.Color :=
    { toFun x := barField T R (N x) i
      map_add' := fun x y => by rw [he,bar_add T h]
      map_smul' := fun x y => by rw [hu,bar_smul T h]; rfl }
  exact ⟨F.toContinuousLinearMap,fun _ => rfl⟩

lemma carrier_near (x y : Site c) (V W : Config G c) (B : ℕ) (h : AgreeNear id x B V W)
    (hk : 4*separation x y ≤ B) : carrier x V y=carrier x W y :=
    travel_near id Work.E03.sep_step V W x (carriage x y) B ((mileage _ _).trans hk) h

lemma short_near (T : Tube G S) (h : S.patch.Branches S.kernel G) (R : ℕ)
    (V W : Config G c) (a b : Directions G f) (p : Rod c f) (d : ℕ) :
    let o := focus S p; let k := R+predReach S.patch+4
    4*k ≤ d → AgreeNear id o d V W →
      (∀ i : Bond f, distAt S i o ≤ k → a i=b i) → straightened T R V a p=straightened T R W b p := by
  intro o k hd hp hx
  apply tangent_local T h
  intro i hi
  unfold spinRow; rw [hx i hi,carrier_near o (atEdge S i) V W d hp (le_trans (Nat.mul_le_mul_left 4 hi) hd)]

lemma projects (S : StepData c f) (s : Signed) (o : Site c) (i : Bond f) :
    distAt S (edge s i) (s.act o) ≤ distAt S i o + 1 := by
  unfold distAt atEdge; cases h : s.flip i.2
  · rw [positive s i h]
    dsimp only; rw [S.ratio.parent_signed S.patch.odd_side,separation_signed]; omega
  rw [negative s i h]
  dsimp only; rw [S.ratio.parent_signed S.patch.odd_side,separation_signed]
  exact (separation_triangle o (S.ratio.parent i.1) _).trans
    (Nat.add_le_add_left (Work.E03.parent_step S ..) _)

lemma exact_turn {n : Side} (i : Bond n) (s : Signed) : separation (s.act i.1) (edge s i).1 ≤ 1 := by
  cases h : s.flip i.2
  · rw [positive s i h]; simp
  rw [negative s i h]; dsimp only
  rw [separation_signed]; exact Work.E03.sep_step ..

lemma projected_wealth (s : Signed) (i : Bond c) (o : Site c) :
    separation (s.act o) (edge s i).1 ≤ separation o i.1 + 1 :=
  (separation_triangle _ (s.act i.1) _).trans (by rw [separation_signed]; gcongr; exact exact_turn i s)

lemma raw_near (T : Tube G S) {P : Teller G} {x : ℝ} (h : Room P S T x)
    (V W : Config G c) (a b : Directions G f) (p : Rod c f) (s : Signed) :
    let o := s.act (focus S p); let d := radiusB x/4
    AgreeNear id o d V W → (∀ i : Bond f, distAt S i o ≤ d → a i=b i) →
      orientedRow T (till x) s p V a=orientedRow T (till x) s p W b := by
  intro o d hv hu
  have hh := h.frame
  have hB : 4*(till x+predReach S.patch+4) ≤ d/2 := by unfold d till; omega
  apply short_near T (SectorMeasure.funds_branch h.accepted) (till x) _ _ _ _ p (d/2) hB
  · intro i hi
    have hs := projected_wealth s i (focus S p)
    change separation (focus S p) i.1 ≤ d/2 at hi
    have he := hv (edge s i) (by change separation (s.act (focus S p)) (edge s i).1 ≤ d; omega)
    rw [charge,charge,he]
  intro i hi
  have hk := projects S s (focus S p) i
  have he : distAt S (edge s i) o ≤ d := by unfold o; omega
  have ht : replica S.ratio V (edge s i)=replica S.ratio W (edge s i) := by
    unfold replica; split
    next hp => rfl
    next hp => exact hv _ he
  dsimp only [displacement]; rw [hu _ he, ht]
end YM.ConnectedActivityE6.SliceRows
