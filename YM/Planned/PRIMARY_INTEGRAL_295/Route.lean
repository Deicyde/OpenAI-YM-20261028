import YM.Planned.PRIMARY_INTEGRAL_295.Stepping
import YM.Source.ODE
import YM.Work.G02


/-!
# Link profiles of the Snap read

Actual cover coordinates in E4, centered at the read anchor. For mixed
log-chart link derivatives we use a (small, not minimal) finite-dimensional
ODE parameter: expand also in time on that link. The functions and identities
here already suffice on a single positive link arbitrarily far from the read
anchor. Used for polynomial reproduction; no common radius there.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Lattice Labels Source Source.Drops RG Work.G02 MeasureTheory
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d j k : ℕ}

def seat (x : Cover) : E4 := WithLp.toLp 2 fun i => ((x i):ℝ)
@[simp] lemma seat_apply (x : Cover) (i : Axis) : seat x i=((x i):ℝ) := rfl
@[simp] lemma seat_step (i : Axis) : seat (step i)=basis i := by ext a; simp
@[simp] lemma seat_add (x y : Cover) : seat (x+y) = seat x + seat y := by ext a; simp
@[simp] lemma seat_zero : seat 0=0 := by ext a; simp

/-- Coefficients of the polynomial input profile on a link. -/
abbrev Route (G : Gauge) (d : ℕ) := (i : Fin (d-1)) → Slices (i.val+1) → G.Color

def signal (v : Route G d) (t : ℝ) : G.Color := ∑ i : Fin (d-1), ∑ s, t^(away s) • v i s

/-- Feed one actual positive oriented link, with initial E4 position in
lattice units. -/
def road (x : E4) (i : Axis) : Snap G d →L[ℝ] Route G d :=
    LinearMap.toContinuousLinearMap {
      toFun A m s := forSlice ((A m).val i) s x (basis i)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

lemma represented_signal (p : Edge Cover) (A : Snap G d) (t : ℝ) :
    signal (road (seat p.1) p.2 A) t = partConnection d (expand d A) 1 p t := by
  unfold signal partConnection; simp only [one_smul,potential,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro i _
  rw [expand,dif_pos i.isLt]
  exact (slice_diagonal ((A i).val p.2) (seat p.1) (basis p.2) t).symm

lemma signal_smooth (v : Route G d) (n : WithTop ℕ∞) : ContDiff ℝ n (signal v) := by
  unfold signal; fun_prop

lemma signal_add (v w : Route G d) (s : ℝ) : signal (v+w) s = signal v s + signal w s := by simp [signal,smul_add,Finset.sum_add_distrib]
lemma signal_smul (v : Route G d) (c s : ℝ) : signal (c•v) s = c•signal v s := by simp [signal,Finset.smul_sum,smul_comm c]

lemma road_band (i : Fin (d-1)) (A : Taylor G i.val) (e : Axis) :
    (fun x : E4 => road x e (Pi.single i A)) ∈ rangeLt (Route G d) (i.val+2) := by
  apply vector_band; intro j; apply vector_band; intro s
  change (fun x => forSlice (((Pi.single i A : Snap G d) j).val e) s x (basis e))∈ _
  by_cases h : j=i
  · subst j; simp_rw [Pi.single_eq_same]
    apply exact_le_band _ (forSlice_home _ _ _); have hh := covers s; omega
  simp only [Pi.single_eq_of_ne h]; apply Submodule.zero_mem

private def damp (b : Slices j) : ℝ := ∫ s : ℝ in 0..1, s^(away b)

/-- Average profile, with the convention of `access` on initial vertices. -/
def steady (v : Route G d) := ∑ i : Fin (d-1), ∑ b, damp b • v i b
lemma steady_eq (v : Route G d) : steady v = ∫ s : ℝ in 0..1, signal v s := by
  have he (i : Fin (d-1)) (b : Slices (i.val+1)) : Continuous fun t : ℝ => t^(away b) • v i b := by fun_prop
  unfold steady signal
  rw [intervalIntegral.integral_finsetSum (by intros; apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl; intro i _
  rw [intervalIntegral.integral_finsetSum (fun b _ => (he _ b).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl; intro b _; rw [damp, intervalIntegral.integral_smul_const]

abbrev Potential (G : Gauge) := E4 → Axis → G.Color

def radialValue (A : Taylor G j) : Potential G := fun x i => A.value i x


/-- Link variation (zero-order transports and log derivative at the identity
will be related below). -/
def variation (A : Taylor G j) : Potential G := fun x i =>
    ∑ b : Slices (j+1), damp b • forSlice (A.val i) b x (basis i)

lemma variation_cost (A : Taylor G j) : variation A - radialValue A ∈ rangeLt (Axis → G.Color) (j+1) := by
  classical
  apply vector_band; intro i
  let M := A.val i
  let p (b : Slices (j+1)) (x : E4) := if away b=0 then 0 else damp b • forSlice M b x (basis i)
  have he : (fun x : E4 => (variation A - radialValue A) x i)=∑ b:Slices (j+1),p b := by
    funext x
    rw [Finset.sum_apply]; change ∑ b:Slices (j+1), _ - Tensor.diagonal M x= _
    rw [slice_center M x (basis i),← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _; by_cases h : away b=0 <;> simp [p,h,damp,M]
  rw [he]; apply Submodule.sum_mem; intro b _
  by_cases h : away b=0
  · unfold p; simp [h,show (fun _ : E4 => (0:G.Color))=0 from rfl]
  unfold p; simp only [if_neg h]; exact Submodule.smul_mem _ (damp b)
    (exact_le_band (by have := covers b; omega) (forSlice_home M b _))

lemma steady_slot (i : Fin (d-1)) (x : E4) (e : Axis) (v : Taylor G i.val) :
    steady (road x e (Pi.single i v))=variation v x e := by
  unfold steady; rw [Finset.sum_eq_single i]
  · unfold variation; refine Finset.sum_congr rfl fun b _ => ?_
    change damp b • forSlice (((Pi.single i v : Snap G d) i).val e) b x _ = _
    rw [Pi.single_eq_same]
  · intro j h hw
    refine Finset.sum_eq_zero fun b hb => ?_
    change damp b • forSlice (((Pi.single i v : Snap G d) j).val e) b x _ = _
    rw [Pi.single_eq_of_ne hw]; apply smul_zero
  simp

/-! The real group ODE gates. Only this local polynomial parameter.
G.Color is the actual Lie space with actual exp; derivative statement
is on its specified norm, *before* any approximation or continuum limits.
-/

def flight (v : Route G d) := (Hol.pipes (signal_smooth v 1)).choose
lemma flight_path (v : Route G d) : SolvesLink (flight v) (signal v) :=
    (Hol.pipes (signal_smooth v 1)).choose_spec

lemma flight_test (H : Hol G) (p : Edge Cover) (A : Snap G d) : flight (road (seat p.1) p.2 A) = H.flow d (expand d A) 1 p := by
  have he := flight_path (road (seat p.1) p.2 A)
  rw [funext (represented_signal p A)] at he
  exact he.unique (H.solves ..)

lemma arrival (G : Gauge) (d : ℕ) : let g (X : Route G d) := G.mat (flight X 1)
    AnalyticAt ℝ g 0 ∧ g 0=1 ∧ ∀ X, HasDerivAt (fun t : ℝ => g (t • X)) (G.colorMat (steady X)) 0 := by
  intro g
  let L : Route G d →ₗ[ℝ] (ℝ → G.Mat) := {
    toFun X s := G.colorMat (signal X s)
    map_add' X Y := by ext1; simp [signal_add]
    map_smul' r X := by ext1; simp [signal_smul] }
  obtain ⟨h,h0,hJ⟩ := endpointGerm L
    (fun X => G.colorMat.continuous_of_finiteDimensional.comp (signal_smooth X 1).continuous)
    (fun X s => G.mat (flight X s)) (fun X => by rw [(flight_path X).1]; rfl) (fun X t => (flight_path X).2 t)
  refine ⟨h,h0,fun X => ?_⟩; apply (hJ X).congr_deriv
  rw [steady_eq]; exact G.colorMat.toContinuousLinearMap.intervalIntegral_comp_comm ((signal_smooth X 1).continuous.intervalIntegrable 0 1)

lemma no_flight (G : Gauge) (d : ℕ) : flight (0 : Route G d) 1=1 :=
    G.mat_injective (arrival G d).2.1

end YM.Planned.PrimaryIntegral295.Place
