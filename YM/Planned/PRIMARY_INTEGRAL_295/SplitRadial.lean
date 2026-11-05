import YM.Planned.PRIMARY_INTEGRAL_295.Route

/-!
# Spanning the polynomial tests by linear radial/gauge variations

This is only a statement about ordinary (logarithmic)
link directions.

The next calculus has to account for the *higher* jets
of this same substitution; reading off just the coefficient of h in a
nonlinear composition wouldn't imply flat cancellation.

Here V_a has
exactly the position degree <a; for a=d include *all* slots through d.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Lattice Labels Source Source.Drops RG WardBin MeasureTheory
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d j a b : ℕ}

/-- Negative discrete derivative, i.e. input `u^-` + transport − `u^+`. -/
def jump (f : E4 → G.Color) : Potential G := fun x i => f x - f (x+basis i)

lemma jump_add (f g : E4 → G.Color) : jump (f+g)=jump f+jump g := by
  ext1 x; ext1 i; simp only [jump,Pi.add_apply]; abel
@[simp] lemma jump_zero : jump (0:E4 → G.Color)=0 := funext fun _ => funext fun _ => sub_self (0:G.Color)

def descent (f : E4 → G.Color) : Potential G := fun x i => fderiv ℝ f x (basis i)
lemma jump_band {f : E4 → G.Color} (h : f ∈ rangeLt G.Color (j+1)) : jump f ∈ rangeLt (Axis → G.Color) j := by
  apply vector_band; intro i
  change (fun x => f x - f (x+basis i)) ∈ _
  rw [show (fun x : E4 => f x-f (x+basis i)) = -(fun x => f (x+basis i)-f x) by
    ext1; simp]
  exact Submodule.neg_mem _ (band_step h _)

lemma jump_descent {f : E4 → G.Color} (h : f ∈ exactDegree G.Color (j+1)) :
    jump f+descent f ∈ rangeLt (Axis → G.Color) j ∧ descent f ∈ exactDegree (Axis → G.Color) j := by
  constructor; swap; · exact vector_pure (fun i x => descent f x i) fun i => pure_direction h _
  apply vector_band; intro i
  rw [show (fun x : E4 => (jump f+descent f) x i)=-(fun x : E4 => f (x+basis i) - f x - fderiv ℝ f x (basis i)) from
    funext fun x => by simp only [jump,descent,Pi.add_apply,Pi.neg_apply]; abel]
  exact Submodule.neg_mem _ (pure_tangent_step h _)

def throughSlot (X : Snap G d) (a : ℕ) : Prop := ∀ i : Fin (d-1), a < i.val+2 → X i=0

-- Combine all through lower weights; map remains linear even if
-- some slots of that generation have no invariants.
def sampled (X : Snap G d) : Potential G := fun x i => steady (road x i X)

lemma steady_zero : steady (0 : Route G d)=0 := by simp [steady]
lemma steady_add (X Y : Route G d) : steady (X+Y)=steady X+steady Y := by
  simp [steady,smul_add,Finset.sum_add_distrib]

@[simp] lemma sampled_zero : sampled (0 : Snap G d)=0 := by
  funext x i; rw [sampled,map_zero,steady_zero]; rfl
lemma sampled_add (X Y : Snap G d) : sampled (X+Y)=sampled X+sampled Y :=
  funext fun x => funext fun i => by simp [sampled,steady_add]
lemma sampled_slot (i : Fin (d-1)) (A : Taylor G i.val) : sampled (Pi.single i A)=variation A :=
    funext fun x => funext fun e => steady_slot i x e A

lemma rations (X : Snap G d) (hX : throughSlot X a) (i : Axis) :
    (fun x => road x i X) ∈ rangeLt (Route G d) a := by
  classical
  let Q j x := road x i (Pi.single j (X j))
  have he : (fun x => road x i X)=∑ j:Fin (d-1), Q j := by
    funext x; rw [Finset.sum_apply]
    unfold Q; rw [← map_sum, Finset.univ_sum_single]
  rw [he]; apply Submodule.sum_mem; intro j _
  by_cases h : a < j.val+2
  · have hz : Q j=0 := funext fun x => by unfold Q; rw [hX j h, Pi.single_zero,map_zero]; rfl
    rw [hz]; apply Submodule.zero_mem
  exact grows _ (le_of_not_gt h) (road_band j (X j) i)

private def prime {G : Gauge} (x : Potential G) (j : ℕ) (z : E4) :=
    (-(((j+1 : ℕ) : ℝ)⁻¹)) • ∑ i : Axis, z i • x z i

private lemma prime_grade {f : Potential G} (h : f ∈ exactDegree (Axis → G.Color) j) :
    prime f j ∈ exactDegree G.Color (j+1) := by
  have he (i : Axis) : (fun z : E4 => z i • f z i) ∈ exactDegree G.Color (j+1) := by
    have hF : (fun z => f z i) ∈ exactDegree G.Color j := linear_pure (ContinuousLinearMap.proj i) h
    apply exact_of_smooth; swap
    · intro z t
      rw [exact_scale h, pow_succ']; change (t*z i) • (t^j • f z i) = _
      rw [smul_smul,smul_smul]; congr 1; ring
    have ht : ContDiffAt ℝ (↑(j+1):WithTop ℕ∞) (fun z => f z i) 0 := (exact_smooth hF _).contDiffAt
    have hg : ContDiffAt ℝ (↑(j+1):WithTop ℕ∞) (fun z : E4 => z i) 0 := by fun_prop
    exact hg.smul ht
  have h1 : (fun z : E4 => ∑ i : Axis, z i • f z i) ∈ exactDegree G.Color (j+1) := by
    rw [show (fun z : E4 => ∑ i : Axis, z i • f z i) = ∑ i : Axis, fun z : E4 => z i • f z i by
      funext _; rw [Finset.sum_apply]]
    exact Submodule.sum_mem _ (fun i _ => he i)
  exact Submodule.smul_mem _ _ h1

private lemma radial_split {f : Potential G} (h : f ∈ exactDegree (Axis → G.Color) j) :
    let v := prime f j
    let R := f+descent v
    R ∈ exactDegree (Axis → G.Color) j ∧ ∀ z : E4, ∑ i, z i • R z i=0 := by
  classical
  intro v R
  have hv : v ∈ exactDegree G.Color (j+1) := prime_grade h
  refine ⟨Submodule.add_mem _ h (jump_descent hv).2,fun z => ?_⟩
  have hD : ∑ i : Axis, z i • descent v z i=fderiv ℝ v z z := by
    have ht : ∑ i : Axis, z i • basis i=z := by ext i; simp
    conv_rhs => rhs; rw [← ht]
    simp [descent]
  have hE : fderiv ℝ v z z=((j+1 : ℕ) : ℝ) • v z := by
    obtain ⟨A,hA,he⟩ := pure_sym hv
    rw [he]; exact Tensor.Euler A hA z
  change ∑ i : Axis,z i • (f z i +descent v z i)=0
  simp only [smul_add, Finset.sum_add_distrib,hD,hE]; unfold v prime
  rw [smul_smul,mul_neg,mul_inv_cancel₀ (by positivity),neg_smul,one_smul]; abel

private lemma at_grade {f : Potential G} (h : f ∈ exactDegree (Axis → G.Color) j) (hi : j+1 ≤ d) :
    let v := prime f j
    ∃ Z : Snap G d, throughSlot Z (j+1) ∧ f-jump v - sampled Z ∈ rangeLt (Axis → G.Color) j := by
  classical
  intro v
  let R := f+descent v
  have hp := prime_grade h
  have H : R∈exactDegree (Axis→G.Color) j ∧ ∀ z : E4,∑ i,z i • R z i=0 := radial_split h
  have hT := jump_descent hp
  have W (Z : Snap G d) (hz : sampled Z - R ∈ rangeLt (Axis→G.Color) j) : f-jump v -sampled Z ∈ rangeLt (Axis→G.Color) j := by
    rw [show f-jump v -sampled Z=-(jump v+descent v)-(sampled Z-R) by unfold R; abel]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hT.1) hz
  have hs := H.1; have ht := H.2
  clear h hp hT H
  cases j with
  | zero =>
    refine ⟨0,fun _ _ => rfl, W 0 ?_⟩
    have Hroc (x y : E4) : R x=R y := by
      have he (x : E4) : R 0=R x := by simpa using exact_scale hs x 0
      exact (he _).symm.trans (he _)
    have he (x : E4) (i : Axis) : R x i=0 := by rw [Hroc x (basis i)]; simpa using ht (basis i)
    rw [show R=0 from funext fun x => funext (he x),sampled_zero, sub_zero]; exact Submodule.zero_mem _
  | succ j =>
    choose T hS hT using fun i : Axis => pure_sym (f:=fun z : E4 => R z i) (linear_pure (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Axis => G.Color) i) hs)
    let X : Taylor G j := ⟨T,hS,fun z => by simpa only [fun i => congr_fun (hT i) z] using ht z⟩
    have hx : R=radialValue X := funext fun z => funext fun i => congr_fun (hT i) z
    let m : Fin (d-1) := ⟨j,by omega⟩
    refine ⟨Pi.single m X,?_, W _ ?_⟩
    · intro i hi
      have he : i≠m := fun h => by rw [h] at hi; simp [m] at hi
      simp only [Pi.single_eq_of_ne he]
    rw [hx,sampled_slot]; exact variation_cost _

/-- Every polynomial log-link direction required at weight `a≤d` is
generated by the linear parts of the *same* Snap holonomy and site
gauges. The node logarithms use degree **≤** a. The edge log directions
use degree **<** a. , including positive/negative signs
on the variation. Also when `a=1,d≤1`, no radial slots. -/
theorem generated (f : Potential G) (hf : f ∈ rangeLt (Axis → G.Color) a) (h : a ≤ d) :
    ∃ (w : E4 → G.Color) (X : Snap G d), w ∈ rangeLt G.Color (a+1) ∧ throughSlot X a ∧ f=jump w+sampled X := by
  classical
  induction a generalizing f with
  | zero =>
    rw [rangeLt,Submodule.mem_bot] at hf; rw [hf]; exact ⟨0,0,Submodule.zero_mem _,fun _ _ => rfl,by simp⟩
  | succ a ih =>
    rw [rangeLt_succ] at hf
    obtain ⟨p,hp,q,hq,rfl⟩ := Submodule.mem_sup.mp hf
    let v := prime p a
    obtain ⟨Z,hZ,hx⟩ := at_grade hp h
    have hu := Submodule.add_mem _ hx hq
    obtain ⟨w,W,hw,hW,he⟩ := ih (_ + q) hu (by omega)
    refine ⟨v+w,Z+W,Submodule.add_mem _ (exact_le_band (by omega) (prime_grade hp))
      (grows _ (Nat.le_succ _) hw),fun i hi => ?_,?_⟩
    · simp [hZ i hi, hW i (by omega : a < i.val+2)]
    rw [jump_add,sampled_add, show jump v + jump w + (sampled Z + sampled W) = jump v+sampled Z+(jump w+sampled W) by abel,← he]; unfold v; abel

end YM.Planned.PrimaryIntegral295.Place
