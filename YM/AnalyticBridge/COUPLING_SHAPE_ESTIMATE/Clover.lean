import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Plane
import YM.Push.STRESS_FLUX.Clover
import YM.Push.STRESS_FLUX.Low
import YM.Work.F03.Transport



/-!
# Anchors, rotations and the signed four-plaquette Hessian witness, 

Positive pairs only in the Flux index. Visits, rotations and norms are on the
actual finite torus, using a nonwrapping hypothesis just for the affine test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Lattice Wilson Filter Function Exterior RG StressFlux Work
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n : Side}

def ringlet (o : Site n) := halo 1 {o}
lemma central (o : Site n) : o ∈ ringlet o := halo_subset _ _ (Finset.mem_singleton_self _)
lemma unwound (hn : 10 < n.val) (o : Site n) : Nonwrapping (ringlet o) o := by
  intro x hx; have h : separation x o ≤ 1 := by simpa [halo_spec,ringlet,separation_comm x o] using hx
  omega

lemma ringlet_turn (s : Signed) (z o : Site n) : ringlet (affine s z o) = (ringlet o).image (affine s z) := by
  ext i
  obtain ⟨j,rfl⟩ := (show Equiv.Perm (Site n) from s.actEquiv.toEquiv.trans (Equiv.addRight z)).surjective i
  change affine s z j ∈ _ ↔ affine s z j ∈ _
  have he : Injective (affine s z) := fun _ _ h => s.act_injective (add_right_cancel h)
  simp only [Finset.mem_image,he.eq_iff,exists_eq_right]; simp [ringlet,halo_spec,affine]

lemma visits_leaf (o : Site n) (a b : Step) : (visits o (Lattice.oriented a b)).toFinset=
    {o,o+a.vec,o+b.vec,o+a.vec+b.vec} := by
  simp only [visits,Lattice.oriented,Step.vec_rev,show o+a.vec+b.vec+ -a.vec=o+b.vec by abel, add_neg_cancel_right]
  ext; simp; tauto

lemma shift_leaf (o : Site n) (a b : Step) : (visits o (Lattice.oriented a b)).toFinset=
    (visits (atFace o a b) (square a.dir b.dir)).toFinset := by
  change _=(visits _ (Lattice.oriented (posDir a.dir) (posDir b.dir))).toFinset
  rw [visits_leaf,visits_leaf]; ext i; cases ha : a.neg <;> cases hb : b.neg <;>
    simp [atFace,Step.vec,ha,hb, posDir] <;> abel_nf <;> tauto

lemma neighbors (o : Site n) (a b : Step) (he : a.dir≠b.dir) :
    (visits o (Lattice.oriented a b)).toFinset ⊆ ringlet o := by
  have hx (c : Step) : separation o (o+c.vec) ≤ 1 := by
    rw [separation_comm,separation,add_comm o,add_sub_cancel_right,Step.vec]
    split
    · rw [pdist_neg]; apply pdist_step
    apply pdist_step
  intro x hh
  refine halo_spec.mpr ⟨o,Finset.mem_singleton_self _,?_⟩
  rw [visits_leaf] at hh; simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with rfl|rfl|rfl|rfl
  · simp
  · exact hx a
  · exact hx b
  rw [separation_comm,separation,add_assoc,add_comm o,add_sub_cancel_right,←wrap_vec n,←wrap_vec n,←map_add]
  apply Finset.sup_le; intro i _; refine (Corona.lap _ _).trans ?_
  cases H : a.neg <;> cases H' : b.neg <;> simp only [Step.vec,H,H',Bool.false_eq_true, ↓reduceIte, Pi.neg_apply,Pi.add_apply,step_apply]
    <;> split_ifs <;> first | omega | (subst_eqs; contradiction)

lemma local_square (F : Face (Per n)) : touched F ⊆ ringlet F.1 := neighbors F.1 (posDir _) (posDir _) F.2.property.ne

lemma local_chord {t : ℝ} {X : Support n} {U : Config G n} (h : Healthy t X U) (F : Face (Per n)) (hh : F.1 ∈ X) :
    G.chord (faceValue U F) ≤ t := by
  by_contra! he; exact Finset.disjoint_left.mp h hh ((flags_spec ..).mpr ⟨F,by simp [touched,square,visits],he⟩)

lemma chord_leaf (o : Site n) {t : ℝ} {U : Config G n} (a b : Step) (h : a.dir < b.dir) (ht : Healthy t (ringlet o) U) :
    G.chord (travel U o (Lattice.oriented a b)) ≤ t := by
  rw [price_shift_pos G.chord U G.chord_inv (fun k g => G.chord_conj g k)]
  refine local_chord ht (atFace o a b,⟨(a.dir,b.dir),h⟩) ?_
  refine neighbors o a b h.ne ?_
  rw [shift_leaf]; change atFace o a b∈_; simp [square,visits]

def windDir (A : Directions G n) : fieldDir G n 1 := fun i => A (i.1, axisEquiv.symm i.2)
lemma collect_wind (A : Directions G n) : collect G (windDir A)=A := by
  funext; simp only [windDir,collect,← coord_map, Equiv.symm_apply_apply]


lemma curl_square (hn : 2≤n.val) {X : Support n} {o : Site n} (hx : Nonwrapping X o) {A : Directions G n}
    {c d} (hA : OnStencil o X c d A) (y : Site n) (i : PlaqAxes) (hy : touched (y,i)⊆X) :
    linkSum A y (square i.val.1 i.val.2) = skew d i := by
  let a:=i.val.1; let b:=i.val.2
  have hh : {y,y+step a,y+step b,y+step a+step b} ⊆ X := visits_leaf y (posDir a) (posDir b) ▸ hy
  have hx1 : y∈X:=hh (by simp); have hx2 : y+step a∈X := hh (by simp); have hx3 : y+step b∈X := hh (by simp)
  have hx4 : y+step a+step b∈X := hh (by simp)
  change linkSum A y (square a b)=_
  have he : linkSum A y (square a b)=A (y,a)+A (y+step a,b)-A (y+step b,a)-A (y,b) := by
    simp [square,linkSum,posDir,negDir,Step.used,Step.vec,show y+step a+step b-step a=y+step b by abel,←sub_eq_add_neg]; abel
  rw [he,hA y hx1 a hx2,hA _ hx2 b hx4,hA y hx1 b hx3,hA _ hx3 a (by rw [add_right_comm]; exact hx4)]
  simp only [profile,Next.Foundations.lift_end hn hx y hx1,slide_plus,slide_step,skew]
  dsimp only [a,b]; abel

lemma linear_leaf (o : Site n) (a b : Step) (A : Directions G n) :
    linkSum A o (Lattice.oriented a b) = (flag a * flag b) • linkSum A (atFace o a b) (square a.dir b.dir) := by
  rcases a with ⟨a,h|h⟩ <;> rcases b with ⟨b,t|t⟩ <;>
    simp [Lattice.oriented,square, atFace,flag,posDir,negDir,Step.rev,Step.vec,Step.used,linkSum,add_right_comm o,sub_eq_add_neg] <;> abel_nf

lemma leaf_derivative (o : Site n) {X : Support n} (hn : 2 ≤ n.val) (hx : Nonwrapping X o) {A : Directions G n} {c d}
    (h : OnStencil o X c d A) (hg : ringlet o ⊆ X) (a b : Step) (ha : a.dir < b.dir) :
    HasDerivAt (fun t : ℝ => plate (increment 1 (t • A)) o a b)
      ((flag a * flag b) • skew d ⟨(a.dir,b.dir),ha⟩) 0 := by
  have hv := curvature_linear G (windDir A) o (Lattice.oriented a b)
  rw [collect_wind, linear_leaf o a b A,
    show linkSum _ _ (square a.dir b.dir)=_ from curl_square hn hx h _ ⟨(a.dir,b.dir),ha⟩ (by
      change (visits _ (square a.dir b.dir)).toFinset ⊆ X
      rw [← shift_leaf]; exact (neighbors o a b ha.ne).trans hg)] at hv
  exact F03.curvature_of_hasDerivAt hv

def needles (o : Site n) (U : Config G n) : Flux G := fun i => clover U o i.1.1 i.1.2

lemma needles_mono (o : Site n) (u : Site n → G.El) (U : Config G n) :
    needles o (gauge u U)=fun i => G.adjoint (u o) (needles o U i) := funext fun _ => clover_gauge ..

lemma clover_zero (o : Site n) : needles (G:=G) o 1=0 := by
  funext i; simp [needles,clover,stencil,plate,travel,Lattice.oriented]

lemma clover_jet (o : Site n) {X : Support n} (hn : 2 ≤ n.val) (hx : Nonwrapping X o) {A : Directions G n} {c d}
    (h : OnStencil o X c d A) (hg : ringlet o ⊆ X) : HasDerivAt (fun t : ℝ => needles o (increment 1 (t • A))) (skew d) 0 := by
  refine (hasDerivAt_pi ..).mpr fun i => ?_
  let a:=i.1.1; let b:=i.1.2
  have ht (e f : Step) (he : e.dir=a) (hf : f.dir=b) :
      HasDerivAt (fun t : ℝ => plate (increment 1 (t • A)) o e f) ((flag e * flag f) • skew d i) 0 := by
    have hh := leaf_derivative _ hn hx h hg e f (by rw [he,hf]; exact i.property)
    convert hh using 2
    simp only [skew,he,hf,a,b]
  refine ((((ht (posDir a) (posDir b) rfl rfl).sub (ht (posDir a) (negDir b) rfl rfl)).sub
    ((ht (negDir a) (posDir b) rfl rfl).sub (ht (negDir a) (negDir b) rfl rfl))).const_smul ((4:ℝ)⁻¹)).congr_deriv ?_
  simp [flag,posDir,negDir]; module

end YM.AnalyticBridge.CouplingShape
