import YM.Next.EXTRACTION.Tails

/-! Exact first variation of the physical Wilson energy on a torus, in left Lie components
*as read at the specified oriented link*. E eq. (jhaar) convention, probability-Haar base,
no coupling folded into `force`. This works at all periods including tiny/wrapping ones by
counting occurrences. Color = physical HS normalization. No small-field assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Set Filter Gauge Lattice Wilson MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace

variable {G : Gauge} {n : Side}

section Trace
attribute [local instance] Gauge.frobInner
lemma price_direction (g : G.El) (c : G.Color) : - (G.colorMat c * G.mat g).trace.re / G.repDim = ⟪c,G.curvature g⟫_ℝ := by
  let P := (1/2 : ℝ) • (G.mat g - G.mat g⁻¹)
  let X := G.colorMat c
  have he := Submodule.starProjection_inner_eq_zero P (G.colorMat c) (G.colorMat_mem c)
  rw [inner_sub_left, ← G.colorMat_project] at he
  change (P * star X).trace.re - (G.colorMat (G.curvature g) * star X).trace.re = 0 at he
  rw [show star X = -X from G.colorMat_skew c,mul_neg,mul_neg,Matrix.trace_neg, Matrix.trace_neg, Complex.neg_re,Complex.neg_re,
    show - (G.colorMat (G.curvature g)*X).trace.re = _ from G.trace_color _ c, real_inner_comm c] at he
  have hi : (G.mat g⁻¹ * X).trace.re = -(X * G.mat g).trace.re := by
    have ht : (star (X*G.mat g)).trace.re = (X*G.mat g).trace.re := by rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]; rfl
    rw [← ht,star_mul,show star X = -X from G.colorMat_skew c,G.mat_inv]; simp
  have hP : (P*X).trace.re=(X*G.mat g).trace.re := by simp [P,sub_mul,-Gauge.mat_inv,Matrix.trace_mul_comm (G.mat g),hi]; ring
  rw [hP] at he; rw [div_eq_iff (by exact_mod_cast G.dimPos.ne')]; unfold X at he; linarith

private lemma twice_price (c d : G.Color) (g h : G.El) :
    HasDerivAt (fun t : ℝ => G.price (G.lieExp (t • c) * g * (G.lieExp (t • d))⁻¹ * h))
      (⟪c,G.curvature (g*h)⟫_ℝ - ⟪d,G.curvature (h*g)⟫_ℝ) 0 := by
  let L := Complex.reCLM ∘L (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap
  have hd (x : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • x))) (G.colorMat x) 0 := by
    simp_rw [G.mat_lieExp, map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
  have he := (((L.hasFDerivAt.comp_hasDerivAt 0 ((((hd c).mul_const (G.mat g)).mul (hd d).star).mul_const (G.mat h))).div_const G.repDim).const_sub 1)
  apply he.congr_deriv
  symm
  simp only [← neg_div]
  change _ = - ((G.colorMat c * G.mat g * star (G.mat (G.lieExp ((0:ℝ) • d))) + G.mat (G.lieExp ((0:ℝ) • c)) * G.mat g * star (G.colorMat d)) * G.mat h).trace.re / _
  rw [← price_direction, ← price_direction]
  simp only [zero_smul, G.mat_lieExp_zero,G.mat_one,star_one,mul_one,one_mul,G.colorMat_skew, mul_neg, neg_mul,add_mul,G.mat_mul,Matrix.trace_add,Matrix.trace_neg,Complex.add_re,Complex.neg_re]
  rw [Matrix.mul_assoc, Matrix.trace_mul_cycle _ _ (G.mat h), Matrix.trace_mul_comm (G.mat h * G.mat g)]
  ring
end Trace

section Cover
variable {R : Type*} [AddCommGroup R] [One R]

def plate (U : Links R G.El) (x : Four R) (a b : Step) := G.curvature (travel U x (Lattice.oriented a b))
private abbrev transverse (a : Axis) : Finset Axis := Finset.univ.erase a

def force (U : Links R G.El) (x : Four R) (d : Step) : G.Color := ∑ i ∈ transverse d.dir,
    (plate U x d (posDir i) + plate U x d (negDir i))

lemma plate_swap (U : Links R G.El) (x : Four R) (d f : Step) : plate U x d f = -plate U x f d := by
  unfold plate; rw [oriented_swap f d,G.curvature_inv]
@[simp] lemma plate_rev (U : Links R G.El) (x : Four R) (a b : Step) : plate U (x+a.vec) a.rev b = - G.adjoint (a.read U x)⁻¹ (plate U x a b) := by
  rw [plate_swap U (x+a.vec)]; unfold plate; rw [oriented_next, ← G.curvature_conjugate, inv_inv]




lemma plate_pull (s : Signed) (z : Four R) (U : Links R G.El) (x : Four R) (d b : Step) :
    plate (pull s z U) x d b = plate U (affine s z x) (d.rotate s) (b.rotate s) := by
  unfold plate; rw [travel_pull]; simp [Lattice.oriented, Step.rev_rotate]


lemma plate_gauge (t : Four R → G.El) (U : Links R G.El) (x : Four R) (a b : Step) : plate (gauge t U) x a b = G.adjoint (t x) (plate U x a b) := by
  simp [plate, travel_gauge,G.curvature_conjugate]


/-- Signed site filter. Transforms as a polar vector in the spacetime index. -/
def siteForce (U : Links R G.El) (x : Four R) (i : Axis) := (2:ℝ)⁻¹ • (force U x (posDir i) - force U x (negDir i))



@[fun_prop] lemma plate_cont (x : Four R) (d b : Step) : Continuous (fun U : Links R G.El => plate U x d b) := by unfold plate; fun_prop
@[fun_prop] lemma force_cont (x : Four R) (d : Step) : Continuous (fun U : Links R G.El => force U x d) := by unfold force; fun_prop



end Cover

section Variation

def modify (x : Site n) (d : Step) (g : G.El) (U : Config G n) : Config G n := fun e => if e=d.used x then
  if d.neg then U e * g⁻¹ else g * U e else U e

def bump (x : Site n) (d : Step) (c : G.Color) (t : ℝ) := modify x d (G.lieExp (t • c))

lemma read_modify (x : Site n) (d : Step) (g : G.El) (U : Config G n) (y : Site n) :
    d.read (modify x d g U) y = (if y=x then g else 1) * d.read U y := by
  unfold Step.read Step.used; split <;> simp [modify,Step.used, *,ite_mul,apply_ite Inv.inv]

lemma read_modify_other (x : Site n) (d : Step) (g : G.El) (U : Config G n) (y : Site n) {b : Step} (h : b.dir ≠ d.dir) :
    b.read (modify x d g U) y=b.read U y := by
  have ht : b.used y ≠ d.used x := fun he => h (show b.dir=d.dir by simpa [Step.used,apply_ite Prod.snd] using congr_arg Prod.snd he)
  unfold Step.read modify; rw [if_neg ht]

lemma bump_face (x : Site n) (d : Step) (c : G.Color) (U : Config G n) (y : Site n) (b : Step) (hb : b.dir ≠ d.dir) :
    HasDerivAt (fun t : ℝ => G.price (travel (bump x d c t U) y (Lattice.oriented d b)))
    ((if y=x then ⟪c,plate U x d b⟫_ℝ else 0) + (if y+b.vec=x then ⟪c,plate U x d b.rev⟫_ℝ else 0)) 0 := by
  let g := d.read U y * b.read U (y+d.vec) * (d.read U (y+b.vec))⁻¹
  let h := (b.read U y)⁻¹
  have circ (V : Config G n) (a b : Step) (z : Site n) : travel V z (Lattice.oriented a b) =
      a.read V z * b.read V (z+a.vec) * (a.read V (z+b.vec))⁻¹ * (b.read V z)⁻¹ := by
    rw [Lattice.oriented]; simp only [travel,mul_one]; rw [Step.vec_rev,show z+a.vec+b.vec+-a.vec=z+b.vec by abel,
      Step.read_rev,add_right_comm z a.vec b.vec,Step.read_rev]; group
  let A (y : Site n) := if y=x then c else 0
  have he (y) (t:ℝ) : (if y=x then G.lieExp (t • c) else (1:G.El)) = G.lieExp (t • A y) := by unfold A; split <;> simp
  have hf (t) : travel (bump x d c t U) y (Lattice.oriented d b) =
      G.lieExp (t • A y) * g * (G.lieExp (t • A (y+b.vec)))⁻¹ * h := by simp [g,h,circ, bump, read_modify x d, read_modify_other x d _ U _ hb, he,mul_assoc]
  have hgh : plate U y d b=G.curvature (g*h) := by rw [plate,circ]
  have hhg : plate U (y+b.vec) d b.rev = -G.curvature (h*g) := by
    rw [plate,oriented_swap b.rev d,circ,G.curvature_inv]; congr 2
    rw [Step.read_rev,Step.vec_rev,add_neg_cancel_right,add_right_comm y b.vec d.vec,Step.read_rev,inv_inv]; unfold g h; group
  simp_rw [hf]
  apply (twice_price ..).congr_deriv
  dsimp only [A]; rw [← hgh, ← neg_eq_iff_eq_neg.mpr hhg]
  split_ifs <;> simp [*]
  rename_i hy hw; rw [← hy,hw,hy]

private lemma active_faces (d : Axis) (f : PlaqAxes → ℝ) :
    ∑ i ∈ transverse d, (if h : i=d then 0 else f (PlaqAxes.ordered i d h)) =
      ∑ p : PlaqAxes with (d=p.val.1 ∨ d=p.val.2), f p := by
  refine Finset.sum_bij (fun i hi => PlaqAxes.ordered i d (Finset.mem_erase.mp hi).1) ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; change d=min i d ∨ d=max i d
    rcases le_total i d with h|h <;> simp [h]
  · intro i hi j hj he
    have h₁ : min i d=min j d := congr_arg (fun p => p.val.1) he
    have h₂ : max i d=max j d := congr_arg (fun p => p.val.2) he
    grind
  · rintro ⟨⟨a,b⟩,hp⟩ hb
    obtain h|h := (Finset.mem_filter.mp hb).2
    · change d=a at h; subst d; refine ⟨b,Finset.mem_erase.mpr ⟨Ne.symm hp.ne, Finset.mem_univ _⟩, Subtype.ext ?_⟩; simp [PlaqAxes.ordered,hp.le]
    change d=b at h; subst d; refine ⟨a,Finset.mem_erase.mpr ⟨hp.ne, Finset.mem_univ _⟩,Subtype.ext ?_⟩; simp [PlaqAxes.ordered, hp.le]
  intro i hi; rw [dif_neg (Finset.ne_of_mem_erase hi)]

private lemma expand_action (d : Step) (U : Config G n) : energy U =
    (∑ y, ∑ i ∈ transverse d.dir, G.price (travel U y (Lattice.oriented d (posDir i)))) +
    ∑ y, ∑ p : PlaqAxes with ¬ (d.dir=p.val.1 ∨ d.dir=p.val.2), G.price (faceValue U (y,p)) := by
  rw [energy,Fintype.sum_prod_type]
  let z : Site n := if d.neg then d.vec else 0
  have he (y : Site n) (i : Axis) (h : i≠d.dir) : G.price (travel U y (Lattice.oriented d (posDir i))) = G.price
      (faceValue U (y+z,PlaqAxes.ordered i d.dir h)) := by
    rw [price_shift_pos G.price U G.price_inv (fun g u => G.price_conj u g), show atFace y d (posDir i)=y+z from add_zero _]
    unfold faceValue PlaqAxes.ordered; dsimp only
    rcases lt_or_gt_of_ne h with hh|hh
    · rw [min_eq_left hh.le,max_eq_right hh.le]; change G.price (travel U (y+z) (Lattice.oriented (posDir d.dir) (posDir i))) = _
      rw [oriented_swap,G.price_inv]; rfl
    rw [min_eq_right hh.le,max_eq_left hh.le]; rfl
  have ha (y : Site n) : ∑ i ∈ transverse d.dir, G.price (travel U y (Lattice.oriented d (posDir i))) =
      ∑ p : PlaqAxes with (d.dir=p.val.1 ∨ d.dir=p.val.2), G.price (faceValue U (y+z,p)) := by
    rw [← active_faces]; refine Finset.sum_congr rfl fun i hi => ?_
    have ht := Finset.ne_of_mem_erase hi; rw [dif_neg ht]; apply he
  let f (y : Site n) := ∑ p : PlaqAxes with (d.dir=p.val.1 ∨ d.dir=p.val.2), G.price (faceValue U (y,p))
  simp_rw [ha, show (∑ y, ∑ p : PlaqAxes with (d.dir=p.val.1 ∨ d.dir=p.val.2), G.price (faceValue U (y+z,p))) =
      ∑ y, f y from Equiv.sum_comp (Equiv.addRight z) f]; unfold f; rw [← Finset.sum_add_distrib]; simp_rw [Finset.sum_filter_add_sum_filter_not]

lemma modify_other_face (x : Site n) (d : Step) (g : G.El) (U : Config G n) (y : Site n) (p : PlaqAxes)
    (hp : ¬ (d.dir=p.val.1 ∨ d.dir=p.val.2)) : faceValue (modify x d g U) (y,p) = faceValue U (y,p) := by
  have h₁ : p.val.1 ≠ d.dir := fun he => hp (Or.inl he.symm)
  have h₂ : p.val.2 ≠ d.dir := fun he => hp (Or.inr he.symm)
  simp only [faceValue,square,travel,read_modify_other x d g U _ (b:=posDir p.val.1) h₁,read_modify_other x d g U _ (b:=posDir p.val.2) h₂,
    read_modify_other x d g U _ (b:=negDir p.val.1) h₁,read_modify_other x d g U _ (b:=negDir p.val.2) h₂]

lemma energy_bump_zero (x : Site n) (d : Step) (c : G.Color) (U : Config G n) : HasDerivAt (fun t => energy (bump x d c t U)) ⟪c,force U x d⟫_ℝ 0 := by
  simp_rw [expand_action d]
  have ht := HasDerivAt.fun_sum (u:=Finset.univ) fun y _ => HasDerivAt.fun_sum (u:=transverse d.dir) fun i hi =>
    bump_face x d c U y (posDir i) (Finset.ne_of_mem_erase hi)
  have he (t:ℝ) y := Finset.sum_congr (s₁:={p:PlaqAxes | ¬(d.dir=p.val.1 ∨ d.dir=p.val.2)}) rfl fun p hp => congr_arg G.price (modify_other_face x d (G.lieExp (t • c)) U y p (Finset.mem_filter.mp hp).2)
  unfold bump; simp_rw [he]
  apply (ht.add_const _).congr_deriv
  rw [Finset.sum_comm,force,inner_sum]; apply Finset.sum_congr rfl; intro i _
  simp [Finset.sum_add_distrib,inner_add_right, ← eq_sub_iff_add_eq]

@[simp] theorem bump_zero (x : Site n) (d : Step) (c : G.Color) (U : Config G n) : bump x d c 0 U = U := by funext; simp [bump,modify]
lemma bump_bump (x : Site n) (d : Step) (c : G.Color) (U : Config G n) (t s : ℝ) : bump x d c t (bump x d c s U) = bump x d c (t+s) U := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  have he : G.lieExp ((t+s) • c) = G.lieExp (t • c) * G.lieExp (s • c) := by
    apply G.mat_injective; rw [G.mat_mul,G.mat_lieExp,G.mat_lieExp,G.mat_lieExp,map_smul,map_smul,map_smul,add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat c)).smul_left t).smul_right s)
  funext e; simp +contextual [bump,he, modify,mul_assoc]

lemma bump_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : Site n) (d : Step) (c : G.Color) {U : Config G n}
    {f : Config G n → F} {t : ℝ} {w : F} (h : HasDerivAt (fun s => f (bump x d c s (bump x d c t U))) w 0) :
    HasDerivAt (fun t => f (bump x d c t U)) w t := by
  have ht := (show HasDerivAt (fun s => f (bump x d c s (bump x d c t U))) w (-t+t) by simpa using h).comp_const_add (-t) t
  simpa only [bump_bump, neg_add_cancel_comm] using! ht

lemma energy_variation (x : Site n) (d : Step) (c : G.Color) (t : ℝ) (U : Config G n) :
    HasDerivAt (fun t => energy (bump x d c t U)) ⟪c,force (bump x d c t U) x d⟫_ℝ t := bump_deriv x d c (energy_bump_zero x d c _)
lemma bare_variation (β : ℝ) (x : Site n) (d : Step) (c : G.Color) (t : ℝ) (U : Config G n) :
    HasDerivAt (fun t => bare β (bump x d c t U)) (bare β (bump x d c t U) * (-β * ⟪c,force (bump x d c t U) x d⟫_ℝ)) t :=
  ((energy_variation x d c t U).const_mul (-β)).exp
end Variation
end YM.StressFlux
