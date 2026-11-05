import YM.Next.MAXWELL.Turn

/-! # Reflection tensor of the two-form covariance -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open WaveOn
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {j k l : ℕ}

/-- Delta and unit bivector evaluated as ordinary real components. -/
def kr (a b : Axis) : ℝ := basis b a
lemma kr_eq (a b) : kr a b = if a=b then 1 else 0 := by simp [kr]
lemma kr_symm (a b) : kr a b = kr b a := by simp only [kr_eq, @eq_comm _ b a]

def wedge (R : M4) (a b i l : Axis) := R a i * R b l - R a l * R b i



lemma wedge_swap (R : M4) (a b i l) : wedge R b a i l = - wedge R a b i l := by unfold wedge; ring

lemma wedge_comp (R Q : M4) (a b i l : Axis) : wedge (R*Q) a b i l =
    ∑ c : Axis, ∑ d : Axis, R a c * R b d * wedge Q c d i l := by
  have he (i l) : (R*Q) a i * (R*Q) b l = ∑ c : Axis, ∑ d : Axis,
      (R a c * Q c i) * (R b d * Q d l) := by
    rw [Matrix.mul_apply,Matrix.mul_apply,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [wedge,he,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _; ring

def houseM (x : E4) : M4 := Matrix.of fun a b => kr a b - 2 * (‖x‖^2)⁻¹ * x a * x b

lemma house_star (x : E4) : star (houseM x) = houseM x := by
  ext a b; change houseM x b a = _; simp only [houseM, Matrix.of_apply, kr_symm b a]; ring

lemma inner4 (x y : E4) : ⟪x,y⟫_ℝ = ∑ i : Axis, x i * y i := by
  rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]; rfl

lemma house_on (x y : E4) : M4.move (houseM x) y = y - (2 * (‖x‖^2)⁻¹ * ⟪x,y⟫_ℝ) • x := by
  ext1 i
  simp only [M4.at_coord,houseM,Matrix.of_apply, kr_eq, ite_mul, one_mul,zero_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,Finset.mem_univ,
    ↓reduceIte, PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  congr 1
  rw [inner4]
  simp_rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring

lemma house_square (x : E4) : houseM x * houseM x = 1 := by
  suffices he : ∀ v : E4, M4.move (houseM x * houseM x) v = v by
    ext a b; rw [← M4.move_basis (houseM x * houseM x), ← M4.move_basis (1:M4),he,M4.move_one]
  intro v
  rw [M4.move_mul,house_on,house_on, inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  by_cases ht : x = 0
  · subst x; simp
  have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  rw [show 2 * (‖x‖ ^ 2)⁻¹ * (⟪x,v⟫_ℝ - 2 * (‖x‖ ^ 2)⁻¹ * ⟪x,v⟫_ℝ * ‖x‖^2) =
      -(2 * (‖x‖ ^ 2)⁻¹ * ⟪x,v⟫_ℝ) by field_simp; ring]
  simp

def house (x : E4) : Ortho := ⟨houseM x, by
  constructor <;> rw [house_star,house_square]⟩

lemma house_inv (x : E4) : (house x)⁻¹ = house x := Subtype.ext (house_star x)

lemma house_conjugate (s : Ortho) (x : E4) : house (Ortho.move s x) * s = s * house x := by
  apply Ortho.ext; intro y
  rw [Ortho.move_mul, Ortho.move_mul]; change M4.move (houseM _) _ = (Ortho.motion s) (M4.move (houseM _) _)
  simp only [house_on, map_sub,map_smul];
  rw [Ortho.move_norm,show ⟪Ortho.move s x,Ortho.move s y⟫_ℝ = ⟪x,y⟫_ℝ from (Ortho.motion s).inner_map_map x y]; rfl

/-- `4*normal/|x|^4` times the reflected 2-form. -/
lemma bare_formula (a b i l : Axis) {x : E4} (hx : x ≠ 0) :
    bareCurl a b i l x = 4 * normal * (‖x‖^2)⁻¹^2 * wedge (house x).val a b i l := by
  have he (q p k r : Axis) : grad q (curlOpp p k r) x =
      kr p k * grad q (grad r Green) x - kr p r * grad q (grad k Green) x := by simp [Bare.opp_grad hx,kr_eq,ite_mul, eq_comm]
  rw [bareCurl,Pi.sub_apply,he a b i l, he b a i l]; simp only [second_Green hx,wedge,house,houseM,Matrix.of_apply]
  rw [← kr, kr_symm l a, ← kr, kr_symm i a, ← kr, kr_symm l b, ← kr, kr_symm i b]
  ring

def blade (i l : Axis) (x : F) : Solution F 0 :=
  let f : Field F := fun a b _ => wedge 1 a b i l • x
  ⟨nth f 0 0, by
    apply WaveOn.jets isOpen_univ _ (mem_univ _)
    refine ⟨fun _ _ _ _ => contDiffAt_const,fun a b _ _ ↦ ?_, ?_, ?_⟩
    · simp only [f, wedge_swap 1 b a i l,neg_smul]
    all_goals simp [f,grad,D]⟩

lemma blade_eval (i l : Axis) (x : F) (a b : Axis) (v) :
    (blade i l x).val a b v = wedge 1 a b i l • x := Tensor.coeff_apply_zero _ _ _

lemma blade_rot (s : Ortho) (a b i l : Axis) (x : F) (v) :
    (solutionTurn s (blade i l x)).val a b v = wedge s.val a b i l • x := by
  change turnJ s _ a b v = _
  simp_rw [turns_apply,blade_eval,smul_smul,← Finset.sum_smul]
  congr 1
  exact (wedge_comp s.val 1 a b i l).symm.trans (by rw [mul_one])

lemma blade_turn (s : Ortho) (a b : Axis) (x : F) :
    solutionTurn s (blade a b x) =
      ∑ i : Axis, ∑ l : Axis, (s.val i a * s.val l b) • blade i l x := by
  apply Subtype.ext; ext1 i; ext1 l; apply ContinuousMultilinearMap.ext; intro v
  rw [blade_rot]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_apply,
    sum_apply, blade_eval,smul_smul]
  simp_rw [← Finset.sum_smul]
  congr 1
  simp [Matrix.one_apply, mul_ite, mul_sub, Finset.sum_sub_distrib,wedge, mul_comm (s.val l a)]

lemma probe_formula (p : Probe G 0) (a b : Axis) (c : G.ColorIndex) {x y : E4} (h : x ≠ y) :
    K p (omegaLeg c a b) x y = 4 * normal * (‖x-y‖^2)⁻¹^2 *
      p (solutionTurn (house (x-y)) (blade a b (unitColor G c))) := by
  have hz := sub_ne_zero.mpr h
  induction p using leg_probe_induction with
  | vars u d i l =>
    have ht : leg u d i l = omegaLeg d i l := by unfold omegaLeg; rw [show u = _ from Subsingleton.elim u (fun _ => 0)]
    rw [leg_eval,blade_rot,ht,omega_K_eq d c i l a b h,bare_formula _ _ _ _ hz,PiLp.smul_apply,unitPaint]
    split_ifs <;> simp [mul_assoc]
  | zero => rw [K_pairing _ _ h]; simp
  | add p q hp hq =>
    rw [K_pairing _ _ h] at hp hq ⊢; simp only [map_add,LinearMap.add_apply,hp,hq]; rw [mul_add]
  | smul t p hp =>
    rw [K_pairing _ _ h] at hp ⊢; simp only [map_smul,LinearMap.smul_apply,hp, smul_eq_mul]; ring

lemma omega_rot (s : Ortho) (a b : Axis) (c : G.ColorIndex) :
    probeTurn s (omegaLeg c a b) = ∑ i : Axis, ∑ l : Axis, (s.val i a * s.val l b) • omegaLeg c i l := by
  ext x
  change turnJ _ x.val a b (fun _ : Fin 0 => 0) c = _
  simp only [turns_apply, inv_entry,WithLp.ofLp_sum,Finset.sum_apply, PiLp.smul_apply,LinearMap.sum_apply,LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => congr_arg (fun u : Fin 0 → E4 =>
    (s.val i a * s.val l b) • (x.val i l u c)) (Subsingleton.elim _ _)

/- Using Ortho.move (active rotation of positions). -/
theorem K_orientation_value (s : Ortho) (p : Probe G 0) {x y : E4} (hx : x ≠ y) (c : G.ColorIndex) (a b : Axis) :
    K (probeTurn s p) (probeTurn s (omegaLeg c a b)) (Ortho.move s x) (Ortho.move s y) = K p (omegaLeg c a b) x y := by
  let z := x-y
  let X := Ortho.move s x
  let Y := Ortho.move s y
  let W (i l : Axis) := blade i l (unitColor G c)
  let P := probeTurn s p
  change K P _ X Y = _
  have he : X ≠ Y := (Ortho.move_injective _).ne hx
  have heq : X-Y = Ortho.move s z := ((Ortho.motion s).map_sub x y).symm
  rw [omega_rot,K_pairing _ _ he]; simp only [map_sum,map_smul,smul_eq_mul];
  rw [probe_formula p a b c hx]
  let T (q : ℝ) := 4 * normal * (q^2)⁻¹^2
  have hf (i l) : pairing (G := G) (show X-Y ∈ away from sub_ne_zero.mpr he) P (omegaLeg c i l) =
      T ‖z‖ * P (solutionTurn (house (Ortho.move s z)) (W i l)) := by
    change K P _ X Y = _
    rw [probe_formula P i l c he, heq, Ortho.move_norm]
  simp_rw [hf]
  let A := solutionTurn (house (Ortho.move s z)) (F:=G.Color) (j:=0)
  calc
    _ = T ‖z‖ * P (A (solutionTurn s (W a b))) := by
      unfold W; rw [blade_turn]; simp only [map_sum,map_smul,smul_eq_mul];
      simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      unfold T P A; ring
    _ = T ‖z‖ * P (solutionTurn s (solutionTurn (house z) (W a b))) := by
      rw [show A=solutionTurn (house (Ortho.move s z)) from rfl, ← solution_rep,house_conjugate,solution_rep]
    _ = _ := by
      change T ‖z‖ * p (solutionTurn s⁻¹ (solutionTurn s _)) = _
      rw [← solution_rep,inv_mul_cancel,solution_id]

theorem K_orientation (s : Ortho) (p : Probe G j) (q : Probe G l) {x y : E4} (hx : x ≠ y) :
    K (probeTurn s p) (probeTurn s q) (Ortho.move s x) (Ortho.move s y) = K p q x y := by
  let Cy (j l) := ∀ (p : Probe G j) (q : Probe G l) (x y : E4), x ≠ y →
    K (probeTurn s p) (probeTurn s q) (Ortho.move s x) (Ortho.move s y) = K p q x y
  suffices H : Cy j l from H p q x y hx
  have ho : Cy 0 0 := by
    intro p q x y h
    have hm := (Ortho.move_injective s).ne h
    induction q using leg_probe_induction with
    | vars u c a b =>
      rw [show leg u c a b = omegaLeg c a b by
        unfold omegaLeg; rw [show u=(fun _ => 0) from Subsingleton.elim ..]]
      exact K_orientation_value s p h c a b
    | zero => rw [K_pairing _ _ hm,K_pairing _ _ h]; simp
    | add p q hp hq =>
      rw [K_pairing _ _ hm,K_pairing _ _ h] at hp hq ⊢; simp only [map_add,hp,hq]
    | smul t p hp =>
      rw [K_pairing _ _ hm,K_pairing _ _ h] at hp ⊢; simp only [map_smul,hp]
  have hs (j l) (h : Cy j l) : Cy j (l+1) := by
    intro p q x y hxy
    have hm := (Ortho.move_injective s).ne hxy
    induction q using leg_probe_induction with
    | zero => rw [K_pairing _ _ hm,K_pairing _ _ hxy]; simp
    | add p q hp hq =>
      rw [K_pairing _ _ hm,K_pairing _ _ hxy] at hp hq ⊢; simp only [map_add,hp,hq]
    | smul t p hp =>
      rw [K_pairing _ _ hm,K_pairing _ _ hxy] at hp ⊢; simp only [map_smul,hp]
    | vars u c i m =>
      let v := u 0
      let q := leg (Fin.tail u) c i m
      let P := probeTurn s p
      let Q := probeTurn s q
      let X := Ortho.move s x
      let L := (Ortho.motion s).toContinuousLinearMap
      have he : K P Q X ∘ L =ᶠ[𝓝 y] K p q x := by
        filter_upwards [isOpen_compl_singleton.mem_nhds (show y ∈ ({x}:Set E4)ᶜ from Ne.symm hxy)] with z hz
        exact h p q x z (Ne.symm hz)
      have hv := GermD v he
      have ht : DifferentiableAt ℝ (K P Q X) (L y) :=
        ((K_smooth P Q (X,L y) hm).comp (g := fun y => K P Q y.1 y.2) (f := fun z => (X,z)) (L y)
          (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
      change fderiv ℝ (K P Q X ∘ L) y v = _ at hv
      rw [fderiv_comp y ht L.differentiableAt, L.fderiv,ContinuousLinearMap.comp_apply] at hv
      change D (Ortho.move s v) (K P (probeTurn s q) X) (Ortho.move s y) = _ at hv
      rw [K_right_D P _ hm, K_right_D p _ hxy, ← raiseTurn] at hv
      unfold v q at hv
      rw [raises,Fin.cons_self_tail,K_pairing _ _ hm,K_pairing _ _ hxy,map_smul,map_smul,map_smul] at hv
      exact smul_right_injective ℝ (by positivity : (↑(l+1 : ℕ):ℝ) ≠ 0) hv
  have hu (l) : Cy 0 l := by induction l with | zero => exact ho | succ k ih => exact hs _ _ ih
  have hb : Cy j 0 := by
    intro P Q x y h
    rw [K_symmetric _ _ ((Ortho.move_injective _).ne h), K_symmetric P Q h, hu _ Q P y x h.symm]
  clear! q
  induction l with
  | zero => exact hb
  | succ k ih => exact hs _ _ ih

@[simp] lemma probe_inv_turn (s : Ortho) (p : Probe G j) : probeTurn s (probeTurn s⁻¹ p) = p := by
  ext x
  change p (solutionTurn s⁻¹⁻¹ (solutionTurn s⁻¹ x)) = _
  rw [inv_inv,← solution_rep,mul_inv_cancel,solution_id]

theorem pulse_orientation (s : Ortho) (p : Probe G j) (i m : Axis) {x y : E4} (hxy : x ≠ y) :
    pulse (probeTurn s p) (Ortho.move s x) i m (Ortho.move s y) = fieldTurn s (pulse p x) i m (Ortho.move s y) := by
  have hm := (Ortho.move_injective s).ne hxy
  ext1 c
  rw [← K_observe (probeTurn s p) c i m hm]
  rw [show omegaLeg c i m = probeTurn s (probeTurn s⁻¹ (omegaLeg c i m)) from (probe_inv_turn ..).symm,
    K_orientation s _ _ hxy, omega_rot, K_pairing _ _ hxy]
  simp only [map_sum,map_smul,inv_entry]
  simp only [← K_pairing _ _ hxy, K_observe _ _ _ _ hxy,fieldTurn,Ortho.inv_move,
    WithLp.ofLp_sum, Finset.sum_apply,PiLp.smul_apply]

end YM.Maxwell.Free
