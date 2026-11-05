import YM.Next.MAXWELL.Kernel

/-! Orthogonal tensors on jets and wavefunctions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open WaveOn
open scoped ContDiff Topology BigOperators RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {j k l : ℕ}

lemma inv_entry (s : Ortho) (i l : Axis) : s⁻¹.val i l = s.val l i := rfl

lemma col_dot (s : Ortho) (i l : Axis) : ∑ a : Axis, s.val a i * s.val a l = if i=l then 1 else 0 := by
  rw [← Matrix.one_apply]
  exact congr_arg (fun M : M4 => M i l) (Ortho.transp s)

lemma ortho_expansion (s : Ortho) (i : Axis) : Ortho.move s (basis i) = ∑ k : Axis, s.val k i • basis k := by
  ext1 k; simp [Ortho.move]

def fieldTurn (s : Ortho) (f : Field F) : Field F := fun a b x =>
  ∑ i : Axis, ∑ l : Axis, (s.val a i * s.val b l) • f i l (Ortho.move s⁻¹ x)

lemma turn_comp_diff {f : Field F} (s : Ortho) (a b : Axis) {x : E4}
    (H : ∀ i l, ContDiffAt ℝ ∞ (f i l) (Ortho.move s⁻¹ x)) :
    ContDiffAt ℝ ∞ (fieldTurn s f a b) x := ContDiffAt.sum fun i _ => ContDiffAt.sum fun l _ =>
  ((H i l).comp x (Ortho.motion s⁻¹).toContinuousLinearEquiv.contDiff.contDiffAt).const_smul _

lemma D_fieldTurn (s : Ortho) (f : Field F) (a b : Axis) {x : E4} (u : E4)
    (H : ∀ i l, ContDiffAt ℝ ∞ (f i l) (Ortho.move s⁻¹ x)) :
    D u (fieldTurn s f a b) x =
      fieldTurn s (fun i l => D (Ortho.move s⁻¹ u) (f i l)) a b x := by
  let L := (Ortho.motion s⁻¹).toContinuousLinearMap
  have hw (i l) : DifferentiableAt ℝ (f i l ∘ L) x :=
    (show ContDiffAt ℝ ∞ (f i l) (L x) from H i l).differentiableAt (by simp) |>.comp x L.differentiableAt
  change D u (fun z => ∑ i : Axis, ∑ l : Axis, (s.val a i * s.val b l) • (f i l ∘ L) z) x = _
  have hh (i l : Axis) : DifferentiableAt ℝ (fun z => (s.val a i * s.val b l) • (f i l ∘ L) z) x :=
    (hw i l).const_smul _
  rw [D, fderiv_fun_sum (fun i _ => DifferentiableAt.fun_sum (fun l _ => hh i l)),sum_apply]
  unfold fieldTurn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fun_sum (fun l _ => hh i l),sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_fun_const_smul (hw i l), fderiv_comp x
    (show DifferentiableAt ℝ (f i l) (L x) from (H i l).differentiableAt (by simp)) L.differentiableAt, L.fderiv]; rfl

lemma fieldTurn_grad {f : Field F} (s : Ortho) (a b c : Axis) {x : E4}
    (H : ∀ i l, ContDiffAt ℝ ∞ (f i l) (Ortho.move s⁻¹ x)) :
    grad a (fieldTurn s f b c) x = ∑ i : Axis, ∑ l : Axis, ∑ k : Axis,
      ((s.val b i * s.val c l) * s.val a k) • grad k (f i l) (Ortho.move s⁻¹ x) := by
  rw [grad, D_fieldTurn _ _ _ _ _ H]
  simp only [fieldTurn,D,grad, ortho_expansion, inv_entry,map_sum, map_smul,Finset.smul_sum, smul_smul]

lemma fieldTurn_wave {f : Field F} {U : Set E4} (s : Ortho) (h : WaveOn U f) :
    WaveOn ((Ortho.move s⁻¹) ⁻¹' U) (fieldTurn s f) := by
  refine ⟨fun a b x hx => turn_comp_diff _ _ _ fun i l => h.smooth _ _ _ hx, ?_, ?_,?_⟩
  · intro a b x hx
    unfold fieldTurn; rw [Finset.sum_comm]
    simp_rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [h.form l i _ hx,mul_comm (s.val a l) (s.val b i),smul_neg]
  · intro a b c x hx
    let y := Ortho.move s⁻¹ x
    have he (a b c) : grad a (fieldTurn s f b c) x = ∑ i : Axis, ∑ l : Axis, ∑ k : Axis,
        ((s.val b i * s.val c l) * s.val a k) • grad k (f i l) y := fieldTurn_grad s _ _ _ fun i l => h.smooth i l y hx
    rw [he, he, he]
    have hc (z : Axis → Axis → Axis → F) : (∑ i : Axis, ∑ l : Axis, ∑ k : Axis, z l k i) =
        ∑ i : Axis, ∑ l : Axis, ∑ k : Axis, z i l k := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (f := fun i k => z _ k i)]
    let A i l k := (s.val b i * s.val c l) * s.val a k
    have ht : (∑ i : Axis, ∑ l : Axis, ∑ k : Axis,
        ((s.val c i * s.val a l) * s.val b k) • grad k (f i l) y) = ∑ i : Axis, ∑ l : Axis, ∑ k : Axis,
        A i l k • grad i (f l k) y := by
      refine (hc (fun i l k => ((s.val c i * s.val a l) * s.val b k) • grad k (f i l) y)).symm.trans ?_
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      dsimp [A]; congr 1; ring
    have hb : (∑ i : Axis, ∑ l : Axis, ∑ k : Axis,
        ((s.val a i * s.val b l) * s.val c k) • grad k (f i l) y) = ∑ i : Axis, ∑ l : Axis, ∑ k : Axis,
        A i l k • grad l (f k i) y := by
      refine (hc (fun i l k => ((s.val a k * s.val b i) * s.val c l) • grad l (f k i) y)).trans ?_
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      dsimp [A]; congr 1; ring
    rw [ht,hb]; simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ =>
      (show A i l k • _ + A i l k • _ + A i l k • _ = (0:F) by rw [← smul_add, ← smul_add, h.cycle _ _ _ _ hx, smul_zero])
  intro b x hx
  let y := Ortho.move s⁻¹ x
  have he (a : Axis) : grad a (fieldTurn s f a b) x = ∑ l : Axis, s.val b l •
      ∑ i : Axis, ∑ k : Axis, (s.val a i * s.val a k) • grad k (f i l) y := by
    rw [fieldTurn_grad (H := fun i l => h.smooth i l y hx),Finset.sum_comm]
    simp_rw [Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      congr_arg (fun q : ℝ => q • grad k (f l i) y) (by ring)
  simp_rw [he]; rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro l _
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hs (i) : (∑ a : Axis, ∑ k : Axis, (s.val a i * s.val a k) • grad k (f i l) y) = grad i (f i l) y := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul,col_dot]
    simp
  simp_rw [hs,h.divergence _ y hx, smul_zero]

def turnJ (s : Ortho) : TwoJet F j →ₗ[ℝ] TwoJet F j where
  toFun A := fun a b => ∑ i : Axis, ∑ l : Axis, (s.val a i * s.val b l) •
    ((A i l).compContinuousLinearMap fun _ => (Ortho.motion s⁻¹).toContinuousLinearMap)
  map_add' A B := by ext a b u; simp [Finset.sum_add_distrib, smul_add]
  map_smul' t A := by ext a b u; simp [Finset.smul_sum, smul_comm t]

lemma turns_apply (s : Ortho) (A : TwoJet F j) (a b : Axis) (v : Fin j → E4) :
    turnJ s A a b v = ∑ i : Axis, ∑ l : Axis, (s.val a i*s.val b l) •
      A i l (Ortho.move s⁻¹ ∘ v) := by
  simp only [turnJ, LinearMap.coe_mk, AddHom.coe_mk, sum_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl

theorem nth_global_turn (f : Field F) (H : ∀ a b, ContDiff ℝ j (f a b)) (s : Ortho) (x : E4) :
    nth (fieldTurn s f) j x = turnJ s (nth f j (Ortho.move s⁻¹ x)) := by
  ext1 a; ext1 b; apply ContinuousMultilinearMap.ext; intro v
  rw [turns_apply]
  let L := (Ortho.motion s⁻¹).toContinuousLinearMap
  let A (i l : Axis) := (s.val a i * s.val b l) • (f i l ∘ L)
  have ht : fieldTurn s f a b = ∑ i : Axis, ∑ l : Axis, A i l := funext fun y => by
    simp only [Finset.sum_apply]; rfl
  have he (i l) : ContDiff ℝ j (A i l) := (((H i l).comp L.contDiff).const_smul (s.val a i * s.val b l))
  change coeff (fieldTurn s f a b) j x v = _
  have hs (i : Axis) : ContDiffAt ℝ j (∑ l, A i l) x := by
    rw [show ∑ l, A i l = (fun y : E4 => ∑ l, A i l y) from funext fun _ => Finset.sum_apply _ _ _]
    exact ContDiffAt.sum (fun l _ => (he i l).contDiffAt)
  rw [ht, coeff_sum j x (fun i => ∑ l, A i l) _ (fun i _ => hs i),sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_sum j x _ _ (fun l _ => (he i l).contDiffAt),sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  dsimp only [A]
  rw [Tensor.coeff_smul _ (((H i l).comp L.contDiff).contDiffAt), coeff,
    ContinuousLinearMap.iteratedFDeriv_comp_right L (H i l) x le_rfl]
  rfl

def solutionTurn (s : Ortho) : Solution F j →ₗ[ℝ] Solution F j where
  toFun A := ⟨turnJ s A.val, by
    have he := fieldTurn_wave s (wavePoly A)
    rw [preimage_univ] at he
    have hs := he.jets isOpen_univ (j := j) (x := 0) (mem_univ _)
    rw [nth_global_turn (asWave A) (fun i l => diag_smooth _ _), show Ortho.move s⁻¹ 0 = 0 from map_zero (Ortho.motion s⁻¹), asWave_jet] at hs
    exact hs⟩
  map_add' _ _ := Subtype.ext (map_add (turnJ s) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (turnJ s) _ _)

theorem rot_wave (s : Ortho) (A : Solution F j) :
    asWave (solutionTurn s A) = fieldTurn s (asWave A) := funext fun a => funext fun b => funext fun x =>
  turns_apply s A.val a b (fun _ => x)

lemma asWave_inj : Injective (asWave (F := F) (j := j)) := by
  intro A B h
  apply Subtype.ext; rw [← asWave_jet,← asWave_jet,h]


lemma row_action (s r : Ortho) (a : Axis) (v : Axis → F) :
    (∑ i : Axis, (s*r).val a i • v i) = ∑ k : Axis, s.val a k •
      ∑ i : Axis, r.val k i • v i := by
  change (∑ i : Axis, (s.val*r.val) a i • v i) = _
  simp_rw [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

lemma fieldTurn_mul (s r : Ortho) (f : Field F) : fieldTurn (s*r) f = fieldTurn s (fieldTurn r f) := by
  funext a b x
  let y := Ortho.move r⁻¹ (Ortho.move s⁻¹ x)
  have he (s : Ortho) (f : Field F) (a b x) : fieldTurn s f a b x = ∑ i : Axis, s.val a i •
      ∑ l : Axis, s.val b l • f i l (Ortho.move s⁻¹ x) := by simp [fieldTurn, Finset.smul_sum,smul_smul]
  simp_rw [he,mul_inv_rev, Ortho.move_mul]
  rw [row_action]
  apply Finset.sum_congr rfl; intro i _
  congr 1
  simp_rw [row_action, Finset.smul_sum]; rw [Finset.sum_comm]
  simp_rw [smul_smul]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _
  congr 1; ring

theorem solution_rep (s r : Ortho) (A : Solution F j) :
    solutionTurn (s*r) A = solutionTurn s (solutionTurn r A) :=
  asWave_inj (by simp_rw [rot_wave,fieldTurn_mul])

@[simp] theorem solution_id (A : Solution F j) : solutionTurn 1 A = A := asWave_inj (by
  rw [rot_wave]; funext a b x; unfold fieldTurn; rw [inv_one,Ortho.move_one]
  change ∑ i : Axis, ∑ l : Axis, ((1:M4) a i * (1:M4) b l) • _ = _
  simp [Matrix.one_apply, mul_ite, ite_smul])

def probeTurn (s : Ortho) : Probe G j →ₗ[ℝ] Probe G j where
  toFun p := p.comp (solutionTurn s⁻¹)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma turn_comp_shift (s : Ortho) (A : Solution F (j+1)) (u : E4) :
    lower F j (Ortho.move s u) (solutionTurn s A) = solutionTurn s (lower F j u A) := by
  apply Subtype.ext; ext1 a; ext1 b; apply ContinuousMultilinearMap.ext; intro v
  rw [lower_apply]
  change (↑(j+1 : ℕ):ℝ) • turnJ s A.val a b _ = turnJ s _ a b v
  simp_rw [turns_apply,lower_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm]
  congr 2
  apply congr_arg (A.val i l)
  funext k; refine Fin.cases ?_ (fun t ↦ ?_) k <;> simp

theorem raiseTurn (s : Ortho) (p : Probe G j) (v : E4) :
    probeTurn s (raiseLeg v p) = raiseLeg (Ortho.move s v) (probeTurn s p) := by
  ext x; apply congr_arg p
  simpa using turn_comp_shift s⁻¹ x (Ortho.move s v)

/- Covariance with the actual radial variables, not merely an isomorphic group action. -/
theorem orientCurl (s : Ortho) (A : Labels.Taylor G j) :
    takeCurl (Labels.Taylor.turn s A) = turnJ s (takeCurl A) := by
  funext a b
  apply ContinuousMultilinearMap.ext; intro v
  let Y := Ortho.move s⁻¹ ∘ v
  have he (a b) : (Labels.Taylor.turn s A).val b (Fin.cons (basis a) v) =
      ∑ i : Axis, ∑ l : Axis, (s.val b i * s.val a l) • A.val i (Fin.cons (basis l) Y) := by
    simp only [Labels.Taylor.turn, LinearMap.coe_mk, AddHom.coe_mk, sum_apply, smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change s.val b i • A.val i (Ortho.move s⁻¹ ∘ Fin.cons (basis a) v) = _
    rw [show Ortho.move s⁻¹ ∘ Fin.cons (basis a) v = Fin.cons (Ortho.move s⁻¹ (basis a)) Y by
      ext1 k; refine Fin.cases ?_ (fun t ↦ ?_) k <;> simp [Y]]
    rw [ortho_expansion]; change s.val b i • ((A.val i).curryLeft _) _ = _
    simp only [inv_entry,map_sum,sum_apply,map_smul,Finset.smul_sum,smul_apply,smul_smul,ContinuousMultilinearMap.curryLeft_apply]
  rw [turns_apply]
  simp only [takeCurl, smul_apply, sub_apply, ContinuousMultilinearMap.curryLeft_apply, he]
  rw [Finset.sum_comm (f := fun i l => (s.val b i * s.val a l) • A.val i (Fin.cons (basis l) Y)),
    ← Finset.sum_sub_distrib]; simp_rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (s.val b l), ← smul_sub, smul_comm]

theorem gauge_orient (s : Ortho) (A : Shell G j) :
    Labels.Taylor.turn s (gaugeJet A) = gaugeJet (solutionTurn s A) := by
  have he := orientCurl s (gaugeJet A)
  rw [match_leg] at he
  apply potential.injective
  exact Subtype.ext (he.trans (match_leg (solutionTurn s A)).symm)

end YM.Maxwell.Free
