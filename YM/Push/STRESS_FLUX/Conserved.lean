import YM.Push.STRESS_FLUX.FreeTests
import YM.Work.A01.Mirror

/-! A *common* physical stress tensor label modulo the all-spectator nulls, conserved,
with its ordinary one-point expectation removed, nonzero (given real-H rank comparisons in
the two relevant degrees). Doesn't assume the weak stress or any O(4) law on this Table.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Gauge Table Climb
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff

variable {G : Gauge} {L : Register G} {S : Table L} {d : ℕ} {A : S.RealSpin}
variable (W : DiffPlan S)

theorem raw_eq {T : S.Stress} (hT : T ∈ TableTwo A) : RawTensor A T := by
  intro k a b
  have he (t : ℝ) (x : S.Field 4) : (t:ℂ) • x = t • x := IsScalarTower.algebraMap_smul ℂ t x
  simp_rw [he,mul_smul,← Finset.smul_sum,signed_sum k b, signed_sum k a,smul_smul]
  exact hT.2.2 ..

theorem deriv_mirror (H : W.Orientation A) (s : Signed) (a : Axis) (x : S.Field d) :
    S.mirror A (d+1) s (W.deriv d a x) = sign s a • W.deriv d (s.perm a) (S.mirror A d s x) := by
  rw [H.mirrorDer]; simp_rw [show ∀ (t : ℝ) (x : S.Field (d+1)), (t:ℂ) • x = t • x from IsScalarTower.algebraMap_smul ℂ,signed_sum]

def nabla (T : S.Stress) := fun b => ∑ a, W.deriv 4 a (T a b)

private lemma deriv_smul (c : ℝ) (a : Axis) (x : S.Field d) : W.deriv d a (c • x) = c • W.deriv d a x :=
  ((W.deriv d a).restrictScalars ℝ).map_smul c x

theorem nabla_vector (H : W.Orientation A) {T : S.Stress} (hT : T ∈ TableTwo A) : nabla W T ∈ TableOne A := by
  constructor
  · intro a; simp [nabla,conjQ,H.realDer,show ∀ a b, S.conj A 4 (T a b)=_ from hT.2.1]
  intro s b
  change S.mirror A 5 s _ = _
  have he (a : Axis) : S.mirror A 5 s (W.deriv 4 a (T a b)) = sign s b • W.deriv 4 (s.perm a) (T (s.perm a) (s.perm b)) := by
    rw [deriv_mirror W H, show S.mirror A 4 s (T a b)=_ from hT.2.2 s a b, mul_smul, deriv_smul,deriv_smul,sign_sign]
  simp only [nabla,map_sum, he, ← Finset.smul_sum, Equiv.sum_comp s.perm (fun i => W.deriv 4 i (T i (s.perm b)))]

def rankOp (H : W.Orientation A) : TableTwo A →ₗ[ℝ] TableOne A where
  toFun v := ⟨nabla W v.val,nabla_vector W H v.property⟩
  map_add' v u := by apply Subtype.ext; funext a; change ∑ b : Axis, W.deriv 4 b (v.val b a + u.val b a) = _; simp only [map_add, Finset.sum_add_distrib]; rfl
  map_smul' c v := by apply Subtype.ext; funext a; change ∑ b, W.deriv _ _ (c • v.val b a) = c • ∑ b, W.deriv 4 b (v.val b a); simp only [deriv_smul,Finset.smul_sum]

def average (S : Table L) (z : Points 1) : S.Field d →ₗ[ℂ] ℂ := (S.classMoment S (fun _ => d) z).toLinearMap (fun _ => 0) 0
lemma average_at (J : S.Stress) (x a b) : oneStress S J x a b = average S x (J a b) := by
  rw [oneStress,quad,average,MultilinearMap.toLinearMap_apply]
  change S.classMoment S (fun _ => 4) x (fun _ => J a b) = _; congr! 1
  funext i; fin_cases i; simp

structure Centers (J : S.Stress) : Prop where
  center (x : Points 1) a b : oneStress S J x a b = 0
  alive : J ≠ 0

private lemma centers_by_symmetry (H : S.Hierarchy) {J : S.Stress} (ht : J ∈ TableTwo H.spin) (hj : (average S 0 (J 0 0)).re = 0) (x : Points 1) (a b : Axis) : oneStress S J x a b = 0 := by
  have hx : x ∈ conf _ := fun _ _ _ => Subsingleton.elim ..
  have hz : (0 : Points 1) ∈ conf _ := fun _ _ _ => Subsingleton.elim ..
  let v i j := (⟨4,J i j⟩ : S.Tag)
  have ha : oneStress S J x a b = oneStress S J 0 a b := by
    rw [show x = Points.across (x 0) (0 : Points 1) by ext1 i; fin_cases i; simp]
    exact H.translations 1 0 hz (x 0) (fun _ => ⟨4,S.representative 4 (J a b)⟩)
  have hb (i j : Axis) : star (oneStress S J 0 i j)=oneStress S J 0 i j := by
    change star (S.useAt S _ (fun _ => v i j))= _
    rw [← Work.A01.real_eval H.laws.toSymmetric H.spin hz (fun _ => v i j),show Work.A01.realTag H.spin ∘ (fun _ : Fin 1 => v i j)= fun _ => v i j from
      funext fun _ => congr_arg (Sigma.mk 4) (ht.2.1 i j)]; rfl
  have hp (i j : Axis) (k : Signed) : oneStress S J 0 i j = (sign k i*sign k j) • oneStress S J 0 (k.perm i) (k.perm j) := by
    have he (T : S.Stress) := average_at T (0:Points 1)
    have hh := Work.A01.mirror_eval H.laws.toSymmetric H.spin hz (fun _ => v i j) k
    rw [show Points.move k.ortho (0 : Points 1)=0 from PiLp.ext (fun _ => map_zero (Ortho.motion k.ortho))] at hh
    change oneStress S (fun a b => spinQ H.spin k (J a b)) 0 i j = oneStress S J 0 i j at hh
    rw [← hh,he,ht.2.2, he]
    exact ((average S 0).restrictScalars ℝ).map_smul _ _
  have h0 : oneStress S J 0 0 0 = 0 := Complex.ext ((congr_arg Complex.re (average_at ..)).trans hj) (Complex.conj_eq_iff_im.mp (hb 0 0))
  rw [ha]
  by_cases h : a=b
  · have he := hp 0 0 (⟨Equiv.swap 0 a, fun _ => false⟩)
    rw [h0] at he; rw [← h]; simpa [sign] using he.symm
  have he := hp a b (Signed.mirror a)
  simp only [sign,Signed.mirror,Equiv.refl_apply,h,decide_true,decide_false,Bool.false_eq_true,reduceIte,mul_one,neg_one_smul] at he
  linear_combination he/2

lemma material_neg (S : Table L) (w : Coeff) : material S (-w) = -material S w := by funext a b; simp [material,-fromPol_formula]
lemma neg_raw (H : S.Hierarchy) {J : S.Stress} (h1 : Centers J) (ht : J ∈ TableTwo H.spin) (hq : nabla W J=0) :
    Centers (-J) ∧ (-J)∈ TableTwo H.spin ∧ nabla W (-J)=0 := by
  refine ⟨⟨fun x a b => ?_, neg_ne_zero.mpr h1.alive⟩, (TableTwo H.spin).neg_mem ht, funext fun a => ?_⟩
  · rw [average_at,Pi.neg_apply,Pi.neg_apply,map_neg,← average_at,h1.center,neg_zero]
  simpa [nabla, Finset.sum_neg_distrib] using congr_arg Neg.neg (congr_fun hq a)

/-- existence part using *only* H-ranks at four and five. The coefficients live
in the actual reference label space. The scale and sign here are not yet fixed by the final
continuum Ward tests. -/
theorem exists_stress (h : G.Simple) (H : S.Hierarchy) (hw : W.Orientation H.spin) {A : (Bel L).RealSpin}
    (U4 : Spin.change S 4) (U5 : Spin.change S 5) (h4 : Spin.realH H.spin A U4) (h5 : Spin.realH H.spin A U5) :
    ∃ w : Coeff, ‖w‖ = 1 ∧ nabla W (material S w) = 0 ∧ Centers (material S w) := by
  let P := rankOp W hw
  let R := Complex.reCLM.toLinearMap ∘ₗ ((average S 0).restrictScalars ℝ) ∘ₗ (LinearMap.proj (R:=ℝ) (0:Axis)) ∘ₗ (LinearMap.proj (0:Axis)) ∘ₗ (TableTwo H.spin).subtype
  let Y := (P.prod R).comp (tableStress H.spin)
  have hn : ¬ Injective Y := by
    intro he
    have ht := LinearMap.finrank_le_finrank_of_injective he
    rw [Module.finrank_fin_fun, Module.finrank_prod,Module.finrank_self] at ht
    have hh := compare_five h U5 h5
    omega
  obtain ⟨u, hu, hx⟩ : ∃ u : Coeff, Y u = 0 ∧ u ≠ 0 := by by_contra! he; exact hn (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr he))
  let w := ‖u‖⁻¹ • u
  have he : ‖w‖ = 1 := by simp [w,norm_smul,hx]
  have hh : Y w = 0 := by simp only [w,map_smul,hu,smul_zero]
  have hn : material S w ≠ 0 := fun e => by
    have h0 : w = 0 := (stress_bijective h U4 h4).1 ((Subtype.ext e).trans (map_zero (tableStress H.spin)).symm)
    rw [h0,norm_zero] at he; exact zero_ne_one he
  refine ⟨w,he,congr_arg (fun v => (v.1 : TableOne H.spin).val) hh, ⟨centers_by_symmetry H ((tableStress H.spin w).property)
    (show (average S 0 ((tableStress H.spin w).val 0 0)).re = 0 from congr_arg Prod.snd hh), hn⟩⟩

lemma material_conserved (H : S.RealSpin) {w : Coeff} (he : nabla W (material S w)=0) :
    Conserved W H (material S w) ∧ RawTensor H (material S w) :=
  ⟨⟨(tableStress H w).property.1,(tableStress H w).property.2.1, congr_fun he⟩,raw_eq (tableStress H w).property⟩
end YM.StressFlux
