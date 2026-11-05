import YM.Next.MAXWELL.Double
import YM.Next.MAXWELL.System
import YM.Next.MAXWELL.Triangle
import YM.Gauge.Casimir

/-! The canonical scalar and its exact free Wick coefficient. No physical comparison asserted
by computing this contraction. Positive pairs vs summed-axis convention explicit. -/
noncomputable section
namespace YM.Trace
open MeasureTheory Set Function Complex Filter Real
open Maxwell Maxwell.Free Maxwell.Wick Analysis Tensor
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {G : Gauge}

/-- All axes summed; antisymmetry is not quotienting out either orientation here. Equivalent
to a half of the positive-pair sum. -/
def actionScalar (G : Gauge) : WickPol G := (((1/4 : ℝ):ℂ)) • ∑ i, sheetEnergy i i
lemma polStress_value i j : polStress G i j = sheetEnergy i j - (↑(kr i j):ℂ) • actionScalar G := by
  rw [actionScalar,polStress,smul_smul]; push_cast; rfl
lemma trace_free : ∑ i, polStress G i i=0 := by
  simp only [polStress_value, Free.kr_eq,Complex.ofReal_one,one_smul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,if_true]
  rw [actionScalar,← Nat.cast_smul_eq_nsmul ℂ,smul_smul, show (↑(4:ℕ):ℂ) * ↑((1/4:ℝ))=1 by norm_num]; norm_num
lemma scalar_packet_mem : actionScalar G∈shellSector G 4 := by
  -- weighted-homogeneous and quadrant arguments from stress_label; use precisely same total grading/normalization.
  refine sector.mpr ⟨Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _=>Submodule.sum_mem _ fun i _=> ?_),?_⟩
  · have he : MvPolynomial.IsWeightedHomogeneous scaleW (phi (G:=G) a a i i) 4 := by
       unfold phi; apply MvPolynomial.IsWeightedHomogeneous.sum
       exact fun c _ => (symbol_hom (omegaLeg c a i) (fun i=>i+2)).mul (symbol_hom (omegaLeg c a i) (fun i=>i+2))
    rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]; exact fun p hp => (he (MvPolynomial.mem_support_iff.mp hp)).le
  exact fun u=> by simp [actionScalar,sheetEnergy,map_sum,map_smul,shade_phi]

def scalarLabel (F : Labels.Frames G) : (Model F).Field 4 := (fields F 4).symm ⟨actionScalar G,scalar_packet_mem⟩
lemma scalar_address (F : Labels.Frames G) : address F 4 (scalarLabel F) = actionScalar G := by unfold scalarLabel; rw [address_eval]; simp

variable {x y : E4}
lemma pair_quadratic (hx : x≠y) (A B C D : Factor G) : bond G x y (letter A * letter B) (letter C * letter D) =
     linkEntry (x,A) (y,C)*linkEntry (x,B) (y,D)+linkEntry (x,A) (y,D)*linkEntry (x,B) (y,C) := by
  let v := fun (_:Factor G) => (0:Fin 1); let R: List (Factor G) := [C,D]; let Q := id (α:=Factor G)
  have he : (fun _ : Fin 1 => letter C*letter D) = bag v Q R := by ext1 i; fin_cases i; simp [bag,v,Q,R]
  rw [bond_eval,he,show letter A * letter B= _ from (by simp : _=([A,B].map letter).prod),
       pairPoints, planted (x:=points fun _ : Fin 1 => y) _ _ _ _ (pair_ok hx)] -- binder x likely explicit
  change pairCost _ [(x,A),(x,B),(y,C),(y,D)]=_
  simp only [pair_step,pulls_cons,pulls_nil,zero_mul,mul_zero,add_zero,zero_add,link_zero]
  rw [pairCost]; ring

private lemma sum_rows (R : Ortho) (a b : Axis) : (∑ i : Axis, R.val a i * R.val b i)=if a=b then 1 else 0 := by
  let h := Matrix.mem_unitaryGroup_iff.mp R.property
  simpa only [Matrix.mul_apply,Matrix.star_apply, star_trivial,Matrix.one_apply] using! congrFun (congrFun h a) b
private lemma wedge_orthonormal (R : Ortho) (a b : Axis) :
      (∑ i : Axis, ∑ k : Axis, (wedge R.val a b i k)^2)=if a=b then 0 else 2 := by
    let P a b i := R.val a i * R.val b i
    have Q (c i j) : (c * ∑ l : Axis,P i j l) = if i=j then c else 0 := by rw [show (∑ l, P _ _ l)=_ from sum_rows R ..]; split_ifs <;> ring
    have ht a b j : (∑ i, (R.val a i*R.val b j)^2) = (R.val b j)^2 := by
      rw [show (∑ i : Axis, (R.val a i * R.val b j)^2) = _ from
          Finset.sum_congr rfl (fun i _ => by exact (by unfold P; ring : (R.val a i * R.val b j)^2 = (R.val b j)^2 * P a a i)), ← Finset.mul_sum, Q,if_pos rfl] -- fill
    have hv (j) : (∑ i : Axis, R.val a j *(R.val b i) * (R.val a i * R.val b j)) =
         if a=b then R.val a j * R.val b j else 0 := by
         rw [show (∑ i : Axis, R.val a j *(R.val b i) * (R.val a i * R.val b j))=_ from Finset.sum_congr rfl
           (fun i _=> by exact (by unfold P; ring : R.val a j * R.val b i * (R.val a i * R.val b j) = R.val a j * R.val b j * P a b i)),← Finset.mul_sum, Q]
    have hs (j) : (∑ i : Axis, wedge R.val a b j i ^2) = (R.val b j)^2+(R.val a j)^2- 2*(if a=b then R.val a j * R.val b j else 0) := by
         simp_rw [wedge,show ∀ i, ((R.val a j * R.val b i - R.val a i * R.val b j)^2)=
             (R.val a i * R.val b j) ^2+(R.val b i * R.val a j)^2 - 2*(R.val a j * R.val b i * (R.val a i * R.val b j)) from fun i=>by ring]
         rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ht, ht, ← Finset.mul_sum, hv j]
    -- target of equality set by expression
    have H (i) : (∑ j : Axis, R.val i j ^2)=1 := by simp_rw [sq]; simpa using sum_rows R i i
    simp_rw [hs]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,H,H, ← Finset.mul_sum]
    by_cases ha : a=b
    · simp [ha,H,← sq]
      norm_num
    norm_num [ha]



lemma total_wedge (R : Ortho) : (∑ a : Axis, ∑ b : Axis, ∑ i : Axis, ∑ j : Axis, wedge R.val a b i j^2) = 12*2 := by
    simp_rw [wedge_orthonormal]; classical
    have hw (i : Axis) : (∑ j : Axis, if i=j then (1:ℝ) else 0) = 1 := by simp
    have hQ (i : Axis) : (∑ j : Axis, if i=j then (0:ℝ) else 2) = 6 := by
        rw [Finset.sum_congr rfl (fun j _ => (by split_ifs <;> norm_num : (if i=j then (0:ℝ) else 2) =
                    2-2*(if i=j then 1 else 0))),Finset.sum_sub_distrib,← Finset.mul_sum,hw i]; norm_num
    simp_rw [hQ]; norm_num

theorem scalar_pair (h : x≠y) :
   bond G x y (actionScalar G) (actionScalar G) = ((3*↑G.lieDim/Real.pi^4:ℝ)/‖x-y‖^8) := by
   let t (c : G.ColorIndex) (a b : Axis) : Factor G := ⟨0,omegaLeg c a b⟩
   let D := (1/4:ℝ); let U := house (x-y)
   let e (c a b) : WickPol G := letter (t c a b) * letter (t c a b)
   have he : actionScalar G = (D:ℂ) • ∑ a : Axis, ∑ b : Axis, ∑ c : G.ColorIndex, e c a b := rfl
   simp_rw [he,map_smul,LinearMap.smul_apply]
   simp only [map_sum,LinearMap.sum_apply,e,pair_quadratic h,link_eq x y _ _ h]
   dsimp only [t];
   let β := (4:ℝ) * normal * (‖x-y‖^2)⁻¹^2

   have hS i j a b (c d:G.ColorIndex) : (↑(K (omegaLeg c a b) (omegaLeg d i j) x y):ℂ) =
       if c=d then ↑(β*wedge U.val a b i j) else 0 := by
      split_ifs with hz <;> simp only [omega_K_eq c d a b i j h,hz,if_false,Complex.ofReal_zero]
      · rw [omega_K_eq _ d _ _ _ _ h, if_pos rfl, Free.bare_formula a b i j (sub_ne_zero.mpr h)]
   have hh (Q : M4) : (∑ a : Axis, ∑ b : Axis, ∑ _d : G.ColorIndex, ∑ i : Axis,∑ j : Axis, (wedge Q i j a b)^2) =
       (↑G.lieDim:ℝ) * (∑ a : Axis,∑ b : Axis,∑ i : Axis,∑ j : Axis,(wedge Q i j a b)^2) := by
       simp_rw [Finset.sum_const,Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul, Finset.mul_sum]
   have hW (i j a b) : wedge U.val i j a b = wedge U.val a b i j := by
        have hx (i j) : U.val i j = U.val j i := by
           have H := congrFun (congrFun (house_star (x-y)) i) j
           unfold U house; simpa using! H.symm
        unfold wedge; rw [hx i a,hx i b,hx j a,hx j b]; ring
   simp_rw [hS,← two_mul]
   simp only [ite_mul,zero_mul,mul_zero,apply_ite]
   -- normalize nested costs
   have heq (a b i j) (d : G.ColorIndex) : (∑ c : G.ColorIndex, if c=d then if c=d then (2:ℂ)*(↑(β*wedge U.val i j a b)*↑(β*wedge U.val i j a b)) else 0 else 0)
          = (2:ℂ)* (↑(β^2 * wedge U.val i j a b^2) : ℂ) := by
        push_cast; simp; ring
   simp_rw [heq,smul_eq_mul, ← Finset.mul_sum,← Complex.ofReal_sum]
   simp_rw [← Finset.mul_sum, hh U.val]
   have hsum : ∑ i : Axis, ∑ j : Axis, ∑ a : Axis, ∑ b : Axis, wedge U.val a b i j ^2 = 12*2 := by
      convert! total_wedge U using 1
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro a _
      exact Finset.sum_congr rfl fun b _ => congrArg (·^2) (hW a b i j)
   rw [hsum]
   unfold β D normal; push_cast; field_simp; ring

/-- Same normalization on the free reference branch already used for labels (the
spin comparator, alias `Model`). -/
lemma reference_pair (F : Labels.Frames G) {x y} (h : x≠y) :
    Ward.disc (fun _ : Fin 2 => (⟨4,scalarLabel F⟩ : (Model F).Tag)) (pairPoints x y) =
      ((3*↑G.lieDim/Real.pi^4:ℝ)/‖x-y‖^8) := by
   unfold Ward.disc
   rw [display,← scalar_pair h,bond_eval]
   congr 1
   ext1 i; fin_cases i <;> change address F 4 (scalarLabel F)=_ <;> rw [scalar_address] <;> rfl
end YM.Trace
