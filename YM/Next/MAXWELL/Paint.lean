import YM.Euclid.Words
import YM.Maxwell.Wick
import YM.Next.MAXWELL.Jets

/-!
# Splitting the shell, real color components and equivariant projection

Need equivariant lift to the actual label variables. Do not identify
all polynomials on the real shell with invariant labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open WaveOn
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j : ℕ} {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- Lift a color linear map without changing tensor indices. -/
def rawMap (j : ℕ) (L : F →L[ℝ] M) : TwoJet F j →ₗ[ℝ] TwoJet M j where
  toFun A a b := L.compContinuousMultilinearMap (A a b)
  map_add' A B := by
    funext a b; ext; exact map_add L _ _
  map_smul' t A := by
    funext a b; ext; exact map_smul L _ _

def faceMap (j : ℕ) (L : F →L[ℝ] M) : Solution F j →ₗ[ℝ] Solution M j where
  toFun A := ⟨rawMap j L A.val, by
    have he : rawMap j L A.val = nth (fun a b => L ∘ asWave A a b) j 0 := by
      funext a b; ext1 v; symm; change coeff _ j 0 v = L (A.val a b v)
      rw [coeff_linear L v ((wavePoly A).smooth a b 0 (mem_univ _) |>.of_le (WithTop.coe_le_coe.mpr le_top))]
      exact congr_arg (fun Z : TwoJet F j => L (Z a b v)) (asWave_jet _)
    rw [he]; exact (composeColor L (wavePoly A)).jets isOpen_univ (mem_univ _)⟩
  map_add' _ _ := Subtype.ext (map_add (rawMap j L) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (rawMap j L) _ _)

theorem face_eval (j) (L : F →L[ℝ] M) (A : Solution F j) (a b v) :
    (faceMap j L A).val a b v = L (A.val a b v) := rfl

abbrev cp {G : Gauge} (i : G.ColorIndex) : G.Color →L[ℝ] ℝ := EuclideanSpace.proj i

def castFace (u : G.El) (j : ℕ) := faceMap j (G.adjoint u).toContinuousLinearMap

lemma color_rise (u : G.El) (A : Labels.Taylor G j) :
    takeCurl (Labels.Taylor.paint u A) = rawMap j (G.adjoint u).toContinuousLinearMap (takeCurl A) := by
  funext a b; ext1 v
  change _ = G.adjoint u (takeCurl A a b v)
  unfold takeCurl Labels.Taylor.paint
  simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_apply, sub_apply,ContinuousMultilinearMap.curryLeft_apply]
  rw [map_smul,map_sub]; rfl

theorem equiv_curl (u : G.El) (A : Shell G j) : gaugeJet (castFace u j A) = Labels.Taylor.paint u (gaugeJet A) := by
  apply potential.injective; apply Subtype.ext; change takeCurl _ = takeCurl _
  rw [match_leg,color_rise,match_leg]; rfl

lemma color_lower (L : F →L[ℝ] M) (u : E4) (A : Solution F (j+1)) :
    lower M j u (faceMap (j+1) L A) = faceMap j L (lower F j u A) := by
  apply Subtype.ext; funext a b; ext1 v; rw [lower_apply, face_eval,face_eval,lower_apply,map_smul]

lemma color_sum (x : G.Color) : (∑ i, x i • unitColor G i) = x := by
  ext1 c; simp [unitPaint]

lemma raw_decompose (A : TwoJet G.Color j) :
    (∑ i : G.ColorIndex, rawMap j (tint (G:=G) (unitColor G i)) (rawMap j (cp (G:=G) i) A)) = A := by
  funext a b; ext1 v; simp only [Finset.sum_apply,sum_apply]
  exact color_sum (G:=G) _

abbrev Sheet (j : ℕ) := Solution ℝ j
abbrev Flavor (j : ℕ) := Module.Dual ℝ (Sheet j)

def flavor (j : ℕ) (i : G.ColorIndex) : Flavor j →ₗ[ℝ] Probe G j where
  toFun p := p.comp (faceMap j (cp (G:=G) i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fill (j : ℕ) (v : G.Color) : Sheet j →ₗ[ℝ] Shell G j := faceMap j (tint (G:=G) v)

theorem which (v : G.Color) (A : Sheet j) (i : G.ColorIndex) :
    faceMap j (cp (G:=G) i) (fill j v A)=v i • A := by
  apply Subtype.ext; funext a b; ext1 u
  exact mul_comm (A.val a b u) (v i)

lemma half_sum (A : Shell G j) : (∑ i : G.ColorIndex, fill j (unitColor G i) (faceMap j (cp (G:=G) i) A))=A := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]; exact raw_decompose (G:=G) A.val

private def project_real (j : ℕ) : TwoJet ℝ j →ₗ[ℝ] Sheet j := (onShell ℝ j).subtype.leftInverse

def demark (G : Gauge) (j : ℕ) : TwoJet G.Color j →ₗ[ℝ] Shell G j :=
    ∑ i : G.ColorIndex, (fill j (unitColor G i)).comp ((project_real j).comp (rawMap j (cp (G:=G) i)))

theorem restore (A : Shell G j) : demark G j A.val=A := by
  unfold demark; rw [LinearMap.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (half_sum A)
  let B := faceMap j (cp (G:=G) i) A
  change fill j _ (project_real j B.val)=_
  rw [show project_real j B.val=B from LinearMap.leftInverse_apply_of_inj (onShell ℝ j).ker_subtype B]

lemma demark_cast (A : TwoJet G.Color j) (L : G.Color →L[ℝ] G.Color) :
    demark G j (rawMap j L A) = faceMap j L (demark G j A) := by
  -- enough to show on each basis color
  suffices H : ∀ (i : G.ColorIndex) (B : TwoJet ℝ j), demark G j (rawMap j L
      (rawMap j (tint (G:=G) (unitColor G i)) B)) = faceMap j L (demark G j
        (rawMap j (tint (G:=G) (unitColor G i)) B)) by
    rw [← raw_decompose A]; simp only [map_sum,H]
  have he (v : G.Color) (B : TwoJet ℝ j) : demark G j (rawMap j (tint (G:=G) v) B) = fill j v (project_real j B) := by
    unfold demark; rw [LinearMap.sum_apply]
    rw [← half_sum (fill j v (project_real j B))] -- one RHS
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht : rawMap j (cp (G:=G) i) (rawMap j (tint (G:=G) v) B) = v i • B := by
      funext a b; ext1 u; exact mul_comm (B a b u) (v i)
    simp only [LinearMap.comp_apply,ht,map_smul,which]
  have hf (i : G.ColorIndex) (B : TwoJet ℝ j) : rawMap j L
      (rawMap j (tint (G:=G) (unitColor G i)) B) = rawMap j (tint (G:=G) (L (unitColor G i))) B := by
    funext a b; ext1 u; exact map_smul L _ _
  intro i B; rw [he, hf,he]; apply Subtype.ext
  funext a b; ext1 v; exact (map_smul L _ _).symm

def assign (G : Gauge) (j : ℕ) : Labels.Taylor G j →ₗ[ℝ] Shell G j :=
    (demark G j).comp ((formSpace j G.Color).subtype.comp (potential (G:=G)).toLinearMap)

theorem retrieve (A : Shell G j) : assign G j (gaugeJet A)=A := by
  change demark G j (takeCurl (gaugeJet A))=_; rw [match_leg, restore]

theorem fit_paint (u : G.El) (A : Labels.Taylor G j) :
    assign G j (Labels.Taylor.paint u A) = castFace u j (assign G j A) := by
  change demark G j (takeCurl _)=_
  rw [color_rise]
  exact demark_cast (G:=G) _ _
end YM.Maxwell.Free
