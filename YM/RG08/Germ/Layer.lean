import YM.RG08.Germ.Gazebo
import YM.RG08.Germ.Hat

/-! # Condition on absolute non-tree chart (finite period). Draw row of predictor mean, keep external y fixed over Wick lanes. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {c f m L : Side} {α β : Type} {G : Gauge} {η B : ℝ}

def veiled (A : Row (Fink G L) (Fink G L)) : Row (Park G L) (Park G L) := fun i j z=> i.elim (fun i=> j.elim (fun j=> A i j z) (fun _=>0)) (fun _=> 0)
lemma veiled_price {A : Row (Fink G L) (Fink G L)} (hp : A.strip η B) (hb : 0≤B) : (veiled A).strip η B := by intro i j; rcases i with i|i <;> rcases j with j|j <;> first|exact hp i j|simp [veiled,Width,SumBudget,hb]
lemma veiled_whole {A : Row (Fink G L) (Fink G L)} (hp : Whole A) : Whole (veiled A) := by obtain ⟨w,B,hw,H⟩:=hp; exact ⟨_,_,hw,veiled_price (strip_mono H le_rfl (le_max_left B 0)) (le_max_right ..)⟩
lemma veiled_minus {A D : Row (Fink G L) (Fink G L)} : veiled (A-D)=veiled A-veiled D := by funext i j z; rcases i with i|i <;> rcases j with j|j <;> first|rfl|simp [veiled]

section matrix
variable (S : StepData c f)
variable (T : Forest S.ratio)

def indent (i : Lines G f 1) : Co c (Park G S.ratio.count) := let v:=splitCo S.ratio _ i; (v.1,.inl v.2)
def pict (G : Gauge) (S : StepData c f) := FreeResolvent.insertion (indent (G:=G) S)
lemma veiled_act (A : Row (Fink G S.ratio.count) (Fink G S.ratio.count)) :
    let E:= splitCo S.ratio (Loc G 1)
    let P:= pict G S
    (veiled A).acts c=P*repackM E.symm E.symm (A.acts c)*Pᵀ := by
  intro E P
  have he (i : Lines G f 1) x y : P (x,Sum.inl y) i= if E i=(x,y) then 1 else 0 := by
    have hz : indent S i=(x,.inl y) ↔ E i=(x,y) := by unfold indent E; simp [Prod.ext_iff]
    by_cases H : E i=(x,y); · simp only [P,pict,FreeResolvent.insertion,of_apply, hz.mpr H,H,if_true]
    simp [P,pict,FreeResolvent.insertion,mt hz.mp H,H]
  have hh (i : Lines G f 1) x y : P (x,Sum.inr y) i=0 := by unfold P pict FreeResolvent.insertion indent; simp
  ext ⟨x,i⟩ ⟨y,j⟩
  rcases i with i|i <;> rcases j with j|j
  · simp_rw [Matrix.mul_apply, Matrix.transpose_apply,he,Equiv.apply_eq_iff_eq_symm_apply E,mul_ite,ite_mul,mul_zero,mul_one,zero_mul,one_mul]; simp [repackM]; rfl
  all_goals simp [veiled,Matrix.mul_apply, Matrix.transpose_apply,hh, Row.acts]
lemma imprints_c : Function.Injective (indent S ∘ FreeResolvent.plant (G:=G) T) := by -- omit z
  apply Injective.comp (g:=indent S) _ (FreeResolvent.plant_inj T); intro i j hj; unfold indent at hj
  apply Equiv.injective (splitCo S.ratio (Loc G 1)); apply Prod.ext <;> simp only [Prod.mk.injEq,Sum.inl.injEq] at hj <;> tauto
def chargeS (G : Gauge) := FreeResolvent.insertion (indent S ∘ FreeResolvent.plant (G:=G) T)
lemma charges_at (G : Gauge) : chargeS S T G=pict G S*sprig S T G := by
  unfold sprig; rw [FreeResolvent.insertion.mul]
  ext i j; by_cases h : indent S (FreeResolvent.plant T j)=i <;> simp [chargeS,pict,FreeResolvent.insertion,h]

lemma mat_basis (v : FreeResolvent.Active G T→ℝ) : chargeS S T G*ᵥ v=lodgeP G S.ratio (sprig S T G*ᵥ v) 0 := by
  rw [charges_at,← Matrix.mulVec_mulVec]
  let E := splitCo S.ratio (Loc G 1)
  generalize hw : sprig S T G*ᵥ v=w; funext i
  rcases i with ⟨z,i|i⟩
  · rw [Matrix.mulVec,dotProduct,Finset.sum_eq_single (E.symm (z,i))]
    · simp only [pict, indent,FreeResolvent.insertion, E, Equiv.apply_symm_apply, of_apply,↓reduceIte,one_mul]; rfl
    · intro j _ hj
      have h : indent S j≠ (z,.inl i) := fun h=> hj (E.injective (by rw [Equiv.apply_symm_apply]; unfold indent at h; simp only [Prod.mk.injEq, Sum.inl.injEq] at h; exact Prod.ext h.1 h.2))
      simp [pict, FreeResolvent.insertion,h]
    simp
  · simp [lodgeP,Matrix.mulVec,dotProduct,pict,FreeResolvent.insertion,indent]
end matrix

-- coordinates for covariance contraction adapter. Works with std repeated
section branch
variable (P : Patch) (K : KernelChoices) (X : Repeated P.L)

lemma people (t : Train P.J) (H : P.Branches K G) {c f : Side} (h : f.val=c.val*P.L.val) :
    let S:= linked P K c f h; let F:= X.forest S.ratio; let I:=chargeS S F G
    let m := pink K.penalty t
    let R := FreeResolvent.treeMatrix G S F m
    (veiled (conditionalCov G X K t)).acts c = I* R⁻¹ * Iᵀ := by
  intro S F I m R
  let M:= conditionalCov G X K t
  let Q:= sprig S F G; let U:= pict G S
  let E:= splitCo S.ratio (Loc G 1)
  have he : M.acts c= repackM E E (FreeResolvent.covariance G S F m) := (conditional_truth G X K _ H).2 c f h
  rw [show (veiled (conditionalCov G X K t)).acts c=U*repackM E.symm E.symm (M.acts c)*Uᵀ from veiled_act S M,he,show repackM E.symm E.symm (repackM E E _)=FreeResolvent.covariance G S F m by ext i j; simp [repackM]]
  unfold FreeResolvent.covariance FreeResolvent.treeInverse FreeResolvent.resolve; rw [zero_smul,add_zero]; change U*(Q*R⁻¹*Qᵀ)*Uᵀ=I*R⁻¹*Iᵀ; rw [show I=U*Q from charges_at S F G,transpose_mul]; simp only [Matrix.mul_assoc]
end branch
end YM.RG08
