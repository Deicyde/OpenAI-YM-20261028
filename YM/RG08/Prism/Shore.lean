import YM.RG08.Prism.Lung
import YM.RG08.Cell.Basis

/-! # Interior Gaussian economics certified from exact green RootField.
    Stays & (composed inverse) solve using joint Tanner.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Wilson Finset RG Precision Stationary RG08.Line Fold Drum Bloch Tree
open scoped Classical Topology Matrix ContDiff BigOperators
variable (G:Gauge){c f:Side}(S:StepData c f)(F:Forest S.ratio)(b v:Bed)

-- F.Free membership

def foamIndex (z:Key F G):Lines G f 1:=((z.1.val).1,coord z.1.val.2,z.2)
lemma foaming0:Injective (foamIndex G S F):=by
 rintro ⟨⟨⟨x,i⟩,h⟩,g⟩ ⟨⟨⟨y,j⟩,he⟩,c⟩ H
 change (x,axisEquiv i,g)=(y,axisEquiv j,c) at H; obtain ⟨rfl,U,rfl⟩:= Prod.mk.inj H |>.imp id (fun h=> Prod.mk.inj h)
 obtain rfl:=axisEquiv.injective U;rfl

def pore :Key F G↪Lines G f 1:=⟨foamIndex G S F,foaming0 G S F⟩
def iris : Matrix (Lines G f 1) (Key F G) ℝ:=of fun i j=> if i=pore G S F j then 1 else 0
lemma forth (x: Lines G f 1 →ℝ): (iris G S F)ᵀ *ᵥ x = x ∘ (pore G S F):= by ext j; simp [mulVec,dotProduct,iris,ite_mul]
lemma frost (i)(y:Key F G → ℝ): (iris G S F *ᵥ y) (pore G S F i)=y i:=by
 simp only [mulVec,dotProduct,iris,Matrix.of_apply,(pore G S F).injective.eq_iff,ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ, if_true]

def Visible (x:Lines G f 1): Prop:= (x.1,axisEquiv.symm x.2.1)∉F.trunks
lemma pale (i:Key F G): Visible G S F (pore G S F i):=by
 rcases i with ⟨⟨⟨v,j⟩,h⟩,x⟩; change (v,axisEquiv.symm (axisEquiv j)) ∉ _; rw [Equiv.symm_apply_apply];exact h
lemma frozen (i:Lines G f 1)(h: ¬ Visible G S F i)(y:Key F G→ℝ): (iris G S F *ᵥ y) i=0:=by
 have ht(j:Key F G):i≠ pore G S F j:=by rintro rfl;exact h (pale G S F j)
 unfold mulVec iris dotProduct;apply sum_eq_zero;intro j _;simp only [Matrix.of_apply,if_neg (ht j),zero_mul]
lemma away (x:Key F G →ℝ): onTree F (iris G S F *ᵥ x):=by
 intro a e he
 apply frozen
 unfold Visible
 dsimp only
 rw [show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply e.2]; simpa using he
lemma insideP : (iris G S F)ᵀ*iris G S F=1:= by
 apply perVec;intro w; rw [←mulVec_mulVec,forth]; simp only [one_mulVec];exact funext fun i=> frost G S F i w
lemma exposed (x:Lines G f 1): x∈ Set.range (pore G S F) ↔ Visible G S F x:=by
 constructor;· rintro ⟨i,rfl⟩;exact pale G S F i
 rintro h; exact ⟨(⟨(x.1,axisEquiv.symm x.2.1),h⟩, x.2.2), by change (_,axisEquiv (axisEquiv.symm x.2.1),x.2.2)=_;rw [axisEquiv.apply_symm_apply] ⟩
lemma sheltering (x:Lines G f 1→ℝ)(h:onTree F x): (iris G S F * (iris G S F)ᵀ) *ᵥ x=x:=by
 funext i; rw [← mulVec_mulVec]; by_cases he:Visible G S F i
 · obtain ⟨v,rfl⟩:= (exposed G S F i).mpr he; rw [frost,forth];rfl
 rw [frozen _ _ _ _ he];unfold Visible at he
 simpa only [show coord (axisEquiv.symm i.2.1)= _ from axisEquiv.apply_symm_apply i.2.1] using! (h i.2.2 (i.1,axisEquiv.symm i.2.1) (Classical.not_not.mp he)).symm

-- constitutive

def grace:Drum (Key F G) (Lines G f 1) (Lines G c 1):=⟨patron G (Precision.K (b.metric.acts f)),patron G (Precision.K (v.metric.acts c)),patron G (probe S),S.kernel.penalty,iris G S F⟩
variable {Γ:Matrix (Lines G f 1) (Lines G f 1) ℝ}
lemma totaled:(grace G S F b v).total=linePrecision G S b:=by
 rw [linePrecision,ink_add_general,ink_factor_general,patron_mul,patron_star];rfl
structure Given {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(b:Bed)(Γ:Matrix (Lines G f 1) (Lines G f 1) ℝ):Prop where
    range x : onTree F (Γ *ᵥ x)
    square x : onTree F x→Γ*ᵥ (linePrecision G S b *ᵥ x)=x
    sym : Γᵀ=Γ
lemma savior (H:Given F b Γ) : (iris G S F) * (iris G S F)ᵀ * Γ=Γ:= by apply perVec;intro x;rw [←Matrix.mulVec_mulVec];apply sheltering G S F _ (H.range x)
lemma installed (H:Given F b Γ): let U:=grace G S F b v;
    ((iris G S F)ᵀ*Γ*iris G S F)* U.inside=1:=by
 intro U
 have he:= savior G S F b H
 unfold inside; rw [totaled]; let D:=iris G S F
 have hz:Γ*(D*Dᵀ)=Γ:=by
    have hi:=congrArg Matrix.transpose he
    rw [Matrix.transpose_mul,H.sym,Matrix.transpose_mul,transpose_transpose] at hi;exact hi
 have hh :Γ*linePrecision G S b*D = D:=by
    apply perVec;intro x; simp only [← Matrix.mulVec_mulVec];exact H.square _ (away G S F x)
 change (Dᵀ*Γ*D)*(Dᵀ*linePrecision G S b*D)=_
 calc
  _= Dᵀ*(Γ*(D*Dᵀ))*(linePrecision G S b)*D:=by simp only [Matrix.mul_assoc]
  _=1:=by rw [hz, show Dᵀ*Γ*linePrecision G S b*D=Dᵀ*(Γ*linePrecision G S b*D) by simp only [Matrix.mul_assoc],hh,insideP]

def Licensed {I J U:Type}[Fintype I][Fintype J][Fintype U](A:Drum I J U)(Γ:Matrix J J ℝ): Prop:= A.g=Γ ∧ IsUnit A.inside.det
private lemma inter {I J U:Type}[Fintype I][Fintype J][Fintype U](A:Drum I J U)(Γ:Matrix J J ℝ)(h:∀ x,((A.vᵀ*Γ*A.v)*A.inside)*ᵥ x=x)(hY:A.v*A.vᵀ*Γ=Γ)(hv:Γᵀ=Γ): Licensed A Γ:=by
 have hinv : (A.vᵀ * Γ * A.v) * A.inside = 1 :=
   perVec fun x => by rw [one_mulVec]; exact h x
 have hright : Γ * (A.v * A.vᵀ) = Γ := by
   simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hv] using
     congrArg Matrix.transpose hY
 refine ⟨?_, Matrix.isUnit_det_of_left_inverse hinv⟩
 change A.v * A.inside⁻¹ * A.vᵀ = Γ
 rw [Matrix.inv_eq_left_inv hinv]
 calc
   A.v * (A.vᵀ * Γ * A.v) * A.vᵀ = (A.v * A.vᵀ * Γ) * (A.v * A.vᵀ) := by
     simp only [Matrix.mul_assoc]
   _ = Γ := by rw [hY, hright]
lemma gross (H:Given F b Γ): Licensed (grace G S F b v) Γ := by
 apply inter (grace G S F b v) Γ _ (savior G S F b H) H.sym
 have ht :∀ x, ((iris G S F)ᵀ*Γ*iris G S F * (grace G S F b v).inside)*ᵥ x=x:=fun x=> by rw [Prism.installed G S F b v H,one_mulVec]
 exact ht

private lemma inter2 {I J U:Type}[Fintype I][Fintype J][Fintype U](A:Drum I J U)(Γ:Matrix J J ℝ)(hl:Licensed A Γ)(hv:A.C.transpose=A.C)(hx:∀ x,A.N *ᵥ x=A.κ • (x - (A.D*(Γ * (A.κ • A.Dᵀ))) *ᵥ x)):
    A.Flourishes ∧ A.g=Γ:=⟨⟨hv,hl.2,perVec (fun x=>by rw [smul_mulVec, sub_mulVec,one_mulVec,Drum.mean,hl.1];exact hx x)⟩,hl.1⟩
-- again decEq U in identity: switch to ν+... = diagonal terms or perVec
lemma illuminated (H:Given F b Γ){L:Matrix (Body 1 f) (Body 1 c) ℝ}{η u:ℝ}{C:Clip}(hf:Floor b C f η u)(hi:Inputs S L (b.metric.acts f) (v.metric.acts c)):let U:=grace G S F b v;U.Flourishes ∧ U.g=Γ:=by
 intro U
 have hh := Cell.tree_station S.kernel G (b':=v) (b:=b) rfl F Γ H.square hi
 have he:= (stationed F L (b.metric.acts f) (v.metric.acts c) hi).1
 apply inter2 (grace G S F b v) Γ (Prism.gross G S F b v H)
 · have hs:(Precision.K (b.metric.acts f))ᵀ=Precision.K (b.metric.acts f):=by rw [Precision.K,transpose_mul,transpose_mul,transpose_transpose,hf.symmetric.1, ← Matrix.mul_assoc]
   change (patron G (Precision.K _))ᵀ=_;rw [←patron_star,hs];rfl
 intro x
 have hw: patron G (Precision.K (v.metric.acts c))= S.kernel.penalty • (1-patron G (probe S)*(Γ* (S.kernel.penalty • (patron G (probe S))ᵀ))):=by
   rw [Matrix.mul_smul,hh,← patron_mul,he,ink_sub,ink_id,ink_factor_general,sub_sub_cancel,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]
 change (patron G _)*ᵥ x = _
 rw [hw,smul_mulVec,sub_mulVec,one_mulVec]; rfl
end YM.RG08.Prism
