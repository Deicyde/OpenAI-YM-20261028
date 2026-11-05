import YM.Contacts.Normal.Subtractions
import YM.Contacts.Score.Order
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Scores for absolute pointwise kernels

A tensor product on the algebraic space. Optical instruction acts on tests, evaluated at x, and
field channel at x is unchanged, then smul/add. Tensor product is only bookkeeping; in particular
an individually evaluated simple tensor might have no integrated meaning. We prove absolute
convergence for the canonical *sum* and for the precise residual combinations demanded, not by replacing
by absolute values of the raw summands. Use in ambient integrals with the norm/separation qualifications
in the reading.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory MultipleContact Submodule Ordered
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable (E A : Type*) {B C : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B] [CommRing C][Algebra ℂ C]
abbrev Score := TensorProduct ℂ (E → A) (Optical E)
variable {E A}
lemma inductionScore {f : Score E A → Prop} (x : Score E A) (h₀ : f 0) (h₁ : ∀ g s, f (g ⊗ₜ[ℂ] s)) (h₂ : ∀ x y,f x→ f y→ f (x+y)) : f x := by
   induction x using TensorProduct.induction_on with
   | zero=>exact h₀
   | tmul f g=> exact h₁ ..
   | add x y hx hy=>exact h₂ _ _ hx hy

def instructionScore (E A : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CommRing A] [Algebra ℂ A] (f : Optical E) : Score E A := 1 ⊗ₜ[ℂ] f
lemma instructions (a b: Optical E) : instructionScore E A (a*b)= instructionScore E A a*instructionScore E A b:= by simp [instructionScore,Algebra.TensorProduct.tmul_mul_tmul]

def action (x : E) (p : SmoothTests E) : Score E A →ₗ[ℂ] A := TensorProduct.lift
  { toFun f:= {
       toFun g:= ((g p).val x) • f x
       map_add' a b:= add_smul ((a p).val x) ((b p).val x) (f x)
       map_smul' t a:= smul_assoc t ((a p).val x) (f x) },
    map_add' a b:= LinearMap.ext fun g=> smul_add ((g p).val x) (a x) (b x),
    map_smul' t f:= LinearMap.ext fun g=> smul_comm ((g p).val x) t (f x) }
lemma action_tmul (x : E) (p : SmoothTests E) (f : E→ A) (s : Optical E) : action x p (f ⊗ₜ[ℂ] s)=(s p).val x • f x:= TensorProduct.lift.tmul ..
lemma action_add_test (x:E) (p q: SmoothTests E) (f : Score E A) : action x (p+q) f=action x p f+ action x q f := by
  induction f using inductionScore with
  | h₀=>simp
  | h₁ f g=> simp only [action_tmul,map_add]; exact add_smul ..
  | h₂ x y hx hy=> simp only [map_add,hx,hy]; abel
lemma action_smul_test (x:E)(t:ℂ)(p:SmoothTests E)(f : Score E A) : action x (t • p) f=t • action x p f := by
  induction f using inductionScore with
  | h₀=>simp
  | h₁ f g=> simp only [action_tmul,map_smul]; exact smul_assoc t _ _
  | h₂ x y hx hy=> simp only [map_add,hx,hy,smul_add]
def under (x : E) (f : Score E A) : SmoothTests E →ₗ[ℂ] A where
   toFun p:= action x p f
   map_add' p q:= action_add_test x p q f
   map_smul' t p:= action_smul_test x t p f
lemma takeRight (x:E) (p:SmoothTests E) (h : Score E A) (f : Optical E) : action x p (h*instructionScore E A f)= action x (f p) h:=by
   induction h using inductionScore with
   | h₀=>simp
   | h₁ a b=> rw [instructionScore,Algebra.TensorProduct.tmul_mul_tmul,mul_one]; simp only [action_tmul]; rfl
   | h₂ a b ha hb=> simp only [add_mul,map_add,ha,hb]

/-- Evaluate several points in the score interpretation with a common field-channel
transform; no smoothness here assumed of fields, transformation need only be linear. -/
def evaluateHeads (f : E → A →ₗ[ℂ] B) : (E → A) →ₗ[ℂ] (E→B):= LinearMap.pi fun i=> (f i).comp (LinearMap.proj i)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma evaluates (f : E → A →ₗ[ℂ] B)(g x) : evaluateHeads f g x= f x (g x):=rfl

def reshape (f : E → A →ₗ[ℂ] B) : Score E A →ₗ[ℂ] Score E B:= TensorProduct.map (evaluateHeads f) (.id)
@[simp] lemma reshape_tape (f : E→ A →ₗ[ℂ] B) (p:E→ A) (U:Optical E) : reshape f (p ⊗ₜ[ℂ] U) = evaluateHeads f p ⊗ₜ[ℂ] U:= TensorProduct.map_tmul ..
lemma action_reshape (f : E → A →ₗ[ℂ] B) (x : E) (v : Score E A)(g : SmoothTests E) : action x g (reshape f v)= f x (action x g v):= by
  induction v using inductionScore with
  | h₀=>simp
  | h₁ g p=> rw [reshape_tape, action_tmul, action_tmul,map_smul]; rfl
  | h₂ g p hg hp=> simp only [map_add, hg,hp]
lemma reshape_id (p : Score E A) : reshape (fun _=> LinearMap.id) p=p := by
  induction p using inductionScore with
  | h₀=>simp
  | h₁ g p=> rw [reshape_tape]; rfl
  | h₂ g h hx hy=> simp only [map_add,hx,hy]
lemma reshape_composes (f : E→ A→ₗ[ℂ] B) (h : E→ B →ₗ[ℂ] C)(p : Score E A) : reshape h (reshape f p)=reshape (fun x=>(h x).comp (f x)) p:=by
  induction p using inductionScore with
  | h₀=>simp
  | h₁ g p=> rw [reshape_tape,reshape_tape,reshape_tape]; rfl
  | h₂ g h hx hy=> simp only [map_add,hx,hy]
lemma reshape_add (f g : E → A →ₗ[ℂ] B) (p : Score E A) : reshape (f+g) p = reshape f p + reshape g p:= by
   induction p using inductionScore with
   | h₀ => simp
   | h₁ x y=> simp only [reshape_tape,← TensorProduct.add_tmul]; rfl
   | h₂ x y hx hy => simp only [map_add,hx,hy]; abel
lemma reshape_zero (p : Score E A) : reshape (0:E→ A→ₗ[ℂ] B) p=0:=by
   have h:= reshape_add (0:E→ A→ₗ[ℂ] B) (0:E→ A→ₗ[ℂ] B) p; rw [add_zero] at h; exact add_eq_left.mp h.symm
lemma reshape_instruction (f : E→ A→ₗ[ℂ] B) (U : Score E A) (p : Optical E) :
    reshape f (U*instructionScore E A p)=reshape f U*instructionScore E B p:=by
   induction U using inductionScore with
   | h₀=>simp
   | h₁ x y=> unfold instructionScore; simp only [reshape_tape, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
   | h₂ x y hx hy=> simp only [add_mul,map_add,hx,hy]

def retag (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a : A →ₐ[ℂ] B) : Score E A →ₐ[ℂ] Score E B where
   __:= reshape (fun _=>a.toLinearMap)
   map_zero':= map_zero (reshape (fun _:E=>a.toLinearMap))
   map_mul' f g:= by
      let H:Score E A→ₗ[ℂ] Score E B:=reshape (fun _=>a.toLinearMap); change H (f*g)=H f*H g
      induction f using inductionScore with
      | h₀=>simp
      | h₁ f k=>
        induction g using inductionScore with
        | h₀=>simp
        | h₁ g l=>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, H, reshape_tape]; congr; funext x; exact map_mul a _ _
        | h₂ f g hx hy=> simp only [mul_add,map_add,hx,hy]
      | h₂ f g hx hy=> simp only [add_mul,map_add,hx,hy]
   map_one':= by change reshape _ ((1:E→A) ⊗ₜ[ℂ] (1:Optical E))= _; rw [reshape_tape]; change _= (1:E→B) ⊗ₜ[ℂ] (1:Optical E); congr; funext x; exact map_one a
-- commutes via map_smul_one
   commutes' r:= by
      let Q:=(reshape (fun _:E=>a.toLinearMap) : Score E A →ₗ[ℂ] Score E B); change Q ((algebraMap ..) r)=_
      have he:Q 1=1:= by change reshape _ ((1:E→A) ⊗ₜ[ℂ] (1:Optical E))= _; rw [reshape_tape]; change _= (1:E→B) ⊗ₜ[ℂ] (1:Optical E); congr; funext x; exact map_one a
      rw [Algebra.algebraMap_eq_smul_one,map_smul,he,Algebra.algebraMap_eq_smul_one]
lemma retags (f : A →ₐ[ℂ] B) (a : Score E A) : retag E f a= reshape (fun _=>f.toLinearMap) a:=rfl
lemma retag_rules (f : A →ₐ[ℂ] B)(p : Optical E) : retag E f (instructionScore E A p) = instructionScore E B p:= by
  rw [retags,instructionScore,reshape_tape]; unfold instructionScore; congr; funext i; exact map_one f
lemma retag_product {I : Type*} (s : Finset I)(x:I → Score E A)(f : A →ₐ[ℂ] B):
     retag E f (Ordered.product s x) = Ordered.product s (fun i=> retag E f (x i)):= Ordered.mapped s x (retag E f).toRingHom
end YM.Contacts.Normal
