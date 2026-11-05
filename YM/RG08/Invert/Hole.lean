import YM.RG08.Invert.Site
import YM.Next.FREE_KERNELS.Signed
/-!
 # Reflection on repeated roots. May use arbitrary Branch roots outside this
 remark but no accidental orientation inference for them. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Matrix
open Planned.PrimaryIntegral295 Carrier
open Stationary Analysis FreeResolvent Tree UVExt.Paths
open scoped BigOperators Topology Real Classical Matrix ContDiff
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}{S:StepData c f}

-- turn intertwiners
structure HeatV {α β:Type}(f: Equiv.Perm α)(g: Equiv.Perm β)(A:Matrix α β ℝ):Prop where
    yes x y:A x y=A (f x) (g y)
namespace HeatV
variable {α β γ:Type}{f:Equiv.Perm α}{g:Equiv.Perm β}{h:Equiv.Perm γ}{A B: Matrix α β ℝ}{C:Matrix β γ ℝ}
lemma plus (h:HeatV f g A)(hp:HeatV f g B): HeatV f g (A+B):=⟨fun i j=> congr_arg₂ (·+·) (h.yes i j) (hp.yes i j)⟩
lemma pay (h:HeatV f g A)(x:ℝ):HeatV f g (x•A):=⟨fun i j=> congr_arg (x * ·) (h.yes i j)⟩
lemma flipped (h:HeatV f g A): HeatV g f Aᵀ:= ⟨fun i j=> h.yes ..⟩
lemma chain [Fintype β] (hp:HeatV f g A)(hh:HeatV g h C): HeatV f h (A*C):= by
   constructor; intro i j; rw [Matrix.mul_apply,Matrix.mul_apply,← Equiv.sum_comp g (fun k=> A (f i) k*C k (h j))]; exact Finset.sum_congr rfl (fun k _=>congr_arg₂ (·*·) (hp.yes i k) (hh.yes k j))
lemma refund [Fintype α][DecidableEq α] {B: Matrix α α ℝ}(hp:HeatV f f B) : HeatV f f B⁻¹:= by
   have ht:B=B.submatrix f f:= funext fun i=>funext fun j=>hp.yes ..; refine ⟨fun i j=> congr_fun (congr_fun (show B⁻¹=B⁻¹.submatrix f f from ?_) _) _⟩; exact (congr_arg (fun v: Matrix α α ℝ=> v⁻¹) ht).trans (inv_submatrix_equiv B f f) -- lemma check
lemma unwarp [Fintype α][Fintype β](h:HeatV f g A)(v:β→ℝ): (A*ᵥ v) ∘ f=A *ᵥ (v ∘ g) := by
    funext i; simp only [Function.comp_apply,Matrix.mulVec,dotProduct]; rw [← Equiv.sum_comp g (fun k=>A (f i) k*v k)]; exact Finset.sum_congr rfl fun j _=> congr_arg (·*_) (h.yes i j).symm
lemma reflect_one [Fintype α][Fintype β] (h:∀ x:β→ℝ, (A *ᵥ x)∘f = A *ᵥ(x∘g)): HeatV f g A:= by
   refine ⟨fun i j=>?_⟩; have he:= congr_fun (h (Pi.single (g j) 1)) i; simp only [Function.comp_apply,mulVec,dotProduct,Pi.single_apply] at he; simp [mul_ite, g.injective.eq_iff] at he; exact he.symm
end HeatV

abbrev toneP (G:Gauge)(L:Side)(r:ℕ): Equiv.Perm (FreeResolvent.Slot G L r):= (((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr (mates L r) (Equiv.refl G.ColorIndex))).trans (Equiv.prodAssoc _ _ _))
lemma tone_on (a:Co L (TypeFace r))(i:G.ColorIndex): toneP G L r (ix a i)=ix (mate L r a) i:=rfl
lemma pigmentT {P:Matrix (Body r f) (Body r c) ℝ} (h:Twilight P): HeatV (toneP G f r) (toneP G c r) (tensor G P) := by
   refine ⟨fun i j=> ?_⟩; rcases i with ⟨i,k,a⟩; rcases j with ⟨j,l,b⟩; rw [show (i,k,a) =ix (i,k) a from rfl,show (j,l,b)=ix (j,l) b from rfl,tone_on,tone_on]; unfold tensor ix; simp only [Matrix.of_apply]; exact congr_arg (fun x=> if a=b then x else 0) (h (i,k) (j,l))

lemma mate_one (i:Axis)(x:Site L): mate L 1 (x,coord i)=(-x-step i,coord i):= by unfold mate brim; simp [coord]
lemma orientAs (x:form 1 L): reorient sigma x= -(x∘ mates L 1):= by
    funext i; rcases i with ⟨x',u⟩; obtain ⟨n,rfl⟩:=axisEquiv.surjective u
    change reorient sigma x (x',axisEquiv n)= -x (mate L 1 (x',coord n)); rw [reorient,Equiv.symm_apply_apply,mate_one]; change -x (-x'+0-step n,coord n) = _; rw [add_zero]
lemma signedAs (x:Link G L): orderTurn sigma x= -(x ∘ toneP G L 1) := by
    funext i; rcases i with ⟨y,i,v⟩; obtain ⟨k,rfl⟩:=axisEquiv.surjective i
    change flipCoords _ ℝ _ (_,coord k,_) = -x (toneP G L 1 (ix (y,coord k) v)); rw [tone_on,mate_one,flip_price]; change -x (_,coord k,v) = _; congr
lemma shadow_v (v:Train j)(k:ℝ)(h:0<k)(hp:4≤j): Twilight (K ((pink k v).acts L)):= by
   intro i b; let A:= K ((pink k v).acts L)
   have he (i:Co L (TypeFace 1)): reorient sigma (Pi.single (mates L 1 i) 1)=-(Pi.single i 1):= by rw [orientAs]; congr 1; funext k; unfold Function.comp; simp [Pi.single_apply,(mates L 1).injective.eq_iff]
   have ht:= apply_bill sigma k h hp v L (Pi.single (mates L 1 i) 1) (Pi.single (mates L 1 b) 1); dsimp only at ht; rw [he,he,mulVec_neg] at ht; simpa using! ht -- contraction simp
end YM.RG08.Invert
