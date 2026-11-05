import YM.RemainderComparison.Solos.Page
/-!
# From "each unit choice" stress bounds to genuine multilinearity

No assumptions on complex continuation of arbitrary conditional leaves,
nor integrability off-region. Costs on unit tests are BEFORE lifting by the
norm of each incoming slot (if already expanded complex-linear operator
apply convention). Infinite-dimensional unit test families allowed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Finset Filter Set Function
open Mosaic Marker
open scoped Topology BigOperators Classical
variable {θ : Type} (E : θ→Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)]
abbrev Space := ∀ i:θ, E i
variable {E}
namespace Scope
variable {i:θ} {a: E i}
-- actual scaling m(a), exact on the entire unit ball not just a corner.
def rank (a:E i):ℝ:= max 1 ‖a‖
omit [∀ i,NormedSpace ℝ (E i)] in
lemma one (x : E i):1 ≤ rank x:=le_max_left _ _
omit [∀ i,NormedSpace ℝ (E i)] in
lemma warm (x : E i):0<rank x:= zero_lt_one.trans_le (one x)
def tune (a: E i):Scope E i:= ⟨(rank a)⁻¹ • a,by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (warm a).le),←div_eq_inv_mul]; exact (div_le_one (warm a)).2 (le_max_right _ _)⟩
lemma fully (a:E i): rank a • (tune a).val=a:=by unfold tune; dsimp only; rw [smul_smul,mul_inv_cancel₀ (warm _).ne',one_smul]
omit [∀ i,NormedSpace ℝ (E i)] in
lemma own (x:Scope E i): rank x.val=1:=max_eq_left x.prop
lemma view (x:Scope E i): tune x.val=x:= Subtype.ext (by simp [tune,own x])
def chorus (x : Space E):Audited E:= fun i=> tune (x i)
def liftU (x:Audited E):Space E:= fun i=> (x i).val
lemma angle (x:Audited E): chorus (liftU x)=x:= funext fun i=> view (x i)
lemma vocal (x:Space E)(i:θ)(u:E i): chorus (Function.update x i u)= Function.update (chorus x) i (tune u):=by
    ext j; by_cases he:j=i
    · subst j; simp [chorus]
    simp only [chorus,Function.update_of_ne he]
end Scope
open Scope
variable (f:Audited E→ℝ)(p: Finset θ) (x:Space E)
def status (x:Space E) := ∏ i∈p,Scope.rank (x i)
def score (f:Audited E→ℝ) (p:Finset θ) (x:Space E):ℝ:= status p x * f (chorus x)
lemma volumes (x:Audited E): score f p (liftU x)= f x:=by unfold score; rw [Scope.angle]; unfold status; unfold liftU; rw [prod_eq_one (fun (i:θ) (_:i∈p)=>Scope.own (x i)),one_mul]
omit [∀ i,NormedSpace ℝ (E i)] in
lemma music (i:θ)(hi:i∈p)(a:E i) : status p (Function.update x i a)= Scope.rank a*status (p.erase i) x:=by
    unfold status; rw [← mul_prod_erase _ _ hi,Function.update_self]; apply congr_arg; refine prod_congr rfl fun j hj=>?_; rw [Function.update_of_ne (ne_of_mem_erase hj)]
-- no contribution for any zero argument anywhere, even though that one was clipped too
variable {f} (H:LinearP p f)
include H
lemma score_holds (z:Space E) (h:∀ i∈p,x i=z i) : score f p x=score f p z:= congr_arg₂ (·*·) (prod_congr rfl (fun i hi=> congr_arg Scope.rank (h i hi))) (H.frame _ _ (fun i hi=> congr_arg Scope.tune (h i hi)))
lemma immersion (i:θ)(hi:i∈p) (b c:E i)(z y: ℝ) :
   score f p (Function.update x i (z • b+y • c))= z* score f p (Function.update x i b)+ y*score f p (Function.update x i c):=by
   let a:=z • b+y • c; let Z:=z*Scope.rank b/(Scope.rank a); let Y:=y*Scope.rank c/(Scope.rank a)
   have he : (tune a).val= Z • (tune b).val+Y • (tune c).val:=by
       dsimp only [Z,Y]; rw [div_eq_inv_mul, div_eq_inv_mul]; rw [mul_smul,mul_smul, mul_smul,mul_smul y,Scope.fully, Scope.fully, ←smul_add]; rfl
   have ha:Scope.rank a ≠ 0:= (warm _).ne'
   change score f p _ =_; unfold score; rw [music p x i hi, music p x i hi, music p x i hi,Scope.vocal,Scope.vocal,Scope.vocal,H.draws i hi _ _ _ _ Z Y he]; unfold Z Y; unfold a at *
   field_simp
lemma aria (i:θ)(hi:i∈p): IsLinearMap ℝ (fun a:E i=> score f p (Function.update x i a)):=by
   constructor
   · intro a b; simpa only [one_smul,one_mul] using immersion p x H i hi a b 1 1
   intro r a; simpa only [smul_eq_mul,zero_smul,zero_mul,add_zero] using immersion p x H i hi a a r 0
end YM.RemainderComparison.Solos
