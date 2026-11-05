import YM.RG08.Room.Refresh
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Series photography for finite-dimensional chart germs, all positive jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I J:Type} [Fintype I] [Fintype J]
 set_option linter.unusedSectionVars false
abbrev Cellar (I:Type):= I→ℝ
abbrev Still (I:Type):=Cellar I→ℝ

def wedge (i:I) (f:Still I)(x:Cellar I):= (fderiv ℝ f x) (Pi.single i 1)
abbrev Pace {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {B:Type} [NormedAddCommGroup B][NormedSpace ℝ B](f:X→B):=ContDiffAt ℝ ω f 0

lemma Pace.wedge (i:I){f:Still I}(h:Pace f):Pace (wedge i f):=(h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const

lemma Pace.diff {f:Still I}(h:Pace f): ∀ᶠ x:Cellar I in 𝓝 0,DifferentiableAt ℝ f x:= (h.eventually (by simp)).mono (fun x hx=> hx.differentiableAt (by simp))
lemma wedge_eq (i:I){f g:Still I}(h:f=ᶠ[𝓝 0] g):wedge i f=ᶠ[𝓝 0] wedge i g:=(h.fderiv (𝕜:=ℝ)).mono (fun _ hx=>congrArg (fun z : Cellar I→L[ℝ]ℝ => z (Pi.single i 1)) hx)
lemma commutes (i j:I){f:Still I}(h:Pace f):wedge i (wedge j f)=ᶠ[𝓝 0] wedge j (wedge i f):= (h.eventually (by simp)).mono (fun x hx=>by
    have he (i j:I):wedge i (wedge j f) x= fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1):=by
      have hf:DifferentiableAt ℝ (fderiv ℝ f) x := (hx.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
      unfold wedge;rw [fderiv_clm_apply hf (differentiableAt_const _)]; simp
    rw [he,he,hx.isSymmSndFDerivAt_of_omega.eq])

-- height n, divide by n!, cross terms via ordinary derivative; left variation

def print (n:ℕ)(f:Still I):Inn I:= match n with
 | 0=>C (f 0)
 | n+1=>(n+1:ℝ)⁻¹ • ∑ i,X i * print n (wedge i f)
def flask (f:Still I):Port I:=PowerSeries.mk (fun n=>print n f)
lemma flute (f:Still I)(n:ℕ):tap n (flask f)=print n f:=PowerSeries.coeff_mk ..

lemma same (n:ℕ){f g:Still I}(h:f=ᶠ[𝓝 0] g):print n f=print n g:=by
 induction n generalizing f g with
 | zero=>simp only [print];rw [h.self_of_nhds]
 | succ n ih=>simp only [print];simp_rw [ih (wedge_eq _ h)] -- wedge Eq metavars maybe

lemma beats (n:ℕ)(f:Still I):(n+1:ℝ) • print (n+1) f=∑ i,X i*print n (wedge i f):=by rw [print,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]

lemma constant (n:ℕ)(a:ℝ):print n (fun _:Cellar I=>a)=if n=0 then C a else 0:=by
 induction n generalizing a with
 | zero=>rfl
 | succ n ih=>
    rw [if_neg (by omega),print];simp_rw [show ∀ i:I,wedge i (fun _=>a)=fun _=>0 from fun i=>by ext; simp [wedge],ih 0];simp
lemma flask_constant (a:ℝ):flask (fun _:Cellar I=>a)=liftInn (C a):=by ext n :1; rw [flask,PowerSeries.coeff_mk,constant,PowerSeries.coeff_C]

lemma print_add (n:ℕ){f g:Still I}(h:Pace f)(hp:Pace g): print n (f+g)=print n f+print n g:=by
 induction n generalizing f g with
 | zero=>simp [print]
 | succ n ih=>
    have he (i:I):wedge i (f+g)=ᶠ[𝓝 0] wedge i f + wedge i g:=( (Pace.diff h).and (Pace.diff hp)).mono (fun x ⟨hh,hj⟩=>by unfold wedge;rw [fderiv_add hh hj];rfl)
    simp only [print]; simp_rw [same n (he _),ih (Pace.wedge _ h) (Pace.wedge _ hp),mul_add,Finset.sum_add_distrib,smul_add]
lemma flask_add {f g:Still I}(h:Pace f)(hp:Pace g):flask (f+g)=flask f+flask g:=by ext e :1; simp [flask,print_add e h hp]
lemma slurry (s:Finset J)(f:J→Still I)(h:∀ j∈s,Pace (f j)): flask (∑ i∈s,f i)=∑ i∈s,flask (f i):=by
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty,show (0:Still I)=(fun _=>0) from rfl,flask_constant];simp
 | insert i s hi he=>rw [sum_insert hi,sum_insert hi,flask_add (h i (mem_insert_self i s)) (show Pace (s.sum f) by have ht : Pace (fun x=>∑ i∈s,f i x):=ContDiffAt.sum fun _ hv=>h _ (mem_insert_of_mem hv); simpa only [←Finset.sum_apply] using ht),he (fun _ hx=>h _ (mem_insert_of_mem hx))]

lemma oneEye (i:I){f:Still I}(h:Pace f)(n:ℕ):pderiv i (print (n+1) f)=print n (wedge i f):=by
 induction n generalizing f with
 | zero=>simp only [print,map_sum,pderiv_mul,pderiv_X,pderiv_C,Pi.single_apply,ite_mul,mul_zero,add_zero,one_mul,zero_mul,sum_ite_eq',if_pos (mem_univ _),Nat.cast_zero,zero_add,inv_one,one_smul]
 | succ n hx=>
   let z (k:I):=print (n+1) (wedge k f)
   apply untangle (by positivity: ((↑(n+1:ℕ)+1:ℝ))≠0)
   rw [←Derivation.map_smul,beats,map_sum]
   simp only [pderiv_mul,pderiv_X,Pi.single_apply,ite_mul,one_mul,zero_mul,hx (Pace.wedge _ h),Finset.sum_add_distrib,sum_ite_eq',if_pos (mem_univ i)]
   have he(k:I):print n (wedge i (wedge k f))=print n (wedge k (wedge i f)):=same n (commutes _ _ h)
   simp_rw [he,←beats,Nat.cast_add,Nat.cast_one,add_smul,one_smul];abel

theorem shutter (i:I){f:Still I}(h:Pace f):pin i (flask f)=PowerSeries.X*flask (wedge i f):=by
 ext e :1;rw [flight_apply]
 rcases e with _|e
 · simp [flask,print]
 simp [flask,oneEye i h,PowerSeries.coeff_succ_X_mul] -- lemma?
