import YM.RG08.Camera.Flash

/-!
# Tensor (joint rank) extraction/injection, real jet factorial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function Forms
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I:Type}[Fintype I]

def billet (i:I):Cellar I:=Pi.single i 1

def deck (n:ℕ)(f:Still I) : Flake n I :=match n with
 | 0 => fun _=> f 0
 | n+1=>fun x=> (n+1:ℝ)⁻¹ * deck n (wedge (x 0) f) (Fin.tail x)
theorem deck_parley (f:Still I)(n:ℕ):parley (deck n f)=print n f:=by
 induction n generalizing f with
 | zero=>simp [parley,print,deck,word,Algebra.smul_def]
 | succ n hi=>
    rw [print,parley_cons];unfold deck
    -- unfold simplifies too much
    change ∑ i:I,X i *parley (fun x:Tape n I=>(n+1:ℝ)⁻¹ * deck n (wedge i f) x)=(n+1:ℝ)⁻¹ • ∑ i:I,X i*print n (wedge i f)
    have he (i:I):(fun x:Tape n I=>(n+1:ℝ)⁻¹ * deck n (wedge i f) x)=(n+1:ℝ)⁻¹ • deck n (wedge i f):=rfl
    simp_rw [he,parley_smul,hi,mul_smul_comm,Finset.smul_sum]

-- iterated derivative factorial on scaled diagonals

def glimpse (x:Cellar I):Inn I→ₐ[ℝ]ℝ:=MvPolynomial.aeval x
private lemma diagonal (x:Cellar I){f:Still I}(h:Pace f)(n:ℕ):glimpse x (print n f)=rfactor n * iteratedFDeriv ℝ n f 0 (fun _=>x):=by
 induction n generalizing f with
 | zero=>simp [glimpse,print,rfactor]
 | succ n ih=>
   let V:=iteratedFDeriv ℝ n (fderiv ℝ f) 0 (fun _=>x)
   have he:iteratedFDeriv ℝ (n+1) f 0 (fun _=>x)=V x:=iteratedFDeriv_succ_apply_right _
   have hi(i:I):iteratedFDeriv ℝ n (wedge i f) 0 (fun _=>x)=V (billet i):=by
     let L:=ContinuousLinearMap.apply ℝ ℝ (billet i)
     unfold wedge;change iteratedFDeriv ℝ n (L ∘ fderiv ℝ f) 0 _=_;rw [L.iteratedFDeriv_comp_left (h.fderiv_right (m:=ω) (by simp)) (mod_cast le_top)];rfl
   rw [print,_root_.map_smul,map_sum];simp_rw [_root_.map_mul, show ∀ i:I,glimpse x (X i)=x i from fun i=> MvPolynomial.aeval_X ..,ih (Pace.wedge _ h),hi]
   rw [he]
   rw [show V x= ∑ i,x i*V (billet i) from ?_]
   · rw [← earns n,smul_eq_mul,Finset.mul_sum,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;field_simp [show ((n:ℝ)+1)≠0 by positivity]
   have he : x =∑ i:I,x i • (billet i):=by funext i;simp [billet,Pi.single_apply,mul_ite,smul_eq_mul]
   conv_lhs=>arg 2;rw [he] -- V eval arg? index
   simp_rw [map_sum,_root_.map_smul,smul_eq_mul]

theorem glimpses {f:Still I}(h:Pace f)(n:ℕ)(x:Cellar I):MvPolynomial.eval x (tap n (flask f)) = (n.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _=>x):=by
 rw [flute];exact diagonal x h n

end YM.RG08.Camera
