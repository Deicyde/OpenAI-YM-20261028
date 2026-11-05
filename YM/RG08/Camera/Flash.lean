import YM.RG08.Camera.Major

/-!
# Exponent & determinant identities from REAL chart germs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I J:Type}[Fintype I]

lemma flask_zero :flask (0:Still I)=0:=by change flask (fun _:Cellar I=>0)=0;rw [flask_constant,map_zero,map_zero]
lemma flask_neg {f:Still I}(h:Pace f):flask (-f) = -flask f:=by
 have he:Pace (-f):=h.neg
 have ht:=flask_add he h
 rw [neg_add_cancel,flask_zero] at ht; exact eq_neg_of_add_eq_zero_left ht.symm
lemma flask_sub {f g:Still I}(h:Pace f)(k:Pace g):flask (f-g)=flask f-flask g:=by have ha:Pace (-g):=k.neg; rw [sub_eq_add_neg,sub_eq_add_neg,flask_add h ha,flask_neg k]

lemma flask_scale {f:Still I}(hf:Pace f)(a:ℝ):flask (a • f) =a • flask f:=by
  let g:Still I:=fun _=>a
  change flask (g*f)=_
  rw [flask_mul (show Pace g from contDiffAt_const) hf,flask_constant,Algebra.smul_def,PowerSeries.algebraMap_apply];rfl
lemma flask_one :flask (1:Still I)=1:=by change flask (fun _:Cellar I=>1)=1; simpa using flask_constant (I:=I) 1
lemma slurry_prod (s:Finset J)(f:J→Still I)(h:∀ j∈s,Pace (f j)): flask (∏ i∈s,f i)=∏ i∈s,flask (f i):=by
 induction s using Finset.induction_on with
 | empty=>rw [prod_empty,prod_empty,flask_one]
 | insert i s hi he=>rw [prod_insert hi,prod_insert hi,flask_mul (h i (mem_insert_self i s)) (by simpa only [←Finset.prod_apply] using (contDiffAt_prod (t:=s) fun _ hv=>h _ (mem_insert_of_mem hv))),he (fun _ hx=>h _ (mem_insert_of_mem hx))]

lemma lamp (i:I):flask (fun (x:Cellar I)=>x i)=bump (rod i):=by
 ext n :1;rcases n with _|n
 · simp [bump,flask,print]
 have hx(k:I):wedge k (fun x:Cellar I=>x i) = fun _=> if i=k then (1:ℝ) else 0:=by
   let L:Cellar I→L[ℝ]ℝ:=ContinuousLinearMap.proj i
   ext x;change (fderiv ℝ L x) (Pi.single k 1)=_;rw [L.fderiv];simp [L,Pi.single_apply]
 change tap _ _=tap _ _;rw [flute,print];simp_rw [hx,constant];rcases n with _|n
 · rw [hopper];simp [tap,rod,liftInn,apply_ite,sum_ite_eq]
 rw [hopper];simp [tap,rod,liftInn]

lemma logarithm {p:Still I}(h:Pace p)(hp:p 0=1):rise (flask (Real.log ∘ p))=flask p:=by
 have ht:Pace (Real.log ∘ p):=(Real.contDiffAt_log.mpr (by simp [hp])).comp (0:Cellar I) h
 rw [←flask_heat ht (by simp [hp])];apply flask_same
 filter_upwards [h.continuousAt.eventually (lt_mem_nhds (by simp [hp]:0<p 0))] with x hx
 exact Real.exp_log hx

variable [Fintype J]
lemma flask_det {P:Cellar I→Matrix J J ℝ}(h:∀ i j,Pace (fun x=>P x i j)):flask (fun x=>Matrix.det (P x))=Matrix.det (Matrix.of (fun i j=>flask (fun x=>P x i j))):=by
 let f (b : Equiv.Perm J) (j:J) : Still I:=fun x=>P x (b j) j
 let g (b : Equiv.Perm J) := ∏ i: J, f b i
 let s (b : Equiv.Perm J):ℝ:= (Equiv.Perm.sign b:ℤ)
 have he(b:Equiv.Perm J):Pace (g b):=by simpa only [g,←Finset.prod_apply] using (contDiffAt_prod (t:=univ) (f:=f b) fun j _=>h (b j) j)
 have hh:(fun x=>Matrix.det (P x))=∑ b:Equiv.Perm J,s b • g b:=by
   funext x; rw [Matrix.det_apply',Finset.sum_apply];simp [s,g,f,Finset.prod_apply]
 rw [hh,slurry _ _ (fun i _=>show Pace (s i • g i) from (he i).const_smul (s i)),Matrix.det_apply']
 apply Finset.sum_congr rfl;intro i _; rw [flask_scale (he i)];unfold g;rw [slurry_prod _ _ (fun j _=>h _ _)]
 rw [Algebra.smul_def]; congr 1;exact map_intCast (algebraMap ℝ (Port I)) _ -- matrix.det' sign

set_option linter.unnecessarySimpa false in
lemma column (h:Strip I I)(hp:∀ i,Pace (h i))(i j:I):flask (wedge j (h i))=(gate (rescaleFields h)) i j:= (pin_out _ hp i).symm
lemma film_determinant (h:Strip I I)(hp:∀ i,Pace (h i)):
    flask (fun x=>(Matrix.of (fun i j=>wedge j (h i) x)).det)=(gate (rescaleFields h)).det:=by
 rw [flask_det (P:=fun x=>Matrix.of (fun i j=>wedge j (h i) x)) (fun i j=> Pace.wedge j (hp i))]; simp_rw [Matrix.of_apply,column h hp];rfl

end YM.RG08.Camera
