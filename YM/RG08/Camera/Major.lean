import YM.RG08.Camera.Shadow

/-! # Jet composition via field differential identity on both sides and zero-field testing. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I J:Type}[Fintype I][Fintype J]

abbrev Strip (I J:Type):= I → Still J
def roll (h:Strip I J)(x:Cellar J):Cellar I:=fun i=>h i x
lemma roll_pace {h:Strip I J}(hp:∀ i,Pace (h i)):Pace (roll h):=contDiffAt_pi.mpr hp

lemma wedge_pull (j:J){h:Strip I J}{f:Still I}(hp:∀ i,Pace (h i))(he:roll h 0=0)(hf:Pace f):
 wedge j (f ∘ roll h) =ᶠ[𝓝 0] ∑ i, (wedge i f ∘ roll h) * wedge j (h i):=by
 have ht:= (roll_pace hp).continuousAt.tendsto;rw [he] at ht
 have hb:=ht.eventually (Pace.diff hf)
 have hu : ∀ᶠ x: Cellar J in 𝓝 0,∀ i:I,DifferentiableAt ℝ (h i) x:=eventually_all.mpr (fun i=>Pace.diff (hp i))
 filter_upwards [hu,hb] with x hx hy
 have hw:DifferentiableAt ℝ (roll h) x:=differentiableAt_pi.mpr hx
 simp only [wedge,fderiv_comp x hy hw,ContinuousLinearMap.comp_apply,Pi.mul_apply, Finset.sum_apply,comp_apply]
 have hd : (fderiv ℝ (roll h) x) (Pi.single j 1)=∑ i, (fderiv ℝ (h i) x) (Pi.single j 1) • (Pi.single i 1 : Cellar I):=by
    funext i
    rw [show roll h=(fun x (i:I)=> h i x) from rfl,fderiv_pi hx];simp [Pi.single_apply]
 rw [hd,map_sum];apply Finset.sum_congr rfl;intro i _;rw [_root_.map_smul,smul_eq_mul,mul_comm]

def liftout {R:Type*}[CommRing R](f:Cab R):Cab R:=PowerSeries.mk (fun e=>tap (e+1) f)
lemma look {R:Type*}[CommRing R](f:Cab R)(e:ℕ):tap e (liftout f)=tap (e+1) f:=PowerSeries.coeff_mk ..
lemma bumpout {R:Type*}[CommRing R]{f:Cab R}(hf:tap 0 f=0):bump (liftout f)=f:=by
 ext i :1; change tap _ _=tap _ _;cases i
 · unfold tap at *; rw [bump,PowerSeries.coeff_zero_X_mul,hf]
 rw [hopper,look]

/-- `rescaleFields` = map in LOG-rescaled fields, keep coupling formal g. If h with no
constant germ, `g rescaleFields` is chart map on `g * X`. -/
def rescaleFields (h:Strip I J)(i:I):Port J:=liftout (flask (h i))
omit [Fintype I] in
lemma pin_out (j:J){h:Strip I J}(hp:∀ i,Pace (h i))(i:I):pin j (rescaleFields h i)=flask (wedge j (h i)):=by
 have he:=shutter j (hp i)
 ext e :1;rw [flight_apply];change MvPolynomial.pderiv j (tap e _)=tap e _;rw [rescaleFields, look];unfold tap;rw [←flight_apply,he];exact hopper (flask (wedge j (h i))) _

omit [Fintype I] in
lemma shade_out {h:Strip I J}(i:I):shade (rescaleFields h i)=0:=by
 ext e :1;change tap _ _=_;rw [seye,rescaleFields,look,←seye,shaded];simp [tap,liftInn]
omit [Fintype I] [Fintype J] in
lemma shade_pull (x:I→Port J)(h:∀ i, shade (x i)=0)(f:Port I):shade (belt x f)=shade f:=by
 -- mapping β to zero field → original coefficient specialization. no basis choices
 ext i :1;change tap _ _=tap _ _;rw [seye,seye]; change silvery (tap _ (spool (lug x) f))=_
 have he(p:Inn I): shade (lug x p)=liftInn (silvery p):=by
   induction p using MvPolynomial.induction_on with
   | C a=>unfold lug silvery;rw [aeval_C,aeval_C,PowerSeries.algebraMap_apply,shade,PowerSeries.map_C];exact congrArg PowerSeries.C (silvery (I:=J)|>.commutes a) -- C_a
   | add _ _ ha hb=>rw [map_add,map_add,map_add,map_add,ha,hb]
   | mul_X a i ha=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,_root_.map_mul,ha]; apply congrArg₂ (·*·) rfl;rw [lug,aeval_X,silvery,aeval_X,h,map_zero]
 rw [ships,map_sum];simp_rw [←seye,he]; unfold tap;rw [Finset.sum_eq_single i (by
   intro b hb hi;rw [PowerSeries.coeff_C,if_neg (by simp only [mem_range] at hb; omega)]) (by simp)];simp; exact (seye f i).symm

lemma carried (e:ℕ){h:Strip I J}{f:Still I}(hp:∀ i,Pace (h i))(he:roll h 0=0)(hf:Pace f):
 tap e (flask (f ∘ roll h))=tap e (belt (rescaleFields h) (flask f)):=by
 induction e using Nat.strong_induction_on generalizing f with
 | h e hi=>cases e with
   | zero=>
     rw [flute,rim,flute,print,print,aeval_C];rw [comp_apply,he];rfl
   | succ e=>
     have hg {f:Still I}(hf:Pace f): Pace (f ∘ roll h) := ContDiffAt.comp (g:=f) (0:Cellar J) (by rw [he];exact hf) (roll_pace hp)
     refine focus _ _ (fun j=>flask (wedge j (f ∘ roll h))) (fun j=>∑ i,belt (rescaleFields h) (flask (wedge i f))*flask (wedge j (h i))) ?_ (fun j=>shutter j (hg hf)) (fun j=>?_) _ ?_
     · rw [shade_pull _ shade_out,shaded,shaded,comp_apply,he]
     · rw [belt_chain,bump,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;rw [shutter i hf,_root_.map_mul,belt_g,pin_out _ hp,mul_assoc]
     intro j
     have ht(i:I) : Pace ((wedge i f ∘ roll h)*wedge j (h i)):= (hg (Pace.wedge i hf)).mul (Pace.wedge j (hp i))
     rw [flask_same (wedge_pull j hp he hf),slurry _ _ (fun i _=>ht i)]
     unfold tap;rw [map_sum,map_sum];apply Finset.sum_congr rfl;intro i _
     rw [flask_mul (show Pace (wedge i f ∘ roll h) from hg (Pace.wedge i hf)) (Pace.wedge j (hp i))]
     apply wired e (fun l hl=>hi l (by omega) (Pace.wedge i hf)) (fun _ _=>rfl)

theorem flask_comp {h:Strip I J}{f:Still I}(hp:∀ i,Pace (h i))(he:roll h 0=0)(hf:Pace f):flask (f ∘ roll h)=belt (rescaleFields h) (flask f):=PowerSeries.ext (fun i=>carried i hp he hf)

end YM.RG08.Camera
