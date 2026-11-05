import YM.RG08.Camera.Shim

/-! # Jets of real-chart products and exponentials -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I :Type} [Fintype I]

def silvery : Inn I→ₐ[ℝ] ℝ:=MvPolynomial.aeval (fun _=>0)
def shade : Port I→+*PowerSeries ℝ:=PowerSeries.map silvery.toRingHom
omit [Fintype I] in
lemma seye (f:Port I)(e:ℕ):tap e (shade f)=silvery (tap e f):=PowerSeries.coeff_map ..
lemma shaded (f:Still I):shade (flask f)=liftInn (f 0):=by
 ext i :1;change tap _ _=_;rw [seye,flute];cases i with
 | zero=>simp [print,silvery]
 | succ i=>simp [print,_root_.map_smul,map_sum,silvery]

abbrev bump {R:Type*}[CommRing R](p:Cab R):Cab R:=PowerSeries.X*p
omit [Fintype I] in
lemma hopper {R:Type*}[CommRing R](p:Cab R)(e:ℕ):tap (e+1) (bump p)=tap e p:=by simp [tap,bump,PowerSeries.coeff_succ_X_mul]

/-- Jet step by one-derivative movement and zero field location; lowers coupling order
*even in the presence* of field-dependent constant-in-g zero-point correction. -/
lemma focus (s t:Port I)(v w:I→Port I)(he:shade s=shade t)(hv:∀ i,pin i s=bump (v i))(hw:∀ i,pin i t=bump (w i))(n:ℕ)
    (hl:∀ i:I,tap n (v i)=tap n (w i)):tap (n+1) s = tap (n+1) t:=by
 have hf(i:I):pderiv i (tap (n+1) s-tap (n+1) t)=0:=by
    rw [map_sub,tap,tap,←flight_apply,←flight_apply,hv i,hw i];change tap (n+1) _-tap (n+1) _=_;rw [hopper,hopper,hl i,sub_self]
 -- derivative zero ⇒ independent of all fields, hence determined by silvery
 let d:=tap (n+1) s-tap (n+1) t
 have hh : MvPolynomial.aeval (X (R:=ℝ) (σ:=I)) d = MvPolynomial.aeval (fun (_:I)=> (0:Inn I)) d :=nearby univ (fun i _=>hf i) (by simp)
 have ht (d:Inn I): MvPolynomial.aeval (fun (_:I)=> (0:Inn I)) d=C (silvery d):=by
    induction d using MvPolynomial.induction_on with
    | C a=>simp [silvery]
    | add _ _ hi hj=>rw [map_add,map_add,map_add,hi,hj]
    | mul_X p i hi=>rw [_root_.map_mul,aeval_X,mul_zero,_root_.map_mul,_root_.map_mul,silvery,aeval_X,map_zero,mul_zero]
 have H:d=0:=by
   simpa only [aeval_X_left_apply,ht,d,map_sub,←seye,he,sub_self,map_zero] using hh
 exact sub_eq_zero.mp H

lemma wedge_side (i:I){f g:Still I}(h:Pace f)(he:Pace g): wedge i (f*g)=ᶠ[𝓝 0] f*wedge i g+g*wedge i f:= ((Pace.diff h).and (Pace.diff he)).mono (fun x hh=>by unfold wedge;rw [fderiv_mul hh.1 hh.2];rfl)

lemma combines (i:ℕ){f g:Still I}(hf:Pace f)(hg:Pace g):tap i (flask (f*g))=tap i (flask f*flask g):=by
 induction i generalizing f g with
 | zero=>simp only [tap,PowerSeries.coeff_zero_eq_constantCoeff,map_mul];simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,flask,PowerSeries.coeff_mk,print,Pi.mul_apply,map_mul]
 | succ n ih=>
    refine focus _ _ (fun i=>flask (wedge i (f*g))) (fun i=>flask f*flask (wedge i g)+flask g*flask (wedge i f)) (by rw [_root_.map_mul,shaded,shaded,shaded, ←_root_.map_mul];rfl) (fun i=>shutter i (hf.mul hg)) (fun i=>?_) _ ?_
    ·
      rw [Derivation.leibniz,shutter _ hf,shutter _ hg]; unfold bump; simp only [smul_eq_mul];ring
    intro i; have ht : Pace (f*wedge i g):=hf.mul (Pace.wedge i hg); have he : Pace (g*wedge i f):=hg.mul (Pace.wedge i hf);rw [flute,same n (wedge_side i hf hg),print_add n ht he,←flute,←flute,ih hf (Pace.wedge i hg),ih hg (Pace.wedge i hf)];unfold tap;rw [map_add]

lemma flask_mul {f g:Still I}(hf:Pace f)(hg:Pace g):flask (f*g)=flask f*flask g:=PowerSeries.ext (fun i=>combines i hf hg)
lemma flask_same {f g:Still I}(h:f=ᶠ[𝓝 0] g):flask f=flask g:=by ext e :1; change tap _ _=tap _ _;rw [flute,flute,same _ h]
lemma wedge_heat (i:I){f:Still I}(hf:Pace f): wedge i (Real.exp ∘ f)=ᶠ[𝓝 0] (Real.exp ∘ f)*wedge i f:= (Pace.diff hf).mono (fun x h=>by unfold wedge comp;rw [fderiv_exp h];rfl)

lemma bright (i:ℕ){f:Still I}(hf:Pace f)(ha:f 0=0):tap i (flask (Real.exp ∘ f))=tap i (rise (flask f)):=by
 have hp:=Real.contDiff_exp.contDiffAt.comp (g:=Real.exp) 0 hf
 have he:tiny (flask f):=by unfold tiny;simp [flask,print,ha]
 induction i using Nat.strong_induction_on with
 | h i hi=>cases i with
   | zero=>simp [tap,flask,print,ha,rise_before]
   | succ i=>
     refine focus _ _ (fun j=>flask (wedge j (Real.exp ∘ f))) (fun j=>rise (flask f)*flask (wedge j f)) (by rw [shaded];unfold shade;rw [rise_map]; rw [←shade,shaded,ha,map_zero,rise_zero];simp [ha]) (fun i=>shutter i hp) (fun j=>?_) _ ?_
     · rw [pin,lift_rise _ he,show flight (pderiv j) (flask f)=_ from shutter j hf,bump];ring
     intro j; rw [flask_same (wedge_heat j hf),flask_mul hp (Pace.wedge j hf)]
     apply wired i (fun l hl=>hi l (by omega)) (fun _ _=>rfl)

lemma flask_heat {f:Still I}(hf:Pace f)(h:f 0=0):flask (Real.exp ∘ f)=rise (flask f):=PowerSeries.ext (fun i=>bright i hf h)

end YM.RG08.Camera
