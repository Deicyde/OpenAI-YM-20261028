import YM.RG08.Hatch.Nest
import YM.RG08.Quarry.Looming

/-!
# Rooted MARK contours, charge separately in common g & reference TEST.
All real first. fpst input kernels CREATE Ward laws, for scalar too. Mom kme
receipt not needed for algebraic translation since stronger stance=Sings.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Hatch
open scoped Topology BigOperators ENNReal Classical PowerSeries
variable {I J:Type}{n d l e:ℕ}{σ C:ℝ}{h:0<σ}

def summit (P:Pack n I)(f:Pearl)(a:Tray I):Dig:=Gallery.volume (during f P) a
def crown (l:ℕ)(P:GrainS I)(f:Pearl)(i:ℕ)(a:Tray I):Dig:=∑ k∈range (l+i+1),summit (P i k) f a
def mint (l:ℕ)(P:GrainS I)(f:Pearl)(a:Tray I):Dig:=PowerSeries.mk (fun e=>∑ i∈range (e+1),tap (e-i) (crown l P f i a))
lemma told [Fintype I](P:GrainS I)(f:Pearl)(a:Tray I): breath a.get (Trickle.mark l P f)=mint l P f a:=by
 ext n:1;change tap _ _=tap _ _;rw [pulses];unfold mint tap;rw [PowerSeries.coeff_mk];apply Finset.sum_congr rfl;intro j _
 unfold Trickle.mark Trickle.shine crown;simp only [PowerSeries.coeff_mk,map_sum,summit,Gallery.vat];rfl

def bond (F:Pack n I)(f:Pearl)(x:I→Dig)(e:ℕ):ℝ:=∑' t:Tape n I,F t f * tap e (fret x t)
def awaken (l:ℕ)(P:GrainS I)(f:Pearl)(x:I→Dig):Dig:=PowerSeries.mk fun e=>∑ i∈range (e+1),∑ k∈range (l+i+1), bond (P i k) f x (e-i)
lemma wet (P:Pack n I)(f:Pearl)(x:Tray I)(e:ℕ):bond P f x.get e=tap e (summit P f x):=by
 rw [summit,Gallery.volume,tap,map_sum,bond,tsum_eq_sum (s:=desks x.base n) (fun i hi=> by rw [desks_out x.shut hi]; simp [tap])]
 apply Finset.sum_congr rfl;intro i _;rw [PowerSeries.coeff_smul,smul_eq_mul];rfl
lemma woken (P:GrainS I)(f:Pearl)(x:Tray I):awaken l P f x.get=mint l P f x:=by ext e :1; rw [awaken,mint,PowerSeries.coeff_mk,PowerSeries.coeff_mk];apply sum_congr rfl;intro _ _;unfold crown tap; rw [map_sum];simp_rw [wet]
lemma hat [Fintype I](x:I→Dig)(P:GrainS I)(f:Pearl):breath x (Trickle.mark l P f)=awaken l P f x:=by
 let a:Tray I:=⟨univ,x,fun _ h=>False.elim (h (mem_univ _))⟩; exact (told (l:=l) P f a).trans (woken ..|>.symm)
lemma broomAwake [Fintype J] (u:I→J){P:GrainS I}(ht:∀ e n,∃ L:Jetty.Loom I,∃ (d:ℕ)(σ:ℝ)(h:0<σ)(C:ℝ),Lyrics (P e n)∧Sings L d h (P e n) C)(f:Pearl)(x:J→Dig):
 awaken l (fun i _=>broom u (P i _)) f x=awaken l P f (x ∘ u):=by
 ext e :1;rw [awaken,awaken,PowerSeries.coeff_mk,PowerSeries.coeff_mk];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro n _
 obtain ⟨L,d,σ,h,C,hv,hy⟩:=ht i n
 let F:=P i n
 let q(y:Tape n J):=tap (e-i) (fret x y)
 let z(t:Tape n I):Tape n J:=u ∘ t
 rw [bond,bond,tsum_fintype]; unfold broom;simp_rw [←tsum_mul_right]
 let D(j:Tape n J)(t:Tape n I):= (if j=z t then F t f else 0)*q j
 have he(j):Summable (D j):= ((portion hv hy f (fun t:Tape n I=> j=z t)).of_norm).mul_right _
 change (∑ j:Tape n J,∑' t,D j t)=_
 have hh (t:Tape n I): (∑ j:Tape n J,D j t)=F t f * tap (e-i) (fret (x ∘ u) t):=by
    unfold D; simp only [ite_mul,zero_mul,sum_ite_eq',mem_univ,if_pos];rfl
 rw [← Summable.tsum_finsetSum (fun j (_:j∈(univ:Finset (Tape n J)))=>he j)]; exact tsum_congr hh

-- cost-independent g variable, constant FPS assignments bound testimony.
abbrev kiosk (x:I→ℝ):I→Dig:=fun i=>PowerSeries.C (x i)
lemma gava (x:I→ℝ)(f:Inn I): MvPolynomial.aeval (kiosk x) f= PowerSeries.C (MvPolynomial.eval x f):=by
 induction f using MvPolynomial.induction_on with
 | C y=>simp
 | add _ _ hi hj=>simp only [map_add,hi,hj]
 | mul_X f i hi=>rw [_root_.map_mul,_root_.map_mul,hi,_root_.map_mul,aeval_X,eval_X]
lemma tutor (x:I→ℝ)(f:Port I)(e:ℕ):tap e (breath (kiosk x) f)=MvPolynomial.eval x (tap e f):=by
 rw [pulses,sum_eq_single_of_mem e (mem_range.mpr (by omega)) (fun i hi hx=>?_)]
 · simp_rw [Nat.sub_self,gava,tap,PowerSeries.coeff_C];rfl
 rw [gava,tap,PowerSeries.coeff_C,if_neg];simp only [mem_range] at hi;omega
lemma lamp (f g:Port I)(h:∀ x:I→ℝ,breath (kiosk x) f=breath (kiosk x) g):f=g:=by
 ext e :1;apply MvPolynomial.funext;intro x
 exact (tutor x _ e).symm.trans ((congrArg (tap e) (h x)).trans (tutor x _ e))
end YM.RG08.Weald
