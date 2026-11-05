import YM.RG08.Weald.Fields
import YM.RG08.Billet.Choice

/-! # Adjacent substitution shuttles on rooted sparse observables.
Variables g relative to OWN measure and trajectory. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Clef
open Function Finset Jetty Skiff Lattice Isles Forms Pert.Bulk Filter
open Room Gallery Camera MvPolynomial Glyph Weald Quarry Billet Nacre
open scoped Topology BigOperators PowerSeries Classical Matrix
set_option backward.isDefEq.respectTransparency false
variable {I:Type}(w:ℕ→ℝ)

def gear (x:Essence)(p:Dig):Dig:=p ⌾ tilt x
def gA (x:Essence) : Dig →ₐ[ℝ] Dig where
 toFun:=gear x
 map_mul' p q:= Billet.fees _ _ (tassel x) -- etc
 map_add' p q:=PowerSeries.subst_add (tassel x) p q
 map_zero':=by unfold gear;change PowerSeries.subst (tilt x) 0=(0:Dig); rw [show (0:Dig)=PowerSeries.C 0 by simp];exact PowerSeries.subst_C ..
 map_one':=by change PowerSeries.subst _ (PowerSeries.C (1:ℝ))=(1:Dig);simpa using PowerSeries.subst_C (a:=tilt x) 1
 commutes' p := by
    rw [PowerSeries.algebraMap_apply]; simp only [Algebra.algebraMap_self_apply]
    exact PowerSeries.subst_C ..
lemma gA_x (x:Essence): gA x PowerSeries.X=tilt x:=xrank (tassel x)
abbrev react := gA (ratio w)
abbrev undo := gA (fringe w)
lemma gA_inv (q:Dig): react w (undo w q)=q:=by
 change (q ⌾ tilt (fringe w)) ⌾ tilt (ratio w)=q
 rw [show ((q ⌾ tilt (fringe w)) ⌾ tilt (ratio w))=q ⌾ (tilt (fringe w) ⌾ tilt (ratio w)) from PowerSeries.subst_comp_subst_apply (tassel _) (tassel _) _,homebound];exact PowerSeries.X_subst q

def via (x:I→Dig)(i:I):Dig:=undo w ((ratio w)⁻¹*x i)
def shuttle (x:Tray I):Tray I where
 base:=x.base
 get:=via w x.get
 shut:=fun i h=>by unfold via;rw [x.shut i h,mul_zero,map_zero]
lemma returning (x:I→Dig)(i:I):react w (via w x i)=(ratio w)⁻¹*x i:=gA_inv w _
lemma frieze {n:ℕ}(x:I→Dig)(t:Tape n I):react w (fret (via w x) t)=(ratio w)⁻¹ ^ n * fret x t:=by
 unfold fret;rw [map_prod];simp_rw [returning];rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
lemma gentle (f g:Dig)(e:ℕ)(h:∀ j≤e,tap j f=tap j g):tap e (react w f)=tap e (react w g):=by
 unfold react tap gA gear;change PowerSeries.coeff e (f ⌾ tilt (ratio w))=PowerSeries.coeff e (g ⌾ tilt (ratio w));rw [Billet.lo,Billet.lo];apply sum_congr rfl;intro j hj;unfold Room.tap at h;rw [h j (by simpa using hj)] -- tap h mismatch
abbrev Gpow (e:ℕ)(x : Dig):= PowerSeries.X ^e*x
lemma gpow_t (i e:ℕ)(x:Dig)(h:e ≤ i):Room.tap i (Gpow e x)=Room.tap (i-e) x:=by unfold Gpow Room.tap; rw [PowerSeries.coeff_X_pow_mul',if_pos h]
lemma gpow_off (i e:ℕ)(x:Dig)(h:i < e):Room.tap i (Gpow e x)=0:=by unfold Gpow Room.tap;rw [PowerSeries.coeff_X_pow_mul',if_neg (by omega)]
lemma flapped (e b:ℕ)(x:ℕ→Dig)(h:e≤b):
 Room.tap e (∑ i∈range (b+1),Gpow i (x i))=∑ i∈range (e+1),Room.tap (e-i) (x i):=by
 unfold Room.tap; rw [map_sum]; rw [← sum_subset (range_mono (show e+1≤b+1 from by omega)) (fun i _ hi=>gpow_off _ _ _ (by simp at hi;omega))]
 apply sum_congr rfl;intro i hi;exact gpow_t _ _ _ (by simpa using hi)

lemma exponents (f:Port I)(x:I→Dig)(e i:ℕ)(h:e ≤ i): tap e (breath x f)=tap e (∑ j∈range (i+1),Gpow j (MvPolynomial.aeval x (tap j f))):=by rw [pulses,flapped _ _ _ h]
lemma minted (l:ℕ)(P:GrainS I)(x:Tray I)(y:Pearl)(e i:ℕ)(h:e ≤ i):tap e (Weald.mint l P y x)=tap e (∑ j∈range (i+1),Gpow j (Weald.crown l P y j x)):=by unfold Weald.mint tap;rw [PowerSeries.coeff_mk];exact (flapped _ _ _ h).symm --]

variable [Fintype I]
lemma octave (x:I→Dig)(f:Still I)(e:ℕ):react w (MvPolynomial.aeval (via w x) (Camera.print e f))=(ratio w)⁻¹ ^e * MvPolynomial.aeval x (Camera.print e f):=by
 induction e generalizing f with
 | zero=>simp only [Camera.print,aeval_C,pow_zero,one_mul,AlgHom.commutes]
 | succ n ih=>
    simp_rw [Camera.print,_root_.map_smul,map_sum,_root_.map_mul,aeval_X,returning, ih]
    rw [mul_smul_comm,pow_succ', Finset.mul_sum];refine congrArg _ (sum_congr rfl fun i _=>?_);ac_rfl
/-- Normalized chart coordinates around the identity, resp. constant rotation origins.
No differentiation regularity premise since only uses homogeneous jet formula and fps logs.
Each output field scaled with $1/\rho$, including even field-independent branch of h(x)
where the extra 1 source amplitude is explicit in the normalization.
-/
lemma scales (x:I→Dig)(f:Still I): react w (breath (via w x) (eye f))= (ratio w)⁻¹ * breath x (eye f):=by
 ext e:1;change tap e _=tap e _
 rw [gentle w _ _ e (fun j hj=>exponents (eye f) _ _ _ hj), wired e (d:=∑ j∈range (e+1),Gpow j (MvPolynomial.aeval x (tap j (eye f)))) (fun _ _=>rfl) (fun i hi=>exponents (eye f) _ _ _ hi)] -- wired args
 apply congrArg
 rw [map_sum,Finset.mul_sum];apply sum_congr rfl; intro i _
 simp_rw [Quarry.eye,look,flute,Gpow,_root_.map_mul,map_pow, gA_x,octave]
 unfold tilt
 generalize he:(MvPolynomial.aeval x (Camera.print (i+1) f))=p
 rw [mul_pow,pow_succ,mul_assoc (PowerSeries.X ^ i),← mul_assoc _ _ p] -- pattern
 have ht:(ratio w)^i*((ratio w)⁻¹)^i=1:=by rw [←mul_pow,reciprocity,one_pow]
 rw [← one_mul ((ratio w)⁻¹ * _),← ht];ac_rfl
end YM.RG08.Clef
