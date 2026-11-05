import YM.RG08.Room.Crew

/-!
# Centered Wick on possibly padded spaces. IBM cost rule consumes inverse in integrated rows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Forms Glyph Cloud Finset Function MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I:Type}[Fintype I]
structure Haze (I:Type) where
 foam : Finset I
 price : I→I→ℝ
 flipped (i j:I):price i j=price j i
 dryL (i j:I): i∉foam→ price i j=0

namespace Haze
variable (H:Haze I)
omit [Fintype I] in
lemma dryR (i j:I)(h:j∉H.foam):H.price i j=0:=by rw [H.flipped,H.dryL j i h]

def stop (i:I):Inn I:=if i∈H.foam then 0 else X i
def stove : Inn I→ₗ[ℝ] Inn I := (MvPolynomial.aeval H.stop).toLinearMap.comp (wind H.price H.flipped)
lemma stove_does (f:Inn I):H.stove f=MvPolynomial.aeval H.stop (wind _ H.flipped f):=rfl
lemma stove_root (i:I)(f:Inn I):H.stove (X i*f)=H.stop i*H.stove f+∑ j,H.price i j • H.stove (pderiv j f):=by
 have he : wind _ H.flipped (X i*f)=X i* wind _ H.flipped f+wind _ H.flipped (Glyph.fork H.price i f) := wick_x H.flipped ..
 simp only [stove_does,he,map_add,map_mul,aeval_X,Glyph.fork_apply,map_sum,_root_.map_smul]
lemma stove_a (a:ℝ):H.stove (C a)=C a:=by change aeval H.stop (wick H.price (C a))=_;rw [wick_c,aeval_C];rfl
lemma stove_one : H.stove 1=1:=H.stove_a 1

lemma stove_out (p f:Inn I)(h:∀ i∈H.foam,pderiv i p=0):H.stove (p*f)=p*H.stove f:=by
 have hp:aeval H.stop p=p:=by
   have he:aeval H.stop p=aeval (X (R:=ℝ)) p:=nearby H.foam h (fun i hi=>if_neg hi)
   simpa using he
 have he(f:Inn I):radiator H.price (p*f)=p*radiator H.price f:=by
    unfold radiator;rw [slab_do,slab_do];simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i _; apply Finset.sum_congr rfl; intro j _
    by_cases hi:i∈H.foam
    · by_cases hj:j∈H.foam
      · unfold axes;rw [pderiv_mul,h _ hj,zero_mul,zero_add,pderiv_mul,h _ hi,zero_mul,zero_add,mul_smul_comm] -- pderiv_mul order?
      simp [half,H.dryR _ _ hj]
    simp [half,H.dryL _ _ hi]
 have hh(i:ℕ)(f:Inn I): (radiator H.price)^[i] (p*f)=p*(radiator H.price)^[i] f:=by induction i with
 | zero=>rfl
 | succ i hx=>rw [iterate_succ_apply', iterate_succ_apply',hx,he]
 have hw(i:ℕ)(f:Inn I):gust H.price i (p*f)=p*gust H.price i f:=by rw [gust,hh,←mul_smul_comm];rfl
 obtain ⟨n,hn⟩:=halts H.price H.flipped f
 have hy:Halt H.price (p*f) n:=fun i hi=>by rw [hw,hn i hi,mul_zero]
 change aeval H.stop (wick H.price (p*f))=p*aeval H.stop (wick H.price f)
 rw [wick_budget hy,wick_budget hn]; simp_rw [hw,←Finset.mul_sum,map_mul,hp]

lemma stove_safe (i:I)(p:Inn I)(hi:i∈H.foam): pderiv i (H.stove p)=0:=by
 rw [stove_does];generalize wind H.price H.flipped p=q
 induction q using MvPolynomial.induction_on with
 | C a=>simp
 | add _ _ ha hb=>simp only [map_add,ha,hb,add_zero]
 | mul_X p j h=>
   rw [_root_.map_mul,aeval_X,pderiv_mul,h];simp only [zero_mul,zero_add]; unfold stop
   by_cases hj:j∈H.foam
   · simp [hj]
   simp [hj,pderiv_X,show j≠i from fun hh=>hj (hh ▸ hi)]

/- series frame expectation with no normalization constants (stove_one), still ignores Q0 external. -/
def brew : Port I→ₗ[ℝ] Port I where
 toFun f:=PowerSeries.mk (fun i=> H.stove (tap i f))
 map_add' _ _ := by ext i :1;simp only [tap,map_add,PowerSeries.coeff_mk]
 map_smul' r f:=by
   ext i :1; change tap i (PowerSeries.mk _) = tap i (r • (PowerSeries.mk _ :Port I));simp only [tap,PowerSeries.coeff_smul,PowerSeries.coeff_mk,_root_.map_smul]

 theorem brew_view (i:ℕ)(f:Port I):tap i (H.brew f)=H.stove (tap i f):=PowerSeries.coeff_mk i (fun e=> H.stove (tap e f))
lemma brew_c (p:Inn I):H.brew (liftInn p)=liftInn (H.stove p):=by
 ext i :1; change tap _ _=tap _ _; rw [brew_view];unfold tap;rw [PowerSeries.coeff_C,PowerSeries.coeff_C];split_ifs <;> simp
lemma brew_one : H.brew 1=1:=by simpa only [_root_.map_one,H.stove_one] using brew_c H 1
lemma brew_steady : Steady H.brew:=fun e a b h=>by rw [brew_view,brew_view,h e le_rfl]
lemma brew_easy (f:Port I): Abroad H.foam (H.brew f):=abroad_coeff _ |>.2 (fun i hi e=>by rw [brew_view];apply H.stove_safe _ _ hi)

lemma brew_shunt {p:Port I}(hp:Abroad H.foam p)(f:Port I): H.brew (p*f)=p*H.brew f:=by
 ext e :1;change tap _ _=tap _ _;rw [brew_view];unfold tap at *;rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul,map_sum]; apply Finset.sum_congr rfl;intro i hi
 change H.stove (tap _ p*tap _ f)=tap _ p*tap _ (H.brew f)
 rw [H.stove_out _ _ (fun k hk=>abroad_coeff _ |>.mp hp k hk _),H.brew_view]

 omit [Fintype I] in
lemma power_easy (e:ℕ):Abroad H.foam (PowerSeries.X ^ e):=fun i _=>by induction e with
 | zero=>simp
 | succ i hi=>rw [pow_succ,Derivation.leibniz,pin_g,hi];simp

lemma brew_prime (p:Port I)(i:I): H.brew (rod i*p)=liftInn (H.stop i)*H.brew p+∑ j,H.price i j • H.brew (pin j p):=by
 ext e :1; change tap _ _=tap _ _;rw [brew_view]; unfold tap;rw [PowerSeries.coeff_C_mul,map_add,map_sum,PowerSeries.coeff_C_mul,H.stove_root, ←H.brew_view]; apply congrArg₂ (·+·) rfl;apply Finset.sum_congr rfl;intro j hj
 rw [PowerSeries.coeff_smul];change _=_ • tap _ _; rw [brew_view]; congr 2;exact (flight_apply ..).symm

lemma brew_fresh (p:Port I)(i:I)(h:i∈H.foam): H.brew (rod i*p)=∑ j,H.price i j • H.brew (pin j p):=by rw [H.brew_prime]; simp [stop,h]

/-- `Q` is NEGATIVE quadratic exponent relative to centered Gaussian, no external or affine
components needed (external-only ones do not affect this hypothesis/statements). P may be
supported anywhere except mixing integrated with external without further equations.
-/
def Boil (P : I→I→ℝ)(Q:Inn I):Prop:= (∀ i∈H.foam,∀ j, (∑ k∈H.foam,P i k*H.price k j) = if i=j then 1 else 0) ∧ ∀ i∈H.foam,pderiv i Q= -(∑ j∈H.foam,P i j • X j)

/-- Algebraic Gaussian IBP all formal orders. -/
theorem mint {P:I→I→ℝ}{Q:Inn I}(h:H.Boil P Q){i:I}(hi:i∈H.foam)(p:Port I):H.brew (pin i (liftInn Q) *p)=-(H.brew (pin i p)):=by
 rw [pin_c,h.2 i hi,map_neg,map_sum]
 have he (a:ℝ)(p:Inn I):liftInn (a • p)=a • liftInn p:=by rw [Algebra.smul_def,Algebra.smul_def,_root_.map_mul,PowerSeries.algebraMap_apply]
 simp_rw [neg_mul,map_neg,he,Finset.sum_mul,smul_mul_assoc,map_sum,_root_.map_smul]
 congr 1
 change ∑ x∈H.foam, P i x • H.brew (rod x*p)=_
 rw [Finset.sum_congr rfl (fun x (hx:x∈H.foam)=> congrArg (fun y=>P i x • y) (H.brew_fresh p x hx))];simp_rw [Finset.smul_sum,smul_smul];rw [Finset.sum_comm];simp_rw [←Finset.sum_smul,h.1 i hi]; simp [ite_smul]

end Haze
end YM.RG08.Room
