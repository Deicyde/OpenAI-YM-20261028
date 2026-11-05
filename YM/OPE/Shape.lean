import YM.OPE.Eye.Civic
import YM.OPE.Height
/-!
# Separation and extent in a layer of log-rate analysis

All statements are *for configurations of every size at a fixed arity*. Arrival times
may depend on the decay schedule and such data incl separation constants. Far exterior
positions do not require an explicit compactness assumption for these upper costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Filter Set Function Lattice RG Matrix MergeProof Cards Extraction
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {I J L : Type}[Fintype I][Fintype J]{φ:Filter L}{T u v : L→ℝ}{a b c d e : ℝ}
variable {x x': L→ I→ E4}{y y':L→ J→E4}

def extentWithin (φ:Filter L)(T:L→ℝ)(x:L→I→E4)(a:ℝ):= RateLE φ T x (-a)
-- reciprocal separation budget; strict gap at every faster phase including positive copies.
def Kept (φ:Filter L)(T:L→ℝ) (a:ℝ)(x:L→ I→ E4) := ∀ b : ℝ,a<b → ∀ᶠ i in φ,Apart (Real.exp (-b*T i)) (x i)
def Intervals (φ:Filter L)(T:L→ℝ)(a:ℝ)(x:L→ I→ E4)(y:L→ J→E4) := ∀ b:ℝ,a<b→ ∀ᶠ i in φ,ApartFrom (Real.exp (-b*T i)) (x i) (y i)
def sole {V:Type*} (x : V) : Unit→V:= fun _=>x
def centerless {U : Type}[Zero U](L : Type*):L→ Unit→ U:=fun _=> sole 0
lemma Kept.mono (h:Kept φ T a x)(hu:a≤b): Kept φ T b x:= fun t ht=> h _ (lt_of_le_of_lt hu ht)
lemma extentWithin.mono (h:extentWithin φ T x a)(hx:b≤a): extentWithin φ T x b:= RateLE.mono h (neg_le_neg hx)
lemma Intervals.mono (h:Intervals φ T a x y)(he:a≤b): Intervals φ T b x y:=fun t ht=> h _ (lt_of_le_of_lt he ht)
lemma Intervals.swap (h:Intervals φ T a x y): Intervals φ T a y x:= fun t ht=> (h t ht).mono (fun i hi a b=> by rw [norm_sub_rev]; exact hi b a)
lemma Kept.sole (φ:Filter L)(T:L→ℝ)(x:L→E4)(a:ℝ): Kept φ T a (fun i=>OPE.sole (x i)) :=fun _ _=> Eventually.of_forall (fun _=>Apart.diagonal _ _)
lemma ApartFrom.short {x:I→E4}{y:J→E4}(h:ApartFrom a x y)(he:b≤a): ApartFrom b x y:= fun i j=> lt_of_le_of_lt he (h i j)
lemma Apart.short {x:I→E4}(h:Apart a x)(he:b≤a): Apart b x:= fun i j hh=> lt_of_le_of_lt he (h i j hh)
lemma Intervals.short (h:Intervals φ T a x y)(hc: a < b)(hT:Tendsto T φ atTop)(hu:RateLE φ T u (-b)): ∀ᶠ i in φ,ApartFrom (u i) (x i) (y i):=by
    obtain ⟨w,hw,hw'⟩:= exists_between hc; filter_upwards [h w hw,(RateIs.exp (-w) hT).overtakes hu hT (neg_lt_neg hw')] with i h he using h.short he.le
lemma Kept.short (h:Kept φ T a x)(hc:a<b)(hT:Tendsto T φ atTop)(hu:RateLE φ T u (-b)) : ∀ᶠ i in φ,Apart (u i) (x i):=by
    obtain ⟨w,hw,hw'⟩:= exists_between hc; filter_upwards [h w hw,(RateIs.exp (-w) hT).overtakes hu hT (neg_lt_neg hw')] with i h he using h.short he.le
lemma Apart.seams {x:I→E4}{y:J→E4}(h:Apart a x)(he:Apart a y)(hf:ApartFrom a x y): Apart a (beside x y):=by
    rintro (i|i) (j|j) h'; exacts [h _ _ (fun H=> h' (congr_arg Sum.inl H)), hf _ _, by rw [norm_sub_rev]; exact hf _ _, he _ _ (fun H=> h' (congr_arg Sum.inr H))]
lemma Kept.chorus (h:Kept φ T a x)(he:Kept φ T a y)(hf:Intervals φ T a x y) : Kept φ T a (fun i=> beside (x i) (y i)):=by intro b hb; filter_upwards [h b hb,he b hb,hf b hb] with i hx he hf using hx.seams he hf
lemma Kept.inject (h:Kept φ T a x): ∀ᶠ i in φ, Injective (x i):= (h (a+1) (by linarith)).mono (fun i hi=> hi.coin (Real.exp_nonneg _))

lemma c_dist_point (x y z:E4): ‖x-z‖ ≤ ‖x-y‖ + ‖y-z‖:= by simpa only [← dist_eq_norm] using dist_triangle x y z
lemma shrinking {q:L→E4}(hT:Tendsto T φ atTop)(hs:a<b)(h:extentWithin φ T (fun i j=>x i j-q i) b)(hu:Intervals φ T a (fun i=> sole (q i)) y): Intervals φ T a x y:=by
    intro c hc; obtain ⟨t,ht,ht'⟩:= exists_between (lt_min hc hs); let w (a:ℝ) (i:L):=Real.exp (-a*T i); have hp: RateIs φ T (fun i=>w t i/2) (-t):=((RateIs.exp (-t) hT).div (RateIs.const hT two_pos)).swap (by ring); have hh:=hp.outweigh h (neg_lt_neg (lt_of_lt_of_le ht' (min_le_right ..))) hT
    filter_upwards [hh,hp.overtakes (RateLE.exp (-c) hT) hT (neg_lt_neg (lt_of_lt_of_le ht' (min_le_left ..))), hu t ht] with i hi hx hF s u
    have hξ:= hF () u; have he : ‖x i s-q i‖ ≤ w t i/2:= (norm_le_pi_norm (fun j=>x i j-q i) s).trans hi; change w t i < ‖q i-y i u‖ at hξ
    linarith only [hξ,(show w c i < w t i/2 from hx), he,c_dist_point (q i) (x i s) (y i u), norm_sub_rev (q i) (x i s)] -- c_dist_point?
lemma extentWithin.bump (hT:Tendsto T φ atTop)(h:extentWithin φ T x a)(he:RateLE φ T (fun i=> x' i-x i) c)(hp:c≤ -a): extentWithin φ T x' a:= (RateLE.add h (he.mono hp) hT).congr (Eventually.of_forall fun i=> add_sub_cancel ..) -- orientation

lemma Intervals.bump (hT:Tendsto T φ atTop)(h:Intervals φ T a x y)(he:RateLE φ T (fun i=> x' i - x i) (-b))(hp:a<b): Intervals φ T a x' y:=by
    intro c hc; obtain ⟨t,ht,ht'⟩:= exists_between (lt_min hc hp); let w (a:ℝ) (i:L):=Real.exp (-a*T i); have hP:RateIs φ T (fun i=>w t i/2) (-t):=((RateIs.exp (-t) hT).div (RateIs.const hT two_pos)).swap (by ring); have hh:=hP.outweigh he (neg_lt_neg (lt_of_lt_of_le ht' (min_le_right ..))) hT
    filter_upwards [hh,hP.overtakes (RateLE.exp (-c) hT) hT (neg_lt_neg (lt_of_lt_of_le ht' (min_le_left ..))),h t ht] with i hi hx hF s u
    have hξ:=hF s u; change w t i< _ at hξ
    have he:‖x' i s-x i s‖ ≤ w t i/2:= (norm_le_pi_norm (x' i-x i) s).trans hi; change w c i < _; linarith only [hξ,(show w c i < w t i /2 from hx),he,c_dist_point (x i s) (x' i s) (y i u),norm_sub_rev (x i s) (x' i s)]
lemma Kept.bump (hT:Tendsto T φ atTop)(h:Kept φ T a x)(he:RateLE φ T (fun i=> x' i-x i) (-b))(hp:a<b): Kept φ T a x':=by
    intro c hc; obtain ⟨t,ht,ht'⟩:=exists_between (lt_min hc hp); let w(a:ℝ)(i:L):=Real.exp (-a*T i); have hP:RateIs φ T (fun i=>w t i/3) (-t):=((RateIs.exp (-t) hT).div (RateIs.const (c:=3) hT (by norm_num))).swap (by ring); have hh:=hP.outweigh he (neg_lt_neg (lt_of_lt_of_le ht' (min_le_right ..))) hT
    filter_upwards [hh,hP.overtakes (RateLE.exp (-c) hT) hT (neg_lt_neg (lt_of_lt_of_le ht' (min_le_left ..))),h t ht] with i hi hx hF j k hj
    have hξ:=hF j k hj; change w t i< _ at hξ; have he s: ‖x' i s-x i s‖≤ w t i/3:= (norm_le_pi_norm (x' i-x i) s).trans hi
    change w c i < _; linarith only [hξ,(show w c i < w t i /3 from hx),he j,he k,c_dist_point (x i j) (x' i j) (x i k),c_dist_point (x' i j) (x' i k) (x i k),norm_sub_rev (x i j) (x' i j)]

end YM.OPE
