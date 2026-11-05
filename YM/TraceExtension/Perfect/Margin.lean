import YM.TraceExtension.Perfect.Gain

/-!
# Marginal gain. P affine remainder scaled L^−2, Q second-order. Applies also to auxiliary legs carrying L^−3.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Stationary Function Matrix Lattice Precision Finset
open scoped Topology BigOperators ContDiff
variable {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def sh (A:I→ℕ)(α:ℝ)(t:ℕ)(r:ℝ)(f:I→ℝ):ℝ := ∑ i,spot α t r (A i) * ‖f i‖
omit [DecidableEq I] in
lemma sh_nn (A α t r)(f:I→ℝ):0≤ sh A α t r f := sum_nonneg fun _ _=> mul_nonneg (spot_pos ..).le (norm_nonneg _)
omit [DecidableEq I] in
lemma sh_anti (A α t r s)(f:I→ℝ)(h:0≤α)(hp:r ≤ s): sh A α t s f ≤ sh A α t r f:= sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (spot_anti _ _ _ h _ _ hp) (norm_nonneg _)
omit [DecidableEq I] in
lemma sh_neg (A α t r)(f:I→ℝ): sh A α t r (-f)= sh A α t r f:= by simp [sh]
omit [DecidableEq I] in
lemma sh_add (A α t r)(f g:I→ℝ): sh A α t r (f+g)≤sh A α t r f+sh A α t r g:=by unfold sh; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _=> ?_; rw [Pi.add_apply,←mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (spot_pos ..).le

variable {α β L C:ℝ}{U P Q:J→I→ℝ}{A:I→ℕ}{B:J→ℕ}{t:ℕ}
omit [DecidableEq I] in
lemma coat (A α t r)(f g:I→ℝ)(ha:0≤α)(hr:0≤r): cost A α t r (fun b:Fin 2→ I=> f (b 0) * g (b 1))≤ sh A α t r f * sh A α t r g:=by
 let v:(Fin 2→ I) ≃ I× I := finTwoArrowEquiv _
 let F b:=spot α t r (A (b:I))*‖f b‖; let G b:=spot α t r (A (b:I))*‖g b‖
 unfold cost; refine (sum_le_sum (g:=fun b:Fin 2→I=> F (b 0)*G (b 1)) (fun b _=>?_)).trans_eq ?_
 · let X i:= spot α t r (A (b i)); have he:spot α t r (limitN A b) ≤ X 0*X 1:=by
     obtain ⟨i,hi⟩:=limitN_mem A b ⟨0⟩; rw [hi]; fin_cases i
     · exact le_mul_of_one_le_right (spot_pos ..).le (spot_one ha ..)
     exact le_mul_of_one_le_left (spot_pos ..).le (spot_one ha ..)
   dsimp only; rw [norm_mul]; refine (mul_le_mul_of_nonneg_right he (show 0 ≤ ‖_‖*‖_‖ from mul_nonneg (norm_nonneg (f _)) (norm_nonneg _))).trans_eq ?_; unfold F G X; ring
 change (∑ b:Fin 2→I,(fun p:I×I=> F p.1*G p.2 ) (v b))=_
 rw [Equiv.sum_comp v (fun p=> F p.1 * G p.2),Fintype.sum_prod_type]; unfold sh; rw [sum_mul]; simp_rw [Finset.mul_sum]; rfl

-- buy two Taylor polynomials and remainder besides full narrow estimate
structure Settle (A:I→ℕ)(B:J→ℕ)(U P Q:J→I→ℝ)(α :ℝ)(t:ℕ)(L C:ℝ):Prop where
   total j : sh A α t (B j/L) (U j) ≤ C * rush L (B j)
   p j : sh A α t 0 (P j) ≤ C*((1+B j)/L^2)
   q j : sh A α t 0 (Q j) ≤ C*((1+B j)^2/L^3)
   near j : B j ≤ L → sh A α t 0 (U j-P j-Q j) ≤ C*((1+B j)^3/L^4)

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma range_weight (H:Settle A B U P Q α t L C)(j:J)(r:ℕ)(hp:B j ≤ r)(hα:0≤α)(hL:0<L) (hC:0≤C):
   sh A α t (r/L) (U j) ≤ C*rush L r ∧ sh A α t 0 (P j)≤ C*((1+r)/L^2) ∧ sh A α t 0 (Q j)≤ C*((1+r)^2/L^3) ∧ ((r:ℝ)≤L → sh A α t 0 (U j-P j-Q j)≤ C*((1+r)^3/L^4)) := by
 have hu:=Nat.cast_le (α:=ℝ).mpr hp
 refine ⟨(sh_anti A α t _ _ (U j) hα (div_le_div_of_nonneg_right hu hL.le)).trans ((H.total j).trans (mul_le_mul_of_nonneg_left (rush_incr hL hp) hC)),(H.p j).trans ?_,(H.q j).trans ?_,fun h=>(H.near j (hu.trans h)).trans ?_⟩ <;> gcongr

def pairF (W V:J→I→ℝ)(b:Fin 2→J) : (Fin 2→I)→ℝ:= fun u=> W (b 0) (u 0)*V (b 1) (u 1)
-- no Q²
private def ash (U P Q:J→I→ℝ)(b:Fin 2→J):= pairF U U b - pairF P P b - pairF P Q b - pairF Q P b
omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
private lemma cooked (b:Fin 2→J): ash U P Q (I:=I) b=pairF Q Q b+
    (pairF (U-P-Q) (P+Q) b + pairF (P+Q) (U-P-Q) b)+pairF (U-P-Q) (U-P-Q) b:=by ext i; simp only [ash,Pi.add_apply,pairF,Pi.sub_apply]; ring

omit [Fintype J] [DecidableEq J] [DecidableEq I] in
private lemma nearest (H:Settle A B U P Q α t L C)(b:Fin 2→J)(r:ℕ) (hL:1≤L) (hα:0≤α) (hC:0≤C) (hp: limitN B b≤r)(hx:(r:ℝ)≤L):
    cost A α t 0 (ash U P Q b) ≤ 100*C^2*((1+r)^4/L^6):=by
 have hL':=lt_of_lt_of_le zero_lt_one hL
 let A':=C*((1+(r:ℝ))/L^2); let V:=C*((1+(r:ℝ))^3/L^4); let A'':=C*((1+(r:ℝ))^2/L^3)
 have h'i(i:Fin 2):= range_weight H (b i) r ((limitN_ge B b i).trans hp) hα hL' hC
 have hA(i:Fin 2):sh A α t 0 ((P+Q) (b i)) ≤ A'+A'':=(sh_add ..).trans (add_le_add (h'i i).2.1 (h'i i).2.2.1)
 have hV(i:Fin 2): sh A α t 0 ((U-P-Q) (b i)) ≤ V:= (h'i i).2.2.2 hx
 have h (x y:J→ I→ℝ)(s t':ℝ)(hh:sh A α t 0 (x (b 0))≤s)(hy:sh A α t 0 (y (b 1))≤t'):
      cost A α t 0 (pairF x y b) ≤ s*t':=(coat A α t 0 _ _ hα le_rfl).trans (mul_le_mul hh hy (sh_nn ..) ((sh_nn ..).trans hh))
 rw [cooked]; apply (le_trans ?_ (a:=_) (b:= (A''*A''+(V*(A'+A'')+(A'+A'')*V))+V*V) ?_)
 · refine (cost_add ..).trans (add_le_add ((cost_add ..).trans (add_le_add (h _ _ _ _ (h'i 0|>.2.2.1) (h'i 1|>.2.2.1)) ((cost_add ..).trans (add_le_add (h _ _ _ _ (hV 0) (hA 1)) (h _ _ _ _ (hA 0) (hV 1)))))) (h _ _ _ _ (hV 0) (hV 1)))
 let p:ℝ:=1+r
 have ht:0<p:=by unfold p; positivity
 have hVA:A'*V=A''*A'':=by unfold V A' A''; ring
 have hh : V = (p/L)*A'':=by unfold p V A''; ring
 have hV : V≤2*A'':= hh ▸ mul_le_mul_of_nonneg_right ((div_le_iff₀ hL').mpr (by unfold p; linarith only [hx,hL])) ((sh_nn ..).trans (h'i 0|>.2.2.1))
 have hz:C^2*((1+(r:ℝ))^4/L^6)=A''*A'':=by unfold A''; ring
 rw [show 100*C^2*((1+(r:ℝ))^4/L^6)=100*(A''*A'') from by rw [mul_assoc,hz]]
 have he:= (sh_nn ..).trans (h'i 0|>.2.2.1); change 0 ≤ A'' at he
 have hw:0≤V:=by unfold V; positivity
 nlinarith only [mul_le_mul hV hV hw (hw.trans hV), mul_le_mul_of_nonneg_right hV he,hVA, sq_nonneg A'']

lemma cost_sub (q w : (Fin 2→I)→ℝ) (A α t r) : cost A α t r (q-w)≤ cost A α t r q+cost A α t r w:=by rw [sub_eq_add_neg]; apply (cost_add ..).trans; simp [cost]
omit [Fintype J] [DecidableEq J] in
private lemma solid_f (H:Settle A B U P Q α t L C)(b:Fin 2→J)(r:ℕ) (hL:1≤L)(hα:0≤α)(hC:0 ≤ C)(hp:limitN B b ≤ r) (hx : L≤ r) (hw: α/L ≤ β) (he : 4≤t):
   cost A α t 0 (ash U P Q b)≤ (2:ℝ)^(t+8)*C^2 / L^6*spot β t 0 r :=by
 let s:ℝ:=1+r; let f:ℝ:=C/L
 let τ:ℝ:= max 0 ((r:ℝ)-0); have h':τ=r:=by unfold τ; simp
 have h0:= lt_of_lt_of_le zero_lt_one hL
 have hV : 1 ≤ s := by unfold s; linarith [Nat.cast_nonneg (α:=ℝ) r]
 have hs : L≤s:= by unfold s; linarith only[hx]
 have h'h : 0≤β:= (div_nonneg hα h0.le).trans hw
 have hT(i:Fin 2):= range_weight H (b i) r ((limitN_ge _ _ _).trans hp) hα h0 hC
 have hC' : C/rush L r^1=C/rush L r:=by ring
 have hU(i:Fin 2): sh A α t (r/L) (U (b i))≤ C/L:= by
    have he: rush L r=L⁻¹:=by unfold rush; rw [min_eq_left ((one_le_div h0).mpr hs),mul_one]
    exact (hT i).1.trans_eq (by rw [he, ← div_eq_mul_inv])
 have hP : cost A α t 0 (pairF U U b) ≤ shelter α t ((r:ℕ)/L)*f^2:=by
    have hh : 0 ≤ (r:ℝ)/L:=by positivity
    refine (cost_build (pairF U U b) A _ _ _ hα hh).trans (mul_le_mul_of_nonneg_left ((coat A _ _ _ _ _ hα hh).trans ?_) (shelter_pos _ _ hh |>.le))
    rw [pow_two]; exact mul_le_mul (hU 0) (hU 1) (sh_nn ..) ((sh_nn ..).trans (hU 0))
 let Z:= C*s/L^2; let Y := C*s^2/L^3
 have hq i:sh A α t 0 (P (b i))≤ Z := (hT i).2.1.trans_eq (by unfold Z s;ring)
 have heR i:sh A α t 0 (Q (b i))≤Y:= (hT i).2.2.1.trans_eq (by unfold Y s;ring)
 have h x y r z (hh: sh A α t 0 (x (b 0)) ≤ r) (ht: sh A α t 0 (y (b 1))≤z):cost A α t 0 (pairF x y b) ≤ r*z := (coat A α t 0 _ _ hα le_rfl).trans (mul_le_mul hh ht (sh_nn ..) ((sh_nn ..).trans hh))
 have hm : cost A α t 0 (ash U P Q b) ≤ shelter α t ((r:ℝ)/L) * f^2+ Z*Z+Z*Y+Y*Z:=
    (cost_sub ..).trans (add_le_add ((cost_sub ..).trans (add_le_add ((cost_sub ..).trans (add_le_add hP (h _ _ _ _ (hq 0) (hq 1)))) (h _ _ _ _ (hq 0) (heR 1)))) (h _ _ _ _ (heR 0) (hq 1)))
 let j := C^2/L^6*spot β t 0 r
 have hshel : shelter α t ((r:ℝ)/L)* f^2 ≤ 2^t*j:=by
    have hy : 0 ≤ (r:ℝ)/L:=by positivity
    have hz : shelter α t ((r:ℝ)/L) ≤ 2^t * s^4/L^4 * (s^(t-4)) * Real.exp (β*r) := by
       have hx' : (1+(r:ℝ)/L)^t ≤ (2*s/L)^t := pow_le_pow_left₀ (by positivity) (by field_simp; unfold s; linarith only [hx]) t
       refine mul_le_mul (hx'.trans ?_) (Real.exp_monotone (le_trans (le_of_eq (show α*((r:ℝ)/L)=α/L*r by ring)) (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)))) (Real.exp_pos _).le (by positivity)
       rw [div_pow,mul_pow]; calc
        _ ≤ (2^t*s^t)/L^4 := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hL he)
        _ = _ := by rw [show s^t=s^4*s^(t-4) from by rw [← pow_add]; congr 1; omega]; ring
    refine (mul_le_mul_of_nonneg_right hz (by positivity : 0 ≤ f^2)).trans_eq ?_
    unfold j spot f shelter; change _=2^t*(C^2/L^6*((1+τ)^t*Real.exp (β*τ)))
    rw [h',show (1+(r:ℝ))^t=s^4*s^(t-4) from by rw [← pow_add, Nat.add_sub_of_le he]]; ring
 have hy: Z≤Y:=by
    calc
     _≤ (s/L)*Z:=le_mul_of_one_le_left ((sh_nn ..).trans (hq 0)) ((one_le_div h0).2 hs)
     _=_:=by unfold Z Y;ring
 have hZ :0 ≤ Z:=(sh_nn ..).trans (hq 0)
 have hh : Y*Y ≤ j:=by
    calc
     _= C^2/L^6*s^4:=by unfold Y; ring
     _ ≤ _:= by
         apply mul_le_mul_of_nonneg_left ?_ (by positivity)
         unfold spot shelter; change _≤(1+τ)^t*Real.exp (β*τ)
         rw [h']; refine le_trans (pow_le_pow_right₀ hV he) (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
 apply hm.trans
 have hJ:0 ≤ j:=le_trans (mul_self_nonneg _) hh
 have hV': (1:ℝ)≤2^t:= one_le_pow₀ (by norm_num)
 rw [pow_add]; change _ ≤ _; rw [show ((2:ℝ)^t*2^8*C^2/L^6*_) = 2^8*(2^t*j) from by unfold j; ring]
 nlinarith only [mul_le_mul hy hy hZ (hZ.trans hy),mul_le_mul_of_nonneg_right hy (hZ.trans hy), hh,hshel,hJ,mul_le_mul_of_nonneg_right hV' hJ]


variable {Y : Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]

lemma moment_awning {β:ℝ}(h :0≤ β)(r:ℕ) (t k:ℕ)(ht:k≤t): (1+(r:ℝ))^k ≤ spot β t 0 r:=by
 unfold spot shelter; rw [sub_zero,max_eq_right (Nat.cast_nonneg _)]
 exact (pow_le_pow_right₀ (by simp) ht).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))

private lemma neutral (H:Settle A B U P Q α t L C) (b:Fin 2→ J)(h:1≤L)(hC:0≤C)(hα:0≤α)(hw: α/L ≤ β)(he:4≤t):
    cost A α t 0 (ash U P Q b)≤ (2:ℝ)^(t+8)*C^2 / L^6*spot β t 0 (limitN B b):=by
 have hp:=lt_of_lt_of_le zero_lt_one h
 let r:= limitN B b
 rcases le_total (r:ℝ) L with hx|hx
 · apply (nearest H b r h hα hC le_rfl hx).trans
   have hu : 100 ≤ (2:ℝ)^(t+8):=by rw [pow_add]; have he:= one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=t);norm_num at *; linarith only[he]
   calc
    _ = (100*C^2)/L^6*((1+(r:ℝ))^4):=by ring
    _≤ _:= mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) (by positivity)) (moment_awning ((div_nonneg hα hp.le).trans hw) r _ 4 he) (by positivity) (by positivity)
 exact solid_f H b r h hα hC le_rfl hx hw he

def bisect (P Q:J→I→ℝ) (H:ContinuousMultilinearMap ℝ (fun _:Fin 2=> Rays J) Y) (v: Fin 2→ I):Y:= ∑ b: Fin 2→J,pairF P Q b v • bank H b
theorem reflection (H:Settle A B U P Q α t L C)(T:ContinuousMultilinearMap ℝ (fun _:Fin 2=> Rays J) Y) (h:1≤L)(hC:0≤C)(hα:0≤α)(hx:α/L≤β)(he:4≤t):
    cost A α t 0 (bisect U U T) ≤ ((2:ℝ)^(t+8)*C^2/L^6)*cost B β t 0 (bank T) + (cost A α t 0 (bisect P P T)+cost A α t 0 (bisect P Q T + bisect Q P T)) :=by
 let f (b) := fun v=> ash U P Q b v • bank T b
 rw [show bisect U U T=(fun v=>∑ b,f b v)+(bisect P P T+(bisect P Q T+bisect Q P T)) from funext (fun v=> by simp only [bisect,f,ash, Pi.add_apply, Pi.sub_apply,sub_smul, Finset.sum_sub_distrib]; abel)]
 refine (cost_add ..).trans (add_le_add ((cost_sum A α t 0 f).trans ?_) (cost_add ..)); unfold cost; rw [Finset.mul_sum]; apply sum_le_sum; intro i _
 change cost A α t 0 (f i)≤_
 unfold f; rw [cost_smul,← mul_assoc]; exact mul_le_mul_of_nonneg_right (neutral H i h hC hα hx he) (norm_nonneg _)

lemma tail_bell (b:Fin 2→ J)(h:1≤L)(hC:0≤C)(hα:0≤α) (hk:0≤β)(he : 3 ≤ t) (H:Settle A B U P Q α t L C):
 cost A α t 0 (fun v=>pairF P Q b v+ pairF Q P b v) ≤ 2*C^2/L^5 * spot β t 0 (limitN B b):=by
 let r:= limitN B b; have hV:=lt_of_lt_of_le zero_lt_one h; have ht i:= range_weight H (b i) r (limitN_ge B b i) hα hV hC
 have hx: cost A α t 0 (pairF P Q b)≤ C*((1+r)/L^2)*(C*((1+r)^2/L^3)):= (coat A α t 0 _ _ hα le_rfl).trans (mul_le_mul (ht 0|>.2.1) (ht 1|>.2.2.1) (sh_nn ..) ((sh_nn ..).trans (ht 0|>.2.1)))
 have hy: cost A α t 0 (pairF Q P b)≤ (C*((1+r)^2/L^3))* (C*((1+r)/L^2)):= (coat A α t 0 _ _ hα le_rfl).trans (mul_le_mul (ht 0|>.2.2.1) (ht 1|>.2.1) (sh_nn ..) ((sh_nn ..).trans (ht 0|>.2.2.1)))
 refine ((cost_add A α t _ _ _).trans (add_le_add hx hy)).trans ?_; refine le_trans ?_ (mul_le_mul_of_nonneg_left (moment_awning hk r _ _ he) (show 0 ≤ 2*C^2/L^5 by positivity)); apply le_of_eq; ring

theorem reflection_near (H:Settle A B U P Q α t L C)(T:ContinuousMultilinearMap ℝ (fun _:Fin 2=> Rays J) Y) (h:1≤L)(hC:0≤C)(hα:0≤α)(hx:α/L≤β)(he:4≤t):
    cost A α t 0 (bisect U U T) ≤ ((2:ℝ)^(t+9)*C^2/L^5)*cost B β t 0 (bank T) + cost A α t 0 (bisect P P T) :=by
 have hp := lt_of_lt_of_le zero_lt_one h
 have hv : cost A α t 0 (bisect P Q T +bisect Q P T) ≤ 2*C^2/L^5*cost B β t 0 (bank T):=by
    let f (b:Fin 2→J) := fun x=> (pairF P Q b x+pairF Q P b x) • bank T b
    rw [show bisect P Q T+bisect Q P T=fun x=>∑ b,f b x from funext fun x=>by simp only [f,add_smul,Finset.sum_add_distrib]; rfl]
    refine (cost_sum A α t 0 f).trans ?_; unfold cost; rw [Finset.mul_sum]; apply sum_le_sum; intro i _
    change cost _ _ _ _ (f i)≤_; unfold f; rw [cost_smul _ _ _ _ (fun x=> pairF P Q i x+ pairF Q P i x),← mul_assoc]; exact mul_le_mul_of_nonneg_right (tail_bell i h hC hα ((div_nonneg hα hp.le).trans hx) (by omega) H) (norm_nonneg (bank T i))
 have hh : ((2:ℝ)^(t+8)*C^2/L^6)+2*C^2/L^5≤2^(t+9)*C^2/L^5:=by
    rw [show 2^(t+9)= (2:ℝ)^(t+8)*2 by ring]; have hv:2≤(2:ℝ)^(t+8):= by
       conv_lhs => rw [← pow_one (2:ℝ)]
       apply pow_le_pow_right₀ (by norm_num); omega
    calc
     _ ≤ (2:ℝ)^(t+8)*C^2/L^5+(2:ℝ)^(t+8)*C^2/L^5:= add_le_add (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ h (by norm_num))) (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (by positivity)) (by positivity))
     _=_:=by ring
 have ht:= mul_le_mul_of_nonneg_right hh (cost_nn B β t 0 (bank T)); rw [add_mul] at ht; apply (reflection H T h hC hα hx he).trans; linarith only [ht,hv]

lemma name_bisect (P Q:J→I→ℝ)(T:ContinuousMultilinearMap ℝ (fun _:Fin 2=> Rays J) Y)(b: Fin 2→I):
    bisect P Q T b=T ![fun j=> P j (b 0),fun j=>Q j (b 1)]:=by
 unfold bisect; erw [many (.atomic 2) T]; refine Finset.sum_congr rfl fun i _=> ?_; unfold pairF; congr 1; change _=∏ k:Fin 2, (![fun j=> P j (b 0), fun j=> Q j (b 1)] : Fin 2→J→ℝ) k (i k) ; rw [Fin.prod_univ_two]; rfl

end YM.Trace.Perfect
