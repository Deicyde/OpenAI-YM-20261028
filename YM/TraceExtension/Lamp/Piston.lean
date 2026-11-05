import YM.TraceExtension.Lamp.Pool
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i b:Axis)(q:G.ColorIndex)
section kernels
lemma prop_drag (F:Site f→ℝ) : ∑ x:Site f,(stampQ 0 (x+step b)-stampQ 0 x)*F x=F (-step b)-F 0:=by
    have h(x:Site f): stampQ 0 (x+step b) = stampQ (-step b) x:=by
       unfold stampQ; simp only [show (0=x+step b)↔-(step b:Site f)=x from by constructor <;> intro h; exact (eq_neg_of_add_eq_zero_left h.symm).symm; rw[←h,neg_add_cancel]]
    simp_rw [h,sub_mul]; rw [sum_sub_distrib]; simp[stampQ,ite_mul]
lemma era_deal (V:Funds (Lines G f 1)) :
    (V*deal G (stampQ (0:Site f)) b).trace=∑ i:Axis,∑ j:G.ColorIndex,(V (-step i,coord b,j) (-step i,coord i,j)- V (0,coord b,j) (0,coord i,j)):=by
    have ht(i:Lines G f 1): (deal G (stampQ (0:Site f)) b*V) i i= (stampQ 0 (i.1+step (axisEquiv.symm i.2.1))-stampQ 0 i.1)* V (i.1,coord b,i.2.2) i:=by
        simp only[Matrix.mul_apply,deal,Matrix.of_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]; simp
    rw[Matrix.trace_mul_comm]; unfold Matrix.trace; simp_rw[Matrix.diag_apply,ht]; rw[Fintype.sum_prod_type,sum_comm,Fintype.sum_prod_type,← Equiv.sum_comp axisEquiv]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ;simp only[Equiv.symm_apply_apply]; exact prop_drag i (fun x=> _)
    -- simplify
lemma era_teat {r:ℕ}(V:Funds (Lines G f r)) :
    (V*teat G (stampQ (0:Site f)) b r).trace=∑ j:Loc G r,(V (-step b,j) (-step b,j)- V (0,j) (0,j)):=by
    rw [Matrix.trace_mul_comm]; simp only [teat,Matrix.trace,Matrix.diag_apply,diagonal_mul]; rw[Fintype.sum_prod_type,sum_comm]; simp_rw [prop_drag]
end kernels
-- entries of core resolvent
variable {F:∀ w,WildM G (g w) k k}
structure Circles (F:WildM G f k k): Prop where
    roll : ∀ (s:Site f),∀ᶠ x in 𝓝 (0:Link G f), F (rideC s x)*car G k s=car G k s*F x
abbrev cutM (F:WildM G f k k) (i j:Loc G k)(x: Site f)(z:Link G f):= F z (x,i) (x,j)
lemma cutT (h:∀ w,Circles (F w))(hp:Parked F 2)(x y:Loc G k): Pico (fun _=>0) (fun w=>cutM (F w) x y 0) 2 ∧ ∀ i, Traverse (cutM (F i) x y):=by
    obtain ⟨a,C,ha,hC,H⟩:= hp.top
    refine ⟨⟨a,C,ha,hC,fun w=>?_⟩, fun i=> ⟨(H i _ _).1,fun s=>?_⟩⟩
    · have hx:= H w (0,x) (0,y); simp only [Decay,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hx;exact hx
    filter_upwards [h i|>.roll s] with z hz
    have ht(x':Loc G k):rideI s (0,x')=(s,x'):= by change (0+s,x')=(s,(x':Loc G k));rw[zero_add]
    change _ = F i (rideC s z) (0,x) (0,y); rw [show F _ _ _ _=F i z _ _ from car_elem _ _ _|>.1 hz (0,x) (0,y),ht,ht]
lemma cirB {μ:ℝ}(hμ:0<μ)(hp:M.Bounds p α C D)(h: (stock p M μ (1:Config G f)).det ≠ 0): Circles (shellB p M μ ∘ input G f) :=by
    refine ⟨fun v=>?_⟩; filter_upwards [gate_n hp hμ h (Army.powL (v:=id) contDiffAt_id) (input_zero ..)] with z hz
    change shellB p M μ (input G f _)*_= _; rw[r_imp];exact shell_b_c _ _ hp hz
lemma cirG {μ:ℝ}(hμ:0<μ)(hp:M.Bounds p α C D): Circles (shellG μ ∘ input G f):=by
    refine ⟨fun v=>?_⟩; filter_upwards with z; change shellG _ (input G f _)*_= _; rw[r_imp];exact shell_g_c _ _ hp hμ
variable (Tn:Tendsto (fun x=>(g x).val) L atTop)
abbrev highray (F:WildM G f k k):ℂ:= (Fintype.card (Site f):ℂ)⁻¹*cob d i q (fun z=> (F z).trace)
lemma high_eq {F:WildM G f k k}(h:Circles F)(hp:Park F a C 2)(ha:0<a)(hx:0≤C): highray d i q F= ∑ k:Loc G k,cob d i q (cutM F k k 0):=by
    have ht(k:Loc G k): Traverse (cutM F k k):= cutT (F:=fun _:Unit=>F) (g:=fun _=> f) (fun _=>h) ⟨a,C,ha,hx,fun _=>hp⟩ k k|>.2 ()
    let A(i: Loc G k):= ∑ x:Site f, cutM F i i x
    have hV i: ContDiffAt ℝ ω (A i) 0:=by rw[show A i=fun z=>∑ x,cutM F i i x z from funext fun z=> Finset.sum_apply ..]; exact ContDiffAt.sum fun x _=>(ht i).team x
    unfold highray; rw[show (fun z=>(F z).trace)=∑ i,A i from ?_,cob_total d i q hV]; swap
    · funext z; rw [Matrix.trace,Fintype.sum_prod_type,sum_comm,Finset.sum_apply]; unfold A; simp_rw [Finset.sum_apply];rfl
    simp_rw [show ∀ j:Loc G k,cob d i q (A j)= _ from fun j=> cob_s_tot d i q (A':=cutM F j j) (ht j),← mul_sum]; apply inv_mul_cancel_left₀;exact Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
include Tn
lemma teat_ro (h:∀ w,Circles (F w))(hp:Parked F 2): Rose L (fun w=> lux d i q b (fun z=>(F w z * teat G (stampQ (0:Site (g w))) b k).trace)) (fun w=> highray d i q (F w)):=by
    let A(w:W)(j:Loc G k)(x):= cutM (F w) j j x
    have hx(w): (fun z=>(F w z * teat G (stampQ (0:Site (g w))) b k).trace)= ∑ j,(A w j (-step b)- A w j 0):=by funext z; rw[Finset.sum_apply]; exact era_teat b _
    have ht(j):=cutT h hp j j
    have he(j): Rose L (fun w=>lux d i q b (A w j (-step b)- A w j 0)) (fun w=> cob d i q (A w j 0)):=by
        have he:=orb_pick d i b q Tn (ht j|>.1) (ht j|>.2) (-step b)
        simp only [map_neg,wrap_step, Pi.neg_apply] at he
        simpa using he
    obtain ⟨a,C,ha,hC,f⟩:=hp.top; rw[show (fun w=> highray d i q (F w))=(fun w=>∑ x,cob d i q (A w x 0)) from funext fun w=> high_eq d i q (h w) (f w) ha hC]
    refine Rose.chain (Rose.skip (Eventually.of_forall fun w=>?_)) (Rose.sumX univ (F:=fun j w=>lux d i q b (A w j (-step b)- A w j 0)) (fun j _=>he j))
    dsimp only; rw[hx]; exact lux_t d i b q (fun v:Loc G k=> (ht v|>.2 w|>.team _).sub (ht v|>.2 w|>.team _))
lemma deal_b {F:∀ w,WildM G (g w) 1 1}(h:∀ w,Circles (F w))(hp:Parked F 2): Rose L (fun w=>lux d i q b (fun z=> (F w z *deal G (stampQ (0:Site (g w))) b).trace)) (fun w=> ∑ x:G.ColorIndex,cob d i q (cutM (F w) (mood G b x) (mood G b x) 0)):=by
    let A(w:W)(a:Axis)(x:G.ColorIndex)(y):=cutM (F w) (mood G b x) (mood G a x) y
    let B w a x:= A w a x (-step a) - A w a x 0
    have ht(a x):= cutT h hp (mood G b x) (mood G a x)
    have hh(a x): Rose L (fun w=>lux d i q b (B w a x)) (fun w=> if a=b then cob d i q (A w a x 0) else 0):=by
       have he:=orb_pick d i b q Tn (ht a x|>.1) (ht a x|>.2) (-step a)
       by_cases hv:a=b
       · subst a; simp only[map_neg, wrap_step, Pi.neg_apply] at he; simpa using (show Rose L (fun w=>lux d i q b (B w b x)) (fun w=>cob d i q (A w b x 0)) from by simpa using he)
       unfold B A; simpa [hv, Ne.symm hv] using he
    let U(w)(a):= ∑ x:G.ColorIndex,B w a x
    have hv(w:W) : (fun z=> (F w z *deal G (stampQ (0:Site (g w))) b).trace)= ∑ a,U w a:=by funext z; rw[Finset.sum_apply]; unfold U; simp_rw [Finset.sum_apply]; exact era_deal b _
    have he:=Rose.sumX univ (fun a (_:a ∈ univ)=> Rose.sumX univ (fun x (_:x∈univ)=> hh a x))
    refine Rose.chain (Rose.skip ?_) (Rose.chain he (Rose.skip ?_))
    · filter_upwards with w; rw [hv]; have ht'(a: Axis)(x:G.ColorIndex): ContDiffAt ℝ ω (B w a x) 0:=(ht a x|>.2 w|>.team _).sub (ht a x|>.2 w|>.team _)
      rw [lux_t d i b q (fun v=> ?_)]; · exact sum_congr rfl fun a _=>lux_t _ _ _ _ (ht' a)
      rw[show U _ _=(fun z=>∑ x,B w v x z) from funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum (fun i _=> ht' v i)
    filter_upwards with w; rw [sum_eq_single b]
    · simp; rfl
    · intro i _ hi;simp[hi]
    simp
end YM.Trace.Lamp
