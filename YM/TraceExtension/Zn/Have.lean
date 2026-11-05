import YM.TraceExtension.Xo.Pane
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft
open scoped BigOperators Topology Classical
private abbrev ellZ:= Real.log
def RLog(x:ℝ):= (ellZ (ellZ x))^2
def Wave(a:ℝ)(x:ℝ):=Real.exp (a*RLog x)
lemma wake (a x:ℝ):0<Wave a x:=Real.exp_pos _
lemma arc : Tendsto RLog atTop atTop := (tendsto_pow_atTop (show 2≠ (0:ℕ) by decide)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
lemma awe {a:ℝ}(h:0<a) : Tendsto (Wave a) atTop atTop:= Real.tendsto_exp_atTop.comp (arc.const_mul_atTop h)
lemma walt (a b x : ℝ) : Wave a x* Wave b x=Wave (a+b) x:=by unfold Wave; rw[← Real.exp_add,add_mul]
lemma wane {a b :ℝ}(x:ℝ)(h:a≤b): Wave a x≤ Wave b x:= Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (sq_nonneg _))
lemma wok (a x:ℝ)(h:0≤ a):1≤ Wave a x:=by simpa only[Wave,zero_mul,Real.exp_zero] using wane x h
lemma wring (a b x:ℝ) : (Wave a x)^b=Wave (a*b) x:=by unfold Wave; rw[← Real.exp_mul, mul_right_comm]
lemma wave_sub (a:ℝ)(p:ℝ)(h:0 < p): ∀ᶠ x:ℝ in atTop, Wave a x ≤ x^p:=by
    by_cases he:a ≤0
    · refine (eventually_ge_atTop 1).mono (fun x hx=> ?_); exact ((wane x he).trans_eq (by simp[Wave])).trans (Real.one_le_rpow hx h.le)
    have hp:0 < a:= lt_of_not_ge he
    have hh:= Real.tendsto_log_atTop.eventually ((Real.isLittleO_pow_log_id_atTop (n:=2)).def (show 0 < p/a by positivity))
    filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with x hx hi
    have ht:0 < x:=lt_trans zero_lt_one hi
    have hv : a*RLog x ≤Real.log x*p:=by
       have hz := Real.log_pos hi
       have H: RLog x≤ p/a*Real.log x:=by unfold RLog; simpa only [Real.norm_eq_abs,id_eq, abs_of_nonneg hz.le,abs_of_nonneg (sq_nonneg (Real.log (Real.log x)))] using! hx
       refine (mul_le_mul_of_nonneg_left H hp.le).trans_eq ?_; field_simp
    rw[Real.rpow_def_of_pos ht]; exact Real.exp_monotone hv
lemma w0(x:ℝ): Wave 0 x=1:=by simp [Wave]
def ConstMass(a:ℝ)(f:ℝ→ℝ):Prop:=∀ b:ℝ,a<b→∀ᶠ x:ℝ in atTop,0 ≤ f x∧ f x≤ Wave b x
variable {F G:ℝ→ℝ}{a b c:ℝ}
lemma mass (h:0≤ a):ConstMass 0 (fun _=>a):= fun b hb=> ((awe hb).eventually_ge_atTop a).mono fun x hx=>⟨h,hx⟩
lemma ConstMass.inc(h:ConstMass a F)(he:a≤b):ConstMass b F:=fun _ hi=> h _ (lt_of_le_of_lt he hi)
lemma ConstMass.prod (h:ConstMass a F)(he:ConstMass b G) :ConstMass (a+b) (fun x=> F x*G x):=by
    intro c hc; let X:=(c-(a+b))/2; have hp:0 < X:=by unfold X; linarith
    filter_upwards [h (a+X) (lt_add_of_pos_right _ hp),he (b+X) (lt_add_of_pos_right _ hp)] with x hx hv
    exact ⟨mul_nonneg hx.1 hv.1, (mul_le_mul hx.2 hv.2 hv.1 ((wake ..).le)).trans_eq (by rw[walt]; unfold X; ring_nf)⟩
lemma ConstMass.gather (h:ConstMass a F) (he:ConstMass a G):ConstMass a (fun x=> F x+ G x):=by
    intro c hc; let b:= (a+c)/2; have hb:a<b:=by unfold b; linarith
    have hp:0<c-b:=by unfold b; linarith
    filter_upwards [h b hb, he b hb,(awe hp).eventually_ge_atTop 2] with x hx hv hk
    refine ⟨add_nonneg hx.1 hv.1,(add_le_add hx.2 hv.2).trans ?_⟩; rw[← two_mul]; apply (mul_le_mul_of_nonneg_right hk (wake b x|>.le)).trans_eq; rw[walt,sub_add_cancel]
lemma ConstMass.times(h:ConstMass a F) (c:ℝ)(hp:0 ≤ c):ConstMass a (fun x=>c*F x):=by simpa only [zero_add] using (mass hp).prod h
lemma ConstMass.pow(h:ConstMass a F)(n:ℕ):ConstMass (n*a) (fun x=> F x^n):=by
    induction n with
    | zero => simpa using mass zero_le_one
    | succ n ih=> have h:= ih.prod h; simpa only[pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using! h
lemma ConstMass.mono (h:ConstMass a F)(he:∀ᶠ x in atTop,0≤G x ∧ G x≤F x):ConstMass a G:=by intro d hd; filter_upwards[h d hd,he] with x ht hx using ⟨hx.1,hx.2.trans ht.2⟩
lemma ConstMass.cop(h:ConstMass 0 F)(he:ConstMass 0 G):ConstMass 0 (fun x=>F x*G x):=by simpa using! h.prod he
lemma ConstMass.crop(h:ConstMass 0 F)(k:ℕ):ConstMass 0 (fun x=>F x^k):=by simpa only [mul_zero] using! h.pow k
lemma logC: ConstMass 0 Real.log:=by
    intro b hb; have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    filter_upwards [ht.eventually_ge_atTop (1/b),eventually_gt_atTop (1:ℝ)] with x hx hX
    have hx:1/b ≤ ellZ (ellZ x):=hx; have hy:= Real.log_pos hX
    refine ⟨hy.le,?_⟩; apply (le_of_eq (Real.exp_log hy).symm).trans (Real.exp_monotone ?_); change ellZ (ellZ x) ≤ b* _; unfold RLog; have hp := (div_le_iff₀ hb).mp hx; have ht :0≤ ellZ (ellZ x):= le_trans (by positivity) hx; nlinarith only [mul_le_mul_of_nonneg_right hp ht]
lemma upperB : ConstMass 0 (fun x => (radiusB x:ℝ)) :=( (mass zero_le_one).gather (logC.crop 2)).mono (Eventually.of_forall fun x=> ⟨Nat.cast_nonneg _,by
    change ((Nat.ceil _):ℝ) ≤ _; exact le_trans (Nat.ceil_lt_add_one (sq_nonneg (ellZ x))|>.le) (add_comm ..).le⟩)
def rim (x:ℝ) := 1000*radiusB x
lemma rim_S : ConstMass 0 (fun x=> (rim x:ℝ)):=by simpa only[rim,Nat.cast_mul,Nat.cast_ofNat] using! upperB.times 1000 (by norm_num)
lemma rim_gt (a:ℕ):∀ᶠ x:ℝ in atTop, a≤ rim x:=by filter_upwards [(Work.E01.radiusB_tendsto).eventually_ge_atTop a] with x hx; unfold rim; omega
lemma waveM (a:ℝ):ConstMass a (Wave a):=fun b hb=> Eventually.of_forall fun x=>⟨(wake ..).le,wane x hb.le⟩
lemma ConstMass.under (T:ℕ→ℝ)(h:MarksP T){G:ℝ→ℕ} (hp:ConstMass 0 (fun i=>(G i:ℝ))): ConstMass 0 (T ∘ G):=by
    obtain ⟨hT,A,n,hA,h⟩:=h; exact ((((mass zero_le_one).gather hp).crop n).times A (by positivity)).mono (Eventually.of_forall fun i=> ⟨hT _,h _⟩)
lemma ConstMass.summit {V:Type}(T:Finset V)(A:V→ℝ→ℝ)(h:∀ i∈T, ConstMass a (A i)) : ConstMass a (fun x=> ∑ i∈T,A i x):=by
    classical
    induction T using Finset.induction with
    | empty=> intro b hb; exact Eventually.of_forall fun x=> ⟨by simp,by simp only[sum_empty]; exact (wake ..).le⟩
    | insert i P hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).gather (ih fun i hi=>h _ (mem_insert_of_mem hi))
end YM.Trace.Zn
