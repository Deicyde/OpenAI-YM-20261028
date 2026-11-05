import YM.OPE.Height

/-!
# Orders against the stronger logarithmic scale

Do not use `RateLE` in place of the eventual inequality when one only has subpower
on this log scale. `Wallet` means a *fixed eventual power*, in the joint geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Lattice RG
open scoped Topology BigOperators
variable {ι ι' I V X Y : Type*} {l l' : Filter ι} {φ : Filter ι'} {T : ι→ℝ} {u : ι'→ι}
    {f : ι→X} {g : ι→Y} {f' : ι→X} {x y z : ι→ℝ}

def Wallet [Norm X](l:Filter ι)(T:ι→ℝ)(f:ι→X):Prop:= ∃ p:ℕ, ∀ᶠ i in l, ‖f i‖ ≤ T i^p
variable (hT:Tendsto T l atTop)
namespace Wallet
lemma transfer [Norm X][Norm Y] (h:Wallet l T f)(hf:∀ᶠ i in l, ‖g i‖ ≤ ‖f i‖) : Wallet l T g:=
 h.imp (fun _ hh=>hf.mp ((hh).mono fun _ hi hb=> hb.trans hi)) -- mp order?
lemma of_est [Norm X](h:Wallet l T x)(hf:∀ᶠ i in l, ‖f i‖ ≤ x i): Wallet l T f:= h.transfer (hf.mono fun i hi=> hi.trans (Real.le_norm_self _))
lemma of_le (h: Wallet l T x)(hf:∀ᶠ i in l, 0≤y i)(hh:∀ᶠ i in l,y i ≤ x i) : Wallet l T y:= by
    apply h.of_est; filter_upwards [hf,hh] with i hi he; rwa [Real.norm_of_nonneg hi]
lemma of_le' (h: Wallet l T x)(hf:∀ᶠ i in l, 0<y i)(hh:∀ᶠ i in l,y i ≤ x i) : Wallet l T y:= h.of_le (hf.mono fun _ hi=> hi.le) hh
lemma congr [Norm X](h:Wallet l T f)(hf:f =ᶠ[l] f'): Wallet l T f':= h.transfer (hf.mono fun _ hi => by rw [hi]) -- simp
lemma small [Norm X](h:Wallet l T f)(he:l'≤l):Wallet l' T f:= h.imp (fun _ hh=> hh.filter_mono he)
lemma comp [Norm X](h:Wallet l T f)(hp:Tendsto u φ l) : Wallet φ (T ∘ u) (f ∘ u):= h.imp fun _ hh=> hp.eventually hh
include hT
lemma raise [Norm X](h:Wallet l T f)(ht:Wallet l z T) : Wallet l z f := by
   obtain ⟨p,h⟩:=h; obtain ⟨v,hv⟩:= ht; refine ⟨v*p,?_⟩; filter_upwards [h,hv,hT.eventually_ge_atTop 0] with i hi hv ht; rw [pow_mul]; exact hi.trans (pow_le_pow_left₀ ht ((Real.le_norm_self _).trans hv) p)
omit hT
lemma of_rate [Norm X]{a : ℝ} (hT:Tendsto T l atTop)(h:RateLE l (Real.log ∘ T) f a) : Wallet l T f:=by
   obtain ⟨p,hp⟩ := exists_nat_gt a
   refine ⟨p,?_⟩; filter_upwards [hT.eventually_gt_atTop 0,h p hp] with i hi hv
   rwa [Function.comp_apply, Real.exp_nat_mul,Real.exp_log hi] at hv
include hT
lemma clock : RateIs l T T 0:= ⟨hT.eventually_gt_atTop 0, Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hT⟩
lemma subpower [SeminormedAddGroup X](h: Wallet l T f): RateLE l T f 0:=by
    obtain ⟨p,h⟩:=h; exact (((clock hT).power p).swap (mul_zero _)).pays hT|>.of_norm_le h
lemma absolute [Norm X](b:ℝ) (hh:∀ᶠ i in l, ‖f i‖≤b): Wallet l T f:= by
    have he:= hh.and (hT.eventually_ge_atTop b); exact ⟨1, he.mono fun i hi=> hi.1.trans (by simpa only [pow_one] using hi.2)⟩
lemma const [Norm X](x:X):Wallet l T (fun _=>x):= absolute hT ‖x‖ (Eventually.of_forall fun _=>le_rfl)
lemma max_price [Norm X] (h:Wallet l T f):∃ a : ℕ, ∀ p:ℕ,a≤p→ ∀ᶠ i in l,‖f i‖ ≤ T i^p :=by
    obtain ⟨p,hp⟩ := h; refine ⟨p,fun i hi=>?_⟩; filter_upwards [hp,hT.eventually_ge_atTop 1] with j hj hq using hj.trans (pow_le_pow_right₀ hq hi)
lemma id : Wallet l T T := by
    refine ⟨1, (hT.eventually_ge_atTop 0).mono (fun i hi=> ?_)⟩; rw [Real.norm_of_nonneg hi,pow_one]
lemma add [SeminormedAddGroup X](h: Wallet l T f)(hh: Wallet l T f') : Wallet l T (fun i=> f i+f' i):= by
    obtain ⟨p,hp⟩:=h.max_price hT; obtain ⟨p',hp'⟩:= hh.max_price hT; let v:=max p p'; refine ⟨v+1,?_⟩; filter_upwards [hp v (le_max_left ..), hp' v (le_max_right ..), hT.eventually_ge_atTop 2] with i h1 h2 H
    exact (norm_add_le ..).trans ((add_le_add h1 h2).trans ((show T i^v+T i^v ≤ T i^(v+1) by rw [← mul_two,pow_succ]; exact mul_le_mul_of_nonneg_left H (pow_nonneg (zero_le_two.trans H) _))))
lemma sum [SeminormedAddCommGroup X]{s:Finset I}{f:I→ι→X}(h:∀ i∈s,Wallet l T (f i)) : Wallet l T (fun i=> ∑ j∈s,f j i):=by
    classical
    induction s using Finset.induction with
    | empty => simpa using const hT (0:X)
    | insert j s hJ ih => simpa only [Finset.sum_insert hJ] using (h j (Finset.mem_insert_self ..)).add hT (ih fun i hi=> h i (Finset.mem_insert_of_mem hi)) -- order
omit hT
lemma norm [SeminormedAddGroup X] (h:Wallet l T f) : Wallet l T (fun i=>‖f i‖) := h.transfer (Eventually.of_forall fun _=> by simp)
lemma neg [SeminormedAddGroup X] (h: Wallet l T f):Wallet l T (fun i=> -f i):= h.transfer (Eventually.of_forall fun _=>by simp)
lemma bind [SeminormedAddGroup X][SeminormedAddGroup Y][Norm V]{u:ι→V}(h:Wallet l T f)(hf:Wallet l T g)(hu:∀ᶠ i in l, ‖u i‖≤ ‖f i‖* ‖g i‖):Wallet l T u := by
    obtain ⟨p,h⟩:=h; obtain ⟨q,hf⟩:= hf; refine ⟨p+q,?_⟩; filter_upwards [hu,h,hf] with i hi h hf; rw [pow_add]; exact hi.trans (mul_le_mul h hf (norm_nonneg _) ((norm_nonneg _).trans h))
lemma mul [SeminormedRing X](h: Wallet l T f)(hf:Wallet l T f') : Wallet l T (fun i=> f i*f' i):= h.bind hf (Eventually.of_forall fun _=> norm_mul_le ..)
lemma smul [NormedField X] [SeminormedAddCommGroup Y][NormedSpace X Y](h:Wallet l T f)(hf: Wallet l T g):Wallet l T (fun i=> f i • g i):= h.bind hf (Eventually.of_forall fun _=> norm_smul_le ..)
include hT
lemma from_tends [NormedAddGroup X]{a:X}(h:Tendsto f l (𝓝 a)): Wallet l T f:= by
    exact absolute hT (‖a‖+1) (h.norm.eventually (ge_mem_nhds (lt_add_of_pos_right _ one_pos))) -- name
lemma of_strict [NormedAddGroup X]{a:ℝ}(h:RateLE l T f a) (ha:a<0): Wallet l T f:=from_tends hT (h.tends ha hT)
lemma sub [SeminormedAddGroup X](h:Wallet l T f)(hh:Wallet l T f'): Wallet l T (fun i=> f i-f' i):= by simpa only [sub_eq_add_neg] using h.add hT hh.neg
omit hT in
lemma invLe (h:Wallet l T (fun i=> (x i)⁻¹))(hx:∀ᶠ i in l,0<x i)(hf:∀ᶠ i in l,x i ≤ y i):Wallet l T (fun i=>(y i)⁻¹):= h.of_le'
       ((hx.and hf).mono fun i hi=>inv_pos.mpr (lt_of_lt_of_le hi.1 hi.2)) ((hx.and hf).mono fun i hi=> inv_anti₀ hi.1 hi.2)
omit hT in
lemma div (h:Wallet l T x)(hf:Wallet l T (fun i=>(y i)⁻¹)): Wallet l T (fun i=>x i/y i):=by simpa only [div_eq_mul_inv] using h.mul hf
lemma pow [SeminormedRing X] (h:Wallet l T f)(p:ℕ): Wallet l T (fun i=> f i^p):= by
    induction p with
    | zero => simpa using const hT (1:X)
    | succ p ih => simpa only [pow_succ] using ih.mul h
lemma prod [SeminormedCommRing X]{s:Finset I}{f:I→ι→X}(h:∀ i∈s,Wallet l T (f i)):Wallet l T (fun i=>∏ j∈s,f j i):=by
    classical
    induction s using Finset.induction with
    | empty => simpa using const hT (1:X)
    | insert j s hJ ih=> simpa only [Finset.prod_insert hJ] using (h j (Finset.mem_insert_self ..)).mul (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
end Wallet
structure ValueStamp (l:Filter ι)(T x:ι→ℝ) : Prop where
    profit : ∀ᶠ i in l, 0 < x i
    up : Wallet l T x
    down : Wallet l T (fun i=> (x i)⁻¹)
namespace ValueStamp
lemma congr (h:ValueStamp l T x)(hf:x =ᶠ[l] y): ValueStamp l T y:=
    ⟨(hf.and h.profit).mono fun i hi=> hi.1 ▸ hi.2,h.up.congr hf,h.down.congr (hf.mono fun i hi=> by simp only [hi])⟩
include hT in
lemma raise (h:ValueStamp l T x)(ht:Wallet l z T) : ValueStamp l z x:=
    ⟨h.profit,h.up.raise hT ht,h.down.raise hT ht⟩ -- hT omit
lemma inv (h:ValueStamp l T x): ValueStamp l T (fun i=> (x i)⁻¹):=
    ⟨h.profit.mono fun _ hi=> inv_pos.mpr hi,h.down,by simpa using h.up⟩
lemma mul (h:ValueStamp l T x)(hf: ValueStamp l T y) : ValueStamp l T (fun i=>x i*y i):=
    ⟨(h.profit.and hf.profit).mono fun _ hi=>mul_pos hi.1 hi.2,h.up.mul hf.up,by simp_rw [mul_inv_rev]; exact hf.down.mul h.down⟩
lemma div (h:ValueStamp l T x)(hf:ValueStamp l T y):ValueStamp l T (fun i=>x i/y i):=by simpa only [div_eq_mul_inv] using h.mul hf.inv
include hT
lemma const {a:ℝ}(ha:0<a):ValueStamp l T (fun _=>a):=⟨Eventually.of_forall (fun _=> ha),Wallet.const hT _,Wallet.const hT _⟩
lemma atT : ValueStamp l T T:= ⟨hT.eventually_gt_atTop 0,Wallet.id hT,Wallet.from_tends hT (tendsto_inv_atTop_zero.comp hT)⟩
lemma zeroCost (h:ValueStamp l T x) : RateIs l T x 0:= by
    obtain ⟨p,hp⟩:= h.down; refine RateIs.of_sandwich ((((Wallet.clock hT).power p).inv).swap (by ring)) (h.up.subpower hT) ?_ (Eventually.of_forall fun _=> le_rfl) hT
    filter_upwards [hp,h.profit,hT.eventually_gt_atTop 0] with i hi hx ht using (inv_le_comm₀ (pow_pos ht p) hx).2 ((Real.le_norm_self _).trans hi)
lemma add (h:ValueStamp l T x)(hf:ValueStamp l T y):ValueStamp l T (fun i=>x i+y i):=
    ⟨(h.profit.and hf.profit).mono fun _ hi=> add_pos hi.1 hi.2,h.up.add hT hf.up,h.down.invLe h.profit (hf.profit.mono fun _ hi=> le_add_of_nonneg_right hi.le)⟩
lemma pow (h:ValueStamp l T x)(p:ℕ):ValueStamp l T (fun i=> x i^p):=
    ⟨h.profit.mono fun _ hi=>pow_pos hi _, h.up.pow hT p, by simpa only [inv_pow] using h.down.pow hT p⟩
lemma prod {s:Finset I}{f:I→ι→ℝ}(h:∀ i∈s,ValueStamp l T (f i)):ValueStamp l T (fun i=>∏ j∈s,f j i):=by
    classical
    induction s using Finset.induction with
    | empty => simpa using const hT one_pos
    | insert j s hJ ih=> simpa only [Finset.prod_insert hJ] using (h j (Finset.mem_insert_self ..)).mul (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
end ValueStamp
end YM.OPE
