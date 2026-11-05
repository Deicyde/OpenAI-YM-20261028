import YM.TraceExtension.Det.Marge

/-! # Anchored charges for single site dilation markers -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k l m n r:ℕ}{α a b c τ A C D:ℝ}
variable {W:Type*}{g:W→Side}{F:∀ w,WildM G (g w) k m}{o:∀ w,Site (g w)}{Y:∀ w,Gal G (g w)}{R:W→PathData G}{μ:W→ℝ}

def stampQ (o:Site f)(x:Site f):ℝ:= if o=x then 1 else 0
lemma trivial_root {M: Funds (Lines G f k)}(x:Site f)(he:∀ i j,‖M i j‖ ≤ C)(h:0≤C)(hp:∀ i j,M i j≠0→ separation x i.1≤1∧i.1=j.1)(hw:0≤a) : PetW x (fun _=> M) a (C*Real.exp (2*a)) n:=by
    intro i j; refine pet_fixed _ x Prod.fst _ ?_
    by_cases hh:M i j=0
    · rw[hh,norm_zero]; exact mul_nonneg (mul_nonneg (mul_nonneg h (Real.exp_pos _|>.le)) (decay_pos ..|>.le)) (decay_pos ..|>.le)
    obtain ⟨hu,hv⟩:= hp i j hh; apply le_trans (he i j); rw [← hv, mul_assoc C, mul_assoc C];
    apply le_mul_of_one_le_right h; unfold Decay; rw [← Real.exp_add, ← Real.exp_add]; apply Real.one_le_exp; nlinarith[show (separation x i.1:ℝ) ≤ 1 by exact_mod_cast hu]
lemma flap_stamp (x:Site f)(b:Axis)(i:Site f): |stampQ x (i+step b)-stampQ x i| ≤ 2 ∧ (¬separation x i ≤ 1→ stampQ x i=0 ∧ stampQ x (i+step b)=0):=by
    constructor
    · unfold stampQ; split<;>split<;>norm_num
    intro h; simp only[stampQ]; rw [if_neg (show x ≠ i from fun e=>h (e ▸ by simp)), if_neg (show x≠ i+step b from fun e=>h (by rw[e, separation,add_comm i,add_sub_cancel_right];exact pdist_step b))]; exact ⟨rfl,rfl⟩
lemma trivial_deal (x:Site f)(b:Axis)(n:ℕ): PetW x (fun _=>deal G (stampQ x) b) 1 (2*Real.exp (2*1)) n:=by
    apply trivial_root x (fun i j=>?_) (by norm_num) (fun i j=> ?_) zero_le_one
    · unfold deal; rw[Matrix.of_apply]; dsimp only; split; rw [mul_one]; exact flap_stamp x _ _ |>.1; rw[mul_zero,norm_zero];norm_num
    unfold deal; rw[Matrix.of_apply]; intro hx; obtain ⟨hv,hz⟩:=mul_ne_zero_iff.mp hx
    split at hz; next e=> refine ⟨?_ ,by rw[e]⟩; by_contra h; obtain ⟨hk,he⟩:= flap_stamp x (axisEquiv.symm i.2.1) i.1|>.2 h; rw[hk,he,sub_self] at hv; exact hv rfl
    exact False.elim (hz rfl)
lemma trivial_mine (x:Site f)(b:Axis)(n:ℕ): PetW x (fun _=> mine G (stampQ x) b) 1 1 n:=by
    intro i j; refine pet_fixed _ x Prod.fst _ ?_
    unfold mine; simp only[Matrix.of_apply]; split
    next h=> rw [mul_one]; unfold stampQ; split
             next e=> rw[e,h]; change ‖(1:ℝ)‖ ≤ (1:ℝ)*Decay 1 i.1 i.1*Decay 1 i.1 i.1; simp [Decay]
             rw [norm_zero]; exact mul_nonneg (by unfold Decay; positivity) (decay_pos ..|>.le)
    rw [mul_zero,norm_zero]; exact mul_nonneg (by unfold Decay; positivity) (decay_pos ..|>.le)
lemma trivial_teat (x:Site f)(b:Axis)(n:ℕ)(r:ℕ): PetW x (fun _=> teat G (stampQ x) b r) 1 (2*Real.exp (2*1)) n:=by
    apply trivial_root x (fun i j=>?_) (by norm_num) (fun i j h=>?_) zero_le_one
    · by_cases hh:i=j; rw [hh,teat,diagonal_apply_eq]; exact (flap_stamp ..|>.1)
      rw[teat,diagonal_apply_ne _ hh,norm_zero]; norm_num
    by_cases hh:i=j
    · subst j; refine ⟨?_,rfl⟩; by_contra hp; obtain ⟨hy,hz⟩:= (flap_stamp x b i.1).2 hp; rw [teat,diagonal_apply_eq,hy,hz,sub_self] at h; exact h rfl
    rw [teat,diagonal_apply_ne _ hh] at h; exact False.elim (h rfl)
lemma mino (G:Gauge)(n:ℕ)(o:∀ w:W,Site (g w))(i:W→Axis): Pella o (fun w _=> mine G (stampQ (o w)) (i w)) n:=⟨1,1,zero_lt_one,zero_le_one,fun w=> trivial_mine _ _ _⟩
lemma locus_extra (h:Pella o (fun w=> tidal (Y w) ∘ input G (g w)) 2)(b:Axis):
    Pella o (fun w=> wB (stampQ (o w)) b (Y w) ∘ input G (g w)) 2∧ Pella o (fun w=>wG (stampQ (o w)) b ∘ input G (g w)) 2:=by
    have ht(k:ℕ):Pella o (fun w _=> teat G (stampQ (o w)) b k) 2:= ⟨1,_,zero_lt_one,show 0≤2*Real.exp (2*1) by positivity,fun w=> trivial_teat _ _ _ _⟩
    have hp: Pella o (fun w _=>deal G (stampQ (o w)) b) 2:= ⟨1, _,zero_lt_one,show 0≤ 2*Real.exp (2*1) by positivity,fun w=>trivial_deal _ _ _⟩
    have hm:= mino G 2 o (fun _=>b); have he:= Parked.mu G g 2; exact ⟨((h.down (hm.leftM he)|>.down hp).shee|>.up ((ht 1).cash _)), ((hm.rightM he).shee).down ((ht 0).cash _)⟩

lemma mica_budget (o:∀ w:W,Site (g w))(b:Axis) (hv:Parked (fun w=>shellB p (R w) (μ w) ∘ input G (g w)) 1)(ht:Parked (fun w=> shellG (μ w) ∘ input G (g w)) 1): CodeM o (fun w=> mica p (R w) (μ w) (stampQ (o w)) b∘ input G (g w)) 1:= juke_budget ((mino G 1 o (fun _=>b)|>.leftM ht).rightM hv)
-- log derivative locality
lemma log_budget (i:∀ w:W,Lines G (g w) 1) (F:∀ w,WildM G (g w) k k)(h:Parked F 2)(hx:Parked (fun w z=>(F w z)⁻¹) 1) (hv:∀ i,(F i 0).det≠0):
    Pico (fun w=>(i w).1) (fun w z=> fderiv ℝ (fun z=> Real.log (F w z).det) z (bolt (i w))) 1:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top
    have he : Pella (fun w=>(i w).1) (fun w z=> directionM (F w) z (bolt (i w))) 1:= ⟨_,_,show 0 < a/((1:ℕ)+1:ℝ)/2 by positivity,hC,fun w=>(f w).hit ha hC _⟩
    obtain ⟨b,D,hb,hD,hp⟩:= ((he.leftM hx).trace).top; refine ⟨_,_,hb,hD,fun w=>?_⟩
    have ht:Memo (F w) 0:=fun i j=> (f w i j).1
    refine (hp w).grows ?_; filter_upwards [ht.det_val.continuousAt.eventually_ne (hv w),eventually_memo ht] with z hz hf; exact (trace_log_first hf hz _).symm
lemma Flare.posit (h:Flare g R p α C)(hb:∀ w,0<μ w)(w): (stock p (R w) (μ w) (input G (g w) 0)).PosDef:=by obtain ⟨B,z,v,k,hb',hf,hx,hu⟩:=h.tanks w; rw[input_zero]; exact (hull_m (hb w) le_rfl hb' hf hx hu).1
lemma score_mark (h:Flare g R p α C)(ha:0<α)(hb:0<b)(hx:∀ w,b≤μ w∧μ w≤c)(i:∀ w,Lines G (g w) 1): Pico (fun w=>(i w).1) (fun w z=>fderiv ℝ (marke p (R w) (μ w) ∘ input G (g w)) z (bolt (i w))) 1:=by
    obtain ⟨hf,hg,hV,hW⟩:= h.house ha hb hx 2
    have ht(w):= hb.trans_le (hx w|>.1)
    have hv(w):=(h.posit ht w).det_pos.ne'
    have hr(w): (ammo (μ w) (input G (g w) 0)).det ≠ 0:=(ammo_safe _ (ht w)|>.det_pos).ne'
    have hu:= log_budget i _ hf (hV.tada (by omega)) hv
    have hy:= log_budget i _ hg (hW.tada (by omega)) hr
    obtain ⟨a,A,he,hA,hx⟩:= (hu.multi (1/2:ℝ) |>.minus hy).top; obtain ⟨a',C',_,_,f⟩:=hf.top; obtain ⟨c',d,_,_,g'⟩:=hg.top
    refine ⟨a,A,he,hA,fun w=>?_⟩; apply (hx w).grows
    let F:= stock p (R w) (μ w) ∘ input G (g w); let L:= ammo (μ w) ∘ input G (g w)
    let A(x):=Real.log (F x).det; let N(x):=Real.log (L x).det
    have hF: Memo F 0:= fun i j=> (f w i j).1
    have hL: Memo L 0:= fun i j=> (g' w i j).1
    filter_upwards [(hF.det_val.log (hv w)).eventually (by simp), (hL.det_val.log (hr w)).eventually (by simp)] with z hf hg
    rw [show marke p (R w) (μ w) ∘ input G (g w)=(fun x=> (1/2:ℝ) • A x)- N from funext fun x=>by change A x/2-N x= ((1/2:ℝ)*A x)-N x; ring]
    rw [fderiv_sub _ (hg.differentiableAt (by simp)),fderiv_fun_const_smul _]; rfl
    any_goals exact hf.differentiableAt (by simp)
    exact (hf.const_smul _).differentiableAt (by simp)
lemma mark_kin (h:Flare g R p α C)(ha:0<α)(hb:0<b)(hx:∀ w,b≤μ w∧μ w≤c): Parked (fun w (_z:Link G (g w))=> beamH (marke p (R w) (μ w)) (1: Config G (g w))) 0:=by
    let w(v: (w:W) × Lines G (g w) 1):= v.1
    let o(v : (w:W) × Lines G (g w) 1) : Lines G (g (w v)) 1:=v.2
    obtain ⟨A,D,hA,hD,H⟩:= (score_mark (R:=fun v=> R (w v)) (μ:=fun v=> μ (w v)) ⟨fun v=> h.tanks (w v)⟩ ha hb (fun i=>hx (w i)) o).top
    refine ⟨_,_,hA,hD,fun z i j=>?_⟩; let M:= marke p (R z) (μ z) (f:=g z); let L:= M ∘ input G (g z); let ψ: Config G (g z):=1
    obtain ⟨B,v,s,t,hp,hf,hr,hs⟩:= h.tanks z; have hμ:= hb.trans_le (hx z|>.1); have hu: (stock p (R z) (μ z) ψ).det≠0:= (hull_m hμ le_rfl hp hf hr hs).1.det_pos.ne'
    have hL: ContDiffAt ℝ ω L 0:= (dyed_mark hp hμ hu).dye
    have ht := H ⟨z,j⟩ |>.halp (m:=0) i; have hh:=ht.2 0 le_rfl Fin.elim0;
    change ‖entry (fun v=> fderiv ℝ (fun z=> fderiv ℝ L z (bolt j)) v (bolt i)) 0 Fin.elim0‖ ≤ _ at hh
    simp only [entry,iteratedFDeriv_zero_apply,spanSites,Finset.sum_of_isEmpty,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hh
    apply pet_fixed
    rw [beam_p, show bal _ _=L from funext fun x=> by simp[bal];rfl]
    rw [divided _ _ hL,bockat,bockat] at hh; rw [decay_comm]; exact hh
end YM.Trace.Det
