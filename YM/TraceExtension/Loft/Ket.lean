import YM.TraceExtension.Loft.Pen
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W ι α:Type} [Fintype α][DecidableEq α]{n:ℕ}{σ A r:ℝ}{X:Burst W ι}{U:W→Film ι α α}{F:ι→Track→Track→ CompM α α}{T μ:W→ℝ}
variable (a:ι)(h:ColdR X T μ r)
structure Sib (U:W→Film ι α α)(a:ι): Prop where
   pay:∃ A σ,0 ≤ A ∧ 0 < σ ∧ ∀ i,Skew (U i) σ A
   front: ∀ w i j, Stationary.Rays 2 (fun k=> legA (U w) k i j)
   top: ∀ w i j, Stationary.Rays 1 (fun k=> legB (U w) a k i j)
lemma sib (h:Floe X U F r)(hx:∀ w,X.mark w=a) (hp:0<σ)(hA:0≤A)(hv:∀ w,Skew (U w) σ A): Sib U a :=by
   refine ⟨⟨_,_,hA,hp,hv⟩,fun w i j=>?_,fun w i j=>?_⟩
   · have ht:= h.spot0 w i j
     let f:= fun k:Track=> legA (U w) k i j; let g:=fun x:Track=> skull x α i j; change Stationary.Rays 2 f
     rw [show f= f-g+g from (sub_add_cancel ..).symm]; exact (ht.weaker (by decide)).add (skull_ray _ i j)
   have ht:= h.spot1 w i j; rw[hx] at ht
   let f(x:Trail):= legB (U w) a x i j; let g(x:Trail):= F a x.1 x.2 i j
   change Stationary.Rays 1 f; rw [show f= f-g+g from (sub_add_cancel ..).symm]; exact (ht.weaker (by decide)).add (h.paid a i j |>.2)
variable (hq:Sib U a)
-- direction fixed vector. pivot X.lens; set ext step0 alone
abbrev summitM (V:Film ι α α)(μ:ℝ):= V.plus (icing α ι μ)
abbrev Mint (T:W→ℝ)(p:Track)(i:W)(t:ℝ):Track:= t • (T i • p)
abbrev rankP (X:Burst W ι)(T:W→ℝ)(p:Track)(i:W)(t:ℝ):Track:= X.lens i+ Mint T p i t
section first
include h hq
lemma pact_tab (p:Track): CashV n (T^2) (fun i t=>legA (summitM (U i) (μ i)) (rankP X T p i t)) :=by
    obtain ⟨A,s,hA,hs,K⟩:= hq.pay; have hh:T^ (2:ℕ) ≥ 0:=fun i=>pow_nonneg (h.lower i|>.le) _
    let F(i:W)(t):= (U i).tab (axes (rankP X T p i t))
    have hx:CashV n (T^2) F:=by
       refine ⟨hh,fun i j=>?_⟩
       -- n<2? buy n+2 then weaken
       have he := shellu (t:=X.lens) (v:=fun i=>T i • p) (T:=T) (lo_h (n:=n+2) K hs i j) (fun w=> hq.front w i j) (by omega) h.lower h.upper h.topC 1 ‖p‖ zero_le_one (norm_nonneg _) (fun w=> by rw[mul_one]; exact (orbit_at _).trans (h.norm w)) (fun w=> Eq.le (by rw[norm_smul,Real.norm_of_nonneg (h.lower w|>.le)]))
       obtain ⟨C,hC,H⟩:=he.keep; exact ⟨hh,C,hC,fun i=> (H i).order (by omega)⟩
    have hv: CashV n (T^2) (fun i (_:ℝ)=> ((μ i^2:ℝ):ℂ) • (1:CompM α α)):=by
       refine ⟨hh,fun i j=> nbill hh (A:= (1:ℝ)) zero_le_one (fun w=>?_ )⟩
       refine (flux_tilt ( ((μ w^2:ℝ):ℂ) • (1:CompM α α)) i j).trans ?_; rw [flux_cost,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),one_mul]; refine le_trans (mul_le_of_le_one_right (sq_nonneg _) flux_one) (pow_le_pow_left₀ (h.pos w|>.le) (h.lease w) _)
    exact sumM hx hv
lemma pact_spot(p q:Track) : CashV n T (fun w t=> legB (summitM (U w) (μ w)) a (Mint T p w t,rankP X T q w t)) :=by
    obtain ⟨A,s,hA,hs,K⟩:= hq.pay; have ht:T≥0:=fun i=>h.lower i|>.le; refine ⟨ht,fun i j=>?_⟩
    let x w:Trail:=(0,X.lens w); let v w:Trail:= T w • (p,q)
    have hx:= shellu (T:=T) (pin_h (n:=n+1) K hs i j a) (fun w=>hq.top w i j) (by omega) x v h.lower h.upper h.topC 1 ‖(p,q)‖ zero_le_one (norm_nonneg _) (fun i=>by rw[mul_one]; simp only[x, Prod.norm_def,norm_zero,max_le_iff]; exact ⟨ht i,(orbit_at _).trans (h.norm i)⟩) (fun w=>by unfold v; rw[norm_smul, Real.norm_of_nonneg (h.lower w|>.le)])
    rw[pow_one] at hx; obtain ⟨C,hC,H⟩:=hx.keep; simp only [legB,rankP, Mint,x,v,Prod.smul_mk,Prod.fst_add,Prod.snd_add,zero_add,summitM,Film.plus,icing,Film.cardF,add_zero] at H ⊢; exact ⟨ht,C,hC,fun w=> (H w).order (by omega)⟩
lemma pact_arc(p q:Track): CashV n 1 (fun w t=> legC (summitM (U w) (μ w)) a a (Mint T p w t,Mint T q w t,X.lens w)):=by
    obtain ⟨A,s,hA,hs,K⟩:=hq.pay; refine ⟨fun _=>zero_le_one,fun i j=>?_⟩
    let f (w) (z:Trest):= legC (U w) a a z i j; let V(p':W): Trest:=(0,0,X.lens p'); let b:Trest:=(p,q,0); let v w:Trest:=T w • b
    obtain ⟨D,hD,H⟩:=(row_h (n:=n) K hs i j a a).top; let R:=1+r*‖b‖; have hR:1 ≤ R:=le_add_of_nonneg_right (mul_nonneg h.topC (norm_nonneg _))
    refine ⟨fun _=>zero_le_one, D*R^n,mul_nonneg hD (by have hu:=zero_le_one.trans hR; positivity),fun w=>?_⟩
    have he: ‖v w‖ ≤ R:=by unfold v; rw [norm_smul,Real.norm_of_nonneg (h.lower w|>.le)]; exact (mul_le_mul_of_nonneg_right (h.upper w) (norm_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)
    have hv:=chord_h (F:=f w) (V w) (v w) 0 (H w _) he hR
    simp only [summitM, legC,Film.plus,icing,Film.cardF,add_zero,Pi.one_apply,mul_one]; apply Allows.germ hv; refine Eventually.of_forall fun x=> ?_; simp [f,v,Mint,V,b,legC]
end first
section kit
include h hq
variable (he:Tall X (T^2) (fun i=> summitM (U i) (μ i)))
include he
lemma pact_cap (p:Track): CashV n (T^ (2:ℕ))⁻¹ (fun i t=>legA (summitM (U i) (μ i)).back (rankP X T p i t)):=by
    let F(i:W)(t):= (summitM (U i) (μ i)).tab (axes (rankP X T p i t))
    have hh(i): F i 0=(summitM (U i) (μ i)).tab (axes (X.lens i)):=by unfold F rankP Mint;rw[zero_smul,add_zero]
    obtain ⟨C,hC,hv⟩:= he.marble
    refine slit (N:=F) (pact_tab a h hq p) he.positive (fun w=>by rw[hh];exact he.keeps w) (A:=C) (fun w=>by rw [hh, ← div_eq_mul_inv]; exact hv w) hC
omit h hq he in
lemma Mint_add (p q:Track)(w:W)(t:ℝ): axes (rankP X T q w t)+axes (Mint T p w t)=axes (rankP X T (q+p) w t):=by rw [← axes_add]; congr 1; unfold rankP Mint; rw[smul_add,smul_add,add_assoc]
lemma pact_b (p q:Track): CashV n (T^(3:ℕ))⁻¹ (fun w t=> legB (summitM (U w) (μ w)).back a (Mint T p w t,rankP X T q w t)):=by
    have hx:= negM (mulM (mulM (pact_cap a h hq (n:=n) he (q+p)) (pact_spot a h hq p q)) (pact_cap a h hq he q))
    rw[show (T^2)⁻¹*T*(T^2)⁻¹=(T^3)⁻¹ from funext fun i=>by change (T i^2)⁻¹*T i*(T i^2)⁻¹=(T i^3)⁻¹;field_simp[(h.lower i).ne']] at hx
    simp only [legB,Film.back,Film.vSpot,Film.coupon]; simp_rw [Mint_add]; exact hx
lemma pact_c (p q:Track): CashV n (T^ (4:ℕ))⁻¹ (fun w t=>legC (summitM (U w) (μ w)).back a a (Mint T p w t, Mint T q w t,X.lens w)):=by
    let F0(w):= summitM (U w) (μ w)
    let p':=Mint T p; let q':=Mint T q; let f w t:= axes (p' w t); let g w t:=axes (q' w t); let x w:=axes (X.lens w)
    have h0(i:W)(t:ℝ): rankP X T 0 i t=X.lens i:=by simp [rankP, Mint]
    have hw:= pact_cap a h hq (n:=n) he 0; simp_rw [h0] at hw
    have hd(U V: Track) : CashV n (T^(2:ℕ))⁻¹ (fun i t=> (F0 i).vSpot a (axes (Mint T V i t)) (x i+axes (Mint T U i t))*(F0 i).spot a (axes (Mint T U i t)) (x i)):=by
        have hz:= pact_spot a h hq (n:=n) U 0; simp_rw[h0] at hz
        have hp:= pact_b a h hq (n:=n) he V U; simp_rw[legB,rankP,axes_add] at hp; have hx:= mulM hp hz; rw[show (T^ (3:ℕ))⁻¹*T=(T^(2:ℕ))⁻¹ from funext fun i=>by change (T i^3)⁻¹*T i= (T i^2)⁻¹; field_simp[(h.lower i).ne']] at hx; exact hx
    have hh:=mulM (pact_cap a h hq he (p+q)) (pact_arc a h hq (n:=n) p q); rw [mul_one] at hh
    have hx(i:W)(t): axes (rankP X T (p+q) i t)=x i+(f i t+ g i t):=by unfold rankP f g p' q' x; simp_rw [Mint,smul_add,axes_add]
    simp_rw [legA, hx] at hh
    have hk:= negM (mulM (sumM (sumM (hd p q) (hd q p)) hh) hw)
    rw [show (T^ (2:ℕ))⁻¹*(T^(2:ℕ))⁻¹=(T^ (4:ℕ))⁻¹ from funext fun i=>by change (T i^2)⁻¹*(T i^2)⁻¹=(T i^4)⁻¹;field_simp[(h.lower i).ne']] at hk;exact hk
end kit
end YM.Trace.Loft
