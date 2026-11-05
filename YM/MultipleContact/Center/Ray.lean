import YM.MultipleContact.Center.Base
import YM.MultipleContact.Pair.Arrow

/-! Taylor shift at a strict field slot tested against an arbitrary separated signed context. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.MultipleContact.Centered
open Filter Set Function MeasureTheory Extraction Spec Table Script Scene Drama ScheduleRow Bunching MergeProof Two RG Ward
open scoped Classical Topology BigOperators ContDiff

variable {G:Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}
variable (H:S.Hierarchy)(hP:P.Derivatives S)(hs:P.Inclusions S)
def rayObserve {S:Table L} (a:Grammar (Alpha S)){d:ℕ}(y:S.Field d)(z:E4):=evaluation S (insertion S z y*a)
private def headPoints {n:ℕ} (z:E4)(p:Fin n → Alpha S):Points (n+1):=Points.cons z (points (Prod.snd ∘ p))
private def packetRead {n:ℕ}(y:E4)(p:Fin n→ Alpha S){d:ℕ}(u:S.Field d):=S.useAt S (headPoints y p) (Fin.cons (⟨d,u⟩:S.Tag) (Prod.fst ∘ p))
private lemma eval_first {n d:ℕ}(T:S.Symmetric)(z:E4)(p:Fin n→ Alpha S)(u:S.Field d):rayObserve (spell p) u z = readFin S (Fin.cons ((⟨d,u⟩,z):Alpha S) p):= by
           rw [rayObserve,insertion,show stamp ((_,_):Alpha S)*spell p= spell (Fin.cons (α:=fun i:Fin (n+1)=>Alpha S) ((⟨d,u⟩,z):Alpha S) p) from (by unfold spell; rw [Fin.prod_univ_succ];rfl), eval_fin S T]
private lemma packet_valid {n d:ℕ}(H:S.Symmetric)(z:E4)(v:S.Field d)(p:Fin n→ Alpha S)(hc:headPoints z p∈conf (n+1)):rayObserve (spell p) v z=packetRead z p v:=by
      let f:=Fin.cons (α:=fun _:Fin (n+1)=>Alpha S) ((⟨d,v⟩,z):Alpha S) p
      have hx(i:Fin (n+1)):(f i).2=headPoints z p i:=Fin.cases rfl (fun _=>rfl) i
      rw [eval_first H,readFin,if_pos (show clear S f from fun i j h=>hc (by simp only [← hx];exact h)),packetRead]
      congr 1
      · ext1 i; exact hx i
      · funext i; exact Fin.cases rfl (fun _=>rfl) i
private lemma rayValid {p:Grammar (Alpha S)}{z:E4}(hp:Precise S p {z}): ∀ i∈p.coeff.support,headPoints z (pickFrame S i) ∈ conf _:=by
          intro i hi
          have h:clear S (pickFrame S i):=(hp i hi).1
          have hne(j:Fin i.card):(pickFrame S i j).2 ≠ z:=fun e=>Set.disjoint_left.mp ((hp i hi).2) (by rw [names_iff]; exact ⟨_, ((letters_frame i).choose_spec.symm ▸ (letters_image _).mpr ⟨j,Prod.eta ..⟩)⟩) (show (pickFrame S i j).2∈({z}:Set E4) from e ▸ Set.mem_singleton z) -- fix
          change headPoints z (pickFrame S i)∈conf (i.card+1)
          unfold headPoints; exact fun j=>Fin.cases (fun l=>Fin.cases (fun _=>rfl) (fun l e=> (hne l e.symm).elim) l) (fun j l=> Fin.cases (fun e=>(hne j e).elim) (fun l e=> Fin.succ_inj.mpr (h e)) l) j
include H
private lemma packetSite {n d:ℕ}(a:Fin n→ Alpha S)(z y:E4)(v:S.Field d)(hc:headPoints (z+y) a ∈ conf (n+1)){p:Points n}(hp:∀i:Fin n,p i=(a i).2-z):Two.siteValue S (fun i:Fin n=> (⟨((a i).1).1,S.representative _ ((a i).1).2⟩:L.Token)) d v y p=rayObserve (spell a) v (z+y):=by
            rw [Two.siteValue,packet_valid H.laws.toSymmetric (z+y) v _ hc,packetRead]
            have hr:headPoints (z+y) a=Points.across z (Points.cons y p):=by ext1 i;exact Fin.cases (by simp [headPoints,Points.cons,add_comm]) (fun j=> by simp [headPoints,Points.cons,hp]) i
            have he(i:(Fin n)): S.classTokens (⟨((a i).1).1,S.representative _ ((a i).1).2⟩:L.Token)=(a i).1:=by simp only [Table.classTokens, S.rep] -- eta
            have hqq: S.classTokens ∘ (fun i:Fin n=> (⟨((a i).1).1,S.representative _ ((a i).1).2⟩:L.Token))=Prod.fst ∘ a:=funext he
            have hy: Points.cons y p∈conf _:=fun i j e=> hc (show (headPoints (z+y) a i)=(headPoints (z+y) a j) from (by rw [hr];change Points.cons y p i+z=Points.cons y p j+z;rw [e]))
            rw [hr,hqq,fixedValue]; let r:Fin (n+1)→S.Tag:=Fin.cons (α:=fun _=>S.Tag) (⟨d,v⟩:S.Tag) (Prod.fst ∘ a); exact (H.translations _ _ hy _ (fun i=>⟨_,S.representative (r i).1 (r i).2⟩)).symm
omit H in
private lemma clearPath {n:ℕ}(a:Fin n→Alpha S)(x y:E4)(t:ℝ)(hc:headPoints (x+t•y) a∈ conf (n+1)):∀ᶠ s in 𝓝 t,headPoints (x+s•y) a∈conf (n+1):=by
             have h : ContinuousAt (fun s:ℝ=>headPoints (x+s•y) a) t:=by
               unfold headPoints Points.cons points; refine (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr fun i=>?_)
               exact Fin.cases (by simpa only [Fin.cons_zero] using! (continuousAt_const (y:=x) (x:=t)).add (continuousAt_id (x:=t)|>.smul (continuousAt_const (y:=y)));) (fun j=>by simp only [Fin.cons_succ];fun_prop) i
             exact h.eventually ((conf_open _).mem_nhds hc)
include hP
lemma ray_derivative {z x:E4}{k:ℕ}{v:S.Field k}{a:Grammar (Alpha S)}(i:ℕ)(t:ℝ)(hc:Precise S a {z+t•x}):let f(n:ℕ)(s:ℝ):= rayObserve a (arrow P k x n v) (z+s•x); HasDerivAt (f i) (f (i+1) t) t:=by
         intro f; let g (j)(a:Multiset (Alpha S))(s:ℝ):= rayObserve (spell (pickFrame S a)) (arrow P k x j v) (z+s•x)
         have hf(i)(s):f i s=∑m∈a.coeff.support,a.coeff m • g i m s:=by
             unfold f rayObserve; nth_rw 1 [sum_terms a]; rw [Finset.mul_sum,map_sum]
             apply Finset.sum_congr rfl; intro m hm; unfold g rayObserve;rw [mul_smul_comm,map_smul];congr 2
         simp_rw [show f i = _ from funext (hf i),hf _ t]; apply HasDerivAt.fun_sum; intro m hm
         let p:=pickFrame S m
         have ht:= rayValid hc m hm
         refine (HasDerivAt.const_smul (f:=g i m) (a.coeff m) ?_)
         let l:=points (fun j=>(p j).2-z); let q:Fin m.card→L.Token:=fun j=>⟨_,S.representative _ ((p j).1).2⟩
         let b(s:ℝ):= siteValue S q (k+i) (arrow P k x i v) (s•x) l
         have he' (j:ℕ)(s:ℝ)(hs:headPoints (z+s•x) p ∈ conf _): g j m s = Two.siteValue S q (k+j) (arrow P k x j v) _ l:= (packetSite H _ _ _ _ hs (fun _=>rfl)).symm
         have he:g i m =ᶠ[𝓝 t] b:= (clearPath _ _ x _ ht).mono (he' i)
         suffices hh:HasDerivAt b (Two.siteValue S q (k+i+1) (axisStep P (k+i) x (arrow P k x i v)) _ l) t by rw [he' (i+1) t ht]; exact hh.congr_of_eventuallyEq he
         apply step_deriv P (k+i) _ _ H.smooth hP
         intro r c heq; refine ht ?_
         have heq': headPoints (z+t•x) p = Points.across z (Points.cons (t•x) l):=by ext1 j;exact Fin.cases (by simp [headPoints,Points.cons,add_comm]) (fun j=> by simp [headPoints,Points.cons,l, Function.comp_def]) j
         rw [← show headPoints (z+t•x) p=headPoints (z+t•x) (pickFrame S m) from rfl,heq']
         exact congr_arg (· + z) heq


theorem rayTaylor {z x:E4}{k:ℕ}(v:S.Field k){a:Grammar (Alpha S)}(m:ℕ)(hc:∀t∈Icc (0:ℝ) 1,Precise S a {z+t•x})(K:ℝ)(h:∀t∈Icc (0:ℝ) 1, ‖rayObserve a (arrow P k x (m+1) v) (z+t•x)‖≤K):
 ‖rayObserve a v (z+x)-∑ i:Fin (m+1), (i.val.factorial:ℝ)⁻¹ • rayObserve a (arrow P k x i v) z‖ ≤ K:=by
    let f(i:ℕ)(t:ℝ):= rayObserve a (arrow P k x i v) (z+t•x)
    let I:=Icc (0:ℝ) 1; have hI: UniqueDiffOn ℝ I:=uniqueDiffOn_Icc (hab:=zero_lt_one)
    have hp:(0:ℝ)∈I ∧ (1:ℝ)∈I:=⟨⟨by rfl,zero_le_one⟩,by constructor <;> norm_num⟩
    have hf(i:ℕ) (t:ℝ)(ht:t∈I): derivWithin (f i) I t=f (i+1) t:= (ray_derivative H hP i t (hc t ht)).hasDerivWithinAt.derivWithin (hI t ht)
    have hv(l:ℕ)(i:ℕ): ContDiffOn ℝ (l:ℕ) (f i) I:=by
         induction l generalizing i with
         | zero=> norm_cast; exact (by norm_cast; rw [show (↑↑0:ℕ∞ω)=0 from rfl,contDiffOn_zero]; exact fun t ht=> ((ray_derivative H hP i t (v:=v) (hc t ht)).continuousAt).continuousWithinAt)
         | succ l ih=>
             rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_derivWithin hI]
             exact ⟨fun t ht=>(ray_derivative H hP i t (hc t ht)).differentiableAt.differentiableWithinAt, by norm_num, (ih (i+1)).congr (hf i)⟩
    have hw(i:ℕ)(t:ℝ)(ht:t∈I): iteratedDerivWithin i (f 0) I t=f i t:=by
       induction i generalizing t with
       | zero=>rfl
       | succ i ih=> rw [iteratedDerivWithin_succ]; exact Eq.trans (derivWithin_congr (f:=f i) ih (ih t ht)) (hf i t ht)
    have ht:=taylor_mean_remainder_bound (f:=f 0) (n:=m) zero_le_one (show ContDiffOn ℝ _ _ _ from by rw [← show (↑↑(m+1:ℕ):ℕ∞ω)=↑↑m+1 by norm_num]; exact hv (m+1) 0) hp.2 (C:=K) fun t ht=>by rw [hw (m+1) t ht]; exact h t ht
    refine (show _ ≤ ‖f 0 1 - taylorWithinEval (f 0) m I 0 1‖ from ?_).trans (ht.trans (by rw [sub_zero,one_pow,mul_one]; exact div_le_self ((norm_nonneg _).trans (h (0:ℝ) hp.1)) (by exact_mod_cast (show (1:ℕ)≤ m.factorial from Nat.factorial_pos m))))
    exact le_of_eq (congr_arg (‖·‖) (congr_arg₂ (· - ·) (show _ =f 0 1 by simp only [f,one_smul,show arrow P k x 0= LinearMap.id from rfl,LinearMap.id_apply]) ((by
        apply Eq.symm
        rw [taylor_within_apply]; simp only [sub_zero,one_pow,mul_one,hw _ _ hp.1, f,zero_smul,add_zero]; exact (Fin.sum_univ_eq_sum_range _ _).symm ) : (∑ i:Fin (m+1),(i.val.factorial:ℝ)⁻¹ • rayObserve a (arrow P k x i v) z)=_)))

include hs
omit H hP in
lemma observe_shift (Hs:S.Symmetric){d e:ℕ}(h:d≤e){a:Grammar (Alpha S)}(v:S.Field d){x:E4}(ha:Precise S a {x}): rayObserve a (P.rise h v) x=rayObserve a v x:=by
        unfold rayObserve; rw [sum_terms a]; simp_rw [Finset.mul_sum,map_sum]; refine Finset.sum_congr rfl fun i hi=>?_;
        rw [mul_smul_comm,mul_smul_comm,map_smul,map_smul]; congr 1
        have hv:headPoints x (letters_frame i).choose ∈conf (i.card+1):=rayValid ha _ hi
        exact (packet_valid Hs x _ _ hv).trans ((hs.kernels h v hv _).trans (packet_valid Hs x _ _ hv).symm)
end YM.MultipleContact.Centered
