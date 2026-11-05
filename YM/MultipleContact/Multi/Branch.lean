import YM.MultipleContact.Multi.Casting

/-! Anchor-based product/detector subtraction on the separated open locus, using fixed detectors on the same hierarchy. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.MultipleContact.Scene
open Set Function Filter MeasureTheory Table Ward Script
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{L:Register G}(S:Table L){n d:ℕ}
local notation "Gram" => Grammar (Alpha S)
def packet (v:Fin n→S.Tag) (y:Fin n → E4) (z:E4) : Gram:= call S v (fun i=>z+y i)
def insertion (z:E4) (v:S.Field d):Gram:= stamp ((⟨d,v⟩:S.Tag),z)
def residue (D:Detector S d)(v:Fin n→S.Tag)(y:Fin n → E4)(z:E4) : Gram := packet S v y z-insertion S z (D.apply v (points y))
def prospect (e:Exterior L):Gram:= spell (fun i:Fin e.n=>(S.classTokens (e.letter i),e.point i.succ))
def Precise (p:Gram)(U:Set E4):= ∀ m∈p.coeff.support, clear S (pickFrame S m) ∧ Disjoint (names S m) U
variable {P:DiffPlan S}
theorem prospect_cost (hs:S.Symmetric)(e:Exterior L)(v:S.Field d): evaluation S ((insertion S (e.point 0) v) * prospect S e) = response S d e v:= by
   let t:= Fin.cons (α:=fun _=> Alpha S) ((⟨_,v⟩:S.Tag),e.point 0) fun i=>(S.classTokens (e.letter i),e.point i.succ)
   rw [show insertion S (e.point 0) v*prospect S e=spell t from ?_,eval_fin S hs]; unfold readFin
   have hz : (points fun i=>(t i).2)=e.point:=by ext1 i; exact Fin.cases rfl (fun j=> rfl) i
   rw [hz,if_pos (show clear S t from fun i j (h : (points _).ofLp i=(points _).ofLp j)=>e.clear (hz ▸ h)),response_self]
   have hh : (fun i=>(t i).1)= Fin.cons (⟨d,v⟩:S.Tag) (S.classTokens∘ e.letter):=by funext i; exact Fin.cases rfl (fun _=>rfl) i
   rw [hh]; exact S.through hs v e.letter e.clear

   unfold prospect insertion spell t; rw [Fin.prod_univ_succ];rfl
lemma strict_packet (hs:S.Symmetric)(e:Exterior L)(v:Fin n→S.Tag)(y:Fin n → E4)(hx: joint e (points y)∈conf _): evaluation S ((packet S v y (e.point 0))*prospect S e)= raw S v (points y) e:=by
    let t0:= fun i:Fin n=> (v i,e.point 0+y i); let t1:=fun i:Fin e.n=>(S.classTokens (e.letter i),e.point i.succ); let t:=Fin.append t0 t1
    rw [show packet S v y (e.point 0)*prospect S e=spell t from (spell_sum ..).symm,eval_fin S hs,read_points]
    have h' :(points (fun i=>(t i).2))= joint e (points y):=by ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp [t,t0,t1,joint,add_comm,Points.tail]
    rw [h',Truncated,if_pos hx];change S.useAt S _ _ = S.useAt S _ _
    congr 1; funext i; unfold tagsPlaced; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp [t,t0,t1]
lemma packet_step (v:Fin n→S.Tag)(y:Fin n → E4)(z:E4)(k:Fin n)(i:Axis)(a t:ℝ): packet S v (moved 0 y k i a t) z=call S v (moved z y k i a t):= by unfold packet moved; simp only [zero_add]
lemma packet_secure {K:Set E4} (v:Fin n→S.Tag){x:Fin n → E4}(z:E4) (hp:Injective x)(hq:Set.range (fun i=>z+x i) ⊆ K):Secure S K (packet S v x z):=call_secure S (fun i j e=>hp (add_left_cancel e)) hq
lemma insertion_secure {K:Set E4} (v:S.Field d){z:E4}(h:z∈K):Secure S K (insertion S z v):= (by rw [show insertion S z v=Script.spell (fun _:Fin 1=>((⟨d,v⟩:S.Tag),z)) from by simp [insertion,spell]]; exact secure_spell S (by rintro j ⟨_,rfl⟩; exact h) (by exact fun i j h=>Subsingleton.elim ..))
lemma precise_secure {K U:Set E4} (h:Disjoint K U){p:Gram}(hp:Secure S K p):Precise S p U:= by
     intro i hi; exact ⟨(secure_selected S (hp i hi)).1,h.mono_left (hp i hi).2⟩
lemma prospect_precise (x:Fin n → E4)(k:Fin n)(q:Axis)(a t:ℝ)(e:Exterior L) (h:∀j:Fin n,∀i:Fin e.n,moved (e.point 0) x k q a t j ≠ e.point i.succ): Precise S (prospect S e) (Set.range (moved (e.point 0) x k q a t)):= by
     let f(i:Fin e.n):= e.point i.succ
     have hi:Injective f:=fun i j h=> Fin.succ_injective _ (e.clear h) -- check
     apply precise_secure S (K:=Set.range f) ?_ (secure_spell S (v:=fun i:Fin e.n=> (S.classTokens (e.letter i),e.point i.succ)) (Subset.refl _) hi)
     refine Set.disjoint_left.mpr ?_
     rintro i ⟨p,e'⟩ ⟨q,hq⟩; exact h q p (hq.trans e'.symm) -- replace
variable {S}(H:S.Hierarchy)(hP:P.Derivatives S)
include H hP
lemma packet_deriv (v:Fin n→S.Tag)(u:E4)(y:Fin n → E4)(p:Grammar (Alpha S))(k:Fin n)(q:Axis)(a:ℝ)(t:ℝ)
    (hcur:Injective (moved u y k q a t)) (hn: Precise S p (Set.range (moved u y k q a t))):
    HasDerivAt (fun w=>evaluation S (packet S v (moved 0 y k q a w) u * p))
        (a • evaluation S (packet S (Function.update v k (Ward.rise P q (v k))) (moved 0 y k q a t) u*p)) t:= by
        let v':=Function.update v k (Ward.rise P q (v k)); let cur:=moved 0 y k q a; let f:=fun b=>moved u y k q a b
        let F(w b):= fun m=> evaluation S (packet S w (cur b) u * spell (pickFrame S m))
        have he(w b):evaluation S (packet S w (cur b) u*p)=∑ m∈p.coeff.support,p.coeff m • F w b m:=by
            nth_rw 1 [sum_terms p]; simp_rw [Finset.mul_sum,map_sum,mul_smul_comm,map_smul]; rfl
        change HasDerivAt (fun w=> evaluation S (packet S v (cur w) u * p)) (a • evaluation S (packet S v' (cur t) u*p)) t
        simp_rw [he _,Finset.smul_sum]
        apply HasDerivAt.fun_sum; intro m hm
        convert (moving_call S H hP v u y (pickFrame S m) k q a t ((hn m hm).1) hcur ?_).const_smul (p.coeff m) using 1
        · funext b; unfold F; simp_rw [cur,packet_step];rfl
        · unfold F; unfold cur; rw [packet_step,smul_comm]
        intro i j he
        apply Set.disjoint_left.mp ((hn m hm).2) ?_ (Set.mem_range_self i)
        rw [names_iff]; exact ⟨_,he.symm ▸ ((letters_frame m).choose_spec.symm ▸ (letters_image (pickFrame S m)).mpr ⟨j,(Prod.eta ..).symm⟩)⟩
omit H hP in
lemma config_moved {y:Fin n→ E4}(k:Fin n)(q:Axis)(a t:ℝ)(h:Injective (moved (0:E4) y k q a t))(u:E4):Injective (moved u y k q a t):=by intro i j e; exact h (by simp only [moved,zero_add]; exact add_left_cancel e)
lemma projection_deriv (D:Detector S d) (v:Fin n→S.Tag)(y:Fin n → E4)(k:Fin n)(q:Axis)(a t:ℝ)
    (hcur:Injective (moved (0:E4) y k q a t)) (hp:∀e∈D.probes,∀i:Fin n,∀j:Fin e.n,moved (e.point 0) y k q a t i ≠ e.point j.succ):HasDerivAt (fun s=>D.apply v (points (moved 0 y k q a s)))
         (a • D.apply (Function.update v k (Ward.rise P q (v k))) (points (moved 0 y k q a t))) t:=by
      let cur:=moved (0:E4) y k q a; let v':=Function.update v k (Ward.rise P q (v k))
      have he:(∀e:D.probes,∀ᶠ s in 𝓝 t, joint (e:Exterior L) (points (cur s))∈conf _):=by
          rintro ⟨e,he⟩
          have hq':Continuous (fun s=>joint e (points (cur s))):=by unfold joint points cur moved; exact (PiLp.continuous_toLp _ _).comp (continuous_pi (fun i=>Fin.addCases (fun i=> by by_cases h':i=k <;> simp [h'] <;> fun_prop) (fun i=>by simp only [Fin.append_right]; fun_prop) i))
          have hh(i:Fin n): cur t i+ e.point 0=moved (e.point 0) y k q a t i:=by simp only [cur,moved,zero_add,add_comm]
          have hj:joint e (points (cur t))∈conf _:= append_clear _ _ (fun i j h=>config_moved k q a t hcur (e.point 0) (by rw [← hh,← hh];exact h)) (fun i j h=>Fin.succ_inj.mp (e.clear h)) (fun i j h=>hp e he i j ((hh i).symm.trans h)) -- may miselaborate
          exact hq'.continuousAt.eventually ((conf_open _).mem_nhds hj)
      let r (x:Fin n → S.Tag) (i:ℝ) (e:D.probes):= raw S x (points (cur i)) (e:Exterior L)
      have hf : HasDerivAt (fun i=>r v i) (a • r v' t) t:=by
           apply hasDerivAt_pi.mpr; rintro e
           change HasDerivAt (fun i=>r v i e) (a • r v' t e) t
           obtain ⟨j,hj⟩:=e
           apply (Filter.EventuallyEq.hasDerivAt_iff (show (fun i=>r v i ⟨j,hj⟩) =ᶠ[𝓝 t] (fun i=>evaluation S (packet S v (cur i) (j.point 0)*prospect S j)) from ?_)).mpr
           · unfold r; dsimp only [Subtype.coe_mk]; rw [← strict_packet S H.laws.toSymmetric j v' (cur t) (mem_of_mem_nhds (s:={s | joint j (points (cur s))∈conf _}) (he ⟨j,hj⟩))]
             exact packet_deriv H hP v _ y (prospect S j) _ _ _ _ (config_moved k q a t hcur _) (prospect_precise S _ _ _ _ _ _ (hp j hj))
           · filter_upwards [he ⟨j,hj⟩] with i hi; exact (strict_packet S H.laws.toSymmetric _ _ _ hi).symm
      let R':= (LinearMap.toContinuousLinearMap D.decode).restrictScalars ℝ
      change HasDerivAt (R' ∘ r v) ( _ • R' (r v' t)) _
      simpa only [map_smul] using ((R'.hasFDerivAt (x:=r v t)).comp_hasDerivAt t hf)
lemma residue_deriv (D:Detector S d) (v:Fin n→S.Tag)(u:E4)(y:Fin n → E4)(p:Grammar (Alpha S))(k:Fin n)(q:Axis)(a:ℝ)(t:ℝ)
    (hcur:Injective (moved 0 y k q a t)) (hn: Precise S p (Set.range (moved u y k q a t)))(hp:∀ e∈D.probes,∀ i:Fin n,∀ j:Fin e.n,moved (e.point 0) y k q a t i ≠ e.point j.succ):
    HasDerivAt (fun w=>evaluation S (residue S D v (moved 0 y k q a w) u*p))
        (a • evaluation S (residue S D (Function.update v k (Ward.rise P q (v k))) (moved 0 y k q a t) u*p)) t:= by
       obtain ⟨f,hf⟩:=inline S H.laws.toSymmetric u p (d:=d); let F:= (LinearMap.toContinuousLinearMap f).restrictScalars ℝ
       unfold residue
       conv => simp only [sub_mul,map_sub,smul_sub,insertion,hf]
       exact (packet_deriv H hP v _ y _ _ _ _ _ (config_moved k q a t hcur u) hn).sub ((F.hasFDerivAt (x:=_)).comp_hasDerivAt t (projection_deriv H hP D v y k q a t hcur hp) |>.congr_deriv (by rw [map_smul];rfl))
end YM.MultipleContact.Scene
