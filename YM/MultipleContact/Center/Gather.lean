import YM.MultipleContact.Center.Stream
/-! Upgrade all flagged slots in arbitrary order but with common constants. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.MultipleContact.Centered
open Set Filter Function MeasureTheory Script Scene Table March Two RG Extraction Spec Bunching Joins Ward
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}
def stem {m:ℕ}{v:Fin m→S.Tag}{d:ℕ}(D:Detector S d)(w:S.Field d)(z:E4)(x:Fin m→E4):=packet S v x z-insertion S z w -- D unused! force binder
lemma fixtureP {n:ℕ}(V:Fin n→S.Tag){p:March S}(x:Fin n→E4)(e:Exterior L)(q:p.Data): March.fixture (n:=fun _=>n) (fun _=>V) (picketOps p e) (probeData p q e) e.point (fun _=>x) 0=prospect S e:=by
       let f(i:Fin (e.n+1)):=if i=0 then (1:Grammar (Alpha S)) else ((picketOps p e i).payload V (e.point i) x ((probeData p q e) i))
       unfold March.fixture
       calc _=(Finset.univ.erase (0:Fin (e.n+1))).prod f:=Finset.prod_congr rfl fun j hj=>(if_neg (Finset.mem_erase.mp hj).1|>.symm)
            _ = ∏ i:Fin (e.n+1), f i:=by rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0:Fin (e.n+1))), show f 0=1 from if_pos rfl,one_mul]
            _ = ∏ i:Fin e.n, ((picketOps p e i.succ).payload ..) :=by rw [Fin.prod_univ_succ, show f 0=1 from if_pos rfl, one_mul]; exact Finset.prod_congr rfl fun i _=>if_neg (Fin.succ_ne_zero i)
            _ = _:=rfl

variable {b k d:ℕ}{n:Fin b→ℕ}[hn:∀i:Fin b,Inhabited (Fin (n i))](V:∀i:Fin b,Fin (n i)→S.Tag)(p:Fin b→March S)
  (κ ε:ℝ) (N:Lattice.Side) (i:Fin b)(D:Detector S d)
  (hpi:p i=.root d D) (hε:0<ε)(hk:0<κ)(weak:Good k S)(first:Good 0 S) -- replace
  (hS:S.Hierarchy)(hP:P.Derivatives S)(hC:P.Inclusions S)(Q:Splitting P)
  (hm:amount p ≤ k+1)
lemma packet_eq (v:March S)(h'':v=.root d D)(w:v.Data){m:ℕ}(x:Fin m→E4)(z:E4)(f:Fin m→S.Tag):v.payload f z x w= packet S f x z-insertion S z (D.apply f (points x)):=by subst v;rfl
include hS hP hpi hε hk weak first hm hC
lemma candidateGood:∃ K> (0:ℝ),∃ r> (0:ℝ),∀ ρ:Fin b→ℝ,∀ z:Fin b→E4,∀ x:∀i,Fin (n i)→E4, Permit p κ r N ρ z x → ∀q:∀i,(p i).Data,
      ‖evaluation S ((Scene.packet S (V i) (x i) (z i)-insertion S (z i) (Candidate Q (V i) D (x i) (x i default)))* March.fixture V p q z x i)‖≤ K * plainLoad p V ε ρ q:=by
   let g(w:Fin (d+1))(x:Fin (n i)→ E4):=Q.part w d (D.apply (V i) (points x))
   have hf(w:Fin (d+1)) : Eye (V i) (expand N 2) (g w) _ := focus (V i) _ first hS Q D hC w (by omega) -- parameter first should Good0 and same N? tests need expand N
   choose A hA r hr hh using fun w:Fin (d+1)=>stream V p κ ε N i D hpi hε hk weak hS hP hm w (hf w)
   obtain ⟨U,hU,s,hs,known⟩:=anchored_first V p κ ε N i D hpi hε hk weak hm
   obtain ⟨R,hR,hReq⟩:=common_radii r hr
   let K:=U+ ∑ i:Fin (d+1),A i
   refine ⟨K,by unfold K; exact add_pos_of_pos_of_nonneg hU (Finset.sum_nonneg fun w _=>(hA w).le),min R s,lt_min hR hs,?_⟩
   intro ρ z x h q; let y:=x i default; let a:=March.fixture V p q z x i
   have h'(w:Fin (d+1)): Permit p κ (r w) N ρ z x:=⟨h.1,fun t=>⟨(h.2.1 t).1,((h.2.1 t).2.trans_le (min_le_left ..)).trans_le (hReq w)⟩,h.2.2⟩
   have hw(w:Fin (d+1)):= hh w ρ z x (h' w) q; let B:=plainLoad p V ε ρ q
   have hm: ∀t∈Icc (0:ℝ) 1,Precise S a {z i+t • y}:= (hw (0:Fin (d+1))).1
   change ‖evaluation S ((_ - _)*a)‖ ≤ K*B
   have hp:= known ρ z x q ⟨h.1,fun t=>⟨(h.2.1 t).1,(h.2.1 t).2.trans_le (min_le_right ..)⟩,h.2.2⟩
   rw [candidate_residual hS.laws.toSymmetric hC Q (show Precise S a {z i} by simpa using hm 0 ⟨by rfl,zero_le_one⟩) (show Precise S a {z i+y} by simpa using hm 1 (by constructor <;> norm_num))]
   refine (norm_add_le ..).trans (add_le_add hp ((norm_sum_le ..).trans (Finset.sum_le_sum fun w _=> (hw w).2)) |>.trans_eq ?_)
   exact (add_mul ..|>.trans (congr_arg _ (Finset.sum_mul Finset.univ A B))).symm -- Finset.sum_mul not specialized

omit hpi hm hk -- V not include; hpi hm omitted
include hS hP hC hε weak first
lemma norm_candidate {m:ℕ}[Inhabited (Fin m)](v:Fin m→S.Tag):∃A r:ℝ,0<A∧0<r∧∀t:ℝ,0<t → t<r→ ∀x:Fin m→E4,March.allow (.root d D) N t x → ‖D.apply v (points x) - Candidate Q v D x (x default)‖ ≤ A*t^(-(massOf v:ℝ)+d+1/64):=by
       let p:=March.root d D
       obtain ⟨A,r,hA,hr,h⟩:=estimatePicket v N p (fun x=>Candidate Q v D x (x default)) hS D (t:=-(massOf v:ℝ)+d+1/64) (by
           intro e he
           obtain ⟨κ,hκ,hclear⟩:=exists_clear e
           let t:=picketOps p e
           have he : t 0=.root d D:=rfl
           have h' : amount t=1:=by
             suffices eq:Finset.univ.filter (fun i:Fin (e.n+1)=>(t i).advanced)={0} by change (Finset.univ.filter fun i=> (t i).advanced).card=1; rw [eq]; rfl
             ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]; refine Fin.cases ?_ (fun j=>?_) i <;> simp [t,p,picketOps,March.advanced]
           let q0:= (default:p.Data)
           obtain ⟨B,hB,r,hr,hR⟩:= candidateGood (n:=fun _=>m) (fun _=>v) t κ ε N 0 D he hε hκ weak first hS hP hC Q (by omega)
           let F:=∏ i:Fin e.n,max 1 ‖S.project _ (e.letter i).2‖
           have hF: 0 < F:=Finset.prod_pos (fun _ _=>lt_max_of_lt_left zero_lt_one)
           refine ⟨B*F,min r (κ/(2*N.val)), mul_pos hB hF,by positivity,?_⟩
           intro u h₁ x hx hU
           have h:= hR (fun _=>u) e.point.ofLp (fun _=>x) (picket_space N p e hκ hclear u r h₁.1 x hx h₁.2|>.1) (probeData p q0 e)
           rw [fixtureP v,point_load v] at h; rw [March.credit,show p.load q0=1 from rfl,mul_one] at h
           refine h.trans_eq ?_; unfold F;rw [mul_assoc];congr 1;exact mul_comm ..)
       refine ⟨_,_,hA,hr,fun t ht hρ x hx=>h t ⟨ht,hρ⟩ x ⟨hx,hx.1,hx.2.1⟩⟩

include hpi hm hk Q
lemma supplement :Price p V ε κ N:=by
          let v:=V i
          obtain ⟨M,r,hM,hr,hErr⟩:=norm_candidate ε N D hε weak first hS hP hC Q v
          obtain ⟨K,hK,R,hR,hProto⟩:= candidateGood V p κ ε N i D hpi hε hk weak first hS hP hC Q hm
          obtain ⟨U,hU,s,hs,hField⟩:= press_bound V p κ ε N i D hpi hε hk weak hm d hS.laws.toSymmetric
          refine ⟨K+U*M,by positivity,min (min r s) R,lt_min (lt_min hr hs) hR,?_⟩
          intro q ρ z x h
          have ht:=hField ρ z x q ⟨h.1,fun j=>⟨(h.2.1 j).1,((h.2.1 j).2.trans_le (min_le_left ..)).trans_le (min_le_right ..)⟩,h.2.2⟩ 0 (by rw [norm_zero];positivity)
          have hv:=hErr (ρ i) (h.2.1 i).1 (((h.2.1 i).2.trans_le (min_le_left ..)).trans_le (min_le_left ..)) (x i) (hpi ▸ (h.2.2 i))
          have hw:= hProto ρ z x ⟨h.1,fun j=>⟨(h.2.1 j).1,(h.2.1 j).2.trans_le (min_le_right ..)⟩,h.2.2⟩ q
          let a:=fixture V p q z x i; let m:=minorCharge V p q ε ρ i
          let J:=D.apply v (points (x i)); let v0:=Candidate Q v D (x i) (x i default)
          let e:= -(massOf v:ℝ)+(d:ℝ)+1/64; let L:=plainLoad p V ε ρ q
          change _ ≤ M*ρ i ^ e at hv
          have hY:=ht.1 (v0-J); rw [add_zero] at hY
          have heq : L = ρ i ^ e * m := by
                  unfold L; rw [plug_credit ,March.credit,show (p i).load (q i) =1 from ?_,mul_one]
                  · congr 2; rw [hpi];rfl
                  rw! (castMode:=.all) [hpi];rfl
          have hm':0< m:=minor_pos V p q ε ρ i (fun k=> (h.2.1 k).1)
          change _≤K*L at hw
          suffices he : evaluation S (work p V z x q) = evaluation S ((packet S (V i) (x i) (z i)-insertion S _ v0)*a) + rayObserve a (v0-J) (z i) by
            rw [he]; refine (norm_add_le ..).trans (add_le_add hw (hY.trans ((mul_le_mul_of_nonneg_left (show ‖v0-J‖ ≤ M*(ρ i)^e from by rw [norm_sub_rev];exact hv) (by exact (mul_pos hU hm').le)).trans_eq ?_)) |>.trans_eq (add_mul K (U*M) L).symm)
            rw [heq]; ring
          obtain ⟨f,hf⟩:=Scene.inline S (d:=d) hS.laws.toSymmetric (z i) a
          rw [plug_product,packet_eq D _ hpi,rayObserve,sub_mul,map_sub,sub_mul,map_sub]; unfold insertion
          change (evaluation S (_*a)- evaluation S (stamp _ * a)= (evaluation S (_*a)- evaluation S (stamp _ * a)) + evaluation S (stamp _*a)) -- let a
          rw [hf,hf,hf,map_sub]; abel

universe u
open Extraction
-- Work on any fixed unselected Wilson hierarchy for which the mixed anchor estimate has been proved.
omit hS hP Q hpi hm hk hC weak hε first in
theorem ascend {C:_root_.YM.Family G}{S:Table C.book}{P:DiffPlan S}(hS:S.Hierarchy)(hP:P.Derivatives S)(hC:P.Inclusions S)(Q:Splitting P)(all:∀k:ℕ,Joins.Store S k) : ∀ k:ℕ,Good k S:=by
     have h:Good 0 S:= voucher0 hS.laws.toSymmetric all
     intro k; induction k with
     | zero => exact h
     | succ k ih=>
       intro b n _ p v ε κ N hε hk hc
       by_cases he:amount p ≤ k
       · exact ih p v ε κ N hε hk he
       obtain ⟨i,hi⟩:=Finset.card_ne_zero.mp (show amount p ≠ 0 by omega)
       obtain ⟨h0,hpi⟩:=Finset.mem_filter.mp hi
       cases he:p i with
       | raw=> simp [he,March.advanced] at hpi
       | field d=> simp [he,March.advanced] at hpi
       | root d D=> exact supplement v p κ ε N i D he hε hk ih h hS hP hC Q hc
       | anchor d D=> simp [he,March.advanced] at hpi

end YM.MultipleContact.Centered
