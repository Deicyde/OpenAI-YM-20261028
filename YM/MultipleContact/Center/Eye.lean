import YM.MultipleContact.Center.Picket
/-! Size the individual exact-weight branches on an anchor. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.MultipleContact.Centered
open Filter Set Function MeasureTheory Script Scene Two RG Extraction Spec Table Bunching Drama ScheduleRow March
open scoped Classical ContDiff Topology BigOperators
variable {G:Gauge}{L:Register G}{S:Table L} {b n h:ℕ} [Inhabited (Fin n)]
def Eye (V:Fin n→S.Tag)(N:Lattice.Side)(f:(Fin n→E4)→ S.Field h)(t:ℝ):=∃  B> (0:ℝ), ∃ r> (0:ℝ),∀u,0<u → u<r→ ∀x:Fin n→ E4,GapF N u x→ x default=0 → ‖f x‖≤B*u^t
variable (V:Fin n→S.Tag)(N:Lattice.Side)(ε:ℝ)(p:March S)(e:Exterior L)(q:p.Data)
lemma amount_null (hp:(p.advanced=false)):amount (picketOps p e)=0:= Finset.card_eq_zero.mpr (Finset.ext_iff.mpr (fun i=>(by have h:(picketOps p e i).advanced=false:=Fin.cases hp (fun _=>rfl) i; simp [h]))) -- syntax
variable (weak:Good 0 S)(H:S.Hierarchy)
include weak
omit H in
lemma ordinary_puff (hp:p.advanced=false)(hε:0<ε):(∃K r:ℝ,0<K ∧ 0<r ∧ ∀ρ:ℝ,(0<ρ ∧ ρ<r)→ ∀x:Fin n→E4,Nearish N p ρ x → joint e (points x) ∈ conf _ →
        ‖evaluation S (p.payload V (e.point 0) x q * prospect S e)‖≤K* p.credit V ε ρ q):=by
        obtain ⟨κ,hκ,Hκ⟩:=exists_clear e
        obtain ⟨K,hK,r,hr,hw⟩:=weak (picketOps p e) (fun _=>V) ε κ N hε hκ (amount_null p e hp|>.le)
        let K':=∏ j:Fin e.n,max 1 ‖S.project _ (e.letter j).2‖
        refine ⟨K*K',min r (κ/(2*N.val)),mul_pos hK (Finset.prod_pos (fun _ _=>lt_max_of_lt_left zero_lt_one)),by positivity,?_⟩ -- unfold K' invalid
        intro ρ hρ x hx _; rw [← fullEquation V ..]
        have h':= hw (probeData p q e) (fun _=>ρ) e.point.ofLp (fun _=>x) ((picket_space N p e hκ Hκ ρ r hρ.1 x hx hρ.2).1)
        exact h'.trans_eq ((congr_arg (K*·) (point_load V ε p q e ρ)).trans (by unfold K'; ring)) -- K binder shadow etc
variable {P:DiffPlan S}
variable (Q:Splitting P)(D:Detector S h) (hP:P.Inclusions S)
include H hP
lemma focus (w:ℕ)(hw:w≤h): Eye V N (fun x=>Q.part w h (D.apply V (points x))) (- (massOf V:ℝ)+(w:ℕ)-1+1/64):=by -- (w:ℕ) is type annotation coerced to Real by context?
 let k:=w-1
 let d':Detector S k:=Classical.choice (detector_exists k S)
 let p:March S:=if w=0 then .raw else .anchor k d'
 let f(x:Fin n→ E4):S.Field h:= if w=0 then 0 else P.rise (Nat.sub_le w 1|>.trans hw) (d'.apply V (points x))
 let t:= -(massOf V:ℝ)+(w:ℝ)-1+1/64
 have hp : ¬ p.advanced:=by unfold p;split_ifs <;> simp [March.advanced]
 have he:p.weight V (63/64)=t:=by
     unfold t p March.weight
     by_cases h:w=0
     · rw [if_pos h,h]; push_cast; ring
     rw [if_neg h]; dsimp [k]; push_cast [Nat.cast_sub (by omega : (1:ℕ)≤w)]; ring
 obtain ⟨A,r,hA,hr,hB⟩:=estimatePicket V N p f H D (t:=t) (by
     intro e he'
     let q:= (default:p.Data)
     obtain ⟨A,r,hA,hr,hread⟩:=ordinary_puff V N (63/64) p e q weak (Bool.eq_false_of_not_eq_true hp) (by norm_num) -- lemma
     refine ⟨A,r,hA,hr,fun ρ₀ hr₀ x hx hC=>?_⟩
     have ht:q=default:=rfl
     have hcharge: p.credit V (63/64) ρ₀ q=ρ₀^t:=by rw [March.credit,he,ht,show p.load default=1 from ?_,mul_one]; unfold p; split_ifs with h0 <;> simp [h0,March.load]
     have hr':= (hread ρ₀ hr₀ x hx hC).trans_eq (congr_arg (A*·) hcharge)
     refine (congr_arg (‖·‖) ?_).trans_le hr'
     by_cases h0:w=0
     · change evaluation S ((Scene.packet .. - _) * _) = evaluation S (p.payload .. * _)
       have hf:f x=0:=if_pos h0
       rw [hf,sub_mul,map_sub]; have hEq:p.payload V (e.point 0) x q= Scene.packet S V x (e.point 0):=by
           rw [ht]; unfold p; rw! (castMode:=.all) [if_pos h0];rfl
       rw [hEq,prospect_cost S H.laws.toSymmetric,map_zero,sub_zero]
     have hshift : rayObserve (prospect S e) (f x) (e.point 0)=rayObserve (prospect S e) (d'.apply V (points x)) (e.point 0):=by
          rw [show f x = P.rise (show k≤h from Nat.sub_le w 1|>.trans hw) (d'.apply V (points x)) from if_neg h0]; refine observe_shift hP H.laws.toSymmetric _ _ ?_
          apply precise_secure S (K:=Set.range (fun t:Fin e.n=>e.point t.succ)) ?_ (secure_spell S ?_ (fun i j h=>Fin.succ_inj.mp (e.clear h))) -- argument mismatch
          · exact Set.disjoint_left.mpr (by rintro a ⟨i,rfl⟩ h; exact i.succ_ne_zero (e.clear (Set.mem_singleton_iff.mp h)))
          · rintro r ⟨i,rfl⟩; exact ⟨i,rfl⟩
     unfold rayObserve at hshift
     rw [sub_mul,map_sub,hshift]
     have hEq:p.payload V (e.point 0) x q= Scene.residue S d' V x (e.point 0):=by rw [ht]; unfold p; rw! (castMode:=.all) [if_neg h0]; rfl
     rw [hEq,residue,sub_mul,map_sub])
 let B:= ‖LinearMap.toContinuousLinearMap (Q.part w h)‖
 refine ⟨(B+1)* A,by exact mul_pos (by unfold B; linarith only[norm_nonneg (LinearMap.toContinuousLinearMap (Q.part w h))]) hA,r,hr,fun u hu hu' x hx h0=> ?_⟩
 have hpPass:p.allow N u x:= by unfold p March.allow; split_ifs; all_goals exact ⟨hx.1,hx.2,fun _ _ _=>h0⟩
 have hw':= hB u ⟨hu,hu'⟩ x ⟨hpPass,hx⟩
 have hf':Q.part w h (f x)=0:=by
          unfold f; by_cases e:w=0
          · rw [if_pos e,map_zero]
          rw [if_neg e,Q.part_rise H.laws.toSymmetric hP, Q.beyondZero (by change w-1<w; omega),LinearMap.zero_apply]
 calc ‖_‖= ‖Q.part w h (D.apply V (points x)-f x)‖:=by rw [map_sub,hf',sub_zero]
       _ ≤ (B+1)*‖D.apply V (points x)-f x‖:= ((LinearMap.toContinuousLinearMap (Q.part w h)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (by refine le_add_of_nonneg_right (a:=B) (by norm_num)) (norm_nonneg _))
       _≤ _:= (mul_le_mul_of_nonneg_left hw' (show 0≤B+1 by unfold B; linarith only [norm_nonneg (LinearMap.toContinuousLinearMap (Q.part w h))])).trans_eq (by simp only [t];ring)
end YM.MultipleContact.Centered
