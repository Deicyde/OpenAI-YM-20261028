import YM.MultipleContact.Center.Press
/-! Expressing the available finite Taylor jets in the physical derivative filtration. -/
set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section
namespace YM.MultipleContact.Centered
open Set Filter Function MeasureTheory TopologicalSpace Script Scene Table March Two RG Extraction Spec Bunching Joins Ward
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}

lemma observe_sum {h:ℕ}{a:Grammar (Alpha S)}(T:S.Symmetric)(hp:P.Inclusions S)(Q:Splitting P){y:E4}(hc:Precise S a {y})(v:S.Field h):rayObserve a v y=∑ w:Fin (h+1),rayObserve a (Q.part w h v) y:=by
       obtain ⟨f,hf⟩:=inline S (d:=h) T y a
       change evaluation S (stamp ((_,_):Alpha S)*a) = _; rw [hf]; nth_rw 1 [← Q.recombine T hp h v]; rw [map_sum]
       exact Finset.sum_congr rfl (fun i _=> (hf ..).symm.trans (observe_shift hp T _ _ hc)) -- hf .. oversat
private abbrev activeWitness (h:ℕ)(w:Fin (h+1))(i:Fin (h-w+1)):w.val+i.val≤h:=by omega
private def monoField (P:DiffPlan S)(h:ℕ)(w:Fin (h+1))(x:E4)(v:S.Field w.val) : S.Field h:=∑ i:Fin (h-w.val+1), P.rise (activeWitness h w i) ((↑(i.val.factorial:ℕ):ℂ)⁻¹ • arrow P w.val x i.val v)
lemma mono_observe (h:ℕ)(H:S.Symmetric)(hp:P.Inclusions S)(w:Fin (h+1)) (T:Grammar (Alpha S))(z:E4)(hc:Precise S T {z})(y:E4)(v:S.Field w.val):
         rayObserve T (monoField P h w y v) z= ∑ i:Fin (h-w.val+1), (i.val.factorial:ℝ)⁻¹ • rayObserve T (arrow P w.val y i.val v) z:=by
         obtain ⟨f,hf⟩:=inline S (d:=h) H z T; change evaluation S _ = _
         rw [insertion,hf,monoField,map_sum]; refine Finset.sum_congr rfl fun i _=>?_;
         rw [← hf]; change rayObserve T _ _=_; rw [observe_shift hp H (activeWitness h w i) _ hc]
         unfold rayObserve insertion; rw [inline_smul,Complex.real_smul]; push_cast; rfl
         exact H

def Candidate (Q:Splitting P){n:ℕ}(V:Fin n → S.Tag){h:ℕ}(D:Detector S h)(x:Fin n→ E4)(y:E4):S.Field h:=∑ w:Fin (h+1),monoField P h w y (Q.part w h (D.apply V (points (x-fun _=>y))))
lemma candidateObserve (h:ℕ)(H:S.Symmetric)(hp:P.Inclusions S)(Q:Splitting P){T:Grammar (Alpha S)}{z:E4}(hc:Precise S T {z}){n:ℕ}{V:Fin n→ S.Tag}{y:E4}{D:Detector S h} (x:Fin n→ E4):
     rayObserve T (Candidate Q V D x y) z = ∑ w:Fin (h+1), ∑ i:Fin (h-w.val+1), (i.val.factorial:ℝ)⁻¹ • rayObserve T (arrow P w.val y i.val (Q.part w h (D.apply V (points (x-fun _=>y))))) z:=by
       obtain ⟨f,hf⟩:=inline S (d:=h) H z T; change evaluation S _=_ ;rw [insertion,hf,Candidate,map_sum]; exact Finset.sum_congr rfl fun i _=>(hf _).symm.trans (mono_observe h H hp _ _ _ hc _ _)
def errTerm (P:DiffPlan S)(a:Grammar (Alpha S))(z y:E4){w:ℕ}(v:S.Field w)(h:ℕ):=rayObserve a v (z+y)- ∑i:Fin (h-w+1), (i.val.factorial:ℝ)⁻¹ • rayObserve a (arrow P w y i.val v) z
lemma candidate_residual {n h:ℕ}{T:Grammar (Alpha S)}{V:Fin n→ S.Tag}{D:Detector S h}(H:S.Symmetric)(hp:P.Inclusions S)(Q:Splitting P){x:Fin n→E4}{z y:E4}(hz:Precise S T {z})(hy:Precise S T {z+y}):
     evaluation S ((packet S V x z-insertion S z (Candidate Q V D x y))*T)= evaluation S ((packet S V x z-insertion S (z+y) (D.apply V (points (x-fun _=>y))))*T)+ ∑ w:Fin (h+1), errTerm P T z y (Q.part w h (D.apply V (points (x-fun _=>y)))) h := by
       rw [sub_mul,sub_mul,map_sub,map_sub]; simp only [errTerm]
       change (evaluation S _ - rayObserve T _ _) = evaluation S _ - rayObserve T _ _+_
       rw [candidateObserve h H hp Q hz x, observe_sum H hp Q hy,Finset.sum_sub_distrib]; ring
--- estimates
variable {b k d:ℕ}{n:Fin b→ℕ}[hn:∀i:Fin b,Inhabited (Fin (n i))](V:∀i:Fin b,Fin (n i)→S.Tag)(p:Fin b→March S)
  (κ ε:ℝ) (N:Lattice.Side) (i:Fin b)(D:Detector S d)
  (hpi:p i=.root d D) (hε:0<ε)(hk:0<κ)(weak:Good k S)(first:Good 0 S)
  (hS:S.Hierarchy)(hP:P.Derivatives S)(hC:P.Inclusions S)(Q:Splitting P)
  (hm:amount p ≤ k+1)
include hS hP hpi hε hk weak hm
lemma stream (w:Fin (d+1)){f:(Fin (n i)→E4)→ S.Field w.val}(he:Eye (V i) (expand N 2) f (-(massOf (V i):ℝ)+(w:ℝ)-1+1/64)):
  ∃ K> (0:ℝ), ∃ r> (0:ℝ),∀ ρ:Fin b→ ℝ,∀ z:Fin b→ E4, ∀ x:∀i₁:Fin b,Fin (n i₁)→ E4, Permit p κ r N ρ z x → ∀q:∀i,(p i).Data,
    let a:=fixture V p q z x i
    let y:= x i default
    (∀t∈Icc (0:ℝ) 1, Precise S a {z i+t•y}) ∧ ‖errTerm P a (z i) y (f (x i-fun _=>y)) d‖≤K* plainLoad p V ε ρ q:=by
       let j:=d-w.val; let j':= w.val+(j+1)
       obtain ⟨B,hB,r,hr,h⟩:= press_bound V p κ ε N i D hpi hε hk weak hm j' hS.laws.toSymmetric
       obtain ⟨A,hA,s,hs,heye⟩:=he
       obtain ⟨C,hK,hq⟩:=Two.arrow_bound P w.val (j+1)
       let U:ℝ:= C*A*(2*N.val:ℝ)^(j+1); have hu:0≤U:=by unfold U; positivity
       let K:= B*U+1
       refine ⟨K,by unfold K; positivity, min (min r s) (smallEnough κ N),lt_min (lt_min hr hs) (enough_pos κ N hk),?_⟩
       intro ρ z x hConfig q a y
       let t:=ρ i; have ht:0<t:= (hConfig.2.1 i).1
       have hR(k:Fin b):ρ k < r:= (hConfig.2.1 k).2.trans_le ((min_le_left ..).trans' (min_le_left ..)) -- min
       have hnear:GapF N t (x i):= by have h:= hConfig.2.2 i; rw [hpi] at h; exact ⟨h.1,h.2.1⟩
       have hN :0 < (N.val:ℝ):=by exact_mod_cast N.pos
       have hf:0 < (N.val:ℝ)*t:=mul_pos hN ht
       have hSmall: t < κ/(8*N.val):= (hConfig.2.1 i).2.trans_le ((min_le_right ..).trans' (min_le_right (a:=min r s) ..))
       have hsmall':‖y‖<κ/4:=by
           have hp:t*(8*N.val)<κ:=(lt_div_iff₀ (by positivity : 0<(8*N.val:ℝ))).mp hSmall
           linarith only [hp,hnear.2 default,show ‖x i default‖=‖y‖ from rfl]
       let x' (l):=x i l-y
       let m:=minorCharge V p q ε ρ i
       have hm₀:0 < m:= minor_pos V p q ε ρ i (fun l=>(hConfig.2.1 l).1)
       have he(t)(hu:t∈Icc (0:ℝ) 1): (∀ v:S.Field j',‖rayObserve a v (z i+t•y)‖ ≤B*m*‖v‖) ∧ Precise S a {z i+t•y}:=by
           refine h ρ z x q ⟨hConfig.1,fun j=>⟨(hConfig.2.1 j).1,hR j⟩,hConfig.2.2⟩ (t•y) ?_
           rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) ((Real.norm_eq_abs _).trans_le (by rw [abs_of_nonneg hu.1];exact hu.2))).trans_lt hsmall'
       let b':ℝ := -(massOf (V i):ℝ)+↑w.val-1+1/64
       let k':ℝ:= -(massOf (V i):ℝ) + d+1/64
       have hv:‖f x'‖≤A*t^b':=heye t ht ((hConfig.2.1 i).2.trans_le ((min_le_right ..).trans' (min_le_left ..))) x' ⟨fun l j h=>by unfold x'; rw [sub_sub_sub_cancel_right];exact hnear.1 _ _ h, fun l=> ?_⟩ (sub_self _)
       · constructor
         · exact fun t ht=>(he t ht).2
         unfold errTerm
         refine (rayTaylor hS hP (z:=z i) (x:=y) (a:=a) (f x') j ?_ (B*m*(U*(t^k'))) ?_).trans ?_
         · exact fun t ht=>(he t ht).2
         · intro u hu'; apply (he u hu'|>.1 _).trans ?_
           rw [show t^k'=(t^b':ℝ)*t^(j+1) from ?_]
           · exact (mul_le_mul_of_nonneg_left ((hq y (f x')).trans (mul_le_mul (mul_le_mul_of_nonneg_left hv hK) (pow_le_pow_left₀ (norm_nonneg y) (hnear.2 default).le (j+1)) (by positivity) (by positivity))) (by positivity : 0≤ B*m)).trans_eq (by unfold U;ring)
           rw [← Real.rpow_natCast t (j+1),← Real.rpow_add ht]; congr 1; unfold k' b' j; push_cast [Nat.cast_sub (Nat.le_of_lt_succ w.isLt)]; ring
         have hc:(p i).load (q i)=1:=by rw! (castMode:=.all) [hpi];rfl
         have heq: plainLoad p V ε ρ q=t^k'*m:=by rw [March.plug_credit,March.credit,hc,mul_one]; congr 2;rw [hpi];rfl
         rw [heq]
         calc B*m*(U*(t^k'))= (B*U)*(t^k'*m):=by ring
              _ ≤ K*(t^k'*m):=mul_le_mul_of_nonneg_right (by unfold K; linarith) (mul_nonneg (Real.rpow_nonneg ht.le _) hm₀.le)
       change ‖x i l-y‖< 2*((N.val*(2+1):ℕ):ℝ)*t;push_cast; linarith only [norm_sub_le (x i l) y,hnear.2 default,hnear.2 l,show ‖x i default‖=‖y‖ from rfl,hf]
end YM.MultipleContact.Centered
