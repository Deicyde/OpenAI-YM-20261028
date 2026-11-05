import YM.MultipleContact.Center.Eye
/-! Recenter a single flagged node, first under an anchor match; uniform linear estimates for the context used to translate that match. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
namespace YM.MultipleContact.Centered
open Set Filter Function Table Extraction Spec Drama Script Scene ScheduleRow Bunching Two Joins
open March
open scoped Classical ContDiff Topology BigOperators

variable {G:Gauge}{L:Register G}{S:Table L}
variable {b k d:ℕ}{n:Fin b→ℕ}[hn:∀i:Fin b,Inhabited (Fin (n i))](V:∀i:Fin b,Fin (n i)→S.Tag)(p:Fin b→March S)
  (κ ε:ℝ) (N:Lattice.Side) (i:Fin b)(D:Detector S d)
  (hpi:p i=.root d D) (hε:0<ε)(hk:0<κ)
-- actual context independent of operation at i. bounds all incoming x within own profile.
variable (weak:Good k S)(hc:amount p≤ k+1)
def smallEnough :ℝ:= min 1 (κ/(8*N.val))
lemma enough_pos (h:0<κ): 0 < smallEnough κ N:=lt_min zero_lt_one (div_pos h (mul_pos (by norm_num) (show 0 < (N.val:ℝ) from (by exact_mod_cast N.pos))))
include hε hpi hc hk weak
lemma eligible (w:March S) (hx:¬(w.advanced=true)): amount (altered p i w) ≤ k:=by have hh:=lessen p i (show (p i).advanced from by rw [hpi];rfl) w hx; omega
lemma anchored_first : ∃ B> (0:ℝ),∃r> (0:ℝ),∀ (ρ:Fin b→ℝ)(z:Fin b→ E4)(x:∀i:Fin b,Fin (n i)→E4)(q:∀i,(p i).Data), Permit p κ r N ρ z x →
    let u:= x i default
    ‖evaluation S ((packet S (V i) (x i) (z i) - insertion S (z i+u) (D.apply (V i) (points (fun s=>x i s-u)))) * fixture V p q z x i)‖ ≤ B * plainLoad p V ε ρ q :=by
     let w:March S:=.anchor d D
     obtain ⟨A,hA,r,hr,hRead⟩:=weak (altered p i w) V ε (κ/2) (expand N 2) hε (half_pos hk) (eligible p κ ε i D hpi hε hk weak hc w Bool.noConfusion)
     refine ⟨A,hA,min r (smallEnough κ N), lt_min hr (enough_pos κ N hk),?_⟩
     intro ρ z x q h u
     let y:=fun s:Fin (n i)=>x i s-u
     let t:=z i+u
     have hNear:= h.2.2 i; rw [hpi] at hNear
     have hu:‖u‖<2*N.val*ρ i:=hNear.2.1 _
     have hN:0<(N.val:ℝ):= by exact_mod_cast N.pos
     have hu':‖u‖<κ/4:=by have hie:= (lt_div_iff₀ (show 0<(8*N.val:ℝ) by positivity)).mp ((h.2.1 i).2.trans_le (le_trans (min_le_right ..) (min_le_right ..)));linarith only [hu,hie]
     have hrN: 0 < (N.val:ℝ)*(ρ i):=mul_pos hN (h.2.1 i).1
     have hz:Close (update z i t) (κ/2):= track z κ i h.1 hk t (show ‖_‖<_ by rw [add_sub_cancel_left]; exact hu') -- argument order track (z κ i)
     have hx:Permit (altered p i w) (κ/2) r (expand N 2) ρ (update z i t) (update x i y):=by
           refine ⟨hz,fun j=>⟨(h.2.1 j).1,(h.2.1 j).2.trans_le (min_le_left ..)⟩,altar_allow p x ρ (expand N 2) i w y ?_ (fun j=>allow_large p x N j 2 (h.2.1 j).1 (h.2.2 j))⟩ -- order altar_allow p x _
           refine ⟨fun l s e=>by unfold y; rw [sub_sub_sub_cancel_right]; exact hNear.1 l s e,fun s=>?_ ,fun _ _ _=>sub_self _⟩
           change ‖x i s-u‖ < 2 * ((N.val*(2+1):ℕ):ℝ)*ρ i; push_cast
           linarith only [norm_sub_le (x i s) u, hNear.2.1 s,hu,hrN]
     have hcharge:w.credit (V i) ε (ρ i) ()=(p i).credit (V i) ε (ρ i) (q i):=by unfold March.credit; congr 1; rw [hpi]; rfl; rw! (castMode := .all) [hpi];rfl
     have hR:=hRead (newData p q i (v:=w) ()) ρ _ _ hx
     rw [alt_product,alt_credit] at hR
     rw [plug_credit,← hcharge]
     refine (congr_arg (fun v=>‖evaluation S (v*fixture V p q z x i)‖) ?_).le.trans hR
     change packet S _ _ _ - insertion S _ _= packet S (V i) y t - insertion S _ _; congr 1
     unfold Scene.packet; congr 1; funext s; dsimp [t,y]; abel

omit hε hpi hk hc weak
lemma secure_part (l:Fin b)(r:ℝ) (z:Fin b→ E4)(x:∀i,Fin (n i)→E4)(q:∀i:Fin b,(p i).Data) (hr:0 < r)(he:(p l).allow N r (x l)):
    Secure S (Metric.closedBall (z l) (2*N.val*r)) ((p l).payload (V l) (z l) (x l) (q l)):=by
          let E:ℝ:=2*N.val*r; let K:=Metric.closedBall (z l) E; have hE:0 ≤ E:=by unfold E;positivity
          have hf(d:ℕ)(v:S.Field d):Secure S K (insertion S (z l) v):=Scene.insertion_secure S v (Metric.mem_closedBall_self hE)
          suffices hv : ∀ u:March S,u.allow N r (x l)→∀w:u.Data,Secure S K (u.payload (V l) (z l) (x l) w) from hv (p l) he (q l)
          intro p hp v; cases p with
          | field k=> exact hf k v
          | raw=>exact (hpacket E K hp.2.1 hp.1) -- hpacket defined where?
          | anchor k D=>exact Secure.diff S (hpacket E K hp.2.1 hp.1) (hf _ _)
          | root k D=>exact Secure.diff S (hpacket E K hp.2.1 hp.1) (hf _ _)
 where hpacket (A:ℝ)(K:Set E4) (hk:∀s,‖x l s‖ <2*N.val*r)(hp:∀s u,s≠u→ r/4<‖x l s-x l u‖) : Secure S (Metric.closedBall (z l) (2*N.val*r)) (packet S (V l) (x l) (z l)):=by
              refine Scene.packet_secure S _ _ (fun a b he=> by by_contra h; have hh:=hp a b h; rw [he,sub_self,norm_zero] at hh; linarith only [hh,hr]) (by rintro u ⟨s,rfl⟩;rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left]; exact (hk s).le)
omit V p in
lemma unbnd {d:ℕ}(a:Grammar (Alpha S))(z:E4)(S0:S.Symmetric)(A:ℝ) (h:∀v:S.Field d, ‖v‖≤1 → ‖rayObserve a v z‖≤ A): ∀v:S.Field d,‖rayObserve a v z‖ ≤ A*‖v‖ :=by
         intro v
         obtain ⟨f,hf⟩:=Scene.inline S (d:=d) S0 z a
         change ‖evaluation S (stamp ((_:S.Tag),z) * _)‖≤ _; rw [hf]
         by_cases he:v=0
         · simp [he]
         let y:= (‖v‖⁻¹:ℝ) • v; have hv':0 < ‖v‖:=norm_pos_iff.mpr he; have hy:v=(‖v‖:ℝ) • y:=by unfold y; rw [smul_smul,mul_inv_cancel₀ hv'.ne',one_smul]
         have hk:‖f y‖≤ A:= by rw [← hf]; change ‖rayObserve a _ z‖≤ A; apply h; exact le_of_eq (by simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv'),inv_mul_cancel₀ hv'.ne'])
         nth_rw 1 [hy];rw [show f (‖v‖ • y)=‖v‖ • f y from (f.restrictScalars ℝ).map_smul ‖v‖ y, norm_smul,Real.norm_eq_abs,abs_of_pos hv', mul_comm A]; exact mul_le_mul_of_nonneg_left hk hv'.le
include hε hpi hc hk weak
lemma press_bound (j:ℕ)(H:S.Symmetric):∃ C'> (0:ℝ),∃ r> (0:ℝ),∀ (ρ:Fin b→ ℝ)(z:Fin b→ E4)(x:∀i,Fin (n i)→E4) (q:∀i:Fin b,(p i).Data),Permit p κ r N ρ z x→ ∀u:E4, ‖u‖<κ/4 →
    let f:=fixture V p q z x i; (∀v:S.Field j, ‖rayObserve f v (z i+u)‖ ≤ C'*minorCharge V p q ε ρ i *‖v‖)∧ Precise S f {z i+u}:=by
            let w:March S:=.field j; obtain ⟨K,hK,r,hr,H'⟩:=weak (altered p i w) V ε (κ/2) N hε (half_pos hk) (eligible p κ ε i D hpi hε hk weak hc w Bool.noConfusion)
            refine ⟨K,hK, min r (smallEnough κ N),lt_min hr (enough_pos κ N hk),?_⟩
            intro ρ z x q h u hu f
            have hN:0<(N.val:ℝ):= by exact_mod_cast N.pos
            have ha(l): 2*N.val*ρ l ≤ κ/4:=by -- casts should be real due ρ
                have hu:=(h.2.1 l).2.trans_le (le_trans (min_le_right ..) (show smallEnough κ N≤ κ/(8*N.val) from min_le_right ..))
                linarith only [(lt_div_iff₀ (show (0:ℝ)<8*N.val by positivity)).mp hu]
            constructor
            · apply unbnd f (z i+u) H
              intro v hv
              let q':w.Data:=v; let t:=z i+u
              have ht:= H' (newData p q i (v:=w) q') ρ (update z i t) (update x i (x i)) ?_
              · rw [alt_product,alt_credit] at ht
                change ‖rayObserve (fixture ..) v t‖ ≤ K*(w.credit (V i) ε (ρ i) q' * _) at ht
                rwa [show w.credit (V i) ε (ρ i) q'=1 from (by unfold March.credit;rw [show w.weight (V i) ε=0 by rfl,Real.rpow_zero,one_mul,show w.load q'=1 from max_eq_left hv]),one_mul] at ht -- max not unfolded
              have ht':=altar_allow p x ρ N i w (x i) (True.intro) h.2.2
              exact ⟨track z κ i h.1 hk t ((by simpa [t] using hu)),fun k=>⟨(h.2.1 k).1,(h.2.1 k).2.trans_le (min_le_left ..)⟩,ht'⟩
            let L(l:Fin b):=Metric.closedBall (z l) (κ/4); let s:=Finset.univ.erase i
            have hgap {l j:Fin b} (he:l≠j)(y)(hy:y∈L l)(hy':y∈L j):False:=by have h₀: dist (z l) (z j)≤κ/4+κ/4:= (dist_triangle _ y _).trans (by rw [dist_comm (z l) y];exact add_le_add (Metric.mem_closedBall.mp hy) (Metric.mem_closedBall.mp hy')); linarith only [hk,h₀,h.1 l j he,dist_eq_norm (z l) (z j)] -- dist_eq_norm inside linarith ok
            refine precise_secure S (K:=⋃l∈s,L l) (Set.disjoint_left.mpr ?_) (secure_product S (fun l hl=> Secure.weak S (Metric.closedBall_subset_closedBall (ha l)) (secure_part V p N l (ρ l) z x q (h.2.1 l).1 (h.2.2 l))) (fun l hl j hj hL=>Set.disjoint_left.mpr (fun y=>hgap hL y))) -- secure_part .. _ _ oversaturate
            rintro y hy (hy':y∈({z i+u}:Set E4)); have eq := Set.mem_singleton_iff.mp hy'; subst y; obtain ⟨l,hl,hL⟩:=Set.mem_iUnion₂.mp hy -- hy' proof singleton
            exact hgap (Finset.mem_erase.mp hl|>.1) _ (by convert hL) ((by change dist _ _≤_; simpa [dist_eq_norm] using hu.le): z i+u ∈ L i)
end YM.MultipleContact.Centered
