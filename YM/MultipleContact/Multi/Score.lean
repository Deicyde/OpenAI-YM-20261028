import YM.MultipleContact.Multi.Collar
/-! Filling one root while retaining the incompatible grids at arbitrary independent other scales. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 100000
noncomputable section
namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Acme Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {b:ℕ}{n d:Fin b→ℕ} (V:∀i:Fin b,Fin (n i)→ S.Tag) (D:∀i:Fin b,Detector S (d i)) (p:Fin b →Mode)
variable [hn:∀i,Inhabited (Fin (n i))]
variable {P:DiffPlan S}(hA:Acme.Aroma C)(hT:Treasury C)(hc:CellHyp C F)(hM:F.PointLimits C S)(H:S.Hierarchy)(hP:P.Derivatives S)(hC:C.Makes)
variable {X:S.Rotation}(hX:X.Oriented S)(hG:G.Simple)
variable {t:ℕ} (h:Store S t)(L:Lattice.Side)(hb:(Finset.univ.filter fun i=>p i=.signed).card ≤ t+1) (κ ε:ℝ)(hs:0<κ)(hε:0<ε) {Θ: Fin b→ℝ}
def Clause (Q:Finset (Fin b))(j:Fin b→ℕ→ℕ)(K:ℝ)(M:ℕ)(r:ℝ):Prop:= ∀ (m:Fin b →ℕ)(z:Fin b→ E4),Close z κ → ∀ρ:Fin b → ℝ, (∀i,M≤ m i ∧ tail C (ρ i) (m i) ∧ 0<ρ i ∧ ρ i < r) → ∀ y:∀i:Fin b,Fin (n i) → E4, (∀ i,p i≠.fused → Cord.Band (n i) L (ρ i) (y i)) → (∀i∈Q,Cord.Near (n i) L (ρ i) (y i)) → (∀i:Fin b,i∉Q→p i=.signed→∀ a:Fin (n i)×Axis,Placed (n i) (C.S.a (j i (m i))) (y i) a) → ∀w:∀i:Fin b,S.Field (d i),(∀i,p i=.fused→‖w i‖≤1) → ‖evaluation S (planted p V D z w y)‖ ≤ K*due V D p ρ ε
variable {Q:Finset (Fin b)}{j:Fin b→ℕ→ℕ}{K:ℝ}{M:ℕ}{r:ℝ}
variable (hj:∀k:Fin b,1< Θ k ∧ Tendsto (j k) atTop atTop ∧ Tendsto (fun m=>C.S.scale (j k m)/C.S.scale m) atTop (𝓝 (Θ k)))
include hP hA hT hc hM H hC hG hX h hb hj hn hs hε
set_option quotPrecheck false
lemma raise {k:Fin b} (hprev:Clause V D p L κ ε Q j K M r)(hK:0 < K)(hr:0 < r)(hq: k∉Q)(hk:p k=.signed):∃ K'> (0:ℝ),∃ r'> (0:ℝ),∃ M',Clause V D p L κ ε (insert k Q) j K' M' r':=by
       obtain ⟨l,hL⟩:=airfare hA (j k) (Θ k) (n k) (hj k).1 (hj k).2.1 (hj k).2.2 ((d k:ℝ)+1/64+ε) -- order
       let T (i:Fin (n k)×Axis):= update V k (Line.tags (V k) P i.1 i.2 l)
       obtain ⟨K0,hK0,hproof⟩:= Cord.sample L l (n k)
       choose U r1 hU hr1 hweak using (fun i:Fin (n k)×Axis=>weaker (T i) D p hA hT hc hM H hP hC hX hG h L hk hb κ ε hs hε)
       obtain ⟨m1,hm⟩:=eventually_atTop.mp hL
       obtain ⟨a,ha,hag,hprobe⟩:= collar_pos (D:=D) hs -- positive margin wrt configurations and probe j=0
       have hR : ∃r₂ : ℝ,0 < r₂ ∧ ∀i:Fin (n k)×Axis,r₂ < r1 i:= by
            have h:(∀ᶠ r in 𝓝 (0:ℝ),∀ i,r< r1 i):= eventually_all.mpr (fun i:Fin (n k)×Axis=>gt_mem_nhds (hr1 i)) -- named params error
            have h'':=h.filter_mono (nhdsWithin_le_nhds (s:=Ioi 0)); obtain ⟨u,hu,hv⟩:=Eventually.exists ((show ∀ᶠ x:ℝ in 𝓝[>]0,0<x from self_mem_nhdsWithin).and h''); exact ⟨u,hu,hv⟩
       obtain ⟨r₀,hr₀,hfine⟩:=hR
       obtain ⟨C',hC'⟩:=Finite.bddAbove_range U
       let Amax:= max K C'; have hAmax:0 < Amax:=hK.trans_le (le_max_left ..)
       let r'':=min r₀ (min r (a/(4*(L.val:ℝ))))
       have hlv:(0:ℝ)<L.val:=by exact_mod_cast L.pos
       refine ⟨Amax*K0,mul_pos hAmax hK0,r'',lt_min hr₀ (lt_min hr (by positivity)),max m1 M,?_⟩
       intro m z hz ρ hρ xe hband hp hplaced w hw
       let price := due V D p ρ ε
       let num (v:Fin b→ ℕ):=C.S.a (j k (v k)); let a' := num m; have ht:0<a':= C.S.a_pos _
       have hc := hm (m k) ((le_max_left ..).trans (hρ k).1) _ (hρ k).2.2.1 (hρ k).2.1
       let y (v):= update xe k v
       let f (v):=evaluation S (planted p V D z w (y v))
       have hρ₀ (i):0<ρ i:=(hρ i).2.2.1
       have hp₀:0<price:=Finset.prod_pos fun i _=>Real.rpow_pos_of_pos (hρ₀ i) _
       have hs (x) (hB:Cord.Band (n k) L (ρ k) x)(hX':∀v,Placed (n k) a' x v):‖f x‖≤ Amax*price:=by
           apply (hprev m z hz _ ?_ (y x) ?_ ?_ ?_ w hw)|>.trans; exact mul_le_mul_of_nonneg_right (le_max_left ..) hp₀.le
           · intro i; exact ⟨(le_max_right ..).trans (hρ i).1,(hρ i).2.1,hρ₀ _,((hρ i).2.2.2.trans_le ((min_le_right ..).trans (min_le_left ..)))⟩
           · intro i hi; by_cases h:i=k
             · rw [h]; unfold y; rw [update_self]; exact hB
             dsimp only [y]; rw [update_of_ne h];exact hband i hi --update_self]; exact hB; rw [← h,update_of_ne h] -- replace
           · intro i hi; have hu':i≠k:=fun h=>(hq (h ▸ hi)); unfold y; rw [update_of_ne hu']; exact hp _ (Finset.mem_insert_of_mem hi)
           intro i hi h'; by_cases hh:i=k
           · rw [hh]; unfold y; rw [update_self]; exact hX'
           unfold y; rw [update_of_ne hh]; exact hplaced i (by simpa only [Finset.mem_insert,not_or] using! And.intro hh hi) h'
       have hd (i:Fin (n k)×Axis)(hi:i.fst≠default) (x:Fin (n k)→ E4)
              (hP':∀t∈ Icc (-Cord.radius (n k) l) (Cord.radius (n k) l),Cord.Band (n k) L (ρ k) (Cord.polar i x a' t)):
              ∃ z':ℕ→ℝ→ℂ,z' 0=(f ∘ Cord.polar i x a') ∧ (∀s<l,∀t∈Icc (-Cord.radius (n k) l) (Cord.radius (n k) l),HasDerivAt (z' s) (z' (s+1) t) t) ∧ ∀t∈Icc (-Cord.radius (n k) l) (Cord.radius (n k) l),‖z' l t‖≤Amax*price:=by
                let v i:=T i
                let X1(s):= y (Cord.polar i x a' s); let V₀ s:= update V k (Line.tags (V k) P i.1 i.2 s)
                let Z' (v:ℕ)(t:ℝ):=a'^v • evaluation S (planted p (V₀ v) D z w (X1 t))
                have hB' (t:ℝ) (ht:t∈Icc (-Cord.radius (n k) l) (Cord.radius (n k) l)) (l:Fin b) (h:l≠k ∨ True) (h':p l≠ .fused): Band (n l) L (ρ l) (X1 t l):=by
                    unfold X1 y; by_cases h:l=k
                    · subst l;rw [update_self]; exact hP' _ ht
                    rw [update_of_ne h]; exact hband _ h'
                have hSmall t (ht:t∈Icc (-Cord.radius (n k) l) (Cord.radius (n k) l)) (u:Fin b) (hL:p u≠.fused)(v):‖(X1 t) u v‖ < a:=((hB' _ ht _ (Or.inr trivial) hL).2.2 v).trans (by have hp:=((lt_div_iff₀ (show 0 < 4*(L.val:ℝ) from mul_pos (by positivity) hlv)).mp ((hρ u).2.2.2.trans_le ((min_le_right ..).trans (min_le_right ..))));linarith only [hp])
                refine ⟨Z',?_,fun s h t ht=>(?_), fun t ht=>?_⟩
                · funext u
                  have he : V₀ 0=V:=by unfold V₀ Line.tags; simp only [trek, update_eq_self]
                  simp [Z',he,f,X1]
                · refine deform H hP s k i hk a' x t a ha (fun i j hij=>hag.trans_le (hz i j hij)) (fun l h' h₁=>?_ ) ?_ ?_ ?_
                  · constructor
                    · exact band_inj (hband _ h₁) (hρ₀ _)
                    intro u; specialize hSmall t ht l h₁ u; simpa only [X1,y,update_of_ne h'] using! hSmall.le
                  · intro u; simpa only [X1,y,update_self] using (hSmall t ht k (hk.symm ▸ (by decide)) u).le
                  · exact band_inj (hP' _ ht) (hρ₀ _)
                  exact band_avoids D L _ _ (hP' t ht) ((hρ k).2.2.2.trans_le ((min_le_right ..).trans (min_le_right ..))) (hprobe k)
                let q:= update p k .raw
                have h0 : ‖evaluation S (planted p (T i) D z w (X1 t))‖ ≤ U i * due (T i) D q ρ ε:= hweak i z hz ρ (fun l=>(by exact ⟨hρ₀ _, (hfine i).trans_le' ((hρ l).2.2.2.le.trans (min_le_left ..))⟩)) (X1 t) (fun l h=>hB' t ht l (Or.inr trivial) h) w hw
                change ‖a'^l • evaluation _ _‖ ≤ _
                rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _)] -- ht clash
                apply (mul_le_mul_of_nonneg_left h0 (pow_nonneg (C.S.a_pos _).le _) |>.trans)
                rw [mul_left_comm]; exact mul_le_mul ((hC' (mem_range_self i)).trans (le_max_right ..)) (due_step P hk l i hρ₀ (hρ₀ k) ε (C.S.a_pos _) hc.1) (mul_nonneg (pow_nonneg (C.S.a_pos _).le _) (weight_pos (T i) D q ρ hρ₀).le) hAmax.le
       have hv:= hproof (ρ k) a' (Amax*price) ht (mul_pos hAmax hp₀) (hρ₀ k) hc.2 f hs hd (xe k) (hp k (Finset.mem_insert_self ..)); rw [mul_right_comm] at hv; apply hv.trans'; unfold f y; rw [update_eq_self]; -- maybe fail
end YM.MultipleContact.Joins

namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Acme Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {b:ℕ}{n d:Fin b→ℕ} (V:∀i:Fin b,Fin (n i)→ S.Tag) (D:∀i:Fin b,Detector S (d i)) (p:Fin b →Mode)
variable [hn:∀i,Inhabited (Fin (n i))]
variable {P:DiffPlan S}(hA:Acme.Aroma C)(hT:Treasury C)(hc:CellHyp C F)(hM:F.PointLimits C S)(H:S.Hierarchy)(hP:P.Derivatives S)(hC:C.Makes)
variable {X:S.Rotation}(hX:X.Oriented S)(hG:G.Simple)
include hA hC hT hc hM H
lemma clause_init (L:Lattice.Side) (κ ε:ℝ)(hs:0<κ)(hε:0<ε):∃ (t:Fin b→ℝ)(j:Fin b→ℕ→ℕ) (K₀:ℝ)(M:ℕ),0<K₀ ∧ Clause V D p L κ ε ∅ j K₀ M 1 ∧ (∀ k:Fin b,1 < t k ∧ Tendsto (j k) atTop atTop ∧ Tendsto (fun m:ℕ=>C.S.scale (j k m)/C.S.scale m) atTop (𝓝 (t k))):=by
        obtain ⟨K',Θ,j,M,h0,h1,hV⟩:=cost_grid V D p hA hT hc H hM hC hε hs (L:=L) -- arg order?
        refine ⟨Θ,j,K',M,h0,?_ ,h1⟩
        intro m z hh ρ hr y he _ hG w hW
        exact hV _ _ (fun i=>⟨(hr i).1, (hr i).2.2.1, (hr i).2.1⟩) _ hh _ he (fun i=>hG i (by simp)) _ hW
lemma clause_done {j:Fin b→ ℕ→ℕ}(hG:G.Simple)(L:Lattice.Side)(κ ε:ℝ){A r:ℝ}{M:ℕ}(Q:Finset (Fin b))(hQ:Q=Finset.univ.filter fun i=>p i=.signed)(hA':0<A)(hr:0<r)(h:Clause V D p L κ ε Q j A M r):
     ∃ (A r:ℝ),0 < A ∧ 0<r ∧ ∀ z:Fin b → E4,Close z κ → ∀ρ:Fin b → ℝ, (∀i,0<ρ i ∧ ρ i < r)→ ∀ y:∀i:Fin b,Fin (n i) → E4,(∀i:Fin b,p i ≠.fused → Cord.Near (n i) L (ρ i) (y i)) →∀w:∀i:Fin b,S.Field (d i),(∀i:Fin b,p i=.fused→‖w i‖≤1)→
     ‖evaluation S (planted p V D z w y)‖ ≤ A*due V D p ρ ε:=by
        obtain ⟨u,hu,hU⟩:=shell_bound hA.notes hG M
        refine ⟨A,min r u,hA',lt_min hr hu,fun z hz ρ hρ y hy w hw=> ?_⟩
        choose m h1 h2 using fun i:Fin b=>hU (ρ i) (hρ i).1 ((hρ i).2.trans_le (min_le_right ..))
        apply h m _ hz _ (fun i=>⟨h1 i, h2 i, (hρ i).1,(hρ i).2.trans_le (min_le_left ..)⟩) _ (fun i hi=> band_of_near (hy _ hi) (hρ i).1) (fun i hiQ=> hy i (fun hi=> Mode.noConfusion ((Finset.mem_filter.mp (hQ ▸ hiQ)).2.symm.trans hi))) (fun i hQ' hg=>(False.elim (hQ' (hQ.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩)))) w hw
include hP hX hG
-- No assumption `Store` retained
lemma fills :∀m:ℕ,Store S m:=by
     intro s
     induction s
     case zero=>
       intro t n hN V d D p hb κ ε hs hε lamp
       obtain ⟨Θ,j,K₀,M,h1,hQ,HQ⟩:= clause_init V D p hA hT hc hM H hC lamp κ ε hs hε
       exact clause_done V D p hA hT hc hM H hC hG lamp κ ε ∅ (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hb)|>.symm) h1 (show (0:ℝ)<1 from zero_lt_one) hQ
     rename_i s IH
     intro t n hN V d D p hb κ ε hs hε lamp
     let Q:= Finset.univ.filter fun i:Fin t=> p i=.signed
     obtain ⟨Θ,j,K₀,M,h1,hQ,HQ⟩:= clause_init V D p hA hT hc hM H hC lamp κ ε hs hε
     have he(Q':Finset (Fin t)) (hq:Q' ⊆ Q): ∃ A> (0:ℝ),∃r> (0:ℝ),∃m,Clause V D p lamp κ ε Q' j A m r:=by
         induction Q' using Finset.induction_on with
         | empty=> exact ⟨K₀,h1,1,one_pos,M,hQ⟩
         | @insert a q ha ih =>
            obtain ⟨K',hP',r,hr,M',he⟩:= ih (fun i hi=> hq (Finset.mem_insert_of_mem hi))
            have hq:=raise V D p hA hT hc hM H hP hC hX hG IH lamp hb κ ε hs hε HQ he hP' hr ha (Θ:=Θ) (by have hq:=hq (Finset.mem_insert_self a q); simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and] using hq)
            exact hq
     obtain ⟨A,hA',r,hR,m,hb⟩:=he Q (by rfl)
     exact clause_done V D p hA hT hc hM H hC hG lamp κ ε Q rfl hA' hR hb
end YM.MultipleContact.Joins
