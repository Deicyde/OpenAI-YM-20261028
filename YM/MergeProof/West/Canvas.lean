import YM.MergeProof.West.Pair
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middle C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNow (d:=d) c R x b hk h q T τ U ε)
variable (P:modes (Fin n) → poly (Chamber G C.S (i+1) p)) (hP : ∀ u,P u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)

def offerNow (_:StageNow (d:=d) c R x b hk h q T τ U ε) (Q:modes (Fin n)→poly (Chamber G C.S (i+1) p)):= inviteFt (hk:=hk) (Q ∘ Subtype.val) T c h
lemma salts_now (s:ViewFt C k b p d x hk)(hs:t_ests x b hk T.2.val s (C:=C)) u z (V' : ViewFt C k b p d x hk→_):
   (p_lanter E V' u z).part s.val.val=p_lanted E V' u s z := by
   rw [p_lanter, Poly.part_sum, Finset.sum_eq_single s, if_pos hs,Poly.part_send,if_pos]
   · rfl
   · intro i _ h; split
     · rw [Poly.part_send,if_neg]; exact fun he=> h (Subtype.ext (Subtype.ext he.symm))
     rfl
   simp
lemma abandoned (s:modes (Fin n)) (h:∀ i:ViewFt C k b p d x hk,i.val.val≠s) u z:
   (p_lanter E (offerNow E P) u z).part s=0:=by
   rw [p_lanter,Poly.part_sum]; refine Finset.sum_eq_zero fun i _=>?_ ; split
   · rw [Poly.part_send,if_neg]; exact (h i).symm
   rfl

def tracesFt (w:List (modes (Fin n))) := fun (j:Fin E.count) z=> (w.map fun i=> (p_lanter E (offerNow E P) j z).part i).prod
variable (hx:roomTest C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olm x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε)(he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ i, Poetic (P i)) (hs:∀ i,totalDegree (P i)≤ D) (hu:∀ i,coin (P i)≤ r) (hp:∀ u : Manner n,∀ i'∈(P u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))
local notation "LK"=> ViewFt C k b p d x hk

def sculptFt (w : List (modes (Fin n))) := dot ((Ship.yard C b c.allow p).hand T.1) (e_legance b c x hk h T U ((R i).read (w.map P).prod))
lemma glare_nn (B ε r:ℝ) (D i:ℕ)(h:1≤ B) (hv:0≤ε) (hr:0≤r):0≤glare B ε r D i:=by
  unfold glare
  have he:0≤defect B ε r D:=by unfold defect; positivity
  have hv':0 ≤ capZ B D r:=mul_nonneg hr (zero_le_one.trans (priced_up _ h))
  have hi :0≤ Common.priced B (2*(i*D)):= zero_le_one.trans (priced_up _ h)
  have hi' :0≤ Common.priced B (i*D):= zero_le_one.trans (priced_up _ h)
  positivity
include hx t he he' H hs hu hp hr hP Hv
lemma wordAnswer (w:List (modes (Fin n))) (hw: ∀ i ∈ w, i.val ⊆ T.2.val.val.val) :
   (∀ j,letI:= (E.tag j).M; Integrable (tracesFt E P w j) (E.tag j).μ) ∧
    ‖plaidFt E (tracesFt E P w) - sculptFt (T:=T) (c:=c) (U:=U) (h:=h) (R:=R) (hk:=hk) P w‖ ≤ glare B ε r D w.length := by
   let K := (Ship.yard C b c.allow p).hand T.1; let V':= offerNow E P; let s := sculptFt (T:=T) (c:=c) (U:=U) (h:=h) (R:=R) (hk:=hk) P w
   by_cases hV: ∀ i ∈ w,∃ j : LK,j.val.val=i
   · haveI : Nonempty (ViewFt C k b p d x hk):= ⟨soloFt _ _ _ _ _ _ (Head T.2.val)⟩
     choose! σ hσ using hV
     let W:=w.map σ; let q:= fun t:Manner n=> P t.val
     have hQ : W.map (fun i=> q i.val)=w.map P:=by
       simp only [W,List.map_map]; apply List.map_inj_left.mpr; intro i hi; simp only [Function.comp_apply,q,hσ i hi]
     have Ht : fullP (C:=C) q W=(w.map P).prod:=congr_arg List.prod hQ --x
     have hh (j: Fin E.count):
       let G':= fullG (E.tag j) W
       let Y':= fullQ (E.tag j) q W
       (tracesFt E P w j)=fun z=>dot K (((↑(G' z):ℂ))*Y' z):=by
       intro GG YY; funext z
       have hv (m: List (modes (Fin n))) (hx:m⊆w) : tracesFt E P m j z=dot K (((↑(fullG (E.tag j) (m.map σ) z):ℂ))*fullQ (E.tag j) q (m.map σ) z):= by
         induction m with
         | nil=>simp [tracesFt,dot,fullG,fullQ]
         | cons a l IH=>
           have he: a∈w:= hx (List.mem_cons_self ..)
           have ht:t_ests x b hk T.2.val (σ a) (C:=C):=by change (σ a).val.val.val⊆_; rw [hσ a he]; exact hw a he
           unfold tracesFt
           rw [List.map_cons,List.prod_cons]; change (p_lanter E V' j z).part a * tracesFt E P l j z=dot K (((↑( (c_hance (E.tag j) (σ a) z)*(fullG (E.tag j) (l.map σ) z)):ℂ))*(traceFt (E.tag j) (σ a) (q (σ a).val) z *fullQ (E.tag j) q (l.map σ) z))
           rw [show (p_lanter E V' j z).part a= _ from Eq.trans (congr_arg _ (hσ a he).symm) (salts_now E (σ a) ht j z V'),show p_lanted E V' j (σ a) z= _ from e_ngages E q _ _ _, IH (fun u hu=> hx (List.mem_cons_of_mem a hu)),Complex.ofReal_mul,dot_times]
           apply congr_arg; unfold c_hance; ring
       exact hv w (List.Subset.refl _)
     have hv : ∀ i∈W,t_ests x b hk T.2.val i (C:=C):=by
       intro i hi; obtain ⟨v,hv,rfl⟩:= List.mem_map.mp hi; change (σ v).val.val.val ⊆ _; rw [hσ v hv]; exact hw v hv
     let F:= fun (j:Fin E.count) z=> ((↑(fullG (E.tag j) W z):ℂ))*fullQ (E.tag j) q W z
     have hW i:= t_worn (E.tag i) q hx t Hv he he' hr (fun i=> H _) (fun i=> hs _) (fun i=> hu _) hp W hv
     refine ⟨fun j =>?_,?_⟩
     · letI:=(E.tag j).M; rw [hh]; exact extra_int _ _ _ (hW j).1
     rw [show tracesFt E P w=(fun j z=> dot K (F j z)) from funext hh]
     apply r_eparation; intro j
     letI:=(E.tag j).M
     have h: ‖(∫ z,F j z ∂(E.tag j).μ)- _‖ ≤ glare B ε r D W.length:= (hW j).2
     rw [show W.length= w.length from List.length_map _,Ht] at h; exact h
   push_neg at hV
   obtain ⟨v,hv,H'⟩:= hV
   have he' (j:Fin E.count) : tracesFt E P w j=0:=by
      funext z; change (w.map _).prod=0; apply List.prod_eq_zero; exact List.mem_map.mpr ⟨_,hv,abandoned E P v H' ..⟩
   have hx: P v=0:= by by_contra h; obtain ⟨i,h⟩:= hP v h; exact H' i h
   refine ⟨fun j=>?_,?_⟩
   · letI:=(E.tag j).M; rw [he']; exact integrable_zero _ _ _
   rw [show tracesFt E P w=fun _ _=>0 from funext he',plaidF_const]; unfold sculptFt
   rw [show (w.map P).prod=0 from List.prod_eq_zero (List.mem_map.mpr ⟨v,hv,hx⟩),map_zero,show e_legance _ _ _ _ _ _ _ 0=0 from map_zero _,dot_zero, sub_self,norm_zero]; exact glare_nn B _ _ _ _ t.grain he.le hr
end YM.Next.Rank.Tapes.West
