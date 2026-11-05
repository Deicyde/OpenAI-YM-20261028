import YM.MergeProof.West.Canvas
import YM.TraceExtension.Prom.Front.West.Leet
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Pair
import YM.TraceExtension.Prom.Front.West.Rose
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middleSky C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNowSky (d:=d) c R x b hk h q T τ U ε)
variable (P:modes (Fin n) → poly (Chamber G C.S (i+1) p)) (hP : ∀ u,P u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)

def offerNowSky (_:StageNowSky (d:=d) c R x b hk h q T τ U ε) (Q:modes (Fin n)→poly (Chamber G C.S (i+1) p)):= inviteFtSky (hk:=hk) (Q ∘ Subtype.val) T c h
lemma salts_nowSky (s:ViewFt C k b p d x hk)(hs:t_ests x b hk T.2.val s (C:=C)) u z (V' : ViewFt C k b p d x hk→_):
   (p_lanterSky E V' u z).part s.val.val=p_lantedSky E V' u s z := by
   rw [p_lanterSky, Poly.part_sum, Finset.sum_eq_single s, if_pos hs,Poly.part_send,if_pos]
   · rfl
   · intro i _ h; split
     · rw [Poly.part_send,if_neg]; exact fun he=> h (Subtype.ext (Subtype.ext he.symm))
     rfl
   simp
lemma abandonedSky (s:modes (Fin n)) (h:∀ i:ViewFt C k b p d x hk,i.val.val≠s) u z:
   (p_lanterSky E (offerNowSky E P) u z).part s=0:=by
   rw [p_lanterSky,Poly.part_sum]; refine Finset.sum_eq_zero fun i _=>?_ ; split
   · rw [Poly.part_send,if_neg]; exact (h i).symm
   rfl

def tracesFtSky (w:List (modes (Fin n))) := fun (j:Fin E.count) z=> (w.map fun i=> (p_lanterSky E (offerNowSky E P) j z).part i).prod
variable (hx:roomTestSky C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olmSky x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε)(he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ i, Poetic (P i)) (hs:∀ i,totalDegree (P i)≤ D) (hu:∀ i,coin (P i)≤ r) (hp:∀ u : Manner n,∀ i'∈(P u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))

def sculptFtSky (w : List (modes (Fin n))) := dot ((Ship.yardSky C b c.allow p).hand T.1) (e_leganceSky b c x hk h T U ((R i).read (w.map P).prod))

local notation "LK"=> ViewFt C k b p d x hk
include hx t he he' H hs hu hp hr hP Hv
lemma wordAnswerSky (w:List (modes (Fin n))) (hw: ∀ i ∈ w, i.val ⊆ T.2.val.val.val) :
   (∀ j,letI:= (E.tag j).M; Integrable (tracesFtSky E P w j) (E.tag j).μ) ∧
    ‖plaidFtSky E (tracesFtSky E P w) - sculptFtSky (T:=T) (c:=c) (U:=U) (h:=h) (R:=R) (hk:=hk) P w‖ ≤ glare B ε r D w.length := by
   let K := (Ship.yardSky C b c.allow p).hand T.1; let V':= offerNowSky E P; let s := sculptFtSky (T:=T) (c:=c) (U:=U) (h:=h) (R:=R) (hk:=hk) P w
   by_cases hV: ∀ i ∈ w,∃ j : LK,j.val.val=i
   · haveI : Nonempty (ViewFt C k b p d x hk):= ⟨soloFt _ _ _ _ _ _ (Head T.2.val)⟩
     choose! σ hσ using hV
     let W:=w.map σ; let q:= fun t:Manner n=> P t.val
     have hQ : W.map (fun i=> q i.val)=w.map P:=by
       simp only [W,List.map_map]; apply List.map_inj_left.mpr; intro i hi; simp only [Function.comp_apply,q,hσ i hi]
     have Ht : fullP (C:=C) q W=(w.map P).prod:=congr_arg List.prod hQ
     have hh (j: Fin E.count):
       let G':= fullGSky (E.tag j) W
       let Y':= fullQSky (E.tag j) q W
       (tracesFtSky E P w j)=fun z=>dot K (((↑(G' z):ℂ))*Y' z):=by
       intro GG YY; funext z
       have hv (m: List (modes (Fin n))) (hx:m⊆w) : tracesFtSky E P m j z=dot K (((↑(fullGSky (E.tag j) (m.map σ) z):ℂ))*fullQSky (E.tag j) q (m.map σ) z):= by
         induction m with
         | nil=>simp [tracesFtSky,dot,fullGSky,fullQSky]
         | cons a l IH=>
           have he: a∈w:= hx (List.mem_cons_self ..)
           have ht:t_ests x b hk T.2.val (σ a) (C:=C):=by change (σ a).val.val.val⊆_; rw [hσ a he]; exact hw a he
           unfold tracesFtSky
           rw [List.map_cons,List.prod_cons]; change (p_lanterSky E V' j z).part a * tracesFtSky E P l j z=dot K (((↑( (c_hanceSky (E.tag j) (σ a) z)*(fullGSky (E.tag j) (l.map σ) z)):ℂ))*(traceFtSky (E.tag j) (σ a) (q (σ a).val) z *fullQSky (E.tag j) q (l.map σ) z))
           rw [show (p_lanterSky E V' j z).part a= _ from Eq.trans (congr_arg _ (hσ a he).symm) (salts_nowSky E (σ a) ht j z V'),show p_lantedSky E V' j (σ a) z= _ from e_ngagesSky E q _ _ _, IH (fun u hu=> hx (List.mem_cons_of_mem a hu)),Complex.ofReal_mul,dot_times]
           apply congr_arg; unfold c_hanceSky; ring
       exact hv w (List.Subset.refl _)
     have hv : ∀ i∈W,t_ests x b hk T.2.val i (C:=C):=by
       intro i hi; obtain ⟨v,hv,rfl⟩:= List.mem_map.mp hi; change (σ v).val.val.val ⊆ _; rw [hσ v hv]; exact hw v hv
     let F:= fun (j:Fin E.count) z=> ((↑(fullGSky (E.tag j) W z):ℂ))*fullQSky (E.tag j) q W z
     have hW i:= t_wornSky (E.tag i) q hx t Hv he he' hr (fun i=> H _) (fun i=> hs _) (fun i=> hu _) hp W hv
     refine ⟨fun j =>?_,?_⟩
     · letI:=(E.tag j).M; rw [hh]; exact extra_int _ _ _ (hW j).1
     rw [show tracesFtSky E P w=(fun j z=> dot K (F j z)) from funext hh]
     apply r_eparationSky; intro j
     letI:=(E.tag j).M
     have h: ‖(∫ z,F j z ∂(E.tag j).μ)- _‖ ≤ glare B ε r D W.length:= (hW j).2
     rw [show W.length= w.length from List.length_map _,Ht] at h; exact h
   push_neg at hV
   obtain ⟨v,hv,H'⟩:= hV
   have he' (j:Fin E.count) : tracesFtSky E P w j=0:=by
      funext z; change (w.map _).prod=0; apply List.prod_eq_zero; exact List.mem_map.mpr ⟨_,hv,abandonedSky E P v H' ..⟩
   have hx: P v=0:= by by_contra h; obtain ⟨i,h⟩:= hP v h; exact H' i h
   refine ⟨fun j=>?_,?_⟩
   · letI:=(E.tag j).M; rw [he']; exact integrable_zero _ _ _
   rw [show tracesFtSky E P w=fun _ _=>0 from funext he',plaidF_constSky]; unfold sculptFtSky
   rw [show (w.map P).prod=0 from List.prod_eq_zero (List.mem_map.mpr ⟨v,hv,hx⟩),map_zero,show e_leganceSky _ _ _ _ _ _ _ 0=0 from map_zero _,dot_zero, sub_self,norm_zero]; exact glare_nn B _ _ _ _ t.grain he.le hr
end YM.Next.Rank.Tapes.West
