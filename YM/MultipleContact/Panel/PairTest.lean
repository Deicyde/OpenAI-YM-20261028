import YM.MultipleContact.Panel.PairData
import Mathlib.Data.List.FinRange
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.MultipleContact.Panel.PairSet
open Set Function Filter MeasureTheory Table Extraction Spec Ward Metric
open scoped ContDiff Classical BigOperators
variable {G:Gauge}{B:Register G}{S:Table B}{b:ℕ}(v:Fin b→Fin 2→ S.Tag)(u:∀i,Choice (v i))
def line (L:List (Fin b)):List (Fin b×ℕ) :=match L with | []=>[] | i::s=>let r:=line s; if (u i).isSome then (i,jetSpec (v i) (u i)-1)::r else r
def queue:List (Fin b×ℕ):=line v u (List.ofFn id)
lemma line_active {L:List (Fin b)}{k:Fin b×ℕ}(h:k∈line v u L):k.1∈ L:=by
        induction L with
        |nil=>exact False.elim ((List.not_mem_nil) h)
        |cons _ _ IH=> unfold line at h; split_ifs at h; obtain h|h:=List.mem_cons.mp h; simp [h]; exact List.mem_cons_of_mem _ (IH h); exact List.mem_cons_of_mem _ (IH h)
lemma line_valid {L:List (Fin b)}(hL:L.Nodup) : ((line v u L).map Prod.fst).Nodup:=by
        induction L with
        |nil=> exact List.nodup_nil
        |cons _ _ IH=> unfold line; split_ifs
                       · rw [List.map_cons,List.nodup_cons,List.nodup_cons.mp hL|>.2|>IH|>iff_true_intro,and_true]; rintro h; obtain ⟨k,hk,rfl⟩:=List.mem_map.mp h; exact (List.nodup_cons.mp hL).1 ((line_active v u hk))
                       exact IH ((List.nodup_cons.mp hL).2)

def lot {v:Fin 2→S.Tag}(s:ℝ)(u:Choice v):ℝ:=if u.isSome then gain ((jetSpec v u)-1) s else 1

def Guard (k:ℕ)(s:ℝ)(f:Board b k→ℂ):Board b k→ℂ:=Factors (port k) s (queue v u) f
lemma line_gain (s:ℝ){k:ℕ}(L:List (Fin b))(x:Board b k): market (port k) s (line v u L) x=(L.map fun i:Fin b=>lot s (u i) * ‖x.2 i‖^(jetSpec (v i) (u i))).prod:=by
              induction L with
              |nil=>rfl
              |cons w s' IH=> unfold line; split_ifs with h
                              · simp only [market, List.map_cons,IH,List.prod_cons,port_read,lot,if_pos h]
                                have he:jetSpec (v w) (u w)-1+1=jetSpec (v w) (u w):=by
                                      rcases ht:u w with _|t
                                      · simp only [ht,Option.isSome_none,Bool.false_eq_true] at h
                                      exact (show (degree (v w)-t.val.val+1)-1+1=degree _-t.val.val+1 from Nat.sub_add_cancel (Nat.le_add_left 1 _))
                                rw [he]
                              have h':u w=none:=by cases he:u w with | none=>rfl | some t=>simp [he] at h
                              rw [IH]; exact (show _ by simp [h',lot,jetSpec])
lemma queue_gain (s:ℝ){k:ℕ}(x:Board b k):market (port k) s (queue v u) x=(∏ i:Fin b, lot s (u i)) * ∏i:Fin b,‖x.2 i‖^(jetSpec (v i) (u i)):=by rw [queue,line_gain,List.map_ofFn,List.prod_ofFn]; exact Finset.prod_mul_distrib
lemma Guard.cost {s:ℝ}(hs:0<s){k:ℕ}(f:Board b k→ℂ){A:ℝ}{D:ℕ}(hA:Cap D f A)(he:payment (queue v u)≤D)(hf:ContDiff ℝ ∞ f)(x:Board b k):‖Guard v u k s f x‖≤ A*(∏i:Fin b,lot s (u i))* (∏i:Fin b, ‖x.2 i‖^(jetSpec (v i) (u i))):=by
             have ht:= Panel.budget (port k) (port_cross k) (port_norm k) s hs (queue v u) (line_valid v u (by rw [List.nodup_ofFn];exact injective_id)) hf hA [] (by simpa) (by simp) x
             change ‖Guard v u k s f x‖ ≤ A* _ * _ at ht; simpa [queue_gain,Guard,mul_assoc] using ht
lemma Guard.smooth (s:ℝ){k:ℕ}(f:Board b k→ℂ)(hf:ContDiff ℝ ∞ f):ContDiff ℝ ∞ (Guard v u k s f):= Factors_smooth (port k) s (queue v u) hf
lemma factor_center_out (s:ℝ){k:ℕ}(f:Board b k→ℂ)(hf:ContDiff ℝ ∞ f) (W:Set (Fin (b+k)→E4))(h: ∀ x∈Function.support f,x.1∈W)(x:Board b k)(hx:x.1∉W)(L:List (Fin b×ℕ)): Factors (port k) s L f x=0:=by
            induction L generalizing x with
            |nil=> exact Classical.by_contradiction (fun h'=>hx (h x h'))
            |cons w L IH=> unfold Factors; rw [(port k w.1).trim_on s w.2 (Factors_smooth _ s L hf)]
                           have he:(port k w.1).slice x (Factors (port k) s L f)=(0:E4→ℂ):=by funext y; unfold Lens.slice;rw [IH _ (show ((port k w.1).lay x y).1∉W from by rw [port_lay_left]; exact hx)];rfl -- IH takes hx explicit
                           rw [he]; simp [diff,polyJet,coeff]
lemma guard_center_support (s:ℝ){k:ℕ}(f:Board b k→ℂ)(hf:ContDiff ℝ ∞ f) (W:Set (Fin (b+k)→E4))(h: ∀ x∈Function.support f,x.1∈W)(x:Board b k)(hx:x.1∉W): Guard v u k s f x=0:=factor_center_out s f hf W h x hx ..
@[simp] lemma Guard.equality (s:ℝ){k:ℕ}(f:Board b k→ℂ)(hf:ContDiff ℝ ∞ f)(he:u=(fun _=>Option.none)) : Guard v u k s f=f:=by rw [he]; unfold Guard queue; rw [show line v (fun _=>Option.none) _=[] from (by generalize (List.ofFn id)=L; induction L with |nil=>rfl |cons i L IH=>unfold line; simp [IH])];rfl
lemma Guard.linear {k:ℕ} (s:ℝ){f g:Board b k→ℂ}(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g)(c:ℂ)(L:List (Fin b×ℕ)): Factors (port k) s L (f+g)= Factors (port k) s L f +Factors (port k) s L g ∧ Factors (port k) s L (c•f)= c • Factors (port k) s L f:=by
          induction L with
          | nil=> exact ⟨rfl,rfl⟩
          | cons l L ih =>
                         let T:= Factors (port k) s L
                         have hf':= Factors_smooth (port k) s L hf; have hg':= Factors_smooth (port k) s L hg; let p:=port k l.1
                         change ContDiff ℝ ∞ (T f) at hf'; change ContDiff ℝ ∞ (T g) at hg'
                         constructor
                         · change p.trim s l.2 (T _) = p.trim s l.2 (T f)+p.trim s l.2 (T g)
                           rw [(show T (f+g)=T f+T g from ih.1)]; funext x; change _= p.trim s l.2 _ _+p.trim s l.2 _ _
                           rw [p.trim_on s l.2 (show ContDiff ℝ ∞ (T f+T g) from hf'.add hg'),p.trim_on s l.2 hf',p.trim_on s l.2 hg']; exact diff_add (p.slice_smooth x hf') (p.slice_smooth x hg') _ _ _
                         change p.trim s l.2 (T _) = c • p.trim s l.2 (T f)
                         rw [(show T (c•f)=c •T f from ih.2)]; funext x; change _= c • p.trim s l.2 _ _
                         rw [p.trim_on s l.2 (show ContDiff ℝ ∞ (c • T f) from hf'.const_smul c),p.trim_on s l.2 hf']; exact diff_smul (p.slice_smooth x hf') _ _ _ _
end YM.MultipleContact.Panel.PairSet
