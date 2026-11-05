import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.MergeProof.Pitch
import YM.MergeProof.Tally


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil 
variable {F:Config G n→Poly B}{t e d c A:ℝ}{o:V→Site n}
lemma Borne.sift {p:Support n}(h:Borne o p F t): Borne o p (fun U=>octave (F U)) t:=by
   refine ⟨fun U V hx hp=> congr_arg _ (h.home U V hx hp),fun g U=>congr_arg _ (h.turns g U),fun i=>?_,fun U i hi=>?_⟩
   · change Measurable (fun U=> if 2 ≤ i.val.card then _ else _); split; exact h.me _; exact measurable_const
   rcases lt_or_ge i.val.card 2 with hh|hh; exact starlet _ _ hh; rw [crest _ _ hh]; exact h.scope _ _ hi
lemma glaze_ne (U:Config G n) (h:octave (F U)≠0) : F U≠0:= fun ht=> h (by rw [ht]; ext i; rcases lt_or_ge i.val.card 2 with h|h; exact starlet _ _ h; exact crest _ _ h)
lemma Flow.sift {p:Box n}(h:Flow o p F t): Flow o p (fun U=>octave (F U)) t:=⟨h.toBorne.sift,fun U hu=>h.permits _ (glaze_ne _ hu)⟩
lemma Burns.sift {p:Support n}(h:Burns o p F t): Burns o p (fun U=>octave (F U)) t:=⟨h.toBorne.sift,fun U hu=>h.permits _ (glaze_ne _ hu),fun U=> hop B _ (octaves _)⟩
lemma Towed.sift {F:I→Y→ Poly B}{w:V→ℝ}{r:I→Support n}{M:ℕ}(h:Towed w r F M d A) : Towed w r (fun i U=>octave (F i U)) M d A:=by
   obtain ⟨a,ha,h,H⟩:=h; refine ⟨a,ha,h,fun i=>?_⟩
   obtain ⟨u,hu,hU,h⟩:= H i; refine ⟨u,hu,fun y v=>?_,h⟩
   by_cases ht:2 ≤ v.val.card; exact (by rw [crest _ _ ht]; exact hU _ _); rw [starlet _ _ (by omega),norm_zero]; exact hu _
lemma Towed.shrink {F:I→Y→Poly B}{w:V→ℝ}{r:I→Support n}{M:ℕ}(h:Towed w r F M d A)(hp:e ≤ d)(hc:A ≤ c)(he:∀ i,0<w i) : Towed w r F M e c:=by
   obtain ⟨v,hv,h,H⟩:=h; have hw i : 0 ≤ v i:= (H i|>.fares he).1; refine ⟨v,hv,fun i=> Extra.Multi.Budget.mono (h i) (fun i=>?_) (fun j=> ?_) hc,H⟩
   · split; exact mul_nonneg (hw _) (Real.exp_pos _).le;rfl
   split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (hw _); rfl
-- any packing economics. e' can be below zero. γ→ cut
variable {w w':V→ℝ}{M:ℕ}
def Repegs (o:V→Site n)(M:ℕ)(w w':V→ℝ)(e c:ℝ) (B:Census V) := ∀ i:B.Mode, 2 ≤ i.val.card → ∀ p:Support n,i.val.image o ⊆ p → Poly.toll w' i ≤ c*Poly.toll w i * Real.exp (e*coverNumber M p)
lemma Towed.peg {F:I→Config G n→Poly B}{r:I→Support n}(h:Towed w r F M (d+e) A)(H:∀ i,Borne o (r i) (F i) t)(ht:∀ i U,rises (F i U))(hp:Repegs o M w w' e c B)(hx:∀ i,0<w i)(hX:∀ i,0<w' i)(hc:0≤c): Towed w' r F M d (c*A):=by
   obtain ⟨a,ha,h,hB⟩:=h
   let Z i:= if (r i).Nonempty then Real.exp (e*coverNumber M (r i)) else Real.exp (e*coverNumber M (r i)) -- even ∅. n finite pays summability via finite patterns. flag closure.
   let f i:= c*Real.exp (e*coverNumber M (r i))*a i
   have hh(i):0 ≤ a i:= (hB i|>.fares hx).1
   have hf: Summable f:= by
      obtain ⟨m,hi,hM⟩:= Finset.exists_max_image (univ:Finset (Support n)) (fun X=> Real.exp (e*coverNumber M X)*c) Finset.univ_nonempty
      refine (ha.mul_left (Real.exp (e*coverNumber M m)*c)).of_nonneg_of_le (fun i=> mul_nonneg (mul_nonneg hc (Real.exp_pos _).le) (hh _)) (fun i=> mul_le_mul_of_nonneg_right ((mul_comm ..).trans_le (hM (r i) (Finset.mem_univ _))) (hh _))
   refine ⟨f,hf,fun x=>?_,fun i=> ?_⟩
   · convert! Extra.Multi.Budget.scale (h x) hc using 1; ext i; unfold f; split_ifs; simp only [add_mul,Real.exp_add]; ring; rw [mul_zero]
   obtain ⟨u,h,hp',hv⟩:= hB i
   let α (j:B.Mode):= 2 ≤ j.val.card ∧ j.val.image o ⊆ r i
   let b (j:B.Mode):= if α j then u j else 0
   have hb(i):0 ≤ b i:=by unfold b;split;exact h _; rfl
   refine ⟨b,hb,fun U j=> by unfold b; split; exact hp' U j; next he=>rw [show (F i U).part j=0 from Classical.byContradiction (fun h=> he ⟨ht i U j h,(H i).place _ _ h⟩),norm_zero],?_⟩
   let P:= c*Real.exp (e*coverNumber M (r i)); have ht':0 ≤ P:=mul_nonneg hc (Real.exp_pos _).le
   refine le_trans ?_ (mul_le_mul_of_nonneg_left hv ht'); unfold wordsPrice; rw [Finset.mul_sum]; refine sum_le_sum fun j _=>?_ ; unfold b
   split
   next hh=> rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((hp j hh.1 (r i) hh.2).trans_eq (by ring)) (h j)
   rw [mul_zero]; exact mul_nonneg ht' (mul_nonneg (Poly.worth hx j).le (h j))
end YM.MergeProof.Accent
