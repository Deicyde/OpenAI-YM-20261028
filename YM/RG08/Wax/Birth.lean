import YM.RG08.Wax.Banner
/-! # Pure REAL coordinate surgery for groups of tags at any origins
 prior to evaluation. All iteration on proper disjoint groups.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Bands Analysis Laurent Lattice Bloch Next.Free
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I X:Type} [DecidableEq I] [Fintype X] [DecidableEq X] {L: Side} {p : Option Side}{K:Bloch.Row X X}{S:Canticle X}
variable {a:I→ℕ}{U:Topaz I (HeatS X)}{o:Site L} -- convolution log

-- conditioned mass $Coda$
def arches (p:Option Side)(K:Bloch.Row X X) : Topaz I (HeatS X)→ Topaz I (HeatS X) → Topaz I (HeatS X):= festival (thunder p K)
def lever (p:Option Side)(K:Bloch.Row X X)(S:Canticle X)(U:Topaz I (HeatS X))(T:Finset I) : HeatS X:= pumpP p K S (U T) + (1/2:ℝ) • arches p K U U T
lemma mountedL (h:∀ t,Reels (vanes a t) (U t))(hk:Whole K)(hp:Gets S)(t): Reels (vanes a t) (lever p K S U t) := by
   refine Reels.more (Reels.more (reeling_peels (p:=p) (h t) hk) (reeling_choir (p:=p) hk hp (h t))) (Reels.sm ?_ _); apply reels_sum; intro i hi; rw [wind_cell a _ hi]; exact thunder_r (h _) (h _) hk

def stageBox (U:Topaz I (HeatS X))(n:ℕ): Topaz I (HeatS X):= fun t i=> if i≤n then U t i else 0
-- uses ALL MEM≤n, could use Rec. 
lemma lever_needs {U V : Topaz I (HeatS X)} (t:Finset I)(n:ℕ)(h:∀ t i,i≤n → U t i=V t i): lever p K S U t n=lever p K S V t n:= by
   unfold lever pumpP arches festival
   simp only [Pi.add_apply,Pi.smul_apply]; refine congr_arg₂ (·+·) (congr_arg₂ (·+·) ?_ ?_) (congr_arg ((1/2:ℝ) • ·) ?_)
   · funext i j; unfold peels; rw [h _ _ le_rfl]
   · funext i; unfold choirR; refine sum_congr rfl fun i hi=> sum_congr rfl fun j _=> ?_; rw [h _ _ (by have hu:=mem_antidiagonal.mp hi; omega)]
   rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl fun i hi=>?_ ; funext j; unfold thunder; refine sum_congr rfl fun m hm=> ?_; have hu:=mem_antidiagonal.mp hm; rw [h _ _ (by omega),h _ _ (by omega)]

def pulse (p:Option Side)(K:Bloch.Row X X)(S:Canticle X)(F:Topaz I (Screed ℝ X))(t:Finset I)(n:ℕ) : Screed ℝ X := match n with
   | 0=> F t
   | n+1=> ((↑(n+1:ℕ)):ℝ)⁻¹ • lever p K S (fun t i=> if h:i≤ n then pulse p K S F t i else 0) t n
termination_by n
lemma pulse_z (F:Topaz I (Screed ℝ X))(T): pulse p K S F T 0=F T:= by rw [pulse]
lemma pulse_up (F:Topaz I (Screed ℝ X))(T)(n:ℕ): pulse p K S F T (n+1)=((↑(n+1:ℕ)):ℝ)⁻¹ • lever p K S (pulse p K S F) T n:= by rw [pulse,lever_needs (U:=_) (V:=pulse p K S F) T n (fun t i hi=>dif_pos hi)]
lemma pulse_ok (F:Topaz I (Screed ℝ X))(hk:Whole K)(he:Gets S)(hx:∀ t,Sails (vanes a t) (F t)) (t): Reels (vanes a t) (pulse p K S F t):= by
  intro i; induction i using Nat.caseStrongRecOn generalizing t with
  | zero=> rw [pulse_z]; exact hx t
  | ind n ih=> rw [pulse]; apply Loomed.fresh; apply mountedL _ hk he t
               intro t i; dsimp only; by_cases h:i≤n; · rw [dif_pos h]; exact ih i h t
               rw [dif_neg h]; exact swung fun j=> Loomed.zero
lemma tip_paid (F:Topaz I (Screed ℝ X))(T): ticks (pulse p K S F T)=lever p K S (pulse p K S F) T:= by
    ext1 n; ext1 i; unfold ticks; rw [pulse_up, Pi.smul_apply, smul_inv_smul₀]; positivity

-- Ensure EMPTYLog shadow. needs no tribute rank. Series at 0 mark empty persistence; F0=0 required.
lemma lever_void {U:Topaz I (HeatS X)}(hp:Whole K)(he:Gets S)(hx: U ∅=0): lever p K S U ∅=0 := by
   unfold lever pumpP arches festival; simp only [hx,par_once,sum_singleton]; ext1 n; ext1 i; ext1 j
   change ((peels p K (0: HeatS X) n i j)+(choirR p K S (0:HeatS X) n i j))+(1/2:ℝ) • thunder p K (0:HeatS X) 0 n i j=0
   unfold peels choirR thunder Quire.hymn grail; simp_rw [Finset.sum_apply,Pi.zero_apply,jib_blank _ hp,count_zero, grant_zero,sum_const_zero]
   simp_rw [show ∀ a b c t,clasp K (0:Rooted ℝ X (a+1)) (Refrain K S p b c (t+1))=0 from fun a b c t=> clasp_zero (refrains_tune hp (fun i j=>(he.2 i j).1) p ..|>.1) hp,grant_zero,sum_const_zero]; simp
lemma pulse_void (F:Topaz I (Screed ℝ X))(hk:Whole K)(he:Gets S)(hx:F ∅=0): pulse p K S F ∅=0:= by
  funext i; induction i using Nat.caseStrongRecOn with
  | zero=> rw [pulse,hx]; rfl
  | ind n ih=>
    rw [pulse]; let U t i:= if h:i≤n then pulse p K S F t i else 0
    have ha : U ∅=0:= by
       funext i; unfold U; split; next hi=> exact ih i hi
       rfl
    change _ • (lever p K S U _ n)=_; rw [lever_void hk he ha, Pi.zero_apply,smul_zero]; rfl
lemma glee_list {V:I→HeatS X}{t:ℕ} (s:Finset I)(h:∀ i∈s,Reels t (V i))(o:Site L): glee t o (∑ i∈s,V i)=∑ i∈s,glee t o (V i):= by
    induction s using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; funext a b; unfold glee large; simp
    | insert i s hi ih=> have hx j hj:= h j (mem_insert_of_mem hj); rw [sum_insert hi,sum_insert hi,glee_m (h _ (mem_insert_self ..)) (reels_sum hx),ih hx]
lemma glee_sm {T:HeatS X}{t:ℕ}(c:ℝ)(h:Reels t T)(o:Site L): glee t o (c • T)=c • glee t o T:= by
    funext n j; unfold glee large; simp only [Pi.smul_apply,smul_sum]; exact sum_congr rfl fun i _=> root_scale _ ((h n).tide j i|>.pens) _
lemma lever_attain (h:∀ t,Reels (vanes a t) (U t))(hk:Whole K)(he:Gets S)(o:Site L) :
    let V t:= glee (vanes a t) o (U t)
    (fun t=>glee (vanes a t) o (lever (some L) K S U t))= action (coda (K.acts L) (Beats K S L)) V + (1/2:ℝ) • archs (K.acts L) V V := by
   intro V; funext t; let P:= some L
   have hx i (hi:i∈partners t): Reels (vanes a t) (thunder P K (U i.1) (U i.2)):= by rw [wind_cell a i hi]; exact thunder_r (h _) (h _) hk
   unfold P at hx
   rw [lever,pumpP, arches, festival,glee_m (V:=(1/2:ℝ) • ∑ i ∈ partners t,thunder (some L) K (U i.1) (U i.2)) (show Reels _ _ from Reels.more (reeling_peels (p:=some L) (h t) hk) (reeling_choir hk he (h t))) (Reels.sm (reels_sum hx) _),glee_sm _ (reels_sum hx),glee_m (reeling_peels (p:=some L) (h t) hk) (reeling_choir (p:=some L) hk he (h t)), peelsD (h t) hk, choirD (h t) hk he, Pi.add_apply]
   congr 1; change (1/2:ℝ) • glee _ _ (_)= (1/2:ℝ) • _; apply congr_arg; rw [glee_list _ hx]; unfold archs festival; refine sum_congr rfl fun i hi=>?_; rw [wind_cell a _ hi]; exact tempo_h (h _) (h _) hk _
end YM.RG08.Wax
