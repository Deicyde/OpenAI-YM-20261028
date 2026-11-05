import YM.RG08.Wax.Incidence
/-! # source-graded exponential relation and PDE with heat
 Proof without forming intermediate mark logs on any actual model. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Bands Analysis
open scoped Topology ContDiff BigOperators Matrix Classical
variable {X I Z:Type} [DecidableEq I][Fintype X][DecidableEq X]{M:Matrix X X ℝ}{U V:Op X}{k:ℕ}
abbrev Carn (I X:Type) := Topaz I (Op X)
-- CLM supporting expressions
lemma dop_nil (v:Op X): dancing 0 v=0:= by ext; simp [dancing]
lemma dop_right (v:Op X)(g:Z→Op X)(f:Finset Z): dancing (∑ i∈f,g i) v=∑ i∈f,dancing (g i) v:= by
   induction f using Finset.induction_on with
   | empty=>simp [dop_nil]
   | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,dance_plus,ih]
lemma dop_other (v:Op X)(g:Z→Op X)(f:Finset Z): dancing v (∑ i∈f,g i)=∑ i∈f,dancing v (g i):= by rw [dance_sym,dop_right]; exact sum_congr rfl fun _ _=> dance_sym ..
abbrev pearl (X:Type) : Op X:= fun n j=> if n+j=0 then 1 else 0
lemma dop_unit (V:Op X): dancing V (pearl X)=V:= by
  funext n j; rw [dancing,sum_eq_single (n,0),sum_eq_single (j,0),pearl,if_pos (by omega),mul_one]
  · intro p hp he
    have hz : p.2≠0:= by intro h; apply he; have hv:=mem_antidiagonal.mp hp; exact Prod.ext (by dsimp; omega) h
    rw [pearl,if_neg (by dsimp; omega),mul_zero]
  · simp [wheel]
  · intro p hp he
    have hz : p.2≠0 := by intro h; apply he; have ht:=mem_antidiagonal.mp hp; exact Prod.ext (by dsimp;omega) h
    exact sum_eq_zero (fun i _=>by rw [pearl,if_neg (by omega),mul_zero])
  simp [wheel]
lemma coda_z (K:Op X): countT (pearl X)=coda M K (pearl X) := by
   ext1 n; ext1 j; ext x; unfold coda landP rim countT; simp only [pearl,Pi.add_apply,Pi.smul_apply,if_neg (show ¬n+1+j=0 by omega),Pi.zero_apply,smul_zero,Finset.sum_apply]; -- wrong occurrence
   have hx (n i : ℕ)(x) : lap M (if n+i=0 then 1 else 0) x=0 := by split; exact congr_fun (lap_const M 1) x; exact congr_fun (lap_const M 0) x
   have hv (n j e i :ℕ)x : arch M (if n+j=0 then 1 else 0) (K e i) x=0:= by split <;> simp [arch,D]
   rw [hx]; simp_rw [hv]; simp

def jubilee : Carn I X → Carn I X → Carn I X:= festival dancing
local infixl:60 " ⋆ " => jubilee
lemma j_turn (v u:Carn I X): v ⋆ u= u ⋆ v:= by
   funext k; unfold jubilee festival; rw [partners_flip k (fun b:Finset I×Finset I=>dancing (v b.1) (u b.2))]; exact sum_congr rfl fun _ _=>dance_sym ..
lemma j_rise (v u t:Carn I X): v ⋆ u ⋆ t= v ⋆ (u ⋆ t):= by
   unfold jubilee festival; funext k; simp_rw [dop_right,dop_other,dance_rotate]; exact partners_3 k fun a b c=>dancing (v a) (dancing (u b) (t c))
lemma j_right (v u t:Carn I X): v ⋆ (u+t)= (v ⋆ u)+(v ⋆ t):= by funext k; simp only [jubilee,festival,Pi.add_apply,dance_add,sum_add_distrib]
lemma j_left (v u t:Carn I X): (v+u) ⋆ t= (v ⋆ t)+(u ⋆ t):= by rw [j_turn,j_right,j_turn v t,j_turn u t]
lemma j_less (v u t:Carn I X): v ⋆ (u-t)= (v ⋆ u)-(v ⋆ t):= by rw [eq_sub_iff_add_eq,← j_right, sub_add_cancel]
lemma j_beat (v u:Carn I X): sons (v ⋆ u)= (sons v ⋆ u)+(v ⋆ sons u):= by
   funext k; simp only [sons,jubilee,festival, Pi.add_apply,Finset.smul_sum,←sum_add_distrib]; refine sum_congr rfl fun b hb=>?_ ; rw [par_count hb,Nat.cast_add, add_smul,dance_price,dance_sym (v _) ((↑b.2.card:ℝ) • _),dance_price,dance_sym (u b.2)]
lemma j_ps (v u:Carn I X)(a:ℝ): (a • v) ⋆ u=a • (v ⋆ u):= by funext k; simp only [jubilee,festival,Pi.smul_apply,smul_sum,dance_price]
variable {f g k Z:Carn I X}{x:X→ℝ}
def action (F:Op X → Op X)(f:Carn I X) : Carn I X := fun n=>F (f n)
lemma fluid_sum {α:Type}{s:Finset α}{v:α→Op X}(h:∀ i∈s,Fluid (v i)): Fluid (∑ i∈s,v i):= by
   intro n j; rw [Finset.sum_apply, Finset.sum_apply,Finset.sum_fn]; exact ContDiff.sum fun i hi=> h i hi ..
lemma flu_z (g:Carn I X)(h:∀ p,Fluid (g p)) (p): Fluid (sons g p):= fun i j=> (h p i j).const_smul ((↑p.card):ℝ)
lemma sway_more {α:Type}{s:Finset α}{v:α→Op X}(h:∀ i∈s,Fluid (v i)): sway x (∑ i∈s,v i)=∑ i∈s,sway x (v i):= by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; ext; simp [sway,D]
   | insert i s hi ih=>
      have hp j hj:= h j (mem_insert_of_mem hj); have ht:=h i (mem_insert_self ..); rw [sum_insert hi,sum_insert hi,← ih hp]; exact funext fun i=> funext fun j=> Daddition x (ht i j) (fluid_sum hp i j)
lemma j_motion (x:X→ℝ)(h:∀ i, Fluid (f i))(hg:∀ i, Fluid (g i)) : action (sway x) (f ⋆ g)= (action (sway x) f ⋆ g)+(f ⋆ action (sway x) g):= by
  funext k; unfold jubilee festival action; rw [sway_more]; swap; · intro i _; exact dance_fluid (h _) (hg _)
  simp only [Pi.add_apply,← sum_add_distrib]; exact sum_congr rfl fun i _=> sway_dance _ (h _) (hg _)
lemma j_sway (x:X→ℝ)(h:∀ i,Fluid (f i)): action (sway x) (sons f)=sons (action (sway x) f):= funext fun i=>funext fun j=>funext fun k=> DscaleL x _ (h i j k)
lemma j_derive (hp:Bulb (pearl X) dancing f g)(hf:∀ i,Fluid (f i))(hg:∀ i,Fluid (g i))(x:X→ℝ): action (sway x) g=(action (sway x) f ⋆ g):= by
  have hz : sons g=sons f ⋆ g:=hp.2.2
  refine sons_one ?_ dop_nil (c:=f) ?_
  · unfold jubilee festival action; simp only [hp.2.1,par_once,sum_singleton,hp.1]; rw [dop_unit]; ext1 p; ext1 q; unfold sway pearl; split <;> ext i <;> simp [D]
  rw [← j_sway x hg,hz,j_motion x (flu_z f hf) hg,j_beat,j_sway x hf, hz]; change _=(sons f ⋆ action (sway x) g)-(sons f ⋆ (action (sway x) f ⋆ g)); rw [← j_rise (action (sway x) f),j_turn (action (sway x) f), j_rise]; abel
end YM.RG08.Wax
