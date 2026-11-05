import YM.RG08.Wax.Festival
/-! # Euler-Poll analytic equation for square-free log avoids graphs. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Bands Analysis
open scoped Topology ContDiff BigOperators Matrix
variable {X I Z:Type} [DecidableEq I] [Fintype X][DecidableEq X] (M:Matrix X X ℝ) {U V:Op X}{k:ℕ}{a b:Carn I X}
local infixl:60 " ⋆ " => jubilee
abbrev cyclone:=coda M
abbrev rust:=action (I:=I) (X:=X) countT
def archs (U V:Carn I X): Carn I X:= festival (rim M) U V

lemma archs_split (a b:Carn I X) : archs M a b=∑ i, ∑ j, M i j • (action (sway (zpk i)) a ⋆ action (sway (zpk j)) b):= by
   funext k; unfold archs festival; simp_rw [rimD,Finset.sum_apply,Pi.smul_apply]; rw [sum_comm]; refine sum_congr rfl fun i _=> ?_
   rw [sum_comm]; unfold jubilee festival action; simp only [smul_sum]
-- avoid using j_count if shadow
lemma j_inters {Z:Type}(s:Finset Z)(f:Z→Carn I X)(v:Carn I X): (∑ i ∈ s,f i) ⋆ v=∑ i∈s,(f i ⋆ v):= by
   funext x; unfold jubilee festival; simp_rw [Finset.sum_apply,dop_right]; exact sum_comm
lemma arch_cond (hp:Bulb (pearl X) dancing a b)(hf:∀ i,Fluid (a i))(hg:∀ i,Fluid (b i))(H:Carn I X) : archs M H b= archs M H a ⋆ b:= by
   rw [archs_split,archs_split]; simp_rw [j_derive hp hf hg,j_inters,j_ps, ← j_rise]
lemma rim_scale (F H:Op X)(x:ℝ)(h:Fluid F) : rim M (x • F) H=x • rim M F H:=by
   have hp i : sway i (x • F)=x • sway i F:= funext fun k=> funext fun j=> DscaleL i x (h _ _)
   simp only [rimD,hp,dance_price, Finset.smul_sum]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>smul_comm ..
lemma arch_count (F:Carn I X)(hp : Mᵀ=M)(h:∀ i, Fluid (F i)) : sons ((1/2:ℝ) • archs M F F)= archs M (sons F) F:= by
   let A:= archs M (sons F) F
   have hH : sons (archs M F F) = A+A:= by
     funext k
     have hx (p)(hx:p∈partners k): (k.card:ℝ) • rim M (F p.1) (F p.2) = rim M (sons F p.1) (F p.2)+rim M (sons F p.2) (F p.1) := by
        rw [par_count hx,Nat.cast_add,add_smul,duo_exchange (sons F p.2) _ hp]; unfold sons; rw [rim_scale M _ _ _ (h p.1),duo_exchange (F p.1) (_ • _) hp,rim_scale M _ _ _ (h p.2),duo_exchange (F p.2) (F p.1) hp]
     rw [sons,archs,festival,smul_sum]; calc
       _ = A k+ ∑ p ∈ partners k,rim M (sons F p.2) (F p.1):= (sum_congr rfl hx).trans (sum_add_distrib)
       _ = _ := by rw [show (∑ p ∈ _, _)= A k from (partners_flip k (fun p=> rim M (sons F p.1) (F p.2))).symm]; rfl
   funext k; refine Eq.trans (smul_comm (k.card:ℝ) (1/2:ℝ) (archs M F F k)) ?_; rw [show (k.card:ℝ) • (archs M F F k)=(A+A) k from congr_fun hH k,Pi.add_apply, ← two_smul ℝ, smul_smul]; simp; rfl
lemma coda_rinse (S:Op X)(hp:Mᵀ=M)(hf:∀ i,Fluid (a i))(hg:∀ i,Fluid (b i)): action (coda M S) (a ⋆ b) = (action (coda M S) a ⋆ b)+(a ⋆ action (coda M S) b)+archs M a b:= by
   have he (f:Finset I × Finset I→Op X)(s:Finset (Finset I × Finset I))(hs:∀ i∈s,Fluid (f i)): coda M S (∑ i∈s,f i)=∑ i∈s,coda M S (f i) := by
     induction s using Finset.induction_on with
     | empty=> simp only [sum_empty]; ext1 n; ext1 j; simp only [coda,landP,rim, Pi.add_apply]; change lap M (fun _=>0)+ _ = _; rw [lap_const M,zero_add]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; ext x; simp [arch,D]
     | insert i s hi ih=>
       have ht j hj:= hs j (mem_insert_of_mem hj); rw [sum_insert hi,sum_insert hi,coda_more M S (hs i (mem_insert_self ..)) (fluid_sum ht),ih ht]
   funext t; unfold jubilee action archs festival; rw [he]; swap; · exact fun i _=> dance_fluid (hf _) (hg _)
   simp only [Pi.add_apply,← sum_add_distrib]; exact sum_congr rfl fun i _=> coda_wash hp (hf _) (hg _) S
lemma coda_pulse (S:Op X)(h:∀ i,Fluid (a i)) : sons (action (coda M S) a)=action (coda M S) (sons a):=by
   funext i; let b:ℝ:=i.card; let V:=a i
   change b • (landP M V+rim M V S) = landP M (b • V)+rim M (b • V) S
   rw [smul_add,rim_scale M _ _ _ (h i),show landP M (b • V)= _ from funext (fun n=>funext fun j=>?_)]; exact lap_scale M (h i _ _) _
lemma rust_prune (b:Carn I X): sons (rust b)=rust (sons b):= by
   funext i n j; exact smul_comm (i.card:ℝ) (n+1) _
lemma rust_precise (a b:Carn I X): rust (a ⋆ b)= (rust a ⋆ b)+(a ⋆ rust b):= by
   funext s; unfold jubilee rust action festival
   have he (f:Finset I × Finset I→Op X)(s:Finset (Finset I × Finset I)): countT (∑ i∈s,f i)=∑ i∈s,countT (f i):= by
     funext n j; simp_rw [countT,Finset.sum_apply, Finset.smul_sum]; rfl
   rw [he,Pi.add_apply,← sum_add_distrib]; exact sum_congr rfl fun i _=> countTn ..
lemma timed_mark (S:Op X)(hx:Mᵀ=M)(hp:Bulb (pearl X) dancing a b) (hf:∀ i,Fluid (a i))(hg:∀ i,Fluid (b i)) (h:rust a=action (coda M S) a + (1/2:ℝ) • archs M a a): rust b=action (coda M S) b:=by
   have hb : sons b=sons a ⋆ b:=hp.2.2
   refine sons_one ?_ dop_nil (c:=a) ?_
   · change countT (b ∅)=coda M S (b ∅); rw [hp.2.1,coda_z]
   change _=(sons a ⋆ rust b)-(sons a ⋆ action (coda M S) b)
   rw [rust_prune,coda_pulse M _ hg,hb,coda_rinse M _ hx (flu_z a hf) hg,rust_precise,← rust_prune,h,sons_add,coda_pulse M _ hf,arch_count M _ hx hf,j_left,arch_cond M hp hf hg]; abel
end YM.RG08.Wax
