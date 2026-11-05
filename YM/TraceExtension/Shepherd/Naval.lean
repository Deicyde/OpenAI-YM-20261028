import YM.TraceExtension.Shepherd.Earner
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side} (x:V→Site n) (d:V→Step) (ν:G.El→ G.El)(S:Finset V)(v: Rain V G) (U:Config G n)
abbrev settles (i:V): Edge (Site n):= (d i).used (x i)
def flotilla (k:Edge (Site n)): G.El:=if h: ∃ i∈ S, settles x d i=k then stunt (x h.choose) (d h.choose) ν U (v h.choose) k else U k
def longC (x:V→ Site n) (d:V→ Step)(ν:G.El→ G.El)(S:Finset V)(v : Rain V G)(U:Config G n):Config G n:=fun k=> flotilla x d ν S v U k
variable (h:Injective (settles x d))
include h
lemma attuned (i:V)(hi:i∈S): longC x d ν S v U (settles x d i)= stunt (x i) (d i) ν U (v i) (settles x d i):=by
   unfold longC flotilla; split
   next he=> rw [h he.choose_spec.2]
   next he=> exact False.elim (he ⟨i,hi,rfl⟩)
lemma stilt_blank (s:Finset V)(v:Rain V G)(i:V)(hi:i∉s): longC x d ν s v U (settles x d i)=U (settles x d i):= dif_neg (by rintro ⟨u,hu,hv⟩; exact hi (h hv ▸ hu))
lemma singZ : longC x d ν ∅ v U=U:=by funext i; unfold longC flotilla; simp
lemma budge (i:V)(hi:i∉S): longC x d ν (insert i S) v U= stunt (x i) (d i) ν (longC x d ν S v U) (v i):=by
    funext k; by_cases hx:k=settles x d i
    · subst k; rw[attuned x d ν _ v U h i (mem_insert_self ..)]; unfold stunt StressFlux.modify; rw [stilt_blank x d ν U h S v i hi]
    rw [show stunt (x i) (d i) ν (longC x d ν S v U) (v i) k= _ from if_neg hx]; by_cases ht:∃ j∈S,settles x d j=k
    · obtain ⟨j,hj,rfl⟩:=ht; rw [attuned x d ν _ v U h j hj,attuned x d ν _ v U h j (mem_insert_of_mem hj)]
    unfold longC flotilla; rw [dif_neg ht,dif_neg (by rintro ⟨j,hj,hk⟩; rcases mem_insert.mp hj with hj|hj; subst j; exact hx hk.symm; exact ht ⟨j,hj,hk⟩)]
lemma offZ (P: Support n)(H:∀ i∈S,x i∉P): Agrees P U (longC x d ν S v U):=by
    induction S using Finset.induction with
    | empty=> rw[singZ x d ν v U h]; intro _ _ _;rfl
    | insert i s hi IH=>
        rw[budge x d ν s v U h i hi]; have hu:= IH fun i hi=> H _ (mem_insert_of_mem hi); intro k hk hk'; exact (hu k hk hk').trans (modify_off (x i) (d i) _ P _ (H i (mem_insert_self ..)) _ hk hk')
lemma notes (P:Support n)(W:Config G n)(hv:Agrees P U W): Agrees P (longC x d ν S v U) (longC x d ν S v W):=by
    induction S using Finset.induction with
    | empty=> rw[singZ x d ν v U h,singZ x d ν v W h]; exact hv
    | insert i s hi IH=>
        rw[budge x d ν s v U h i hi,budge x d ν s v W h i hi]; exact modify_local _ _ _ _ IH
lemma village (P:Support n)(T:Finset V)(ht:T⊆S)(hs:∀ i∈S,x i∈P→i∈T): Agrees P (longC x d ν S v U) (longC x d ν T v U):=by
    induction S using Finset.induction generalizing T with
    | empty =>rw [Finset.subset_empty.mp ht];exact fun _ _ _=>rfl
    | insert i s hi IH=>
        rw[budge x d ν s v U h i hi]; by_cases H:i∈T
        · let p:=T.erase i; have hy : p⊆ s:=by intro x hx; exact (mem_insert.mp (ht (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
          have hP : longC x d ν T v U= stunt (x i) (d i) ν (longC x d ν p v U) (v i):=by nth_rw 1 [← insert_erase H]; exact budge _ _ _ _ v U h _ (notMem_erase i T)
          rw[hP]; exact modify_local _ _ _ _ (IH p hy (fun j hj hx=>mem_erase.mpr ⟨ne_of_mem_of_not_mem hj hi,hs j (mem_insert_of_mem hj) hx⟩))
        intro k hk hK
        have he : T⊆s:=fun i' hI=>(mem_insert.mp (ht hI)).resolve_left (fun he=> H (he ▸ hI)); refine Eq.trans (modify_off _ _ _ P _ (fun hh=> H (hs i (mem_insert_self ..) hh)) k hk hK).symm (IH T he (fun j hj hx=> hs j (mem_insert_of_mem hj) hx) k hk hK)
lemma whirlM (hb:Measurable ν): Measurable (uncurry (longC x d ν S)):=by
    induction S using Finset.induction with
    | empty=> have ht: uncurry (longC x d ν ∅)=(Prod.snd (α:=Rain V G) (β:=Config G n)):= funext fun ⟨p,U⟩=> singZ x d ν p U h
              rw [ht]; exact measurable_snd
    | insert i s hi IH=>
        let f:= uncurry (longC x d ν s); let g(k:Rain V G × Config G n):= (ν (k.1 i),f k); have he: uncurry (longC x d ν (insert i s))= (fun k:G.El × Config G n=> StressFlux.modify (x i) (d i) k.1 k.2) ∘ g:= funext fun ⟨p,U⟩=> budge x d ν s p U h i hi
        rw [he]; exact (flowA _ _).comp ((hb.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk IH)
lemma whirlK : MeasurePreserving (longC x d ν S v) (prior G n) (prior G n):=by
    induction S using Finset.induction with
    | empty=>rw[show longC x d ν ∅ v=id from funext fun U=> singZ _ _ _ _ _ h]; exact MeasurePreserving.id _
    | insert i s hi IH=> rw[show longC x d ν (insert i s) v= StressFlux.modify (x i) (d i) (ν (v i)) ∘ longC x d ν s v from funext fun U=> budge _ _ _ _ v U h i hi]; exact (prior_modify ..).comp IH
lemma whirlG (g:Site n→G.El)(hv:∀ x y:G.El,ν (x*y)=x*ν y*x⁻¹): longC x d ν S ((g ∘ x)*v) (Lattice.gauge g U)= Lattice.gauge g (longC x d ν S v U):=by
    induction S using Finset.induction with
    | empty=> rw [singZ x d ν _ _ h,singZ _ _ _ _ _ h]
    | insert i s hi IH=> rw [budge x d ν _ _ _ h i hi,budge x d ν _ v U h i hi, IH]; unfold stunt; rw[modify_g,Pi.mul_apply,hv]; rfl
lemma readsZ (v' : Rain V G)(hr:∀ i∈S,v i=v' i): longC x d ν S v U = longC x d ν S v' U:=by
   funext i; unfold longC flotilla; split
   next he=>rw [hr _ he.choose_spec.1]
   next he=>rfl
end YM.Trace.Shepherd
