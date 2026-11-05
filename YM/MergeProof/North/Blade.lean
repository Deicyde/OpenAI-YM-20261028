import YM.MergeProof.Domino
import YM.MergeProof.North.Amber
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory
open scoped Topology BigOperators Classical
variable {ι β:Type}{G:Gauge}{n c:Side}{R:Rep G n}{κ e t z a:ℝ} {o:Site n}
local notation "L"=> Config G n→ℂ
-- tracked unit at B key (canonical P grown, remains constant during off)
structure Saber [Fintype ι](o:Site n)(M:ι→ Leaf R)(s:ι→ℂ)(g: L)(K: Res G n)(p:ℂ)(a:ℝ):Prop where
   sit i: o∈ (M i).crest
   lit : g=(fun _=>p)+∑ i,s i • prose (M i)
   run : K=∑ i,s i • entry (M i)
   pay : ∑ i,‖s i‖* load (M i) ≤ a

def Blade (R:Rep G n)(o:Site n)(g:L)(K:Res G n)(p:ℂ)(a:ℝ): Prop:=∃ (ι:Type) (_: Fintype ι) (M:ι→ Leaf R) (s:ι→ℂ), Saber o M s g K p a
section tips
variable [Fintype ι]{M:ι→ Leaf R}{s:ι→ℂ}{g:Config G n→ℂ}{K: ℕ→ Config G n→ℂ}{u:ℂ} {P: Res G n}
namespace Saber
variable (h:Saber o M s g P u a)
include h
lemma suffice : Blade R o g P u a:= ⟨ι,inferInstance,M,s,h⟩
lemma swap_weight (v:ℂ): Saber o M (v • s) (v • g) (v • P) (v*u) (‖v‖*a):=by
   refine ⟨h.sit,by rw [h.lit,smul_add,Finset.smul_sum];simp_rw [Pi.smul_apply, smul_eq_mul, smul_smul];rfl,by rw [h.run,Finset.smul_sum];simp_rw [Pi.smul_apply, smul_eq_mul, smul_smul],?_⟩
   simp_rw [Pi.smul_apply, norm_smul,mul_assoc, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h.pay (norm_nonneg _)
lemma alongside [Fintype β]{N:β→Leaf R}{p:β→ℂ}{F':L}{q:Res G n}{w:ℂ} (ht:Saber o N p F' q w t): Saber o (Sum.elim M N) (Sum.elim s p) (g+F') (P+q) (u+w) (a+t):=by
   refine ⟨fun i=>match i with|.inl i=>h.sit i|.inr i=>ht.sit i,by rw [h.lit,ht.lit,Fintype.sum_sum_type,add_add_add_comm];rfl, by rw [h.run,ht.run,Fintype.sum_sum_type];rfl,(by rw [Fintype.sum_sum_type]; exact add_le_add h.pay ht.pay)⟩
lemma receipt (w:ℝ)(hw:a≤w): Blade R o g P u w:=⟨ι,inferInstance,M,s,{h with pay:=h.pay.trans hw}⟩ -- rm extra
end Saber
lemma Saber.display (h:Saber o M s g (profile R.activities K) u a)(hr:R.activities.Valid R.p t e)(hq:Dominated K): coin R g K=u • (Complex.ofReal ∘ R.eval) + ∑ i,s i • (Complex.ofReal ∘ (M i).cicada):=by
   let q(i):=s i • line (M i); have hj i:Dominated (q i):=rainbow (linemark _) _
   have hx :profile R.activities K=profile R.activities (0+∑ i,q i):=by rw [zero_add,prof_sum q hj,h.run]; simp_rw [q,profile_scale,banner]
   rw [coin_port R g hq (combn pawn0 (combies q hj _)) hx hr,h.lit,coin_plus _ _ _ pawn0 (combies q hj _) hr.boundK,coin_sum q _ hj _ hr.boundK]; simp_rw [q,coin_mul,coin_leaf]
   congr 1; funext i; rw [coin₀]; exact mul_comm ..
lemma Saber.to_tale {E:Rep G c}{D: GaugeDoor R E} {P: Res G n}(h:Saber o M s g P u a)(b:Site c)(K': Res G c) (hp:K'=∑ i,s i • quoted D (M i)): Tale (fun i=>i∈ Set.range (fun i=>(M i).turn)) o b 1 g P K' u a 0 D:=by
   refine Odyssey.tale (M:=M) (s:=s) (ψ:=0) ?_; refine ⟨fun i=>⟨h.sit i,⟨i,rfl⟩⟩,⟨fun i=> mul_nonneg (norm_nonneg _) ((M i).profit.trans ((R.p).loMass _ _ (M i).profit)),Summable.of_finite,by rw [tsum_fintype]; exact h.pay⟩,Attainment.blank _,fun U=>?_,fun p U=>?_,fun j U=>?_⟩
   · rw [h.lit]; simpa [Finset.sum_apply] using! hasSum_fintype (fun i=>s i *prose (M i) U)
   · rw [h.run]; simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using! hasSum_fintype (fun i=>s i*entry (M i) p U)
   rw [hp]; simpa [hook,Finset.sum_apply] using! hasSum_fintype (fun i=>s i*quoted D (M i) j U)
end tips
variable {g f:Config G n→ℂ} {P W:Res G n}{u v:ℂ}
lemma blade₀ (h:0 ≤ a): Blade R o (fun _=>u) 0 u a:=by
   refine ⟨Empty,inferInstance,Empty.elim,Empty.elim,⟨fun i=>i.elim,?_,?_,?_⟩⟩ <;> simp [h]
lemma Blade.comp (h:Blade R o g P u a)(hf:Blade R o f W v t):Blade R o (g+f) (P+W) (u+v) (a+t):=by
   obtain ⟨I,i,M,s,h⟩:=h; obtain ⟨J,j,K,w,hf⟩:=hf; exact (h.alongside hf).suffice
lemma Blade.rate (h:Blade R o g P u a)(x:ℂ):Blade R o (x • g) (x • P) (x*u) (‖x‖*a):=by obtain ⟨J,j,M,s,h⟩:=h; exact (h.swap_weight x).suffice
lemma Blade.more (h:Blade R o g P u a)(hp:a≤e):Blade R o g P u e:=by obtain ⟨J,j,M,s,h⟩:=h; exact (h.receipt _ hp)
lemma comp_many (F:ι→ L)(W:ι→ Res G n)(u:ι→ℂ)(C:ι→ℝ)(p:Finset ι)(h:∀ i∈p, Blade R o (F i) (W i) (u i) (C i)): Blade R o (∑ i∈p,F i) (∑ i∈p,W i) (∑ i∈p,u i) (∑ i∈p,C i):=by induction p using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact blade₀ le_rfl
   | @insert i s hi IH=> simp_rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).comp (IH (fun j hj=>h j (mem_insert_of_mem hj)))
-- live leaf
lemma bristle (M:Leaf R)(ho:o∈M.crest):Blade R o (prose M) (entry M) 0 (load M):= by
   refine ⟨Unit,inferInstance,fun _=>M,fun _=>1,⟨fun _=>ho,by simp; rfl,by simp,by simp⟩⟩
end YM.MergeProof.Float
