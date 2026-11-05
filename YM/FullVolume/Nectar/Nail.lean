import YM.FullVolume.Sym.Snippet
import YM.MergeProof.SwitchCost
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
/-!
# Interpolation in the insertion fibres

Degree counted in *slots*, not in polymer powers nor in number of ingredients. No Lebesgue constant here depends on volume, on the size of a molecule or on the number of heads.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function MeasureTheory Finset Polynomial PhysicalNext.Repeat.Jams
open scoped Topology BigOperators Classical ENNReal
variable {k i:ℕ}
def Nail (k:ℕ) (f:sun→ℝ) := ∃ g:ℝ→ℝ, ink k g ∧ ∀ t:sun,f t=g t.val
namespace Nail
variable {a b:ℝ}{f g:sun→ℝ}
lemma const (c:ℝ): Nail k (fun _=>c):=⟨_,ink.termC c,fun _=>rfl⟩
lemma straight (a b:ℝ): Nail 1 (fun t=>a+b*t.val):= ⟨_,ink.straight a b,fun _=>rfl⟩
lemma raise (h : Nail i f)(he:i≤k):Nail k f:= ⟨_,h.choose_spec.1.rise he,h.choose_spec.2⟩
lemma add (h : Nail k f) (hz:Nail k g): Nail k (fun x=>f x+g x):=⟨_,ink.abreast h.choose_spec.1 hz.choose_spec.1,fun t=> congr_arg₂ (·+·) (h.choose_spec.2 t) (hz.choose_spec.2 t)⟩
lemma star (h:Nail k f)(hx:Nail i g): Nail (k+i) (fun x=> f x*g x):=⟨_,ink.docket h.choose_spec.1 hx.choose_spec.1,fun t=> congr_arg₂ (·*·) (h.choose_spec.2 t) (hx.choose_spec.2 t)⟩
lemma mul_left (h:Nail k f)(a:ℝ):Nail k (fun x=>a*f x):=by simpa only [Nat.zero_add] using (const (k:=0) a).star h
lemma mul_right(h:Nail k f)(a:ℝ):Nail k (fun x=>f x*a):= h.star (const (k:=0) a)
lemma net {ι:Type*}(s:Finset ι)(F:ι→sun→ℝ)(h:∀ i∈s,Nail k (F i)): Nail k (fun t=>∑ i∈s,F i t):=by
   induction s using Finset.induction_on with
   | empty=> simpa using const (k:=k) 0
   | insert i s hi ih => simp_rw [sum_insert hi]; exact add (h _ (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma all {ι:Type*}(s:Finset ι)(f:ι→sun→ℝ)(k:ι→ℕ)(h:∀ i∈s,Nail (k i) (f i)):Nail (∑ i∈s,k i) (fun x=> ∏ i∈s,f i x):=by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty,prod_empty]; exact const 1
   | insert i s hi ih=> simp_rw [sum_insert hi,prod_insert hi];exact star (h _ (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
abbrev title (k:ℕ):= gloss k (sampleP k)
lemma axis (h:Nail k f)(x:sun): f x=∑ i,f (sampleP k i)*title k i x:=by
   obtain ⟨g,h',he⟩:=h; simp_rw [he]; exact ink.tour _ h' (Subtype.val_injective.comp (samples_in _)) _
lemma park (i:Fin (k+1)): Nail k (title k i):= by
   let v(x):=(sampleP k x).val; let s:= (Finset.univ (α:=Fin (k+1)))
   let h:= Lagrange.natDegree_basis (Subtype.val_injective.comp (samples_in k)).injOn (Finset.mem_univ i)
   exact ⟨fun x=>(Lagrange.basis s v i).eval x,⟨_,h.trans_le (by simp),fun x=>rfl⟩,fun x=>rfl⟩
lemma lead (F:sun→ℝ) (k:ℕ)(h:∀ x,F x=∑ i,F (sampleP k i)*title k i x):Nail k F:=by
   have hp:Nail k (fun x=>∑ i,F (sampleP k i)*title k i x):= net _ _ fun i _=> (park _).mul_left _
   rw [← funext h] at hp;exact hp
lemma integral {α:Type*}[MeasurableSpace α]{μ:Measure α}(f: sun→ α → ℝ)(he:∀ x,Nail k (fun t=> f t x))(ht:∀ t, Integrable (f t) μ): Nail k (fun t=> ∫ x,f t x ∂μ):=by
   refine lead _ _ (fun i=>?_); let v:=sampleP k; have hp: f i=fun x=> ∑ j,f (v j) x*title k j i:=funext fun x=> (he x).axis _
   conv_lhs =>rw [hp]
   rw [integral_finsetSum _ fun i _=> (ht _).mul_const _]; simp_rw [integral_mul_const]; rfl
end Nail
open Merge Switch
variable {A β U:Type}[Fintype A] {C:A→ℕ}
local notation "𝒲" => sun → Ways A
def Bed (C:A→ℕ)(f:sun→Ways A):Prop:= (∀ t:sun,∃ g, Switch.Models (f t) g) ∧ ∀ s:Finset A,Nail (∑ i∈s,C i) (fun t=> jet (f t) s)
namespace Bed
variable {F G:sun→Ways A}
lemma clickY {f:sun→ℝ}(i:Finset A)(h:Nail (∑ j∈i,C j) f):Bed C (fun t=>click i (f t)):=by
   refine ⟨fun t=>⟨_,modelClick i _⟩,fun j=>?_⟩; simp_rw [fun c=> (modelClick i c).exact]; by_cases hx:j=i
   · subst j; simpa [Switch.bench] using h
   simp_rw [bench,if_neg hx];exact Nail.const 0
lemma casket (a:ℝ): Bed C (fun t y p=>a):=by
   convert! clickY (C:=C) (∅: Finset A) (Nail.const a) using 1; ext; simp [click]
lemma plus (h:Bed C F)(ht:Bed C G): Bed C (F+G):=by
   choose g hg using h.1; choose k hk using ht.1; refine ⟨fun t=>⟨_,(hg t).add (hk t)⟩,fun s=>?_⟩
   have hh (t:sun): jet ((F+G) t) s=jet (F t) s+jet (G t) s:=by dsimp only [Pi.add_apply]; rw [((hg t).add (hk t)).exact,(hg t).exact,(hk t).exact];rfl
   simp_rw [hh]; exact Nail.add (h.2 _) (ht.2 _)
lemma time (h:Bed C F)(hk:Bed C G):Bed C (F*G):=by
   choose f H using h.1; choose g H' using hk.1; refine ⟨fun t=> ⟨_,(H t).mul (H' t)⟩,fun i=>?_⟩
   have ht t: jet ((F*G) t) i=comb 0 (jet (F t)) (jet (G t)) i:=by simp only [Pi.mul_apply,((H t).mul (H' t)).exact,(H t).exact,(H' t).exact]
   simp_rw [ht]; unfold comb; apply Nail.net _ _; rintro ⟨x,y⟩ _; split_ifs with hx; swap; · exact Nail.const 0
   subst i; by_cases hy:Disjoint x y
   · rw [disjoint_iff_inter_eq_empty.mp hy, Finset.card_empty, Finset.sum_union hy]; simp_rw [pow_zero,one_mul]; exact Nail.star (h.2 x) (hk.2 y)
   have hh: 0 < (x∩y).card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (disjoint_iff_inter_eq_empty.not.mp hy)); simp_rw [zero_pow hh.ne',zero_mul]; exact Nail.const 0
lemma pour (h:Bed C F)(i:ℕ):Bed C (F^i):=by
   induction i with | zero=>rw [pow_zero]; exact casket 1 | succ i ih=> rw [pow_succ];exact ih.time h
lemma spray(h:Bed C F)(x:ℝ): Bed C (x • F):= (casket x).time h
lemma many (F:β→sun→Ways A)(s:Finset β)(h:∀ i∈s,Bed C (F i)): Bed C (∑ i∈s,F i):=by
   induction s using Finset.induction_on with
   | empty=>simp only [Finset.sum_empty]; exact casket 0
   | insert i s hi ih=> rw [sum_insert hi];exact (h i (mem_insert_self ..)).plus (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma seals (F:β→sun→Ways A)(s:Finset β)(h:∀ i∈s,Bed C (F i)): Bed C (∏ i∈s,F i):=by
   induction s using Finset.induction_on with
   | empty=>simp only [Finset.prod_empty]; exact casket 1
   | insert i s hi ih=> rw [prod_insert hi];exact (h i (mem_insert_self ..)).time (ih fun i hi=> h i (mem_insert_of_mem hi))
open Extra.Trajectories Marker
variable {V:Type} [Fintype V] [DecidableEq V] {B:Census V}
lemma viewTag (tag:A→B.Mode)(a:A→ℂ)(h:Bed (fun a=>(tag a).val.card) F)(t:sun): let z i:= Poly.send (tag i) (a i); let v x:= Switch.sound z (F x); let n:=Fintype.card V; v t=∑ i,(↑(Nail.title n i t):ℂ) • v (sampleP n i):=by
   intro z v n; simp_rw [v,Switch.sound, Switch.mapScores_apply,Finset.smul_sum]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i _
   by_cases he:∏ j∈i,z j=0; simp [he];
   have hx := fits_of_tagged_prod tag he
   have hp : ∑ j∈i,(tag j).val.card ≤ n:=le_trans (Finset.card_biUnion hx.1|>.symm.le) (unionTag tag i hx).val.card_le_univ
   have ht : Switch.jet (F t) i= ∑ j, jet (F (sampleP n j)) i * Nail.title n j t:= ((h.2 _).raise hp).axis t
   rw [ht,Complex.ofReal_sum,Finset.sum_smul]; refine sum_congr rfl fun j _=> ?_; rw [← smul_assoc]; rw [smul_eq_mul]; rw [Complex.ofReal_mul,mul_comm (↑(Switch.jet _ _):ℂ)]
end Bed
end YM.FullVolume.Ray
