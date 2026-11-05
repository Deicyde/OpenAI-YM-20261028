import YM.RG08.Gallery.Boot

/-! # Multipoint separation (including repeated locations) -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J:Type}{n:ℕ}

def soft (S:Finset J)(a:J→Demo I):=S.biUnion (Demo.firm ∘ a)
def synth(S:Finset J)(c:J→ℝ)(a:J→Demo I):Demo I where
 firm:=soft S a
 play i:=∑ j∈S,c j*(a j).play i
 size' i hi:=Finset.sum_eq_zero fun j hj=>by rw [(a j).size' i (fun hz=>hi (Finset.mem_biUnion.mpr ⟨_,hj,hz⟩)),mul_zero]

def appled (S:Finset I)(x:Flake n I)(w:Tape n (Demo I)) :=∑ t∈desks S n,x t*∏ i,(w i).play (t i)
def multi (F:Flake n I)(w:Tape n (Demo I)):=appled (soft univ w) F w
lemma multi_in (S:Finset I)(F:Flake n I)(w:Tape n (Demo I))(h:soft univ w⊆S):multi F w=appled S F w:=by
 unfold multi appled;apply Finset.sum_subset (by intro x hx; simp only [desks,Fintype.mem_piFinset] at hx ⊢; exact fun j=>h (hx j))
 intro t ht hz;simp only [desks,Fintype.mem_piFinset,not_forall] at hz;obtain ⟨i,hi⟩:=hz
 rw [Finset.prod_eq_zero (Finset.mem_univ i) ((w i).size' _ (fun hz=>hi (Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,hz⟩))),mul_zero]

lemma multi_symmetric {F:Flake n I}(h:Sym F)(w:Tape n (Demo I))(e:Equiv.Perm (Fin n)): multi F (w ∘ e)=multi F w:=by
 let S:=soft univ w ∪ soft univ (w ∘ e)
 rw [multi_in S _ _ Finset.subset_union_right,multi_in S _ _ Finset.subset_union_left]
 let g(t:Tape n I):=F t*∏ i,(w i).play (t i)
 have he : (desks S n).image (twist e (I:=I))=desks S n:=by
    ext i;rw [Finset.mem_image];constructor
    · rintro ⟨x,hx,rfl⟩;simp only [desks,Fintype.mem_piFinset] at hx ⊢; intro l;exact hx (e l)
    intro hi
    refine ⟨i ∘ e.symm,by simp only [desks,Fintype.mem_piFinset] at *;exact fun t=> hi (e.symm t),?_⟩;ext t; simp [twist]
 unfold appled
 nth_rw 1 [←he]
 rw [Finset.sum_image (twist (I:=I) e).injective.injOn];apply Finset.sum_congr rfl;intro t _
 rw [show F (twist e t)=F t from congrFun (h e) t];congr 1;exact Equiv.prod_comp e fun j=>(w j).play (t j)

/- Id coefficient isolates product on all ordered terms if symmetric. -/
lemma diagonal (c: Fin n→ℝ)(a:Tape n (Demo I))(F:Flake n I):
 regard F (synth univ c a)= MvPolynomial.eval c (parley (fun x:Tape n (Fin n)=>multi F (a ∘ x))):=by
 unfold regard parley synth basic;dsimp only; simp_rw [Fintype.prod_sum (f:=fun (i j:Fin n)=>c j*(a j).play _), _root_.map_sum, MvPolynomial.smul_eq_C_mul, eval_mul, eval_C,word,map_prod,eval_X, Finset.mul_sum];rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _
 have he: soft univ (a ∘ x)⊆ soft univ a:=by intro i hi; obtain ⟨b,hb,h⟩:=Finset.mem_biUnion.mp hi; exact Finset.mem_biUnion.mpr ⟨x b,mem_univ _,h⟩
 rw [multi_in _ _ _ he,appled,Finset.sum_mul]; apply Finset.sum_congr rfl;intro i _;rw [Finset.prod_mul_distrib]; simp only [comp_apply];ring

lemma unravel {F T:Flake n I}(h:Sym F)(H:Sym T)(s t:Tape n (Demo I))(he:∀ c:Fin n→ℝ,regard F (synth univ c s)=regard T (synth univ c t)):multi F s=multi T t:=by
 have hd:= MvPolynomial.funext (R:=ℝ) (fun c=>by simpa only [diagonal] using he c)
 have ht (F:Flake n I)(h:Sym F)(s:Tape n (Demo I)): Sym (fun x:Tape n (Fin n)=>multi F (s ∘ x)):=fun e=>funext (fun x=>multi_symmetric h (s ∘ x) e)
 exact congrFun (Carrel.pursuit (ht _ h _) (ht _ H _) hd) id

def needle (a:I): Demo I:=⟨{a},Pi.single a 1,fun j hj=>Pi.single_eq_of_ne (by simpa using hj) _⟩
lemma mlikes (F:Flake n I)(w:Tape n I):multi F (needle ∘ w)=F w:=by
 rw [multi,appled,Finset.sum_eq_single_of_mem w (by simp [desks,soft,needle,Fintype.mem_piFinset])];swap
 · intro y hy h;obtain ⟨i,hi⟩:=Function.ne_iff.mp h;rw [Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne hi _ : (needle (w i)).play (y i)=0),mul_zero]
 simp [needle]
end YM.RG08.Gallery
