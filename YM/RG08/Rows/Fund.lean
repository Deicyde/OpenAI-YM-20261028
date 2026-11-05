import YM.RG08.Rows.Algebra
import YM.RG08.Flat.Curl

/-!
# Finite-range translational operators (post-block costs)
-/
noncomputable section
namespace YM.RG08.Rows
open Filter Finset Pert.Bulk Lattice Laurent Bloch RG08.Packets Function Matrix
open scoped Topology ENNReal Matrix Classical
set_option autoImplicit false
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] {p q σ : ℝ}
    {K : Kernel α β}
    {A : ∀ n:Side,Matrix (Co n α) (Co n β) ℝ}

/-- Exists post-L cost (fix *any* nonnegative width first). Use only where there is no price to
be multiplied through many same-component steps. -/
def Fund (A : ∀ n:Side,Matrix (Co n α) (Co n β) ℝ) := ∀ σ : ℝ, 0 ≤ σ → ∃ p K, Tagged σ p K A

namespace Fund
lemma ticket (R : Row α β) (s : Finset Cover) (he : ∀ i j x,x∉s→R i j x=0): Fund R.acts:=by
  intro σ _
  obtain ⟨A,hA,h⟩:= Work.F06.strip_of_fin s R he σ
  exact ⟨A,_,Tagged.ticket R h hA⟩

omit [Fintype α] in
lemma plus (h:Fund A){B:∀ n:Side,Matrix (Co n α) (Co n β) ℝ}(ht:Fund B): Fund (A+B) := by
  intro σ hs; obtain ⟨_,_,h⟩:=h σ hs; obtain ⟨_,_,ht⟩:=ht σ hs; exact ⟨_,_,h.add ht hs⟩
omit [Fintype α] in
lemma minus (h:Fund A){B:∀ n:Side,Matrix (Co n α) (Co n β) ℝ}(ht:Fund B): Fund (A-B) := by
  intro σ hs; obtain ⟨_,_,h⟩:=h σ hs; obtain ⟨_,_,ht⟩:=ht σ hs; exact ⟨_,_,h.sub ht hs⟩
omit [Fintype α] [Fintype γ] in
lemma times (h:Fund A){B:∀ n:Side,Matrix (Co n β) (Co n γ) ℝ}(ht:Fund B): Fund (fun n=>A n*B n):= by
  intro σ hs; obtain ⟨_,_,h⟩:=h σ hs; obtain ⟨_,_,ht⟩:=ht σ hs; exact ⟨_,_,h.mul ht hs⟩
omit [Fintype α] [Fintype β] in
lemma scaled (h:Fund A)(p:ℝ): Fund (fun n=>p • A n) := by intro σ hs; obtain ⟨_,_,h⟩:=h σ hs; exact ⟨_,_,h.smul p⟩
omit [Fintype α] [Fintype β] in
lemma reversed (h:Fund A):Fund fun n=>(A n).transpose:=by intro σ hs; obtain ⟨_,_,h⟩:=h σ hs; exact ⟨_,_,h.rear hs⟩

omit [Fintype α] [Fintype β] in
lemma zero : Fund (fun n:Side=> (0: Matrix (Co n α) (Co n β) ℝ)) :=
  fun σ _=>⟨0,0,Priced.zero σ,fun n x y=> by simp [display] ⟩ -- structure nested

omit [Fintype α] in
lemma sum {ρ : Type*} (s:Finset ρ)(A:ρ→∀ n:Side,Matrix (Co n α) (Co n β) ℝ)(he:∀i∈s,Fund (A i)) : Fund fun n=>∑ i∈s,A i n := by
  induction s using Finset.induction with
  | empty => simpa only [sum_empty] using Fund.zero (β:=β) (α:=α)
  | insert i s ht hh =>
    simp_rw [sum_insert ht]
    change Fund (A i+fun n=>∑ i∈s,A i n)
    exact (he i (mem_insert_self ..)).plus (hh fun k hk=> he k (mem_insert_of_mem hk))

-- An offset may be chosen per pair of coefficient types.
def slip (C : Matrix α β ℝ) (v : α → β → Cover) : Row α β := fun i j x=> if x=v i j then C i j else 0
lemma slip_control (C : Matrix α β ℝ) (v : α→β→Cover) : Fund (slip C v).acts :=
  ticket _ ((Finset.univ (α:=α×β)).image (Function.uncurry v)) fun i j _x hx=> if_neg fun h=>hx (mem_image.mpr ⟨(i,j),mem_univ _,h.symm⟩)

 omit [Fintype α] in
lemma slip_at (C : Matrix α β ℝ) (v : α→β→Cover) (n : Side) (F : Corn (Co n β))(x : Co n α):
    ((slip C v).acts n*ᵥ F) x = ∑ j:β,C x.2 j * F (x.1+wrap n (v x.2 j),j) := by
  unfold Row.acts Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type, sum_comm]
  refine Finset.sum_congr rfl fun i _=> ?_
  simp only [Matrix.of_apply]
  have hh (b : Site n): (∑' w, (if b = x.1+wrap n w then slip C v x.2 i w else 0)) = if b=x.1+wrap n (v x.2 i) then C x.2 i else 0 := by
    rw [tsum_eq_single (v x.2 i)]
    · simp [slip]
    intros k hk; simp [slip,hk]
  simp_rw [hh,ite_mul]; simp

/-- Shift with multiple offsets and weights per pair/anchor. -/
lemma rout (ι:Type)[Fintype ι] (C:ι→Matrix α β ℝ)(v:ι→α→β→Cover)
    (A:∀ n:Side,Matrix (Co n α) (Co n β) ℝ)
    (h:∀ n (F:Corn (Co n β))(x), (A n*ᵥ F) x=∑ t:ι,∑ j:β,C t x.2 j*F (x.1+wrap n (v t x.2 j),j)) : Fund A := by
  have he n : A n=∑ t:ι,(slip (C t) (v t)).acts n := by
    refine Matrix.toLin'.injective ?_; apply LinearMap.ext; intro F; funext x
    change (A n *ᵥ F) x= ((∑ _, _)*ᵥ F) x
    rw [h, Matrix.sum_mulVec]; simp_rw [Finset.sum_apply,slip_at]
  rw [show A=(fun n=>∑ t:ι,(slip (C t) (v t)).acts n) from funext he]
  exact sum Finset.univ (fun i=>(slip (C i) (v i)).acts) (fun i _=>slip_control _ _)
end Fund
end YM.RG08.Rows
