import YM.RG08.Line.Pine

/-!
# A funded stencil by tests at cell origins
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows
open scoped Matrix BigOperators Topology Classical
set_option autoImplicit false
variable {α β γ : Type} [Fintype α] [Fintype β]

lemma onePrice (W : α→β)(u:α→Cover)(A:∀ n:Side,Matrix (Co n α) (Co n β) ℝ) (q:α→ℝ)
    (h:∀ n v x,(A n*ᵥ v) x=q x.2 * v (x.1+wrap n (u x.2),W x.2)):Fund A := by
  refine Fund.rout Unit (fun _=> Matrix.of fun a b=> if b=W a then q a else 0) (fun _ a _=> u a) A (fun n v x=>?_)
  rw [h]; simp [ite_mul]

/-- Each output orientation sees a finite list of translated input sites/orientations.
Weights real, no positivity assumption. Test translations are from the *coarse-cell* origin.
No hypothesis yet on moment/rank scaling so this is strictly post-block (length costs may see J).
-/
abbrev stencil (α β : Type) := α→List (Cover × β × ℝ)

def stint (V : stencil α β) (n : Side)(v:Corn (Co n β))(x : Co n α) := ((V x.2).map fun w=> w.2.2 * v (x.1+wrap n w.1,w.2.1)).sum

lemma readsPrice (V : stencil α β)(A:∀ n:Side,Matrix (Co n α) (Co n β) ℝ)
    (h:∀ n v x,(A n*ᵥ v) x=stint V n v x): Fund A := by
  let K := univ.sup (fun i : α=> (V i).length)
  let pick (t:Fin K) (i:α)(k:β) : Cover × β × ℝ := ((V i)[t.val]?).getD (0,k,0)
  let X (t:Fin K): Matrix α β ℝ := Matrix.of fun i k=> if k=(pick t i k).2.1 then (pick t i k).2.2 else 0
  refine Fund.rout _ X (fun t i k=> (pick t i k).1) A fun n v x=>?_
  rw [h]
  let f (a: Cover × β × ℝ) := a.2.2 * v (x.1+wrap n a.1,a.2.1)
  have ht (s:List (Cover × β × ℝ)) : (s.map f).sum = ∑ i:Fin s.length,f (s.get i):=by
    induction s with
    | nil => simp
    | cons a s ih =>
      change _=∑ i:Fin (s.length+1),_
      rw [Fin.sum_univ_succ]; simpa only [List.get_eq_getElem, Fin.val_zero,Fin.val_succ,List.getElem_cons_succ,List.getElem_cons_zero,List.map,List.sum_cons] using congr_arg (f a + ·) ih
  rw [stint]
  calc
    _ = ∑ i:Fin (V x.2).length,f ((V x.2).get i):= ht _
    _ = ∑ t:Fin K,∑ j:β,X t x.2 j*v (x.1+wrap n (pick t x.2 j).1,j) := by
      let g := fun t:Fin K=>∑ j:β,X t x.2 j*v (x.1+wrap n (pick t x.2 j).1,j)
      let hk : (V x.2).length ≤ K := Finset.le_sup (f:=fun i=> (V i).length) (b:=x.2) (mem_univ _)
      let E : Fin (V x.2).length ↪ Fin K := ⟨Fin.castLE hk,(fun _ _ h=> Fin.ext (congr_arg (fun t:Fin K=>t.val) h))⟩
      have he (t:Fin (V x.2).length)(j:β): pick (E t) x.2 j=(V x.2).get t:=by simp [pick,E,List.get_eq_getElem]
      have hg (t:Fin (V x.2).length): f ((V x.2).get t)=g (E t):=by
        unfold g f X; simp only [of_apply,he,ite_mul]; simp
      simp_rw [hg]
      change (∑ t,g (E t))=∑ t,g t
      rw [← Finset.sum_map]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hI
      have hy:(V x.2).length ≤ i.val:= by
        by_contra! hh
        have ht: i=E ⟨i.val,hh⟩ := Fin.ext rfl
        exact hI (Finset.mem_map.mpr ⟨_,mem_univ _,ht.symm⟩)
      have hy' (j:β):pick i x.2 j=(0,j,0):=by simp [pick,List.getElem?_eq_none hy]
      unfold g X; simp [hy']

-- transferring a test from a repacked fine index
omit [Fintype α] [Fintype β] in
lemma repack_test [Fintype β] [Fintype γ] {δ:Type}(e:α ≃ δ)(k:β≃γ)(A:Matrix α β ℝ)(v:Corn γ)(x:δ):
    (repackM e k A *ᵥ v) x=(A *ᵥ (v ∘ k)) (e.symm x):= by
  classical
  unfold repackM Matrix.mulVec dotProduct
  simpa [Matrix.submatrix] using Equiv.sum_comp k.symm (fun i=> A (e.symm x) i*(v ∘ k) i)
end YM.RG08.Line
