import YM.RG08.Spar.Appraise

/-!
# Column stencils cofinal continuation. Enforce all windings on finite periods, including
period one and repeated stubs landing on same body. Works after color reindexing at
arbitrary arity, no uniformity asserted in volume or horizon. Use for comparing literal
kernels, not costs on ANY complete mask labels.
-/
noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows
open scoped Topology BigOperators Classical ENNReal Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}[Fintype I]{H J:Type}[Fintype H][Fintype J]{n:ℕ}{l u:ℕ→Side}{P:Side}

def Appears (l:ℕ→Side)(f:Flake n (Market I))(g:(m:ℕ)→Flake n (Co (l m) I)):=∀ z,Tendsto (fun m=>g m (port (l m) ∘ z)) atTop (𝓝 (f z))

omit [Fintype I] in
lemma visible {f:Flake n (Market I)}{a b:(m:ℕ)→ Flake n (Co (l m) I)}(h:Appears l f a)(he:a=b): Appears l f b:= he ▸ h

/-- Reader at each coarse link. Keeps fixed arity sum, with support corresponding to a true
cover path. -/
def Holes (l:ℕ→Side)(A:(m:ℕ)→Matrix (Co (l m) I) (Co (l m) J) ℝ)(S:Market J→H→Market I)(c:Market J→H→ℝ):Prop:=
  ∀ m (z:Market J) b, A m b (port (l m) z)=∑ h:H,if b=port (l m) (S z h) then c z h else 0

def rafters {A B:Type} (S:B→H→A)(c:B→H→ℝ)(f:Flake n A):Flake n B:=fun x=>∑ w:Tape n H,f (fun i=>S (x i) (w i))*∏ i,c (x i) (w i)

omit [Fintype J] in
lemma appears_holes {f:Flake n (Market I)}{A:(m:ℕ)→ Matrix (Co (l m) I) (Co (l m) J) ℝ}{g:(m:ℕ)→Flake n (Co (l m) I)}{S:Market J→H→Market I}{c:Market J→H→ℝ}(he:Holes l A S c)(hf:Appears l f g):
 Appears l (rafters S c f) (fun m=>query (A m) (g m)):=by
 intro x
 have he'(m):query (A m) (g m) (port (l m) ∘ x)=∑ w:Tape n H,g m (port (l m) ∘ fun i=>S (x i) (w i))*∏ i,c (x i) (w i):=by
   unfold query
   have hi(h:Tape n H)(y:Tape n (Co (l m) I)): (∏ i, if y i=port (l m) (S (x i) (h i)) then c (x i) (h i) else 0)=
       if y=(port (l m) ∘ fun i=> S (x i) (h i)) then ∏ i,c (x i) (h i) else 0:=by
     by_cases he:y=(port (l m) ∘ fun i=> S (x i) (h i))
     · simp [he]
     rw [if_neg he];obtain ⟨i,hh⟩:=Function.ne_iff.mp he; exact prod_eq_zero (mem_univ i) (if_neg hh)
   unfold Holes at he
   simp_rw [comp_apply,he,Fintype.prod_sum,Finset.mul_sum,hi,mul_ite,mul_zero]
   rw [Finset.sum_comm]; simp [sum_ite_eq']
 simp_rw [he'];unfold rafters; refine tendsto_finsetSum _ fun w _=> (hf (fun i=> S (x i) (w i))).mul_const _

omit [Fintype I] in
lemma coboundHoles (l:ℕ→Side)(I:Type):
 ∃ (S:Market (Kind I 1)→ TypeFace 2 × Axis × Bool → Market (Kind I 2)) (t:Market (Kind I 1)→ TypeFace 2 × Axis × Bool→ℝ),
      Holes l (fun m=> shaded (l m) (l m) I ((cobound 1).acts _)) S t:=by
 let U:=TypeFace 2×Axis×Bool
 let S (x:Market (Kind I 1))(w:U):Market (Kind I 2):=((if w.2.2 then x.1-step w.2.1 else x.1), w.1,x.2.2)
 let t (x:Market (Kind I 1))(w:U):ℝ:= left ℝ 1 w.2.1 w.1 x.2.1 * (if w.2.2 then 1 else -1)
 refine ⟨S,t,?_⟩
 intro m x b
 change (if b.2.2=x.2.2 then _ else 0) = _
 simp only [port, S, t, Prod.ext_iff, Fintype.sum_prod_type, Fintype.sum_bool, acts_apply]
 by_cases he : b.2.2 = x.2.2
 · simp only [he, and_true, Bool.false_eq_true, ite_true, ite_false, mul_one, mul_neg,
     mul_sub, mul_ite, mul_zero]
   rw [Finset.sum_eq_single b.2.1]
   · apply Finset.sum_congr rfl
     intro j _
     have hw : b.1 = wrap (l m) (x.1 - step j) ↔ wrap (l m) x.1 = b.1 + step j := by
       rw [map_sub, wrap_step, eq_sub_iff_add_eq, eq_comm]
     simp only [and_true, hw, eq_comm (a := b.1) (b := wrap (l m) x.1)]
     split_ifs <;> ring
   · intro a _ ha
     simp [Ne.symm ha]
   · simp
 · simp [he]
end YM.RG08.Spar
