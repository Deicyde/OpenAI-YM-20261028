import YM.Push.PRICE_COMPILER.Post

/-!
# Actual row cost from the pre-L kernel quote, for one path convention

For use by path construction. This supplies one small
piece of `PathInputs`: assuming a priced Fourier kernel (`Floor` etc on one
Bed, such as priced by the Pin interface), can make canonical path rows,
with *actual counts*, ending at the needed site on the cover and paying the
true length mass. At the symbolic cost and widths here there is no need to
assume this additional price inequality from L-dependent path choices. Matches
the B70 `Attached` hashes. For this convention `Adjoint` is always actual
matrix adjoint via the evaluator; if using these lemmas with towers etc
must use these SAME paths (or supply a justified different calculation).

It doesn't give the loop/cubic/quartic pieces, nor produce the underlying
Fourier data. Not claiming suitability of these paths for all stationary
or RG constructions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler.Canonical
open Filter Function Lattice RG Precision Laurent Exterior Matrix Bloch
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- One canonical choice of shortest coordinate walk; retain as a real
kernel address. -/
def slot (b : PlaqAxes) (x : Cover) : Slot := ⟨route 0 x 1,b⟩
lemma endSlot (b : PlaqAxes) (x : Cover) : (slot b x).offset = x := route_end ..
lemma sizeSlot (b : PlaqAxes) (x : Cover) : (slot b x).length = size x + 4 := by
  have ha : allAxes 1 = [0,1,2,3] := by decide
  simp [Slot.length,slot,route, axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]

def enumPath : ℕ ≃ PlaqAxes × Cover := by
  classical
  have : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  letI : Denumerable (PlaqAxes × Cover) := Classical.choice (nonempty_denumerable (PlaqAxes × Cover))
  exact (Denumerable.eqv _).symm

/-- No wrap/residue truncation. -/
def row (H : Bed) (b : PlaqAxes) (i : ℕ) : ℝ × Slot :=
    let v := enumPath i
    (H.roots (plaquette b) (plaquette v.1) v.2,slot v.1 v.2)

/-- Layout holds independent of summability. -/
lemma attached {H : Bed} (W : PathData G) (h : W.row=row H) : Attached H W := by
  classical
  constructor
  intro b p x
  rw [h]
  let a := enumPath.symm (p,x)
  have hw (i : ℕ) : (row H b i).2.plaq = p ∧ (row H b i).2.offset=x ↔ i=a := by
    change (enumPath i).1=p ∧ _ ↔ _
    rw [show (row H b i).2 = _ from (show (row H b i).2=slot _ _ from rfl),endSlot]
    suffices hb : enumPath i = (p,x) ↔ i=a by simpa only [Prod.ext_iff] using hb
    exact ⟨fun h => enumPath.injective (h.trans (enumPath.apply_symm_apply ..).symm),
      fun h => by rw [h]; exact enumPath.apply_symm_apply _⟩
  simp_rw [hw]
  have he : H.roots (plaquette b) (plaquette p) x = (if a=a then (row H b a).1 else 0) := by simp [row,a]
  rw [he]; exact hasSum_single a (fun i hi => by simp [hi])

/-- Price for all columns for a *fixed row*, not requiring counting
period-specific numbers of torus sites. -/
def fee (s C : ℝ) := (Fintype.card PlaqAxes : ℝ) * (Real.exp (s*4)*C)




lemma cost {a A : ℝ} (H : Bed) (h : H.roots.strip a A) (b : PlaqAxes) :
    SumBudget (fun i : ℕ => |(row H b i).1| * Real.exp (a * (row H b i).2.length)) (fee a A) := by
  classical
  let f (y : PlaqAxes × Cover) : ℝ := |H.roots (plaquette b) (plaquette y.1) y.2| *
    Real.exp (a * (slot y.1 y.2).length)
  let c := Real.exp (a*4)
  have hh (p : PlaqAxes) : SumBudget (fun x : Cover => f (p,x)) (c*A) := by
    let G x := Real.exp (a*size (α:=Axis) x)*‖H.roots (plaquette b) (plaquette p) x‖
    have hg : SumBudget G A := h (plaquette b) (plaquette p)
    rw [show (fun x : Cover => f (p,x)) = (fun x => c*G x) by
      funext x; unfold f G c; rw [sizeSlot]; push_cast; rw [mul_add,Real.exp_add,Real.norm_eq_abs]; ring]
    exact ⟨fun i => mul_nonneg (Real.exp_pos _).le (hg.1 i),hg.2.1.mul_left c,(Eq.trans_le tsum_mul_left
      (mul_le_mul_of_nonneg_left hg.2.2 (Real.exp_pos _).le))⟩
  have hz : 0 ≤ f := fun p => (hh p.fst).1 _
  have hu := (summable_prod_of_nonneg hz).mpr ⟨fun p => (hh p).2.1,Summable.of_finite⟩
  change SumBudget (f ∘ enumPath) _
  refine ⟨fun _ => hz _, enumPath.summable_iff.mpr hu,?_⟩
  calc
    _ = ∑' i, f i := enumPath.tsum_eq f
    _ = ∑' i, ∑' x, f (i,x) := hu.tsum_prod
    _ ≤ ∑ _i : PlaqAxes, c*A := by rw [tsum_fintype]; exact Finset.sum_le_sum fun p _ => (hh p).2.2
    _ = fee a A := by simp [fee,c]

/-- The scalar zero mode read and smallest-torus action agree exactly,
no mode-count normalization. This statement doesn't need convergence of
separate fibers; using these sums with arithmetic will still require the
absolute budget. -/
private lemma harmonic {α β : Type*} (R : Row α β) (i : α) (j : β) :
    R.read 0 i j = (R.acts 1 (0,i) (0,j):ℝ) := by
  change (∑' a, mode 0 a • ((R i j a:ℝ):ℂ)) = ((∑' x, if (0 : Site 1) = 0 + wrap 1 x then R i j x else 0 : ℝ):ℂ)
  letI : Subsingleton (Site 1) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
  have he (x : Cover) : (0 : Site 1) = 0 + wrap 1 x := Subsingleton.elim ..
  simp only [mode_constant,one_smul]
  rw [Complex.ofReal_tsum]
  exact tsum_congr (fun x => by rw [if_pos (he x)])

/-- `symbol0` at one plaque pair from the canonical row; all wraps
come in the sum. Need `h` credit. -/
lemma symbol {a A : ℝ} {H : Bed} (h : H.roots.strip a A) (ha : 0 ≤ a)
    (b p : PlaqAxes) {W : PathData G} (hw : W.row=row H) :
    W.symbol0 b p = H.roots.acts 1 ((0 : Site 1),plaquette b) ((0 : Site 1),plaquette p) := by
  classical
  let f (y : PlaqAxes × Cover) := if y.1=p then H.roots (plaquette b) (plaquette p) y.2 else 0
  have he : Summable (H.roots (plaquette b) (plaquette p)) := ((h (plaquette b) (plaquette p)).summable ha)
  have hb : Summable f := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun x => norm_nonneg (f x))).mpr
    constructor
    · intro i; by_cases ht : i=p
      · simpa [f,ht] using (he.norm)
      simp [f,ht]
    exact Summable.of_finite
  unfold PathData.symbol0
  rw [hw]
  have hg : (fun i => if (row H b i).2.plaq = p then (row H b i).1 else 0) = f ∘ enumPath := by
    funext i; by_cases he : (enumPath i).1=p <;> simp [row,f,Function.comp,he,slot]
  rw [hg,show ∑' i, (f ∘ enumPath) i = ∑' j, f j from enumPath.tsum_eq _, hb.tsum_prod,tsum_fintype]
  rw [Finset.sum_eq_single p]
  · simp only [f,if_true]
    change _ = ∑' _, _
    letI : Subsingleton (Site 1) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
    apply tsum_congr; intro i; rw [if_pos (Subsingleton.elim ..)]
  · intro i _ hi; simp [f,hi]
  simp

/-- Use the harmonic part of Floor. No wrongly treating the smallest torus as
having no constrained modes. The *promises* from Rack/Horizon require Floor
for EVERY n. -/
lemma weights {a A v : ℝ} {H : Bed} (h : H.roots.strip a A) (ha : 0 ≤ a) {p : Clip}
    (hp : Floor H p 1 v A) {W : PathData G} (hw : W.row=row H) : W.metric_zero p := by
  classical
  let f := H.full p 1
  have he (i j : TypeFace 2) : H.metric.acts 1 ((0 : Site 1),i) ((0 : Site 1),j) = if i=j then 1 else 0 := by
    have h' := harmonic H.metric i j
    rw [hp.starts] at h'; by_cases hh : i=j <;> simp [hh, Matrix.one_apply] at h' ⊢ <;> exact_mod_cast h'.symm
  intro i j
  simp_rw [symbol h ha _ _ hw]
  let x := plaquette i; let y := plaquette j
  have hx : x=y ↔ i=j := Exterior.plaq_iff i j
  have hh := congr_fun (congr_fun hp.roots ((0 : Site 1),x)) ((0 : Site 1),y)
  rw [he x y, Matrix.mul_apply, Fintype.sum_prod_type] at hh
  -- one physical site
  letI : Unique (Site 1) := inferInstanceAs (Unique (Axis → ZMod 1))
  have hu : (default : Site 1) = 0 := Subsingleton.elim ..
  rw [Fintype.sum_unique,hu] at hh
  rw [Fintype.sum_sum_type] at hh
  dsimp [Matrix.transpose,Bed.full] at hh
  -- known quadratic direct block
  let g (r z : TypeFace 2) := Real.sqrt p.direct * (1: Matrix (Co (1:Side) (TypeFace 2)) (Co (1:Side) (TypeFace 2)) ℝ) (0,r) (0,z)
  let Gg (r z : TypeFace 2) := H.roots.acts 1 (0,r) (0,z)
  change (∑ z : TypeFace 2, g z x * g z y) + ∑ z : TypeFace 2, Gg z x * Gg z y = _ at hh
  have ht : ∑ z : TypeFace 2, g z x * g z y = if i=j then p.direct else 0 := by
    rw [Finset.sum_eq_single x]
    · by_cases hm : i=j
      · have hk : x=y := hx.mpr hm
        simp [g,hk,hm,Matrix.one_apply, Real.mul_self_sqrt p.quadratic_pos.le]
      have hk : ¬x=y := fun h => hm (hx.mp h)
      simp [g,hk,hm,Matrix.one_apply]
    · intro b _ hb
      simp [g, Matrix.one_apply,hb]
    simp
  have hf (m : TypeFace 2 → ℝ) : (∑ z, m z) = ∑ w : PlaqAxes, m (plaquette w) :=
    (Equiv.sum_comp plaqEquiv m).symm
  rw [ht, hf] at hh
  simpa only [hx] using hh
/-- Arrange the corresponding pre-L quotes without using a particular
`Rolls`. -/
structure Quotes (K : MapPrices) (w : Openings) (u : Amounts) : Prop where
  fit : w.wish ≤ K.α
  top i : fee (K.α i) (K.Ω i) ≤ u.born i
  send i j : StepStages j i → fee (K.α i) (K.Ω i) ≤ u.sends j i

/-- Before choosing the amounts, fix width upper requests to include
these. Kernel quotation itself must still be priced **before** this use. -/
def orderWidth (K : MapPrices) (w : Openings) : Openings :=
    { w with wish := fun i => min (w.wish i) (K.α i), wp := fun i => lt_min (w.wp i) (K.alpha_pos i) }

lemma orderWidth_le (K : MapPrices) (w : Openings) : (orderWidth K w).wish ≤ w.wish :=
    fun _ => min_le_left ..

/-- Given raw input amounts including the estimates *at the installed
widths*, **before** committing caps, ensure canonical row cost also paid. -/
def orderRows (K : MapPrices) (u : Amounts) : Amounts :=
    let f (i : ℕ) := fee (K.α i) (K.Ω i)
    { u with born := fun i => max (u.born i) (f i)
             sends := fun j i => max (u.sends j i) (f i)
             born_pos := fun i => (u.born_pos i).trans_le (le_max_left ..)
             sends_pos := fun j i => (u.sends_pos j i).trans_le (le_max_left ..) }
lemma orderRows_quotes (K : MapPrices) (w : Openings) (u : Amounts) :
    u.born ≤ (orderRows K u).born ∧ u.sends ≤ (orderRows K u).sends ∧
      Quotes K (orderWidth K w) (orderRows K u) :=
    ⟨fun _ => le_max_left .., fun _ _ => le_max_left .., fun _ => min_le_right ..,
      fun _ => le_max_right ..,fun _ _ _ => le_max_right ..⟩

open RG.Supply



/-- When trying to choose Clip/Stage numbers that actually cross the
canonical port, note that Clip alone only asks `0 < direct`. Taking any
old Clip later may be impossible. -/
lemma direct_le_one {W : PathData G} {p : Clip} (h : W.metric_zero p) : p.direct ≤ 1 := by
  let a : PlaqAxes := ⟨(0,1),by decide⟩
  have he := h a a
  simp only [if_true] at he
  have hp : 0 ≤ ∑ i : PlaqAxes, W.symbol0 i a * W.symbol0 i a := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  linarith
end YM.Push.PriceCompiler.Canonical
