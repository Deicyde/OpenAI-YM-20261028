import YM.Push.FREE_RESOLVENT.Focus
import YM.Push.FREE_RESOLVENT.FullRow
import YM.Push.FREE_RESOLVENT.GaugeProjection
import YM.Work.A15


/-!
# Compare arbitrary periods in the interior of matched patches

Transport from both periods to ONE numbering in the patch. Same lengths,
parameters, placement and slots there; allow different worlds outside.
No treating resonance grids or periodizing an inverse after an unrelated
tree choice. Match includes all colors used, though comparisons at one
column need only the distance hypotheses to excluded coordinates. Theorem
`shared_price` is usable in nonuniform geometries too (local discrepancy in
precision on *matched patch*, not whole operator or inverse).
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Matrix RG Precision Bloch Laurent Tree Bid
open scoped BigOperators

section Two
variable {X Y ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ]

-- pull metrics with exact numerical costs
omit [DecidableEq κ] in
lemma rows_here {D : Cost X} {D' : Cost Y} {x : κ → X} {y : κ → Y}
    (h : D.pull x = D'.pull y) (A : Matrix κ κ ℝ) {M σ : ℝ} (H : D.Schur x x σ M A) :
    D'.Schur y y σ M A := by
  have hh (i j : κ) : D.weight σ (x i) (x j)=D'.weight σ (y i) (y j) :=
    congr_arg (fun C : Cost κ => C.weight σ i j) h
  constructor <;> constructor <;> intro i
  · simp_rw [← hh]; exact H.rows.bound i
  simp_rw [← hh]; exact H.cols.bound i

/-- Estimate for a common core with a shared horizon; both full inverse errors
from *their own* windows, local mismatch controlled only on these windows. -/
theorem shared_price (e : κ ↪ ι) (f : κ ↪ ι') (i j : κ)
    (D : Cost X) (D' : Cost Y) (a : ι → X) (b : ι' → Y)
    {R M V W σ γ μ u r : ℝ} {A : Matrix ι ι ℝ} {B : Matrix ι' ι' ℝ}
    (ha : ∀ k : ι, k ∉ Set.range e → R ≤ D.d (a (e i)) (a k))
    (hb : ∀ k : ι', k ∉ Set.range f → R ≤ D'.d (b (f i)) (b k))
    (he : D.pull (a ∘ e) = D'.pull (b ∘ f))
    (hp : D.Schur a a σ M A) (hq : D'.Schur b b σ M B)
    (hg : Gap A r) (hg' : Gap B r)
    (hx : D.Volume a (safeRate σ M r-μ) V)
    (hy : D'.Volume b (safeRate σ M r-μ) V)
    (hz : D.Schur (a ∘ e) (a ∘ e) γ W (A.submatrix e e-B.submatrix f f))
    (hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < σ) (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hm : γ ≤ μ)
    (hσ : μ ≤ σ) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    D.weight γ (a (e i)) (a (e j)) * |resolve A u (e j) (e i)-resolve B u (f j) (f i)| ≤
      windowPrice M V r u μ γ R + (V*(r/2+u)⁻¹)*W*(V*(r/2+u)⁻¹) + windowPrice M V r u μ γ R := by
  let E := V*(r/2+u)⁻¹
  let w := D.weight γ (a (e i)) (a (e j))
  have hw : w = D'.weight γ (b (f i)) (b (f j)) := congr_arg (fun C : Cost κ => C.weight γ i j) he
  have ha' := hg.submatrix e e.injective
  have hb' := hg'.submatrix f f.injective
  have hp' : D.Schur (a ∘ e) (a ∘ e) γ E (Pane.thin A e u) :=
    (resolve_schur hM hs (hp.submatrix e.injective e.injective) ha' hr hu (hx.comp e.injective)).mono hm le_rfl
  have hq' : D.Schur (a ∘ e) (a ∘ e) γ E (Pane.thin B f u) := rows_here he.symm _
    ((resolve_schur hM hs (hq.submatrix f.injective f.injective) hb' hr hu (hy.comp f.injective)).mono hm le_rfl)
  have hE : 0 ≤ E := mul_nonneg hV (by positivity)
  have ht : D.Schur (a ∘ e) (a ∘ e) γ (E*W*E) (Pane.thin B f u-Pane.thin A e u) := by
    unfold Pane.thin
    rw [resolve_diff ((ha'.shift u).unit_det (by positivity)) ((hb'.shift u).unit_det (by positivity))]
    exact (hq'.mul hz hγ hE hW).mul hp' hγ (mul_nonneg hE hW) hE
  let α := resolve A u (e j) (e i)
  let β := resolve B u (f j) (f i)
  let C := windowPrice M V r u μ γ R
  let c := Pane.thin A e u j i
  let d := Pane.thin B f u j i
  have h1 : w*|α-c| ≤ C := by rw [abs_sub_comm]; exact focus_price e i ha hu hr hs hM hγ hm hσ hV hp hg hx j
  have h2 : w*|d-β| ≤ C := by rw [hw]; exact focus_price f i hb hu hr hs hM hγ hm hσ hV hq hg' hy j
  have h3 : w*|c-d| ≤ E*W*E := by rw [abs_sub_comm]; exact ht.cols.weighted i j
  have hl : |α-β| ≤ |α-c| + |c-d| + |d-β| := by
      rw [show α-β = (α-c + (c-d)) + (d-β) by ring]
      exact (abs_add_le ..).trans (add_le_add_left (abs_add_le ..) _)
  apply (mul_le_mul_of_nonneg_left hl (D.weight_nn γ (a (e i)) (a (e j)))).trans
  rw [mul_add, mul_add]
  exact add_le_add (add_le_add h1 h3) h2
end Two

-- Period system with embeddings to common cover offsets.
namespace Lifted
variable {G : Gauge} {c f : Side}

/-- Coarse offsets in D.native widths, with *free* status preserved. -/
def grid (S : StepData c f) (T : Forest S.ratio) (i : Active G T) := splitCo S.ratio (PAC G 1) (plant T i)

lemma grid_site (S : StepData c f) (T : Forest S.ratio) (i : Active G T) :
    (grid S T i).1 = theta _ T i := by rw [grid,split_co]; rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {P : Patch} {K : KernelChoices}

-- need equality transporting also tile types: specialize S with sizes implicit
abbrev data {c f : Side} (h : f.val = c.val * P.L.val) (K : KernelChoices) :=
  StepData.mk (c:=c) (f:=f) P K h

lemma tree_read {S : StepData c f} {s M : ℝ} {H : FaceRow} (hs : 0 ≤ s) (h : H.strip s M)
    (T : Forest S.ratio) :
    treeMatrix G S T H = ((fullRow G S.patch S.kernel.penalty H).acts c).submatrix (grid S T) (grid S T) := by
  rw [treeMatrix, fullRow_periods S hs h]; rfl

/-- e is the common patch's actual physical location in THIS period. y is
any chosen anchor. Use one patch offset/name/color `names` in corresponding
calls for both tori. -/
def Copies (S : StepData c f) (T : Forest S.ratio) (e : κ ↪ Active G T)
    (y : Site c) (names : κ → Cover × Co S.patch.L (PAC G 1)) :=
  ∀ i, grid S T (e i)=(y+wrap c (names i).1,(names i).2)

/-- Common max-cost on the lifted patch. -/
def spread (x : Cover) := Finset.univ.sup fun i => (x i).natAbs

def Small {L : Side} (names : κ → Cover × Co L (PAC G 1)) (R : ℕ) : Prop :=
  ∀ i j, size ((names i).1-(names j).1) ≤ R

omit [Fintype κ] [DecidableEq κ] in
lemma agrees {S : StepData c f} {T : Forest S.ratio} {e : κ ↪ Active G T} {y}
    {names} (h : Copies S T e y names) {R : ℕ} (H : Small names R) (hp : 2*R < c.val) (i j : κ) :
    separation (theta S.ratio T (e i)) (theta S.ratio T (e j)) = spread ((names i).1-(names j).1) := by
  rw [← grid_site, ← grid_site,h i,h j]; simp only [separation,pdist, add_sub_add_left_eq_sub, ← map_sub,
    size_centers _ _ (H i j) hp,spread]

omit [Fintype κ] [DecidableEq κ] in
lemma chargeHere {S : StepData c f} {T : Forest S.ratio} {e : κ ↪ Active G T} {y}
    {names} (h : Copies S T e y names) {R : ℕ} (H : Small names R) (hp : 2*R < c.val) (A : Row (Co S.patch.L (PAC G 1)) (Co S.patch.L (PAC G 1)))
    (i j : κ) :
    (shorten R A).acts c (grid S T (e i)) (grid S T (e j)) = A (names i).2 (names j).2 ((names j).1-(names i).1) := by
  rw [h i,h j, show y+wrap c (names j).1=y+wrap c (names i).1+wrap c ((names j).1-(names i).1) by rw [map_sub]; abel]
  exact cut_lift A _ _ _ _ _ (H j i) hp

lemma grid_inj (S : StepData c f) (T : Forest S.ratio) : Function.Injective (grid (G:=G) S T) :=
  (splitCo S.ratio _).injective.comp (plant_inj T)

def shortenMatrix (G : Gauge) (S : StepData c f) (T : Forest S.ratio) (H : FaceRow) (R : ℕ) :=
  let g := grid S T
  ((shorten R (fullRow G S.patch S.kernel.penalty H)).acts c).submatrix g g

-- W exponential in R not in shortest image. No circular comparison of Bs.
lemma matrix_tail (S : StepData c f) (T : Forest S.ratio) (R : ℕ) {σ μ M : ℝ} {H : FaceRow}
    (hm : 0 ≤ μ) (he : μ ≤ σ) (hM : 0 ≤ M) (hp : H.strip σ M) :
    (native c).Schur (theta S.ratio T) (theta S.ratio T) μ
      (Real.exp ((μ-σ)*R)*billing G S.patch S.kernel.penalty σ M)
      (treeMatrix G S T H-shortenMatrix G S T H R) := by
  have hw := fullRow_width (G:=G) S.patch S.kernel.penalty (hm.trans he) hM hp
  let e := grid S T (G:=G)
  have hg : Function.Injective e := grid_inj ..
  have hy : Prod.fst ∘ e = theta S.ratio T := funext (grid_site S T)
  have hh := (physical (strip_tail hw R he) hm c).submatrix hg hg
  erw [Work.F08.acts_minus (hm.trans he) hw (strip_shorten hw R), Matrix.submatrix_sub, hy] at hh
  rw [billing, mul_left_comm, tree_read (hm.trans he) hp]; exact hh

omit [Fintype κ] [DecidableEq κ] in
lemma native_match {c' f' : Side} {h : f.val = c.val*P.L.val} {h' : f'.val = c'.val*P.L.val}
    {T : Forest (data h K).ratio} {U : Forest (data h' K).ratio} (i : κ ↪ Active G T) (j : κ ↪ Active G U)
    {names : κ → Cover × Co P.L (PAC G 1)} {y y'} (hv : Copies (data h K) T i y names) (hw : Copies (data h' K) U j y' names)
    {R : ℕ} (hh : Small names R) (hr : 2*R < c.val) (hr' : 2*R < c'.val) :
    (native c).pull (theta (data h K).ratio T ∘ i) = (native c').pull (theta (data h' K).ratio U ∘ j) := by
  have he : ∀ a b, ((native c).pull (theta (data h K).ratio T ∘ i)).d a b =
    ((native c').pull (theta (data h' K).ratio U ∘ j)).d a b := by
    intro a b
    change ((separation _ _):ℝ) = ((separation _ _):ℝ)
    rw [Function.comp_apply,Function.comp_apply,Function.comp_apply,Function.comp_apply,agrees hv hh hr,
      agrees hw hh hr']
  cases hx : (native c).pull (theta (data h K).ratio T ∘ i)
  cases hy : (native c').pull (theta (data h' K).ratio U ∘ j)
  rw [hx,hy] at he
  congr; exact funext fun a => funext (he a)

/-- Compare tree inverse *in place*, not replacing either by a different
tree or an averaged kernel. Can pay all displacements across the retained
patch (γ ≤ μ is not enough for exponential depth in ρ, so reserve μ>γ
when using that). `R` in stencil one units; hp & hq in output periods.
Works also when comparing with same period/different tree. -/
theorem columns {c' f' : Side} {h : f.val = c.val*P.L.val} {h' : f'.val = c'.val*P.L.val}
    (T : Forest (data h K).ratio) (U : Forest (data h' K).ratio) (i : κ ↪ Active G T) (j : κ ↪ Active G U)
    {names : κ → Cover × Co P.L (PAC G 1)} {y y'}
    (ht : Copies (data h K) T i y names) (ht' : Copies (data h' K) U j y' names)
    (hx : Larger (G:=G) (data h K)) (hx' : Larger (G:=G) (data h' K))
    {R : ℕ} (hR : Small names R) (hp : 2*R < c.val) (hq : 2*R < c'.val)
    {ρ u a γ μ σ M : ℝ} {H : FaceRow} (hm : 0 ≤ M) (hu : 0 ≤ u) (hs : 0 < σ)
    (hH : H.strip σ M) (ha : 0 < a) (hc : Gap (H.acts f) a) (hd : Gap (H.acts f') a)
    (he : 0 ≤ γ) (hh : γ ≤ μ) (hk : μ < expansion G P K σ M a)
    (k l : κ)
    (hl : ∀ z : Active G T, z ∉ Set.range i →
      ρ ≤ (native c).d (theta _ T (i k)) (theta _ T z))
    (hl' : ∀ z : Active G U, z ∉ Set.range j →
      ρ ≤ (native c').d (theta _ U (j k)) (theta _ U z)) :
    let V := torusPay (Co P.L (PAC G 1)) (expansion G P K σ M a-μ)
    let r := treeFare G P K a
    let B := billing G P K.penalty σ M
    let D := Real.exp ((γ-σ)*R)*B
    let C := V*(r/2+u)⁻¹
    (native c).weight γ (theta _ T (i k)) (theta _ T (i l)) *
      |treeInverse G (data h K) T H u (i l) (i k)-treeInverse G (data h' K) U H u (j l) (j k)| ≤
      windowPrice B V r u μ γ ρ + C*(D+D)*C + windowPrice B V r u μ γ ρ := by
  let S := data h K
  let S' := data h' K
  have hy := native_match i j ht ht' hR hp hq
  intro V r B D C
  have hB : 0 ≤ B := billing_nn G P K.penalty σ M hm
  have hr : 0 < r := treeFare_pos _ _ _ ha
  have hv : 0 ≤ D := mul_nonneg (Real.exp_pos _).le hB
  have hσ : μ ≤ σ := le_trans hk.le (rate_lt hs).le
  apply shared_price i j k l (native c) (native c') (theta _ T) (theta _ U) hl hl' hy
    (treeSchur _ _ hs.le hm hH) (treeSchur _ _ hs.le hm hH) (tree_gap _ _ _ hx ha hc)
    (tree_gap _ _ _ hx' ha hd) (treeVolume (data h K) T (sub_pos.mpr hk))
    (treeVolume (data h' K) U (sub_pos.mpr hk)) _ hu hr hs hB he hh hσ
    (torusPay_nn _ _ (sub_pos.mpr hk)) (add_nonneg hv hv)
  let A := treeMatrix G S T H
  let A' := treeMatrix G S' U H
  let F := shortenMatrix G S T H R
  let F' := shortenMatrix G S' U H R
  have hF : F.submatrix i i = F'.submatrix j j := by
    ext v w
    exact (chargeHere ht hR hp (fullRow G P K.penalty H) v w).trans (chargeHere ht' hR hq _ v w).symm
  rw [show A.submatrix i i-A'.submatrix j j = (A-F).submatrix i i - (A'-F').submatrix j j by simp only [submatrix_sub,Pi.sub_apply,hF]; abel]
  have h1 := (matrix_tail (G:=G) S T R he (hh.trans hσ) hm hH).submatrix i.injective i.injective
  have h2 := (matrix_tail (G:=G) S' U R he (hh.trans hσ) hm hH).submatrix j.injective j.injective
  exact h1.sub (rows_here hy.symm _ h2)
end Lifted
end YM.FreeResolvent
