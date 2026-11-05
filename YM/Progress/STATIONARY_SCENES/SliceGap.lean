import YM.Progress.STATIONARY_SCENES.Probe


/-!
# Post-L, flat, uncut no-hole active Hessian inverse

Consumer  inspired. Literal matrix on ANY tested tree,
physical charts. Not a contour estimate, nor differentiation in fields, nor
the more stringent joint matrix gaps (pre-L). Do not infer that cut/affine
versions or interpolations have these bounds -- here not using A_W of any
post-mask-reblocking procedure. No theta scheduling for NONZERO backgrounds
needed; don't use those versions without extra proof!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes
open Filter Lattice RG RG.Supply Wilson Precision Bid Function Matrix Exterior Bloch Tree
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
namespace Green

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {F : Forest S.ratio} {p : Clip} {P : PathData G} {D : Bed}

lemma vertical (t : S.Choices) (h : Prismatic F p P) (hc : Comptroller F D p P)
    (v w : AxisChart G F) :
    iteratedFDeriv ℝ 2 (tested F t p P 0) 0 ![v,w] =
      iteratedFDeriv ℝ 2 (uncurry (tested F t p P)) 0 ![(0,v),(0,w)] := by
  let g := uncurry (tested F t p P)
  let L := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G F)
  change iteratedFDeriv ℝ 2 (g ∘ L) 0 _ = _
  rw [(Work.F03.hessian_comp (g := L) (map_zero L) (show ContDiffAt ℝ 2 g 0 from
    (h t).of_le le_top) (L.contDiff.contDiffAt) ((hc t).2.1)).2,L.fderiv]; rfl

/-- In flat, vertical (H slice) charts. -/
def actual (S : StepData c f) (D : Bed) :=
    K (D.metric.acts f)+ S.kernel.penalty • ((probe S).transpose*probe S)

/-- Even though the stationary action is nonabelian, in these FLAT Hessians
there are no off-color terms. Tree select as principal subset. -/
lemma price_pair (t : S.Choices) (h : Prismatic F p P) (hc : Comptroller F D p P)
    (v w : AxisChart G F) :
    let f (x : AxisChart G F) := parts G 1 (stretch F (0,x))
    iteratedFDeriv ℝ 2 (tested F t p P 0) 0 ![v,w] = ∑ i : G.ColorIndex,
      dotProduct (f v i) (actual S D *ᵥ f w i) := by
  intro g
  rw [vertical t h hc,(hc t).2.2, Work.F04.counting_inner]
  unfold gaugeFiscal; rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
  have he (v : AxisChart G F) : parts G 1 (crop F (0,v)) i = -(probe S *ᵥ g v i) := by
    rw [Work.F04.parts_crop, show parts G 1 (0 : Dir G c) i=0 from rfl]; exact zero_sub _
  rw [actual,Matrix.add_mulVec,dotProduct_add, Matrix.smul_mulVec,dotProduct_smul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ ((probe S).transpose), Matrix.vecMul_transpose,
    he, he, neg_dotProduct,dotProduct_neg, neg_neg]; rfl

/-- Lift a free link to its physical counting index (no coloring). -/
def link (F : Forest S.ratio) : F.Free ↪ Body 1 f :=
    (Function.Embedding.subtype _).trans (Equiv.prodCongr (Equiv.refl _) axisEquiv).toEmbedding

def address (F : Forest S.ratio) (x : Key F G) := x.1.val.1

lemma frame_input (x : Key F G) (i : G.ColorIndex) : parts G 1 (stretch F (0,frame F x)) i =
    if i=x.2 then Pi.single (link F x.1) 1 else 0 := by
  rcases x with ⟨e,b⟩
  ext1 z
  rcases z with ⟨z,j⟩
  obtain ⟨j,rfl⟩ := axisEquiv.surjective j
  change collect G (stretch F (0,frame F (e,b))) (z,j) i = _
  rw [Work.F01.collect_vertical]
  by_cases hh : (z,j)∈F.trunks
  · rw [dif_pos hh]
    have hf : (z,axisEquiv j)≠link F e := by
      intro hZ
      have hz : (z,j)=e.val := (Equiv.prodCongr (Equiv.refl _) axisEquiv).injective hZ
      rw [hz] at hh; exact e.property hh
    split
    · rw [Pi.single_eq_of_ne hf]; rfl
    rfl
  rw [dif_neg hh]
  let l : F.Free := ⟨(z,j),hh⟩
  change frame F (e,b) l i = (ite (i=b) (Pi.single (link F e) 1) (0 : Body 1 f → ℝ)) (link F l)
  unfold frame; by_cases hw : l=e
  · rw [hw]
    by_cases hu : i=b
    · subst i; simp
    simp [hu,EuclideanSpace.basisFun_apply]
  rw [Pi.single_eq_of_ne hw]
  have hx := (link F).injective.ne hw
  split
  · rw [Pi.single_eq_of_ne hx]; rfl
  rfl

lemma entries (t : S.Choices) (h : Prismatic F p P) (hc : Comptroller F D p P)
    (i j : Key F G) :
    hessian F t p P 0 0 i j = if i.2=j.2 then actual S D (link F i.1) (link F j.1) else 0 := by
  rw [hessian, Matrix.of_apply, price_pair t h hc]; simp_rw [frame_input]
  rw [Finset.sum_eq_single i.2]
  · by_cases hh : i.2=j.2 <;> simp [hh]
  · intro b _ hb; rw [if_neg hb]; simp
  simp

lemma symmetric (t : S.Choices) (h : Prismatic F p P) :
    IsHermitian (hessian F t p P 0 0) := by
  have hs := (Work.F05.hold_jet (x := (0: Dir G c)) (y := (0: AxisChart G F)) (h t)).isSymmSndFDerivAt_of_omega
  ext i j; simp_rw [hessian, conjTranspose_apply,star_trivial,of_apply,iteratedFDeriv_two_apply]
  exact hs ..

/-- The ambient invoice for all forests. -/
def reserve (r L : ℕ) (η C k : ℝ) :=
    1+max 0 (kinetic η C + |k| *(sideCount r L η * sideCount r L η))

theorem ticket (t : S.Choices) (hp : Prismatic F p P) (hc : Comptroller F D p P)
    {η C : ℝ} (he : 0 ≤ η) (h : D.metric.strip η C) :
    let H := hessian F t p P 0 0
    let B := reserve S.patch.radius S.patch.L.val η C S.kernel.penalty
    Both (address F) (address F) H η B B := by
  intro H B
  have hw := probe_budget S η he
  have hv : Rows Prod.fst Prod.fst (actual S D) η B := by
    have hc : 0 ≤ fee S.patch.radius S.patch.L.val := by unfold fee; positivity
    have h₁ := Rows.multiply he hw.2 hw.1 (by unfold sideCount; dsimp only; positivity)
    have ha := (kinetic_price f D h he).plus (h₁.pay S.kernel.penalty)
    exact fun i => (ha i).trans ((le_max_right ..).trans ((le_add_of_nonneg_left (by norm_num))))
  have hX (x y : Key F G) := entries t hp hc x y
  have hg : Rows (address F) (address F) H η B := by
    intro i
    apply le_trans _ (hv.restrict (link F) (link F) i.1)
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro y _
    rw [Finset.sum_eq_single i.2]
    · unfold H; rw [hX, if_pos rfl]; exact le_rfl
    · intro x _ hx; unfold H; rw [hX,if_neg (show ¬_ from hx.symm),abs_zero,mul_zero]
    simp
  have hs : H.transpose=H := by
    have he := symmetric t hp; ext i j
    rw [show H.transpose i j=star (H j i) from (star_trivial _).symm]
    exact congr_fun (congr_fun he i) j
  exact ⟨hg,hs.symm ▸ hg⟩

lemma basis_count (x : AxisChart G F) :
    let B := Work.F05.countingBasis F G
    ∑ i, ‖x i‖^2 = dotProduct (B.equivFun x) (B.equivFun x) := by
  intro B
  let a := B.equivFun x
  have he (y : Key F G) : x y.1 y.2 = a y := by
    let dot : AxisChart G F →ₗ[ℝ] ℝ := (LinearMap.comp (LinearMap.proj y.2)
      (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color →ₗ[ℝ] ℝ).comp (LinearMap.proj y.1)
    calc
      x y.1 y.2 = dot x := rfl
      _ = dot (∑ i, a i • B i) := by rw [show (∑ i, a i • B i) = x from B.sum_equivFun x]
      _ = _ := by
        rw [map_sum,Finset.sum_eq_single y]
        · rw [map_smul]; change a y * dot (B y) = _
          unfold B; rw [Work.F05.countingBasis_apply]; change a y * frame F y y.1 y.2 = _
          simp [frame]
        · rintro ⟨x,i⟩ _ hi; rw [map_smul,show B (x,i)=_ from Work.F05.countingBasis_apply F G (x,i)]
          change a (x,i) * frame F (x,i) y.1 y.2 = _
          by_cases hh : y.1=x
          · have hk : y.2 ≠ i := fun H => hi (Prod.ext hh.symm H.symm)
            simp [frame, hh,hk, EuclideanSpace.basisFun_apply]
          unfold frame; rw [Pi.single_eq_of_ne (show y.1 ≠ _ from hh)]; simp
        simp
  rw [dotProduct,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl; intro b _
  rw [he (i,b),pow_two]

lemma counted (t : S.Choices) {r : ℝ} (h : PriceGap F p P r) :
    Bottom (hessian F t p P 0 0) r := by
  let B := Work.F05.countingBasis F G
  intro v
  have hh := basis_count (S := S) (F := F) (B.equivFun.symm v)
  change _ = dotProduct (B.equivFun (B.equivFun.symm v)) _ at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  rw [← hh, Work.F05.hessian_eq]
  have he := dotProduct_toMatrix₂_mulVec B B (Work.F05.bend (tested F t p P 0) 0) v v
  apply le_trans (h t _); apply le_of_eq
  exact (Work.F05.bend_apply _ _ _ _).symm.trans he.symm

/-- Freeze THESE costs immediately after buying eta; before β, p's/waits, N's
and path correction work. Physical applicability on the priced stages below. -/
def factor (r C : ℝ) := min 1 ((r/2)/C)


end Green

open Green
variable {G : Gauge}


end YM.Progress.StationaryScenes
