import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Frozen
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Selected
import YM.Push.FREE_RESOLVENT.BlockRate

/-! # Full-address presentation ($I-\mathcal P$ on unintegrated tangent slots)

Keep widths uniform between any shapes paid here. Covariance calculated
with `clouded` on the same extended A, NOT recomputed with any wider set
of affine rows. Comparing endpoints includes all colors and crossing
footprints, no claim about tags at another component yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Full
open Function Filter Lattice RG Pressure Precision Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps
open Next.SectorChange.Completion
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {G : Gauge} {c f : Side} {S : StepData c f}

omit [DecidableEq α] in
lemma embed_rates {C d : ℝ} {x : Coord G c} {A : Coord G c → Matrix α α ℝ} {p : α⊕β→Site c}
    {k : ℕ} (hp : 0 ≤ C) (h : Tagged (p ∘ Sum.inl) (p ∘ Sum.inl) k d C A x) :
    Tagged p p k d (C+1) (fun z => wide (A z) (1:Gaussian.Table β)) x := by
  let L : Matrix α α ℝ →L[ℝ] Gaussian.Table (α⊕β) := LinearMap.toContinuousLinearMap
    ({toFun := fun M => wide M (0:Gaussian.Table β)
      map_add' := by intro A B; ext (i|i) (j|j) <;> simp [wide]
      map_smul' := by intro v B; ext (i|i) (j|j) <;> simp [wide] } :
      Matrix α α ℝ →ₗ[ℝ] Gaussian.Table (α⊕β))
  have he : Tagged p p k d C (fun y => L (A y)) x := by
    constructor
    · exact L.contDiff.contDiffAt.comp x h.smooth
    intro l hl; erw [jet_linear (direction G c) l L (smooth_of_le h.smooth hl)]
    let M := jet (direction G c) A l x
    change Bill _ _ _ _ _ _ _ (wide M (0:Gaussian.Table β))
    have h1 (i : α) := (h.bound l hl).row.rows i
    have h2 (j : α) := (h.bound l hl).col.rows j
    constructor <;> constructor
    · rintro (i|i)
      · rw [Fintype.sum_sum_type]
        simpa only [wide,fromBlocks_apply₁₁,fromBlocks_apply₁₂,Matrix.zero_apply,abs_zero,mul_zero,
          Finset.sum_const_zero,add_zero,Function.comp_apply] using! h1 i
      rw [Fintype.sum_sum_type]; simpa [wide,fromBlocks] using hp
    rintro (i|i)
    · rw [Fintype.sum_sum_type]
      simpa only [wide,Matrix.transpose_apply,fromBlocks_apply₁₁,fromBlocks_apply₂₁,Matrix.zero_apply,abs_zero,
        mul_zero,Finset.sum_const_zero,add_zero,Function.comp_apply] using! h2 i
    rw [Fintype.sum_sum_type]; simpa [wide,fromBlocks] using hp
  let I := wide (0:Gaussian.Table α) (1:Gaussian.Table β)
  have hI : Tagged p p k d 1 (fun _ => I) x := by
    constructor
    · exact contDiffAt_const
    intro l hl; by_cases hz : l=[]
    · subst l; rw [zeroth]; apply Bill.origin
      constructor <;> constructor <;> rintro (i|i) <;> rw [Fintype.sum_sum_type] <;>
        simp [I,wide,Matrix.one_apply,apply_ite abs,mul_ite]
    rw [jet_const _ _ hz]; exact Bill.zero zero_le_one
  have hf : (fun z => wide (A z) (1:Gaussian.Table β)) = fun z => L (A z) + I := by
    funext z; change wide (A z) _ = wide (A z) 0 + wide _ (1:Gaussian.Table β)
    ext (i|i) (j|j) <;> simp [wide]
  rw [hf]; exact he.one_add hI

def point (S : StepData c f) (i : Index G f) : Site c := S.ratio.parent i.1.1

def groupWindow (G : Gauge) (S : StepData c f) (x : ℝ) : Index G f → Set (Index G f) := fun i =>
  { j | meeting S x i.1 j.1 }

lemma full_bars {x : ℝ} (hx : 120 ≤ radiusB x) :
    Bars (groupWindow G S x) (point S (G:=G)) (radiusB x/60) := by
  intro i j he a ha b hb
  have hl := meetings (S:=S) _ ha
  have ht := meetings (S:=S) _ hb
  apply le_trans (separation_triangle a (point S j) b)
  have hs := separation_triangle a (point S i) (point S j)
  have hg : separation a (point S i) ≤ 1 := (separation_comm ..).trans_le hl
  change separation (point S j) b ≤ 1 at ht
  omega

lemma smallWindow (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) :
    panels (x:=x) A F (G:=G) = fun i => Sum.inl ⁻¹' allPanels A F (x:=x) (.inl i) := rfl

def board (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge)
    (B : Gaussian.Table (Rows.In x A F (G:=G))) : Gaussian.Table (Index G f) :=
  (wide B (1 : Gaussian.Table (vacant A F x G))).submatrix (sorted A F).symm (sorted A F).symm

lemma aboard (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge)
    (B : Gaussian.Table (Rows.In x A F (G:=G))) :
    (board x A F G B).submatrix (sorted A F) (sorted A F) = wide B (1:Gaussian.Table (vacant A F x G)) := by
  ext i j; unfold board; simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]

lemma panelInside (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) (hx : 120 ≤ radiusB x)
    (B : Gaussian.Table (Rows.In x A F (G:=G))) (u : ℝ) :
    (panes (groupWindow G S x) u (board x A F G B)).submatrix (sorted A F) (sorted A F)=
      panes (allPanels A F) u (wide B (1:Gaussian.Table (vacant A F x G))) := by
  let e := sorted A F (G:=G) (x:=x)
  rw [reflect_windows (p:=allPanels A F) e (by intro i; rfl) ?_, aboard]
  intro i; exact (full_bars hx (G:=G)) (e i) (e i) (by simp)



lemma active_any (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge)
    {u : ℝ} (hx : 120 ≤ radiusB x) (hu : 0 ≤ u) (B : Gaussian.Table (Rows.In x A F (G:=G)))
    (p q : Rows.In x A F (G:=G)) :
    panes (groupWindow G S x) u (board x A F G B)
        (fundEdge A F p.1,p.2) (fundEdge A F q.1,q.2)=panes (panels A F) u B p q := by
  apply Eq.trans (congr_fun (congr_fun (panelInside x A F G hx B u) (.inl p)) (.inl q))
  let W := allPanels A F (x:=x) (G:=G)
  have hs (i : Rows.In x A F (G:=G)) : Sum.inl i ∈ W (.inl i) := by
    exact per_self (boards A F G hx) i
  have ht := side W B u hu hs (smallWindow x A F G) q p
  convert ht using 2

def deck (x : ℝ) (A : Stores S) (F : Forest S.ratio) (V : Config G c)
    (k : S.Choices) (T : Tube G S) (z : Coord G c) := board x A F G (precision x A F V k T z)

def coverKernel (x : ℝ) (A : Stores S) (F : Forest S.ratio) (V : Config G c)
    (k : S.Choices) (T : Tube G S) (z : Coord G c) := clouded (groupWindow G S x) (deck x A F V k T z)

omit [Fintype α] [Fintype β] [DecidableEq α] in
private lemma wideAverage (Y : Gaussian.Table α) :
    let I := (1:Gaussian.Table β)
    (1/2:ℝ) • (wide Y I + (wide Y I).transpose)=wide ((1/2:ℝ) • (Y+Y.transpose)) I := by
  dsimp only
  ext (i|i) (j|j) <;> first | rfl | simp [wide,Matrix.one_apply,eq_comm]
  split <;> norm_num

omit [Fintype β] in
private lemma reflect_cover {γ : Type} [Fintype γ] [DecidableEq γ] (Q : γ → Set γ)
    (R : α → Set α) (A : Gaussian.Table γ) (B : Gaussian.Table α) (e : (α ⊕ β) ≃ γ)
    (hp : (panes Q 0 A).submatrix e e=wide (panes R 0 B) (drain 0 • (1:Gaussian.Table β))) :
    clouded Q A=(wide (clouded R B) (1:Gaussian.Table β)).submatrix e.symm e.symm := by
  let Z := clouded Q A
  have he : Z.submatrix e e=wide (clouded R B) (1:Gaussian.Table β) := by
    let Y := Schur.per Q A
    rw [panes_zero,panes_zero,show drain 0=1 by simp [drain],one_smul] at hp
    change Y.submatrix e e=_ at hp
    change (1/2:ℝ) • (Y.submatrix e e+(Y.submatrix e e).transpose)=_
    rw [hp]
    apply wideAverage
  change Z=_
  rw [← he]
  ext i j
  rw [Matrix.submatrix_apply,Matrix.submatrix_apply,e.apply_symm_apply,e.apply_symm_apply]



lemma cover_reads (x : ℝ) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices)
    (T : Tube G S) (z : Coord G c) (hx : 120 ≤ radiusB x) (i j : Rows.In x A F (G:=G)) :
    coverKernel x A F V k T z (fundEdge A F i.1,i.2) (fundEdge A F j.1,j.2)=
      sector x A F V k T z i j := by
  let q := precision x A F V k T z
  have he p t := active_any x A F G hx (u:=0) le_rfl q p t
  simp_rw [panes_zero] at he
  let M p : Index G f := (fundEdge A F (Prod.fst (show Rows.In x A F (G:=G) from p)),p.2)
  let Z := Schur.per (groupWindow G S x) (board x A F G q)
  change (1/2:ℝ)*(Z (M i) (M j)+Z (M j) (M i))=_
  rw [show Z (M i) (M j)=_ from he i j, show Z (M j) (M i)=_ from he j i]; rfl

end YM.AnalyticBridge.NonflatCovarianceLocality.Full
