import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Street

/-!
# Stencil geometry Borel in V/Y (finite period). Matrices, through chart.

One must carry relative chart WITH reference moving, not approximate by
factorization at one V for V families. No smooth claims about thresholds. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Art
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {x : Type*} [MeasurableSpace x] {ι κ τ : Type*}

abbrev Borel (A : x→Matrix ι κ ℝ) := ∀ i j, Measurable fun p=> A p i j
lemma borel_mul [Fintype κ] {A : x→Matrix ι κ ℝ} {D : x→ Matrix κ τ ℝ} (h : Borel A) (hp : Borel D) :
    Borel (fun i=>A i*D i) := by intro j k; simp_rw [Matrix.mul_apply]; exact Finset.measurable_fun_sum _ fun i _=> (h _ _).mul (hp _ _)
lemma borel_times [Fintype κ] {A : x→Matrix ι κ ℝ} {d : x→κ→ℝ} (h : Borel A) (hp : ∀ i,Measurable (fun p=>d p i)) (i : ι) :
    Measurable fun p=> (A p*ᵥd p) i := Finset.measurable_fun_sum _ fun k _=> (h i k).mul (hp k)
lemma det_m [Fintype ι] [DecidableEq ι] {A : x→Matrix ι ι ℝ} (h : Borel A) : Measurable fun p=> (A p).det := by
  let f p:=(fun i j=> A p i j)
  have he : Measurable f := measurable_pi_lambda _ fun i=> measurable_pi_lambda _ (h i)
  exact ((show Continuous (fun v:ι→ι→ℝ => (Matrix.of v).det) from Continuous.matrix_det (by fun_prop)).measurable).comp he
lemma inverse [Fintype ι] [DecidableEq ι] {A : x→Matrix ι ι ℝ} (h : Borel A) : Borel fun p => (A p)⁻¹ := by
  let f p:=(fun i j=> A p i j)
  have he : Measurable f := measurable_pi_lambda _ fun i=> measurable_pi_lambda _ (h i)
  have hh (i j : ι) : Measurable (fun p=> (A p).adjugate i j) :=
    ((continuous_apply_apply i j).comp (Continuous.matrix_adjugate (show Continuous (fun v : ι→ι→ℝ=> Matrix.of v) by fun_prop))).measurable.comp he
  intro i j
  have hv (X : Matrix ι ι ℝ) : X⁻¹ i j=X.det⁻¹ • X.adjugate i j := by change Ring.inverse X.det • X.adjugate i j= _; rw [Ring.inverse_eq_inv]
  simp_rw [hv]; exact Measurable.smul (det_m h|>.inv) (hh i j)
lemma borel_pad [Fintype ι] [DecidableEq ι] {a : ι→Site c} {n : ℕ} (W : Window a n) (A : x → Matrix ι ι ℝ)
    (h : Borel A) : Borel (fun i=> W.pad (A i)) := by
  intro i j
  by_cases he : i∈W.take j
  · simp_rw [W.inside _ j ⟨i,he⟩]; exact Art.inverse (A:=fun i => W.principal (A i) j) (fun i j=> h _ _) ..
  simp_rw [W.outside _ i j he]; exact measurable_const

lemma loyal : Continuous (replica S.ratio (G:=G)) := by unfold replica; apply continuous_pi; intro i; split <;> fun_prop
lemma optical (G : Gauge) : Continuous (fun p : G.El×G.Color => G.adjoint p.1 p.2) :=
    G.projectColor.continuous_of_finiteDimensional.comp (show Continuous _ by unfold Gauge.conjugate; fun_prop)

/-- improv identity flat specialization for continuity. -/
lemma alongRow (X : Coat T F) (h : P.Funds S T) (s : Signed) (i : Rod c f) : Continuous
    (fun x : Config G c × Directions G f => orientedRow T X.R s i x.1 x.2) := by
  unfold orientedRow straightened
  obtain ⟨b,r,hp,-⟩:=h.feeds
  obtain ⟨Z,hZ⟩:= SliceRows.linear T X.R hp 1 i 1
  have he u : barField T X.R u i=Z u := by rw [hZ,turns_here,flat_strip]
  let D (x : Config G c × Directions G f) := displacement s x.2 (replica S.ratio x.1)
  have hh : Continuous D := by
    apply continuous_pi; intro i; unfold D displacement; dsimp only; split
    next hz =>
      have ht := ((continuous_apply (A:=fun _ : Bond f=> G.El) (Channel.edge s i)).comp ((Art.loyal (S:=S) (G:=G)).comp (continuous_fst (Y:=Directions G f))))
      have hg (w : Bond f) : Continuous (fun p : Config G c × Directions G f => p.2 w) := by fun_prop
      have he : Continuous (fun x:Config G c × Directions G f=> ((replica S.ratio x.1 (edge s i))⁻¹,x.2 (edge s i))) := by
        refine Continuous.prodMk ?_ (hg _)
        change Continuous (fun p=> ( _ )⁻¹)
        exact (show Continuous (fun p:Config G c × Directions G f=> replica S.ratio p.1 (edge s i)) from ht).inv
      exact ((optical G).comp (f:=fun x:Config G c×Directions G f=> ((replica S.ratio x.1 (edge s i))⁻¹,x.2 (edge s i))) he).neg
    next hz => exact (continuous_apply (A:=fun _:Bond f=> G.Color) (Channel.edge s i)).comp continuous_snd
  simp_rw [he]; refine Z.continuous.comp ?_; apply continuous_pi; intro j
  have ht := (continuous_pull (G:=G) s (0:Site c)).comp (continuous_fst (Y:=Directions G f))
  let f' (x : Config G c × Directions G f) : G.El × G.Color := (carrier (focus S i) (pull s 0 x.1) (atEdge S j), D x j)
  have hg : Continuous (fun x:Config G c×Directions G f=> D x j) := (continuous_apply (A:=fun _:Bond f=>G.Color) j).comp hh
  have hv : Continuous (fun p:Config G c×Directions G f=> carrier (focus S i) (pull s 0 p.1) (atEdge S j)) := (continuous_travel (G:=G) (carriage (focus S i) (atEdge S j)) (focus S i)).comp ht
  change Continuous (fun p=> G.adjoint (f' p).1 (f' p).2)
  exact (optical G).comp (show Continuous f' from hv.prodMk hg)

variable (X : Coat T F) (h : P.Funds S T)
include h
lemma borel_form : Borel fun v=> (vary X v).form := by
    intro i j; change Measurable fun v=> Coat.scale*stand ((vary X v).motion (sing j)) i
    have hi : Measurable fun v=> (vary X v).motion (sing j) i.1 := by
      change Measurable fun v=> if X.selected i.1.1 (spot S i.1.2) then orientedRow T X.R i.1.1 i.1.2 v (X.lens (sing j)) else 0
      by_cases hk : X.selected i.1.1 (spot S i.1.2)
      · simp_rw [if_pos hk]
        have hp : Continuous (fun v:Config G c=> (v,X.lens (sing j))) := continuous_id.prodMk continuous_const
        exact ((alongRow X h i.1.1 i.1.2).comp (f:=fun v:Config G c=> (v,X.lens (sing j))) hp).measurable
      simp_rw [if_neg hk]; exact measurable_const
    exact measurable_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) i.2).measurable.comp hi)
lemma borel_plate : Borel fun v=> (vary X v).plate := by
  have he:= borel_form X h
  intro i j
  have hg : Borel fun v=> (vary X v).form.transpose := fun i j=> he j i
  exact (borel_mul hg he _ _).add (measurable_const (a:= X.sleepy i j))
end YM.ConnectedActivityE6.Art
