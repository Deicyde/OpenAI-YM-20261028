import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Drew

/-!
# Borel arms

No appeal to invertible local germs; includes zeros. -/
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

variable (X : Coat T F) (hb : P.Funds S T)
lemma c_measured [Fintype ι] [DecidableEq ι] {a : ι→Site c} {A : x→ Matrix ι ι ℝ} {M : ℕ} (D : Window a M) (he : Borel A) :
    Borel (fun i => D.frameMean (A i)) ∧ Borel (fun i => D.flawed (A i)) := by
  have hp := borel_pad D _ he
  have hh : Borel (fun i=> D.frameMean (A i)) := fun i j=> Measurable.smul (measurable_const (a:=(1/2:ℝ))) ((hp i j).add (hp j i))
  exact ⟨hh,fun i j=> (borel_mul he hh i j).sub (measurable_const (a:= (1:Matrix ι ι ℝ) i j))⟩
lemma intervalB (g : x → ℝ → ℝ) (he : Measurable (fun y:x × ℝ=> g y.1 y.2)) :
    Measurable (fun i => ∫ s in (0:ℝ)..1, g i s) :=
    (he.stronglyMeasurable.integral_prod_right' (ν:=volume.restrict (Set.Ioc 0 1))).measurable.sub
      (he.stronglyMeasurable.integral_prod_right' (ν:=volume.restrict (Set.Ioc 1 0))).measurable
lemma comboB {D : x→ℕ→Mat f G} (he : ∀ i,Borel (fun y=>D y i)) {n : ℕ} (l : Itinerary f n) (i) :
    Borel fun u=>combo i l (D u) := by
  induction n generalizing i D with
  | zero => exact fun j k=> measurable_const (a:=(1:Matrix G.ColorIndex G.ColorIndex ℝ) j k)
  | succ n ih =>
    let p:= Itinerary.next l
    apply borel_mul (A:=fun x=>restrict (D x 0) i p) (D:=fun u => combo p (Itinerary.after l) (fun i => D u (i+1))) (fun a b=> he 0 (i,a) (p,b)); exact ih (fun k=> he (k+1)) (Itinerary.after l) p
lemma stampB {D : x→ℝ→ℕ→Mat f G} (he : ∀ i,Borel (fun v : x×ℝ=> D v.1 v.2 i)) (n : ℕ) (l : Itinerary f n) (i) :
    Measurable fun u=> stamp (D u) i l := by
  refine Finset.measurable_fun_sum _ (fun j _=> ?_)
  apply intervalB (fun u t=> if arrive i l=i then combo i l (D u t) j j else 0)
  split_ifs
  · exact comboB (D:=fun x:x×ℝ=>D x.1 x.2) he l i j j
  exact measurable_const
lemma budding [Fintype ι] [DecidableEq ι] {A : x→ Matrix ι ι ℝ} (h : Borel A) {s : x→ℝ} (hs : Measurable s) :
    Borel (fun i=> glide (A i) (s i)) := by
  intro i j; let a:= (1:Matrix ι ι ℝ) i j; exact measurable_const.add (Measurable.smul hs ((h i j).sub (measurable_const (a:=a))))
lemma amps {A : x→ Mat f G} (h : Borel A) : (∀ i : Ledger f 1, Measurable fun v=>Itinerary.ArmS X.shutter (A v) i) ∧
    (∀ i : Ledger f 3, Measurable fun v=> Itinerary.ArmA X.shutter (A v) i) ∧ (∀ j, Measurable fun v=> Batch.joint (A v) X.shutter j) := by
  let S' := X.shutter
  have hd : Borel fun v : x×ℝ => A v.1 := fun i j=> (h i j).comp measurable_fst
  have hh := Art.budding hd measurable_snd
  have hg := Art.borel_pad X.shutter (fun t:x×ℝ=> glide (A t.1) t.2) hh
  have hp := (c_measured X.shutter hd).2
  have hk : Borel (fun v:x×ℝ=>A v.1-1) := fun i j => (hd i j).sub measurable_const
  refine ⟨fun i=>stampB (D:=fun v=>Itinerary.sSeq X.shutter (A v)) (fun j=> ?_) ..,fun i=>stampB
    (D:=fun v=>Itinerary.aSeq X.shutter (A v)) (fun j=> ?_) ..,fun i=> Finset.measurable_fun_sum _ fun j _=>?_⟩
  · cases j
    · exact hp
    exact fun i j=> (Measurable.smul measurable_snd (hp i j)).neg
  · match j with
    | 0 => exact hk
    | 1 => exact hg
    | _+2 => exact fun i j=> ((borel_mul hh hg _ _).sub (measurable_const (a:= (1:Mat f G) i j))).neg
  apply intervalB (fun v s=> Pulse.intensity X.shutter (A v) s 0 (i,j) (i,j)); simp only [intensity,pow_zero,mul_one]; exact Art.borel_mul hk hg (i,j) (i,j)
end YM.ConnectedActivityE6.Art
