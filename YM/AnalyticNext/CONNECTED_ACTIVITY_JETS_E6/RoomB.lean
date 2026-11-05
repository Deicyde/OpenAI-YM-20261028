import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood

/-!
# Read the varying V and optional rows

Compact weights only afterwards; this just BOREL measurable on the true charts.
Enrollment uses actual guards. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Art
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open  Ursell Trees   
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {x : Type*} [MeasurableSpace x] {ι κ τ : Type*}

lemma tableB [Fintype κ] {V : x→Config G c} {D : Config G c→ ι→κ→Pay G} {Y : x→ κ→G.Color}
    (he : ∀ i j, Continuous (fun a=> D a i j)) (hv : Measurable V) (hp : ∀ i, Measurable (fun x=> Y x i)) (i : ι) :
    Measurable (fun x => zip (D (V x)) (Y x) i) := by
  refine Finset.measurable_fun_sum _ fun j _=> ?_
  have h : Continuous fun a : Config G c× G.Color=> D a.1 i j a.2 := ((he i j).comp (f:= Prod.fst) continuous_fst).clm_apply continuous_snd
  exact h.measurable.comp (hv.prodMk (hp j))
lemma retabB [Fintype ι] {V : x→Config G c} {D : Config G c→ ι→κ→Pay G} {Y : x→ ι→G.Color}
    (he : ∀ i j, Continuous (fun a=> D a i j)) (hv : Measurable V) (hp : ∀ i, Measurable (fun x=> Y x i)) (i : κ) :
    Measurable (fun x => unzip (D (V x)) (Y x) i) := by
  change Measurable (fun p=> zip (fun j k => (D (V p) k j).adjoint) (Y p) i)
  apply tableB (D:=fun v j k=> (D v k j).adjoint) _ hv hp
  intro i j; exact ContinuousLinearMap.adjoint.continuous.comp (f:=fun a=>D a j i) (he j i)

lemma census_o (h : P.Funds S T) {U : x→ Config G f} {V : x→Config G c} (hu : Measurable U) (hv : Measurable V)
    (k : S.Choices) (α : ℝ) :
      let R:=till α; let _t:=Pressure.temp α
      (∀ i : Rod c f, Measurable (fun y=> guide T α (V y) i) ∧
        Measurable (fun y=> entryCost T R (U y) k (V y) i)) ∧
      ∀ i, Measurable (fun y=> Coat.principal T α (U y) (V y) (S.prediction (U y) k) i) ∧
        Measurable (fun y=> Coat.yielding T α (U y) (V y) k i) := by
  intro R t
  have hk := (S.prediction_meas (funds_branch h) k).comp hu
  obtain ⟨v₁,v₂,hp,ht⟩:=h.feeds; rw [← h.low] at ht; rw [← h.high] at hp
  obtain ⟨A,B,D,-⟩ := h.crosses
  have hc1 i j : Continuous (fun x=> T.Φ R x i j) := leap_cont (Row.rights _ _ D P.width.le) ..
  have hc2 i j : Continuous (fun x=> T.Φ' R x i j) := lane_cont (Row.rights _ _ A P.width.le) ..
  have hc3 i j : Continuous (fun x=> T.N R x i j) := lane_cont (Row.rights _ _ B P.width.le) ..
  have H₁ (i) : Measurable fun y=> T.vision R t (V y) i := (measurable_pi_apply i).comp ((SectorMeasure.env_read ht
    R S.patch.L.val t (temp_nonneg α)).meas.comp hv)
  have H₂ i : Measurable fun y=> T.Xn R (V y) i := (plotted_cont ht R S.patch.L.val i).measurable.comp hv
  have W₁ i : Measurable (fun y=> T.Xf R (U y) i) := (plotted_cont hp R 1 i).measurable.comp hu
  have W₂ i : Measurable fun y=>Tube.Z S (S.prediction (U y) k) (V y) i :=
    ((show Continuous (fun r : Config G c × Config G c => Tube.Z S r.2 r.1 i) by unfold Tube.Z; fun_prop).measurable.comp (f:=fun i=> (V i,S.prediction (U i) k)) (hv.prodMk hk))
  have hv' i : Measurable (fun y=> T.Mv R t (V y) i) := tableB hc1 hv (Y:=fun y=>T.vision R t (V y)) H₁ i
  have hU i : Measurable (fun y=> T.Mw R t (V y) i) := tableB hc2 hv (Y:=fun y=>T.vision R t (V y)) H₁ i
  have hj {A B : x→G.Color} (h : Measurable A) (hp : Measurable B) : Measurable (fun y=> inner ℝ (A y) (B y)) :=
    (show Continuous (fun i : G.Color×G.Color=> inner ℝ i.1 i.2) by fun_prop).measurable.comp (h.prodMk hp)
  have h3 i := tableB hc3 hv (Y:=fun y=> T.vision R t (V y)) H₁ i
  refine ⟨fun i=> ?_,fun i=> ?_⟩
  · rcases i with i|i
    · exact ⟨hv' i,W₁ i⟩
    exact ⟨hU i,W₂ i⟩
  obtain ⟨hz,hT⟩ := env_cuts h α hu hv
  rcases i with i|i|i|i
  · refine ⟨(hz i).meas.add (Finset.measurable_fun_sum _ fun p _=>
      (((hv' (i,p)).norm.pow_const (2:ℕ)).div_const _).sub (hj (hv' (i,p)) (W₁ (i,p)))),?_⟩
    let W:= G.El; have hP : Measurable (fun y=> T.high.direct*flaw (faceValue (U y) i)) :=
      ((show Continuous (fun U=> T.high.direct*flaw (G:=G) (faceValue U i)) by unfold flaw faceValue; fun_prop).measurable.comp hu)
    exact hP.add (Finset.measurable_fun_sum _ fun p _=> (((W₁ (i,p)).sub (hv' (i,p))).norm.pow_const (2:ℕ)|>.div_const _))
  · have hh (p) : Measurable fun y=> monetary S (S.prediction (U y) k) (V y) p :=
      (show Continuous (fun v: Config G c × Config G c=> monetary S v.1 v.2 p) by unfold monetary wire; fun_prop).measurable.comp (f:=fun i=>(S.prediction (U i) k,V i)) (hk.prodMk hv)
    have hy := (hh i).add ((((hU i).norm.pow_const (2:ℕ)).div_const 2).sub (hj (hU i) (W₂ i)))
    exact ⟨hy,hy⟩
  · have hl j := retabB hc1 hv (Y:= fun v=> T.Xf R (U v)) W₁ j
    have hX j := retabB hc2 hv (Y:=fun v=> Tube.Z S (S.prediction (U v) k) (V v)) W₂ j
    have hc := Finset.measurable_fun_sum univ (fun (p : Bool) _ =>
      (hj (H₁ (i,p)) (H₂ (i,p))).sub (((H₁ (i,p)).norm.pow_const (2:ℕ)).div_const 2))
    have HD := Finset.measurable_fun_sum univ (fun (p : Bool) _=> hj (H₁ (i,p)) (((hl (i,p)).add (hX (i,p))).sub (H₂ (i,p))))
    have h4 j := retabB hc1 hv (Y:=fun v=> T.Mv R t (V v)) hv' j
    have h5 j := retabB hc2 hv (Y:=fun v=> T.Mw R t (V v)) hU j
    have h6 j := retabB hc3 hv (Y:=fun v=>zip (T.N R (V v)) (T.vision R t (V v))) h3 j
    have HF := Finset.measurable_fun_sum univ (fun (p : Bool) _=> (hj (H₁ (i,p)) ((H₁ (i,p)).sub
      (((h4 (i,p)).add (h5 (i,p))).add (h6 (i,p))))|>.div_const 2))
    have hy := (hc.sub (hT i).meas).add (HD.add HF)
    exact ⟨hy,hy⟩
  have he := ((h3 i).norm.pow_const (2:ℕ)).div_const 2; exact ⟨he,he⟩
end YM.ConnectedActivityE6.Art
