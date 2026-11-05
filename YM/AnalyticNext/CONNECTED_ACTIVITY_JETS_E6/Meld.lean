import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cincture
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Facility
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tablet

/-!
# Real extended spatial formula. Marginalization at FULL original stencil

No receipts off healthy. BOREL representatives; no claim that this Polar is
smooth on rank-changing corners. Keep F.Slice complete W. Uses unclipped
V queries only (even incident) for logH in output P. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Shield
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine  Frond Corona Brush   Tablet Strokes Quill Bid Matter
open Packets Art  Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type*} [MeasurableSpace E]
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Q : YM.ConnectedActivityE6.Target G P}
variable {V : E→ Config G c} {U : E→ Config G f} {w : E → Directions G f} {u : E→ Air f G} {o : Target.Order G W} {χ : Chi}
variable (h : P.Funds S T) (he : Measurable V)
include h he
lemma visualB (V' : ℝ) (i : Rod c f) : Measurable (fun y=> Scroll.visual T (till V') (V y) i) := by
  obtain ⟨b,c,hp,hq⟩ := h.feeds; rw [← h.low] at hq; let R:=till V'; obtain ⟨A,B,D,-⟩:=h.crosses
  have hc1 i j : Continuous (fun x=> T.Φ R x i j) := leap_cont (Row.rights _ _ D P.width.le) ..
  have hc2 i j : Continuous (fun x=> T.Φ' R x i j) := lane_cont (Row.rights _ _ A P.width.le) ..
  have hf i : Measurable fun y=> T.Xn R (V y) i := (plotted_cont hq R S.patch.L.val i).measurable.comp he
  rcases i with i|i
  · exact tableB hc1 he hf i
  exact tableB hc2 he hf i
lemma liftB (k : S.Choices) (x : ℝ) (b : Bool) (i : Spot c f) (hu : Measurable U) :
    Measurable (fun y=>loft T x (U y) k (V y) b i) := by
  let Z t:= S.prediction (U t) k; let R:=till x
  obtain ⟨A,B,hp,hq⟩:= h.feeds
  rw [← h.high] at hp; rw [← h.low] at hq
  have hz j : Measurable (fun y=> effective T R (U y) (Z y) (V y) j) := ((Art.census_o h hu he k x).1 j).2.sub (visualB h he x j)
  obtain ⟨A,B,D,-⟩:=h.crosses
  have hc1 i j : Continuous (fun x=> T.Φ R x i j) := leap_cont (Row.rights _ _ D P.width.le) ..
  have hc2 i j : Continuous (fun x=> T.Φ' R x i j) := lane_cont (Row.rights _ _ A P.width.le) ..
  have hc3 i j : Continuous (fun x=> T.N R x i j) := lane_cont (Row.rights _ _ B P.width.le) ..
  have hf i : Measurable fun y=> T.Xn R (V y) i := (plotted_cont hq R S.patch.L.val i).measurable.comp he
  have hv i : Measurable fun y=> T.Xf R (U y) i := (plotted_cont hp R 1 i).measurable.comp hu
  have hC : Measurable Z:= (S.prediction_meas (funds_branch h) k).comp hu
  have hN i : Measurable fun y=>canopyN T R (V y) i := tableB hc3 he hf i
  have hj {A B : E→ G.Color} (ha : Measurable A) (hb : Measurable B) : Measurable (fun y=> inner ℝ (A y) (B y)) :=
      (show Continuous (fun p : G.Color × G.Color=> inner ℝ p.1 p.2) by fun_prop).measurable.comp (ha.prodMk hb)
  rcases i with i|i|i|i
  · cases b
    · refine ((env_crown hp R 1 _ i).meas.comp hu).add (Finset.measurable_fun_sum _ fun j _=> ?_)
      have hh:= visualB h he x (.inl (i,j)); exact ((hh.norm.pow_const (2:ℕ)).div_const 2).sub (hj hh (hv (i,j)))
    exact (((show Continuous (fun U=> T.high.direct*flaw (G:=G) (faceValue U i)) by unfold flaw faceValue; fun_prop).measurable.comp hu).add
      (Finset.measurable_fun_sum _ fun j _=> (((hz (.inl (i,j))).norm.pow_const (2:ℕ)).div_const 2)))
  · have hF : Continuous fun p : Config G c× Config G c=> S.kernel.penalty*flaw (p.1 i*(p.2 i)⁻¹) := by unfold flaw; fun_prop
    exact (hF.measurable.comp (he.prodMk hC)).add (((hz (.inr i)).norm.pow_const (2:ℕ)).div_const 2)
  · have hk : Measurable (fun y=> Scroll.stormL T R (U y) (Z y) (V y) i) := by
      apply Finset.measurable_fun_sum; intro p _; refine hj (hf _) ((((retabB hc1 he hv _).add (retabB hc2 he ?_ _))).sub (hf _))
      intro b; exact ((census_o h hu he k x).1 (.inr b)).2
    have hh : Continuous (fun x:Config G _=> Scroll.stormC T x i) := by unfold stormC flaw faceValue; fun_prop
    refine (hh.measurable.comp he).add (hk.add ?_)
    apply Finset.measurable_fun_sum; intro p _; exact (hj (hf _) ((hf _).sub
      (((retabB hc1 he (fun i=> tableB hc1 he hf i) _).add (retabB hc2 he (fun i=> tableB hc2 he hf i) _)).add
      (retabB hc3 he hN _)))).div_const _
  exact ((hN i).norm.pow_const (2:ℕ)).div_const 2

variable (X : Coat T F) {Y : E → F.Slice G} (hp : Measurable Y) (hΞ : ShellAccess S G X.x W X.width γ)
include hp hΞ
lemma strains (hw : Measurable w) (s : Signed) (p : Rod c f) : Measurable (fun t=> strain (drive X (V t) (Y t)) s p (w t)) := by
  let Z x:= pull s 0 (V x); have hz : Measurable Z := (continuous_pull s (0:Site c)).measurable.comp he
  have hu := (census_o h (U:=fun x:E=> (1:Config G f)) measurable_const hz (choice s X.k) X.x).1 p
  have hv (t : E) : strain (drive X (V t) (Y t)) s p (w t)=(drive X (V t) (Y t)).realPath s p (w t) +
      guide T X.x (Z t) p- Scroll.visual T (till X.x) (Z t) p := by
    unfold strain Coat.realPath freely request; dsimp only [Art.drive,vary,wrapY,Z,Coat.R]; abel
  simp_rw [hv]; exact ((Art.tumbling X h hΞ he hp hw s p).add hu.1).sub (visualB h hz X.x p)

lemma compassBro (β : ℝ) :
    let Z t:=drive X (V t) (Y t); Measurable (fun i=> voltage (Z i)) ∧ (∀ p : Tubular f G, Measurable fun i=> shimmer (Z i) β p) ∧
      ∀ u : E→ Air f G, Measurable u → Measurable (fun i=> worldZ (Z i) β (u i)) := by
  intro Z; have hF : Borel fun i=> (Z i).plate := fun i j=> (borel_plate X h i j).comp he
  have hb k : Measurable fun t=> Vine.leanB (Z t) k := by
    have hh j : Measurable fun i=> bar (Z i) 0 j := by
      change Measurable fun i=> if X.selected _ _ then _ else 0; split_ifs
      next => exact Measurable.smul (measurable_const (a:=Coat.scale)) (strains h he X hp hΞ (w:=fun _=> 0) measurable_const j.1 j.2)
      exact measurable_const
    exact Art.borel_times (fun i j=> (Art.borel_form X h j i).comp he : Borel (fun i=> (Z i).form.transpose))
      (d:=fun i=> stand (bar (Z i) 0)) (fun i=> (EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) i.2).measurable.comp (hh i.1)) k
  have hh i : Measurable fun t=> well (Z t) i := (borel_times (d:=fun i=> leanB (Z i))
    (fun i j=> Art.borel_pad X.shutter _ hF j i : Borel fun t=> (Z t).kernelA.transpose) hb i).neg
  have hV : Measurable fun i=> voltage (Z i) := measurable_pi_lambda _ (fun i=>
    (WithLp.measurable_toLp _ _).comp (measurable_pi_lambda _ (fun j=> hh (i,j))))
  refine ⟨hV,fun i=> (measurable_const (a:= -(gStep β)⁻¹)).smul ((borel_times (d:=fun i=> well (Z i)) hF hh _).add (hb i)),?_⟩
  intro u hu
  exact hV.add (Measurable.smul (measurable_const (a:=gStep β)) (measurable_pi_lambda _ fun i=> (X.tale i).measurable.comp hu))
end YM.ConnectedActivityE6.Blaze.Shield
