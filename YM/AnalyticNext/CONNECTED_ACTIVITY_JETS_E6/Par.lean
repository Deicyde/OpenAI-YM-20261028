import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ColorB
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Meld
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Polar

/-!
# Measurability bare. No Yankee puncture branch, no regularity apart
 from true representatives. Density attempted even at zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Shield
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid Matter
open Packets Art  Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type*} [MeasurableSpace E]
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Ñ : ChartRatio G}
variable {V : E→ Config G c} {U : E→ Config G f} {w : E → Directions G f} {u : E→ Air f G} {Y : E→ F.Slice G}
variable (X : Coat T F) (hΞ : ShellAccess S G X.x W X.width γ) (h : Intake P T X.x R) (hP : LocalRatio Ñ)
variable (he : Measurable V) (hp : Measurable Y) (hv : Measurable u)

include h he in
private lemma remnants (i : LogLetter c f) (hu : Measurable U) : Measurable fun t => nest T X.x (V t) (U t) R i := by
  rcases i with i|i|i|i|i|i
  · simpa only [Function.comp_def,nest,expo,Sum.elim] using! ((rawlog_b h (1:Config G c) (.inl i)).comp hu)
  · simpa only [Function.comp_def,nest,expo,Sum.elim] using! ((rawlog_b h (1:Config G c) (.inr (.inl i))).comp hu)
  · simpa only [Function.comp_def,nest,expo,Sum.elim] using! ((rawlog_b h (1:Config G c) (.inr (.inr (.inl i)))).comp hu)
  · simpa only [Function.comp_def,nest,expo,Sum.elim] using! ((rawlog_b h (1:Config G c) (.inr (.inr (.inr (.inl i))))).comp hu)
  · simpa only [Function.comp_def,nest,expo,Sum.elim] using! ((rawlog_b h (1:Config G c) (.inr (.inr (.inr (.inr (.inl i)))))).comp hu)
  have hF : Continuous fun U:Config G c=>icicle T.down U X.R S.patch.L.val (-(-orientation*R.beta)) i := by
    unfold icicle Polar.twin; split_ifs
    next ht => unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
    next ht=> exact continuous_const
  exact hF.measurable.comp he

include hΞ h hP he hp hv
lemma bornB (a : ℝ) (l : ℕ) (k : Finset ℕ) (i : Head S) :
    let Z t:=drive X (V t) (Y t); let z t:= worldZ (Z t) R.beta (u t); let f t:= (Z t).input (z t)
    Measurable (fun t=> Polar.ember (Z t) a R W Ñ (z t) (f t) (u t) k l i) := by
  intro Z z f
  obtain ⟨hf,hM,hQ⟩:=compassBro h.ready he X hp hΞ R.beta
  have ht:=hQ u hv; have hF := Art.entering X he hp ht
  obtain ⟨hu,hx⟩:=Art.terror (W:=W) X h.ready he hp ht k R
  have hh p := ((Art.royal X h.ready hΞ he hp hv R.beta).1 p)
  have hK p i {w:E → Directions G _} (he' : Measurable w) : Measurable fun t=> Vine.costs (Z t) (w t) p i := by
    refine Finset.measurable_fun_sum _ fun j _=> ?_
    change Measurable fun i=> if X.selected _ _ then _ else 0; split_ifs
    · exact (((Shield.strains h.ready he X hp hΞ he' p j).norm.pow_const 2).div_const 2)
    exact measurable_const
  have hC (s) i b : Measurable fun t=> rootface (Z t) (z t) (f t) b s i :=
    (liftB h.ready ((continuous_pull s (0:Site c)).measurable.comp he) (choice s X.k) X.x b i ((continuous_pull ..).measurable.comp hF)).sub (hK _ _ ht)
  have hz : ∀ i, Measurable fun t=> Vine.costs (Z t) (voltage (Z t)) 1 i := fun i=> hK _ _ hf
  rcases i with i|i|i|i
  · let O:= i.dome (300*X.B)
    change Measurable fun t=> ite (connected S l X.B i) (Polar.stock (Z t) a R W Ñ (z t) (f t) k i) 0
    split_ifs
    · change Measurable fun t=> ite (i.place⊆X.seeds.place ∧ i.flags=∅) (Real.exp (plumeLog (Z t) a R Ñ (z t) (f t) i)*
        Contract.order R k (vias S i (300*X.B)) (f t)* Mask.tickets i _ (f t) X.k*Mask.profiles i X.χ _ X.x W (f t) X.k (V t)*X.enforce a (z t) (X.plaza (i.dome (304*X.B)))) 0
      split_ifs
      · let u t:= plumeLog (Z t) a R Ñ (z t) (f t) i
        have h : Measurable fun t=> chalky (Z t) (z t) (f t) i := measurable_const.mul (Finset.measurable_fun_sum _ fun s _=>
          Finset.measurable_fun_sum (posted (turnStore s i) (200*X.B)) fun j _=> hC _ _ false)
        have h' : Measurable fun t=> crispy (Z t) i := measurable_const.mul (Finset.measurable_fun_sum _ fun s _=>
          Finset.measurable_fun_sum (posted (turnStore s i) (200*X.B)) fun j _=> hK _ _ hf)
        have hι: Measurable u := ((((measurable_const (a:=-R.beta)).mul (h.add h')).add (Finset.measurable_fun_sum
          (visit i (200*X.B)) fun i _=> hh _)).add (Finset.measurable_fun_sum (X.plaza (i.dome (304*X.B))) fun i _=> (X.gentry_b i _ hP a).comp ht)).sub
          (measurable_const (a:= (X.pens i).card * Real.log (measure_g Ñ R.beta)))
        exact (((((Real.measurable_exp.comp hι).mul (Finset.measurable_fun_prod _ (fun j _=> (contract_b ..).comp hF))).mul (Measurable.mul
          (Finset.measurable_fun_prod O (fun j _=>hu (.inr (.inr (.inr (.inl j)))) i))
          (Finset.measurable_fun_prod (readBonds O) fun j _=> hu (.inr (.inr (.inl j))) i))).mul ((Finset.measurable_fun_prod
          (readFine O S) (fun j _=> hu (.inl j) i)).mul (Finset.measurable_fun_prod (readBonds O) (fun j _=>hu (.inr (.inl j)) i)))).mul ((X.enforce_b ..).comp ht))
      exact measurable_const
    exact measurable_const
  · exact ((h.cap.labels.forced.meas i).comp hF).mul ((X.enforce_b (2*a) (X.plaza (forcedFoot S.ratio 0 X.B R i))).comp ht)
  · refine (Real.measurable_exp.comp (?_ : Measurable fun t=> logMoment (Z t) a R Ñ (z t) (f t) (u t) i)).sub measurable_const
    rcases i with i|i|i
    · exact (remnants X h he i hF).mul ((X.enforce_b _ (X.plaza (space T 0 X.B R i))).comp ht)
    · rcases i with i|i|i
      · change Measurable fun t=> if Inside (rowSite S i) X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation * _
        split_ifs
        · exact measurable_const
        exact measurable_const.mul ((((X.enforce_b (2*a) (X.booth _)).comp ht).mul (hC i.1 i.2 true)).add (hK i.1 i.2 hf))
      · change Measurable fun t=> if voyage X.seeds (200*X.B) i then 0 else _; split_ifs
        · exact measurable_const
        exact hh i
      change Measurable fun t=> if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then X.gentry Ñ a (z t) i else 0; split_ifs
      · exact (X.gentry_b _ _ hP _).comp ht
      exact measurable_const
    have hb : Borel fun p=> (Z p).plate := fun i j=> (borel_plate X h.ready i j).comp he
    have hB := amps X hb
    have hL k : Measurable fun t=>Polar.patch (Z t) a (z t) k := by
      change Measurable fun t=> if X.Hot k then X.cone (2*a) (z t) k else 1; split_ifs
      · exact (X.cone_b _ _).comp ht
      exact measurable_const
    have hA (p : Tubular _ G) : Measurable fun t=> WithLp.ofLp (u t) p := (EuclideanSpace.proj (𝕜:=ℝ) p).measurable.comp hv
    rcases i with i|i|i|i|i
    · exact ((hB.2.1 i).neg.div_const 2)
    · exact ((Art.royal X h.ready hΞ he hp hv R.beta).2 (.inr (.inl i)) a)
    · exact ((hB.1 i).div_const 2)
    · exact (hL i).mul (Finset.measurable_fun_sum _ fun k _=> (hA (i,k)).mul (hM _))
    have hz k : Borel fun t=> (Z t).finale i.1 k := by
      unfold finale; split_ifs
      · exact fun u v=> ((c_measured X.shutter hb).2 u v).neg
      exact hb
    have hC : Borel fun t=> combo i.2.1 i.2.2 ((Z t).finale i.1) := comboB (D:=fun i k=> (Z i).finale _ k) hz _ _
    exact ((hL i.2.1).mul (hL (arrive i.2.1 i.2.2))).mul ((measurable_const (a:=(1/2:ℝ))).mul (Finset.measurable_fun_sum _
      fun x _=> (hA _).mul (Finset.measurable_fun_sum _ fun j _=> (hC x j).mul (hA _))))
  exact hx i a

lemma collectionB (k : Finset ℕ) (a : ℝ) (l : ℕ) (s : Molecule S) : Measurable
    (fun t=> Polar.floating (drive X (V t) (Y t)) a R W Ñ (u t) k l s) := Finset.measurable_fun_prod s fun i _ => bornB X hΞ h hP he hp hv a l k i
end YM.ConnectedActivityE6.Blaze.Shield
