import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ColorB

/-!
# Matrix integration meas. Hard assignments, finite support colors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Art
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {A : Type*} [MeasurableSpace A] {V : A→Config G c} {Y : A→F.Slice G} {z : A→Air f G}
variable (X : Coat T F) (H : Intake P T X.x R) (Ñ : ChartRatio G) (hh : LocalRatio Ñ) (ht : ShellAccess S G X.x W X.width C)
variable (he : Measurable V) (hp : Measurable Y) (hk : Measurable z) (l : Finset ℕ) (m : ℕ) (a : ℝ)

private lemma flagsTest (p : Support c) (t : ℝ) {i : Finset (Site c)} (he : Measurable V) : MeasurableSet
    {x:A| ∀ y∈i,y∈p ↔ y∈RG.flags t (V x)} := by
  simp only [Set.setOf_forall]; apply MeasurableSet.iInter; intro y; apply MeasurableSet.iInter
  intro _; by_cases hf : y∈p
  · simp only [hf,true_iff]
    exact he (RG.flags_open ..).measurableSet
  simp only [hf,false_iff]; exact MeasurableSet.compl (he (RG.flags_open ..).measurableSet)

include H he in
private lemma rawly {U : A → Config G f} (hF : Measurable U) (p : LogLetter c f) : Measurable fun t=> expo T X.x R (U t) (V t) p := by
        have hu {d} (T : ℕ → Atom G d) (b : ℝ) (i : Trans f) : Measurable fun q=>translateValue R.p T b (U q) i :=
          (measurable_const (a:=b)).mul (((masked_measurable _ _ _ ((T i.2.2).unmasked_cont (n:=f) i.2.1).measurable)).comp (pulling_meas i.1 hF))
        rcases p with p|p|p|p|p|p <;> simp only [expo,Sum.elim]
        · exact ((masked_measurable _ _ _ ((H.cap.labels.regular.smooth p).borel)).comp hF).neg
        · exact hu _ _ _
        · exact hu _ _ _
        · exact hu _ _ _
        · exact (measurable_const (a:= -orientation*R.beta)).mul ((pair_measurable R.path R.clip X.R 1 R.p.threshold
            (p.2.2.1,p.2.1) p.2.2.2).comp (pulling_meas p.1 hF))
        exact (measurable_const (a:= -(-orientation*R.beta))).mul ((pair_measurable T.down T.low X.R S.patch.L.val
          (Pressure.temp X.x) (p.2.2.1,p.2.1) p.2.2.2).comp (pulling_meas p.1 he))
include H hh ht he hp hk
lemma portage (p : Head S) : Measurable fun t=> (drive X (V t) (Y t)).vertex R Ñ W a l m (z t) p := by
  let E t:= drive X (V t) (Y t); let f' t:= (E t).liftA R.beta (z t); let U t:= (E t).input (f' t)
  have hr:=H.ready
  have hu : Measurable f' := levitate X hr ht he hp _ hk
  have hF : Measurable U := entering X he hp hu
  have ⟨hy,hC⟩ := royal X hr ht he hp hk R.beta
  have hs := (wages X hr ht he hp).2.2
  have hw i s {u : A→Directions G f} (hg : Measurable u) : Measurable fun t=> (E t).extracted (u t) i s := by
    unfold Coat.extracted; apply Finset.measurable_fun_sum; intro p h
    change Measurable fun t=> if X.selected i _ then ‖(E t).realPath i p (u t)‖ ^2/2 else 0
    split_ifs
    · exact (((tumbling X hr ht he hp hg i p).norm.pow_const (2:ℕ)).div_const _)
    exact measurable_const
  have hI i := (census_o hr (pulling_meas i hF) (pulling_meas i he) (choice i X.k) X.x).2
  rcases p with p|p|p|p
  · let P':= p.dome (300*X.B); let J:= X.plaza (p.dome (304*X.B))
    change Measurable fun t=> if Packets.connected S m X.B p then (E t).Pack R Ñ l W a p (f' t) else 0
    split_ifs
    · unfold Coat.Pack; refine Measurable.ite ?_ ?_ measurable_const
      · by_cases hP : p.place⊆X.seeds.place
        · change MeasurableSet {t:A| p.place⊆ X.seeds.place ∧ ∀ i∈P',i∈p.flags ↔ i∈RG.flags (Pressure.temp X.x) (V t)}
          simp only [hP,true_and]; exact flagsTest p.flags _ he
        change MeasurableSet {t:A| p.place⊆ X.seeds.place ∧ _}; simp [hP]
      have he' : Measurable fun t=> (E t).quoteNear p (f' t) := (measurable_const (a:=Raw.orientation)).mul
        (Finset.measurable_fun_sum univ fun s _=> Finset.measurable_fun_sum (posted (turnStore s p) (200*X.B)) fun i _=>
          ((hI s i).1).sub (hw s i hu))
      have hf : Measurable fun t=> (E t).far_bills p := (measurable_const (a:=Raw.orientation)).mul
        (Finset.measurable_fun_sum univ fun s _=> Finset.measurable_fun_sum (posted (turnStore s p) (200*X.B)) fun i _=> hw s i hs)
      have hg : Measurable fun t=> (E t).steamLog R Ñ a p (f' t) :=
        ((((measurable_const (a:=-R.beta)).mul (he'.add hf)).add (Finset.measurable_fun_sum (visit p (200*X.B)) fun i _=> hy _)).add
          (Finset.measurable_fun_sum J fun i _=> (X.gentry_b i _ hh a).comp hu)).sub (measurable_const (a:=(X.pens p).card*Real.log (measure_g Ñ R.beta)))
      let g (t:A) i:= (E t).rawStorm (f' t) W p R l i
      have hq : Measurable (fun t:A=> ∏ i:Panic c f, if mandatory p X.B i then g t i else 1) := by
        apply Finset.measurable_fun_prod; intro i _; split_ifs
        · exact (terror (W:=W) X hr he hp hu l R).1 i p
        exact measurable_const
      have hr : ∀ v,(E v).steam R Ñ l W a p (f' v)=Real.exp ((E v).steamLog R Ñ a p (f' v)) *
          (∏ i:Panic c f, if mandatory p X.B i then g v i else 1) * X.enforce a (f' v) J := by
        intro v
        let F:= (E v); let U':=f' v; have hx:= F.forceds p R l W U'
        change _=_*(∏ i:Panic c f, if mandatory p F.B i then F.rawStorm _ _ _ _ _ i else 1) * F.enforce a U' (F.plaza (p.dome (304*F.B)))
        unfold steam; dsimp only at hx ⊢; rw [hx]; unfold F U'; ring
      simp_rw [hr]; exact ((Real.measurable_exp.comp hg).mul hq).mul ((X.enforce_b ..).comp hu)
    exact measurable_const
  · exact ((H.cap.labels.forced.meas p).comp hF).mul ((X.enforce_b (2*a) (X.plaza (Raw.forcedFoot S.ratio 0 X.B R p))).comp hu)
  · change Measurable fun t=> Real.exp ((E t).farLog R a Ñ (z t) p)-1
    refine (Real.measurable_exp.comp ?_).sub measurable_const
    rcases p with p|p|p
    · have hm:= rawly X H he hF p
      exact hm.mul ((X.enforce_b (2*a) (X.plaza (Raw.space T 0 X.B R p))).comp hu)
    · rcases p with p|p|p
      · let q:=rowSite S p
        change Measurable fun t=> if Inside q X.seeds (200*X.B) then 0 else -_ * Raw.orientation*(X.enforce (2*a) (f' t) (X.booth q)*
          (E t).light (f' t) p.1 p.2+(E t).extracted ((E t).μ) p.1 p.2)
        split_ifs
        · exact measurable_const
        have hg := (hw p.1 p.2 hu)
        exact measurable_const.mul ((((X.enforce_b (2*a) (X.booth q)).comp hu).mul (((hI p.1 p.2).2).sub hg)).add (hw p.1 p.2 hs))
      · change Measurable fun t=> if voyage X.seeds (200*X.B) p then 0 else (E t).condensation p; split_ifs
        · exact measurable_const
        exact hy p
      change Measurable fun t=> X.solo (f' t) Ñ a p; unfold solo; split_ifs
      · exact (X.gentry_b _ _ hh a).comp hu
      exact measurable_const
    exact hC p a
  exact (terror (W:=W) X hr he hp hu l R).2 p a
end YM.ConnectedActivityE6.Art
