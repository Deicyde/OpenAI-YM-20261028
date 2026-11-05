import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Relief

/-!
# Coefficients through V, still Borel (zero factors included)
Hard decisions and picking Σ′ globally only measurable. This is before
imposing Gas log History. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters Art
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G} {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

namespace Cash
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)
variable (p : Renewed j a δ e H)

omit he in
lemma chatting (_hk : X.x=α) (s : Molecule S) : MeasurableSet {V : Config G c| standsIn (vary X V) R Q.halo s} := by
  let f (u:Config G c) := RG.flags (Pressure.temp X.x) u
  have hh : ∀ i, MeasurableSet {V: Config G c | f V=i} := RG.flags_measurable_eq _
  by_cases ha : Ac.Spark (areas R T Q.halo X.B) s ∧ Matter.troupe T R Q.halo X.B s
  · let D : Support c := ground R T Q.halo X.B s
    rw [show {V: Config G c| standsIn (vary X V) R Q.halo s} = ⋃ i∈ univ.filter (fun i => i∩ D=(roster s).flags), {V| f V=i} from ?_]
    · exact MeasurableSet.iUnion fun i=> MeasurableSet.iUnion fun _=>hh i
    ext v
    have he : standsIn (vary X v) R Q.halo s ↔ f v ∩ D=(roster s).flags := and_iff_right ha.1|>.trans (and_iff_right ha.2)
    simp only [Set.mem_setOf_eq,he,Set.mem_iUnion,mem_filter,mem_univ,true_and]; simp
  rw [show {V| standsIn (vary X V) R Q.halo s}=∅ from Set.eq_empty_iff_forall_notMem.mpr (fun i hi=>ha (by
    change standsIn (vary X i) R Q.halo s at hi
    exact ⟨hi.1,hi.2.1⟩))]; exact MeasurableSet.empty

include H
private lemma fraction {A : Type*} [MeasurableSpace A] (V : A→Config G c) (he' : Measurable V) (z : A→Air f G) (hz : Measurable z) :
    Measurable fun t => (vary X (V t)).thetaRef (z t) := by
  have hp:= H.laws.intake.ready
  have hF : Art.Borel fun t=> (vary X (V t)).plate := fun i j=> (Art.borel_plate X hp i j).comp he'
  have hx := (c_measured X.shutter hF).1
  let g t:=(vary X (V t)).relating
  have hg : Art.Borel g := hx
  have hc i : Measurable fun t=> WithLp.ofLp (z t) i := (EuclideanSpace.proj (ι:=Tubular f G) (𝕜:=ℝ) i).measurable.comp hz
  have hm : Measurable fun t=> dotProduct ((z t).ofLp) ((g t)⁻¹ *ᵥ WithLp.ofLp (z t)) := Finset.measurable_fun_sum _ fun i _ =>
    (hc i).mul (Art.borel_times (Art.inverse hg) (d:=fun t=> WithLp.ofLp (z t)) hc i)
  exact measurable_const.mul (Real.measurable_exp.comp ((((Real.measurable_log.comp (Art.det_m hg)).neg.div_const _).sub (hm.div_const _))))

include he hk
lemma attends_b (i : Molecule S) (l : Finset ℕ) : Measurable
    (fun V=> if RG.flags (Pressure.temp X.x) V=X.seeds.flags then (vary X V).attains R Q.table W o.a l Q.halo i else 0) := by
  let A:= (F.order G)
  let f' (V : Config G c) (p : F.Slice G×Air f G):=(vary X V).body R Q.table W o.a l Q.halo i p
  have hg (V) (hv : RG.flags (Pressure.temp X.x) V=X.seeds.flags) : (vary X V).attains R Q.table W o.a l Q.halo i =
      ∫ y, (∫ z,f' V (y,z)*(vary X V).thetaRef z) ∂A := by
    let Y:= vary X V; have hY : Y.manifest := hv.symm
    have hp : Y.dice=MeasureTheory.volume.withDensity (fun x=> ENNReal.ofReal (Y.thetaRef x)) := Poll.sweep_pdf
      (H.laws.data.localP F Y hk he hY).sails.fullC
    have he := H.integrated Y hk he hY l i
    unfold attains; rw [integral_prod _ he]; apply integral_congr_ae; filter_upwards with y
    have hf : Measurable (fun x=> ENNReal.ofReal (Y.thetaRef x)) := by unfold Coat.thetaRef dotProduct; fun_prop
    change _ = ∫ x,f' V (y,x) * _; rw [hp, integral_withDensity_eq_integral_toReal_smul hf (ae_of_all _ fun _=> ENNReal.ofReal_lt_top)]
    apply integral_congr_ae; filter_upwards with x
    change (ENNReal.ofReal _).toReal • f' V (y,x)=_
    rw [ENNReal.toReal_ofReal (show 0 ≤ Y.thetaRef x by unfold Coat.thetaRef bell; positivity),smul_eq_mul]; exact mul_comm ..
  have ht (V : Config G c) : (if RG.flags (Pressure.temp X.x) V=X.seeds.flags then (vary X V).attains R Q.table W o.a l Q.halo i else 0)=
      if RG.flags (Pressure.temp X.x) V=X.seeds.flags then ∫ y,(∫ z,f' V (y,z)*(vary X V).thetaRef z) ∂A else 0 := by
    split; next hx=> exact hg V hx
    next hx=> rfl
  simp_rw [ht]
  refine Measurable.ite (RG.flags_measurable_eq ..) ?_ measurable_const
  let X' := (Config G c × F.Slice G)× Air f G
  have hU : Measurable (fun y:X'=> y.1.1) := measurable_fst.comp measurable_fst
  have h' : Measurable (fun p:X' => f' p.1.1 (p.1.2,p.2)) := Finset.measurable_fun_prod _ fun k _=> Art.portage X (hk.symm ▸ H.laws.intake) Q.table Q.table_exists
    (by rw [hk,he]; exact H.laws.data.access) hU (measurable_snd.comp measurable_fst) measurable_snd ..
  have hF : Measurable (fun y:X' => f' y.1.1 (y.1.2,y.2)*(vary X y.1.1).thetaRef y.2) := h'.mul
    (H.fraction X _ hU Prod.snd measurable_snd)
  have hx := hF.stronglyMeasurable.integral_prod_right' (ν:= MeasureTheory.volume); exact (hx.integral_prod_right' (ν:=A)).measurable

lemma throws (s : Molecule S) : Measurable fun V=> H.emerging (vary X V) s := by
  unfold emerging proceedsA amountP
  apply Measurable.ite (chatting X hk s) _ measurable_const
  unfold levelMean likely; refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> ?_)
  let f (V) := ((planted (vary X V) s).taggedL i).attains R Q.table W o.a (own s) Q.halo s
  let Z d:= (preps (X.taggedL i) {(roster s) with flags:=d})
  let g (d : Support c) (V) := if RG.flags (Pressure.temp X.x) V=d then (vary (Z d) V).attains R Q.table W o.a (own s) Q.halo s else 0
  have he V : (∑ d,g d V)=f V := by
    unfold g f Z; classical
    rw [sum_ite_eq]; simp only [mem_univ, if_true]; rfl
  change Measurable f; rw [← funext he]; refine Finset.measurable_fun_sum _ fun i _=> ?_
  exact H.attends_b (Z i) hk ‹X.width=o.K› _ _

end Cash
end YM.ConnectedActivityE6
