import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.UnifiedValue

/-!
# Split Y/F integration and masks before chart

Allocation X.χ and K labels fixed. Nothing paid for total measure / dummy
integrals. Monitor already on accepted Tickets. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F) (l : Finset ℕ)

abbrev Signal := {i : F.Free // X.Hot i.val}
abbrev Fog := {i : F.Free // ¬ X.Hot i.val}

def shore : (F.Slice G) ≃ᵐ ((X.Signal→ G.El) × (X.Fog→G.El)) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _=> G.El) (fun i:F.Free => X.Hot i.val)

def shifted (a : X.Signal→G.El) : F.Slice G := X.shore.symm (a,(X.shore X.Y).2)
def stages := Measure.pi fun _ : X.Signal=> G.probHaar
instance stages_p : IsProbabilityMeasure X.stages := by unfold stages; infer_instance

def forecast := Measure.pi fun _ : X.Fog=> G.probHaar
instance forecast_p : IsProbabilityMeasure X.forecast := by unfold forecast; infer_instance

lemma propagation : MeasurePreserving X.shore (F.order G) (X.stages.prod X.forecast) :=
    measurePreserving_piEquivPiSubtypeProd ..

lemma tangibleB (hR : Intake P T X.x R) (hw : 0<W) : Measurable fun Y=> X.tangible R W Y l := by
  let e:= F.drape (G:=G)
  have he : Measurable e := F.continuous_drape.measurable
  let D := fun a : F.Slice G=> a
  have ht : 0<X.t := by
    unfold Coat.t Pressure.fiery Pressure.temp; have hh := zero_lt_one.trans hR.height; positivity
  have hr := hR.cap
  have hg : Measurable (R.activities.gasOccurrence R.p l) :=
    Measurable.ite (R.activities.admissible_borel ..) (Finset.measurable_fun_prod _ fun i _ => hr.labels.forced.meas _) measurable_const
  have hv (s : Signed) : Envelope (fun U:Config G f=> ∑ i,crown R.path R.clip X.R 1 R.p.threshold (pull s 0 U) i) :=
    Envelope.sum _ _ fun i=> Env.along (env_crown hr.paths ..) (continuous_pull ..).measurable
  have hh : Envelope (cutR R X.R) := env_mean hv
  have hx : Measurable (separate R X.R l) := (((Real.measurable_exp.comp (measurable_const.mul hh.meas)).mul
    (Real.measurable_exp.comp (R.exponentEnv hr).meas)).mul hg)
  exact (((measurable_const.mul ((X.χ.profiles _ _ _ _ hw ht).envelope (funds_branch hR.ready) he measurable_const X.seeds X.k).meas).mul
    (hx.comp he)).mul (env_enters hR.ready R.beta X.x X.k he (V:=fun _=> X.V) measurable_const).meas)

lemma sum_tangible (hR : Intake P T X.x R) (hw : 0<W) (h : 0<X.t) :
    (∀ k, Integrable (fun Y=>X.tangible R W Y k) (F.order G)) ∧
    HasSum (fun k=> ∫ Y,X.tangible R W Y k ∂F.order G) (∫ Y, X.χ.distribute X.seeds X.x W (F.drape Y) X.k X.V*
        (taggedKernel S R.beta X.k (F.drape Y) X.V * R.eval (F.drape Y)) ∂F.order G) := by
  let F' := F.drape (G:=G)
  have hZ : Measurable F' := F.continuous_drape.measurable
  let A := X.χ.profiles G S X.x W hw h
  let B := fun y => enters T R.beta X.x X.k X.V (F' y)*sieve T R.beta X.x X.V
  let f := atomTerm A X.seeds F R X.V X.k B
  have hy := atom_series hR.cap (funds_branch hR.ready) A X.seeds F X.V X.k B
    ((env_enters hR.ready R.beta X.x X.k hZ (V:=fun _=> X.V) measurable_const).mul (Envelope.const _))
  have hk (k) (i) : X.tangible R W i k=f k i := by unfold tangible f atomTerm B; dsimp only [A, Chi.profiles,F']; unfold Coat.R; ring
  have hF i : X.χ.distribute X.seeds X.x W (F' i) X.k X.V * (taggedKernel S R.beta X.k (F' i) X.V * R.eval (F' i))=
    A.bill X.seeds X.k (F' i) X.V * (exposed R X.R (F' i)* B i) := by
    rw [Presented.use_gap hR.received]; unfold B
    change _= X.χ.distribute X.seeds X.x W (F' i) X.k X.V*_ ; unfold Coat.R; ring
  refine ⟨fun k=> by simp_rw [hk]; exact hy.1 k,?_⟩
  simp_rw [hk]; convert! hy.2.2.2 using 2; exact funext hF

lemma shore_tangible (hR : Intake P T X.x R) (hw : 0<W) (ht : 0<X.t) :
    (∫ Y, X.tangible R W Y l ∂F.order G)=∫ Y, ∫ z,X.tangible R W ((X.wrapY Y).shifted z) l ∂X.stages ∂F.order G := by
  let f (Y) := X.tangible R W Y l
  have he : Integrable (f ∘ X.shore.symm) _ := (X.propagation.symm.integrable_comp_emb
    X.shore.symm.measurableEmbedding).mpr ((sum_tangible X hR hw ht).1 l)
  let g (v) := ∫ z,f (X.shore.symm (z,v)) ∂X.stages
  have hr : Integrable (fun w : (X.Signal → G.El) × (X.Fog→G.El) => g w.2) (X.stages.prod X.forecast) :=
    he.integral_prod_right.comp_snd _
  rw [← X.propagation.symm.integral_comp' f]; symm
  change (∫ Y, ∫ z, f _ ∂X.stages ∂_)=_
  rw [← X.propagation.symm.integral_comp' (fun Y=> ∫ z,f ((X.wrapY Y).shifted z) ∂X.stages)]
  simp_rw [shifted]
  change (∫ v, ∫ z, f (X.shore.symm (z,(X.shore (X.shore.symm v)).2)) ∂X.stages ∂_)=_
  simp_rw [X.shore.apply_symm_apply]; rw [Function.comp_def] at he; rw [integral_prod_symm _ hr, integral_prod_symm _ he]; simp [g]

lemma licenses (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)
    {Y : F.Slice G} (h : X.tangible R W Y l ≠ 0) (i : Bond f) (hi : X.Hot i) :
    ∃ v ∈ Metric.ball (0:G.Color) Q.table.radius, ‖v‖ ≤ o.a*X.t ∧
      F.drape Y i=G.lieExp v*replica S.ratio X.V i := by
  have hz := K.laws.data
  let A := X.χ.profiles G S X.x W hz.W_pos hz.room.fiery
  have hv : A.bill X.seeds X.k (F.drape Y) X.V ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hu : S.likelihood (F.drape Y) X.k≠0 := left_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul h))
  have hf := hz.covers; rw [← hz.funds.length_eq] at hf
  refine buys_empty X (γ:=o.γ) (?_) (?_) Q.table_exists (?_) (F.drape Y) (A.actual _ _ _ _ hv)
    (lt_of_le_of_ne (S.likelihood_pos ..) (Ne.symm hu)) (fun i hi=> F.on_tree _ ⟨_,hi⟩) i hi
  · rw [hk]; exact hz.access
  · rw [hk]; exact o.gamma
  nlinarith only [hf, mul_pos o.large hz.room.fiery]
end YM.ConnectedActivityE6.Coat
