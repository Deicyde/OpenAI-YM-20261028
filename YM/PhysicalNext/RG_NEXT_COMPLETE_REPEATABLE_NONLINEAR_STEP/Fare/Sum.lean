import YM.Next.MULTISOURCE.Tumble
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Jas
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Rooms
import YM.Push.RELAY_MARK.PrePrice

/-!
# Pure integral actual closed ball in station tangent coordinate

Own chart/measure conversion. On all nonzero y in ball. This does
 not reorganize the physical expansions at history. Aux VOL can be exp
 expensive exponential tails only. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (F : Forest S.ratio) (T : Tube G S) (O : ChartRatio G) (k : S.Choices)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
variable (x : X) (ρ : Bid.Dir G c→AxisChart G F) (B : BudgetPoint) (β d v p : ℝ)

def actU (β : ℝ) (V : Config G c) (U:F.Slice G):= taggedKernel S β k (F.drape U) V * (Pane.virgin T B β).eval (F.drape U)
def overall (β : ℝ) (V : Config G c) (U:F.Slice G):= ∑ k:S.Choices,actU F T k B β V U
lemma total (V : Config G c) (U:F.Slice G) : overall F T B β V U=S.density β (F.drape U) V*(Pane.virgin T B β).eval (F.drape U) := by unfold overall StepData.density; rw [Finset.sum_mul]; rfl
lemma true_point (V : Config G c) (U:F.Slice G) : S.noise β (S.prediction (F.drape U) k) V= Sector.prefactor S G β * Real.exp (-β*noiseTaylor S V (F.drape U) k) := by
  unfold StepData.noise StepData.penaltyWeight Sector.prefactor noiseTaylor; simp_rw [Finset.prod_mul_distrib,prod_const,card_univ,mul_sum,Real.exp_sum]; congr 1; apply prod_congr rfl; intro i _; congr 1; ring
lemma acts (V : Config G c) (U:F.Slice G) (he : flags B.threshold (F.drape U)=∅) :
    let a:= mainTerm T.high T.up (F.drape U) + noiseTaylor S V (F.drape U) k
    actU F T k B β V U=prefactor S G β*S.likelihood (F.drape U) k* Real.exp (-β*a-Precision.loop T.up (F.drape U)) := by
  intro a; unfold actU taggedKernel; rw [true_point,Pane.sparkling,if_pos he]
  rw [mul_assoc, mul_assoc (prefactor S G β),← Real.exp_add]; unfold a; ring_nf

-- On all fields including exact hard seam. Does not require hm Opposite.
lemma amt (P : Teller G) (Q : Intake P T v (Pane.virgin T B β)) (V : Config G c):
    let G':=overall F T B β V
    RG.Envelope G' ∧ S.push β (Pane.virgin T B β).eval V=∫ U,G' U ∂F.order G := by
  intro Y'; have he:= (Q.ready.kernel)
  have hr:= (Pane.virgin T B β).envelope Q.cap
  constructor
  · refine RG.Envelope.sum _ _ (fun k=> ?_); exact (env_tagged _ _ (Q.ready.knobs.symm ▸ he) F.continuous_drape.measurable measurable_const).mul (Env.along hr F.continuous_drape.measurable)
  have hI:=S.isKernel (Q.ready.knobs.symm ▸ he) β
  rw [F.pushing hI _ V (lawful_gi Q.cap) (hr.integrable _) (fun k U=>S.covary (Q.ready.knobs.symm ▸ he) k β U V)]; apply integral_congr_ae; filter_upwards with a using (total F T B β V a).symm
section transfer

def windmill (Y' : Y) : LogArray G F.Free := tint G _ Y'.ofLp
lemma spinning : ∃ e:Y ≃ᵐ LogArray G F.Free, MeasurePreserving e ∧ ⇑e=windmill F := by
  let e: Y ≃ᵐ LogArray G F.Free := ((weld _).trans (tint G _)).toHomeomorph.toMeasurableEquiv
  exact ⟨e,tape_volume.comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Precision.Key F G)),rfl⟩

def floorG (V : Config G c) : LinkArray G F.Free := fun i=>replica S.ratio V i
def draw (V : Config G c) (y : Y): F.Slice G:= release (floorG F V) (windmill F y)

lemma draw_cont (V : Config G c): Continuous (draw F V):= (release_continuous _).comp (((Lapis.weld _).trans (Uniform.tint G _)).continuous) -- edit
def staying (b : Y) (t r : ℝ) (V : Config G c) := draw F V '' ((fun z:Y=> b+t • z) '' (closedBall 0 r))
lemma staying_meas (b : Y) (t r : ℝ) (V : Config G c) : MeasurableSet (staying F b t r V) := (((isCompact_closedBall _ _).image (show Continuous (fun z:Y=> b+t • z) by fun_prop)).image (draw_cont F V)).measurableSet
lemma kernel (g : Y→ℝ) (a : Y) {u : ℝ} (hu : 0 < u) : ∫ y,g y= u ^ Fintype.card (Precision.Key F G) *∫ z,g (a+u • z) := by
  rw [Measure.integral_comp_smul_of_nonneg (hR:=hu.le) volume (fun z => g (a+z)) u, integral_add_left_eq_self]; change _=_*(_⁻¹*_); rw [finrank_euclideanSpace]; field_simp

lemma cubits (B : Y) (V : Config G c) (t D : ℝ) (u : F.Slice G→ℝ) (he : 0<t) (hO : LocalRatio O) (h : ∀ z, ‖z‖ ≤ D → windmill F (B+t • z) ∈ mouth O) (hp : StronglyMeasurable u) :
    ∫ y in staying F B t D V, u y ∂F.order G = t^ Fintype.card (Precision.Key F G)* ∫ z:Y in closedBall 0 D, pay O (windmill F (B+t•z)) * u (draw F V (B+t•z)) := by
  let Z:= staying F B t D V; let T:= Z.indicator u; let W:= floorG F V; let Xs:= draw F V; let Y' := closedBall (0:Y) D; let R (q:Y):=B+t • q
  have hv v (he:v∈Z):v∈ covered O W:= by
    obtain ⟨w,⟨z,hz,rfl⟩,rfl⟩:=he; rw [← release_image]; exact ⟨_,h z (mem_closedBall_zero_iff.mp hz),rfl⟩
  obtain ⟨-,hx⟩:=release_integral hO W T (hp.indicator (staying_meas ..)) (fun y hy=> Set.indicator_of_notMem (mt (hv y) hy) _)
  rw [← integral_indicator (staying_meas ..),← integral_indicator measurableSet_closedBall]; let V' : LogArray G F.Free → ℝ := (mouth O).indicator (fun y=> pay O y * T (release W y))
  change (∫ x,T x ∂piHaar G _)=_
  rw [show (∫ x,T x ∂piHaar G _)=∫ y,V' y from hx]
  obtain ⟨e,hK,hζ⟩:= spinning F (G:=G)
  rw [← hK.integral_comp' V',hζ, kernel F (fun y=> V' (windmill F y)) B he]; apply congr_arg (fun x : ℝ=> t^Fintype.card (Precision.Key F G)*x); apply integral_congr_ae; filter_upwards with z
  by_cases H:z∈Y'
  · have hX : Xs (R z)∈Z:= ⟨_,⟨z,H,rfl⟩,rfl⟩
    have hR : windmill F (B+t • z) ∈ mouth O:= h z (mem_closedBall_zero_iff.mp H)
    change V' (windmill F _)=_; unfold V' T; rw [Set.indicator_of_mem hR,Set.indicator_of_mem H]; exact congr_arg (pay _ _* ·) (Set.indicator_of_mem hX _)
  change V' (windmill F (R z))=_; rw [Set.indicator_of_notMem H]; by_cases hf : windmill F (R z)∈mouth O
  · have hp:Xs (R z) ∉ Z:= by
      rintro ⟨y,⟨v,hv,rfl⟩,hp⟩; apply H; have hq := release_injOn hO W (h v (mem_closedBall_zero_iff.mp hv)) hf hp
      rw [← hζ] at hq; exact (smul_right_injective Y he.ne' (add_left_cancel (e.injective hq))) ▸ hv
    unfold V' T; rw [Set.indicator_of_mem hf]; change _ * Z.indicator u (Xs (R z))=_; rw [Set.indicator_of_notMem hp,mul_zero]
  exact Set.indicator_of_notMem hf _
end transfer
end YM.PhysicalNext.Repeat.Fare
