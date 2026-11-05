import YM.Push.LOOP_COEFFICIENT.Chain
import YM.Work.F02
import YM.Work.F05.Actions




/-!
# Joint stationary inputs and their gauge rules

 in ROOTED variables. `completed` is the physical action
including the V penalty, before the gauge square. All unmasked, with the
actual predictor & site frame from the given tag, no cut path substitute. At
small fields these choices are ignored by the actual functions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Set Filter Function Lattice RG Precision Exterior Wilson
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators
variable {c f : Side} {S : StepData c f} {G : Gauge} {p : Clip} {W : PathData G} {σ C Λ : ℝ}

abbrev positions (U : Loops.Inputs G c f) : Config G f := U ∘ Sum.inl
abbrev auxiliaries (U : Loops.Inputs G c f) : NodeField G c := U ∘ Sum.inr

def Zmap (t : S.Choices) (U : Loops.Inputs G c f) : Config G c :=
  Lattice.gauge (auxiliaries U) (S.prediction (positions U) t)

def penalty (S : StepData c f) (V Z : Config G c) : ℝ := S.kernel.penalty * ∑ i, G.price (V i * (Z i)⁻¹)

def completed (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) : ℝ :=
  mainTerm p W (positions U) + penalty S V (Zmap t U)

/-- Representative in the frame patch, using the actual centered odd block residue. -/
def relativePoint (S : StepData c f) (x : Site f) : S.patch.Points :=
  ⟨lift (S.ratio.residue x),by
    have ht : S.ratio.count.val / 2 ≤ S.patch.radius := (Nat.div_le_self ..).trans <|
      (Nat.le_mul_of_pos_left _ (by omega : 0 < S.patch.J+3))
    have hi := box_test.mp (S.ratio.half_box S.patch.odd_side (S.ratio.residue x))
    exact box_test.mpr ⟨fun i => (by omega :
      -((S.patch.radius:ℕ):ℤ) ≤ -(↑(S.ratio.count.val/2 : ℕ):ℤ)).trans (hi.1 i),
      fun i => (hi.2 i).trans (by exact_mod_cast ht)⟩⟩

/-- At a fine x, using the group's site-frame predictor at its actual parent. -/
def Psi (t : S.Choices) (U : Loops.Inputs G c f) : NodeField G f := fun x =>
  let y := S.ratio.parent x
  auxiliaries U y * S.frames (positions U) t.1 y (relativePoint S x)

/-- Combined fine/coarse action on rooted variables. -/
def gaugeJoint (S : StepData c f) (k : NodeField G f) (u : NodeField G c) (U : Loops.Inputs G c f) : Loops.Inputs G c f :=
  Sum.elim (Lattice.gauge k (positions U)) (fun i => u i * auxiliaries U i * (k (S.ratio.embed i))⁻¹)

@[simp] lemma gauge_one {n : Side} (U : Config G n) : Lattice.gauge 1 U = U := by ext1 i; simp [Lattice.gauge]
@[simp] lemma gaugeJoint_one (U : Loops.Inputs G c f) : gaugeJoint S 1 1 U = U := by
  ext i; cases i <;> simp [gaugeJoint]

lemma Zmap_gauge (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    (U : Loops.Inputs G c f) : Zmap t (gaugeJoint S k u U) = Lattice.gauge u (Zmap t U) := by
  ext1 i
  change u _ * U _ * (k _)⁻¹ * S.prediction (Lattice.gauge k (positions U)) t i * (u _ * U _ * (k _)⁻¹)⁻¹ =
    u _ * (U _ * S.prediction (positions U) t i * (U _)⁻¹) * (u _)⁻¹
  rw [StepData.prediction, S.updateGauged h, (S.patch.bond_gauge (h:=h) ..).2]
  unfold StepData.prediction; group

lemma completed_gauge (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices)
    (k : NodeField G f) (u : NodeField G c) (V : Config G c) (U : Loops.Inputs G c f) :
    completed p W t (Lattice.gauge u V) (gaugeJoint S k u U) = completed p W t V U := by
  simp only [completed,Zmap_gauge h,show positions (gaugeJoint S k u U)=Lattice.gauge k (positions U) from rfl,
    Work.F05.mainTerm_gauge hw]
  unfold penalty; congr 2
  exact Finset.sum_congr rfl fun i _ => by
    rw [show Lattice.gauge u V i * (Lattice.gauge u (Zmap t U) i)⁻¹ = u i.1 * (V i * (Zmap t U i)⁻¹) * (u i.1)⁻¹ by
      unfold Lattice.gauge; group]
    exact G.price_conj ..

lemma Psi_gauge (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    (U : Loops.Inputs G c f) (x : Site f) :
    Psi t (gaugeJoint S k u U) x = u (S.ratio.parent x) * Psi t U x * (k x)⁻¹ := by
  unfold Psi
  let y := S.ratio.parent x
  let i := relativePoint S x
  change (u y * _ * _⁻¹) * S.frames (Lattice.gauge k _) t.1 y i = _
  rw [StepData.frames, expandAt_gauge, (S.patch.frame_gauged h ..).2, Patch.changed,
      show wrap f S.patch.center.val + S.ratio.embed y = S.ratio.embed y from ?_,
      show wrap f i.val + S.ratio.embed y = x by rw [add_comm]; exact S.ratio.unpack_at _]
  · change (u y * _ * (k _)⁻¹) * (k _ * _ * _⁻¹) = u y * (_ * S.frames _ _ y i) * _⁻¹
    unfold StepData.frames y; group
  · simp only [Patch.center,map_zero,zero_add]

lemma Zmap_one (h : S.patch.Branches S.kernel G) (t : S.Choices) : Zmap t (1 : Loops.Inputs G c f) = 1 := by
  rw [Zmap, show auxiliaries _ = (1:NodeField G c) from rfl,gauge_one]
  exact funext (fun i => Push.settled S h i t)

section smooth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

lemma Zmap_diff (h : S.patch.Branches S.kernel G) (t : S.Choices) {U : E → Loops.Inputs G c f}
    (hu : U x = 1) (hf : MatDiffAt U x) : MatDiffAt (Zmap t ∘ U) x := by
  have hd : MatDiffAt (fun y => positions (U y)) x := fun i => hf (Sum.inl i)
  intro i
  have he := hd.along (g:=fun A => G.mat (S.prediction A t i)) (show positions (U x)=1 by rw [hu]; rfl)
    (show ContDiffAt ℝ ω _ 0 from ?_)
  · simp only [Zmap, Function.comp_apply, Lattice.gauge, G.mat_mul]; exact ((hf _).mul he).mul (mat_inv_diff (hf _))
  exact (show ContDiffAt ℝ ω ((fun A => G.mat (S.prediction A t i)) ∘ vary 1) (0:Loops.Links G f) by
    conv => arg 3; ext; rw [Function.comp_apply, ← represent_chart]
    exact (show ContDiffAt ℝ ω (fun v => G.mat (S.prediction (represent v) t i)) (chartEquiv G f 0) by
      simpa only [map_zero] using prediction_cont S h i t).comp 0 (chartEquiv G f).contDiff.contDiffAt)

lemma Psi_diff (h : S.patch.Branches S.kernel G) (t : S.Choices) {U : E → Loops.Inputs G c f}
    (hu : U x = 1) (hf : MatDiffAt U x) : MatDiffAt (Psi t ∘ U) x := by
  have hd : MatDiffAt (fun y => positions (U y)) x := fun i => hf (Sum.inl i)
  intro i
  have he (k a) : ContDiffAt ℝ ω ((fun A => G.mat (S.frames A t.1 k a)) ∘ vary 1) (0:Loops.Links G f) := by
    conv => arg 3; ext; rw [Function.comp_apply, ← represent_chart]
    exact (show ContDiffAt ℝ ω (fun v => hats S k t.1 v a) (chartEquiv G f 0) by
      rw [map_zero]; exact scheme S k t.1 (h:=h) a).comp 0 (chartEquiv G f).contDiff.contDiffAt
  apply (hf _).mul (hd.along (show positions (U x)=1 by rw [hu]; rfl) (he _ _))

-- Cost is globally analytic in matrix coords, no chart test there.
lemma price_diff {V : E → G.El} (h : ContDiffAt ℝ ω (fun y => G.mat (V y)) x) :
    ContDiffAt ℝ ω (fun y => G.price (V y)) x :=
  contDiffAt_const.sub ((Complex.reCLM.contDiff.contDiffAt.comp x
    ((Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun y => G.mat (V y)) x h)).div_const _)

lemma penalty_diff (S : StepData c f) {V Z : E → Config G c} (h : MatDiffAt V x) (hz : MatDiffAt Z x) :
    ContDiffAt ℝ ω (fun y => penalty S (V y) (Z y)) x := by
  apply contDiffAt_const.mul
  exact ContDiffAt.sum (fun i _ => price_diff (V:=fun y => V y i * (Z y i)⁻¹) ((h i).mul (mat_inv_diff (hz i))))

lemma completed_diff (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices)
    {U : E → Loops.Inputs G c f} {V : E → Config G c} (h1 : U x = 1) (hu : MatDiffAt U x) (hv : MatDiffAt V x) :
    ContDiffAt ℝ ω (fun y => completed p W t (V y) (U y)) x :=
  (Work.F02.mainTerm_contDiffAt hw (A:=fun y => positions (U y)) (fun _ => hu _)).add
    (penalty_diff S hv (Zmap_diff h t h1 hu))

lemma gauge_diff {n : Side} {k : E → NodeField G n} {U : E → Config G n} (hk : MatDiffAt k x) (hu : MatDiffAt U x) :
    MatDiffAt (fun t => Lattice.gauge (k t) (U t)) x := fun i => ((hk _).mul (hu i)).mul (mat_inv_diff (hk _))

lemma gaugeJoint_diff {U : E → Loops.Inputs G c f} {u : E → NodeField G c} {k : E → NodeField G f}
    (hu : MatDiffAt U x) (hv : MatDiffAt u x) (hk : MatDiffAt k x) :
    MatDiffAt (fun y => gaugeJoint S (k y) (u y) (U y)) x := by
  rintro (i|j)
  · exact gauge_diff (U:=fun y => positions (U y)) hk (fun _ => hu _) i
  exact ((hv j).mul (hu _)).mul (mat_inv_diff (hk _))
end smooth

end YM.Push.Loops
