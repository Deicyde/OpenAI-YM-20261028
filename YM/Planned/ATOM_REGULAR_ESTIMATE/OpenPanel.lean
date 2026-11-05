import YM.Next.SCHEDULE.Dues
import YM.Planned.ATOM_REGULAR_ESTIMATE.Ducts
import YM.Planned.ATOM_REGULAR_ESTIMATE.Echo


/-! Launch the patch extensions for ANY healthy variation. Provides e.g. the
uniform service's Clips obligation. `LinearVals` need only test ONE panel-
independent linear estimate (`LinearStencil` on weighted directions). No
claim Uniform alone supplies this valuation. Eagerly keeps the lower hypotheses on
cost with INVARIANT payloads, the precise linear stencil, not an intercept
for already marked measures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage.Cube
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform Next.Foundations
open WardBin.Lies Sample Exterior
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {n m : Side} {r q k l d : ℕ} {G : Gauge} {T : Collar G k}

def moduleBill (P : BudgetPoint) (q : ℕ) := P.threshold*(1+(q:ℝ))^P.power

def Wire (P : BudgetPoint) (R : ℕ) (T : Collar G k) :=
    G.colorScale * (4*moduleBill P R) < T.r ∧ moduleBill P R ≤ 1

/-- Costs conditional on gauges in Anchored, not supplied if using patch of
radius beyond reach. -/
lemma ready (G : Gauge) (p R : ℕ) (T : Collar G k) : ∃ Z : ℝ, ∀ H : Levels G, ∀ m : ℕ, Z ≤ H.clock.hatBeta m →
      (H.budget m).power=p → Wire (H.budget m) (R*(H.budget m).B) T := by
  open Next.Scheduling in
    have hm := vapors p ((R+1:ℝ)^p)
    obtain ⟨M,hM⟩ := eventually_atTop.mp (((show Tendsto (fun x : ℝ => G.colorScale * (4 * ((R+1:ℝ)^p * ether x * (1 + (Clock.cover x:ℝ))^p))) atTop (𝓝 0) by
      simpa only [mul_zero] using (hm.const_mul 4).const_mul G.colorScale).eventually (gt_mem_nhds T.pos)).and (hm.eventually (ge_mem_nhds zero_lt_one)))
    refine ⟨M,fun H m h hv => ?_⟩
    let k := H.clock.hatBeta m
    obtain ⟨hi,hx⟩ := hM _ h
    let U := H.budget m
    have he : moduleBill U (R*U.B) ≤ (R+1:ℝ)^p * ether k * (1+(Clock.cover k:ℝ))^p := by
      have hu : U.threshold=ether k := by unfold ether; rw [Clock.watch_two]; rfl
      change U.threshold*(1+((R*U.B:ℕ):ℝ))^U.power ≤ _
      rw [show U.power=p from hv, ← hu, mul_comm ((R+1:ℝ)^p) U.threshold,mul_assoc,← mul_pow, Nat.cast_mul]
      apply mul_le_mul_of_nonneg_left _ U.threshold_pos.le
      gcongr
      have hh : Clock.cover k = U.B := rfl
      rw [hh]; nlinarith [Nat.cast_nonneg (α:=ℝ) R,Nat.cast_nonneg (α:=ℝ) U.B]
    exact ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num)) G.colorScale_pos.le) hi, he.trans hx⟩



def gather : Directions G m →L[ℝ] In G m := ContinuousLinearMap.pi fun i : Body 1 m =>
    ContinuousLinearMap.proj (i.1,axisEquiv.symm i.2)
def indices : Directions G m →L[ℝ] Origin G m := (tint G _).symm.toContinuousLinearMap.comp gather



/-- Output arrays to test at root anchor. -/
def FitsWire (P : BudgetPoint) (o : Site m) (q : ℕ) (c : ℝ) (u : Origin G m) :=
    ∃ v : Directions G m, u=indices v ∧ ∀ i, ‖v i‖ ≤ c * (if separation o i.1 ≤ q then weight P o i else 0)

structure Extended (P : BudgetPoint) (o : Site m) (q : ℕ) (c : ℝ) (x : Panels l → Origin G m) : Prop where
  size : Clips x 0 l (c*moduleBill P q)
  derivatives : ∀ i, i ≤ l → ∀ v : Fin i → Panels l, (∀ j, ‖v j‖ ≤ 1) → FitsWire P o q c (iteratedFDeriv ℝ i x 0 v)







end YM.Planned.AtomRegular.Foliage.Cube
