import YM.UVExtension.Orchard.Barrel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
/-! Relaxed choice hypotheses. permits *even* regulator dependent successes and
    beta at reference. running kept. No asserting `Selected` without reinstating
    the calibrated b=0 prescription. -/
set_option autoImplicit false
noncomputable section
open YM Lattice Function Filter Complex RG Wilson
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} -- frame
structure Vintage.YM.RG.History.Selected (A:History G) : Prop where
  path_shared (N p q m : ℕ) : m ≤ N → (A.rep N p m).path=(A.rep N q m).path
  represents (N p m:ℕ) : m ≤ N → A.Conv N p m
  starts (N p :ℕ) : (A.rep N p N).v=0 ∧ (A.rep N p N).eval = bare (A.β N p N)
  steps (N p m:ℕ) : m<N → A.Transfer N p m
  reaches (_ _ :ℕ) : True
  running : A.Running
structure Vintage.YM.Family.Makes (C:Family G) : Prop where
  wilson : Vintage.YM.RG.History.Selected C.path
  sections (d : ℕ) : (C.localSection d).Sound C.params
  stages (d : ℕ) : d+3 ≤ C.path.levels.clock.J (C.ref d) ∧
    ∀ m, C.ref d ≤ m → d+1 ≤ (C.path.levels.params m).order ∧ d ≤ (C.path.levels.params m).power
  places (d N p : ℕ) : C.ref d ≤ N → ∀ x ∈ (C.localSection d).stencil,
    ∀ i : Axis, 20*((x i).natAbs + 1) ≤ (C.side N p).val
  priced (d N p : ℕ) : C.ref d ≤ N →
    let P := C.path.levels.budget N
    let F := C.labels.level d
    let D := C.localSection d
    ∀ o : Site (C.side N p), ∀ i : F.Index,
      P.Regular (D.footprint o) (D.places (Pi.single i 1) o) ∧
      P.supBounds o (D.footprint o) (D.places (Pi.single i 1) o) ((C.path.levels.params N).columns *
        P.threshold^(F.grades i).2)
  calibrated (d N p : ℕ) : C.ref d ≤ N → (C.factory d N p).Based C.params (C.localSection d) (C.ref d)

open Org Input Shoot Supply
variable {X:Metals G}{P:Rolls X.p} {A:Alloy X P}
structure Vintage.YM.Org.Bolt (A:Alloy X P) where
  program : A.B.Program
  history : ℕ → ∀ i, Trail A.B.a i
  sticks : A.B.bake.Stays history
  choice : Vintage.YM.RG.History.Selected (A.B.bake.make history)
  moves N m p : m < N → A.B.Move N m p (history N p m) (history N p (m+1))
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.Progress.DirectedRecipe YM.UVNext.CouplingReset Graces
structure Vintage.YM.PhysicalNext.Repeat.Graces.Nest (R:Roost.Factor A) (V:Vintage.YM.Org.Bolt A) : Prop where
  born N p : HasSlots (V.history N p N).p (V.history N p N).activities
  held N m p (h: m<N):Protected R N m p (V.history N p m) (V.history N p (m+1)) ∧ Accurate A.B R.post N m p (V.history N p m) (V.history N p (m+1))

namespace YM.UVExtension.Orchard
lemma loosen {C:Family G} (h:C.Makes) : Vintage.YM.Family.Makes C:=
   ⟨⟨h.wilson.path_shared,h.wilson.represents,h.wilson.starts,h.wilson.steps,fun _ _=>trivial,h.wilson.running⟩,h.sections,h.stages,h.places,h.priced,h.calibrated⟩
private def costQ (a : Levels G) : ℕ → ℝ
  | 0 => a.clock.bar
  | m+1 => costQ a m+(a.params (m+1)).drift

lemma traject (H : History G) (hh : ∀ N p m:ℕ,m≤N → H.Conv N p m)
    (ht : ∀ N p j, j<N → H.Transfer N p j) : H.Running := by
  let A := H.levels.clock
  have hd (N p i : ℕ) (hi : i≤N) : |H.β N p i-A.hatBeta i|≤costQ H.levels i := by
    induction i with
    | zero =>
        have hv: _∈ Set.Icc _ _:= (hh N p 0 (Nat.zero_le _)).band
        have hA:A.hatBeta 0=A.bar:=by simp [Calendar.hatBeta]
        rw [hA]; change H.β N p 0∈ Set.Icc (A.hatBeta 0/2) (2*A.hatBeta 0) at hv; rw [hA] at hv; refine abs_le.mpr ?_; change _ ≤ _ ∧ _ ≤ A.bar; obtain ⟨hx,hv⟩:=hv; unfold costQ; change -A.bar ≤ _ ∧ _ ≤ _; constructor <;> linarith only [hx,hv,A.bar_pos]
    | succ i ih =>
      calc
        _ = |(H.β N p i-A.hatBeta i)+(H.β N p (i+1)-H.β N p i-G.slopeConstant*Real.log (H.S.block i).val)| := by
          congr 1; unfold Calendar.hatBeta; rw [Schedule.scale_succ]; unfold A History.S Levels.S; ring
        _ ≤ _ := (abs_add_le ..).trans (add_le_add (ih (le_trans (Nat.le_succ _) hi)) ((ht N p i hi).2))
  intro ε he
  have hh' : Tendsto (fun m => ((A.J (m+1):ℝ)^2)⁻¹) atTop (𝓝 0) := by
    have hz := H.levels.fits.deep.comp (tendsto_add_atTop_nat 1)
    exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_natCast_atTop_atTop.comp hz))
  obtain ⟨j,hj⟩ := eventually_atTop.mp (hh'.eventually (ge_mem_nhds (half_pos he)))
  have hu (i : ℕ) (hi : j ≤ i) : costQ H.levels i ≤ costQ H.levels j + (ε/2)*(H.S.scale i-H.S.scale j) := by
    induction i,hi using Nat.le_induction with
    | base => rw [sub_self,mul_zero,add_zero]
    | succ i hi ih =>
      have hg : 0 < Real.log (H.S.block i).val := Real.log_pos (by
        have H0 := H.S.block_large i
        exact_mod_cast (show 1 < (H.S.block i).val from lt_of_lt_of_le (by norm_num) H0))
      have hy := (div_le_iff₀ hg).mp ((H.levels.fits.driftSmall i).trans (hj i hi))
      rw [costQ,Schedule.scale_succ]; linarith
  have hb := (H.S.divergent.const_mul_atTop (half_pos he)).eventually_ge_atTop (costQ H.levels j)
  filter_upwards [eventually_ge_atTop j,hb] with i hi hz
  intro N p hn
  apply (hd N p i hn).trans ((hu i hi).trans ?_)
  have hb : costQ H.levels j ≤ (ε/2)*H.S.scale i := hz
  nlinarith [mul_nonneg he.le (scale_nn H.levels j)]
end YM.UVExtension.Orchard
