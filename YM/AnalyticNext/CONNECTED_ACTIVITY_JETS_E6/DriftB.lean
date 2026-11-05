import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Issue

/-!
# Measurability on the per-sector product inputs

Don't assume continuity in all of the group. Frozen chart uses genuine
smooth extension. Plate comparisons presume one color frame; here stationary
also same X. Z meas, counts later. $T,X$ depend on Cargo.B and forest in the
actual step. This proof in Y,Z, k discrete (V held for thresholds).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ K : ℝ} {η r Q Y : ℝ} {L : Side} (X : Coat T F)

def wrapY (y : F.Slice G) : Coat T F := {X with Y := y}



section pre
variable {α : Type*} [MeasurableSpace α]
variable {Y : α → F.Slice G} {U : α → Directions G f} {v : α → Air f G}

lemma tale (i : Bond f) : Continuous (fun z : Air f G=> X.atmos z i) := by
  let l : Air f G →ₗ[ℝ] G.Color :=
    { toFun z := X.atmos z i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact l.continuous_of_finiteDimensional

lemma summon (hY : Measurable Y) (hU : Measurable U) : Measurable fun u => (X.wrapY (Y u)).input (U u) := by
  refine F.continuous_drape.measurable.comp ?_
  apply measurable_pi_lambda; intro i
  by_cases he : X.Hot i.1
  · change Measurable (fun u => (X.wrapY (Y u)).view (U u) i)
    have hx u : (X.wrapY (Y u)).view (U u) i=G.lieExp (U u i.val)*replica S.ratio X.V i.val := if_pos he
    simp_rw [hx]; exact (G.lieExp_cont.measurable.comp ((measurable_pi_apply i.val).comp hU)).mul_const _
  have ht u : (X.wrapY (Y u)).view (U u) i=Y u i := if_neg he
  change Measurable (fun u => (X.wrapY (Y u)).view (U u) i); simp_rw [ht]
  exact (measurable_pi_apply i).comp hY

lemma saving (h : ShellAccess S G X.x W X.width γ) (hY : Measurable Y) : Measurable fun u => (X.wrapY (Y u)).saved := by
  apply measurable_pi_lambda; intro i
  change Measurable (fun u => if _ ∨ X.Hot i then (0:G.Color) else X.small i (F.drape (Y u)))
  split_ifs
  · exact measurable_const
  unfold small
  exact (h.log.borel X.χ).comp (((measurable_pi_apply _).comp (F.continuous_drape.measurable.comp hY)).mul_const _)

lemma through (h : ShellAccess S G X.x W X.width γ) (hp : P.Funds S T) (hY : Measurable Y) (hU : Measurable U)
    (s : Signed) (p : Rod c f) : Measurable (fun u=> (X.wrapY (Y u)).realPath s p (U u)) := by
  have ht : Measurable (fun u => (X.wrapY (Y u)).signal (U u)) :=
    (X.saving h hY).add ((show Measurable X.lens by
      apply measurable_pi_lambda; intro i; unfold lens; split_ifs
      · exact measurable_pi_apply _
      exact measurable_const).comp hU)
  obtain ⟨a,b,H,-⟩ := hp.feeds
  obtain ⟨M,hm⟩ := SliceRows.linear T X.R H s p X.V
  change Measurable fun u => request T X.x (choice s X.k) (pull s 0 X.V) p+
    orientedRow T X.R s p X.V ((X.wrapY (Y u)).signal (U u))
  simp_rw [← hm]; exact measurable_const.add (M.measurable.comp ht)

lemma airwards (h : ShellAccess S G X.x W X.width γ) (hp : P.Funds S T) (hY : Measurable Y) :
    Measurable (fun u => (X.wrapY (Y u)).linearBill) ∧ Measurable (fun u => (X.wrapY (Y u)).μ) ∧
    ∀ β, Measurable v → Measurable (fun u => (X.wrapY (Y u)).liftA β (v u)) := by
  have hh i : Measurable (fun u : α => (X.wrapY (Y u)).priced 0 i) := by
    by_cases he : X.selected (Prod.fst i) (spot S (Prod.snd i))
    · have hm u : (X.wrapY (Y u)).priced 0 i=scale • (X.wrapY (Y u)).realPath i.1 i.2 0 := if_pos he
      simp_rw [hm]; exact (measurable_const (a:=scale)).smul (X.through h hp hY (U:=fun _=>0) measurable_const _ _)
    simp_rw [show ∀ u, (X.wrapY (Y u)).priced 0 i=0 from fun u => if_neg he]; exact measurable_const
  have he : Measurable (fun u => stand ((X.wrapY (Y u)).priced 0)) := by
    apply measurable_pi_lambda; intro i
    exact (EuclideanSpace.proj i.2).measurable.comp (hh _)
  have hx : Measurable fun u => (X.wrapY (Y u)).linearBill :=
    (show Continuous (fun v => X.form.transpose *ᵥ v) by fun_prop).measurable.comp he
  have hk : Measurable fun u => (X.wrapY (Y u)).driftM :=
    ((show Continuous (fun v => -(X.kernelA.transpose *ᵥ v)) by fun_prop).measurable.comp hx)
  have hm i : Measurable (fun u => (X.wrapY (Y u)).μ i) := by
    let l : (Tubular f G → ℝ) →ₗ[ℝ] G.Color :=
     { toFun z := erect G z i
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl }
    exact l.continuous_of_finiteDimensional.measurable.comp hk
  refine ⟨hx, measurable_pi_lambda _ hm, fun β hz=> measurable_pi_lambda _ (fun i => (hm i).add ?_)⟩
  exact (measurable_const (a:=gStep β)).smul ((X.tale i).measurable.comp hz)
end pre
end YM.ConnectedActivityE6.Coat
