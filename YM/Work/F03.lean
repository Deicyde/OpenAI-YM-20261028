import YM.Work.F03.Flat


/-!
# F03. Transport the canonical Hessian onto the tree slice

Use the actual tested function with fixed `k`. Log of the lifted links gives a smooth
chart substitution on some neighborhood in the real parameter plane, and its tangent
is exactly the `stretch`. Gradient already zero in flat coordinates, so the mixed
Hessian pulls back on these tangents alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F03
open Filter Function Lattice Tree RG Wilson Precision Exterior Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

variable {G : Gauge} {c f : Side} {S : StepData c f}

section chart
variable {g : Ratio c f} (H : Forest g)

abbrev ChartVars (G : Gauge) := Dir G c × AxisChart G H

def live (a : ChartVars H G) := lifting H (represent a.1) a.2

lemma live_zero : live H (0 : ChartVars H G) = 1 := by
  simp only [live, Prod.snd_zero, Prod.fst_zero, lifted, link_one, replica_one]

def axisLog (b : ChartVars H G) : Dir G f := fun i =>
  G.plog (G.mat (live H b (i.1, axisEquiv.symm i.2)))

def inclusion (b : ChartVars H G) : Logs G c f := (b.1, axisLog H b)

lemma inclusion_zero : inclusion H (0 : ChartVars H G) = 0 := by
  apply Prod.ext
  · rfl
  funext i
  change axisLog H 0 i = _
  simp [axisLog, live_zero]

lemma live_smooth (e : Edge (Site f)) :
    ContDiffAt ℝ ω (fun b : ChartVars H G => G.mat (live H b e)) 0 := by
  by_cases h : e ∈ H.trunks
  · have he (b : ChartVars H G) : live H b e = 1 := H.on_tree _ ⟨e,h⟩
    simp_rw [he]
    exact contDiffAt_const
  have he (b : ChartVars H G) : live H b e =
      G.lieExp (b.2 ⟨e,h⟩) * replica g (represent b.1) e := H.off_tree _ ⟨e,h⟩
  have hh : ContDiffAt ℝ ω (fun b : ChartVars H G => b.2 (⟨e,h⟩ : H.Free)) 0 :=
    (contDiffAt_apply ℝ G.Color ⟨e,h⟩ (0:AxisChart G H)).comp (f:=Prod.snd) (0:ChartVars H G) contDiffAt_snd
  simp_rw [he,G.mat_mul]
  apply (G.exp_jet.contDiffAt.comp (f:=fun b : ChartVars H G => b.2 ⟨e,h⟩) _ hh).mul
  unfold replica
  split
  · exact contDiffAt_const
  exact (represent_smooth (G:=G) _).contDiffAt.comp (f := Prod.fst) (0:ChartVars H G) contDiffAt_fst

lemma inclusion_smooth : ContDiffAt ℝ ω (inclusion H (G:=G)) 0 := by
  refine contDiffAt_fst.prodMk (show ContDiffAt ℝ ω (axisLog H (G:=G)) 0 from
    contDiffAt_pi.mpr fun i => ?_)
  have ht := live_smooth H (G:=G) (i.1, axisEquiv.symm i.2)
  refine ContDiffAt.comp (g:=G.plog) _ ?_ ht
  rw [live_zero, Pi.one_apply, G.mat_one]
  exact G.plog_diff

lemma inclusion_works : (fun x : ChartVars H G => represent (axisLog H x)) =ᶠ[𝓝 0] live H := by
  have he (e : Edge (Site f)) :
      ∀ᶠ x : ChartVars H G in 𝓝 0, G.lieExp (G.plog (G.mat (live H x e))) = live H x e := by
    have hb : ContinuousAt (fun x : ChartVars H G => live H x e) 0 :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
        (live_smooth H (G:=G) e).continuousAt.tendsto
    have hv := hb.tendsto
    rw [live_zero,Pi.one_apply] at hv
    exact hv.eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with x hx
  funext e
  rw [represent_link,axisLog, show axisEquiv.symm (coord e.2) = e.2 from
    axisEquiv.symm_apply_apply _]
  exact hx e

end chart

variable (H : Forest S.ratio)

lemma live_rate (e : Edge (Site f)) (a : ChartVars H G) :
    HasDerivAt (fun t : ℝ => G.mat (live H (t • a) e))
      (G.colorMat (stretch H a (e.1,coord e.2))) 0 := by
  dsimp only [stretch]
  rw [show axisEquiv.symm (coord e.2) = e.2 from axisEquiv.symm_apply_apply _]
  by_cases h : e ∈ H.trunks
  · have he (b : ChartVars H G) : live H b e = 1 := H.on_tree _ ⟨e,h⟩
    have hp : linearCopy S.ratio (collect G a.1) e = 0 :=
      if_pos (H.trunk_internal (show (e.1,e.2) ∈ H.trunks from h))
    simp_rw [he]
    rw [dif_pos (show (e.1,e.2) ∈ H.trunks from h)]
    change HasDerivAt _ (G.colorMat (linearCopy S.ratio (collect G a.1) e + 0)) _
    rw [hp, add_zero, map_zero]
    exact hasDerivAt_const ..
  rw [dif_neg (show (e.1,e.2) ∉ H.trunks from h)]
  let l := a.2 (⟨e,h⟩ : H.Free)
  have he (t : ℝ) : live H (t • a) e =
      G.lieExp (t • l) * replica S.ratio (represent (t • a.1)) e := H.off_tree _ ⟨e,h⟩
  simp_rw [he,G.mat_mul]
  have ht : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • l))) (G.colorMat l) 0 := by
    have hd : HasFDerivAt (fun x => G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap
        ((0:ℝ) • l) := by rw [zero_smul]; exact G.expDiff_zero
    have hi : HasDerivAt (fun t : ℝ => t • l) l 0 := by
      simpa using! (hasDerivAt_id' (0:ℝ)).smul_const l
    exact hd.comp_hasDerivAt 0 hi
  have hv : HasDerivAt (fun t : ℝ => G.mat (replica S.ratio (represent (t • a.1)) e))
      (G.colorMat (linearCopy S.ratio (collect G a.1) e)) 0 := by
    unfold linearCopy replica
    split
    · rw [map_zero]; exact hasDerivAt_const ..
    exact represent_rate a.1 (S.ratio.parent e.1,e.2)
  convert! ht.mul hv using 1
  change G.colorMat (linearCopy S.ratio (collect G a.1) e + l) = _
  simp [add_comm]

lemma inclusion_deriv (a : ChartVars H G) :
    fderiv ℝ (inclusion H (G:=G)) 0 a = (a.1, stretch H a) := by
  let d := fderiv ℝ (inclusion H (G:=G)) 0 a
  have he : HasDerivAt (fun t : ℝ => inclusion H (t • a)) d 0 :=
    Push.side _ ((inclusion_smooth H).differentiableAt (by simp)) a
  have hf : ∀ᶠ t : ℝ in 𝓝 0, represent (axisLog H (t • a)) = live H (t • a) := by
    have hg : Tendsto (fun t : ℝ => t • a) (𝓝 0) (𝓝 0) := by
      simpa using! (show Continuous fun t : ℝ => t • a from by fun_prop).tendsto 0
    exact hg.eventually (inclusion_works H)
  apply Prod.ext
  · have hh : HasDerivAt (fun t : ℝ => t • a.1) d.1 0 := he.fst
    have ha : HasDerivAt (fun t : ℝ => t • a.1) a.1 0 := by
      simpa using! (hasDerivAt_id' (0:ℝ)).smul_const a.1
    exact hh.unique ha
  change d.2 = stretch H a
  funext ⟨x,i⟩
  obtain ⟨j,rfl⟩ := axisEquiv.surjective i
  change d.2 (x,coord j) = stretch H a (x,coord j)
  apply G.colorMat_injective
  have hd : HasDerivAt (fun t : ℝ => (inclusion H (t • a)).2 (x,coord j)) (d.2 (x,coord j)) 0 :=
    hasDerivAt_pi.mp he.snd _
  have hu : HasFDerivAt (fun v => G.mat (G.lieExp v)) G.colorMat.toContinuousLinearMap
      ((inclusion H ((0:ℝ) • a)).2 (x,coord j)) := by
    rw [zero_smul, inclusion_zero]; exact G.expDiff_zero
  have ha : HasDerivAt (fun t : ℝ => G.mat (live H (t • a) (x,j))) (G.colorMat (d.2 (x,coord j))) 0 := by
    refine (hu.comp_hasDerivAt 0 hd).congr_of_eventuallyEq ?_
    filter_upwards [hf] with t ht
    rw [← ht, represent_link]; rfl
  exact ha.unique (live_rate H (x,j) a)

lemma from_flat (k : S.Choices) (W : PathData G) (p : Clip) :
    uncurry (tested H k p W) =ᶠ[𝓝 0] flat S k p W ∘ inclusion H := by
  filter_upwards [(inclusion_works H (G:=G))] with z hz
  change mainTerm p W (live H z) + noiseTaylor S _ (live H z) k =
    mainTerm p W (represent (axisLog H z)) + noiseTaylor S _ (represent (axisLog H z)) k
  rw [hz]; rfl

/-- Ticket F03. `Fires` and the spectral/path/step properties here remain inputs. -/
theorem answer : YM.Bid.F03 := by
  intro G c f S h H B p W σ C Λ u v hf hb ht hs hi
  constructor
  · intro k
    have he : ContDiffAt ℝ ω (flat S k p W) (inclusion H 0) := by
      rw [inclusion_zero]; exact flat_smooth h.1 k hi
    exact (he.comp 0 (inclusion_smooth H)).congr_of_eventuallyEq (from_flat (S:=S) H k W p)
  intro k F
  have hv : F =ᶠ[𝓝 0] flat S k p W ∘ inclusion H := from_flat H k W p
  obtain ⟨h0,h1,h2⟩ := flat_jets h.1 k hb ht hf hs hi
  have he := hessian_comp (f := flat S k p W) (inclusion_zero H)
    ((flat_smooth h.1 k hi).of_le le_top) ((inclusion_smooth H).of_le le_top) h1
  refine ⟨hv.eq_of_nhds.trans ?_, hv.fderiv_eq.trans he.1, fun a b => ?_⟩
  · rw [comp_apply,inclusion_zero,h0]
  rw [(hv.iteratedFDeriv ℝ 2).eq_of_nhds, he.2, h2,
    inclusion_deriv H, inclusion_deriv H]
  rfl

end YM.Work.F03
