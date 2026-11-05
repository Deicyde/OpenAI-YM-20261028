import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Shell



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Frozen-input shell logarithms 

Extend by zero on real group shells. This patch is part of the affine
reference data, not a constraint on Y: Y is integrated on full Haar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Tree Metric NormedSpace
  YM.Pressure YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {x d : ℝ}

/-- A convenient fixed log patch, independent of LocalRatio choice. -/
def firstRadius (G : Gauge) := (LocalH.geom_patch G).choose
lemma first_pos (G : Gauge) : 0 < firstRadius G := (LocalH.geom_patch G).choose_spec.1

def firstBall (G : Gauge) := ball (0 : G.Color) (firstRadius G)
def firstChart (G : Gauge) := G.lieExp '' firstBall G
lemma first_geom (G : Gauge) : LocalH.Geom G (firstChart G) (firstBall G) :=
  (LocalH.geom_patch G).choose_spec.2 _ le_rfl

lemma over_ball {x : G.Color} (h : x ∈ firstBall G) : LocalH.snap G (G.lieExp x)=x :=
  (first_geom G).2.2.1 h

lemma under_ball {z : G.El} (h : z∈firstChart G) : G.lieExp (LocalH.snap G z)=z :=
  (first_geom G).2.2.2.1 h

def patched (q : Chi) (d : ℝ) (u : G.El) :=
  (firstChart G).indicator (fun z => broad q d (LocalH.snap G z) • LocalH.snap G z) u

/-- No global matrix log or null-set choices in taking Y-dependent
expectations. -/
lemma patched_continuous (q : Chi) (hd : 0 < d) (he : 2*d < firstRadius G) :
    Continuous (patched (G:=G) q d) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let s := firstChart G
  let t := G.lieExp '' closedBall (0:G.Color) (2*d)
  have ht : IsClosed t := ((isCompact_closedBall _ _).image G.lieExp_cont).isClosed
  have hl : t⊆s := image_mono (closedBall_subset_ball he)
  have hs := first_geom G
  let A := fun x : G.El => broad q d (LocalH.snap G x) • LocalH.snap G x
  by_cases hx : u ∈ s
  · have ha : patched q d =ᶠ[𝓝 u] A := by
      filter_upwards [hs.1.mem_nhds hx] with x hh
      exact indicator_of_mem hh A
    have hg : ContinuousAt (LocalH.snap G) u := (hs.2.2.2.2.2.2 u hx).continuousAt.comp G.continuous_mat.continuousAt
    exact (((broad_smooth q d).continuous.continuousAt.comp hg).smul hg).congr ha.symm
  have hy : u∈tᶜ := fun hv => hx (hl hv)
  suffices patched q d (G:=G)=ᶠ[𝓝 u] (fun _ => 0) by
    exact continuousAt_const.congr this.symm
  filter_upwards [ht.isOpen_compl.mem_nhds hy] with z hh
  unfold patched
  by_cases hm : z∈s
  · rw [indicator_of_mem hm]
    have ht : broad q d (LocalH.snap G z) = 0 := by
      by_contra ht
      have hr := broad_span q hd _ ht
      exact hh ⟨_,mem_closedBall.mpr (by simpa using hr.le),under_ball hm⟩
    rw [ht,zero_smul]
  exact indicator_of_notMem hm _

lemma patched_small (q : Chi) (hd : 0 < d) (u : G.El) : ‖patched q d u‖ ≤ 2*d := by
  unfold patched
  by_cases h : u∈firstChart G
  · rw [indicator_of_mem h]; change ‖broad q d (LocalH.snap G u) • _‖ ≤ _
    by_cases hh : broad q d (LocalH.snap G u)=0
    · rw [hh,zero_smul,norm_zero]; positivity
    obtain ⟨hn,ht⟩ := broad_range q (LocalH.snap G u) d
    rw [norm_smul,Real.norm_of_nonneg hn]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (broad_span q hd _ hh).le
  rw [indicator_of_notMem h,norm_zero]; positivity

lemma patched_agrees (q : Chi) (hd : 0 < d) (he : d < firstRadius G) {x : G.Color} (h : ‖x‖ ≤ d) :
    patched q d (G.lieExp x) = x := by
  have hl : x∈firstBall G := mem_ball.mpr (by simpa using h.trans_lt he)
  rw [patched,firstChart,indicator_of_mem (mem_image_of_mem _ hl)]; change broad q d _ • _ = _
  rw [over_ball hl,broad_one q hd h,one_smul]

lemma exp_adjoint (u : G.El) (x : G.Color) :
    G.lieExp (G.adjoint u x) = u * G.lieExp x * u⁻¹ := by
  apply G.mat_injective
  let W := G.mat u
  let X := G.colorMat x
  have he : SemiconjBy W X (W*X*star W) := by change W*X=W*X*star W*W; rw [mul_assoc (W*X),G.mat_star_mul,mul_one]
  have ht := he.exp_right
  change W*exp X = exp (W*X*star W)*W at ht
  simp only [G.mat_lieExp,G.mat_mul,G.mat_inv,G.mat_adjoint,Gauge.conjugate]
  change exp (W*X*star W)=W*exp X*star W
  rw [ht,mul_assoc (exp (_ : G.Mat)),show W * star W = 1 from G.mat_mul_star u, mul_one]

private lemma chart_conj (u v : G.El) (h : v∈firstChart G) : u*v*u⁻¹∈firstChart G := by
  obtain ⟨x,hx,rfl⟩ := h
  exact ⟨G.adjoint u x,by simpa only [firstBall,mem_ball,dist_zero_right,G.norm_adjoint] using hx,exp_adjoint ..⟩

lemma patched_covary (q : Chi) (d : ℝ) (u v : G.El) :
    patched q d (u*v*u⁻¹) = G.adjoint u (patched q d v) := by
  by_cases hv : v∈firstChart G
  · obtain ⟨x,hx,hv'⟩ := hv
    have ht : G.adjoint u x ∈ firstBall G := by simpa only [firstBall,mem_ball,dist_zero_right,G.norm_adjoint] using hx
    subst v; rw [← exp_adjoint]
    unfold patched firstChart
    rw [indicator_of_mem (mem_image_of_mem _ hx),indicator_of_mem (mem_image_of_mem _ ht)]
    change broad _ _ _ • _ = G.adjoint u (broad _ _ _ • _)
    rw [over_ball hx,over_ball ht,map_smul]; simp only [broad,G.norm_adjoint]
  have he : u*v*u⁻¹∉firstChart G := by
    intro hh; apply hv; have he := chart_conj u⁻¹ _ hh; group at he; exact he
  rw [patched,indicator_of_notMem he,patched,indicator_of_notMem hv,map_zero]

lemma patched_inv (q : Chi) (d : ℝ) (v : G.El) : patched q d v⁻¹ = -patched q d v := by
  have hh {v : G.El} (h : v∈firstChart G) : v⁻¹∈firstChart G := by
    obtain ⟨x,hx,rfl⟩ := h
    exact ⟨-x,by simpa [firstBall] using hx,exp_negative x⟩
  by_cases hv : v∈firstChart G
  · obtain ⟨x,hx,hv'⟩ := hv
    have ht : -x ∈ firstBall G := by simpa [firstBall] using hx
    subst v; rw [← exp_negative]
    unfold patched firstChart
    rw [indicator_of_mem (mem_image_of_mem _ hx),indicator_of_mem (mem_image_of_mem _ ht)]
    change broad _ _ _ • _ = -(broad _ _ _ • _)
    rw [over_ball hx,over_ball ht, smul_neg]; simp only [broad,norm_neg]
  rw [patched,indicator_of_notMem (fun h => hv (by simpa using hh h)),patched,indicator_of_notMem hv,neg_zero]

def autoShell (q : Chi) (d : ℝ) (V : Config G c) {A : Stores S} {F : Forest S.ratio}
    (Y : LinkArray G (Frozen A x F)) : LogArray G (Frozen A x F) := fun i =>
  patched q d (Y i * (replica S.ratio V i.val.val)⁻¹)

lemma autoShell_continuous (q : Chi) {A : Stores S} {F : Forest S.ratio} (hd : 0<d) (he : 2*d < firstRadius G) :
    Continuous (uncurry (autoShell (G:=G) (A:=A) (F:=F) (x:=x) q d)) := by
  apply continuous_pi; intro i
  unfold uncurry autoShell
  apply (patched_continuous q hd he).comp
  unfold replica
  split <;> fun_prop

end YM.Next.SectorChange
