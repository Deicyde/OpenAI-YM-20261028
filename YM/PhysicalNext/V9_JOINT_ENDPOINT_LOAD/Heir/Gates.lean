import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Pastoral

/-! # Centred noise profile example satisfying BOTH Silences and Natural

Use all keys in registered list, on the actual fine-coupling scaled
radius. No claim of joint legitimacy of the removal/addition of this
occurrence in a hard companion field or through the larger sets of
variables that must still pass defaults / raw sector tests. No parameter
regularity estimate of this profile needed for the principal singleton's
V derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Metric Set Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.SectorChange.Rows Wisps
    Precision Next.Fluctuations Exterior Bloch Bid Push.SectorMeasure AnalyticBridge.LocalGaussian
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {X : Support f} {Y : Support c} {F : Forest S.ratio} {A : Stores S}
    {x u t : ℝ} {D : Record} {n r : ℕ} {I : Type} [Fintype I]

def guard (χ : Chi) (G : Gauge) (I : Type) [Fintype I] (u t : ℝ) (z : Prices G I) := doors χ ((t/u)/4) (tape z)

variable (χ : Chi)
lemma guard_open (hu : 0<u) (ht : 0<t) {z : Prices G I} (h : ∀ i,u*‖tape z i‖ ≤ t/8) : guard χ G I u t z = 1 := Finset.prod_eq_one fun i _ => broad_one χ (by positivity)
    (le_trans (by apply (le_div_iff₀ hu).mpr; simpa only [mul_comm] using h i : ‖tape z i‖ ≤ t/8/u) (by apply le_of_mul_le_mul_left _ hu; field_simp; linarith))

lemma guard_silent (hu : 0<u) (ht : 0<t) : Silences G I n u t (guard χ G I u t) := by
  let d := (t/u)/4; have hd : 0<d := by unfold d; positivity
  haveI : ProperSpace (LogArray G I) := FiniteDimensional.proper ℝ _
  have hK : tsupport (guard χ G I u t) ⊆ gaugeCount ⁻¹' closedBall (0:LogArray G I) (t/u) := by
    refine closure_minimal (fun z hz => mem_closedBall_zero_iff.mpr ?_) (isClosed_closedBall.preimage gaugeCount.continuous)
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => le_trans (broad_span χ hd _ (every_door χ (x:=tape z) hz i)).le (by unfold d; linarith only [div_pos ht hu]))
  have he : ContDiff ℝ ∞ (guard χ G I u t) := (doors_smooth χ d (ι:=I) (G:=G)).comp (@gaugeCount G I _).contDiff
  refine ⟨fun z => ?_,fun z hz => ?_, he.of_le (mod_cast le_top), (gaugeCount.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)).of_isClosed_subset (isClosed_tsupport _) hK⟩
  · rw [guard,doors,Finset.abs_prod]; exact (Finset.prod_le_prod (g:=fun _ => (1:ℝ)) (fun i _ => by positivity) (fun i _ => by
      have h := broad_range χ (tape z i) d; exact abs_le.mpr ⟨le_trans (by norm_num) h.1,h.2⟩)).trans_eq Finset.prod_const_one
  have h := (le_div_iff₀ hu).mp (mem_closedBall_zero_iff.mp (hK hz)); rwa [mul_comm];

lemma guard_natural [DecidableEq I] (M : Museum F x A X Y I) : M.Natural (guard χ G I u t) := by
  intro g z
  rw [guard,guard,Museum.toned, ascent_read]; unfold doors broad; apply Finset.prod_congr rfl fun i _ => ?_
  change χ.innerShare _ ‖G.adjoint _ (tape z i)‖=_; rw [G.norm_adjoint]
end YM.PhysicalNext.JointLoad.Heir
