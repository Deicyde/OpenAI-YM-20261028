import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Ink
import YM.Work.F05.Actions

set_option warningAsError false

/-! Pull the actual row, orientations, and exp-increment chart to the
fixed reference patch. Select the flattening gauge only ONCE (near the
row being tested); therefore no derivative of the gauge choice is owed.
Preserve both endpoints, this is a rule for pricing a single row, not an
estimate of the whole configuration in a single gauge. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Press
open Function Filter Lattice RG RG.Patch Wilson Pressure Pressure.Tube Precision Exterior Bloch
open YM.Push.SectorMeasure YM.Push YM.Next YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f c' f' : Side} {S : StepData c f} {T : StepData c' f'}

/-- Linear replication of the perturbation in the *left* chart on COMMON
positive links. Crossing tests as stored on the Ratio. -/
def copyKick (G : Gauge) (S : StepData c f) : Directions G c →L[ℝ] Directions G f :=
  (LinearMap.pi fun e => if S.ratio.parent (e.1+step e.2)=S.ratio.parent e.1 then 0 else
    (LinearMap.proj (S.ratio.parent e.1,e.2) : Directions G c →ₗ[ℝ] G.Color)).toContinuousLinearMap

lemma copyKick_eq (S : StepData c f) (b : Directions G c) : copyKick G S b = linearCopy S.ratio b := by
  funext e; change (if _ then _ else (LinearMap.proj _ : Directions G c →ₗ[ℝ] G.Color)) b=_
  unfold linearCopy; split <;> rfl
lemma copyKick_norm (S : StepData c f) (b : Directions G c) : ‖copyKick G S b‖ ≤ ‖b‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; rw [copyKick_eq]
  intro i; unfold linearCopy; split
  · rw [norm_zero]; exact norm_nonneg _
  exact norm_le_pi_norm _ _

lemma copyKick_uses (S : StepData c f) (V : Config G c) (b : Directions G c) :
    replica S.ratio (increment V b)=increment (replica S.ratio V) (copyKick G S b) := by
  rw [copyKick_eq]; unfold replica linearCopy; funext e; unfold increment; split
  next h => simp [h,G.mat_lieExp_zero]
  next h => simp [h]

lemma gauged_facade (S : StepData c f) (V : Config G c) (s : Signed) (w : Site f → G.El)
    (B : Directions G c) (a : Directions G f) :
    gauge (w ∘ affine s 0) (facade S s (increment V B) a) =
      pull s 0 (increment (increment (gauge w (replica S.ratio V)) (swing w (copyKick G S B))) (swing w a)) := by
  unfold facade
  rw [copyKick_uses S V B, swing_increment w, swing_increment w, Work.F05.pull_gauge_zero]; rfl

/-- Copy Q table consumes precise membership only in its stated stencil.
Output uses canonical fine k and actual orientation s. The two gauge endpoints
in the equality are fixed (at ALL b,a); do not replace either by a V transport.
Includes norms NO reference period factor. -/
lemma freshQ (S : StepData c f) (s : Signed) (V : Config G c) (w : Site f → G.El)
    (hB : S.patch.Branches S.kernel G) (i : Bond c) (t : S.Choices) (i' : Bond c') (t' : T.Choices)
    (q : Bond f' → Bond f) (J : Bond f' → Bool)
    (hq : ∀ U : Config G f, S.prediction U (choice s t) i =
      T.prediction (fun e => if J e then U (q e) else 1) t' i')
    {D : ℝ} (hD : 0 ≤ D) (h : ∀ e, J e=true →
        ∃ z : G.Color, ‖z‖ ≤ D ∧ G.lieExp z = gauge w (replica S.ratio V) (sendEdge s 0 (q e))) :
    ∃ (A : Directions G f') (rev : Bond f' → Bool) (L : Directions G c →L[ℝ] Directions G f')
      (M : Directions G f →L[ℝ] Directions G f') (u v : G.El),
      ‖A‖ ≤ D ∧ (∀ B, ‖L B‖ ≤ ‖B‖) ∧ (∀ a, ‖M a‖ ≤ ‖a‖) ∧
        ∀ B a, pasteQ t' rev i' (A, L B, M a) = u * predictGroup (increment V B) t s i a * v⁻¹ := by
  let g (e : Bond f') := sendEdge s 0 (q e)
  let rev (e : Bond f') := s.flip (q e).2
  let X := gauge w (replica S.ratio V)
  let U (e : Bond f') := if hJ : J e=true then (h e hJ).choose else (0:G.Color)
  let P : Directions G f →L[ℝ] Directions G f' :=
    (LinearMap.pi fun e => if J e then (LinearMap.proj (g e) : Directions G f →ₗ[ℝ] _) else 0).toContinuousLinearMap
  let M := P ∘L swing w; let L := M ∘L copyKick G S
  let k := w ∘ affine s 0
  let u := k (S.ratio.embed i.1); let v := k (S.ratio.embed (i.1+step i.2))
  have hp (a : Directions G f) (e : Bond f') : P a e = if J e then a (g e) else 0 := by
    change (if _ then (LinearMap.proj _ : Directions G f →ₗ[ℝ] G.Color) else _) a=_; split <;> rfl
  have hm (a : Directions G f) : ‖M a‖ ≤ ‖a‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro j; change ‖P _ j‖ ≤ _
    rw [hp]; split
    next h => exact (swing_size w a _).trans_le (norm_le_pi_norm a _)
    rw [norm_zero]; exact norm_nonneg _
  refine ⟨U,rev,L,M,u,v,(pi_norm_le_iff_of_nonneg hD).mpr (fun i => ?_),fun b => (hm _).trans (copyKick_norm _ b),hm,?_⟩
  · unfold U; split
    next hJ => exact (h i hJ).choose_spec.1
    rw [norm_zero]; exact hD
  intro B a
  let H := facade S s (increment V B) a
  have hh : imageGroup rev (U,L B,M a) = fun e => if J e then gauge k H (q e) else 1 := by
    funext e; by_cases hJ : J e=true
    · rw [if_pos hJ]
      unfold H k; rw [gauged_facade _ _ _ _, turn_read s]
      have ht : unturned (U,L B,M a) e=increment (increment X (swing w (copyKick G S B))) (swing w a) (g e) := by
        have h1 : M a e=swing w a (g e) := by change P (swing w a) e=_; rw [hp,if_pos hJ]
        have h2 : L B e=swing w (copyKick G S B) (g e) := by change P (swing w _) e=_; rw [hp,if_pos hJ]; rfl
        have h3 : G.lieExp (U e)=X (g e) := by unfold U; rw [dif_pos hJ]; exact (h e hJ).choose_spec.2
        unfold unturned increment; dsimp only [Pi.one_apply]; rw [h1,h2,h3,mul_one]
      unfold imageGroup; unfold g rev X at *; simp_rw [ht]
    rw [if_neg hJ]; unfold imageGroup unturned increment; dsimp only [Pi.one_apply]
    have h1 : M a e=0 := by change P (swing w a) e=_; rw [hp,if_neg hJ]
    have h2 : L B e=0 := by change P (swing w _) e=_; rw [hp,if_neg hJ]
    have h3 : U e=0 := by unfold U; rw [dif_neg hJ]
    simp_rw [h1,h2,h3,G.mat_lieExp_zero,one_mul]; simp
  unfold pasteQ
  rw [hh,← hq,(choice_gauge hB H (choice s t) k).2]; rfl
end YM.AnalyticBridge.Covariance.Press
