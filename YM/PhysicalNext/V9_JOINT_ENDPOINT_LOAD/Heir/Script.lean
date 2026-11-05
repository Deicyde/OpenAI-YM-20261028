import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.AuditHits
import YM.AnalyticBridge.RESET_INCOME_PORT.LocalPrice
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Crowd
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Reading


/-! # Full price support kept even through fixed finite θ mixtures

Pricing-only input register for `L_X`, *not* reconstruction of physical
sector/factor dictionary. All the argument/seat/postal requirements have
to be met (and averaged authentically) in addition at actual uses of the
returned fields. For example, not prescribing alternate or aligned `k` to
satisfy them, restricting tested coordinates when a mixture coefficient
vanishes, nor inserting a likelihood at the exterior of the mixture. Y
must carry all relevant queries at the caller, not the support of a sample
term that differs from it by an outer-hull extension. Exclusive random
variables, not a product of E-exponents. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.SectorChange.Rows Wisps WardBin.Lies
    Precision Next.Fluctuations Exterior Bloch Bid Push.SectorMeasure AnalyticBridge.LocalGaussian
open Push.AbsoluteSums MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {o : Site f} {S : StepData c f} {V : Config G c} {X : Support f} {Y : Support c}
    {x u τ : ℝ} {q : Chi} {d : ℝ} {z : Desk G S} {D : Record} {n r : ℕ} {C : Libretto G n} {P B : BudgetPoint} {f' : Config G f → ℝ} {Pt : Teller G} {T : Tube G S}

structure Script (G : Gauge) (S : StepData c f) (X : Support f) (Y : Support c) (r : ℕ) (x : ℝ) where
  Tag : Type
  [basis : Fintype Tag]
  Keys : Tag → Type
  [fin : ∀ i, Fintype (Keys i)]
  [dec : ∀ i, DecidableEq (Keys i)]
  chart : Tag → Stores S
  forest : Tag → Forest S.ratio
  θ : Tag → S.Choices
  fits i : Museum (forest i) x (chart i) X Y (Keys i)
  profile i : Prices G (Keys i) → ℝ
  moves i : (fits i).Natural (profile i)
  coefficient : Tag → ℝ
  admissible : ∑ i, |coefficient i| ≤ 1
  fields : Walled S X Y x r

attribute [instance] Script.basis Script.fin Script.dec

lemma mixture (J : Type) [Fintype J] {f : J → Config G c → ℝ} {α : J → ℝ} {o : Site c} (hτ : 0 ≤ τ) (ha : ∑ i, |α i| ≤ 1) (hr : ∀ i,P.Regular Y (f i))
    (he : ∀ i, P.supBounds o Y (f i) τ) : let F := ∑ i,α i • f i; P.Regular Y F ∧ P.supBounds o Y F τ := by
  intro F
  let L (j) := α j • ContinuousLinearMap.id ℝ ℝ
  have h (i : J) (U : Config G c) (hU : Healthy P.threshold Y U) : Push.Local.Chart P.order (α i • f i) U := (hr i).smooth U hU |>.const_smul (α i)
  have hF (U : Config G c) (hU : Healthy P.threshold Y U) : Germ P.order F U := by
    unfold WardBin.Lies.Germ F; simp_rw [Finset.sum_apply]; exact ContDiffAt.sum (fun i _ => h i U hU)
  have hf (i) := (hr i).borel
  refine ⟨⟨(fun U V h => by simp [F,(hr _).sites U V h]),(by unfold F; fun_prop),fun k U => by simp [F,(hr _).symmetry k U],fun U hv => hF U hv, fun U hv A l hl => (hF U hv).has l A hl⟩,hτ,fun U hU l hl hA => ?_⟩
  unfold F; rw [Push.Local.left_sum _ _ _ _ (fun i _ => h i U hU) hl]; apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i,|α i| * τ := Finset.sum_le_sum (fun i _ => by
      rw [show α i • f i=L i ∘ f i from rfl, Push.Local.left_linear (L i) l ((hr i).smooth _ hU) hl,smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left ((he i).2 _ hU _ hl hA) (norm_nonneg _))
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left hτ ha

namespace Script
variable (s : Script G S X Y r x) (u q d T f')
def tuning := ∑ i, s.coefficient i • ((s.fits i).principal T u q d (s.θ i) f' (s.profile i))
structure Played (s : Script G S X Y r x) (n : ℕ) (u t : ℝ) : Prop where
  stage i : Silences G (s.Keys i) n u t (s.profile i)
variable {u q d T f'}

lemma choirs (hg : G.Simple) (hT : Plays C D P B Pt T x) (hS : Seed B o X f') (hτ : B.supBounds o X f' τ) (hu : 0 ≤ u) (hp : s.Played n u (D.ε*B.threshold)) :
    P.Regular Y (s.tuning u q d f' T) ∧ P.supBounds (S.ratio.parent o) Y (s.tuning u q d f' T) (τ*Lute.returnFee C D P B S.patch.L X r x u) := by
  have hh := D.peak; have h := hτ.1
  exact mixture s.Tag (by unfold Lute.returnFee AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate
                          positivity [Lute.beat_nn C,Lute.decay_pos (L:=S.patch.L) (X:=X) (B:=B), Lute.rust_nn hu (C:=C) (D:=D) (P:=P) (B:=B) (L:=S.patch.L) (r:=r) (x:=x) (X:=X)]) s.admissible
    (fun i => (s.fits i).grown hg hT hS hτ s.fields hu (hp.stage i) (s.moves i)) (fun i => Lute.hall hg (s.fits i) hT hS hτ s.fields hu (hp.stage i))

structure Addressed (V : Config G c) (s : Script G S X Y r z.betaHat) (A' : s.Tag → Stores S) (F' : s.Tag → Forest S.ratio) (k' : s.Tag→S.Choices) where
  ear i : Museum (F' i) z.betaHat (A' i) X Y (s.Keys i)
  indices i : (s.fits i).address=(ear i).address
  order i : Folio.Postal Y (s.chart i) (A' i) (s.forest i) (F' i) V V (s.θ i) (k' i)
  lawful i : ((spectacle z (A' i) (F' i) (k' i)).C V).PosSemidef


end Script
end YM.PhysicalNext.JointLoad.Heir
