import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Captains
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Fawn
import YM.Push.LOCAL_SPLITTING.ProductDensity

/-!
# In the forward tube, only invoke inherited E when it's licensed.

No assuming continuity of hard decisions. Want integrands with E mask
 on U HELD FIXED. Re-evaluate anytime even Γ supported on boundary equality.
Full compact ζ controls from Cash.Safety. Propagate to SCRIPT BRANCH for the
comparison even if other ambient controls fail. Keep both κ and χ6 fixed. Arc
neighborhood authorization; not a shrink depending on Z probe. Colors margins
non-strict unless specified. Use full Θ bill returned in sole budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c} {E : Support f} (a : Museum F X.x (bareStores S) E Y I)
variable {W : Config G f} {ζ d A β b t L u v : ℝ} [Fintype I] (h : Canary G d A) (hp : 0<β) {s : Prices G I}

lemma inside_guard (χ : Chi) (hu : 0<u) (hv : 0<v) (he : guard χ G I u v s≠0) (i : I) : u*‖tape s i‖ ≤ v/2 := by
  have ht:=broad_span χ (show 0<v/u/4 by positivity) _ (every_door χ (x:=tape s) he i); rw [mul_comm]
  apply (le_div_iff₀ hu).1; apply ht.le.trans; apply le_of_mul_le_mul_right _ hu; field_simp; linarith

lemma genesis (X : Coat T F) {u:I→G.Color} (h : 0 < ζ*X.t) (he : ∀ i, ‖u i‖ ≤ 2*ζ*X.t) : creates X ζ u=1 := by
  refine Finset.prod_eq_one fun i hi=>?_ ; unfold Chi.innerShare; apply X.χ.to_one
  have hx : 0< 2*ζ*X.t:= by rw [mul_assoc]; positivity
  have hq : 0 ≤ ‖u i‖/(2*ζ*X.t) := div_nonneg (norm_nonneg _) hx.le
  have hv : ‖u i‖/(2*ζ*X.t) ≤ 1 := (div_le_one hx).2 (he i)
  nlinarith

section income
variable {n j p : ℕ} {B B' : BudgetPoint} {C' : Libretto G n} {D : JointLoad.Heir.Record} {χ q : Chi}
  (hP : Plays C' D B B' P T X.x) (hv : Healthy B.threshold Y X.V) (hs : Scrim X a)
include hp hP hv
lemma lampLife {p : Prices G I} (q : Chi) (b : ℝ) (hh : gStep β * ‖tape p‖ ≤ D.ε*B'.threshold) :
    Healthy B'.threshold E (a.received X.k T q b (gStep β) X.V 1 p) := by
  have hβ := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  have hr := hP.rehearsed; have hm := B.order_ge
  exact border_healthy hP.sew C'.width C'.price hr.early (hP.acts F X.k) D.majorant (by rw [← hr.test]; omega) hr.tensions a hP.bulletin C'.Z rfl hr.wire hP.space hr.temp_eq hv _ _ hβ.le hh B'.threshold_pos

variable {J : Type} [TopologicalSpace J] {Z : J → Config G c} {x:J}
variable (q κ : Chi) (b : ℝ)
def magic (D : Record) (B' : BudgetPoint) (β : ℝ) (κ : Chi) := guard κ G I (gStep β) (D.ε*B'.threshold)
def veil (D : Record) (B' : BudgetPoint) (d β : ℝ) (s : Prices G I) (V : Config G c) := magic D B' β κ (reading9 X V a s q b d β)

include hs h
lemma liveIn (hZ : Tendsto Z (𝓝 x) (𝓝 X.V)) (hx : ∀ i, Tendsto (volume9 X a q 1 b i ∘ Z) (𝓝 x) (𝓝 (volume9 X a q 1 b i X.V)))
    (hr : 0 < ζ*X.t) (he : ∀ i, ‖volume9 X a q 1 b i X.V‖ ≤ L * X.t) (hd : L*X.t+D.ε*B'.threshold ≤ ζ*X.t) :
    ∀ᶠ z in 𝓝 x, ∀ u : Prices G I, veil X a q κ b D B' d β u (Z z)≠0 →
      creates X ζ (fawn X (Z z) a u d β)=1 ∧ Healthy B'.threshold E (strip6 X a X.V (anchor X a u β)) := by
  let δ := D.ε * B'.threshold; have ht : 0<δ := mul_pos D.guards B'.threshold_pos
  let g:=gStep β; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr hp)
  filter_upwards [portal_gap X a h hp q b hZ hx (half_pos ht), homing X a h hZ hr (β:=β)] with z hm hv' u hp'
  let y s:=reading9 X s a u q b d β; let m:=y X.V
  have hy (i:I): g*‖tape (y (Z z)) i‖ ≤ δ/2:= inside_guard κ hg ht hp' i
  have hH (i:I) : g*‖tape m i‖ ≤ δ := by
    have h := norm_sub_le_norm_sub_add_norm_sub (tape m i) (tape (y (Z z)) i) 0
    rw [sub_zero,sub_zero] at h
    apply (mul_le_mul_of_nonneg_left h hg.le).trans; rw [mul_add]; apply (add_le_add (hm u i) (hy i)).trans; linarith
  have hh i : ‖anchor X a u β i‖ ≤ ζ*X.t := by
    rw [← sunny X a h u, ← credits X a hp u q]
    apply (norm_add_le ..).trans; rw [norm_smul,Real.norm_of_nonneg hg.le]; exact (add_le_add (he i) (hH i)).trans hd
  refine ⟨genesis X hr (fun i=> ?_),?_⟩
  · let p:= fawn X (Z z) a u d β i; let b:=anchor X a u β i
    refine (show ‖p‖ ≤ ‖p-b‖+‖b‖ by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub p b 0).trans ((add_le_add (hv' u i).le (hh i)).trans (by linarith))
  have H := lampLife X a hp hP hv (p:=m) q b (show g*‖tape m‖≤δ from by rw [mul_comm]; refine (le_div_iff₀ hg).1 ((pi_norm_le_iff_of_nonneg (div_nonneg ht.le hg.le)).mpr (fun i=> (le_div_iff₀ hg).mpr ((mul_comm ..).trans_le (hH i)))))
  have hF: Agrees (inspected E) (a.received X.k T q b g X.V 1 m) (strip6 X a X.V (anchor X a u β)):= by
    have he:= hears9 X X.V a hp hs u q b d; rwa [reading6,fast_zero X a h hp u] at he
  change Disjoint E _; rw [Finset.disjoint_iff_inter_eq_empty,← flags_agree B'.threshold _ _ _ hF]; exact Finset.disjoint_iff_inter_eq_empty.mp H
end income
end YM.PhysicalNext.Repeat.Baffle
