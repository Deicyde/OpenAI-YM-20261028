import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Hinges
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Rod
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Iceland

/-!
# Hold mask convention at U on both readings

Detection fixed by the *actual* Choice stencil. Credited even if term is
inside a partially flagged pole. Do not change E's unmasked extension.
A universal testing family on all positions; even when U(f)-V close not
licensed unless actual guard plateau. `a: scrim`. Tuple coordinates with
Φ canopy cone in all of I. Even equality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} (V : Config G c) {E : Support f} (a : Museum F X.x (bareStores S) E Y I)
variable {W : Config G f} {ζ d A β b : ℝ} [Fintype I] (h : Canary G d A) (hp : 0<β) (hv : Drivable X d A V) (hs : Scrim X a)

section locked
variable (z : Prices G I)

abbrev reading6 (d β : ℝ) := fast X V a d β z
abbrev anchor (β : ℝ) := peanuts X a X.V β z
def fawn (d β : ℝ) (i : I) := fleece G X.χ d (G.mat (action X V (a.address i))) (anchor X a z β i)
def distance9 (q : Chi) (b β : ℝ) := (gStep β)⁻¹ • tape.symm ((fun j=> -(offsetRun X a j q b (1:Config G f) V)):LogArray G I)
abbrev reading9 (q : Chi) (b d β : ℝ) := fast X V a d β z+distance9 X V a q b β

include hp
lemma to_strip (d:ℝ) : peanuts X a V β (reading6 X V a z d β)=fawn X V a z d β := by
  funext i; rw [peanuts,reading6,fast,tape.apply_symm_apply]; unfold hang chore
  change _+(gStep β) • ((gStep β)⁻¹ • (_-volume6 X a i V))=_; rw [smul_inv_smul₀ (show gStep β≠0 from (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'), add_sub_cancel]; rfl

lemma record9 (q : Chi) (b d : ℝ) (i:I) : a.deposited X.k T q b (gStep β) V 1 (reading9 X V a z q b d β) (a.seat i)= fawn X V a z d β i := by
  rw [← to_strip X V a hp z d, Museum.deposited, a.seat.injective.extend_apply]
  let v6:= volume6 X a i V; let v9:= volume9 X a q 1 b i V; let g:=gStep β; have hg:g≠0:= (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'
  let W:= reading6 X V a z d β; let s:=distance9 X V a q b β
  have he: tape s i=g⁻¹ • -(v9-v6) := by
    change colors _ _= _; unfold s distance9; rw [map_smul]; rfl
  change v9+g • tape (W+s) i=v6+ g • tape W i; rw [show tape (W+s)=tape W+tape s from colors.map_add _ _,Pi.add_apply,smul_add, he, smul_inv_smul₀ hg]; abel

include hs in
lemma hears9 (q : Chi) (b d : ℝ) : Agrees (inspected E) (a.received X.k T q b (gStep β) V 1 (reading9 X V a z q b d β))
    (strip6 X a V (peanuts X a V β (reading6 X V a z d β))) := by
  rw [to_strip X V a hp z]
  intro i hi hj
  by_cases hh : i∈F.trunks
  · exact (F.on_tree _ ⟨i,hh⟩).trans (F.on_tree _ ⟨i,hh⟩).symm
  obtain ⟨j,H⟩:= falls X a ⟨i,hh⟩ hi hj; change a.address j=i at H; subst i
  unfold Museum.received; unfold physical Next.SectorChange.returned thaw; rw [strip6, (vary X V).viewing _ _ (borne X a hs j)]
  rw [increment, tap]
  have hx := record9 X V a hp z q b d j
  change F.drape _ ((a.seat j).val.val)=_; rw [F.off_tree,freeze_regular]; unfold release; rw [hx]; rfl

include h in
lemma fast_zero : fast X X.V a d β z = z := by
  apply tape.injective; funext i
  unfold fast hang; rw [tape.apply_symm_apply,chore]
  change (gStep β)⁻¹ • (fleece G X.χ d (G.mat (action X X.V (a.address i))) _ - voltage X (a.address i))=tape z i
  rw [Silica.action,mul_inv_cancel,G.mat_one,nothing_f h, id_eq,add_sub_cancel_left,inv_smul_smul₀ (show gStep β≠0 from (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne')]

include hv h hs
-- off-mask held input, when Enforce not zero
omit hp in
lemma felt (ha : 0<ζ*X.t) (he : 8*ζ*X.t ≤ d/2) (hh : creates X ζ (fawn X V a z d β)≠0) :
    Agrees (inspected E) (strip6 X a V (fawn X V a z d β)) (strip6 X a X.V (anchor X a z β)) := by
  let u:= isotope X a (anchor X a z β); let v:= steer X d u V; let U:= vary X V
  have hr j:v (a.address j)=fawn X V a z d β j := by unfold v u steer; rw [tap]; rfl
  have hp := (conquered X h V u hv ha he)
  intro i hi hj
  apply Eq.trans ((entered X a hs (V:=V) X.Y v hr i hi hj).symm)
  refine hp.same i (or_iff_not_imp_left.mpr fun hb=> ?_)
  have hb:= not_not.mp hb
  obtain ⟨j,hj'⟩ := falls X a ⟨i,hb.1⟩ hi hj; change a.address j=i at hj'; subst i
  have ht' : U.cone (2*ζ) v (a.address j)≠0 := by
    unfold Coat.cone; rw [hr]; exact Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ _)
  change ‖v (a.address j)‖≤4*(2*ζ)*U.t
  exact (U.amount (show 0 < 2*ζ*U.t by change 0 < 2*ζ*X.t; rw [mul_assoc]; positivity) _ _ ht').trans (by change _ ≤ 4*(2*ζ)*X.t; change 2*(2*ζ)*X.t ≤ _; nlinarith only [ha])
end locked
end YM.PhysicalNext.Repeat.Baffle
