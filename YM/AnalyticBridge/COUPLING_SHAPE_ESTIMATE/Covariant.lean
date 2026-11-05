import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Clover
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Projection
import YM.Push.LOCAL_SPLITTING.Orientation



/-! # Sites and colors of the affine subtraction

Includes the case of wrapping atoms whose budget doesn't buy a projection.
Projection test for a nonwrapping incoming address X can be done with
an enlarged X ∪ Clover, not prematurely testing a gradient after truncating
actual paths. Nothing here rotates through separate reset choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Filter Function Lattice Wilson RG Push.Local ProjectorNext.Equivariance
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side}

open StressFlux (clover sign)
def parityPrice (s : Signed) (p : PlaqAxes) := sign s p.val.1 * sign s p.val.2 * if s.perm p.val.1 < s.perm p.val.2 then 1 else -1
lemma parityPrice_abs (s : Signed) (p : PlaqAxes) : |parityPrice s p|=1 := by unfold parityPrice sign; split_ifs <;> norm_num

def swivels (G : Gauge) (s : Signed) : Flux G →L[ℝ] Flux G := LinearMap.toContinuousLinearMap {
  toFun U p := parityPrice s p • U (PlaqAxes.transform s p)
  map_add' := fun x y => funext fun i => smul_add ..
  map_smul' := fun x y => funext fun i => by simp only [RingHom.id_apply, Pi.smul_apply]; apply smul_comm }

lemma spins (U : Config G n) (s : Signed) (b o : Site n) :
    needles o (pull s b U) = swivels G s (needles (affine s b o) U) := by
  funext p
  change clover (pull s b U) o _ _ =parityPrice s p • needles (affine s b o) U (PlaqAxes.rotate s p)
  let x:=p.1.1; let y:=p.1.2
  have he := StressFlux.clover_pull s b U o x y; rw [he]; unfold parityPrice needles PlaqAxes.rotate PlaqAxes.ordered
  rcases lt_or_gt_of_ne (show s.perm x≠s.perm y from s.perm.injective.ne p.property.ne) with hh|hh
  · simp only [min_eq_left hh.le,max_eq_right hh.le,hh, if_true,mul_one, x,y]
  rw [StressFlux.clover_swap U _ (s.perm x)]
  simp [min_eq_right hh.le, max_eq_left hh.le, if_neg (not_lt.mpr hh.le) , x,y]

lemma pull_empty (s : Signed) (z : Site n) : pull s z (1:Config G n)=1 := by funext; unfold pull Step.read; split <;> simp

lemma pull_skew (s : Signed) (z : Site n) (hn : 2 ≤ n.val) {X : Support n} {o : Site n} (hx : Nonwrapping X o)
    (ht : ringlet o ⊆ X) {A : Directions G n} {c d} (hA : OnStencil (affine s z o) (X.image (affine s z)) c d A)
    {c' d'} (he : OnStencil o X c' d' (pulledDirection s z 1 A)) :
    skew d'=swivels G s (skew d) := by
  have h₁ := clover_jet o hn hx he ht
  have h' : Nonwrapping (X.image (affine s z)) (affine s z o) := (nonwrapping_turn s z o X).mpr hx
  have h₂ := clover_jet _ hn h' hA (by rw [ringlet_turn]; exact Finset.image_subset_image ht)
  have hh := (swivels G s).hasFDerivAt.comp_hasDerivAt (0:ℝ) h₂
  have ht (t : ℝ) : needles o (increment 1 (t • pulledDirection s z 1 A)) = swivels G s (needles (affine s z o) (increment 1 (t • A))) := by
    rw [← map_smul,← show pull s z (increment 1 (t • A))=increment 1 (pulledDirection s z 1 (t • A)) by rw [pull_increment,pull_empty]]
    exact spins ..
  simp_rw [ht] at h₁; exact h₁.unique hh

lemma strip_via_pull (s : Signed) (z : Site n) (hn : 10<n.val) {p : BudgetPoint} {o : Site n} {X : Support n}
    {f : Config G n→ℝ} (hs : G.Simple) (hf : p.Regular X f) (hg : p.Regular (X.image (affine s z)) (f ∘ pull s z)) (x y) :
    stripJet (f ∘ pull s z) (affine s z o) (X.image (affine s z)) x y=stripJet f o X (swivels G s x) (swivels G s y) := by
  by_cases hX : Nonwrapping X o
  · let g:= f ∘ pull s z; let X':= X∪ringlet o; let o':=affine s z o; let Z:= X.image (affine s z)
    have hz : Nonwrapping Z o' := (nonwrapping_turn ..).mpr hX
    have hw : Nonwrapping X' o := fun x hx => (Finset.mem_union.mp hx).elim (hX x) (unwound hn o x)
    have he (u : Flux G) : stripJet g o' Z u u=stripJet f o X (swivels G s u) (swivels G s u) := by
      let A:=rise G o' u
      have hA := rise_hits u o' (X'.image (affine s z))
      obtain ⟨c,d,hB⟩:=pull_onSt s z (by omega) hw hA
      have hk := pull_skew s z (by omega) hw Finset.subset_union_right hA hB
      rw [lower_skew] at hk
      rw [strip_on hz]; change H g A A= _
      rw [← hk,← strip_affine (by omega) hX hs hf (hB.mono Finset.subset_union_left) (hB.mono Finset.subset_union_left),
        diagonal hs hg,diagonal hs hf]
      dsimp only [A]; simp_rw [comp_apply,pull_increment s z,pull_empty,map_smul]
    have ht := he (x+y); simp only [map_add, add_apply, strip_symm hf _ (swivels G s y) (swivels G s x),he] at ht
    change stripJet g o' Z x y=_; linarith [strip_symm (f:=g) (X:=Z) hg o' x y]
  have hx : ¬Nonwrapping (X.image (affine s z)) (affine s z o) := mt (nonwrapping_turn ..|>.mp) hX
  simp [stripJet,hx,hX]
end YM.AnalyticBridge.CouplingShape
