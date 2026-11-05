import YM.Next.FREE_KERNELS.Signal
import YM.Next.UV_STRESS.SpanQ
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.PRICE_COMPILER.Suppression
import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size

/-!
# Palette at degree four with only one- and two-point requests

Preserves common generic configuration and works with frames on the given
Family. Existential accuracy as for SpanQ (no numerical condition number).
Doesn't assert any of `Marking.Seen` at these points.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule Wick MeasureTheory Analysis Filter
open scoped Topology ContDiff
variable {G : Gauge} (C : Family G) (F : Frames G) {n : ℕ}

-- homogeneity also without `Hierarchy`
private lemma traveled (x : Points n) (z : E4) (W : Powers G n) : Wick.monomial (Points.across z x) W=Wick.monomial x W := by
  unfold Wick.monomial
  simp [Occ.graph,Occ.edge,entry]

lemma home (x : Points n) (z : E4) (v : Fin n → WickPol G) : moment G (Points.across z x) v = moment G x v := by
  simp_rw [sumFormula,traveled]

lemma hearing_home (x : Points 2) (z : E4) (a b i k : Axis) (v : FourFields F) :
    hearing F (Points.across z x) a b i k 4 v=hearing F x a b i k 4 v := by
  simp_rw [listens]
  let q := Fin.cons (α:=fun _ : Fin (1+1) => (freeTable F).Tag) ⟨4,v⟩ (negs F a b i k)
  exact home x z (fun i => observable G (q i).1 ((F.level (q i).1).coords.symm ((freeTable F).representative (q i).1 (q i).2)))

abbrev soundtrack (x : Points 2) : Option Face → FourFields F →ₗ[ℂ] ℂ
  | none => expectation (freeTable F) 4
  | some ⟨(p,q),_⟩ => hearing F x p.val.1 p.val.2 q.val.1 q.val.2 4

def groupMic (x : Points 2) : FourFields F →L[ℂ] (Option Face → ℂ) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi (soundtrack F x))

private theorem sector_exact (hG : G.Simple) : ∀ z : E4, Injective (groupMic F (Points.across z (camera 0))) := by
  intro z p q hp
  let b := stand F hG
  suffices ht : ∀ i, b.repr p i=b.repr q i by
    apply b.repr.injective; exact Finsupp.ext ht
  have he (i : Option Face) (v : FourFields F) : b.repr v i = portLine F i v := by
    conv_rhs => rw [← b.sum_repr v]
    have hb (j : Option Face) : b j=embed F 4 (sectors j) := Module.Basis.mk_apply ..
    simp only [map_sum,map_smul,hb,separates F hG, smul_eq_mul,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
  intro i; simp_rw [he]
  have h := congr_fun hp i
  rcases i with _|⟨⟨a,b⟩,k⟩
  · exact h
  change hearing F (Points.across z _) _ _ _ _ 4 p = hearing F _ _ _ _ _ 4 q at h
  simp_rw [hearing_home] at h
  unfold portLine reader negative; simp only [LinearMap.smul_apply]; congr 2

private lemma hears_cont {x : Points 2} (hz : x∈conf _) (i j k l : Axis) (v : FourFields F) :
    ContinuousAt (fun y => hearing F y i j k l 4 v) x := by
  simp_rw [listens]
  exact (((freeTable F).class_smooth _ (table_smooth F) _ _ hz).contDiffAt ((conf_open _).mem_nhds hz)).continuousAt

-- all requests can be moved on one configuration (any displacement here small enough).
lemma open_air {x : Points 2} (h : x∈conf _) : ContinuousAt (groupMic F) x := by
  let b := Module.finBasis ℂ (FourFields F)
  let i := Fin (Module.finrank ℂ (FourFields F))
  let W : (i → Option Face → ℂ) →ₗ[ℂ] FourFields F →L[ℂ] (Option Face → ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℂ).toLinearMap
  have he y : groupMic F y = W (fun j => groupMic F y (b j)) := by
    apply ContinuousLinearMap.coe_injective; exact b.ext fun j => (b.constr_basis ℂ (fun k => groupMic F y (b k)) j).symm
  rw [show groupMic F = (fun y => (W (fun j => groupMic F y (b j)))) from funext he]
  apply W.continuous_of_finiteDimensional.continuousAt.comp
  unfold ContinuousAt
  apply tendsto_pi_nhds.mpr; intro j
  apply tendsto_pi_nhds.mpr; intro p
  rcases p with _|⟨⟨r,w⟩,hw⟩
  · exact tendsto_const_nhds
  exact hears_cont F h r.val.1 r.val.2 w.val.1 w.val.2 (b j)


def slope : E4 := WithLp.toLp 2 fun _ => 1
def tilt (r : ℝ) : E4 := -YM.basis 0-r • slope
def sloping (r : ℝ) : Points 2 := points (readings 0 (tilt r))

private lemma slope_at (a : Axis) : slope a=(1:ℝ) := rfl

theorem gentle : Continuous sloping := by
  unfold sloping
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E4)).symm.continuous.comp
  refine continuous_pi ?_; intro i; rcases (show i=0∨i=1 by omega) with rfl|rfl
  exact continuous_const
  simp only [read_one,tilt]; exact continuous_const.sub (continuous_id.smul continuous_const)

lemma generic_tilt {r : ℝ} (hp : 0<r) : sloping r ∈ generic 2 := by
  intro a i j h
  have he : sloping r 0 a ≠ sloping r 1 a := by
    simp only [sloping,points_apply,read_zero,read_one,tilt,WithLp.ofLp_zero,Pi.zero_apply, PiLp.sub_apply,PiLp.smul_apply, PiLp.neg_apply,
      smul_eq_mul,slope_at,mul_one,basis_eq]
    split_ifs <;> linarith
  rcases (show i=0∨i=1 by omega) with rfl|rfl <;> rcases (show j=0∨j=1 by omega) with rfl|rfl
  exacts [rfl,(he h).elim,(he h.symm).elim,rfl]

lemma tilted_home : sloping 0=Points.across (-YM.basis 0) (camera 0) := by
  ext1 i
  rcases (show i=0∨i=1 by omega) with rfl|rfl <;> simp [sloping,camera,tilt]

def picker (r : ℝ) (h : 0<r) : Option Face → Palette C
  | none => ⟨0, blank (Bel C.book), (0:Points _), fun _ _ _ _ => @Subsingleton.elim (Fin 1) _ _ _,rfl⟩
  | some ⟨(p,q),_⟩ => ⟨1,negs C.book.grid p.val.1 p.val.2 q.val.1 q.val.2, sloping r, generic_tilt h, rfl⟩

lemma palette_run (r : ℝ) (h : 0<r) (v : Entry C) : ∀ i,
    (picker C r h i).eval C v = groupMic C.book.grid (sloping r) v i
  | none => rfl
  | some ⟨(_p,_q),_hp⟩ => rfl

def picked (r : ℝ) (h : 0<r) := by
  classical exact Finset.univ.image (picker C r h)

-- All sufficiently small (positive) fan tilts work. Existential budget, no
-- numerical gate claim for δ. The requested tolerance can be chosen after C
-- & geometry alone, before stations & offsets.
theorem tests (hG : G.Simple) : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ h : 0<r,
    (Injective (groupMic C.book.grid (sloping r))) ∧ ∃ ε : ℝ,0<ε ∧ sturdy C (picked C r h) ε := by
  classical
  let F := C.book.grid
  let i0 : Points 2 := sloping 0
  have ht : ContinuousAt (fun r => groupMic F (sloping r)) (0:ℝ) := by
    apply ContinuousAt.comp (g:=groupMic F) ?_ gentle.continuousAt
    exact open_air F (by rw [tilted_home]; exact Points.across_in _ (shutter 0))
  have hj : Injective (groupMic F (sloping 0)) := by rw [tilted_home]; exact sector_exact F hG _
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [ht.tendsto.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hj)] with r hr
  intro h
  refine ⟨hr, sturdy_exists C (picked C r h) ?_⟩
  intro y z he; apply hr; funext i
  change groupMic C.book.grid _ _ _ = groupMic C.book.grid _ _ _
  simp_rw [← palette_run C r h]
  exact congr_fun he (show ↑(picked C r h) from ⟨picker C r h i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)

end YM.UVNext.FreeStress
