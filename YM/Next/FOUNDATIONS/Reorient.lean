import YM.Next.FOUNDATIONS.JetReads
import YM.Work.G01

/-!
# Compatibility with moves of the local insert

No independent optimization of coordinates after moving a read. In addition
to the *section* transport law (already in Sound), check local reads on
arbitrary stencil placements. This is local/algebraic only, not transfer
down scales. E.g., estimates with actual `BudgetPoint.dirBound` under an
operation may have costs (it matters from which endpoint the distance
weight is measured); we do NOT assume exact invariance of all bounds.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations

open Function Filter Lattice RG Wilson Source Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}

private lemma lift_rotate {o : Site n} (x : Site n) {X : Support n}
    (h : Nonwrapping X o) (hx : x ∈ X) (s : Signed) :
    s.act (lift (x-o)) = lift (s.act (x-o)) := by
  have ht := h x hx
  refine Eq.symm (lift_eq_iff.mpr ⟨by rw [← wrap_signed, wrap_lift], fun i => ?_⟩)
  obtain ⟨j,rfl⟩ := s.perm.surjective i
  rw [Signed.act_at]
  have hb : (lift (x-o) j).natAbs ≤ separation x o := component_le _ _
  split <;> omega

/-- The test on the torus can use literal reads even when rotating through
negative orientation. Only a **local** comparison, not an equation for
all links of the torus. Endpoints of the flipped edge must be accounted for. -/
lemma test_rotation (H : Hol G) (d : ℕ) (s : Signed) (o b : Site n) {X : Support n}
    (h : Nonwrapping X o) (hn : 2 ≤ n.val) (J : Jet G) (t : ℝ) :
    Agrees X (pull s b (H.testLinks d (affine s b o) J t))
      (H.testLinks d o (changedJet (fun _ => Taylor.turn s.ortho⁻¹) J) t) := by
  let U := H.testLinks d (affine s b o) J t
  let V := expandAt (affine s b o) U
  let W := H.links d J t
  have he (x : Site n) (hx : x ∈ X) (i : Axis) :
      V (s.act (lift (x-o)),i) = W (s.act (lift (x-o)),i) := by
    rw [lift_rotate x h hx]
    simp [V,W,U,expandAt,Hol.testLinks]
  rintro ⟨x,i⟩ hx hi
  let J' := changedJet (fun _ => Taylor.turn s.ortho⁻¹) J
  let z := lift (x-o)
  change pull s b U (x,i) = H.links d J' t (z,i)
  rw [← show expandAt o (pull s b U) (z,i) = pull s b U (x,i) by simp [z,expandAt],
    expandAt_pull, ← Work.G01.swirls_of_flow H s]
  change ((posDir i).rotate s).read V (affine s 0 z) = ((posDir i).rotate s).read W (affine s 0 z)
  simp only [affine, add_zero]
  cases hs : s.flip i
  · rw [show (posDir i).rotate s = posDir (s.perm i) by simp [Lattice.Step.rotate, posDir,hs]]
    exact he x hx _
  have ht : (posDir i).rotate s = negDir (s.perm i) := by simp [Lattice.Step.rotate, posDir, negDir, hs]
  rw [ht, Lattice.Step.neg_read, Lattice.Step.neg_read]
  rw [show s.act z-step (s.perm i)=s.act (lift (x+step i-o)) by
    rw [lift_end hn h x hx, Signed.act_add, ← Lattice.Step.vec_pos i,
      ← Lattice.Step.vec_rotate, ht]; simp [z, sub_eq_add_neg]]
  exact congr_arg Inv.inv (he _ hi _)

lemma reads_pull {H : Hol G} {d : ℕ} {b o : Site n} {X : Support n} {f : Config G n → ℂ}
    {p : Label G d} (h : Reads H o X p f) (hf : LocalOn X f) (hn : 2 ≤ n.val) (s : Signed) :
    Reads H (affine s b o) (X.image (affine s b)) (tensor s.ortho p) (f ∘ pull s b) := by
  have he : Nonwrapping X o ↔ Nonwrapping (X.image (affine s b)) (affine s b o) := by
    constructor
    · intro hp y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      simpa only [affine, separation_signed,separation_translate] using hp x hx
    intro hp x hx
    simpa only [affine,separation_signed,separation_translate] using hp _ (Finset.mem_image_of_mem _ hx)
  unfold Reads at *
  split at h <;> rename_i hX
  · rw [if_pos (he.mp hX)]
    intro J
    dsimp only [comp_apply]
    let A := fun j : ℕ => Taylor.turn (G:=G) (j:=j) s.ortho⁻¹
    let J' := changedJet A J
    rw [show (fun t => f (pull s b (H.testLinks d (affine s b o) J t))) =
      (fun t => f (H.testLinks d o J' t)) from funext fun t => hf _ _ (test_rotation H d s o b hX hn J t)]
    rw [show (fun t => read (scaleJet J t) (tensor s.ortho p).val) =
        (fun t => read (scaleJet J' t) p.val) by
      funext t
      change read _ (changed A _) = _
      rw [eval_changed, show changedJet A (scaleJet J t)= scaleJet J' t from
        funext fun i => map_smul (A i) (t^(i+2)) _]]
    exact h J'
  rw [if_neg (fun hb => hX (he.mpr hb)), h,map_smul, comp_apply]
  have ha : tensor s.ortho (unit G d) = unit G d := Subtype.ext (map_one (rotated (G:=G) s.ortho))
  rw [ha, show pull (K:=G.El) s b 1 = 1 by
    funext x; simp [pull,Lattice.Step.read]]

/-- Ordinary conjugation, not the time-reflected star. -/
lemma reads_bar {H : Hol G} {d : ℕ} {o : Site n} {X : Support n} {f : Config G n → ℂ}
    {p : Label G d} (h : Reads H o X p f) : Reads H o X (realBar p) (star f) := by
  unfold Reads at *
  split at h <;> rename_i hX
  · rw [if_pos hX]
    intro J
    simp only [Pi.star_apply]
    rw [show (fun x => read (scaleJet J x) (realBar p).val) =
      (fun x => star (read (scaleJet J x) p.val)) from funext fun x => conj_value p.val _]
    have he := h J
    let L := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
    change ContDiffAt _ _ (L ∘ (f ∘ H.testLinks d o J)) 0 ∧ _
    refine ⟨L.contDiff.contDiffAt.comp 0 he.1, L.contDiff.contDiffAt.comp 0 he.2.1, fun k hk => ?_⟩
    have hh (w : ℝ → ℂ) (hw : ContDiffAt ℝ k w 0) :
        iteratedDeriv k (L ∘ w) 0 = L (iteratedDeriv k w 0) := by
      unfold iteratedDeriv; rw [L.iteratedFDeriv_comp_left hw le_rfl]; rfl
    have hu := hh (f ∘ H.testLinks d o J) (he.1.of_le (Nat.cast_le.mpr hk))
    exact hu.trans ((congr_arg L (he.2.2 k hk)).trans
      (hh _ (he.2.1.of_le (Nat.cast_le.mpr hk))).symm)
  rw [if_neg hX, h, map_smulₛₗ, unit_real]; rfl

end YM.Next.Foundations
