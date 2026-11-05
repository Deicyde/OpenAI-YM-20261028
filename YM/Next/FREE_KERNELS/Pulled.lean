import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Hadamard
import YM.Next.FREE_KERNELS.Curl

/-!
# Reindexing under signed transformations

The compared precision K is the one *attached to the path*, not a translation
averaged over another cutoff. Use diagonal H (K unchanged later). Negative
axes move the canonical anchor; equal-axis *pair* diagonal entries move both
anchors identically even on even side. Scalar real first, then each color.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {j : ℕ} {n : Side}

lemma signed_base {p : Momentum} (hp : p∈baseCube) (s : Signed) : s.act p ∈ baseCube := by
  rw [show baseCube = {p | physical p ∧ ∀ i, |(p i).re| ≤ Real.pi} from rfl]
  refine ⟨(physical_iff _).mpr ?_,?_⟩ <;> intro i <;> obtain ⟨i,rfl⟩ := s.perm.surjective i <;> rw [Signed.act_at]
  · have h := (physical_iff p).mp hp.1 i; split <;> simp [h]
  have h := hp.2 i; split <;> simpa

lemma dollar_sign (s : Signed) (k : ℝ) (v : Train j) (p : Momentum) : v.rho k (s.act p)=v.rho k p := by
  unfold Train.rho
  rw [← Equiv.sum_comp s.perm (fun i => jewel 1 (s.act p) i / v.levelD k i (s.act p))]
  refine Finset.sum_congr rfl fun i _ => ?_; rw [Train.D_signed,jewel_one,jewel_one,Signed.act_at]; split <;> simp only [neg_neg]; ring

private lemma holding (s : Signed) (f g : Axis → ℂ) (p : PlaqAxes)
    (h : ∀ i, f i=g (s.perm i)) : inventory (plaquette p) f=inventory (plaquette (p.rotate s)) g := by
  have he (p : PlaqAxes) (f : Axis → ℂ) : inventory (plaquette p) f = f p.val.1 * f p.val.2 := by simp [inventory,plaquette,p.property.ne]
  rw [he,he,h,h]; unfold PlaqAxes.rotate PlaqAxes.ordered; dsimp only
  rcases lt_or_gt_of_ne (s.perm.injective.ne p.property.ne) with h|h
  · rw [min_eq_left h.le,max_eq_right h.le]
  rw [min_eq_right h.le,max_eq_left h.le,mul_comm]
lemma pink_sign (s : Signed) (k : ℝ) (hk : 0<k) (v : Train j) (p : PlaqAxes) {q : Momentum} (hq : q∈baseCube) :
    let a := plaquette p; let b := plaquette (p.rotate s)
    pulse k v q a a = pulse k v (s.act q) b b := by
  intro a b; have hx := base_subset_realCube zone_pos hq; have hy := base_subset_realCube zone_pos (signed_base hq s)
  by_cases he : q=0
  · simp [he]
  have ht : s.act q≠0 := Signed.act_zero (R:=ℂ) s ▸ s.act_injective.ne he
  rw [pulse_sources _ hk _ hx he,pulse_sources _ hk _ hy ht, dollar_sign]
  simp only [mask,Matrix.smul_apply,Matrix.diagonal_apply_eq]
  apply congr_arg (fun z : ℂ => (Train.rho k v q)⁻¹ * z); unfold a b; exact holding s _ _ p fun i => congr_arg Inv.inv (Train.D_signed k v i s q).symm

lemma prompt_flip (s : Signed) (p : Momentum) (x : Cover) : mode (s.act p) (s.act x) = mode p x := by
  unfold mode; congr! 2
  rw [← Equiv.sum_comp s.perm (fun i => s.act p i*(s.act x i))]; refine Finset.sum_congr rfl fun a _ => ?_; simp only [Signed.act_at]; split <;> simp

lemma pink_row (s : Signed) (k : ℝ) (hk : 0<k) (hj : 4≤j) (v : Train j) (p q : PlaqAxes) :
    let f := pink k v
    let a := plaquette p; let b := plaquette q
    let x := plaquette (p.rotate s); let y := plaquette (q.rotate s)
    (∀ z : Cover, f a b z=f x y (s.act z)) ∧ (a≠b → f a b=0) := by
  intro f a b x y
  obtain ⟨h,_⟩ := heart_true k hk hj v
  have hx : f.safe := h.safe
  have he (a b : TypeFace 2) (z) (hz : z∈baseCube) : RRead (f a b) z=pulse k v z a b := congr_fun (congr_fun (h.echo z hz) _) _
  have hzero (a b : TypeFace 2) (hn : a≠b) : f a b=0 := by
    apply RRead_injective (hx a b) (by simp) fun z hz => ?_
    rw [he _ _ _ hz,pulse_diagonal,if_neg hn]; simp [RRead,Laurent.read]
  refine ⟨?_,hzero a b⟩; by_cases ht : p=q
  · subst q; change ∀ z, f a a z=f x x _
    let w z := f x x (s.act z)
    have hm : Summable fun z => ‖w z‖ := (Signed.actEquiv (R:=ℤ) s).toEquiv.summable_iff.mpr (hx x x)
    have hh : f a a=w := by
      apply RRead_injective (hx _ _) hm; intro z hz
      have ht := he x x (s.act z) (signed_base hz s)
      rw [he _ _ _ hz, show pulse k v z a a=pulse k v _ x x from pink_sign s k hk v p hz,← ht]
      unfold RRead Laurent.read w
      rw [← (Signed.actEquiv (R:=ℤ) s).toEquiv.tsum_eq]; refine tsum_congr fun i => ?_; rw [show mode (s.act z) ((Signed.actEquiv (R:=ℤ) s).toEquiv i)=mode z i from prompt_flip s z i]; rfl
    exact congr_fun hh
  have hh := hzero a b (fun h => ht ((plaq_iff p q).mp h))
  have hb := hzero x y (fun h => ht ((PlaqAxes.transform s).injective ((plaq_iff ..).mp h)))
  rw [hh,hb]; exact fun _ => rfl

def turned (s : Signed) (p : PlaqAxes) : ℝ :=
    let a := p.val.1; let b := p.val.2
    (if s.flip a then -1 else 1)*(if s.flip b then -1 else 1)*(if s.perm a<s.perm b then 1 else -1)
lemma turned_sq (s : Signed) (p : PlaqAxes) : turned s p*turned s p=1 := by unfold turned; dsimp only; split_ifs <;> ring

def reorient (s : Signed) (f : form 1 n) : form 1 n := fun b =>
  let v := (posDir (axisEquiv.symm b.2)).rotate s
  let i := v.used (affine s 0 b.1); if v.neg then -f (i.1,coord i.2) else f (i.1,coord i.2)

set_option maxHeartbeats 1000000 in
lemma rotations_d (f : form 1 n) (s : Signed) (x : Site n) (p : PlaqAxes) :
    (d 1 n *ᵥ reorient s f) (x,plaquette p)=turned s p*(d 1 n*ᵥf) ((Face.send s 0 (x,p)).1,plaquette (p.rotate s)) := by
  obtain ⟨⟨a,b⟩,h⟩ := p; change a<b at h
  rw [d_plaquettes,d_plaquettes]
  have he (k : Axis) : s.act (step k:Site n) = if s.flip k then -step (s.perm k) else step (s.perm k) := by
    rw [← Step.vec_pos,← Step.vec_rotate]; simp [Step.rotate,Step.vec,posDir]
  have hj (k : Axis) : axisEquiv.symm (coord k)=k := axisEquiv.symm_apply_apply _
  simp only [turned, PlaqAxes.rotate,PlaqAxes.ordered,Face.send,Face.lower,atFace,affine,Signed.act_add,
    he, reorient,hj, Step.rotate,posDir,Step.vec, Step.used, Bool.false_xor, add_zero]
  -- reduce sorting and flips then canonicalize vertex additions
  rcases lt_or_gt_of_ne (s.perm.injective.ne h.ne) with hm|hm <;> cases hg : s.flip a <;> cases hk : s.flip b <;>
    simp only [hm,if_true, hm.not_gt,if_false, Bool.false_eq_true,min_eq_left hm.le, max_eq_right hm.le,
      min_eq_right hm.le, max_eq_left hm.le, neg_one_mul, one_mul,neg_neg,add_zero,sub_eq_add_neg] <;>
    abel_nf
end YM.Next.Free
