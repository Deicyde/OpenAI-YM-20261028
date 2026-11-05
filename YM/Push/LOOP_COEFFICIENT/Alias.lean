import YM.Push.LOOP_COEFFICIENT.Pullback

/-! # Raw uncolored one-step alias normalization in the actual Cross convention -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
variable {L c f : Side} {g : Ratio c f} {k : Site c} {p : Momentum}

omit [Fintype b] [DecidableEq b] in lemma plane_mul (E : Type) (e : Grid c E a) (M : Matrix a b ℂ) (i : Site c) (x j) :
    (plane e i * M) x j = cell i (e x).1 * M (e x).2 j := plane_apply ..

lemma acts_routed (R : Row a b) (h : R.safe) (hp : Matches p k) :
    Routed (Equiv.refl _) (Equiv.refl _) k k (cmat (R.acts c)) (R.read p) := by
  obtain ⟨z,hz⟩ := hp.canonical
  unfold Routed; rw [hz,R.periods]; ext ⟨x,i⟩ j
  rw [plane_mul]; exact (congr_fun (congr_fun (circulant c R h) (x,i)) (k,j)).trans (rot_fiber ..)

lemma installed_routed (R : Cross g.count a b) (h : Row.safe R) (hp : Matches p k) :
    Routed (splitCo g a) (Equiv.refl _) k k (cmat (installed g R)) (Row.read R p) := by
  have hh := acts_routed R h hp
  ext i j; exact congr_fun (congr_fun hh (splitCo g a i)) j

lemma alias_phase (g : Ratio c f) (l : Site g.count) (x : Site f) (z : Cover) :
    cell (wrap c z) (g.parent x) * mode (aliasAt (quant c z) l) (lift (g.residue x)) = cell (aliasSite g z l) x := by
  conv_rhs => arg 2; rw [← g.unpack_at x]
  rw [cell_add, ← (alias_match g z l).read (lift (g.residue x)),Ratio.embed,← (alias_match g z l).read,← mode_scale,alias_scale,mode_phase,
    mode_periodic,mul_one,(quant_matches c z).read,wrap_lift]

def aliasColumns (a : Type) [DecidableEq a] (z : Cover) (g : Ratio c f) : Matrix (Co f a) (Co g.count a) ℂ := of fun i j =>
    plane (Equiv.refl (Co f a)) (aliasSite g z j.1) i j.2

lemma alias_convert (z : Cover) : plane (splitCo g a) (wrap c z) * aliasBlock g.count a (quant c z) = aliasColumns a z g := by
  ext i j; rw [plane_mul, split_co]; unfold aliasBlock aliasColumns plane
  simp only [Matrix.of_apply,Equiv.refl_apply,mul_ite,mul_zero,alias_phase]

def aliasMatrix (A : Cross L a b) (p : Momentum) := (((L.val:ℂ)^4)⁻¹ • returned (aliasBlock L a) p) * Row.read A p

def profile (A : Cross L a b) (p : Momentum) (l : Site L) : Matrix a b ℂ := (aliasMatrix A p).submatrix (fun x => (l,x)) id

lemma aliasProject (A : Cross g.count a b) (hA : Row.safe A) : Projects g (Equiv.refl (Co f a)) (Equiv.refl (Co c b))
    (cmat (installed g A)) (profile A) := by
  intro z
  have hp := quant_matches c z
  rw [installed_routed A hA hp,show Row.read A (quant c z) = aliasBlock g.count a (quant c z) * aliasMatrix A (quant c z) from ?_,
      ← Matrix.mul_assoc, alias_convert]
  · ext i j; rw [Matrix.mul_apply,Fintype.sum_prod_type, Matrix.sum_apply]; rfl
  unfold aliasMatrix
  rw [← Matrix.mul_assoc, Matrix.mul_smul,straighten',smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (side_ne g.count)),one_smul,Matrix.one_mul]
end YM.Push.Loops
