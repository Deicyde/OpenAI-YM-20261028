import YM.CellFourier.Alias

/-! # Unreduced momenta on actual grids (affine and alias rules) -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Matrix Bloch Lattice Laurent
open scoped Topology BigOperators
variable {n c f : Side} {u v : Site n} {p q : Momentum}

def quant (n : Side) (z : Cover) := (n.val:ℂ)⁻¹ • Laurent.reciprocal z

def Matches (p : Momentum) (u : Site n) := ∃ z : Cover, p = quant n z ∧ u = wrap n z

lemma mon_matches (u : Site n) : Matches (mon u) u := ⟨_,rfl,(wrap_lift _).symm⟩
lemma quant_matches (n : Side) (z : Cover) : Matches (quant n z) (wrap n z) := ⟨z,rfl,rfl⟩
@[simp] lemma quant_zero (n : Side) : quant n 0 = 0 := by ext1 i; simp [quant,reciprocal]

@[simp] lemma quant_add (n : Side) (x y : Cover) : quant n (x + y) = quant n x + quant n y := by
  ext1 i; simp [quant,reciprocal,mul_add]
@[simp] lemma quant_neg (n : Side) (x : Cover) : quant n (-x) = -quant n x := by ext1 i; simp [quant,reciprocal]
@[simp] lemma quant_signed (n : Side) (x : Cover) (s : Signed) : quant n (s.act x) = s.act (quant n x) := by
  ext1 i; obtain ⟨a,rfl⟩ := s.perm.surjective i; simp only [Signed.act_at,quant,Pi.smul_apply, smul_eq_mul,reciprocal]; split <;> simp

namespace Matches
lemma add (h : Matches p u) (h' : Matches q v) : Matches (p + q) (u + v) := by
  obtain ⟨z,rfl,rfl⟩ := h; obtain ⟨y,rfl,rfl⟩ := h'; exact ⟨z+y,(quant_add ..).symm,(map_add ..).symm⟩
lemma neg (h : Matches p u) : Matches (-p) (-u) := by obtain ⟨z,rfl,rfl⟩ := h; exact ⟨-z,(quant_neg ..).symm,(map_neg ..).symm⟩
lemma signed (h : Matches p u) (s : Signed) : Matches (s.act p) (s.act u) := by obtain ⟨z,rfl,rfl⟩ := h; exact ⟨s.act z,(quant_signed ..).symm,wrap_signed ..⟩
lemma bar (h : Matches p u) : star p = p := by
  obtain ⟨z,rfl,_⟩ := h; ext1 i; simp [quant,reciprocal]
lemma canonical (h : Matches p u) : ∃ z : Cover, p = mon u + reciprocal z := by
  obtain ⟨z,rfl,rfl⟩ := h
  obtain ⟨j,hj⟩ := cover_of_eq _ z (wrap_lift _)
  refine ⟨j,?_⟩
  conv_lhs => rw [hj, quant_add]; arg 2; unfold quant
  unfold mon; congr 1
  ext1 i; simp only [Pi.smul_apply,smul_eq_mul,reciprocal]
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; field_simp [side_ne]
lemma read (h : Matches p u) (z : Cover) : mode p z = cell u (wrap n z) := by
  obtain ⟨j,rfl⟩ := h.canonical; rw [mode_phase,mode_periodic,mul_one,cell_wrap]
lemma step (h : Matches p u) (i : Axis) : cell u (Lattice.step i) = Complex.exp (Complex.I * p i) := by
  rw [← wrap_step, ← h.read]; simp [mode,mul_ite]
end Matches

lemma mode_dual (s : Signed) (p : Momentum) (z : Cover) : mode (s.act p) (s.act z) = mode p z := by
  unfold mode; rw [← Equiv.sum_comp s.perm]; congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Signed.act_at]; split <;> simp
lemma cell_dual (s : Signed) (u v : Site n) : cell (s.act u) (s.act v) = cell u v := by
  have h := mon_matches u
  conv_lhs => rhs; rw [← wrap_lift v,wrap_signed]
  rw [← (h.signed s).read, mode_dual]; rfl

section aliasing
variable {g : Ratio c f}

def aliasSite (g : Ratio c f) (z : Cover) (l : Site g.count) : Site f := wrap f (z + c.val • lift l)

lemma alias_match (g : Ratio c f) (z : Cover) (l : Site g.count) :
    Matches (aliasAt (quant c z) l) (aliasSite g z l) := by
  refine ⟨_,?_,rfl⟩
  rw [aliasAt,mon,quant_add]
  ext1 i
  simp only [quant, reciprocal, Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast, g.exact_size,Nat.cast_mul]
  field_simp [side_ne]

lemma aliasSite_inj (z : Cover) : Injective (aliasSite g z) := by
  intro x y h
  obtain ⟨j,hj⟩ := cover_of_eq _ _ h
  have ht : lift y = lift x + g.count.val • j := by
    funext i
    apply mul_left_cancel₀ (show ((c.val:ℕ):ℤ) ≠ 0 by positivity)
    have h := congr_fun hj i
    simp only [Pi.smul_apply, Pi.add_apply] at h ⊢
    simp only [nsmul_eq_mul,g.exact_size,Nat.cast_mul] at h ⊢
    rw [mul_add,← mul_assoc]; rw [add_assoc] at h; exact add_left_cancel h
  rw [← wrap_lift y,ht,map_add,wrap_lift, show wrap g.count (g.count.val • j) = 0 by ext i; change (((g.count.val • j : Cover) i : ℤ) : Per g.count) = 0; simp [Per]]; simp

lemma aliasSite_neg (z : Cover) (l : Site g.count) : -aliasSite g z l = aliasSite g (-z) (-l) := by
  obtain ⟨d, hd⟩ := cover_of_eq _ _ (show wrap g.count (-lift l) = wrap g.count (lift (-l)) by simp)
  unfold aliasSite
  rw [hd,smul_add,← mul_smul,← g.exact_size,← add_assoc,show ∀ x : Cover, wrap f (x + f.val • d) = wrap f x by
      intro x; rw [map_add,show wrap f (f.val • d) = 0 by ext i; change (((f.val • d : Cover) i : ℤ):Per f)=0; simp [Per],add_zero]]
  simp [add_comm]

lemma alias_opposite (l : Site n) (p : Momentum) : ∃ z : Cover, aliasAt (-p) (-l) = -aliasAt p l + reciprocal z := by
  obtain ⟨z,hz⟩ := ((mon_matches l).neg.canonical)
  refine ⟨-z,?_⟩
  rw [aliasAt, aliasAt, smul_neg,show mon (-l) = -mon l - reciprocal z from eq_sub_of_add_eq hz.symm]
  rw [show reciprocal (-z) = -reciprocal z by ext1 i; simp [reciprocal]]; abel
end aliasing
end YM.Push.Loops
