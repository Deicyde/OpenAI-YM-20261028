import YM.Labels.Reference

/-!
# Common reference coordinates

The same in extraction and in reconstruction of a particular hierarchy.
Regulator fixes the unit magnitude `space^d` (at `space=S.a(m_d)`).
Free-comparison example changes only that magnitude via `space=1`.
Quotient maps not part of a register: they depend on S.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Labels
open scoped Topology BigOperators

structure Register (G : Gauge) where
  grid : Frames G
  space (d : ℕ) : ℝ
  positive (d) : 0 < space d

namespace Register
variable {G : Gauge} (L : Register G)

abbrev coord := L.grid.level
abbrev Ref (d : ℕ) := (L.coord d).Coeff

def scalar (d : ℕ) : L.Ref d := ((L.space d : ℂ) ^ d) • (L.coord d).e0

def bar (d : ℕ) : L.Ref d →ₛₗ[starRingEnd ℂ] L.Ref d where
  toFun p := star p
  map_add' p q := star_add p q
  map_smul' r p := star_smul r p

@[simp] theorem bar_apply (d) (x : L.Ref d) : L.bar d x = star x := rfl

theorem geom_conj (d) (p : L.Ref d) : realBar ((L.coord d).coords.symm p) = (L.coord d).coords.symm (star p) := by
  apply (L.coord d).coords.injective
  rw [(L.coord d).coords.apply_symm_apply]; funext k
  exact (L.coord d).conj_basis _ _

@[simp] theorem bar_scalar (d : ℕ) : star (L.scalar d) = L.scalar d := by
  unfold scalar
  simp only [star_smul, star_pow, Complex.star_def, Complex.conj_ofReal]
  congr 1
  funext i
  simp [Frame.e0, Pi.single_apply]

/-- Raw H transformations at every degree. -/
abbrev mirrorGroup (d : ℕ) (s : Signed) : L.Ref d →ₗ[ℂ] L.Ref d := (L.coord d).act s.ortho

@[simp] theorem mirror_scalar (s : Signed) (d : ℕ) : L.mirrorGroup d s (L.scalar d) = L.scalar d := by
  unfold scalar
  rw [map_smul, ← (L.coord d).coords_unit, mirrorGroup,Frame.act_coords]
  congr 2
  apply Subtype.ext
  exact (rotated (G := G) _).map_one

@[simp] theorem mirror_mul (s q : Signed) (d : ℕ) (v : L.Ref d) :
    L.mirrorGroup d (s*q) v = L.mirrorGroup d s (L.mirrorGroup d q v) := by
  have hx : (s*q).ortho = s.ortho*q.ortho := map_mul Signed.inclusionO ..
  simp only [mirrorGroup,hx,Frame.act_mul]

@[simp] theorem mirror_one (d : ℕ) (v : L.Ref d) : L.mirrorGroup d 1 v = v := by
  simp [mirrorGroup, show (1:Signed).ortho = 1 from map_one Signed.inclusionO]

@[simp] theorem star_mirror (s : Signed) (d : ℕ) (v : L.Ref d) :
    star (L.mirrorGroup d s v) = L.mirrorGroup d s (star v) := by
  apply (L.coord d).coords.symm.injective; rw [← geom_conj L]
  simp [mirrorGroup,Frame.act,L.geom_conj]

/-- Reflection adjoint at coordinate through 0. Use `bar` alone for ordinary complexification, Euclidean real label conventions. -/
def adj (d : ℕ) (a : Axis) : L.Ref d →ₛₗ[starRingEnd ℂ] L.Ref d :=
  (L.mirrorGroup d (Signed.mirror a)).comp (L.bar d)

@[simp] theorem adj_scalar (d a) : L.adj d a (L.scalar d) = L.scalar d := by
  simp only [adj,LinearMap.comp_apply,bar_apply,bar_scalar,mirror_scalar]

@[simp] theorem reflected (d a) (v : L.Ref d) : L.adj d a (L.adj d a v) = v := by
  simp only [adj,LinearMap.comp_apply,bar_apply,star_mirror, star_star]
  rw [← mirror_mul, show Signed.mirror a * Signed.mirror a = 1 from
    calc
      _ = (Signed.mirror a)⁻¹ * Signed.mirror a := rfl
      _ = _ := inv_mul_cancel _, mirror_one]

/-- Reference label carrying its own weight. Works across arities with no casts
until reading a slot. -/
abbrev Token := (d : ℕ) × L.Ref d

def one (d : ℕ) : L.Token := ⟨d,L.scalar d⟩
def move (s : Signed) (x : L.Token) : L.Token := ⟨x.1,L.mirrorGroup x.1 s x.2⟩
def conjugate (x : L.Token) : L.Token := ⟨x.1,star x.2⟩
def reflectedToken (a : Axis) (x : L.Token) : L.Token := ⟨x.1,L.adj x.1 a x.2⟩

@[simp] theorem token_adjoint (a : Axis) (x : L.Token) : L.move (Signed.mirror a) (L.conjugate x) = L.reflectedToken a x := rfl
end Register
end YM
