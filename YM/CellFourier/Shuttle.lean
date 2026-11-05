import YM.CellFourier.Circulant

/-!
# Same mesh, different row geometry

Using centered residues for every offset. `Cross` even types with no
orientation. Mats ℝ with Frobenius notation at `Linear`, counting separated
from Color directions. Coarse p with fine aliases verifies full-kernel
identities against the exact footprint fibers. No removal of harmonic modes
on tori. Bounds are separate from these exact relations (see also `Row`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bloch
open Lattice Laurent Matrix Function Filter Set Complex
open scoped Topology BigOperators ComplexConjugate ContDiff Matrix.Norms.Frobenius

abbrev Co (c : Side) (α : Type*) := Site c × α

variable {c f : Side} (g : Ratio c f) {α β γ : Type*}

/-- Universal real stencil with true coarse displacement, even when used on
the torus. From Coarse β to fine α; fine position x splits x= Lg + r, query
from r with `y-g`. For row from fine to coarse, use transpose of such.
-/
abbrev Cross (L : Side) (α β : Type*) := Row (Co L α) β

def splitCo (α : Type*) : Co f α ≃ Co c (Co g.count α) :=
  ((Equiv.prodCongr g.splitSites (Equiv.refl α)).trans (Equiv.prodAssoc _ _ _))

lemma split_co (x : Co f α) : splitCo g α x=(g.parent x.1,g.residue x.1,x.2) := by
  change ((g.splitSites _).1,(g.splitSites _).2,_)=_; rw [← g.unpack]; rfl

/-- PERIODIC counting action via the cover stencil, no hidden period scalars. -/
def installed (P : Cross g.count α β) : Matrix (Co f α) (Co c β) ℝ := Matrix.submatrix (P.acts c) (splitCo g α) id

section aliases
variable (α) [DecidableEq α]
/-- Coarse transformed p, not yet alias-parsed. -/
def coarseReading : Matrix (Co f α) (Co c (Co g.count α)) ℂ := (rotations c (Co g.count α)).submatrix (splitCo g α) id

def parsed := fiber (fun p : Site c => aliasBlock g.count α (mon p))

variable [Fintype α]

def readings := coarseReading g α*parsed g α

lemma parserGram : star (parsed g α) * parsed g α=(g.count.val:ℂ)^4 • 1 := by
  unfold parsed
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Matrix.star_eq_conjTranspose,mul_apply,Fintype.sum_prod_type]
  by_cases h : x=y
  · subst y
    have H := congr_fun (congr_fun (straightens g.count α (mon x)) i) j
    simpa [fiber, Matrix.smul_apply,smul_ite, Matrix.one_apply,mul_ite,ite_mul,returned,star_zero, apply_ite star, real_frequency,mul_apply] using H
  simp only [Matrix.smul_apply,Matrix.one_apply,Prod.mk.injEq,h,false_and, ↓reduceIte,smul_zero]
  refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun i _ ↦ ?_
  simp only [Matrix.conjTranspose_apply,fiber, of_apply]; split_ifs <;> simp_all

lemma parserGram' : parsed g α * star (parsed g α)=(g.count.val:ℂ)^4 • 1 := by
  have hp : ((g.count.val:ℂ)^4) ≠ 0 := pow_ne_zero _ (side_ne _)
  have hh : (((g.count.val:ℂ)^4)⁻¹ • star (parsed g α))*parsed g α=1 := by rw [smul_mul_assoc, parserGram,smul_smul,inv_mul_cancel₀ hp,one_smul]
  conv_rhs => rw [← mul_eq_one_comm.mp hh]
  rw [mul_smul_comm,smul_smul,mul_inv_cancel₀ hp,one_smul]

theorem readingsGram : readings g α * (readings g α).conjTranspose=(f.val:ℂ)^4 • 1 := by
  have he : coarseReading g α * (coarseReading g α).conjTranspose=(c.val:ℂ)^4 • 1 := by
    let s := splitCo g α
    have hx := congr_arg (fun m : Matrix _ _ ℂ => submatrix m s s) (rotations_gram c (Co g.count α))
    ext i j
    simpa only [coarseReading,s,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply,
      Matrix.smul_apply,Matrix.one_apply,id_eq, (splitCo g α).injective.eq_iff,
      Matrix.star_eq_conjTranspose] using congr_fun (congr_fun hx i) j
  unfold readings; rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (parsed g α),
    ← Matrix.star_eq_conjTranspose,parserGram', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,he,smul_smul, show (f.val:ℂ)=(c.val:ℂ)*g.count.val by rw [g.exact_size,Nat.cast_mul],mul_pow, mul_comm]

-- prove alias frequencies on the fine torus without requiring centered branch identification of the high alias
omit [DecidableEq α] [Fintype α] in
lemma winds (p : Site c) (l : Site g.count) (x : Cover) : mode (aliasAt (mon p) l) (f.val • x)=1 := by
  rw [g.exact_size,mul_comm c.val, mul_smul, ← mode_scale, alias_scale,mode_phase,
    mode_periodic,← mode_scale, mon_phase,mode_periodic,mul_one]

omit [DecidableEq α] [Fintype α] in
lemma mesh_alias (p : Site c) (l : Site g.count) {x y : Cover} (h : wrap f x=wrap f y) :
    mode (aliasAt (mon p) l) x = mode (aliasAt (mon p) l) y := by
  obtain ⟨j,rfl⟩ := cover_of_eq x y h; rw [mode_shift, winds, mul_one]

lemma sample (p : Site c) (l : Site g.count) (x : Site f) (a b : α) : readings g α (x,b) (p,l,a)=
    if b=a then mode (aliasAt (mon p) l) (lift x) else 0 := by
  let r := g.residue x
  let y := g.parent x
  have hh : readings g α (x,b) (p,l,a)=(rotations c (Co g.count α)*parsed g α) (y,r,b) (p,l,a) := by
    simp only [readings,mul_apply,coarseReading,submatrix_apply,split_co]; rfl
  rw [hh, parsed, rot_fiber]
  simp only [aliasBlock,Matrix.of_apply]
  split <;> rename_i H
  · rw [show mode (aliasAt (mon p) l) (lift x)=mode (aliasAt (mon p) l) (g.count.val • lift y + lift r) by
      apply mesh_alias; rw [wrap_lift,map_add]; exact (g.unpack_at x).symm]
    rw [mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one]
    rfl
  simp
end aliases

section algebra
variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def direct (R : Row α β) (L : Side) (p : Momentum) := fiber (fun l : Site L => R.read (aliasAt p l))

/-- Counting proof on every high & harmonic alias on every torus. -/
lemma aligns (R : Row α β) (h : R.safe) :
    approached (R.acts f)*readings g β=readings g α*fiber (fun p : Site c => direct R g.count (mon p)) := by
  ext ⟨x,i⟩ ⟨p,l,b⟩
  have hu : (readings g α*fiber (fun p : Site c => direct R g.count (mon p))) (x,i) (p,l,b) = mode (aliasAt (mon p) l) (lift x)*R.read (aliasAt (mon p) l) i b := by
    simp [mul_apply,Fintype.sum_prod_type, sample,fiber,direct,Row.read,Laurent.read,mul_ite,ite_mul]
  rw [hu,mul_apply,Fintype.sum_prod_type]
  simp only [Row.acts, approached, Matrix.map_apply, Matrix.of_apply, sample]
  simp_rw [mul_ite,mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let q := aliasAt (mon p) l
  have hs (y : Site f) : Summable fun a => (if y = x+wrap f a then R i b a else 0) := by
    have H := (h i b).of_norm.indicator {a | y=x+wrap f a}
    exact H.congr (fun z => by simp [indicator])
  have ht (y : Site f) : Summable fun a => ((if y=x+wrap f a then R i b a else 0:ℝ) : ℂ)*mode q (lift y) := (Complex.ofRealCLM.summable (hs y)).mul_right _
  simp_rw [ofReal_tsum,← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun y _ => ht y),Row.read,of_apply, Laurent.read, ← tsum_mul_left]
  refine tsum_congr fun z => ?_
  simp_rw [apply_ite ((↑):ℝ→ℂ),ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [show mode q (lift (x+wrap f z))=mode q (lift x+z) by
    apply mesh_alias; simp only [wrap_lift,map_add],mode_shift]
  simp only [q, smul_eq_mul]; ring

lemma assembled (A : Cross g.count α β) (h : A.safe) : approached (installed g A)*rotations c β=
    coarseReading g α*fiber (fun p : Site c => A.read (mon p)) := by
  ext i j
  simpa only [installed,coarseReading, Matrix.mul_apply, Matrix.submatrix_apply, approached,map_apply,id_eq] using
    congr_fun (congr_fun (circulant c A h) ((splitCo g α) i)) j
end algebra
end YM.Bloch
