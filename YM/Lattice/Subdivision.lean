import YM.Lattice.Site
import Mathlib.Tactic.Ring

/-!
# Subdividing the site torus

Fine roots sit over coarse sites.

Works also for even ratios, but the
**canonical block** uses the centered lift, and it commutes with reflections
for an odd ratio.

Provides decompositions for the actual finite RG kernel
and later replica cell geometries.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Lattice

/-- A subdivision of two tori of the same period. -/
structure Ratio (c f : Side) where
  count : Side
  exact_size : f.val = c.val * count.val

namespace Ratio
variable {c f : Side} (g : Ratio c f)

def embed (x : Site c) : Site f := wrap f (g.count.val • lift x)

theorem lift_embed (x : Site c) : lift (g.embed x) = g.count.val • lift x := by
  rw [lift_eq_iff]; refine ⟨rfl, fun i ↦ ?_⟩
  have hp : 0 < (g.count.val : ℤ) := by exact_mod_cast g.count.property
  have hc := lift_centers x i
  simp only [Pi.smul_apply, nsmul_eq_mul, g.exact_size, Nat.cast_mul]
  constructor
  · calc
      -(c.val * (g.count.val : ℤ)) = (g.count.val : ℤ) * -(c.val : ℤ) := by ring
      _ < _ := (mul_lt_mul_of_pos_left hc.1 hp).trans_eq (by ring)
  · calc
      _ = (g.count.val : ℤ) * (2 * lift x i) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hc.2 hp.le).trans_eq (by ring)

theorem embed_injective : Function.Injective g.embed := by
  intro x y h
  have ht : lift x = lift y := by
    funext i
    have e := congr_fun ((g.lift_embed x).symm.trans (h ▸ g.lift_embed y)) i
    simp only [Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ (show (g.count.val : ℤ) ≠ 0 from by exact_mod_cast g.count.property.ne') e
  calc x = wrap c (lift x) := (wrap_lift _).symm
       _ = y := by rw [ht, wrap_lift]

/-- Canonical embedding is multiplicative scaling even for off-window lifts. -/
theorem embed_wrap (x : Cover) : g.embed (wrap c x) = wrap f (g.count.val • x) := by
  let y := lift (wrap c x)
  have hy : wrap c y = wrap c x := wrap_lift _
  funext i
  have h : (c.val : ℤ) ∣ x i - (y i : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congr_fun hy i)
  change (((g.count.val • y : Cover) i : ℤ) : Per f) = (((g.count.val • x : Cover) i : ℤ) : Per f)
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  simp only [Pi.smul_apply, nsmul_eq_mul, g.exact_size, Nat.cast_mul, ← mul_sub]
  rw [mul_comm ((c.val : ℤ))]
  exact mul_dvd_mul_left _ h

def root : Site c →+ Site f where
  toFun := embed g
  map_zero' := by
    calc g.embed 0 = g.embed (wrap c 0) := by rw [map_zero]
         _ = _ := by rw [embed_wrap, smul_zero, map_zero]
  map_add' x y := by
    obtain ⟨x,rfl⟩ := (Function.surjective_iff_hasRightInverse.mpr ⟨lift, fun x => wrap_lift x⟩ : Function.Surjective (wrap c)) x
    obtain ⟨y,rfl⟩ := (Function.surjective_iff_hasRightInverse.mpr ⟨lift, fun x => wrap_lift x⟩ : Function.Surjective (wrap c)) y
    rw [← map_add, g.embed_wrap, g.embed_wrap, g.embed_wrap, smul_add, map_add]

@[simp] theorem root_embed (x : Site c) : g.root x = g.embed x := rfl
@[simp] theorem signed (x : Site c) (s : Signed) : g.embed (s.act x) = s.act (g.embed x) := by
  obtain ⟨x,rfl⟩ := (Function.surjective_iff_hasRightInverse.mpr ⟨lift, fun x => wrap_lift x⟩ : Function.Surjective (wrap c)) x
  rw [wrap_signed, embed_wrap, embed_wrap, wrap_signed]; exact congr_arg _
    ((map_nsmul (s.actEquiv (R := ℤ)) g.count.val x).symm)

private theorem count_dvd : g.count.val ∣ f.val := by simp [g.exact_size]

def residue : Site f →+ Site g.count where
  toFun x i := ZMod.castHom g.count_dvd (Per g.count) (x i)
  map_zero' := by ext; simp
  map_add' x y := by funext i; exact (ZMod.castHom g.count_dvd (Per g.count)).map_add _ _

@[simp] theorem residue_wrap (x : Cover) : g.residue (wrap f x) = wrap g.count x := by
  funext i; exact map_intCast (ZMod.castHom g.count_dvd (Per g.count)) (x i)

@[simp] theorem residue_embed (x : Site c) : g.residue (g.embed x) = 0 := by
  rw [embed, residue_wrap]; funext i; change (((g.count.val • lift x : Cover) i : ℤ) : Per g.count) = 0
  simp [Per]

/-- Every site is uniquely in one centered block. -/
def assemble (p : Site c × Site g.count) : Site f := g.embed p.1 + wrap f (lift p.2)

@[simp] theorem assemble_res (p : Site c × Site g.count) : g.residue (g.assemble p) = p.2 := by
  simp [assemble]

theorem assemble_bijective : Function.Bijective g.assemble := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨x,i⟩ ⟨y,j⟩ h
    have he : i=j := by simpa using congr_arg g.residue h
    subst j
    change g.embed x + _ = g.embed y + _ at h
    rw [g.embed_injective (add_right_cancel h)]
  rw [Fintype.card_prod, site_card, site_card, site_card, g.exact_size, mul_pow]

def splitSites : Site f ≃ Site c × Site g.count :=
  (Equiv.ofBijective g.assemble g.assemble_bijective).symm

/-- The projected ancestor of a fine site. -/
def parent (x : Site f) : Site c := (g.splitSites x).1

theorem unpack (x : Site f) : (g.parent x, g.residue x) = g.splitSites x := by
  let p := g.splitSites x
  have e : g.assemble p = x := g.splitSites.symm_apply_apply x
  refine Prod.ext rfl ?_
  exact congr_arg g.residue e.symm |>.trans (g.assemble_res p)

@[simp] theorem assemble_parent (p : Site c × Site g.count) : g.parent (g.assemble p) = p.1 :=
  congr_arg Prod.fst (g.splitSites.apply_symm_apply p)

theorem unpack_at (x : Site f) : g.embed (g.parent x) + wrap f (lift (g.residue x)) = x := by
  change g.assemble (g.parent x, g.residue x) = x
  rw [g.unpack]; exact g.splitSites.symm_apply_apply x

theorem unambiguous {p : Side} (hp : Odd p.val) (x : Site p) (i) :
    2*(lift x i) < p.val := by
  obtain ⟨k, he⟩ := hp
  have := (lift_centers x i).2
  omega

theorem lift_signed_of_odd {p : Side} (hp : Odd p.val) (x : Site p) (s : Signed) :
    lift (s.act x) = s.act (lift x) := by
  rw [lift_eq_iff]; refine ⟨?_, ?_⟩
  · rw [← wrap_signed, wrap_lift]
  intro i
  obtain ⟨a,rfl⟩ := s.perm.surjective i
  rw [s.act_at]; split
  · have h := lift_centers x a
    have e := unambiguous hp x a
    omega
  exact lift_centers x a

theorem assemble_signed (hp : Odd g.count.val) (x : Site c) (y : Site g.count) (s : Signed) :
    g.assemble (s.act x,s.act y) = s.act (g.assemble (x,y)) := by
  simp only [assemble, lift_signed_of_odd hp, g.signed, s.act_add, wrap_signed]

@[simp] theorem parent_signed (hp : Odd g.count.val) (x : Site f) (s : Signed) :
    g.parent (s.act x) = s.act (g.parent x) := by
  obtain ⟨⟨x,y⟩,rfl⟩ := g.assemble_bijective.2 x
  rw [← g.assemble_signed hp, g.assemble_parent, g.assemble_parent]

end Ratio
end YM.Lattice
