import YM.Pressure.Seeds
import YM.SectorNext.RECONNECTED_LOCALITY.Parts


set_option warningAsError false

/-!
# Moving ALL declared addresses and partitions

The structural tests used at the merging
step. The hypotheses for indexwise moving of the raw h's (and covariance/kernel,
likelihood and window, addressed eligibility etc, even on unforced
extensions at identity) remain a substantive prescription on the analytic
& path construction; this is NOT an argument about transporting a total push
from `Branches` and assuming individual summands therefore transport. The gauge
condition on supports actually tested will be propagated similarly, before sum.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
open Function RG Lattice Wilson

variable {c : Side}

/-- affine on the native address lattice including shift. -/
def sitePerm (s : Signed) (b : Site c) : Equiv.Perm (Site c) :=
    s.actEquiv.toEquiv.trans (Equiv.addRight b)

@[simp] lemma sitePerm_val (s : Signed) (b x : Site c) : sitePerm s b x = affine s b x := rfl

/-- Generic transport of full tested endpoints (or inventories). -/
def carrying {ι ι' : Type*} (v : ι ≃ ι') (e : Equiv.Perm (Site c)) (X : ι → Support c)
    (X' : ι' → Support c) := ∀ i,X' (v i)=(X i).map e.toEmbedding

namespace carrying
variable {ι ι' : Type*} {v : ι ≃ ι'} {e : Equiv.Perm (Site c)} {X : ι → Support c} {X' : ι' → Support c}

theorem inverse (h : carrying v e X X') : carrying v.symm e.symm X' X := by
  intro a; obtain ⟨a,rfl⟩:=v.surjective a
  rw [Equiv.symm_apply_apply,h a]; ext x
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding,Finset.image_image]; simp

theorem region (h : carrying v e X X') (p : Finset ι) :
    Words.region X' (v.finsetCongr p) = e.finsetCongr (Words.region X p) := by
  classical
  ext x
  simp only [Equiv.finsetCongr_apply, Words.region, Finset.mem_map, Finset.mem_biUnion, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨i,⟨j,hj,rfl⟩,hj'⟩
    rw [h j] at hj'; obtain ⟨k,hk,rfl⟩:=Finset.mem_map.mp hj'
    exact ⟨k,⟨j,hj,hk⟩,rfl⟩
  · rintro ⟨k,⟨j,hj,hk⟩,rfl⟩
    refine ⟨_,⟨j,hj,rfl⟩,?_⟩; rw [h j]; exact Finset.mem_map_of_mem _ hk



theorem chain (h : carrying v e X X') (s : Finset ι) (i j : ι) (he : Ac.chain X s i j) :
    Ac.chain X' (v.finsetCongr s) (v i) (v j) := by
  refine Relation.ReflTransGen.lift (r:=Ac.bonds X s) (p:=Ac.bonds X' (v.finsetCongr s)) v ?_ _ _ he
  rintro i k ⟨hi,hk,x,h1,h2⟩
  change Ac.bonds X' _ (v i) (v k)
  rw [Equiv.finsetCongr_apply]
  exact ⟨Finset.mem_map_of_mem v.toEmbedding hi,Finset.mem_map_of_mem v.toEmbedding hk,
    e x,(h i).symm ▸ Finset.mem_map_of_mem _ h1,(h k).symm ▸ Finset.mem_map_of_mem _ h2⟩





theorem reach [DecidableEq ι] [DecidableEq ι'] (h : carrying v e X X') (s : Finset ι) (i : ι) :
    v.finsetCongr (Ac.burst X s i) = Ac.burst X' (v.finsetCongr s) (v i) := by
  ext j; obtain ⟨j,rfl⟩:=v.surjective j
  simp only [Equiv.finsetCongr_apply, Ac.bright, Finset.mem_map,Equiv.coe_toEmbedding, v.injective.eq_iff,
    exists_eq_right]
  refine and_congr_right fun _ => ⟨h.chain s _ _,fun he => ?_⟩
  have hh : Ac.chain X (v.finsetCongr.symm (v.finsetCongr s)) (v.symm (v i)) (v.symm (v j)) :=
    h.inverse.chain _ _ _ he
  simpa only [Equiv.symm_apply_apply] using hh



end carrying













end YM.SectorNext.Reconnect
