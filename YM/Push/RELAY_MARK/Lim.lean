import YM.Push.RELAY_MARK.Assembly

/-!
#  in this construction

Persistence of real and H, not assuming even converging orthonormal
basis choices. Further RShort-RPrep consumer preparing the right
finite-dimensional maps in the limit, even before smooth repair.
Includes an **application** to the normalized base interface from
EXTRACTION once all its inputs are paid. Assume needed
identifications on the exact free comparator (`RFree`, separate task).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter Labels Lattice Bid
open Extraction Extraction.Lease Next.Extract Dash
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {d : ℕ} {R : Weave G} {b : Presentation C}
    {S : Table C.book} {D : Bin S} {Z : ∀ d : ℕ, ℕ→CoordMap C d}

lemma warp (h : Memento C R) (hb : Purse C R b) (ht : Projected b F D Z) (d : ℕ) :
    ∃ L : Label G d ≃ₗ[ℂ] C.label d, (∀ p, p∈Maxwell.equationIdeal G d ↔ L p∈LinearMap.ker (D d).trueP.toLinearMap) ∧
      (∀ p,L (realBar p)=star (L p)) ∧ ∀ p s,L (theta s p)=(C.labels.level d).act s.ortho (L p) := by
  let W := C.labels.level d
  let T := (D d).trueP
  let A := (D d).step
  have hx : ∀ᶠ i : ℕ × ℕ in F.fuse, C.ref d ≤ i.1 := by
    rw [Extraction.Order.fused]; exact Eventually.of_forall fun p=> F.mesh.cofinal.eventually_ge_atTop _
  have ha := ht.approaches d
  change Tendsto A F.fuse (𝓝 T) at ha
  have hg : ∀ᶠ i in F.fuse, Symmetry W (A i) := by
    filter_upwards [hx] with i hi; dsimp only [W,A]
    rw [ht.same]; exact hb.shows d i.1 i.2 (active h.made (h.wrote d) hi)
  have hw (x : W.Coeff) : Tendsto (fun i=> A i x) F.fuse (𝓝 (T x)) := Dash.arcing ha tendsto_const_nhds
  have hp : Symmetry W T := by
    constructor
    · intro s x
      let g := travelH W s
      exact tendsto_nhds_unique_of_eventuallyEq (hw (g x)) (g.continuous.continuousAt.tendsto.comp (hw x)) (hg.mono fun i hi=> hi.signed s x)
    intro x
    exact tendsto_nhds_unique_of_eventuallyEq (hw (star x)) (hw x |>.star) (hg.mono fun i hi=> hi.real_ x)
  let X (i) := T * A i + (1-T)*(1-A i)
  have h0 : T*T=T := by
    apply ContinuousLinearMap.ext; exact (D d).final
  have hu : Tendsto X F.fuse (𝓝 1) := by
    have hh := (tendsto_const_nhds (x:=T)|>.mul ha).add
      ((tendsto_const_nhds (x:=(1-T))|>.mul (tendsto_const_nhds (x:=1)|>.sub ha)))
    rw [show T*T+(1-T)*(1-T)=1 by rw [sub_mul,one_mul,mul_sub,h0,mul_one]; abel] at hh
    exact hh
  obtain ⟨⟨N,p⟩,hs,hN,H⟩ := ((hu.eventually (Units.isOpen.mem_nhds (x:=1) (isUnit_one ))).and (hx.and hg)).exists
  let i := (N,p)
  have hz : IsUnit (X i) := hs
  obtain ⟨Y,hY⟩ := Spin.unit_shape (X i) hz
  have he (x) : Y x = T (A i x) + ((x-A i x)-T (x-A i x)) := by
    have hv (x) : Y x= X i x := LinearMap.congr_fun hY x
    simp [hv,X]
  refine ⟨(embedTo C R d N p).trans Y, fun q=>?_,fun q=>?_,fun q s=>?_⟩
  · suffices hh : A i= b.step d i by
      have hl (x) : Y (A i x)=T (Y x) := by
        have hr x : A i (A i x)=A i x := (D d).projection ..
        have hc x : T (T x)=T x := (D d).final _
        rw [he,he,hr,sub_self,map_zero, sub_self,add_zero,map_add,hc]
        simp only [map_sub,hc,sub_self,add_zero]
      let L := embedTo C R d N p
      change q∈Maxwell.equationIdeal G d ↔ T (Y (L q))=0
      rw [← hl, map_eq_zero_iff _ Y.injective,hh]
      change _↔ _∈LinearMap.ker _
      rw [(hb.pure d N p).ker]
      exact ⟨entry_mem C R d N p q,fun h=>by
        obtain ⟨x,hx,h⟩ := obtained R _ h; exact (L.injective h).symm ▸ hx⟩
    rw [show A = _ from ht.same d]
  · have ht : ∀ x,Y (star x) = star (Y x) := fun x=>by
      simp only [he,hp.real_,(show Symmetry W (A i) from H).real_,← star_sub, ← star_add] -- Y after
    simp only [LinearEquiv.trans_apply,embed_real R h.made (h.wrote d) hN, ht]
  · let V := travelH W s
    have ht (x) : Y (V x) = V (Y x) := by
      rw [he,he]; simp only [(show ∀ x,A i (V x)=_ from fun _=> H.signed s _),hp.signed]
      simp only [i,V,map_sub,map_add,hp.signed]
    simp only [LinearEquiv.trans_apply, embed_signed R h.made (h.wrote d) hN]; exact ht _

-- Apply at exactly the post-ties normalized base. Needs FREE comparison assumptions,
-- not assuming any rank agreement with interacting S.

end YM.Push.Mark
