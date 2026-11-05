import YM.Next.MULTISOURCE.Affordable
import YM.Work.I02

/-!
# Evaluate in the actual vacuum alphabet
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Marker Function Finset Pack Overlay Mix
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {n : Side} {G : Gauge}
variable {P : Rep G n} {o : V → Site n} {D : Hot R → Pulse G n} {k : Hot R → ℝ} {κ w : ℝ}

omit [Fintype V] in
def sendC (x : R.Mode) : ℂ →L[ℂ] Poly R where
  toFun := Poly.send x
  map_add' := send_add x
  map_smul' := send_scale x
  cont := Bands.sends _

namespace Writers
variable (Y : Writers P κ D o k)

lemma power (U : Config G n) (H : Summable fun i => Y.toBands.ray i U) :
    Y.toBands.extra U=lit R (fun i => (D i).1 U) := by
  unfold Bands.extra lit
  let f ℓ := Y.toBands.ray ℓ U
  let g (i : Hot R) j := masked P.p.threshold (Y.soil i j) (Y.crop i j) U
  have h : Summable fun x => f (Y.code x) := Y.code.summable_iff.mpr (show Summable f from H)
  have ht (i : Hot R) (ℓ : ℕ) : f (Y.code (i,ℓ)) = Poly.send i.val (g i ℓ) := by simp [f,Bands.ray,toBands,g]
  have hg (i) : Summable (g i) := (Banked.reserve (i.property.image o) (le_refl 0) (fun j =>
    (Y.plots i j).2.2.2) (Y.finiteCost i)).summable U
  have he (i) : (∑' j,f (Y.code (i,j)))=Poly.send i.val (∑' j, g i j) := by
    simp_rw [ht]; exact ((sendC i.val).map_tsum (hg i)).symm
  rw [← Y.code.tsum_eq f, h.tsum_prod, tsum_fintype]
  simp_rw [he, Y.collects, send_add, Finset.sum_add_distrib]
  refine congrArg (fun q => q+_) ?_
  let M := Finset.univ.image (Hot.one R)
  rw [show (∑ i : V, Poly.send (R.fire i) (Y.toBands.units i)) = ∑ i∈ M, Poly.send i.val (Y.cash i) by
    rw [Finset.sum_image (fun x _ y _ h => (Hot.one_inj ..).mp h)]; rfl]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have ht : 2 ≤ i.sites.card := by
    by_contra h
    have he : 0 < i.sites.card := card_pos.mpr i.property
    obtain ⟨x,hx⟩ := Hot.one_of_card (x:=i) (show i.sites.card=1 by omega)
    exact hi (mem_image.mpr ⟨x,mem_univ _,hx⟩)
  rw [Y.singles i ht,Poly.send_zero]

-- Only one selected slot for each pack is needed to recover all its rows together.
omit [Fintype V] in
lemma pressed (U : Config G n) (i : ℕ) : (∑' j,Y.toBands.tagged i j U)=
    if Y.slot (ofAddress P.activities i)=i then lit R fun q => (D q).2 (ofAddress P.activities i) U else 0 := by
  let f := fun j => Y.toBands.tagged i j U
  by_cases h : Y.slot (ofAddress P.activities i)=i
  · rw [if_pos h]
    let r := fun j : Hot R => Y.code (j,0)
    have hf (j : ℕ) (hj : j ∉ Finset.univ.image r) : f j=0 := by
      have hz : (Y.code.symm j).2 ≠ 0 := by
        intro he
        apply hj; refine mem_image.mpr ⟨(Y.code.symm j).1,mem_univ _, ?_⟩
        unfold r; rw [← he]; exact Y.code.apply_symm_apply j
      simp [f,Bands.tagged,toBands,hz]
    rw [tsum_eq_sum hf, sum_image (fun i _ j _ h => (Prod.mk.inj (Y.code.injective h)).1)]
    unfold lit; exact sum_congr rfl fun x _ => by simp [f,Bands.tagged,toBands,h]
  simp [Bands.tagged,toBands,h]

lemma food (U : Config G n) {δ r : ℝ} (hp : P.activities.Valid P.p δ r)
    {s : V → ℝ} {u c d b : ℝ} (ht : Y.toBands.Radial s u c d b) :
    Y.toBands.cluster U = ∑ l∈ Pack.clears (flags P.p.threshold U), ∏ q∈l, (Poly.send R.quiet (incumbent P U q)+
      lit R (fun T => (D T).2 q U)) := by
  let A := Y.toBands
  let f i := A.each i U
  have hh := A.baseBound Y.active ht hp U
  have hs : Summable f := (Poly.budgeted ht.pure (f:=f) hh.2.2.1 (fun i => le_rfl)).1
  unfold Bands.cluster; change (∑' l, A.packet l U) = _
  erw [Pack.regroup P U f hs (A.population Y.active ht hp U).1]
  refine Finset.sum_congr rfl fun i hi => Finset.prod_congr rfl fun q _ => ?_
  let p (i : ℕ) := if ofAddress P.activities i = q then (P.activities.K i U:ℂ) else 0
  let E := lit R (fun T => (D T).2 q U)
  have he j : (if ofAddress P.activities j=q then f j else 0) =
      Poly.send R.quiet (p j) + if j = Y.slot q then E else 0 := by
    unfold p
    by_cases hj : ofAddress P.activities j=q
    · simp only [hj, ↓reduceIte, f,A,Bands.each,Y.pressed, eq_comm (a:=Y.slot q)]; rfl
    simp only [if_neg hj, Poly.send_zero, if_neg (show j ≠ Y.slot q from fun h => hj (h ▸ Y.valid _)),add_zero]
  let T i := if i = Y.slot q then E else 0
  have hv : HasSum T E := by
    have he := hasSum_single (f:=T) (Y.slot q) (fun j hj => if_neg hj)
    simpa only [T, ↓reduceIte] using he
  let k' i := P.activities.K i U
  have hk : Summable k' := by
    obtain ⟨b,hb,hB⟩ := Activities.K_total hp.boundK
    exact (hb.of_nonneg_of_le (fun i => norm_nonneg (k' i)) fun i => (hB i).2 U).of_norm
  have hx : HasSum p (incumbent P U q) := (Pack.access P _ (Complex.summable_ofReal.mpr hk) q).hasSum
  unfold Pack.collect; simp_rw [he]
  exact ((hx.map (sendC (R:=R) R.quiet) (sendC R.quiet).continuous).add hv).tsum_eq
end Writers

lemma imprint [Nonempty V] (h : Room P) (H : Afield P.p κ o D k w) (hw : 0 < w) (hc : κ ≤ 1) (hs : Spaced o P.p.B)
    (hB : 8 ≤ P.p.B) {δ r : ℝ} (hv : P.activities.Valid P.p δ r) :
    ∃ A : Bands R P, A.origins=o ∧ Stubs.Holds A w ∧ A.density=many P R D := by
  obtain ⟨Y⟩ := H.writers h (hs.injective P.p.B_pos)
  have he := Y.honors H hw hc hs hB
  have hf := Work.I02.answer Work.I01.answer G n V R P Y.toBands w hw he
  refine ⟨Y.toBands,rfl,he,?_⟩
  funext U
  unfold Bands.density
  rw [Y.power _ (Y.toBands.bulkBound Y.active hf _).1,Y.food _ hv hf]; rfl
end YM.Multi
