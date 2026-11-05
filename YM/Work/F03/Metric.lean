import YM.Bid.Station
import YM.Work.F03.Transport

/-!
# The quadratic contribution and the real periodic `Bed`

Only `Attached` *on the cover* is given. We prove explicitly that the root
matrix periodizes to the same output as the sum over the actual paths of the
leading slot values. Then identify the fiscal form with the stacked inner
product used by `Floor`. All sums in physical counting coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F03
open Filter Function Lattice RG Wilson Precision Exterior Push Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
open Matrix Bloch Laurent

variable {G : Gauge} {n : Side}
  (B : Bed) {W : PathData G} {p σ C Λ u v} (hb : W.Bounds p σ C Λ) (ht : Attached B W)

include hb ht
/-- Collect all coefficients over a given *physical* face. Infinitely
many offsets on the cover can contribute to this one coefficient. -/
lemma layout_physical (b c : Face (Per n)) :
    HasSum (fun i : ℕ => if slotFace (W.row b.2 i).2 b.1 = c then (W.row b.2 i).1 else 0)
      (B.roots.acts n (b.1,plaquette b.2) (c.1,plaquette c.2)) := by
  let F i := if slotFace (W.row b.2 i).2 b.1 = c then (W.row b.2 i).1 else 0
  let l (i : ℕ) := (W.row b.2 i).2.offset
  have hs : Summable F := by
    have h := row_abs_summable W hb b.2
    refine Summable.of_norm_bounded h ?_
    intro i; unfold F; split
    · rw [Real.norm_eq_abs]
    rw [norm_zero]; exact abs_nonneg _
  have he : HasSum (fun x => if c.1 = b.1 + wrap n x
        then B.roots (plaquette b.2) (plaquette c.2) x else 0) (∑' i, F i) := by
    classical
    apply HasSum.congr_fun (hs.hasSum.tsum_fiberwise l)
    intro y
    rw [tsum_subtype]
    split_ifs with hz
    · rw [← (ht.layout b.2 c.2 y).tsum_eq]
      refine tsum_congr fun i => ?_
      by_cases h : (W.row b.2 i).2.offset = y
      · rw [Set.indicator_of_mem (show i ∈ l ⁻¹' {y} from h)]; unfold F slotFace
        rw [h, add_comm, ← hz]
        simp [Prod.ext_iff]
      rw [Set.indicator_of_notMem (show i ∉ l ⁻¹' {y} from h)]; rw [if_neg (fun a => h a.2)]
    rw [← tsum_zero (α := ℝ) (β := ℕ)]
    symm; refine tsum_congr fun i => ?_
    by_cases H : i ∈ l ⁻¹' {y}
    · rw [Set.indicator_of_mem H]; unfold F; rw [if_neg]
      intro hi
      have hy : (W.row b.2 i).2.offset = y := H
      have he := congr_arg Prod.fst hi
      apply hz; unfold slotFace at he
      simpa [hy,add_comm] using he.symm
    exact Set.indicator_of_notMem H _
  rw [show B.roots.acts n (b.1,plaquette b.2) (c.1,plaquette c.2) = ∑' i, F i from he.tsum_eq]
  exact hs.hasSum

lemma ellLine_root (b : Face (Per n)) (a : fieldDir G n 1) :
    ellLine W b a = ∑ c : Face (Per n),
      B.roots.acts n (b.1,plaquette b.2) (c.1,plaquette c.2) • faceCurl c a := by
  let l (i : ℕ) := slotFace (W.row b.2 i).2 b.1
  have hs := (ellLine_summable W hb b a).hasSum.tsum_fiberwise l
  have he : HasSum (fun c : Face (Per n) =>
        B.roots.acts n (b.1,plaquette b.2) (c.1,plaquette c.2) • faceCurl c a)
      (ellLine W b a) := by
    apply HasSum.congr_fun hs
    intro c
    rw [← ((layout_physical B hb ht b c).smul_const (faceCurl c a)).tsum_eq]
    classical
    rw [tsum_subtype (l ⁻¹' {c}) (fun i => (W.row b.2 i).1 • faceCurl (slotFace (W.row b.2 i).2 b.1) a)]
    refine tsum_congr fun i => ?_
    by_cases h : i ∈ l ⁻¹' {c}
    · have hv : slotFace (W.row b.2 i).2 b.1 = c := h
      rw [Set.indicator_of_mem h, if_pos hv, hv]
    have hv : slotFace (W.row b.2 i).2 b.1 ≠ c := h
    rw [Set.indicator_of_notMem h, if_neg hv, zero_smul]
  rw [← he.tsum_eq, tsum_fintype]

lemma ellLine_mulVec (b : Face (Per n)) (a : fieldDir G n 1) (i : G.ColorIndex) :
    (ellLine W b a) i =
      (B.roots.acts n *ᵥ (d 1 n *ᵥ parts G 1 a i)) (b.1,plaquette b.2) := by
  rw [ellLine_root B hb ht]
  let f : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj i) (WithLp.linearEquiv 2 ℝ _).toLinearMap
  change f (∑ b : Face (Per n), _) = _
  rw [map_sum, mulVec, dotProduct,
    ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site n)) plaqEquiv)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

lemma left_stack (a b : fieldDir G n 1) (hf : Floor B p n u v) (i : G.ColorIndex) :
    dotProduct (parts G 1 a i) (K (B.metric.acts n) *ᵥ parts G 1 b i) =
      ∑ x : Face (Per n), ((p.direct * ((faceCurl x a) i * (faceCurl x b) i)) +
        (ellLine W x a) i * (ellLine W x b) i) := by
  let m (z : fieldDir G n 1) := d 1 n *ᵥ parts G 1 z i
  rw [Precision.K, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    ← hf.roots, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  change dotProduct (B.full p n *ᵥ m a) (B.full p n *ᵥ m b) = _
  have he (x : Face (Per n)) (z) : (B.full p n *ᵥ m z) (x.1, Sum.inr (plaquette x.2)) =
      (ellLine W x z) i := (ellLine_mulVec B hb ht x z i).symm
  have ha (x : Face (Per n)) (z) : (B.full p n *ᵥ m z) (x.1, Sum.inl (plaquette x.2)) =
      Real.sqrt p.direct * (faceCurl x z) i := by
    change (∑ j : Body 2 n, (Real.sqrt p.direct *
      (1 : Matrix (Body 2 n) (Body 2 n) ℝ) (x.1, plaquette x.2) j) * m z j) = _
    simp_rw [mul_assoc]; rw [← Finset.mul_sum]
    change Real.sqrt p.direct * ((1 : Matrix (Body 2 n) (Body 2 n) ℝ) *ᵥ m z)
      (x.1,plaquette x.2) = _
    rw [Matrix.one_mulVec]; rfl
  rw [dotProduct, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
  conv_lhs =>
    arg 1; rw [← Equiv.sum_comp plaqEquiv]
  conv_lhs =>
    arg 2; rw [← Equiv.sum_comp plaqEquiv]
  congr 1
  · apply Finset.sum_congr rfl; intro j hj
    rw [show plaqEquiv j = _ from plaq_map j, ha (x,j), ha (x,j)]
    have hp := Real.sq_sqrt p.quadratic_pos.le
    conv_rhs => rw [← hp]
    ring
  apply Finset.sum_congr rfl; intro j hj
  rw [show plaqEquiv j = _ from plaq_map j, he (x,j), he (x,j)]

omit B hb ht in
lemma inner_color (x y : G.Color) : inner ℝ x y = ∑ i, x i * y i := by
  rw [real_inner_comm, PiLp.inner_apply]
  simp

lemma metric_pair (a b : fieldDir G n 1) (hf : Floor B p n u v) :
    gaugeFiscal B a b = ∑ x : Face (Per n), ((p.direct *
      inner ℝ (faceCurl x a) (faceCurl x b)) + inner ℝ (ellLine W x a) (ellLine W x b)) := by
  unfold gaugeFiscal
  simp_rw [left_stack B hb ht a b hf, inner_color, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]

end YM.Work.F03
