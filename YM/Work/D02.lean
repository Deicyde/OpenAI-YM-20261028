import YM.Bid.Drops

/-!
# From gain on separated tuples to vanishing smeared discrepancy

Write the finite sum with mesh volume factors as a step integral. The cells
that can contribute lie in a fixed enlargement of the test support. On their
grid corners we need some separating coordinate per pair, in periodic
geometry (eventually in period), not simultaneous projection-gap conditions.
We use a uniform integral norm estimate rather than exchanging two limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.D02
open Bid Set Filter Function MeasureTheory Extraction Extraction.Lease Dash Wilson Lattice
open scoped Topology

private lemma cells_bucket {G : Gauge} (C : Family G) {n N p : ℕ} {x : Points n}
    (hx : x ∈ Fund C.S p n) : Order.cells C N p (bucket N p x) = tag (C.S.a N) (address (C.S.a N) x) := by
  have h := show address (C.S.a N) x = _ from found (N := N) hx
  rw [h]
  rfl

theorem answer : YM.Bid.D02 := by
  classical
  intro G C f _ _ P ⟨y,hy,hg⟩ v
  let K := tsupport v.f
  have hk : IsCompact K := v.f.hasCompactSupport
  obtain ⟨δ,hδ,hp⟩ := Gaps.someGrows C.S hk (show K ⊆ conf v.n from v.f.tsupport_subset)
  obtain ⟨A,hA,he⟩ := hg v.n v.left v.i δ hδ
  obtain ⟨M,hM⟩ := (hk.image continuous_norm).bddAbove
  let B := Metric.closedBall (0 : Points v.n) (M+1)
  have hB : IsCompact B := isCompact_closedBall ..
  obtain ⟨T,hT,hf⟩ := Order.testSup v.f
  let bound := fun z : ℕ × ℕ => T*(A*|uncurry y z|)
  let stairF := fun N p : ℕ => stair C.S (fun r : Var C.S v.n N p =>
    v.f (Order.cells C N p r) * featuring P v.left v.i N p r)
  have hmesh : ∀ᶠ N : ℕ in atTop, (4*v.n:ℝ)*C.S.a N ≤ 1 :=
    (C.S.shrinks.const_mul (4*v.n : ℝ)).eventually (ge_mem_nhds (by simp))
  have hr : ∀ᶠ z in f.fuse, ∀ x, ‖stairF z.1 z.2 x‖ ≤ B.indicator (fun _ => bound z) x := by
    rw [Order.fused, Order.late]
    unfold Order.late at he
    filter_upwards [he,f.per.cofinal.eventually hp] with p he' hp'
    filter_upwards [he',f.mesh.cofinal.eventually hmesh] with N hg' ha x
    let n' := f.mesh N
    let p' := f.per p
    let r := bucket n' p' x (S := C.S)
    let t := tag (C.S.a n') (address (C.S.a n') x)
    change ‖stairF n' p' x‖ ≤ B.indicator (fun _ => bound (n',p')) x
    have hpos : 0 ≤ B.indicator (fun _ => bound (n',p')) x := indicator_nonneg (fun _ _ => by
      dsimp only [bound]; positivity) _
    by_cases hx : x ∈ Fund C.S p' v.n
    · have hcell : Order.cells C n' p' r = t := cells_bucket C hx
      change ‖(Fund C.S p' v.n).indicator _ x‖ ≤ _
      rw [indicator_of_mem hx]
      change ‖v.f (Order.cells C n' p' r) * featuring P v.left v.i n' p' r‖ ≤ _
      rw [hcell]
      rcases eq_or_ne (v.f t) 0 with ht|ht
      · rwa [ht,zero_mul,norm_zero]
      have htK : t ∈ K := subset_closure ht
      have hd := approximate (C.S.a_pos n') x
      change dist t x ≤ _ at hd
      have hxB : x ∈ B := Metric.mem_closedBall.mpr (calc
        dist x 0 ≤ dist x t + dist t 0 := dist_triangle x t 0
        _ ≤ M+1 := by
          rw [dist_zero_right,dist_comm x t]; have h := hM ⟨t,htK,rfl⟩; linarith)
      rw [indicator_of_mem hxB]
      have hsep := Gaps.gridSeparation C.S r rfl (hp' t htK)
      have h := (hg' r (fun i j hij => hsep j i hij.symm)).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hA)
      exact (norm_mul_le ..).trans (mul_le_mul (hf t) h (norm_nonneg _) hT)
    · rw [show stairF n' p' x = 0 from indicator_of_notMem hx _ ,norm_zero]
      exact hpos
  have h0 : Tendsto (fun z : ℕ × ℕ => volume.real B * bound z) f.fuse (𝓝 0) := by
    simpa only [bound,abs_zero,mul_zero] using (((hy.abs.const_mul A).const_mul T).const_mul (volume.real B))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [hr] with z hz
  have hI : Integrable (B.indicator (fun _ => bound z)) := (integrable_indicator_iff hB.measurableSet).mpr
    (integrableOn_const hB.measure_lt_top.ne)
  have H := norm_integral_le_of_norm_le hI (Eventually.of_forall hz)
  rw [integral_indicator hB.measurableSet, setIntegral_const, smul_eq_mul] at H
  change ‖targetB P v _ _‖ ≤ _
  have ht : (∫ x, stairF z.1 z.2 x) = targetB P v z.1 z.2 := stair_integral _
  rwa [← ht]
end YM.Work.D02
