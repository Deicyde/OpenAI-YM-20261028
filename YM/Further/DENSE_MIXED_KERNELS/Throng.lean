import Mathlib.Combinatorics.SimpleGraph.Acyclic
import YM.Further.DENSE_MIXED_KERNELS.Surface
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.SECTOR_MEASURE.Oriented

/-!
# A concrete family of forced-component estimates, I: throng geometry

One family where we can PRICE the mandatory packet fully from existing
energy components on the matching sector. Aggregate **only when entire
space is in the support with genuine mandatory queries** in this protocol.
Important for uses with many distributed markers and especially K gas
matches. Can for example include density sectors with output flags dense
on the indicated scale (doesn't require flag on EVERY site, period can
grow without bound). For this recipe use all-frozen, no Γ change.
Failures of these hypotheses elsewhere REQUIRE other prices.

No physical existence of a forced cell asserted (indeed e.g. impossible
primary flags can make some allocations zero). It's the estimate for those
vertices, even when only value bounds are available for marked copies inside.
Vac.Caps allow buying extensive vacuum defects **here**; price stays
uniform in period. This isn't the general E packet compulsory estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {w x β κ : ℝ} {U : Config G f} {V : Config G c}

open Oriented
/-- All output geometry queried in compulsory 2B halo. Use just
coverage by OUTPUT portion of packet. -/
def Throng (A : Stores S) (x : ℝ) := halo (2*radiusB x) A.flags=univ

namespace Throng
variable (h : Throng A x)
include h

lemma whole : A.dome (2*radiusB x) = univ := by
  refine eq_univ_of_forall fun i => ?_
  have hp : (A.flags) ⊆ A.place := subset_union_right
  exact Corona.halo_mono le_rfl hp ((show _ = univ from h).symm ▸ mem_univ i)


lemma card : Fintype.card (Site c) ≤ A.flags.card*(4*radiusB x+1)^4 := by
  have he := Corona.halo_size A.flags (2*radiusB x)
  rw [h,card_univ,show 2*radiusB x + 2*radiusB x=4*radiusB x by omega] at he; exact he

omit h in
lemma sep (s : Signed) (i j : Site c) : separation ((StepData.sendSites s 0) i) ((StepData.sendSites s 0) j) = separation i j := by
  change separation (affine s 0 i) (affine s 0 j)=_; simp [affine]

lemma turns (s : Signed) : Throng (turnStore s A) x := by
  let T := StepData.sendSites s (0:Site c)
  apply eq_univ_of_forall; intro i
  obtain ⟨y,hy,hZ⟩ := halo_spec.mp (show T i∈halo (2*radiusB x) A.flags from (show _=univ from h).symm ▸ mem_univ _)
  refine halo_spec.mpr ⟨T.symm y,Finset.mem_map_of_mem _ hy,?_⟩
  rwa [← sep s, (show _ = y from T.apply_symm_apply y)]

omit h in
lemma flat_charge (T : Tube G S) (F : Forest S.ratio) (k : S.Choices) (hm : S.patch.Branches S.kernel G)
    (hU : Stores.SliceSet S F U)  (Hp : PointCharge T x w κ) (hb : 0≤β) (q : ℝ) (hQ : q ≤ 1) (hD : q ≠ 0 → Seeded A U k V x w)
    (hP : ∀ s,(turnStore s A).dome (2*radiusB x)=univ) :
    q * enters T β x k V U / prefactor S G β ≤ Real.exp (-β*(κ*(fiery G x S.patch.L)^2*A.shares)) := by
  have hy : meanRest A T x U k V=0 := by
    unfold meanRest
    apply Eq.trans _ (av_const 0)
    apply congr_arg averaged; ext s
    unfold unassigned
    simp only [Stores.assessed, Stores.limit, Stores.outs, Stores.intern, Stores.coordN, Stores.tally, Stores.talli, Stores.tallc, Stores.talln, Stores.talll,hP s,
      mem_univ,filter_true,Finset.sum_add_distrib]; abel
  rw [enters_eq hm A, leaves, hy, mul_zero, Real.exp_zero, mul_one,
    show q*(prefactor S G β* _*S.likelihood U k)=
      (prefactor S G β)*(q*S.likelihood U k*Real.exp (-β*meanEnergy A T x U k V)) by ring,
    mul_div_cancel_left₀ _ (prefactor_pos β).ne']
  by_cases ht : q=0
  · rw [ht,zero_mul,zero_mul]; exact (Real.exp_pos _).le
  by_cases hp : Alive S U k
  · have hh := mean_pays F A x w U k V hm hU (hD ht) hp Hp
    have he : S.likelihood U k ≤ 1 := by
      rw [← S.chosen hm U]; exact single_le_sum (fun i _ => S.likelihood_pos U i) (mem_univ k)
    exact (mul_le_of_le_one_left (Real.exp_pos _).le (mul_le_one₀ hQ hp.le he)).trans
      (Real.exp_monotone (mul_le_mul_of_nonpos_left hh (by linarith)))
  rw [dead hp, mul_zero,zero_mul]; exact (Real.exp_pos _).le

lemma full_charge (T : Tube G S) (F : Forest S.ratio) (k : S.Choices) (hm : S.patch.Branches S.kernel G)
    (hU : Stores.SliceSet S F U) (D : Allocation G S x w) (Hp : PointCharge T x w κ) (hb : 0≤β) :
    D.bill A k U V * enters T β x k V U / prefactor S G β ≤ Real.exp (-β*(κ*(fiery G x S.patch.L)^2*A.shares)) := flat_charge T F k hm hU Hp hb _ (D.range ..) (fun hp => D.actual _ _ _ _ hp) (fun s => (h.turns s).whole)

omit h in
open Packets in
/-- Enlarged seed halo manifest (mixed uses actual flag coordinates).
Proves a bill for any WHOLE seed packet (for B its price radius).
Use its whole support: no teleporting via another packet label. -/
theorem whole_connect (hv : A.dome (2*radiusB x) = univ) {l : ℕ} (hh : 2*radiusB x < l*radiusB x) :
    Packets.support S l (radiusB x) (seeds S A) = univ ∧ Packets.connected S l (radiusB x) A := by
  let B := radiusB x
  have he : Packets.support S 2 B (seeds S A)=univ := (support_reads ..).trans hv
  refine ⟨?_,?_⟩
  · rw [support_reads]; apply eq_univ_of_forall
    intro i; exact Corona.halo_mono hh.le (Subset.refl _) (show i∈A.dome (2*radiusB x) from hv.symm ▸ mem_univ i)
  have hl : (support S l B (seeds S A))=(A.dome (l*B)) := support_reads S A l B
  refine ⟨by rw [← support_nonempty S 2 B,he]; exact univ_nonempty,fun i hi j hj => ?_⟩
  -- each site along a native step route has a seed witness in dense INNER halo
  have hy (i : Site c) : ∃ j∈seeds S A, i∈skin S 2 B j := mem_biUnion.mp (show i∈support S 2 B (seeds S A) from he.symm ▸ mem_univ i)
  let a := anchor S i; let b := anchor S j
  let q : ℕ → Site c := line a b
  have hs i (t) (hp : t∈skin S 2 B i) : t∈skin S l B i := Corona.halo_mono hh.le (Subset.refl _) hp
  have hZ (k : ℕ) : ∀ j∈seeds S A, q k∈skin S 2 B j → Ac.chain (skin S l B) (seeds S A) i j := by
    induction k with
    | zero =>
      intro k hk he; have hx : a∈skin S l B k := hs _ _ (by simpa only [q,line_home] using he)
      exact .single ⟨hi,hk,a,Packets.contained ..,hx⟩
    | succ k ih =>
      intro j hj hh'
      obtain ⟨z,h₁,h₂⟩ := hy (q k)
      apply Relation.ReflTransGen.tail (ih z h₁ h₂)
      refine ⟨h₁,hj,q (k+1),?_,hs _ _ hh'⟩
      obtain ⟨z',hz,hz'⟩ := halo_spec.mp h₂
      have hx : separation (q k) (q (k+1)) ≤ 1 := (line_dist _ _ _ _ (by omega)).trans (by omega)
      exact halo_spec.mpr ⟨_,hz,(separation_triangle z' (q k) _).trans ((Nat.add_le_add hz' hx).trans hh)⟩
  exact hZ (separation a b) j hj (by rw [show q _=b from line_end a b le_rfl]; exact Packets.contained ..)
open Packets in
theorem connective {l : ℕ} (hh : 2*radiusB x < l*radiusB x) :
    Packets.support S l (radiusB x) (seeds S A) = univ ∧ Packets.connected S l (radiusB x) A := whole_connect h.whole hh
end Throng
end YM.Further.DenseMixedKernels
