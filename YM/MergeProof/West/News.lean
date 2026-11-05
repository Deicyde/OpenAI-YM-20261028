import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.PathPair
import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Awaken
import YM.MergeProof.Badlands
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Bonfire
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Spinto
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Comparison
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Hybrid

-- following YM.Next.UV_STRESS.{Annulus Watch.planted,Value.curves_bound},
-- but center instead of terrace; comparisons here only at single j.
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (I: Watch C)
lemma buffer (S:Schedule)(k:ℕ){N:ℕ}(h:k≤N)(p:ℕ)(x:Cover):
    let T:= center S p h 0
    Cells.location S k N p x ∈ T.margin (wrap (S.side k p) x) (T.side.val/3) :=by
    intro T; let u:= wrap (S.side k p) x; let t:= Cells.location S k N p x; let b:= T.side.val/2
    have he: t=T.units.root u:= by unfold t; rw [Cells.location,dif_pos h]; rfl
    have ht:T.side.val= Cells.span S h p:=rfl
    have hp :0 < T.side.val := T.side.property
    have hh (i):T.coordinated u t i=b:=by
       have hx:t i-T.starts u i=(b:Per (S.side N p)):=by
          rw [he]; unfold Tiling.starts; change (T.units.root u i) - ((0 - (b:Per (S.side N p)))+T.units.root u i)=_; abel
       unfold Tiling.coordinated;rw [hx]; exact ZMod.val_natCast_of_lt ((show b<T.side.val from Nat.div_lt_self hp (by norm_num)).trans T.narrow)
    refine ⟨fun i=>?_,fun i=>?_⟩
    · change T.coordinated u t i<T.side.val
      rw [hh]; exact Nat.div_lt_self hp (by norm_num)
    change T.side.val/3≤ T.coordinated u t i ∧ T.coordinated u t i + T.side.val/3+1 ≤ T.side.val
    rw [hh]; dsimp only [b]; omega
lemma acorns (hp : C.Makes) (h : CellHyp C F) (k : ℕ) (hg : I.t≤k) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ i : ℕ×ℕ in F.fuse, ∃ hN : k+1 ≤ i.1,
      ∀ f : Config G (C.side i.1 i.2) → ℂ,
      let T := center C.S i.2 ((Nat.le_succ k).trans hN) 0
      Interior (T.chamber 0) f →
      ‖moment (C.beta i.1 i.2) (fun x => f x * I.plot i.1 i.2 x)‖ ≤ T.rootTest (C.beta i.1 i.2) f * B := by
  classical
  have hY := C.S.shrinks.const_mul (9:ℝ)
  rw [mul_zero] at hY
  obtain ⟨j, ⟨A,hA,H⟩, hj, hs⟩ := ((grows h I.q).and ((eventually_ge_atTop (k+1)).and
    (hY.eventually (ge_mem_nhds (C.S.a_pos k))))).exists
  let z := pushSite C.S hg ∘ I.table
  have hD : Injective z := by
    intro i j hx
    apply I.distinct
    change C.S.gridPoint I.t (I.table i)=C.S.gridPoint I.t (I.table j)
    rw [← finer C.S hg (I.table i), ← finer C.S hg (I.table j)]
    exact congr_arg _ (show pushSite C.S hg (I.table i) = _ from hx)
  refine ⟨A^I.n,pow_nonneg hA _,?_⟩
  have he : ∀ᶠ i : ℕ×ℕ in F.fuse, Injective ((wrap (C.S.side k i.2)) ∘ z) := by
    rw [Extraction.Order.fused,Extraction.Order.late]
    exact (F.per.cofinal.eventually (sparse C.S k z hD)).mono fun r hr => Eventually.of_forall fun s => hr
  have ht : ∀ᶠ i in F.fuse,imageBudget I.q A j i.1 i.2 := H
  filter_upwards [he,ht] with i hh hg'
  obtain ⟨N,p⟩ := i; let X := C.side N p
  have hq : j≤N := hg'.1
  let T := center C.S p ((Nat.le_succ k).trans (hj.trans hq)) 0
  let g (s : Fin (I.n+1)) : T.Cell := wrap (C.S.side k p) (z s)
  let d := 3 * Cells.span C.S hq p
  have hd : d≤T.side.val/3 := by
    apply (Nat.le_div_iff_mul_le (by decide)).2; apply (Nat.cast_le (α:=ℝ)).1
    apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [show C.S.a N * T.side.val=C.S.a k from C.S.embeds_scale T.units]
    unfold d; push_cast; convert hs using 1
    rw [← C.S.embeds_scale (C.S.toDepth hq p)]; ring
  have hv s : I.among N p s ∈ T.margin (g s.succ) d := by
    unfold Watch.among; rw [← location_down C.S hg (by omega) (I.x s)]
    exact Lease.fewer T _ hd (buffer C.S k ((Nat.le_succ k).trans (hj.trans hq)) p (pushSite C.S hg (I.x s)))
  choose U hU hQ hB using fun (s : Fin I.n) =>
    Lease.alive (T:=T) hp s (I.among N p s) hg' hq (inherits (by omega : k≤j) hq) (hv s)
  refine ⟨hj.trans hq,fun f hm => ?_⟩
  let D : Fin (I.n+1) → Config G X → ℂ := Fin.cons f U
  have hi : ∀ (i : Fin (I.n+1)), Interior (T.chamber 0) (D i) := Fin.cases hm hQ
  have hw (x) : (∏ i : Fin (I.n+1), T.copy (g i) (D i) x)= f x * I.plot N p x := by
    have hi : g 0=0 := by dsimp only [g,z, Function.comp_apply]; rw [Watch.table, Fin.cons_zero,pushSite,smul_zero,map_zero]; rfl
    rw [Fin.prod_univ_succ,hi,T.copy_zero]; congr 1
    exact Finset.prod_congr rfl fun j _ => congr_fun (hU j) x
  let β := C.beta N p
  have hx := T.planted (h.all _ _) g hh D hi
  simp_rw [hw] at hx
  apply hx.trans; rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (T.root_nonneg β f)
  calc
    _ ≤ ∏ _ : Fin I.n,A := Finset.prod_le_prod (fun i _ => T.root_nonneg β (U i)) (fun i _ => hB i)
    _ = _ := by simp
end YM.MergeProof.Ribbons
