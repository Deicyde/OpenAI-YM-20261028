import YM.MergeProof.North.Brim
import YM.MergeProof.West.News
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}(hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy)
variable {ι:Type*}[Fintype ι](I:ι→Watch C)(g:ι→ℂ){B d h:ℕ}
set_option quotPrecheck false
def arena (r:ℝ):Set E4:={y| r/16< ‖y‖∧ ‖y‖ < 4*r}
local notation "R" => fun i:ℕ=> fuga C.path.levels (i+1)
include hC hq ho H
lemma stencil_pay (q:ℕ)(hp:∀ i,(I i).t ≤ q)
   (ht : ∀ t:S.Field B, (∑ i:ι,g i*(I i).tester S B t)=0):
 ∃ A:ℝ,0 ≤ A∧ ∀ (d h:ℕ)(b:C.book.Ref d)(T:C.book.Ref 4)(m j:ℕ)(ε:ℝ), ShellNode C q j m B d h b T F ε → ∀ x:Lattice.Cover, C.S.gridPoint j x∈ arena ((R) m) → (∀ i,(I i).point j x∈generic _) →
    ‖∑ i:ι, g i * ((((R) m:ℂ)^h) * (I i).asked (S.project 4 T) (S.project d b) (C.S.gridPoint j x))‖ ≤ ε*A:=by
   choose a ha hA using fun i=> acorns (I i) hC hq q (hp i)
   refine ⟨∑ i, a i*‖g i‖,Finset.sum_nonneg (fun i _=>mul_nonneg (ha _) (norm_nonneg _)),fun d h b T m j ε he x hx hv=>?_⟩
   obtain ⟨w,Q,hw⟩:=he.corners x hx.1.le hx.2.le
   let r:ℝ:=(R) m
   let f (i:ι):=(r:ℂ)^h*((I i).asked (S.project 4 T) (S.project d b) (C.S.gridPoint j x))
   have hp':∀ᶠ u: ℕ×ℕ in F.fuse,‖w u‖ ≤ Q:=show F.late fun N p=> ‖w (N,p)‖ ≤ Q from hw.mono fun N h=>h.mono fun p hh=> hh.choose_spec.1
   obtain ⟨z,hz,_,c,hE⟩:= finite_extract (𝓛:=F.fuse) w Q hp'
   let Y := S.project B c
   have hy (i:ι):‖f i-(I i).tester S B Y‖ ≤ ε*a i:=by
       have hm:= ((I i).cost_limit j x F (d:=d) T b ho H hz (hv i) h r hE).norm
       rw [Watch.test_known]; apply le_of_tendsto hm
       apply Eventually.filter_mono hz
       let Fw (u:ℕ×ℕ):= fragment (C:=C) (d:=d) (D:=B) h r T b j x u.1 u.2 (w u)
       have hl:∀ᶠ u:ℕ×ℕ in F.fuse, ∃ hN:q≤u.1, ‖w u‖≤ Q∧ Interior ((center C.S u.2 hN 0).chamber 0) (Fw u) ∧ (center C.S u.2 hN 0).rootTest (C.beta u.1 u.2) (Fw u)≤ε:=hw
       filter_upwards [hl,hA i] with u hh hv';obtain ⟨hN,_,hW,hP⟩:=hh;obtain ⟨_,p'⟩:=hv'
       exact (p' _ hW).trans (mul_le_mul_of_nonneg_right hP (ha _))
   calc
       _ = ‖∑ i:ι, g i*(f i-(I i).tester S B Y)‖:= by simp_rw [mul_sub,Finset.sum_sub_distrib,ht,sub_zero]; rfl
       _ ≤ _:= (norm_sum_le ..).trans (by
            rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [norm_mul]
            exact (mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)).trans_eq (by ring))
end YM.MergeProof.Ribbons
