import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.Further.DENSE_MIXED_KERNELS.Hall
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-!
 # Probe-only criterion → actual Raw.Models port
 Such models need not themselves be the flat-gauge recipe.Test capacity stiffness converted from measure estimate on JUST these normalized basis readings. Applicable for union of supports, nonwrapping only ONE. Does not book extra corrections in record.X,E.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Lattice Set MeasureTheory Wilson RG RG.Supply Input Org Labels
open Source Extra.Histories Next.Foundations MultiNext.SignedSource Lyre
open Push Push.Local Planned.GuardedAtom Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n : Side} {m d:ℕ}{F:Frame G d} {R:Rep G n}{T: SectionData F} {A: Hol G}
lemma score {o:Site n}{f:Config G n→ℂ}(p:Probe G d)(t:ℝ)(A:Hol G)(X:Support n): logSample A o X t (f ∘ increment 1) p = sample A o X t f p:=by
  unfold logSample sample; split
  · exact ((increment_testLog ..).fun_comp f |>.iteratedDeriv_eq p.2.val).symm
  split; exact congr_arg f (Work.G07.at_zero_increment ..); rfl
variable {o:Site n}{w η:ℝ}
lemma self {p:Probe G d}{B:BudgetPoint}{f : Config G n→ℂ}{X:Support n}(h:B.Regular X f)(he:d ≤ B.order):IdentityTest A o X B f (f ∘ increment 1) p 0:=by
  have ht : f 1=f (increment 1 0):= congr_arg f (Work.G07.at_zero_increment ..).symm
  refine ⟨le_of_eq (by change ‖f 1-f (increment 1 0)‖=_; rw [← ht]; simp),fun _=> ?_,fun m k _ _ _=>by simp⟩
  exact (h.smooth 1 (one_healthy X B.threshold B.threshold_pos.le)).of_le (Nat.cast_le.mpr he)

-- Account price table. All rep sizes Collars permitted. minC Corr.Small w≥1.
def corn (G:Gauge)(d:ℕ) := 1+∑ i∈range (d+1),(Lyre.lyre i G).choose
lemma cornBig : 1 ≤ corn G d:= le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>zero_le_one.trans (Lyre.lyre i G).choose_spec.1))

-- correcting ONE nonwrapping charge. Anchor shrinks computed by actual Y.Focus irrespective field defined outside neighborhood.
variable (M:Raw F n) {X:ℕ→Support n}(hT: Readable A T R.p n w) (hM:M.Format o X R)(hs:Nonwrapping (X m) o)
include hM hs hT
lemma rerouted (y:F.Coeff)(hf:Summable (M.row o X A R.p.threshold))(he:F.coeffSize (y-(M.seed + ∑' i, M.row o X A R.p.threshold i))≤η):∃ g, Models A o X R.p M y (corn G d*w*η) g:=by
   let S i:=M.row o X A R.p.threshold i
   let y0:= y - (M.seed+ ∑' i,S i)
   let V(i):= M.bulk i ∘ increment (1:Config G n)
   let k:=R.p.threshold; let f:= presented T o k y0
   have hh:= presented_good o hT y0
   let g(i):=V i+ if i=m then f ∘ increment 1 else 0
   have hY(i): ContDiffAt ℝ (d : WithTop ℕ∞) (V i) 0:= ((hM.regular _).smooth 1 (one_healthy _ _ R.p.threshold_pos.le)).of_le (Nat.cast_le.mpr hT.order)
   have hE:ContDiffAt ℝ (d : WithTop ℕ∞) (f ∘ increment 1) 0 := (hh.1.smooth 1 (one_healthy _ _ R.p.threshold_pos.le)).of_le (Nat.cast_le.mpr hT.order)
   have hκ:= Work.G07.at_zero_increment (1:Config G n)
   let u:= corn G d*w*η
   have hw:= hT.nonneg; have hy:0 ≤ η:= (Work.G08.size_nonneg F _).trans he; have hx :w * F.coeffSize y0≤ w*η :=mul_le_mul_of_nonneg_left he hw
   have ht: 1≤ corn G d:= cornBig
   have h0: u≥0:=by unfold u; positivity
   refine ⟨g,fun p hp=>?_,fun p hp=> ?_⟩
   · let t:=runProbe F p
     have he:t (∑' i,S i)+t y0=t (y-M.seed):=by rw [← map_add]; congr 1; unfold y0; abel
     let Y i:=if i=m then t y0 else 0
     have hx : (fun i => t (S i) + if i=m then t y0 else 0)= (fun i=> logSample A o (X i) k (g i) p):=by
       funext i
       have ht:t (S i)=logSample A o (X i) k (V i) p:= (sample_eq F A o _ (hM.regular i) hT.order p).symm.trans (score ..).symm
       change t (S i)+ _= _; rw [ht]; by_cases hj : i=m
       · subst i; unfold g; simp only [if_true]
         rw [logSample,logSample,if_pos hs,if_pos hs]; let Z:=T.footprint o
         have hk: Nonwrapping Z o:=nonwrapping_placement T o hT.fit; let K:=testLog A d o (k • p.1)
         have hK: ContDiffAt ℝ (d : WithTop ℕ∞) K 0:= (testLog_diff ..).of_le le_top; have hz : K 0=0:=testLog_zero ..
         have hp' {f:Directions G n→ℂ}(h:ContDiffAt ℝ (d : WithTop ℕ∞) f 0): ContDiffAt ℝ (p.2.val : WithTop ℕ∞) (f∘ K) 0:= (ContDiffAt.comp _ (hz.symm ▸ h : ContDiffAt ℝ (d : WithTop ℕ∞) f (K 0)) hK).of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt))
         have ht : weighted A F o Z R.p.threshold f = y0:=by
             unfold weighted; have he: project A o Z f d= F.coords.symm (F.scaled R.p.threshold⁻¹ y0):=project_eq (placed_reads T o hT.fit hT.sound _); rw [he,F.coords.apply_symm_apply,F.scaled_inv R.p.threshold_pos.ne']
         have h: iteratedDeriv p.2.val ((f ∘ increment 1) ∘ K) 0 = t y0 := by
             have hx': logSample A o Z k (f ∘ increment 1) p=t y0 := (score p k A Z).trans ((sample_eq F A o _ hh.1 hT.order p).trans (congr_arg t ht))
             rw [logSample,if_pos hk] at hx'; exact hx'
         -- lift from if via cal.
         rw [show (V m + f ∘ increment 1) ∘ testLog _ _ _ _= (V m ∘ K) + (f ∘ increment 1) ∘ K from rfl, iteratedDeriv_add (hp' (hY m)) (hp' hE), h]
       simp only [g,hj, if_false,add_zero]
     rw [← he] -- potential map linear coe
     rw [← show _=_ from hx]; exact ((show Summable S from hf).hasSum.mapL t).add (hasSum_ite_eq _ (t y0))
   let e(i:ℕ):ℝ:= if i=m then u else 0
   refine ⟨e,⟨fun i=>by unfold e; split; exact h0; exact le_rfl,(hasSum_ite_eq m u).summable,le_of_eq (hasSum_ite_eq m u).tsum_eq⟩,fun j=>?_⟩
   unfold g e; by_cases hj:j=m
   swap; · rw [if_neg hj,add_zero,if_neg hj]; exact self (hM.regular _) hT.order
   subst j; rw [if_pos rfl,if_pos rfl]
   refine ⟨?_,fun _=> (hY m).add hE,fun _ j hj v h=> ?_⟩
   · rw [Pi.add_apply]; unfold V; simp only [Function.comp_apply,hκ, sub_add_eq_sub_sub, sub_self,zero_sub,norm_neg]; have hv : w*η ≤ u:= by unfold u; rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) ht
     exact (hh.2.2 1 (one_healthy _ _ R.p.threshold_pos.le) [] (Nat.zero_le _) (by simp)).trans (hx.trans hv)
   rw [iteratedFDeriv_add_apply ((hY m).of_le (Nat.cast_le.mpr hj)) (hE.of_le (Nat.cast_le.mpr hj))]; change ‖iteratedFDeriv ℝ j (V m) 0 v - (iteratedFDeriv ℝ j (V m) 0 v + iteratedFDeriv ℝ j (f ∘ increment 1) 0 v)‖ ≤ _; rw [sub_add_eq_sub_sub]; change ‖iteratedFDeriv ℝ j (V m) 0 v - _ - _‖ ≤ _
   rw [sub_self,zero_sub,norm_neg]
   let C:= (Lyre.lyre j G).choose
   have hp : C≤ corn G d:= (Finset.single_le_sum (s:=range (d+1)) (f:=fun j=>(Lyre.lyre j G).choose) (fun i _=> zero_le_one.trans (Lyre.lyre i G).choose_spec.1) (mem_range.mpr (Nat.lt_succ_of_le hj))).trans (le_add_of_nonneg_left zero_le_one)
   have hf:= (Lyre.lyre j G).choose_spec.2 n _ _ _ _ _ _ v (fun _=>1) (hj.trans hT.order) (one_healthy _ _ R.p.threshold_pos.le) hh.1 hh.2 (fun i=> ⟨zero_le_one,fun x=>by rw [one_mul]; exact (h i).1 x⟩)
   unfold u; rw [mul_assoc]; simp only [prod_const_one,one_mul] at hf; exact hf.trans (mul_le_mul hp hx hh.2.1 (zero_le_one.trans ht))
end YM.PhysicalNext.Repeat.Cub
