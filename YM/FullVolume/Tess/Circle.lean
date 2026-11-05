import YM.FullVolume.Tess.Wave
/- uniform interpolation and physical tests on padded sets, tunnels. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Tess
open Filter Function Set Metric MeasureTheory Lattice RG Ray Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp Amp.Beam
variable {S:Schedule} {n N j m p:ℕ}{K K': Set (Points n)}
local notation "A"=>S.a
namespace Scroll
variable {U:ℕ→ Positions n→ Beam ℂ}{G:Points n→Beam ℂ}(hk:Scroll S K U G)
abbrev cruise (S:Schedule)(V: Positions n→ Beam ℂ)(i:ℕ)(x:Points n):= ∑ j:Vertex n, mass x (S.a i) j • V (vertex x (S.a i) j)
lemma sync {f:sun→Positions n→ℂ}(s:sun) (x:Points n)(hv:∀ i:Vertex n,f s (vertex x (A N) i)=read ℂ s (U N (vertex x (A N) i))) : interpolated S N (f s) x = read ℂ s (cruise S (U N) N x):=by unfold interpolated cruise; simp_rw [map_sum,map_smul]; simp_rw [hv]
lemma inked (h:IsCompact K')(hp:K' ⊆ interior K):∀ᶠ i in atTop,∀ x∈ K',∀ v:Vertex n,tag (A i) (vertex x (A i) v)∈ K:=by
   obtain ⟨r,hr,hR⟩:= h.exists_cthickening_subset_open (isOpen_interior) hp; have he:Tendsto (fun i=>2*(4*n:ℝ)*A i) atTop (𝓝 0):=by simpa using S.shrinks.const_mul (2*(4*n:ℝ))
   filter_upwards [he.eventually (ge_mem_nhds hr)] with i hi x hx v; exact interior_subset (hR (mem_cthickening_of_dist_le _ _ _ _ hx ((surrounds _ _ (S.a_pos _)).trans hi)))
lemma crest (x:Points n)(v:ℝ)(P: Beam ℂ)(V:Positions n→Beam ℂ)(hp:∀ j:Vertex n,dist (V (vertex x (A N) j)) P ≤ v): dist (cruise S V N x) P ≤ v:=by
   let U:= vertex x (A N); let f:= mass x (A N); rw [dist_eq_norm,show cruise S V N x-P=∑ j:Vertex n, f j • (V (U j)-P) from (by simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul, f,sums,one_smul];rfl)]
   exact (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun j=>f j*v) (fun i _=> by rw [norm_smul, Real.norm_of_nonneg (mass_pos _ (S.a_pos _) _),← dist_eq_norm]; exact mul_le_mul_of_nonneg_left (hp i) (mass_pos _ (S.a_pos _) _))).trans_eq (by rw [← Finset.sum_mul,sums,one_mul]))
include hk
lemma ether (h:IsCompact K') (hp:K'⊆ interior K): TendstoUniformlyOn (fun i=> cruise S (U i) i) G atTop K':=by
   refine Metric.tendstoUniformlyOn_iff.mpr (fun ε he=>?_)
   have hP(v:Vertex n):∀ᶠ i in atTop,∀ x∈K',dist (U i (vertex x (A i) v)) (G x)<ε/2:=by
      by_contra! hx; obtain ⟨j,hj,hx⟩:=extraction_of_frequently_atTop hx; choose y hy hY using hx
      obtain ⟨x,hK,s,hs,hS⟩:= h.tendsto_subseq hy; let v'(i):= vertex (y (s i)) (A (j (s i))) v; have ht:=hj.tendsto_atTop.comp hs.tendsto_atTop
      have hh:=hk.inure (x:=v') ht (hp hK) (hS.congr_dist (squeeze_zero (fun _=>dist_nonneg) (fun _=>(dist_comm ..).trans_le (surrounds _ v (S.a_pos _))) (by simpa using! (S.shrinks.comp ht|>.const_mul (2*(4*n:ℝ))))))
      have hvv:Tendsto (fun i=>G (y (s i))) atTop (𝓝 (G x)):= (hk.land.continuousAt (mem_interior_iff_mem_nhds.mp (hp hK))).tendsto.comp hS; have hg:=hh.dist hvv; rw [dist_self] at hg
      obtain ⟨i,hi⟩:= (hg.eventually (gt_mem_nhds (half_pos he))).exists; exact (hY (s i)).not_gt hi
   filter_upwards [eventually_all.mpr hP] with i hi x hx; rw [dist_comm]; apply (crest _ _ _ _ (fun j=> hi j x hx|>.le)).trans_lt (half_lt_self he)
end Scroll
end YM.FullVolume.Tess
#print axioms YM.FullVolume.Tess.Scroll.ether
