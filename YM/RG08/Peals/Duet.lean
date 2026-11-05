import YM.RG08.Peals.Ferry

/-! # All genuine period contractions inter-valence are literal -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α : Type} {σ θ A B C : ℝ} {r s : ℕ} {m : Side} {M : Row α α}
variable {F : Shale α (r+1)} {K : Shale α (s+1)}

variable [Fintype α] [DecidableEq α]
-- Pick derivative at input position z,i.
private def tapped (i : Co m α) (x : PAC α m) : Fin (r+1) → PAC α m := Fin.cons (zpk i) (fun _=>x)
omit [Fintype α] in
private lemma cantor (F : Shale α (r+1)) (v : Co m α) (z) (b) (x : PAC α m) (hg : ordered F) :
    F b * rosary (tapped v x) z b= if (z,(b 0).2)=v then F b*rosary (fun _=>x) z (stem1 b) else 0 := by
  by_cases h : F b=0
  · simp [h]
  unfold rosary tapped; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,zpk,Pi.single_apply]
  rw [show silks z b 0=(z,(b 0).2) by unfold silks; rw [show (b 0).1=0 from hg b h,map_zero,add_zero]]; split <;> simp_all; rfl
omit [DecidableEq α] in
private def subRec (F : Shale α (r+1)) (x : PAC α m) (b : Beads α (r+1)) (z : Site m) := F b * rosary (fun _ => x) z (stem1 b)
private lemma flat_tap (h : Tunable F) (v : Co m α) (x : PAC α m) :
    recital F m (tapped v x)= ∑' b,if (b 0).2=v.2 then subRec F x b v.1 else 0 := by
  have hz z := bead_summable F (tapped v x) h.1 z
  rw [recital_eval _ h.1,← Summable.tsum_finsetSum (fun z _=> hz z)]; apply tsum_congr; intro b
  simp_rw [cantor _ _ _ _ _ h.2.1]; rw [sum_eq_single v.1]; · obtain ⟨v,j⟩ := v; simp [subRec]
  · intro i _ hi; rw [if_neg (fun he=> hi (congr_arg Prod.fst he))]
  simp
private lemma flat_coin (h : Tunable F) (v : Co m α) (x : PAC α m) :
    Summable (fun b:Beads α (r+1)=> if (b 0).2=v.2 then subRec F x b v.1 else 0) := by
  apply Summable.congr (bead_summable F (tapped v x) h.1 v.1) (fun b=>?_); rw [cantor _ _ _ _ _ h.2.1]; obtain ⟨v,j⟩ := v; simp [subRec]
omit [Fintype α] [DecidableEq α] in
private lemma ships (i : Coves α r s × Cover) (v : PAC α m) (z : Site m) :
    leads (layerT F K) (wakes M) i *rosary (fun _=>v) z (tide i)=wakes M i * (subRec F v i.1.1 z * subRec K v i.1.2 (z+wrap m i.2)) := by
  unfold subRec layerT leads rosary tide; rw [Fin.prod_univ_add]
  simp only [silks, Fin.append_left, Fin.append_right,shiftedBy, map_add]
  simp_rw [← add_assoc, add_right_comm z _ (wrap m i.2)]; ring -- danger loop

omit [Fintype α] [DecidableEq α] in
private lemma awaken_at (h : Whole M) (F : Shale α (r+1)) (K : Shale α (s+1)) (b : Coves α r s) (x : PAC α m) (z : Site m) :
    ∑' a:Cover, wakes M (b,a)*(subRec F x b.1 z * subRec K x b.2 (z+wrap m a))=
      ∑ v:Site m, M.acts m (z,(b.1 0).2) (v,(b.2 0).2) * (subRec F x b.1 z * subRec K x b.2 v) :=
    (Work.F08.sift_action (h.safe (b.1 0).2 (b.2 0).2).of_norm m z (fun v => _ * subRec K x b.2 v)).symm

private def heard (x : PAC α m) (F : Shale α (r+1)) (z : Site m) (i : α) (b : Beads α (r+1)) :=
    if (b 0).2=i then subRec F x b z else 0

private def shipsE (x : PAC α m) (F : Shale α (r+1)) (K : Shale α (s+1)) (M : Row α α) (z : Site m) (i : α) (u : Site m) (j : α) (b : Coves α r s) :=
    M.acts m (z,i) (u,j) * (heard x F z i b.1 * heard x K u j b.2)
lemma manifold (x : PAC α m) (z : Site m) (hf : Tunable F) (hk : Tunable K) (h : Whole M) :
    (∑ i : α,∑ u : Site m,∑ j : α, M.acts m (z,i) (u,j) * (recital F m (tapped (z,i) x) * recital K m (tapped (u,j) x)))=
    ∑' b,leads (layerT F K) (wakes M) b * rosary (fun _=> x) z (tide b) := by
  have hc (i q j) : M.acts m (z,i) (q,j) * (recital F m (tapped (z,i) x) * recital K m (tapped (q,j) x))=∑' b, shipsE x F K M z i q j b := by
    rw [flat_tap hf, flat_tap hk, tsum_mul_tsum_of_summable_norm (flat_coin hf (z,i) x).norm (flat_coin hk (q,j) x).norm, ← tsum_mul_left]; rfl
  have hs i q j : Summable (shipsE x F K M z i q j) :=
    (summable_mul_of_summable_norm (flat_coin hf (z,i) x).norm (flat_coin hk (q,j) x).norm).mul_left _
  simp_rw [hc, ← Summable.tsum_finsetSum (s:=univ) (fun j _=> hs _ _ j), ← Summable.tsum_finsetSum (s:=univ) (fun j _ => summable_sum (s:=univ) (fun i _ => hs _ j i))];
  rw [← Summable.tsum_finsetSum (s:=univ) (fun i _ => summable_sum (s:=univ) (fun j _=> summable_sum (s:=univ) (fun u _=> hs i j u)))]
  have hD := sum_bounded (voyage_exists h hf.1 hk.1) (g:=fun i : Coves α r s × Cover=>rosary (fun _=>x) z (tide i)) (fun i => rosary_bill _ _ _)
  rw [hD.tsum_prod]; refine tsum_congr fun b=>?_ ; simp_rw [ships]; rw [awaken_at h F K, sum_eq_single (b.1 0).2]
  · apply sum_congr rfl; intro i _; rw [sum_eq_single (b.2 0).2]; simp [shipsE,heard]; intro j _ hj; simp [shipsE,heard,hj.symm]; simp
  · intro i hi hk; simp [shipsE,heard,hk.symm]
  simp

lemma duets_play (hf : Tunable F) (hk : Tunable K) (h : Whole M) (m : Side) :
    stanza (medley M F K) m=arch (M.acts m) (stanza F m) (stanza K m) := by
  rw [medley, stanza_scale _ (score_summable (skiff_exists h hf.1 hk.1)),stanza_score (skiff_exists h hf.1 hk.1)]
  funext x; symm
  have hy (i j : Co m α) : M.acts m i j * D (zpk i) (stanza F m) x * D (zpk j) (stanza K m) x=syl r s*( M.acts m i j * (recital F m (tapped i x)*recital K m (tapped j x))) := by
    unfold stanza; rw [Dfade _ _ (hf.2.2 m), Dfade _ _ (hk.2.2 m)]; simp only [Pi.smul_apply, Tensor.diagonal,ContinuousMultilinearMap.curryLeft_apply]; unfold syl tapped; simp only [smul_eq_mul]; ring
  rw [arch]; simp_rw [hy,← Finset.mul_sum]; rw [Pi.smul_apply,smul_eq_mul]; congr 1; unfold stanza Tensor.diagonal skiff; rw [recital_pool _ (voyage_exists h hf.1 hk.1)]
  rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro z _; simp_rw [Fintype.sum_prod_type]; exact manifold x z hf hk h
end YM.RG08
