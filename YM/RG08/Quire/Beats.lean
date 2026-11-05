import YM.RG08.Quire.Toll
import YM.RG08.Origin.Axe

/-!
# Marked machine on finite periods `∀m` independently
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff BigOperators
variable {α X ι : Type} [Fintype α] [DecidableEq α] {m : Side}
variable {p : Option Side} {M : Row α α} {r e n L H : ℕ} {U V : Screed ℝ α} {S : Canticle α}
variable (i : Site m)

def large (L : ℕ) (U : Spine ℝ α) := ∑ j∈range (L+1), rootSong (U j) m i
@[simp] lemma root_zero : rootSong (0:Shale α r) m i=0 := by simp [rootSong]; rfl
lemma root_sum (s : Finset ι) (f : ι→Rooted ℝ α r) (h : ∀ i∈s, Pens (f i)) : rootSong (∑ i∈s,f i) m i=∑ j∈s,rootSong (f j) m i := by
  unfold rootSong; rw [st_sums s (fun i hi=> (h i hi).of_norm)]; funext x; simp only [Finset.sum_apply,Tensor.diagonal,_root_.sum_apply]
lemma root_plus {f g : Rooted ℝ α r} (h : Pens f) (k : Pens g) : rootSong (f+g) m i=rootSong f m i+rootSong g m i := by unfold rootSong; rw [st_plus h.of_norm k.of_norm]; rfl
lemma root_scale {f : Rooted ℝ α r} (h : Pens f) (a : ℝ) : rootSong (a • f) m i=a • rootSong f m i := by unfold rootSong; rw [st_scale _ h.of_norm]; rfl
lemma root_smooth (U : Rooted ℝ α r) : ContDiff ℝ ω (rootSong U m i) := Tensor.diag_smooth ..
lemma large_smooth (u : Spine ℝ α) : ContDiff ℝ ω (large i L u) := by unfold large; simp_rw [Finset.sum_fn]; exact ContDiff.sum fun _ _=>root_smooth ..

private lemma root_lap0 (A : Rooted ℝ α 0): lap (M.acts m) (rootSong A m i)=0 := by funext x; unfold rootSong lap; simp_rw [Dhush]; simp [D]
private lemma root_lap1 (A : Rooted ℝ α 1): lap (M.acts m) (rootSong A m i)=0 := by
  have h : Tensor.Sym (stitch A m i) := fun v s=>by rw [show v ∘ s=v from funext fun _=>congr_arg v (Subsingleton.elim ..)]
  funext x; unfold rootSong lap; simp_rw [Dfade _ _ (n:=0) h]; norm_num [Dhush]
private lemma lap_larger (h : Whole M) {U : Spine ℝ α} (ht : ∀ k,Tidy (U k)) : lap (M.acts m) (large i (L+2) U) = large i L (fun k=> jib (some m) M (U (k+2))) := by
  unfold large; rw [lap_sum (h:=fun k _=>root_smooth i (U k)),sum_range_succ',sum_range_succ',root_lap0 i,root_lap1 i,add_zero,add_zero]; apply sum_congr rfl; intro b _; exact root_lap (ht _) h m i
private lemma zero_arch_left (A : Rooted ℝ α 0)(f : Psalm (Co m α)): arch (M.acts m) (rootSong A m i) f=0 := by funext x; unfold rootSong arch; simp_rw [Dhush]; simp
private lemma zero_arch_right (f : Psalm (Co m α))(A : Shale α 0) : arch (M.acts m) f (stanza A m)=0 := by funext x; unfold stanza arch; simp_rw [Dhush]; simp
private lemma archway (h : Whole M) {U : Spine ℝ α} {V : Verse α} (ht : ∀ i,Tidy (U i)) (hv : ∀ i,Tunable (V i))
    (he : ∀ i,L+1 < i → U i=0) (hp : ∀ i,H+1 < i → V i=0) :
    arch (M.acts m) (large i (L+1) U) (grand (H+1) V m)=large i (L+H) (hymn M U V) := by
  unfold large grand; rw [arch_first (h:=fun k _=>root_smooth i (U k))]; simp_rw [arch_second (s:=range (H+1+1)) _ (fun v _=> stanza_smooth (V v) m)]; rw [sum_range_succ']; simp only [zero_arch_left,sum_const_zero,add_zero]; simp_rw [sum_range_succ' (n:=H+1),zero_arch_right,add_zero]; let F j k := arch (M.acts m) (rootSong (U (j+1)) m i) (stanza (V (k+1)) m)
  rw [triangle_sum F L H]; apply sum_congr rfl; intro z _
  · unfold hymn; rw [root_sum i (wheel z) _ (h:=fun j _=> Tidied z (clasp_tidy (ht (j.1+1)|>.pens) (hv (j.2+1)|>.1) h)|>.pens)]; apply sum_congr rfl; intro b hb; rw [← mem_antidiagonal.mp hb,grant_self]; exact clasp_love (ht _) (hv _) h m i
  intro x y hf
  constructor
  · by_contra hz; apply hf; unfold F; rw [he _ (by omega),root_zero,arch_stop]
  by_contra hz; apply hf; unfold F; rw [hp _ (by omega),stanza_zero,arch_wait]

private lemma large_under {U : Spine ℝ α}(h : ∀ k, L<k → U k=0)(he : L≤H) : large i H U=large i L U := by unfold large; symm; exact sum_subset (range_mono (by omega)) fun j hj hk=>by rw [h j (by simp only [mem_range] at hk; omega),root_zero]

def vault (L : ℕ) (U : Screed ℝ α) (M : Row α α) (S : Canticle α) : Op (Co m α) := fun n e=> large i (L+e) (murmur (some m) M S U n e)

theorem pendants (hp : Whole M) (hv : ∀ e r,Tunable (S e r)) (hw : Decked S) (ht : ∀ e r,Tidy (U e r)) (h : Fits L U) :
    let P := vault i L U M S
    Fluid P ∧ (∀ j k,windows L k<j → P j k=0) ∧ countT P=landP (M.acts m) P + rim (M.acts m) P (Beats M S m) := by
  let R := murmur (some m) M S U; let K := Refrain M S (some m)
  intro P
  have hp' (n e r): Tidy (R n e r) := quiet_tidily hp hv ht (some m) n e r
  have hs n e r : Tunable (K n e r) := refrains_tune hp hv _ n e r
  have hc n e r : R n e r≠0 → r≤L+e ∧ 2*n+r ≤ L+3*e := murmur_degree hp hv hw ht h
  refine ⟨fun _ _=> large_smooth i _,?_,?_⟩
  · intro n e he
    refine sum_eq_zero (s:=range (L+e+1)) (f:=fun r=> rootSong (R n e r) m i) fun r _=> ?_
    exact (congr_arg (fun f=>rootSong f m i) (not_ne_iff.mp (mt (hc n e r) (fun H=> by unfold windows at he; omega)))).trans (root_zero i)
  funext n e
  have hC j k v : L+k<v→R j k v=0 := fun H=>not_ne_iff.mp (mt (hc j k v) (fun h=>(not_lt.mpr h.1) H))
  have hK j k v : k+2 < v → K j k v=0 := fun H=>not_ne_iff.mp (mt (treble_reel hp hv hw) (fun ⟨⟨he,a,ha⟩,hd⟩=> by omega))
  rw [countT,← Nat.cast_smul_eq_nsmul ℝ]; change _ • large i (L+e) (R (n+1) e)=lap (M.acts m) (large i (L+e) (R n e)) + ∑ b∈wheel n,∑ a∈wheel e, _
  rw [← large_under i (H:=L+e+2) (hC n e) (by omega),lap_larger i hp (hp' n e)]
  let Y b a v := hymn M (R (b : ℕ×ℕ).1 (a : ℕ×ℕ).1) (K b.2 a.2) v
  have hy b a v : Tidy (Y b a v) := hymn_tidy hp (fun k=> (hp' b.1 a.1 k).pens) (fun k=> (hs b.2 a.2 k).1) v
  have hh (b : ℕ×ℕ) (a : ℕ×ℕ) (ha:a∈wheel e) : arch (M.acts m) (P b.1 a.1) (Beats M S m b.2 a.2) =large i (L+e) (Y b a) := by
    -- pad U to L+a.1+1. then last rank vanishes
    change arch _ (large i (L+a.1) _) (grand (a.2+2) (K b.2 a.2) m)=_
    rw [← large_under i (H:=L+a.1+1) (hC b.1 a.1) (by omega),archway i hp (ht:=hp' _ _) (hv:=hs _ _)]; rotate_left
    · intro j hj; exact hC b.1 a.1 j (by omega)
    · exact hK b.2 a.2
    have he := mem_antidiagonal.mp ha
    rw [show L+a.1+(a.2+1)=L+e+1 by omega]; refine large_under i ?_ (by omega)
    intro k' hk'; refine sum_eq_zero (s:=wheel k') fun j hj=> ?_
    have ht':=mem_antidiagonal.mp hj
    by_cases hL : L+a.1<j.1+1
    · rw [show R b.1 a.1 (j.1+1)=0 from hC b.1 a.1 (j.1+1) hL,clasp_zero (hs b.2 a.2 (j.2+1)|>.1) hp, grant_zero]
    rw [show K b.2 a.2 (j.2+1)=0 from hK b.2 a.2 (j.2+1) (by omega),clasp_stop (hp' b.1 a.1 _|>.pens) hp,grant_zero]
  have hg v : ((↑(n+1:ℕ)):ℝ) • rootSong (R (n+1) e v) m i=rootSong (jib (some m) M (R n e (v+2))) m i+∑ b∈wheel n, ∑ a∈wheel e,rootSong (Y b a v) m i := by
    have hU b : Pens (∑ a∈wheel e,Y b a v) := Pens.additions fun a _=> (hy b a v).pens
    have hV : Pens (∑ b∈wheel n,∑ a∈wheel e,Y b a v) := Pens.additions fun b _=> hU b
    have hE := jib_tidy (hp' n e (v+2)|>.pens) hp (.some m)
    rw [show R (n+1) e v=_ from murmur_step _,root_scale i (hE.pens.plus hV),smul_inv_smul₀ (by positivity),root_plus i hE.pens hV]
    change _+rootSong (∑ b∈wheel n,∑ a∈wheel e,Y b a v) m i= _
    rw [root_sum i (h:=fun b _=>hU b)]; simp_rw [root_sum i (h:=fun a _=> (hy _ a v).pens)]
  rw [show (∑ b∈wheel n,∑ a∈wheel e,arch (M.acts m) (P b.1 a.1) (Beats M S m b.2 a.2))=∑ b∈wheel n,∑ a∈wheel e,large i (L+e) (Y b a) from sum_congr rfl fun b _=>sum_congr rfl fun a ha=>hh b a ha]; unfold large; rw [Finset.smul_sum]; simp_rw [hg,sum_add_distrib,add_right_inj]; rw [sum_comm]; exact sum_congr rfl fun b _=> Finset.sum_comm
end YM.RG08.Quire
