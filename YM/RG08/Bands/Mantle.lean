import YM.RG08.Bands.Braid
/-!
# Actual pair contacts in rooted equations. Winding or no winding.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Matrix.Norms.Frobenius
variable {I α:Type}{m c f:Side}{r s j n k E ε τ:ℕ}{η A B:ℝ}{U:Rooted ℝ α (r+1)}{V:Rooted ℝ α (s+1)}{p:Option Side}{K:Row α α}
def stemPair (x: Beads α (r+1) × Beads α (s+1)) : Beads α (r+s):= aboardB (stem1 x.1,stem1 x.2)
def bob (p:Option Side)(K:Row α α)(x:Beads α (r+1)×Beads α (s+1)):= stroke K p (x.1 0) (x.2 0)
def countP (p:Option Side)(K:Row α α)(U:Rooted ℝ α (r+1))(V:Rooted ℝ α (s+1)) : Rooted ℝ α (r+s) := sew (syl r s • tub (interU U V*bob p K) stemPair)
lemma bob_pens (h:Pens U)(hv:Pens V)(hk:Whole K) : Pens (interU U V*bob p K):= by
   obtain ⟨n,C,hn,hQ⟩:=hk; exact (sum_bounded (inter_pens h hv|>.of_norm) (g:=bob p K) (fun i=>stroke_known K hQ hn.le ..)).norm
lemma count_tid (h:Pens U)(hv:Pens V)(hk:Whole K): Tidy (countP p K U V):= Tidy.sewn ((bob_pens (p:=p) h hv hk).pours _|>.scale _)
lemma count_zero : countP p K (0:Rooted ℝ α (r+1)) V=0 := by
   unfold countP; rw [show interU (0:Rooted ℝ α (r+1)) V=0 from funext fun i=>zero_mul _,zero_mul,show tub (0: Beads α (r+1)×Beads α (s+1)→ℝ) stemPair=0 from funext fun i=>tsum_zero,smul_zero]; simpa using sew_sub (x:=(0:Rooted ℝ α (r+s))) (y:=0)
lemma count_zen : countP p K U (0:Rooted ℝ α (s+1))=0 := by unfold countP; rw [show interU U (0:Rooted ℝ α (s+1))=0 from funext fun i=>mul_zero _,zero_mul,show tub (0:Beads α (r+1)×Beads α (s+1)→ℝ) stemPair=0 from funext fun i=>tsum_zero,smul_zero]; simpa using sew_sub (x:=(0:Rooted ℝ α (r+s))) (y:=0)
def grail (p:Option Side)(K:Row α α)(U V: Spine ℝ α) r := ∑ a∈wheel r,grant r (countP p K (U (a.1+1)) (V (a.2+1)))
lemma grail_story {U V:Spine ℝ α}(h:Loomed (k+1) U)(hv:Loomed (n+1) V)(hk:Whole K) : Loomed (k+n) (grail p K U V) := by
   refine ⟨fun i=> Tidy.additions (fun j (_:j∈wheel i)=> Tidied i (count_tid (p:=p) (K:=K) (h.tide (j.1+1)|>.pens) (hv.tide (j.2+1)|>.pens) hk)), fun i hi=> sum_eq_zero (s:=wheel i) ?_⟩
   intro j hj; have he:=mem_antidiagonal.mp hj; by_cases hx:k+1 < j.1+1; · rw [h.budget _ hx,count_zero,grant_zero]
   rw [hv.budget (j.2+1) (by omega),count_zen,grant_zero]

variable [Fintype α][DecidableEq α]
private def brood (i : Co m α) (x : PAC α m): Fin (r+1)→PAC α m:=Fin.cons (zpk i) (fun _=>x)
private def paidU (U:Rooted ℝ α (r+1))(x:PAC α m)(z:Site m)(b:Beads α (r+1))(i:Co m α):= U b*rosary (brood i x) z b
private lemma routine (U:Rooted ℝ α (r+1))(x:PAC α m)(z:Site m)(b:Beads α (r+1))(i:Co m α) : paidU U x z b i = if silks z b 0=i then U b*rosary (fun _=>x) z (stem1 b) else 0 := by
   unfold paidU rosary brood; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,zpk,Pi.single_apply]; split <;> simp_all; left; rfl
private lemma cares (x:PAC α c)(z:Site c)(u:Coves α r s): (∑ i:Co c α,∑ j,K.acts c i j*(paidU U x z u.1 i*paidU V x z u.2 j))=(interU U V * bob (some c) K : Coves α r s →ℝ) u * rosary (fun _=>x) z (stemPair u) := by
   simp_rw [routine]; rw [sum_eq_single (silks z u.1 0),if_pos rfl,sum_eq_single (silks z u.2 0),if_pos rfl]; rotate_left
   · intro j _ hj; simp [Ne.symm hj]
   · simp
   · intro j _ hj; simp [Ne.symm hj]
   · simp
   unfold bob stemPair interU aboardB rosary; rw [Pi.mul_apply,stroke_trans _ _ _ _ z, Fin.prod_univ_add]; unfold silks; simp only [Fin.append_left, Fin.append_right]; ring
private lemma pairs_k (h: Tidy U)(hv:Tidy V)(hp: Whole K)(x:PAC α c)(z:Site c):
   (∑ i:Co c α,∑ j,K.acts c i j*(stitch U c z (brood i x)*stitch V c z (brood j x))) = stitch (tub (interU U V*bob (some c) K) stemPair) c z (fun _=>x) := by
   let P i j (b:Coves α r s):= K.acts c i j*(paidU U x z b.1 i*paidU V x z b.2 j); have hx(i j): Summable (P i j):= (summable_mul_of_summable_norm (bead_summable U (brood i x) h.pens.of_norm z).norm (bead_summable V (brood j x) hv.pens.of_norm z).norm).mul_left _
   rw [st_tub _ _ (bob_pens h.pens hv.pens hp)]
   simp_rw [stitch_apply h.pens.of_norm,stitch_apply hv.pens.of_norm,tsum_mul_tsum_of_summable_norm (bead_summable U _ h.pens.of_norm _).norm (bead_summable V _ hv.pens.of_norm _).norm,←tsum_mul_left]; change (∑ i:Co c α,∑ j,∑' b,P i j b)=_
   simp_rw [← Summable.tsum_finsetSum (fun j _=>hx _ j)]; rw [← Summable.tsum_finsetSum (s:=univ) (fun i _=>summable_sum (s:=univ) (fun j _=>hx i j))]; exact tsum_congr fun i=> cares ..
lemma pairs_earn (h:Tidy U)(hv:Tidy V)(hp:Whole K)(z:Site c): arch (K.acts c) (rootSong U c z) (rootSong V c z)= rootSong (countP (some c) K U V) c z:= by
   have hm := (bob_pens (p:=some c) h.pens hv.pens hp).pours (stemPair (α:=α) (r:=r) (s:=s)); unfold countP; rw [sew_diagonal (hm.scale _),root_scale z hm]; funext x
   have hy (i j: Co c α) : K.acts c i j* Analysis.D (zpk i) (rootSong U c z) x * Analysis.D (zpk j) (rootSong V c z) x=syl r s* (K.acts c i j*(stitch U c z (brood i x)*stitch V c z (brood j x))) := by
      unfold rootSong; rw [Dfade _ _ (h.sym _),Dfade _ _ (hv.sym _)]; simp only [Pi.smul_apply, Tensor.diagonal, ContinuousMultilinearMap.curryLeft_apply, brood,syl,smul_eq_mul]; ring
   simp_rw [arch,hy,← Finset.mul_sum]; exact congr_arg (syl r s*·) (pairs_k h hv hp x z)
lemma hush₁ (F: Rooted ℝ α 0)(z:Site c)(G:Psalm (Co c α)) : arch (K.acts c) (rootSong F c z) G=0 := by funext x; unfold arch rootSong; simp_rw [Dhush]; simp
lemma hush₂ (F: Rooted ℝ α 0)(z:Site c)(G:Psalm (Co c α)) : arch (K.acts c) G (rootSong F c z)=0 := by funext x; unfold arch rootSong; simp_rw [Dhush]; simp
lemma chorus_frame {U V:Spine ℝ α}(h:Loomed (k+1) U)(hf:Loomed (n+1) V)(hp:Whole K)(z: Site c): large z (k+n) (grail (some c) K U V)= arch (K.acts c) (large z (k+1) U) (large z (n+1) V):= by
   unfold large; rw [arch_first (h:=fun i _=> root_smooth z (U i))]; simp_rw [arch_second (h:=fun (j:ℕ) (_:j∈range (n+1+1))=> root_smooth z (V j))]
   rw [sum_range_succ' (n:=k+1), show (∑ j∈range _, arch (K.acts c) (rootSong (U 0) _ z) (rootSong (V j) _ z))=0 from sum_eq_zero (s:=range (n+1+1)) (fun i _=> hush₁ (K:=K) ..),add_zero]; simp_rw [sum_range_succ' (n:=n+1),hush₂,add_zero]
   rw [triangle_sum (fun i j=> arch (K.acts c) (rootSong (U (i+1)) c z) (rootSong (V (j+1)) c z)) k n]; swap
   · intro i j hh; constructor; · by_contra he; exact hh (by rw [h.budget (i+1) (by omega),root_zero,arch_stop])
     by_contra he; exact hh (by rw [hf.budget (j+1) (by omega),root_zero,arch_wait])
   refine sum_congr rfl ?_; intro i hi; unfold grail; rw [root_sum z (wheel i) (h:=fun j _=> Tidied i (count_tid (h.tide _|>.pens) (hf.tide _|>.pens) hp)|>.pens)]; refine sum_congr rfl ?_; intro j hj; rw [← mem_antidiagonal.mp hj,grant_self, pairs_earn (h.tide _) (hf.tide _) hp]
end YM.RG08.Bands
