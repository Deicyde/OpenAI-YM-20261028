import YM.MergeProof.Ember
import YM.MergeProof.Gallery
import YM.MergeProof.Hash
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable {σ d e t u:ℝ}(p:Hat B R)(T: GaugeDoor R E) (q:ι→Hat B R) (U:Config G f)
def odour := Poly.send p.s (prose p.M U*p.charge)
def fragrance (i:Box f):= Poly.send p.s (entry p.M i U*p.charge)
def owl (i:V)(a:Box c)(U:Config G c):ℂ:= if p.s=B.fire i then p.charge*quoted T p.M a U else 0
variable [Fintype ι]
lemma odors (k:Finset ℕ)(h:∀ i,p.M.turn=.logKey i → i∈ k): (∑ j∈k, if WKey p=.logKey j then amount p U else 0)= odour p U:=by
   unfold WKey; cases hx:p.M.turn with
   | logKey i=> rw [varnish,odour,prose,hx,sum_eq_single i]; rw [if_pos rfl]
                · intro j _ hj; simp [hj.symm]
                · intro hp; exact False.elim (hp (h i hx))
   | gasKey i=> simp [odour,prose,hx]
lemma perfumes : roll q U=∑ i:ι, odour (q i) U:=by
   unfold roll rush; rw [sum_comm]; apply sum_congr rfl; intro i hi; exact odors (q i) U (logDeck q) (fun j h=> (cams q j).2 ⟨i,h⟩)
private lemma flagBase (i:Box f): ∑' j:{ j//barcode R.activities j=i}, (if WKey p=.gasKey j.val then amount p U else 0)=fragrance p U i:=by
   unfold WKey fragrance; cases hp:p.M.turn with
   | logKey i=> simp [entry,hp]
   | gasKey j =>
      unfold entry; rw [hp,varnish]; dsimp only; by_cases hx:barcode R.activities j=i
      · rw [if_pos hx,tsum_eq_single (⟨j,hx⟩)]
        · rw [if_pos rfl]
        intro b hb; exact if_neg fun h=> hb (Subtype.ext (Wing.gasKey.inj h|>.symm))
      rw [if_neg hx,zero_mul,Poly.send_zero];exact (tsum_congr (fun j=> if_neg (fun h=> hx ((congr_arg (barcode R.activities) (Wing.gasKey.inj h)).trans j.property)))).trans tsum_zero
lemma patron (p:Box f): board q p U=∑ i,fragrance (q i) U p:=by
   unfold board rush; rw [Summable.tsum_finsetSum]; exact sum_congr rfl fun i _=>flagBase ..
   intro i _; cases ht:WKey (q i) with
   | logKey j=> simp
   | gasKey j=>
     by_cases he:barcode R.activities j=p
     · refine summable_of_ne_finset_zero (s:={⟨j,he⟩}) ?_; intro i hi; exact if_neg fun h=> hi (mem_singleton.mpr (Subtype.ext (Wing.gasKey.inj h|>.symm))) -- ht rewritten?
     have hx(z:{i// barcode R.activities i=p}): Wing.gasKey j≠.gasKey z.val:=fun h=> he ((congr_arg (barcode R.activities) (Wing.gasKey.inj h)).trans z.property)
     simp [hx] -- edit
lemma freeze (i:V)(a:Box c)(U:Config G c): (∑ j: Mound q, owl (heap q j) T i a U)=∑ j, owl (q j) T i a U:=by
   unfold Mound; rw [Fintype.sum_sum_type,sum_eq_zero (s:=univ) (f:=fun x:Σ j:logDeck q, Rock q (.logKey j.val)=> owl (heap q (.inr x)) T i a U) ?_,add_zero];rfl
   intro j _; unfold owl; rw [if_neg ?_]; intro hx; have ht:2 ≤ (heap q (.inr j)).s.val.card:=large q _ _ j.2.prop; rw [hx] at ht; simp [Census.fire] at ht
lemma banded : board (heap q)=board q:= by funext i U; unfold board; simp_rw [gases]
end YM.MergeProof.Menu
