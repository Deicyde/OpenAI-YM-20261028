import YM.FullVolume.Nectar.Warp
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open MeasureTheory
open FullVolume.Ray Jams
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {n:Side} {B:BudgetPoint} {ι I:Type*}{X:ι→Support n}{p e v:ℝ}
namespace RollsUp
variable {f:sun→ι→ Config G n→ℂ}
lemma surge (h:RollsUp B X f p e v)(x:ℂ):RollsUp B X (x • f) p e (‖x‖*v):=by
   obtain ⟨a,hx,h⟩:=h.funds; exact ⟨‖x‖ • a,br_scale hx (norm_nonneg x),fun i U=> mult (Scout.still (h i U).ray _) (h i U)⟩
lemma wave (S:Finset I) (hv:1≤p)(b:I→ℝ)(F:I→sun→ι→ Config G n→ℂ)(h:∀ i∈S,RollsUp B X (F i) p e (b i)): RollsUp B X (∑ i∈S,F i) p e (∑ i∈S,b i):=by
    induction S using Finset.induction with
    | empty => simp only [sum_empty];refine ⟨0,br_zero ..,fun i U=>?_⟩;exact (Scout.still hv (0:ℂ)).enlarged norm_zero.le
    | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact addsUp (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma rock (h:RollsUp B X f p e v)(he:0≤e)(y:sun)(u:Config G n): Summable fun i=>f y i u:=by
    obtain ⟨a,ha,h⟩:=h.funds; apply Summable.of_norm_bounded ha.2.1; intro i; have ht:=h i u; have hx:= ht.held y.property;rw [phrased] at hx; exact hx.trans (le_mul_of_one_le_left ht.nonneg (Real.one_le_exp (mul_nonneg he (by positivity))))
lemma emptyWave (B:BudgetPoint)(X:ι→Support n)(p e:ℝ)(hp:1≤p): RollsUp B X (0:sun→ι→ Config G n→ℂ) p e 0:=by convert! wave (B:=B) (X:=X) (e:=e) (∅:Finset Unit) hp (fun _=> (0:ℝ)) (fun _=> (0:sun→ι→ Config G n→ℂ)) (by simp) <;> simp
end RollsUp
end YM.PhysicalNext.Repeat.Luna
