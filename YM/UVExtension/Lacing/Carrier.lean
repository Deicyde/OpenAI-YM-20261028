import YM.UVExtension.Lacing.Canvas
/-!
 # Full UV fixed layout at every permitted level, operator consequence.
 analytic needs later. Quantitative restart. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08 Remnant
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:Levels G} {d:ℕ}{F:Frame G d}{A:Hol G} {p:ℕ}
variable (F A H p)
abbrev RestA (m:ℕ):= Cow G (H.S.side m p) (H.budget m) d A -- F absence
abbrev Card (m:ℕ):= F.Coeff →ₗ[ℂ] Cow G (H.S.side m p) (H.budget m) d A
abbrev Banner (m:ℕ):= RoutesF F (H.S.side m p) (H.S.side (m+1) p) (H.budget (m+1)) (H.budget m) A
variable {F A H p} (L:∀ m:ℕ, ℕ → Banner (H:=H) F (A:=A) (p:=p) m) (Y:∀ m:ℕ,ℕ→Card (H:=H) F (A:=A) (p:=p) m)
--- binder badges
abbrev glaring (K:Levels G) (i p:ℕ): 2≤(K.S.side i p).val:= Nat.le_trans (by decide : 2 ≤ 4) (Next.Foundations.actual_side_ge K.S i p)

def slip {m:ℕ}(Y': ℕ → Card (H:=H) F (A:=A) (p:=p) (m+1)) (i:ℕ) := crown (fun _=> L m i) (fun _=> Y' i) (glaring H m p) -- var m missing

def stopE (i j:ℕ)(hp:i ≤ j) : ℕ→Card (H:=H) F (A:=A) (p:=p) i:= Nat.decreasingInduction (motive:=fun i _=>ℕ→Card (H:=H) F (A:=A) (p:=p) i) (fun k hk x=> slip L x) 0 hp

structure Tribe (m:ℕ)(L:Banner (H:=H) F (p:=p) (A:=A) m)(u v c:ℝ): Prop where
  efforts: ∃ T:Heading F,Tips L (H.S.block m) T u v∧∀ x, F.coeffSize (T.map x)≤ c*F.coeffSize x∧ F.coeffSize (T.map.symm x) ≤ c* F.coeffSize x
variable {w c v u:ℕ→ℝ}
def Length (F:Frame G d) {X: Type}[AddCommGroup X][Norm X][Module ℂ X] (L:F.Coeff→ₗ[ℂ] X)(s:ℝ):=∀ x, ‖L x‖≤ s*F.coeffSize (F.core x)
structure Arcus (r:ℕ)(F:Frame G d)(L:∀ m:ℕ, ℕ→ Banner (H:=H) F (A:=A) (p:=p) m)(Y:∀ i:ℕ,ℕ→Card (H:=H) F (p:=p) (A:=A) i)(u v c w:ℕ→ℝ) : Prop where
   stamp i (hi:r ≤ i):Lacing.Tollgate F (u i) (v i) (c i) (w i) (w (i+1))
   port i (hi:r ≤ i) j (hp:i<j): Tribe i (L i j) (u i) (v i) (c i)
   land i (hi:r ≤ i): Course (L i)
   light i (hi:r ≤ i) j (hv:i ≤ j) : Length F (Y i j) (w i)
   slip i (hi:r ≤ i) k (hk:i<k) : Y i k=Lacing.slip L (Y (i+1)) k

namespace Arcus
variable {L Y} {r:ℕ}(h:Arcus (H:=H) (p:=p) r F (A:=A) L Y u v c w)
include h
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 420000 in
lemma price (m k:ℕ) (hp:r ≤ m)(hk:m ≤ k)(j:ℕ)(hV:k≤j):let X:= stopE L m k hk j
    Length F X (w m) ∧ Length F (X-Y m j) ((1/8)^(k-m)*w m):=by
   induction hk using Nat.decreasingInduction with
   | self =>
      rw [stopE,Nat.decreasingInduction_self]; dsimp only [Pi.zero_apply,Nat.sub_self,pow_zero,one_mul]; refine ⟨fun x=> ?_, fun x=> ?_⟩
      · rw [LinearMap.zero_apply,norm_zero]; exact mul_nonneg (zero_le_one.trans (h.stamp k hp).t_now) (size_nonneg ..)
      rw [zero_sub,LinearMap.neg_apply,norm_neg,Nat.sub_self,pow_zero,one_mul]; exact h.light _ hp _ hV x
   | of_succ i hi IH=>
      intro Z; have hp':=hp.trans i.le_succ; let X:=stopE L (i+1) k hi j; obtain ⟨hX,hY⟩:= IH hp'
      have hJ:=hi.trans_le hV; obtain ⟨T,hT,hC⟩:= (h.port i hp j hJ).efforts; have he:=h.stamp i hp
      let f:=fun _:Motion=> L i j; let g:=fun _:Motion=> X; let p':= Y (i+1) j
      have hx: Z=crown f g (glaring H i p):= by
         change stopE L i k _ j=_; unfold stopE; rw [Nat.decreasingInduction_succ_left]; rfl
      rw [hx,h.slip i hp j hJ]
      have hz(i':Motion): ∀ x, ‖(fun _=>X) i' x‖≤ (w (i+1))*F.coeffSize (F.core x):= hX
      have ht :∀ k, Tips (f k) (H.S.block i) T (u i) (v i):=fun _=> hT
      constructor
      · intro x; have hv:=brunt he ht hC (Y:=g) (hh:=hz) (glaring H i p) x; convert! hv
      intro x
      let t:= (1/8:ℝ)^(k-(i+1))
      have hs:∀ k:Motion,∀ x, ‖g k x-(fun _ :Motion=> p') k x‖ ≤ t*(w (i+1))*F.coeffSize (F.core x):= fun i x=> hY x
      have hU:= discount (L:=f) (Y:=g) _ he ht hC (hh:=hz) (glaring H i p) (by unfold t; positivity) (fun _=> h.light _ hp' _ hJ) hs x
      rw [show k-i=k-(i+1)+1 by omega, pow_succ]; unfold Lacing.slip; rw [LinearMap.sub_apply]; convert! hU

lemma cone (m k:ℕ)(hp:r ≤ m)(hk:m ≤ k)(x:F.Coeff): Arrives fun i=> stopE L m k hk i x:= by
   induction hk using Nat.decreasingInduction generalizing x with
   | self=> unfold stopE; simp_rw [Nat.decreasingInduction_self]; exact Arrives.steady 0
   | of_succ i hi IH =>
      let X n:=fun _:Motion=>stopE L (i+1) k hi n; let f n:=fun _:Motion=> L i n; let Y n:= stopE L i k hi.le n; let hn:=glaring H i p; have hW:=pilastered (H:=A) (Y:=X) (L:=f) hn (fun _=> h.land i hp) (fun _ a=> IH (hp.trans i.le_succ) a) (2*c i) (by
         filter_upwards [eventually_ge_atTop k] with y hy; obtain ⟨T,hT,hC⟩:= (h.port i hp y (hi.trans_le hy)).efforts; exact fun x=>(Gate (h.stamp i hp) (L:=f y) (Y:=X y) (fun _=>hT) hC (fun _=> (h.price _ _ (hp.trans i.le_succ) hi y hy).1) hn x).1) (mul_nonneg zero_le_two (zero_le_one.trans (h.stamp i hp).calm)) x
      apply hW.2.copy; filter_upwards with j; symm; unfold stopE; rw [Nat.decreasingInduction_succ_left]; rfl

lemma cove (m:ℕ)(hp:r ≤ m)(x:F.Coeff): Arrives fun i=> Y m i x := by
   let f:= fun i=>Y m i x; apply cauchySeq_tendsto_of_complete; rw [Metric.cauchySeq_iff]
   intro ε he
   let T:=F.coeffSize (F.core x)
   have hT: Tendsto (fun i:ℕ=> (1/8:ℝ)^i *w m*T) atTop (𝓝 0) :=by
      simpa only [zero_mul] using! (((tendsto_pow_atTop_nhds_zero_of_lt_one (r:=1/8) (by norm_num) (by norm_num)).mul_const (w m)).mul_const T)
   obtain ⟨k,hk⟩:= (hT.eventually (gt_mem_nhds (by positivity:0 < ε/3))).exists
   let s:=m+k; have hS:m ≤ s:=by unfold s; omega
   let P i:= stopE L m s hS i x; obtain ⟨q,hq⟩:= h.cone m s hp hS x
   obtain ⟨i,hx⟩:= Metric.cauchySeq_iff.mp hq.cauchySeq (ε/3) (by positivity)
   have hj(j:ℕ)(hi:s ≤ j): dist (P j) (f j)< ε/3:=by
      rw [dist_eq_norm]; refine ((h.price m s hp hS j hi).2 x).trans_lt ?_; rw [show s-m=k from by unfold s; omega]; exact hk
   refine ⟨max i s,fun j hj' k hk' =>?_⟩
   have hE := hj j (by omega); have hQ:= hj k (by omega); have hf:= hx j (by omega) k (by omega); change dist (P j) (P k)<_ at hf; rw [dist_comm] at hE; change dist (f j) (f k)<_; linarith [dist_triangle (f j) (P j) (P k),dist_triangle (f j) (P k) (f k)]
end Arcus
end YM.UVExtension.Lacing
