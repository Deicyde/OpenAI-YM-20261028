import YM.UVExtension.Steady.Waves
import YM.UVExtension.Steady.Scout
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Spool

/-! Finite under fixed periods: many copies of the *same* record may differ by
    i. Condense only to account summability in fixed cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Push.AbsoluteSums Finset ConnectedActivityE6
open Next.Fluctuations Exterior Blaze Channel SliceRows Work.F03 Reward AnalyticBridge.NonflatCovarianceLocality
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {ι κ π : Type*}{v:Filter ι} {R:ι→ PathData G} {σ:ℝ} {g:PathData G}

namespace Revenues
def oneOf (R:PathData G)(b:PlaqAxes)(s:Slot)(i:ℕ):= if (R.row b i).2=s then (R.row b i).1 else 0
def coins (R:PathData G)(b:PlaqAxes)(s:Slot):= ∑' i, oneOf R b s i
variable (p: Revenues v σ R g)
include p
-- exact locus finite; use exp weights for prices.
lemma leaf (n:ι)(b:PlaqAxes):Summable (fun i=>|((R n).row b i).1|):=by
    obtain ⟨w,x,t,H⟩:=p.cops n; exact row_abs_summable (R n) H b
lemma whole (n:ι)(b:PlaqAxes)(s:Slot): Summable (oneOf (R n) b s) := by
    refine Summable.of_norm_bounded (p.leaf n b) ?_; intro i; unfold oneOf; split; exact le_rfl; rw [norm_zero]; exact abs_nonneg _
lemma countTo (b:PlaqAxes)(s:Slot): Tendsto (fun n=> coins (R n) b s) v (𝓝 (coins g b s)):=by
   rcases eq_or_ne v ⊥ with h|h
   · rw [h]; exact tendsto_bot
   haveI : NeBot v:= ⟨h⟩; obtain ⟨r,hr⟩:= (p.fees b).2.books; have ht:= (p.fees b).1
   have hp:=p.pos; have hk : Summable (oneOf g b s):= by
     apply Summable.of_norm_bounded ht; intro i; unfold oneOf; split
     next h=> exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
     next h=> rw [norm_zero]; positivity
   rw [Metric.tendsto_nhds]; intro ε he
   filter_upwards [p.gap _ (half_pos he)] with n hx; unfold coins
   let X:=R n; let f:=fun i=>oneOf X b s i-oneOf g b s i; have hL : Summable f:= (p.whole n b s).sub hk
   rw [dist_eq_norm, ← Summable.tsum_sub (p.whole n b s) hk]; change ‖∑' i,f i‖<_
   refine (norm_tsum_le_tsum_norm hL.norm).trans_lt ((hL.norm.tsum_mono (hx.1 b).2.1 (fun i=>?_)).trans_lt ((hx.1 b).2.2.trans_lt (half_lt_self he))) -- sum sign
   unfold f X oneOf; rw [p.slots]; split
   · exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
   rw [sub_zero,norm_zero]; exact (hx.1 b).1 _
lemma condensed_use {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F] (n:ι)(b:PlaqAxes)(f:Finset Slot) (X:Slot→F):
     (∑' i, if ((R n).row b i).2∈f then ((R n).row b i).1 • X ((R n).row b i).2 else 0)= ∑ i∈f,coins (R n) b i • X i :=by
   have hp := hasSum_sum (f:=fun i j=>oneOf (R n) b i j • X i) (s:=f) (fun i _=> ((p.whole n b i).hasSum.smul_const (X i)))
   apply Eq.trans ?_ hp.tsum_eq; apply tsum_congr; intro i; simp only [oneOf, ite_smul,zero_smul,Finset.sum_ite_eq]
-- Exact finite support fix: d positive
lemma braces (k:ι)(x:Cell n)(U:Config G n)(P:ℕ) {d:ℕ}(hd:0<d):
   let s:= (spool P).filter fun i=> i.length*d ≤ P; shorten (R k) P d U x=∑ i∈s, coins (R k) x.2 i • i.atSite U x.1:=by
  intro s; rw [← condensed_use p .. ]
  · apply tsum_congr; intro i; unfold shortenTerm
    have h(s':Slot): s'.length*d≤P ↔ s'∈s:=by
       simp only [s,mem_filter,on_spool]; constructor; exact fun h=> ⟨(le_mul_of_one_le_right (Nat.zero_le _) hd).trans h,h⟩; exact And.right
    simp only [← h]; rfl

lemma rates (k:ι)(x:Cell n)(u:LogField G n)(P:ℕ): ellCut (R k) P u x= ∑ i∈spool P,coins (R k) x.2 i • faceCurl (slotFace i x.1) u :=by
   rw [← condensed_use p .. ]; apply tsum_congr; intro n; simp only [on_spool]
end Revenues
lemma pairsHere {F:Type*}[NormedAddCommGroup F](f:ι→ Bool→F)(x:F)(h:∀ i,Tendsto (fun n=>f n i) v (𝓝 x)): Together v f:= by
   refine ⟨⟨‖x‖+1,(eventually_all.mpr (?_ : ∀ i:Bool,∀ᶠ k in v, ‖f k i‖≤ ‖x‖+1))⟩,?_⟩
   · exact fun i=> (h i).norm.eventually_le_const (by linarith)
   simpa using (h true).dist (h false)
section maps
variable {F E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q:ℕ} {d:ℝ} {V:ι→ E→ Config G n}
   {τ:ι→ E} (h:∀ᶠ t in v, Mode (V t) (τ t) p d)
variable (a:ι→ Bool→ PathData G)(hw:∀ b,Revenues v σ (fun n=>a n b) g)
include hw
lemma domino {W:ι→ Bool→ E→ Directions G n} (hP:∀ i,Walt v τ p (fun n b y=> W n b y i)) (i:Cell n) (t:ℕ): Walt v τ p (fun n b y=> ellCut (a n b) t (toLog (W n b y)) i):=by
   have hz(j): Walt v τ p (fun n b y=>faceCurl j (toLog (W n b y))):= by simp_rw [curl_eq]; exact ((hP _).minus (hP _)).minus ((hP _).minus (hP _))
   let coins' u x b:= Revenues.coins (a x b) i.2 u
   let f u x b y:= coins' u x b • faceCurl (slotFace u i.1) (toLog (W x b y))
   refine (Walt.schedule (spool t) f (fun j _=> Walt.pay (Walt.stamp (pairsHere (fun n b=> coins' j n b) (Revenues.coins g _ j) (fun y=> (hw y).countTo i.2 j))) (hz _))).same ?_; filter_upwards with n b; filter_upwards with y; exact (hw b).rates ..
include h
lemma media (Z d':ℕ)(i:Cell n)(he:0<d') : Walt v τ p (fun n b y=> shorten (a n b) Z d' (V n y) i):=by
   have hp(s:Slot):Walt v τ p (fun n (_:Bool) y=> s.atSite (V n y) i.1):= by
      apply Walt.twin (royalty G^2) (2*s.length*(d*royalty G)); exact h.mono fun n hn=>⟨slot_cost s _ hn.pos hn.atLink,rfl⟩
   let s:= (spool Z).filter fun i=> i.length*d'≤Z; let f (u:Slot) x b y:= Revenues.coins (a x b) i.2 u • u.atSite (V x y) i.1
   refine (Walt.schedule s f (fun u _=> Walt.pay (Walt.stamp (pairsHere (fun n b=> Revenues.coins (a n b) i.2 u) _ (fun y=>(hw y).countTo i.2 u))) (hp u))).same ?_
   exact Eventually.of_forall fun n b=> Eventually.of_forall fun y=> (hw b).braces n i (V n y) Z he
lemma queries (t D:ℕ)(A:Clip)(ht:0<D)(i:Twin n): Walt v τ p (fun n b y=> plotted (a n b) A t D (V n y) i):=by
   unfold plotted; split_ifs
   exact media h a hw t D i.1 ht
   exact Walt.pay (Walt.ready _) (Walt.twin 1 (4*(d*royalty G)) (h.mono fun n hn=>⟨show Brush p 1 (4*(d*royalty G)) (fun y=> G.curvature (faceValue (V n y) i.1)) (τ n) from Blaze.sculpt (g:=fun y=> faceValue (V n y) i.1) (by convert! (Blaze.tour (square i.1.2.val.1 i.1.2.val.2) i.1.1 hn.pos hn.atLink) using 1),rfl⟩))
end maps
end YM.UVExtension.Steady
