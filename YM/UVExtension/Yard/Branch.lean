import YM.UVExtension.Yard.Signal
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Yard
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Finset
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration WilsonStartup Residual Averaging Geo
open Lamppost Concert
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint} {P : Listing G n} {X:Support n} {D Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y} {σ C Λ b c : ℝ}
    (a:D→ Collection.Source G n)
    (K : PathData G)(v:Clip)
variable (hG : G.Simple) (F:Atlas (fork p G P.reg (preExponent p)) M (fun d=>trill p G P.reg (preExponent p) (a d).logRead) (fun _=>b))
    (H:∀ d,smoothP p P.reg (a d).logRead)

variable {A:Collection.Source G n}
    (hv:Decent v p)(hK: K.Bounds v σ C Λ)(he: Geo.Width p v σ)
include hv hK he hG
lemma switch (x:ℝ)(h:smoothP p P.reg A.logRead)(hp: Meter.MeasureP (fork p G P.reg (preExponent p)) (trill p G P.reg (preExponent p) A.logRead) b): let X:= shelves P K p; let Y:= branch P K v p A x
     smoothP p X.reg Y.regular∧ (fork p G X.reg p.supportExponent).MeasureP (trill p G X.reg p.supportExponent Y.regular) (regularNeed G p v σ C x b)∧ (softer X p.B (p.supportExponent+1)).MeasureP (fun i u=> Y.logarithm i u) (softNeed G p v σ C x b):=by
  intro X Y
  have hr:= projects_ledger h hp; let t:= delta (P.read A); let Q i:=archive P K v A x t i
  obtain ⟨f,hf,hF⟩:= (fork_earns ..).1 hp
  obtain ⟨hq,hW⟩:= Collection.Local.quote_family hK hv he x t hf hF (delta_bound hG hr)
  have hx i U := Collection.Local.quote_soft (R:=K) (c:=v) hG x t hf h i U
  have he' i:= Collection.Local.quote_regular hG hK hv x t hf h i
  have ht (i:EKey n): p.Regular (incoming P K p i).support (Q i):= by
    rcases i with i|⟨z,d⟩|⟨z,d⟩; exact rebate_regular _ (h _); exact z.regular (d.fresh_regular K v 0 hv _); exact z.regular (d.fresh_regular K 0 hK p _ _)
  refine ⟨fun i=> ht _,(fork_earns X.reg _).2 ⟨_,fun i=> he' (numbering _ i),fun i=>?_⟩,⟨fun i=> Collection.quoteL K p v x t f (numbering _ i),fun i=>⟨?_,fun U=> hx _ U⟩,(soot ..).2 (fun i=> Cost.equiv (numbering _) (hW i))⟩⟩
  ·
    have hy: Quotes.anchored p X.reg (fun i=> Collection.quoteE K p v x t f (numbering _ i)) (regularNeed G p v σ C x b):= fun i=> Cost.equiv (numbering _) (hq i)
    convert hy i using 2 with z; split <;> first | exact mul_comm .. | rfl
  exact (norm_nonneg _).trans (hx _ 1)

omit hv hK he hG
variable (s:Finset D)(w:D→ℝ)
include H
private lemma furl (i:ℕ)(x:Config G n): payout (P.reg i) ((terms a s w).logRead i) x= ∑ j∈s,w j*payout (P.reg i) ((a j).logRead i) x:=by
  simp_rw [payout,counter,quad, collapse a H s w]; simp_rw [Finset.sum_mul,← mul_div_assoc, Finset.mul_sum]; rw [← Finset.sum_div]; congr 1; conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; rw [sum_comm]; refine Finset.sum_congr rfl fun j _=>?_ ; apply Finset.sum_congr rfl; intro j _; ring
include hG F
lemma linear {sp:ℝ} (hf:Projects (P.read (terms a s w)) p sp): let _X:=shelves P K p; let t(d):= branch P K v p (a d) 0; let U:= branch P K v p (terms a s w) 0
    (∀ i,U.regular i= ∑ j∈s,w j • (t j).regular i)∧ (∀ i x,U.logarithm i x=∑ j∈s,w j*(t j).logarithm i x):=by
  intro X t U
  let b j:=Averaging.delta (P.read (a j))
  have hb := stepL a hG F H s w hf
  let A:= terms a s w
  let c:=delta (P.read A); have hc:c=∑ j∈s,w j*b j:=hb
  have hu i x:A.logRead i x= ∑ j∈s,w j*(a j).logRead i x:= Finset.sum_apply .. -- ambiguity
  -- shortcut pointwise
  constructor
  · intro i; funext x; rw [Finset.sum_apply]
    suffices he: ∀ i:EKey n,archive P K v A 0 c i x= ∑ j∈s,w j*archive P K v (a j) 0 (b j) i x from he (numbering _ i)
    rintro (i|i|i)
    · simp_rw [archive,Sum.elim,rebate,Pi.sub_apply, hu,show payout (P.reg i) (A.logRead i) _= _ from furl a H s w i x,mul_sub,sum_sub_distrib]
    · simp_rw [archive,Sum.elim,Function.comp_apply, Low.fresh,hc]; rw [Finset.mul_sum]; simp_rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _=> (by ring)
    simp_rw [archive,Sum.elim,Function.comp_apply, High.fresh,hc, mul_zero,zero_add, Finset.mul_sum, ← sum_neg_distrib, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (by ring)
  intro i x
  suffices he :∀ i:LKey n, loses P K v p A 0 c i x= ∑ j∈s,w j*loses P K v p (a j) 0 (b j) i x from he _
  rintro (i|i)
  · simp_rw [loses,Sum.elim, fault]; split
    next => simp
    next h => split <;> split <;> simp only [add_zero,sub_zero,hu, show payout (P.reg i) (A.logRead i) x= _ from furl a H s w i x, mul_add,mul_sub,sum_sub_distrib,sum_add_distrib]
  simp_rw [loses,Sum.elim, Function.comp_apply, Low.loan]; split; next => simp
  next => split <;> simp only [mul_zero,zero_add,hc,mul_sum,sum_mul,mul_sub,sum_sub_distrib,sub_zero]
          all_goals congr 1 <;> first | rfl | (funext j; ring) | (exact Finset.sum_congr rfl fun i hi=> by ring)
end YM.UVExtension.Yard
