import YM.UVExtension.Rafter.Hales
import YM.UVExtension.Wet.Laces
/-! # Credit conversion for regular raw hull including rebate.Joint enlargement.Portion. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Lamppost Concert Local MergeProof Planned.GuardedAtom Guard Rainfall Eyelet Source Next.Foundations Wet
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{d:ℕ}{ι D Z Y:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    {T:Opening D Z}{A:Hol G}{U:Labels.Frame G d}{B:SectionData U}
set_option quotPrecheck false
noncomputable def shop (p:BudgetPoint)(X:ι→Support n): Meter.{0} ι Unit:=⟨fun i=> Tap p G 0 (X i),fun _ i=>Real.exp ((p.supportExponent+2)*coverNumber p.B (X i)),fun _ _=>(Real.exp_pos _).le, fun _=>⟨(),Real.exp_pos _⟩⟩
-- need include G
noncomputable def bank (p:BudgetPoint)(X:ι→Support n): Meter.{0} ι Unit:=⟨fun _=> Config G n,fun _ i=>Real.exp ((p.supportExponent+2)*coverNumber p.B (X i)), fun _ _=> (Real.exp_pos _).le,fun _=>⟨(), Real.exp_pos _⟩⟩
variable (p:BudgetPoint)(w t:ℝ) (X:ι→Support n) (M:D→ι→ Config G n→ℂ) (hv:∀ i, (0:Site n)∈ X i)(h:Readable A B p n t)(hp:∀ i j,p.Regular (X j) (M i j))
variable (s:Finset D)(F:D→ℂ)(u:ℝ)
local notation "H"=> shop (G:=G) p X
local notation "G'"=> fun i : ι=> joint B (0:Site n) (X i)
local notation "Σ'"=> shop (G:=G) p G'
local notation "U!"=> bank (G:=G) p G'
local notation "T!"=> fun d i k => (k:Tap p G 0 (X i)).read (M d i)
local notation "V"=> p.threshold
local notation "φ"=> readPrice A U
local notation "r"=> atomPrice A U t
local notation "ξ"=> Local.factor A B p.supportExponent t
include hp hv h
lemma countertop (hZ:(H).MeasureP (fun i (k:Tap p G 0 (X i))=> ∑ j∈s,F j*k.read (M j i)) u) :
    SumBudget (fun i=> ‖∑ j∈s,F j • weighted A U 0 (X i) V (M j i)‖) (φ*u) ∧
     (Σ').MeasureP (fun i (k:Tap p G 0 (joint B 0 (X i)))=> ∑ j∈s,F j*k.read (Local.residual A B 0 (X i) V (M j i))) (ξ*u) ∧ (U!).MeasureP (fun i k=> ∑ j∈s,F j*rebate A B 0 (X i) V (M j i) k) (ξ*u):=by
   obtain ⟨a,ha,hT⟩:= hZ.afloat; have ht:= hT ()
   let f i:=∑ j∈s,F j • M j i
   have hF(i):= Rainfall.shelly (X:=X i) h (fun j=> M j i) F (fun j=> hp j i) s
   have hg (i): p.supBounds 0 (X i) (f i) (a i):= tap_bound.mpr ⟨(ha i).1, fun k=>?_⟩; swap
   · apply Eq.trans_le (congr_arg norm ?_) ((ha i).2 k); change k.read (f i)= _; unfold f; rw [Tap.read,Local.left_sum _ _ _ _ (fun j _=> (regular_smul _ (hp j i)).smooth k.view k.live) k.card]; exact Finset.sum_congr rfl (fun j _=> Local.left_linear (F j • ContinuousLinearMap.id ℝ ℂ) k.poll ((hp j i).smooth k.view k.live) k.card)
   constructor
   · have hA : SumBudget a u:= budget_mono ht (fun i=> (ha i).1) fun i=> le_mul_of_one_le_left (ha i|>.1) (Real.one_le_exp (mul_nonneg (add_nonneg p.exponent_pos.le zero_le_two) (by positivity)))
     exact budget_mono (budget_scale (zero_le_one.trans (readPrice_pos A U)) hA) (fun i=> norm_nonneg _) (fun i=>by rw [← (hF i).2]; exact (Local.norm_le_size ..).trans (weighted_bound _ _ _ (hF i).1 h.order h.power (hg i)))
   let z(i:ι):= r*a i; have hr:0 ≤ r:= zero_le_one.trans (atomPrice_ge_one _ _ h.nonneg); have hV(i):0 ≤ z i:=mul_nonneg hr (ha i|>.1)
   have hr' : SumBudget (fun i=> reservedMass p (joint B (0:Site n) (X i)) (z i)) (ξ*u):= budget_mono (budget_scale (mul_nonneg (Real.exp_pos _).le hr) ht) (fun i=>mul_nonneg (Real.exp_pos _).le (hV i)) (fun i=>price_join B A _ (hv i) h.sound h.nonneg (ha i|>.1)) -- field
   let g i:= Local.residual A B 0 (X i) p.threshold
   have he i:g i (f i)= ∑ j∈s,F j • g i (M j i):= by
      unfold g f Local.residual; rw [(hF i).2,map_sum]; simp_rw [map_smul, smul_sub]; rw [Finset.sum_sub_distrib]
   have hf(i):= charge_atom _ h (hF i).1 (hg i)
   constructor
   · refine ⟨z,fun i=> ⟨hV i,fun k=>?_⟩,fun _=>hr'⟩; let k':Tap p G 0 (G' i):= k
     refine Eq.trans_le (congr_arg norm ?_) ((tap_bound.mp (hf i).1).2 k'); symm
     change k'.read (g i (f i))= ∑ j∈s,F j*k'.read (g i (M j i))
     have hL(j):p.Regular (joint B 0 (X i)) (g i (M j i)):= (convert_atom _ h (hp j i)).1
     rw [he i,Tap.read,Local.left_sum _ _ _ _ (fun j _=> (regular_smul _ (hL j)).smooth k'.view k'.live) k'.card]; exact Finset.sum_congr rfl (fun j _=> Local.left_linear (F j • ContinuousLinearMap.id ℝ ℂ) k'.poll ((hL j).smooth _ k'.live) k'.card)
   refine ⟨z,fun i=> ⟨hV i,fun k=>?_⟩,fun _=>hr'⟩
   refine Eq.trans_le (congr_arg norm ?_) ((hf i).2 k); symm; let Gp:=rebate A B 0 (X i) p.threshold
   change Gp (f i) k= ∑ j∈s,F j*Gp (M j i) k
   have hP(q):Gp q = maskLinear V (X i) q -Local.primary B 0 V (weighted A U 0 (X i) V q)-maskLinear V (joint B 0 (X i)) (g i q):=rfl
   rw [show Gp (f i)= ∑ j∈s,F j • Gp (M j i) from ?_,Finset.sum_apply]; rfl
   simp_rw [hP]; rw [(hF i).2, map_sum, he i, map_sum, map_sum]; simp_rw [smul_sub,map_smul, Finset.sum_sub_distrib];
lemma hold (ha:0≤w)(he:Stalk (shop (G:=G) p X) T (fun i j (k:Tap p G 0 (X j))=> k.read (M i j)) w)(hT:∀ i,Summable fun j=> weighted A U (0:Site n) (X j) V (M i j)):
   (∃ f:Z→U.Coeff,Bumps T.span f ∧ (∀ d,f (T.call d)=∑' i,weighted A U 0 (X i) V (M d i))∧∀ z∈T.span,‖f z‖≤2*φ*w)∧ Stalk (Σ') T (fun d i (k:Tap p G 0 (joint B 0 (X i)))=> k.read (Local.residual A B 0 (X i) V (M d i))) (4*ξ*w) ∧ Stalk (U!) T (fun d i k=> rebate A B 0 (X i) V (M d i) k) (4*ξ*w):=by
   have hx:0≤ξ:=mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (atomPrice_ge_one _ _ h.nonneg))
   have hv(s F k hk):= countertop p t X M hv h hp s F k hk
   refine ⟨sprigs he ha (zero_le_one.trans (readPrice_pos ..)) _ ?_,he.directs _ (fun s F k _ hk=>(hv s F k hk).2.1) hx ha, he.directs _ (fun s F k _ hk=>(hv s F k hk).2.2) hx ha⟩
   intro s F k hk hx
   let f i j:= weighted A U 0 (X j) V (M i j); let e j:=∑ i∈s,F i • f i j
   have hg:= (hv s F k hx).1; have h':∑' j,e j=∑ i∈s,F i • ∑' j,f i j:=by
      unfold e; rw [Summable.tsum_finsetSum]; swap; · intro i _; exact (hT i).const_smul _
      apply Finset.sum_congr rfl; intro i _; exact (hT i).tsum_const_smul _
   rw [show ∑ i∈s,F i • ∑' j,weighted A U 0 (X j) V (M i j)= _ from h'.symm]; exact (norm_tsum_le_tsum_norm hg.2.1).trans hg.2.2
end YM.UVExtension.Rafter
