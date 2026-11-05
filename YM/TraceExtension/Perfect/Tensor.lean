import YM.TraceExtension.Perfect.Volume

/-! # Tensor shell composition packets -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Stationary Filter Function Matrix Lattice Precision Finset OrderedFinpartition
open scoped Topology BigOperators ContDiff
variable {I J W:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
    {m : ℕ} {X : Type*}[NormedAddCommGroup X][NormedSpace ℝ X]

def scheme (c:OrderedFinpartition m)(x:Fin m→I) (i:Fin c.length) := x ∘ c.emb i
omit [Fintype I] [DecidableEq I] in
lemma scheme_equiv (c:OrderedFinpartition m): Bijective (scheme (I:=I) c) := by
 refine ⟨?_,?_⟩
 · intro x y h; ext i; obtain ⟨⟨k,l⟩,hi⟩:=c.equivSigma.surjective i; rw [← hi]; exact congr_fun (congr_fun h k) l
 intro z; let v : Fin m→I:= (fun j : (i:Fin c.length)×Fin (c.partSize i)=>z j.1 j.2) ∘ c.equivSigma.symm; refine ⟨v,?_⟩; ext i j; change z ((c.equivSigma.symm _).1) ((c.equivSigma.symm _).2)=_; exact congr_arg (fun j : (i:Fin c.length)×Fin (c.partSize i)=> z j.1 j.2) (c.equivSigma.symm_apply_apply ⟨i,j⟩)

omit [DecidableEq I] in
lemma splitSum (c:OrderedFinpartition m)(F:(i:Fin c.length)→(Fin (c.partSize i)→I)→ℝ):
    (∑ x : Fin m → I,∏ i,F i (scheme c x i)) = ∏ i, ∑ v,F i v:=by
 classical
 let f (z:(i:Fin c.length)→(Fin (c.partSize i)→I)):= ∏ i,F i (z i)
 change (∑ x : Fin m→ I, f ((Equiv.ofBijective _ (scheme_equiv c)) x)) = _
 rw [Equiv.sum_comp]; unfold f; rw [Fintype.prod_sum]

omit [DecidableEq I] in
lemma plate (A:I→ℕ)(α t r)(c:OrderedFinpartition m) (f:(i:Fin c.length)→ (Fin (c.partSize i)→ I) → ℝ)
    (h : 0≤α)(hr:0≤r): cost A α t r (fun x=> ∏ i,f i (scheme c x i))≤∏ i,cost A α t r (f i):=by
 classical
 unfold cost; refine le_trans ?_ (le_of_eq (splitSum c (fun i y=> spot α t r (limitN A y) * ‖f i y‖)))
 apply sum_le_sum; intro x _; dsimp only; rw [norm_prod,prod_mul_distrib]; exact mul_le_mul_of_nonneg_right (splitN A _ _ _ _ _ h hr) (prod_nonneg (fun i _=>norm_nonneg _))

omit [DecidableEq I] in
lemma cost_smul (A:I→ℕ)(α t r)(f:(W→I)→ℝ) (u:X): cost A α t r (fun x=>f x • u)=cost A α t r f*‖u‖:=by
 unfold cost; simp_rw [norm_smul,Finset.sum_mul, mul_assoc]

abbrev Rays (I : Type) := I → ℝ
abbrev desk (x: I) : Rays I := Pi.single x 1
abbrev bank (F : ContinuousMultilinearMap ℝ (fun _ : Fin m=> Rays I) X) (v:Fin m → I):X:= F (desk ∘ v)

lemma many (c:OrderedFinpartition m) (F : ContinuousMultilinearMap ℝ (fun _ : Fin c.length=> Rays J) X)
    (x: Fin c.length → Rays J): F x=∑ b: Fin c.length→ J, (∏ i,x i (b i)) • bank F b:=by
 classical
 let g (i:Fin c.length) (j : J):= x i j • desk j
 have h:x=(fun i=>∑ j,g i j):=by ext i l; rw [Finset.sum_apply]; unfold g; simp [desk,Pi.single_apply]
 conv_lhs=> rw [h]
 change F.toMultilinearMap _=_ ; rw [MultilinearMap.map_sum]; apply Finset.sum_congr rfl; intro b _; exact F.toMultilinearMap.map_smul_univ (fun i=>x i (b i)) (desk ∘ b)

omit [DecidableEq I] in
lemma volume_join (A:I→ℕ) (α t)(c:OrderedFinpartition m) (F : ContinuousMultilinearMap ℝ (fun _ : Fin c.length=> Rays J) X)
    (L:(i:Fin c.length)→(Fin (c.partSize i)→ I)→ Rays J)(R:(Fin c.length→ J)→ℝ)
    (h:0 ≤ α)(hR:∀ b,0≤R b) : cost A α t 0 (fun x=> F (fun i=> L i (scheme c x i))) ≤
       ∑ b: Fin c.length→J, shelter α t (R b) * (∏ i,cost A α t (R b) fun v=> L i v (b i))* ‖bank F b‖:=by
 classical
 let g (b:Fin c.length→J) (x:Fin m→I):=(∏ i,L i (scheme c x i) (b i)) • bank F b
 rw [show (fun x=> F (fun i=> L i (scheme c x i)))=fun x=>∑ b,g b x from funext fun x=>many c F _]; refine (cost_sum A α t 0 g).trans (sum_le_sum (fun b _=>?_))
 unfold g; rw [cost_smul]; exact mul_le_mul_of_nonneg_right ((cost_build (fun x:Fin m→I=>∏ i,L i (scheme c x i) (b i)) A α t (R b) h (hR b)).trans (mul_le_mul_of_nonneg_left (plate A α t _ c (fun i v=> L i v (b i)) h (hR b)) (shelter_pos _ _ (hR _)).le)) (norm_nonneg _)

end YM.Trace.Perfect

namespace YM.Trace.Perfect
open scoped Classical Topology BigOperators ContDiff
open Stationary Function Matrix Lattice Precision Finset OrderedFinpartition
variable {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {m : ℕ} {X : Type*}[NormedAddCommGroup X][NormedSpace ℝ X] {f : Rays I → X} {a:Rays I}

abbrev leaf (f:Rays I→ X)(a:Rays I)(m : ℕ):= bank (iteratedFDeriv ℝ m f a)
-- useful high estimates
end YM.Trace.Perfect
