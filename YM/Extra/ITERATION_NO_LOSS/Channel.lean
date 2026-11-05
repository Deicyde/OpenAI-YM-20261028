import YM.Bid.Town
import YM.Next.EXTRACTION.Tails
import YM.Work.B04
import YM.Work.F03.Flat
import YM.Work.F04.Pairing

/-!
# Transporting stationary linear curls in every orientation

Do not assume equivariance of tree representatives or of their logs. Transform the
*linear equation* and use positivity to discard only their possible curl-null
difference. The physical rooted probe equivariance is deduced from the actual
predictor (derivative at flat on its branches). Includes nonzero shifts on
inverted links and the counting/physical color normalization unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Channel
open Lattice Wilson RG Exterior Precision Bloch Tree Matrix Function Finset Bid
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n c f : Side} {S : StepData c f}

def bondBody (n : Side) : Edge (Site n) ≃ Body 1 n := Equiv.prodCongr (Equiv.refl _) axisEquiv
lemma pulled_edge (x : Dir G n) (s : Signed) (e : Edge (Site n)) : pulled x s (bondBody n e) =
    if s.flip e.2 then -x (bondBody n (sendEdge s 0 e)) else x (bondBody n (sendEdge s 0 e)) := by
  rcases e with ⟨a,i⟩
  unfold pulled; change (let u := (posDir (axisEquiv.symm (axisEquiv i))).rotate s; let v := u.used (affine s 0 a)
    if u.neg then -x (v.1,axisEquiv v.2) else x (v.1,axisEquiv v.2)) = _
  rw [axisEquiv.symm_apply_apply]; simp only [sendEdge,Step.rotate,posDir,Bool.false_xor]; rfl

lemma pulls_onto (s : Signed) : Function.Surjective (fun x : Dir G n => pulled x s) := by
  intro x
  let E := StepData.sendBonds (c:=n) s 0
  refine ⟨fun e => let v := E.symm ((bondBody n).symm e); if s.flip v.2 then -x (bondBody n v) else x (bondBody n v), funext fun i => ?_⟩
  obtain ⟨i,rfl⟩ := (bondBody n).surjective i
  dsimp only
  rw [pulled_edge, (bondBody n).symm_apply_apply,show sendEdge s 0 i = E i from rfl,E.symm_apply_apply]
  split <;> simp [*]
lemma pulls_sub (s : Signed) (u v : Dir G n) : pulled (u-v) s = pulled u s - pulled v s := by
  funext i; obtain ⟨i,rfl⟩ := (bondBody n).surjective i
  rw [Pi.sub_apply, pulled_edge,pulled_edge,pulled_edge]
  split <;> simp [*]; abel

def pairing (u v : Dir G n) := ∑ b, dotProduct (parts G 1 u b) (parts G 1 v b)
lemma pair_signed (s : Signed) (u v : Dir G n) : pairing (pulled u s) (pulled v s) = pairing u v := by
  apply sum_congr rfl; intro i _
  unfold dotProduct
  rw [← Equiv.sum_comp (bondBody n), ← Equiv.sum_comp (bondBody n)]
  conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s (0:Site n))]
  apply sum_congr rfl; intro j _; unfold parts
  rw [pulled_edge,pulled_edge]; cases h : s.flip j.2 <;> simp only [Bool.false_eq_true,↓reduceIte, PiLp.neg_apply, neg_mul_neg] <;> rfl
lemma pair_nn (u : Dir G n) : 0 ≤ pairing u u := sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_self_nonneg _
lemma pair_sub (u v w : Dir G n) : pairing u (v-w) = pairing u v - pairing u w := by
  unfold pairing parts dotProduct; simp [sum_sub_distrib,mul_sub]
lemma fiscal_sub (B : Bed) (u v w : Dir G n) : gaugeFiscal B u (v-w)=gaugeFiscal B u v-gaugeFiscal B u w := by
  unfold gaugeFiscal; simp_rw [show ∀ i, parts G 1 (v-w) i=parts G 1 v i-parts G 1 w i from fun _ => rfl,
    mulVec_sub,dotProduct_sub,sum_sub_distrib]
lemma fiscal_flux (B : Bed) (u v : Dir G n) : gaugeFiscal B u v = ∑ i, dotProduct (d 1 n *ᵥ parts G 1 u i)
    (B.metric.acts n *ᵥ (d 1 n *ᵥ parts G 1 v i)) := by
  unfold gaugeFiscal Precision.K; simp_rw [← mulVec_mulVec, dotProduct_mulVec (A:=(d 1 n).transpose),vecMul_transpose]
lemma fiscal_spec {B : Bed} {p η A} (hf : Floor B p n η A) (u : Dir G n) :
    η*(∑ i : G.ColorIndex, ∑ w, ((d 1 n *ᵥ parts G 1 u i) w)^2) ≤ gaugeFiscal B u u := by
  rw [fiscal_flux,mul_sum]; exact sum_le_sum fun i _ => by simpa [dotProduct,sq] using (hf.uniform.1 (d 1 n *ᵥ parts G 1 u i)).1
lemma fiscal_kernel {B : Bed} {p η A} (he : 0 < η) (hf : Floor B p n η A) {u : Dir G n}
    (hz : gaugeFiscal B u u ≤ 0) (i : G.ColorIndex) : d 1 n *ᵥ parts G 1 u i = 0 := by
  have hu := nonpos_of_mul_nonpos_right ((fiscal_spec hf u).trans hz) he
  funext w
  have hx : ((d 1 n *ᵥ parts G 1 u i) w)^2 ≤ 0 := calc
    _ ≤ ∑ w, ((d 1 n *ᵥ parts G 1 u i) w)^2 := single_le_sum (f:=fun w => ((d 1 n *ᵥ parts G 1 u i) w)^2) (fun _ _ => by positivity) (mem_univ w)
    _ ≤ _ := le_trans (single_le_sum (f:=fun i => ∑ w, ((d 1 n *ᵥ parts G 1 u i) w)^2) (fun _ _ => sum_nonneg fun _ _ => by positivity) (mem_univ i)) hu
  rw [Pi.zero_apply]; nlinarith

lemma bills_sub (a b : Dir G f) : bills S (a-b) = bills S a - bills S b := by
  ext e i; change ((probe S) *ᵥ (parts G 1 a i-parts G 1 b i)) _ = _; rw [mulVec_sub]; rfl

lemma bills_signed (s : Signed) (hs : S.patch.Branches S.kernel G) (a : Dir G f) : bills S (pulled a s) = pulled (bills S a) s := by
  let tag : S.Choices := Classical.arbitrary _
  let tag' := S.withinChoice s 0 tag
  funext i; obtain ⟨i,rfl⟩ := (bondBody c).surjective i
  rw [pulled_edge]; apply G.colorMat_injective
  let v := sendEdge s (0:Site c) i
  have he := Push.prices S hs i tag (pulled a s); have hv := Push.prices S hs v tag' a
  change HasDerivAt _ (G.colorMat (bills S _ (bondBody c i))) _ at he
  change HasDerivAt _ (G.colorMat (bills S a (bondBody c v))) _ at hv
  have hz : S.ratio.embed 0 = 0 := S.ratio.root.map_zero
  have h (t : ℝ) : S.prediction (represent (t • pulled a s)) tag i = if s.flip i.2 then (S.prediction (represent (t • a)) tag' v)⁻¹
      else S.prediction (represent (t • a)) tag' v := by
    have he := S.prediction_channel hs s 0 (represent (t • a)) tag
    rw [hz, Work.F03.represent_pulled] at he; rw [he]
    simp only [pull,Step.read,v,sendEdge,tag',posDir,Step.rotate,Bool.false_xor]
  simp_rw [h] at he
  split <;> rename_i H
  · simp_rw [if_pos H,G.mat_inv] at he; rw [map_neg,← G.colorMat_skew]; exact he.unique hv.star
  simp_rw [if_neg H] at he; exact he.unique hv

section station
variable {H : Forest S.ratio} {B C : Bed} {U : Matrix (Body 1 f) (Body 1 c) ℝ}
def rising (H : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ) (x : Dir G c) := stretch H (x,relative (S:=S) H U x)

def solves (S : StepData c f) (B : Bed) (z : Dir G f) (v : Dir G c) := ∀ x : Dir G f,
    gaugeFiscal B x z + S.kernel.penalty * pairing (bills S x) (bills S z-v) = 0

lemma equation (hd : Inputs S U (B.metric.acts f) (C.metric.acts c)) (v : Dir G c) : solves S B (rising H U v) v := by
  intro x
  let z := rising H U v
  obtain ⟨he,hb⟩ := stationed H U _ _ hd
  have h (i : G.ColorIndex) : parts G 1 z i = _ := Work.F04.parts_stretch (S:=S) H U v i
  have hz i : parts G 1 (bills S z - v) i = -(S.kernel.penalty⁻¹ • (Precision.K (C.metric.acts c)*ᵥ parts G 1 v i)) := by
    change probe S *ᵥ (parts G 1 z i) - parts G 1 v i = _
    rw [h,mulVec_mulVec,he,sub_mulVec,one_mulVec,smul_mulVec]; abel
  change gaugeFiscal B _ z + _ * pairing _ (bills S z-v) = _
  unfold gaugeFiscal pairing; rw [mul_sum,← sum_add_distrib]; apply sum_eq_zero; intro i _
  rw [h,mulVec_mulVec,hb,← mulVec_mulVec,dotProduct_mulVec,vecMul_transpose,hz, dotProduct_neg,dotProduct_smul,
    smul_eq_mul, mul_neg,← mul_assoc _ S.kernel.penalty⁻¹, mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_mul]
  change dotProduct (parts G 1 (bills S x) i) _ + _ = _; exact add_neg_cancel _

lemma solved_unique {p η D} {v : Dir G c} {z w : Dir G f} (he : 0 < η) (hf : Floor B p f η D) (ha : solves S B z v) (hb : solves S B w v)
    (i : G.ColorIndex) : d 1 f *ᵥ parts G 1 z i = d 1 f *ᵥ parts G 1 w i := by
  refine sub_eq_zero.mp ?_; rw [← mulVec_sub]
  change d 1 f *ᵥ (parts G 1 (z-w) i) = 0; apply fiscal_kernel he hf _ i
  have hz := ha (z-w); have hw := hb (z-w)
  have hn := pair_nn (bills S (z-w))
  rw [bills_sub, pair_sub] at hn
  rw [pair_sub, bills_sub] at hz hw
  rw [fiscal_sub]; linarith [mul_nonneg S.kernel.penalty_pos.le hn]

lemma solved_signed (s : Signed) {v : Dir G c} {z : Dir G f} (hs : S.patch.Branches S.kernel G)
    (hb : Sworn B f G) (ha : solves S B z v) : solves S B (pulled z s) (pulled v s) := by
  intro x; obtain ⟨x,rfl⟩ := pulls_onto s x
  rw [hb,bills_signed s hs,bills_signed s hs,← pulls_sub,pair_signed]; exact ha x

lemma column_signed (hs : S.patch.Branches S.kernel G) {p η D} (he : 0 < η) (hf : Floor B p f η D) (hb : Sworn B f G)
    (hd : Inputs S U (B.metric.acts f) (C.metric.acts c)) (v : Dir G c) (s : Signed) (i : G.ColorIndex) :
    d 1 f *ᵥ parts G 1 (pulled (rising H U v) s) i = (d 1 f * U) *ᵥ parts G 1 (pulled v s) i := by
  rw [solved_unique he hf (solved_signed s hs hb (equation hd v)) (equation (H:=H) hd _), rising, Work.F04.parts_stretch, mulVec_mulVec]
  rw [extracted,Matrix.mul_add, ← Matrix.mul_assoc, Exterior.closed 0,Matrix.zero_mul,add_zero]
end station
end YM.Extra.Iteration.Channel
