import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lac
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tablet

/-!
# Local inverse jets, including varying sector data.

Finite jets derived pointwise from price of A⁻¹ (real Combes). No need to
 assume a bound across an unmasked region from the matrix Price at base.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c : Side} {E ι κ ν : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush
variable {v z f g : ℝ} {k : ℕ}
variable [Fintype ι] [Fintype κ] {x : E} {a : ι → Site c} {b : κ → Site c} {d : ν → Site c} {η γ : ℝ}
variable [DecidableEq ι] {A B : E → Matrix ι ι ℝ}

lemma determinant {k : WithTop ℕ∞} (h : ∀ i j, ContDiffAt ℝ k (fun x=> A x i j) x) : ContDiffAt ℝ k (fun x=> (A x).det) x := by
  simp_rw [Matrix.det_apply]; exact ContDiffAt.sum fun s _=> (contDiffAt_prod fun i _=>h ..).const_smul _
lemma jetBack {k : WithTop ℕ∞} (h : ∀ i j,ContDiffAt ℝ k (fun x=> A x i j) x) (he : IsUnit (A x).det) (i j) :
    ContDiffAt ℝ k (fun x => ((A x)⁻¹) i j) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,adjugate_apply]
  refine ((determinant h).inv he.ne_zero).mul (determinant ?_)
  intro u v
  by_cases hg : u=j
  · simp_rw [hg,updateRow_self]; exact contDiffAt_const
  simp_rw [updateRow_ne hg]; exact h ..

-- Vanishing remainder from F⁻¹ jets at base. Keep no derivative across germ boundaries.
def Bud (k n : ℕ) (f : E→ℝ) (x : E) := ContDiffAt ℝ (↑k) f x ∧ ∀ j : ℕ, j ≤ k → j<n → normJ j f x=0
lemma Bud.shoot {i j k : ℕ} {f g : E→ℝ} (p : Bud k i f x) (q : Bud k j g x) : Bud k (i+j) (fun x=> f x*g x) x := by
  have h := p.1.mul q.1; refine ⟨h, fun l hl ht=>?_⟩
  obtain ⟨s,hs,hx,-,hf⟩:= opens k p.1 Set.univ univ_mem
  obtain ⟨t,he,hX,ht',hg⟩:= opens k q.1 s (hs.mem_nhds hx)
  unfold normJ; rw [← iteratedFDerivWithin_eq_iteratedFDeriv he.uniqueDiffOn (h.of_le (Nat.cast_le.mpr hl)) hX]
  refine le_antisymm ((norm_iteratedFDerivWithin_mul_le (hf.mono ht') hg he.uniqueDiffOn hX (Nat.cast_le.mpr hl)).trans_eq (Finset.sum_eq_zero fun n hn=>?_ ))
    (norm_nonneg _)
  rw [mem_range] at hn
  rw [iteratedFDerivWithin_eq_iteratedFDeriv he.uniqueDiffOn (p.1.of_le (show (↑n:WithTop ℕ∞) ≤ (↑k) from Nat.cast_le.mpr (by omega))) hX,
    iteratedFDerivWithin_eq_iteratedFDeriv he.uniqueDiffOn (q.1.of_le (show (↑(l-n):WithTop ℕ∞) ≤ (↑k) from Nat.cast_le.mpr (by omega))) hX]
  change _*normJ n f x * normJ (l-n) g x=0; by_cases hm : n < i
  · rw [p.2 n (by omega) hm, mul_zero, zero_mul]
  rw [q.2 _ (by omega) (by omega),mul_zero]
lemma Bud.scores {k' i j : ℕ} (p : ∀ k l, Bud k' i (fun x=> A x k l) x)
    (q : ∀ k l,Bud k' j (fun x=>B x k l) x) k l : Bud k' (i+j) (fun x=>(A x*B x) k l) x := by
  have he {f g : E→ℝ} (h : Bud k' (i+j) f x) (p : Bud k' (i+j) g x) : Bud k' (i+j) (fun x=> f x+g x) x := by
    refine ⟨h.1.add p.1,fun j hp hj=>?_⟩
    change ‖iteratedFDeriv ℝ j (f+g) x‖=0
    rw [iteratedFDeriv_add_apply (h.1.of_le (Nat.cast_le.mpr hp)) (p.1.of_le (Nat.cast_le.mpr hp))]
    rw [norm_eq_zero.mp (h.2 j hp hj),norm_eq_zero.mp (p.2 j hp hj),add_zero,norm_zero]
  have ht (s : Finset ι) : Bud k' (i+j) (fun x=>∑ z∈s,A x k z*B x z l) x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [sum_empty]; have h:=Brush.certified (k:=k') (x:=x) zero_le_one (0:ℝ)
      refine ⟨h.1,fun i hi _=> le_antisymm ?_ (norm_nonneg _)⟩; simpa only [norm_zero,zero_mul] using! h.order _ hi
    | insert i s hi hh => simp_rw [sum_insert hi]; exact he ((p ..).shoot (q ..)) hh
  simp_rw [Matrix.mul_apply]; exact ht Finset.univ

lemma melts (p : Tablet k η f v A a a x) (h : A x=0) (j : ℕ) (i l : ι) : Bud k j (fun x=> (A x^j) i l) x := by
  induction j generalizing i l with
  | zero => simp only [pow_zero]; exact ⟨contDiffAt_const,fun i _ hi=> by omega⟩
  | succ j ih => simp_rw [pow_succ]; exact Bud.scores (A:=fun x=> A x^j) ih (j:=1) (B:=A)
                            (fun i j=> ⟨(p.singular i j).smooth,fun k hk hh=>by
                              have hp : k=0 := by omega
                              unfold normJ; subst k; simp only [norm_iteratedFDeriv_zero,h]; simp⟩) ..

namespace Tablet
-- grows k+book poly. -/
def token (j : ℕ) (f g : ℝ) := ∑ i∈range (j+1), (f*g+1)^i*g

def driftP (j : ℕ) (v : ℝ) := j*v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma call (A : E → Matrix ι ι ℝ) (x H : E) (k : ℕ) (h : IsUnit (A x).det) (_p : IsUnit (A H).det) :
    let F:=(A H)⁻¹; let V:=1-F*A x
    (A x)⁻¹=(∑ i∈range (k+1),V^i*F)+(V^(k+1)*(A x)⁻¹) := by
  intro F V
  have hf : F=(1-V)*(A x)⁻¹ := by unfold V; rw [sub_sub_cancel,mul_assoc,Matrix.mul_nonsing_inv _ h,mul_one]
  conv_rhs => arg 1; rw [hf]
  simp_rw [← mul_assoc,← Finset.sum_mul]; rw [← add_mul, _root_.geom_sum_mul_neg,sub_add_cancel,one_mul]

lemma inverter (p : Tablet k η f v A a a x) (h : IsUnit (A x).det) (hk : Price a a (A x)⁻¹ η g) (hg : 0≤g) :
    Tablet k η (token k f g) (driftP k v) (fun x=> (A x)⁻¹) a a x := by
  let F : E→Matrix ι ι ℝ := fun _=> (A x)⁻¹
  let V:= (1: E→Matrix ι ι ℝ) + -(F*A)
  let W:= (fun x=> (A x)⁻¹)
  have hF := Tablet.fixed (x:=x) (k:=k) (A x)⁻¹ hk p.scale hg (le_rfl : 0 ≤ (0:ℝ))
  have hV : Tablet k η (f*g+1) v V a a x := by
    have hx : Tablet k η (g*f) (0+v) (-(F*A)) a a x := (hF.enjoin p).mirror
    rw [zero_add] at hx
    convert (Tablet.fixed (1:Matrix ..) (one_pay a _) p.scale zero_le_one p.pos).joined hx using 1 <;> first | rfl | ring
  have hx : V x=0 := by change (1:Matrix ..)+ -(F x*A x)=_; rw [show F x*A x=_ from Matrix.nonsing_inv_mul _ h,add_neg_cancel]
  let g' (j) := (f*g+1)^j*g
  let b := driftP k v; have ht : 0≤ b := mul_nonneg (Nat.cast_nonneg _) p.pos
  let D j (x:E) := (V x)^j*F x
  have hh (i) (hi:i∈range (k+1)) : Tablet k η (g' i) b (D i) a a x := by
    have he := (hV.tall i).enjoin hF; rw [add_zero] at he
    convert! he.tilt (le_refl _) (mul_le_mul_of_nonneg_right (show (i:ℝ)≤(k:ℝ) from by
      rw [mem_range] at hi; exact_mod_cast Nat.le_of_lt_succ hi) p.pos) p.scale le_rfl using 1
  have he (s : Finset ℕ) (h : s⊆range (k+1)) : Tablet k η (∑ i∈s,g' i) b (∑ i∈s,D i) a a x := by
    induction s using Finset.induction_on with
    | empty => simp only [sum_empty]; exact fixed 0 (⟨fun _=> by simp, fun _=>by simp⟩ : Price a a _ _ _) p.scale le_rfl ht
    | insert i s hi hs => rw [sum_insert hi,sum_insert hi]; exact (hh _ (h (mem_insert_self ..))).joined (hs (insert_subset_iff.mp h).2)
  let K : E→Matrix ι ι ℝ := fun x=> V x^(k+1)*W x
  have hv i j : Brush k 0 b (fun y=>K y i j) x := by
    have he := Bud.scores (k':=k) (A:=fun x=> V x^(k+1)) (B:=W) (melts hV hx (k+1)) (j:=0) (fun i j=> ⟨jetBack
      (fun i j=> (p.singular i j).smooth) h _ _, fun i _ hi=>by omega⟩) i j
    refine ⟨he.1, ht, fun i hi=>?_⟩; rw [zero_mul]; exact (he.2 i hi (by omega)).le
  apply ((he (range (k+1)) (Finset.Subset.refl _)).rests hv).merges
  have hg' : ∀ᶠ i in 𝓝 x, (A i).det≠0 := (determinant (fun i j=> (p.singular i j).smooth)).continuousAt.eventually_ne h.ne_zero
  filter_upwards [hg'] with z hz
  rw [call A z x k (IsUnit.mk0 _ hz) h]; simp only [Pi.add_apply,Finset.sum_apply,D]
  rfl
end Tablet
end YM.ConnectedActivityE6.Blaze
