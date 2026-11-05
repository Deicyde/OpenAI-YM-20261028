import YM.FullVolume.Ray.Weight
import Mathlib.LinearAlgebra.Lagrange
/-! Width polynomial-price devices. Lagrange at *outer* real probing knots, avoids high power of the actual width radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Polynomial Finset
open scoped Topology BigOperators NNReal ContDiff Polynomial
variable {k i n:ℕ}
def ink (k:ℕ) (f:ℝ → ℝ) := ∃ P: Polynomial ℝ, P.natDegree≤k ∧ ∀ t,f t=P.eval t
namespace ink
variable {a b:ℝ}{f g:ℝ→ℝ}
lemma rise (h:ink i f) (ht:i≤k):ink k f:=⟨h.choose,h.choose_spec.1.trans ht,h.choose_spec.2⟩
lemma termC (c:ℝ): ink k (fun _=> c):=⟨C c,by simp,by simp⟩
lemma straight (a b:ℝ):ink 1 (fun x=>a+b*x):= by
  refine ⟨C a+C b*X, natDegree_add_le_of_degree_le ?_ ?_,?_⟩ -- naming
  · simp
  · exact (natDegree_mul_le).trans (by simp)
  simp
lemma abreast (h : ink k f) (hz:ink k g):ink k (fun x=>f x+g x):=by
  obtain ⟨F,hF,h⟩:=h; obtain ⟨G,hG,he⟩:=hz
  exact ⟨F+G,natDegree_add_le _ _ |>.trans (max_le hF hG),fun x=> by dsimp only; rw [he,h,eval_add]⟩
lemma docket (h:ink k f) (hv:ink i g): ink (k+i) (fun x=>f x*g x):=by
  obtain ⟨F,hF,h⟩:=h; obtain ⟨G,hG,hh⟩:=hv; exact ⟨F*G,natDegree_mul_le.trans (Nat.add_le_add hF hG),fun x=>by dsimp only; rw [h,hh,eval_mul]⟩
lemma scale (c:ℝ) (h:ink k f): ink k (fun x=> c*f x):=by simpa using (termC (k:=0) c).docket h
lemma collection {ι : Type*} (S : Finset ι) (f:ι→ℝ→ℝ) (h:∀ i∈S,ink k (f i)): ink k (fun x=> ∑ i∈S,f i x):= by
  classical induction S using Finset.induction_on with
  | empty => simpa using (termC (k:=k) 0)
  | insert j s hj ih => simp_rw [sum_insert hj]; exact (h _ (mem_insert_self ..)).abreast (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma shift (h:ink k f) (a:ℝ):ink k (fun x=>f (a*x)):=by
  obtain ⟨F,hF,h⟩:= h
  exact ⟨F.comp (C a *X), natDegree_comp_le.trans ((Nat.mul_le_mul hF (show (C a*X).natDegree≤1 from natDegree_mul_le.trans (by simp))).trans_eq (mul_one _)),fun x=>by simp [h]⟩
-- norm flight for any query at cost view `zeta/R`. basis maximum independent R
private def total (p:Polynomial ℝ):ℝ:=∑ k∈ range (p.natDegree+1),‖p.coeff k‖
private lemma gallery (p:Polynomial ℝ) {R:ℝ} (hr:1≤R): Scout R (fun t=>p.eval (t/R)) (total p):=by
  have hR:=zero_lt_one.trans_le hr
  have hf:Scout R (fun t:ℝ=> t/R) 1:=by
    have hh:= (Scout.line hr).scale R⁻¹; unfold id at hh
    rw [norm_inv,Real.norm_of_nonneg hR.le,inv_mul_cancel₀ hR.ne'] at hh; exact hh.replace (fun i _=> by change R⁻¹*i=_; rw [mul_comm,(div_eq_mul_inv i R)])
  let f(k:ℕ) (t:ℝ):=p.coeff k*(t/R)^k
  have hz(k:ℕ):Scout R (f k) ‖p.coeff k‖:=by
    have ht:= (hf.power k).scale (p.coeff k); simp_rw [one_pow,mul_one] at ht; exact ht
  exact (Scout.pieces _ f _ hr (fun k _=> hz k)).replace (fun t ht=> Eq.symm (eval_eq_sum_range' (lt_add_one _) _))
variable {m : ℕ} (r:Fin (m+1) →ℝ)
abbrev lamp (i:Fin (m+1)) (t:ℝ) := (Lagrange.basis univ r i).eval t
def prices (i:Fin (m+1)):= total (Lagrange.basis univ r i)
def pay:=∑ i,prices r i
lemma price_pos (i:Fin (m+1)):0≤ prices r i := by unfold prices total; exact sum_nonneg fun _ _=> norm_nonneg _
lemma pay_pos : 0≤ pay r:=sum_nonneg fun i _=> price_pos r i
lemma vitals (i : Fin (m+1)) {R} (hr:1 ≤ R): Scout R (fun t=>lamp r i (t/R)) (prices r i) := gallery _ hr
lemma tour (h: ink m f) (he: Injective r) (a:ℝ): f a=∑ i,f (r i)*lamp r i a:=by
  obtain ⟨P,hp,h⟩:=h; simp_rw [h]
  have ht:P.degree < ↑(Finset.univ (α:=Fin (m+1))).card:= by
    apply lt_of_le_of_lt (degree_le_natDegree) (WithBot.coe_lt_coe.mpr _); simpa [Nat.lt_succ_iff] using hp -- nat coercion
  conv => lhs; rw [Lagrange.eq_interpolate he.injOn ht, Lagrange.interpolate_apply]
  rw [eval_finsetSum]; apply sum_congr rfl; simp [lamp]
lemma token (h:ink m f) (he: Injective r) {a} (ha : 0<a) (t:ℝ): f t=∑ i,f (a*r i)*lamp r i (t/a):=by
  have hh:= tour r (shift h a) he (t/a); rwa [show a*(t/a)=t from by field_simp] at hh -- reduce
end ink
end YM.FullVolume.Ray
