import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Charges
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Meter
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Voyage

/-!
# Per true path forms (capacity L² usable by a single rough direction)
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n l : Side} {ι : Type*} [DecidableEq ι]
variable {P : Purse ι (Site n)} {η : ℝ}
open Purse

omit [DecidableEq ι] in
def Linkbill (l : Side) (P : Purse ι (Site n)) (d : ι→Dir G n) := ∀ (i : ι) (j : TypeFace 1), P.Pays {i} (fun x => d i (x,j)) (l.val:ℝ)⁻¹

namespace Logfee
omit [DecidableEq ι] in
lemma stroke {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 ≤ η) (i : ι) (e : Step) :
    P.Pays {i} (width (d i) e) (guide l η 1*(l.val:ℝ)⁻¹) := by
  rcases e with ⟨a,x|x⟩
  · rw [show width (d i) ⟨a,false⟩=fun x => ‖d i (x,coord a)‖ from funext fun _ => rfl]
    exact ((h i (coord a)).under (g:=fun x => ‖d i (x,coord a)‖) (fun _ => by simp)).mono (le_mul_of_one_le_left (by positivity)
      (Real.one_le_exp (by positivity)))
  rw [show width (d i) ⟨a,true⟩=fun x => ‖d i (x-step a,coord a)‖ from funext fun _ => rfl]
  have ht := h i (coord a)
  let F := Equiv.addRight (-step a:Site n)
  have hh (x : Site n) : separation x (F x) ≤ 1 := (Response.by_one x (negDir a)).1
  have hk := shifting P he hp ht 1 F hh; rw [Finset.card_singleton,pow_one] at hk
  exact hk.under (fun x => by change ‖‖d i (_,_)‖‖ ≤ ‖d i (_+ -_,_)‖; simp [sub_eq_add_neg])
omit [DecidableEq ι] in
lemma travel_bill {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 ≤ η) (i : ι) (w : Walk) :
    P.Pays {i} (weight (d i) w) ((w.length:ℝ)/l.val*guide l η w.length) := by
  induction w with
  | nil => simpa only [show weight (d i) []=(0:Site n→ℝ) from rfl,List.length_nil,Nat.cast_zero,zero_div,zero_mul] using (Pays.zero (C:=0) (P:=P) (S:={i}) le_rfl : P.Pays {i} (0 : Site n → ℝ) 0)
  | cons e w ih =>
    let F := Equiv.addRight (e.vec:Site n)
    have ht := shifting P he hp ih 1 F (fun i => (Response.by_one i e).1); rw [Finset.card_singleton,pow_one] at ht
    apply ((stroke h he hp i e).plus ht).mono
    let x := guide l η 1; let z := guide l η w.length
    have hx : 0 ≤ x := (guide_pos ..).le
    have hz : 1≤z := Real.one_le_exp (by positivity)
    rw [List.length_cons,Nat.cast_add,succ_guide l w.length,Nat.cast_one,add_div,add_mul]
    change x*(l.val:ℝ)⁻¹+x*(_/l.val*z) ≤ w.length/(l.val:ℝ)*(z*x)+_*(z*x)
    rw [show x*(w.length/(l.val:ℝ)*z)=w.length/(l.val:ℝ)*(z*x) from by ring, add_comm _ (_*(_*x))]
    apply add_le_add le_rfl _
    exact (le_mul_of_one_le_left (mul_nonneg hx (by positivity : 0 ≤ (l.val:ℝ)⁻¹)) hz).trans_eq (by ring)

def basicPay (G : Gauge) (l : Side) (η : ℝ) (m k r : ℕ) := (unitPrice G m).C^k * ((r:ℝ)/(l.val:ℝ)*guide l η r)^k
lemma insured {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 ≤ η) (S : Finset ι) (w : Walk)
    (m : ℕ) (hv : S.card ≤ m) (x : Dir G n) (hx : ‖x‖ ≤ 1) : P.Jets S d (transport w) x (ample G*basicPay G l η m S.card w.length) := by
  have ht := Pays.prod (fun i => weight (d i) w) _ S (fun i _ => travel_bill h he hp i w)
  have hy : 0 ≤ (unitPrice G m).C := zero_le_one.trans (unitPrice G m).used
  simp only [Finset.prod_const] at ht
  rw [basicPay,← mul_assoc]
  exact ht.repay (mul_nonneg (ample_pos G).le (by positivity)) fun i =>
    (ticket _ _ _ m w S hv hx).trans_eq (by rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => weight_nonneg ..),mul_assoc])

def tollBound (G : Gauge) (η : ℝ) (m : ℕ) := ample G * ((unitPrice G m).C * max 1 η⁻¹)^m
lemma tollBound_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0 < tollBound G η m := mul_pos (ample_pos _) (pow_pos
    (mul_pos (zero_lt_one.trans_le (unitPrice G m).used) (lt_of_lt_of_le one_pos (le_max_left ..))) _)
lemma speed (hp : 0 < η) (r : ℕ) : (r:ℝ)/(l.val:ℝ) ≤ max 1 η⁻¹*guide l η r := by
  apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (guide_pos l η r).le)
  rw [inv_mul_eq_div]; apply (le_div_iff₀ hp).mpr; unfold guide
  apply le_trans _ (Real.add_one_le_exp _); ring_nf; simp
lemma guide_ge (l : Side) (r : ℕ) (η : ℝ) (he : 0 ≤ η) : 1 ≤ guide l η r := Real.one_le_exp (by positivity)


lemma book {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 < η) (w : Walk) (S : Finset ι)
    (m : ℕ) (hv : S.card ≤ m) (x : Dir G n) (hx : ‖x‖ ≤ 1) : P.Jets S d (transport w) x (tollBound G η m * guide l (2*m*η) w.length) := by
  apply (insured h he hp.le S w m hv x hx).mono
  let r := w.length; let y := guide l η r; let k := (unitPrice G m).C; let z := max 1 η⁻¹
  have h1 : 1≤ k := (unitPrice G m).used; have h2 : 1≤z := le_max_left ..; have h3 : 1≤y := guide_ge l r _ hp.le
  have hy : 1 ≤ y*y := one_le_mul_of_one_le_of_one_le h3 h3
  have hh : 1 ≤ k*z := one_le_mul_of_one_le_of_one_le h1 h2
  have hm : (y*y)^m=guide l (2*m*η) r := by
    unfold guide y guide; rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring
  unfold tollBound
  rw [mul_assoc (ample G)]; apply mul_le_mul_of_nonneg_left _ (ample_pos G).le; unfold basicPay
  change k^S.card*((r:ℝ)/l.val*y)^S.card ≤ (k*z)^m*guide l _ r
  rw [← hm,← mul_pow, ← mul_pow]
  refine le_trans (pow_le_pow_left₀ ?_ ?_ S.card) (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hh hy) hv)
  · have H := zero_le_one.trans h1; have h := zero_le_one.trans h3; positivity
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (speed hp r) (zero_le_one.trans h3)) (zero_le_one.trans h1)).trans_eq (show k*(z*y*y)=_ from by ring)
end Logfee
end YM.AnalyticNext.QuarticMatch.Estimate
