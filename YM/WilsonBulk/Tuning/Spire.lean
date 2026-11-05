import YM.WilsonBulk.Tickets.Race
import YM.Push.LOOP_COEFFICIENT.ExteriorRules

/-!
# Unit transverse test for FULL summit. EXACT `μ` on link-origin coordinate
 y, - sign from Fourier second at 0. Acts with metric.read0 and independent
 of other metric parts/B labels and coupling schedule. Uses full hess impulse
 rather than separating plaquette cover paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Equiv Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open Work.F08 RG Stationary -- momentWeight wide
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {B : Bed} {V : Text (Cloth G) 2} {σ M : ℝ}

-- identity stencil price for actionKernel origin Q. On cover (cost units). Tic polynomial only.
abbrev resolver := Work.F08.unitRow Two
def turf0 := actionKernel resolver
def stakeLine (a : Axis) (x : Cover) := (x a : ℝ)*(x a:ℝ)
lemma line_degree (a : Axis) : DegLess 3 (stakeLine a) := by
  apply degLess_succ.mpr; intro i; apply degLess_succ.mpr; intro j; apply degLess_succ.mpr; intro k; rw [degLess_zero]; ext1 x; unfold MultiNext.SignedSource.Newt.jump stakeLine; simp only [Pi.add_apply, Pi.zero_apply]; push_cast; ring
lemma turnStalk {n : ℕ} (a : TypeFace n) (b : TypeFace (n+1)) (f : Cover→ℝ) : ∑' x, cobound n b a x*f x=∑ i:Axis,left ℝ n i b a*(f (step i)- f 0) := by
  rw [tsum_eq_sum (s:=Exterior.support)]; swap; · intro x hx; rw [certified n b a x hx,zero_mul]
  simp_rw [cobound,Finset.sum_mul,mul_sub,sub_mul ]; rw [sum_comm]; refine sum_congr rfl fun v _=>?_
  simp only [sum_sub_distrib,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,sum_ite_eq']; rw [if_pos (show (step v:Cover)∈ Exterior.support from mem_insert_of_mem (mem_image.mpr ⟨v, mem_univ v,rfl⟩)),if_pos (show (0:Cover)∈Exterior.support from mem_insert_self ..)]
  -- halt
lemma action_turf : turf0 = composeRows (transRows (cobound 1)) (cobound 1) := by
  have ht : Stamped (cobound 1) := Stamped.cobound _
  unfold turf0 actionKernel; congr 1
  obtain ⟨p,hp,h⟩:= ht.opposite.bound 0
  apply Next.Free.bank_injective (Row.rights _ _ (strip_compose (le_refl 0) h strip_unit) le_rfl) (Row.rights _ _ h le_rfl)
  intro x; rw [acts_compose (le_refl 0) h strip_unit]; simp only [ acts_unit,Matrix.mul_one]
lemma pitch (a : PotentialForm) (b : Two) (i : Axis) (x : Cover) : applied (cobound 1 b a) (stakeLine i) x = left ℝ 1 i b a*(2*(x i:ℝ)+1) := by
  unfold applied; rw [turnStalk,sum_eq_single i]; rotate_left
  · intro j _ hj; simp [stakeLine,Ne.symm hj]
  · simp
  simp [stakeLine]; ring_nf; simp
lemma jumpLaw (i j : Axis) (hj : i≠j) :
    (∑' x, turf0 (coord j) (coord j) x*stakeLine i x)= -2 := by
  let a := coord j; let F:=cobound 1
  have hp b (x:Cover) := (pitch a b i x) -- fix signature
  have he (t : Two) : (∑' y,F t a (-y) * applied (F t a) (stakeLine i) y) = -(2:ℝ) * (left ℝ 1 i t a*left ℝ 1 i t a) := by
    rw [← (Equiv.neg Cover).tsum_eq (fun x=> F t a (-x)*applied (F t a) (stakeLine i) x)]; simp only [Equiv.neg_apply,neg_neg]
    unfold F; simp_rw [hp t]; rw [turnStalk a t (fun x=> left ℝ 1 i t a*(2*((-x) i:ℝ)+1)),sum_eq_single i]; rotate_left
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    simp only [Pi.neg_apply,Int.cast_neg,step_apply,↓reduceIte,Pi.zero_apply,Int.cast_one,Int.cast_zero]; ring
  have ht j:= (Stamped.cobound 1).bound j; obtain ⟨M,hM,h⟩:= ht 1
  have hd b := width_routed zero_le_one (fun k:Cover=> (show size (id k) ≤ size k from le_rfl)) (strip_trans h a b) (fun _=>h b a)
  rw [action_turf]; simp_rw [composeRows, sum_mul]; rw [Summable.tsum_finsetSum (f:=fun b x=> routed id (transRows F a b) (fun _=> F b a) x * stakeLine i x) (fun b hb=> finite_pairing one_pos (hd b) (line_degree i).power)];
  have hy (b : Two) : (∑' x, routed id (transRows F a b) (fun _=> F b a) x * stakeLine i x) = -(2:ℝ) * (left ℝ 1 i b a*left ℝ 1 i b a):= (multiply_applied one_pos one_pos (strip_trans h a b) (h b a) (line_degree i).power).trans (he b)
  change ∑ b, ∑' x, routed id (transRows F a b) (fun _=> F b a) x * stakeLine i x =_; simp_rw [hy,← Finset.mul_sum]
  have hW := Push.Loops.diag_coaxis ℝ i a (Pi.single a 1); simp only [Matrix.mulVec_single_one] at hW
  rw [if_neg (show i∉ a.val from by simp [a,coord,hj]), Pi.single_eq_same] at hW; change -2 * _ = _; rw [show (∑ b:Two,left ℝ 1 i b a*left ℝ 1 i b a)= _ from hW, mul_one]
end YM.WilsonBulk.Parapet
