import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.Regular
import YM.Next.FOUNDATIONS.SU2
import YM.Next.MULTISOURCE.Germs
import YM.Next.SCHEDULE.Blocks


/-!
# Ordered left derivative calculus for the real finite Gaussian tables

All fixed geometry, unmasked germ/equality at U, including for higher
jets, not differentiation of a global threshold decision.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson RG Precision Multi.Puff
open Next.Foundations (left_has leftDerivs_chart)
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {c : Side} {G : Gauge} {I : Type*} [Fintype I] [DecidableEq I]
abbrev Field (G : Gauge) (c : Side) (I : Type*) := Config G c → Table I
abbrev Word (G : Gauge) (c : Side) := List (Directions G c)

def jet (l : Word G c) (A : Field G c I) (U : Config G c) := Matrix.of fun i j => leftDerivs (fun V => A V i j) l U
def Good (A : Field G c I) (k : ℕ) (U : Config G c) := ∀ i j, ContDiffAt ℝ (k:WithTop ℕ∞) (fun y => A (increment U y) i j) 0
variable {l : Word G c} {A B : Field G c I} {U : Config G c} {m k : ℕ}
lemma Good.const (M : Table I) : Good (fun _=> M) k U := fun _ _=> contDiffAt_const
lemma Good.lower (h : Good A k U) (hm : m≤k) : Good A m U := fun i j => (h i j).of_le (by exact_mod_cast hm)
lemma Good.plus (h : Good A k U) (hb : Good B k U) : Good (fun V => A V+B V) k U := fun i j => (h i j).add (hb i j)
lemma Good.minus (h : Good A k U) (hb : Good B k U) : Good (fun V => A V-B V) k U := fun i j => (h i j).sub (hb i j)
lemma Good.neg (h : Good A k U) : Good (fun V => -A V) k U := fun i j => (h i j).neg
lemma Good.scale (x : ℝ) (h : Good A k U) : Good (fun V => x • A V) k U := fun i j => (h i j).const_smul x
lemma Good.prod (h : Good A k U) (hb : Good B k U) : Good (fun V => A V*B V) k U := fun i j => ContDiffAt.sum (fun l (_:l∈Finset.univ)=> (h i l).mul (hb l j))
lemma Good.transpose (h : Good A k U) : Good (fun V => (A V).transpose) k U := fun i j => h j i
lemma Good.restrict {X : Type*} (e : X → I) (h : Good A k U) : Good (fun V => (A V).submatrix e e) k U := fun i j => h (e i) (e j)
lemma Good.entry (h : Good A k U) (i j : I) : Crest k (fun V => A V i j) U := into _ _ (h i j)
lemma Good.near (h : Good A k U) : ∀ᶠ V in 𝓝 U, Good A k V :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => ((h.entry i j).near).mono fun _ he => he.germ
lemma Good.jet (h : Good A k U) (he : l.length+m≤k) : Good (jet l A) m U := by intro i j; exact leftDerivs_chart l m ((h.lower he) i j)
lemma Good.det (h : Good A k U) : ContDiffAt ℝ (k:WithTop ℕ∞) (fun y => (A (increment U y)).det) 0 := by
  simp only [Matrix.det_apply,Units.smul_def, zsmul_eq_mul]; refine ContDiffAt.sum (fun σ _ => contDiffAt_const.mul (contDiffAt_prod (fun i _=> h _ i)))
lemma Good.adj (h : Good A k U) : Good (fun V => (A V).adjugate) k U := by
  intro i j; simp only [Matrix.adjugate_apply]
  refine Good.det (A:=fun V=>(A V).updateRow j (Pi.single i 1)) (fun m n=>?_); by_cases hm : m=j
  · simp only [Matrix.updateRow_apply,hm, if_true]; exact contDiffAt_const
  simp only [Matrix.updateRow_apply,if_neg hm]; exact h _ _
lemma Good.inv (h : Good A k U) (hv : IsUnit (A U)) : Good (fun V => (A V)⁻¹) k U := by
  intro i j; simp only [Matrix.inv_def,Ring.inverse_eq_inv', Matrix.smul_apply,smul_eq_mul]; refine (h.det.inv ?_).mul (h.adj i j)
  rw [inc_zero]; exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hv)
lemma Good.near_regular (h : Good A k U) (he : IsUnit (A U)) : ∀ᶠ V in 𝓝 U, IsUnit (A V) := by
  obtain ⟨g,hg,H⟩ := into (G:=G) (k:=k) (fun V=>(A V).det) h.det
  have ht : ContinuousAt (fun V=>(A V).det) U := (hg.continuousAt.comp visible.continuousAt).congr H.symm
  exact (ht.eventually_ne (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp he))).mono fun i hi=> (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hi)
lemma Good.pow (h : Good A k U) (d : ℕ) : Good (fun V => (A V)^d) k U := by
  induction d with | zero => simpa only [pow_zero] using! Good.const (1:Table I) | succ d ih => simpa only [pow_succ] using ih.prod h

lemma jet_nil : jet ([] : Word G c) A U=A U := rfl
lemma jet_const (M : Table I) : jet l (fun _ => M) U = if l=[] then M else 0 := by
  ext; rw [jet,Matrix.of_apply,Work.G07.left_const]; split <;> rfl
lemma jet_cons (d : Directions G c) (i j : I) : jet (d::l) A U i j = deriv (fun t : ℝ => jet l A (increment U (t • d)) i j) 0 := rfl
lemma iter {t : Word G c} : jet l (jet t A) U = jet (l++t) A U := by ext; simp only [jet,of_apply,Work.G07.left_append]
lemma Good.has (h : Good A k U) (he : l.length < k) (d : Directions G c) (i j : I) :
    HasDerivAt (fun t : ℝ => Jets.jet l A (increment U (t • d)) i j) (Jets.jet (d::l) A U i j) 0 := left_has (f:=fun v=>A v i j) d he (h i j)
lemma jet_plus (ha : Good A k U) (hb : Good B k U) (he : l.length≤k) : jet l (fun V => A V+B V) U = jet l A U+jet l B U := by
  ext i j; exact Crest.sum_at l he U (ha.entry i j) (hb.entry i j)
lemma jet_scale (x : ℝ) : jet l (fun V => x • A V) U = x • jet l A U := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih => ext i j; simp_rw [jet_cons, ih,Matrix.smul_apply,smul_eq_mul, deriv_const_mul_field]; rfl
lemma jet_neg : jet l (fun V => -A V) U = - jet l A U := by simpa only [neg_one_smul] using jet_scale (l:=l) (A:=A) (U:=U) (-1)
lemma jet_minus (ha : Good A k U) (hb : Good B k U) (he : l.length≤k) : jet l (fun V => A V-B V) U = jet l A U-jet l B U := by simp_rw [sub_eq_add_neg, jet_plus ha hb.neg he, jet_neg]
lemma jet_eq (h : A =ᶠ[𝓝 U] B) : jet l A U=jet l B U := by
  induction l generalizing U with
  | nil => exact h.eq_of_nhds
  | cons a l ih =>
    ext i j; apply EventuallyEq.deriv_eq
    filter_upwards [(Multi.Puff.swing U a).eventually (eventually_eventually_nhds.mpr h)] with t ht using congr_fun (congr_fun (ih ht) _) _
lemma jet_entry_eq (i j : I) {b : ℝ} (h : ∀ᶠ V in 𝓝 U,A V i j=b) : jet l A U i j = if l=[] then b else 0 := by
  let f (W : Config G c) := Matrix.of fun (_ _: I) => A W i j
  let g := Matrix.of fun (_ _: I) => b
  have ht := jet_eq (l:=l) (h.mono fun v hv=> show f v = (fun _=>g) v from Matrix.ext (fun _ _=>hv))
  rw [jet_const] at ht; change jet l f U i j=_; rw [ht]; split <;> rfl

def share : Word G c → (Word G c → Word G c → Table I) → Table I
  | [], f => f [] []
  | d::l,f => share l (fun b t => f (d::b) t + f b (d::t))
lemma share_has (l : Word G c) (f : ℝ → Word G c → Word G c → Table I) (z : Word G c → Word G c → Table I) (i j : I)
    (h : ∀ b t, b.length+t.length=l.length → HasDerivAt (fun x => f x b t i j) (z b t i j) 0) :
    HasDerivAt (fun x => share l (f x) i j) (share l z i j) 0 := by induction l generalizing f z with
      | nil => exact h [] [] rfl
      | cons a l ih => exact ih _ _ (fun b t hb => (h (a::b) t (by simp; omega)).add (h b (a::t) (by simp; omega)))

lemma jet_prod (ha : Good A k U) (hb : Good B k U) (he : l.length≤k) :
    jet l (fun V => A V*B V) U = share l (fun b t => jet b A U * jet t B U) := by
  induction l generalizing U with
  | nil => rfl
  | cons d l ih =>
    ext i j; rw [jet_cons,share]
    have ht := (Multi.Puff.swing U d).eventually (ha.near.and hb.near)
    apply HasDerivAt.deriv
    refine (share_has (G:=G) l (fun x b t => jet b A (increment U (x • d)) * jet t B (increment U (x • d))) _ i j ?_).congr_of_eventuallyEq
      (ht.mono fun x ⟨h1,h2⟩ => congr_fun (congr_fun (ih h1 h2 (by simpa only [List.length_cons] using Nat.le_of_succ_le he)) i) j)
    intro b t ht
    have heq := HasDerivAt.fun_sum (u:=Finset.univ) (fun m _=> (ha.has (l:=b) (by simp at he; omega) d i m).mul (hb.has (l:=t) (by simp at he; omega) d m j))
    rw [zero_smul,inc_zero] at heq
    simpa only [Matrix.add_apply, Matrix.mul_apply,Finset.sum_add_distrib] using! heq
lemma inv_one (ha : Good A 1 U) (hu : IsUnit (A U)) (d : Directions G c) :
    let B := (A U)⁻¹; jet [d] (fun V => (A V)⁻¹) U = - (B * jet [d] A U * B) := by
  intro B
  have hh := jet_prod (ha.inv hu) ha (show [d].length ≤ 1 from le_rfl)
  rw [jet_eq (ha.near_regular hu |>.mono fun i hi => Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hi) : (fun V => (A V)⁻¹ * A V)=ᶠ[𝓝 U] (fun _=>1)),jet_const, if_neg (by simp), share,share] at hh
  change 0 = jet [d] (fun V => (A V)⁻¹) U * A U + B * jet [d] A U at hh
  have ht := congr_arg (fun M => M*B) hh
  rw [Matrix.add_mul,Matrix.mul_assoc _ (A U), Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), mul_one,zero_mul] at ht
  exact eq_neg_of_add_eq_zero_left ht.symm

lemma jet_inverse (ha : Good A 1 U) (hu : IsUnit (A U)) (d : Directions G c) :
    jet (l++[d]) (fun V => (A V)⁻¹) U = - jet l (fun V => (A V)⁻¹ * jet [d] A V * (A V)⁻¹) U := by
  rw [← iter, jet_eq ((ha.near.and (ha.near_regular hu)).mono fun i ⟨hi,hv⟩ => inv_one hi hv d :
      jet [d] (fun V => (A V)⁻¹) =ᶠ[𝓝 U] (fun V => - ((A V)⁻¹ * jet [d] A V * (A V)⁻¹))), jet_neg]
end YM.Further.CurvedGaussianJets.Jets
