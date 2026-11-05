import YM.Distribution.Tests
import YM.Mink.Poincare
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Smearing products AND joint Schwartz topology

Type adapts the spacelike pair support convention, not ordered Euclidean tests.
Product words suffice at common invariant domain, but their correlation functionals
are *joint* distributions. No tensor density assumption used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open MeasureTheory Filter Complex Function Set
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace Probe
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev size (n k : ℕ) (f : Probe U) := SchwartzMap.seminorm ℂ n k f

def term (n k : ℕ) (f : Probe U) (g : Probe V) :=
  ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ) * (size n i f * size 0 (k-i) g + size 0 i f * size n (k-i) g)

@[fun_prop] lemma cont_size (k n : ℕ) : Continuous (fun f : Probe U => size k n f) :=
  (schwartz_withSeminorms ℂ U ℂ).continuous_seminorm (k,n)

lemma term_nonneg (n k : ℕ) (f : Probe U) (g : Probe V) : 0 ≤ term n k f g := by unfold term size; positivity
lemma term_zero (n k : ℕ) (f : Probe U) : term n k f (0 : Probe V) = 0 := by simp [term,size]
lemma zero_term (n k : ℕ) (g : Probe V) : term n k (0 : Probe U) g = 0 := by simp [term,size]
lemma term_cont (n k : ℕ) : Continuous fun p : Probe U × Probe V => term n k p.1 p.2 := by
  unfold term
  apply continuous_finsetSum; intro i _
  apply continuous_const.mul; apply Continuous.add
  · exact ((cont_size ..).comp continuous_fst).mul ((cont_size ..).comp continuous_snd)
  exact ((cont_size ..).comp continuous_fst).mul ((cont_size ..).comp continuous_snd)

theorem via (L : V →L[ℝ] U) (h : ‖L‖ ≤ 1) (f : Probe U) (x : V) (n k : ℕ) :
    ‖L x‖^n * ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ size n k f := by
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) x (i := k) (by exact_mod_cast le_top)]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (SchwartzMap.le_seminorm ℂ n k f (L x))
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) h

lemma extent_bound (f : Probe U) (g : Probe V) (n k : ℕ) (x : U × V) :
    ‖x‖^n * ‖iteratedFDeriv ℝ k (fun a : U × V => f a.1 * g a.2) x‖ ≤ term n k f g := by
  let F := f ∘ (↑(ContinuousLinearMap.fst ℝ U V) : U × V → U)
  let G := g ∘ (↑(ContinuousLinearMap.snd ℝ U V) : U × V → V)
  have hf : ContDiff ℝ ∞ F := (f.smooth ⊤).comp (ContinuousLinearMap.fst ℝ U V).contDiff
  have hg : ContDiff ℝ ∞ G := (g.smooth ⊤).comp (ContinuousLinearMap.snd ℝ U V).contDiff
  apply le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hf hg x (n := k) (by exact_mod_cast le_top)) (by positivity))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  let A := ‖iteratedFDeriv ℝ i F x‖
  let B := ‖iteratedFDeriv ℝ (k-i) G x‖
  have ht (y) : ‖x.1‖ ^ y*A ≤ size y i f := via _ (ContinuousLinearMap.norm_fst_le ℝ U V) f x y i
  have hs (y) : ‖x.2‖ ^ y*B ≤ size y (k-i) g := via _ (ContinuousLinearMap.norm_snd_le ℝ U V) g x y _
  change ‖x‖ ^ n * (_ * A * B) ≤ _
  rw [show ‖x‖ ^ n*((k.choose i:ℝ)*A*B)= (k.choose i:ℝ)*(‖x‖^n*A*B) by ring,Prod.norm_def]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rcases le_total ‖x.2‖ ‖x.1‖ with e | e
  · rw [max_eq_left e]
    have he : B ≤ size 0 (k-i) g := by simpa using hs 0
    apply le_add_of_le_of_nonneg (mul_le_mul (ht n) he (norm_nonneg _) (apply_nonneg ..)) (by unfold size; positivity)
  rw [max_eq_right e, mul_right_comm, mul_comm _ A]
  have he : A ≤ size 0 i f := by simpa using ht 0
  exact le_add_of_nonneg_of_le (by unfold size; positivity) (mul_le_mul he (hs n)
    (by dsimp only [B]; positivity) (apply_nonneg ..))

def combine (f : Probe U) (g : Probe V) : Probe (U × V) where
  toFun x := f x.1*g x.2
  smooth' := ((f.smooth ⊤).comp contDiff_fst).mul ((g.smooth ⊤).comp contDiff_snd)
  decay' i j := ⟨_,extent_bound f g i j⟩

@[simp] theorem combine_at (f : Probe U) (g : Probe V) (p) : combine f g p=f p.1*g p.2 := rfl
lemma size_bound (f : Probe U) (g : Probe V) (n k) : size n k (combine f g) ≤ term n k f g :=
  (combine f g).seminorm_le_bound ℂ n k (term_nonneg ..) (extent_bound f g n k)

lemma compact_combine {f : Probe U} {g : Probe V} (h : HasCompactSupport ⇑f) (k : HasCompactSupport ⇑g) :
    HasCompactSupport (combine f g : U × V → ℂ) := by
  apply HasCompactSupport.intro (h.prod k); intro p hp
  classical
  rw [Set.mem_prod] at hp; push Not at hp
  rw [combine_at]; by_cases he : p.1 ∈ tsupport f
  · rw [image_eq_zero_of_notMem_tsupport (hp he),mul_zero]
  rw [image_eq_zero_of_notMem_tsupport he,zero_mul]

private def tsumx (i j : ℕ) (p q : Probe U × Probe V) := term i j (q.1-p.1) p.2 + term i j q.1 (q.2-p.2)

private lemma viaeq (i j : ℕ) (p q : Probe U × Probe V) : size i j (combine q.1 q.2 - combine p.1 p.2) ≤ tsumx i j p q := by
  unfold tsumx
  rw [show combine q.1 q.2 - combine p.1 p.2 = combine (q.1-p.1) p.2 + combine q.1 (q.2-p.2) by ext1; simp;ring]
  unfold size; refine le_trans (map_add_le_add (SchwartzMap.seminorm ℂ i j) _ _) (add_le_add (size_bound (q.1-p.1) p.2 i j) (size_bound q.1 (q.2-p.2) i j))

private lemma viact (i j : ℕ) (p : Probe U × Probe V) : Continuous (tsumx i j p) := by
  let F : Probe U × Probe V → Probe U × Probe V := fun q => (q.1-p.1,p.2)
  let G : Probe U × Probe V → Probe U × Probe V := fun q => (q.1,q.2-p.2)
  have ht : Continuous F := (continuous_fst.sub continuous_const).prodMk continuous_const
  have hs : Continuous G := continuous_fst.prodMk (continuous_snd.sub continuous_const)
  exact ((term_cont i j).comp ht).add ((term_cont i j).comp hs)

lemma tendN {R : Type*} (L : Filter R) (F : R → Probe U) (w : Probe U) :
    Tendsto F L (𝓝 w) ↔ ∀ (i j : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ k in L, size i j (F k-w) < ε := by
  rw [(schwartz_withSeminorms ℂ U ℂ).tendsto_nhds F w]
  simp only [Prod.forall]
  rfl

lemma normCont : Continuous (fun p : Probe U × Probe V => combine p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro p
  apply (tendN (𝓝 p) (fun q : Probe U × Probe V => combine q.1 q.2) (combine p.1 p.2)).mpr
  intro i j ε hε
  have hh := (viact i j p).continuousAt (x := p) |>.tendsto
  rw [show tsumx i j p p=0 by simp [tsumx,term_zero,zero_term]] at hh
  exact (hh.eventually (gt_mem_nhds hε)).mono (fun q hq => lt_of_le_of_lt (viaeq ..) (show tsumx i j p q < ε from hq))

end Probe

abbrev Test4 := Probe E4
abbrev Joint (n : ℕ) := Probe (Points n)

namespace Joint
variable {n : ℕ}

def trivial : Joint 0 := (HasCompactSupport.of_compactSpace (f := fun _ : Points 0 => (1:ℂ))).toSchwartzMap contDiff_const
@[simp] theorem trivial_at (x : Points 0) : trivial x=1 := rfl

def breakAt : Points (n+1) ≃L[ℝ] E4 × Points n := Points.peel.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ E4 (Points n))

def combine (f : Test4) (g : Joint n) := Probe.along breakAt (Probe.combine f g)
@[simp] theorem combine_at (x : Test4) (f : Joint n) (v) : combine x f v=x (v 0) * f (Points.tail v) := rfl
lemma contCombine : Continuous (fun p : Test4 × Joint n => combine p.1 p.2) :=
  ((Probe.along breakAt).continuous).comp Probe.normCont

def materialize : (n : ℕ) → (Fin n → Test4) → Joint n
  | 0,_ => trivial
  | n+1,v => combine (v 0) (materialize n (Fin.tail v))

@[simp] theorem material_at (f : Fin n → Test4) (p : Points n) : materialize n f p = ∏ i, f i (p i) := by
  induction n with
  | zero => simp [materialize]
  | succ n ih => rw [materialize,combine_at,ih, Fin.prod_univ_succ];rfl

@[fun_prop] theorem jointCont (n) : Continuous (materialize n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have he : Continuous (fun v : Fin (n+1) → Test4 => Fin.tail v) := continuous_pi (fun i => continuous_apply i.succ)
    exact contCombine.comp ((continuous_apply 0).prodMk (ih.comp he))

variable (n) (p : Mink.Poincare)
def gpush : Joint n →L[ℂ] Joint n := (Probe.ahead (points fun _ => p.b)).comp (Probe.along (Mink.Poincare.togetherL p.Λ n).symm)
def push : Test4 →L[ℂ] Test4 := (Probe.ahead p.b).comp (Probe.along p.Λ.sends.symm)

@[simp] lemma gpush_at (f x) : gpush n p f x=f (p⁻¹.zusammen n x) := by
  simp only [gpush,ContinuousLinearMap.comp_apply,Probe.ahead_at,Probe.along_at]
  congr 1; ext1 i; simp [Mink.Poincare.zusammen]

@[simp] lemma push_at (f x) : push p f x=f (p⁻¹.sends x) := by simp [push]
lemma tests (v : Fin n → Test4) : gpush n p (materialize n v)=materialize n fun i => push p (v i) := by
  ext1; simp [Mink.Poincare.zusammen]

end Joint
end YM.Boundary
