import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Products

/-!
# Infinite rows and atoms. Derivative summability at finite real logs
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {n l : Side} {ι α : Type*} {k : ℕ}
open Purse Logfee Plaque Cargo

section central
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem honorable {f : ι → X→Y} (h : ∀ i, ContDiff ℝ ω (f i)) {u : ι→ℝ} (he : Summable u) {m : ℕ}
    (p : Set X) (hp : IsOpen p) (hc : IsPreconnected p) (hg : ∀ i,∀ x∈p,∀ j≤m, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ u i) {x : X}
    (hx : x∈p) : ∀ j : ℕ,j≤m → HasSum (fun i => iteratedFDeriv ℝ j (f i) x) (iteratedFDeriv ℝ j (fun v => ∑' i, f i v) x) := by
  have hh i (hi : i≤m) (x) (hx : x∈p) : Summable fun j => iteratedFDeriv ℝ i (f j) x := .of_norm_bounded he fun k => hg k x hx i hi
  intro j
  induction j generalizing x with
  | zero =>
    intro hj; convert! (hh _ hj x hx).hasSum using 1
    simp_rw [iteratedFDeriv_zero_eq_comp]; exact (continuousMultilinearCurryFin0 ℝ X Y).symm.toContinuousLinearEquiv.map_tsum
  | succ j ih =>
    intro hj; have hv := j.le_succ.trans hj
    have h₁ : HasFDerivAt (fun x => ∑' i, iteratedFDeriv ℝ j (f i) x) _ x := hasFDerivAt_tsum_of_isPreconnected he hp hc
      (fun i x _ => ((h i).contDiffAt.differentiableAt_iteratedFDeriv (m:=j) (by simp)).hasFDerivAt)
      (fun i x hx => by
        simpa only [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_map,
          Function.comp_apply] using hg i x hx _ hj) hx (hh j hv x hx) hx
    · convert! (hh (j+1) hj x hx).hasSum using 1
      have ht : iteratedFDeriv ℝ j (fun z => ∑' i,f i z) =ᶠ[𝓝 x] fun z => ∑' i, iteratedFDeriv ℝ j (f i) z :=
        (show ∀ᶠ z in 𝓝 x, z∈p from hp.mem_nhds hx).mono fun z hz => (ih hz hv).tsum_eq.symm
      simp_rw [iteratedFDeriv_succ_eq_comp_left]
      dsimp only [Function.comp_apply]; rw [(h₁.congr_of_eventuallyEq ht).fderiv]; exact
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => X) Y).symm.toContinuousLinearEquiv.map_tsum
omit [CompleteSpace Y] in
lemma spends {j : Finset ι} {d : ι → X} {F : α→X→Y} {f : X → Y} {x : X}
    (h : HasSum (fun i => iteratedFDeriv ℝ j.card (F i) x) (iteratedFDeriv ℝ j.card f x)) : HasSum (fun i => bill j d (F i) x) (bill j d f x) :=
    (ContinuousMultilinearMap.apply ℝ _ Y (hook j d)).hasSum h
end central

section pose
variable {P : Purse ι (Site n)} {η C σ : ℝ}

def purePay (d : ι→Dir G n) : Purse ι (Site n) where
  mark := none
  cap := 1
  rooted := zero_le_one
  amps i := ‖d i‖
  budget _ := norm_nonneg _
  toll _ _ := 1
  toll_pos _ _ := zero_lt_one

lemma signs (d : ι→Dir G n) {η : ℝ} (h : 0 ≤ η) : tollRate (purePay d) l η := fun _ _ _ => by
  change 1 ≤ _ * 1; rw [mul_one]; apply Real.one_le_exp; positivity
lemma flex (d : ι→Dir G n) : Linkbill 1 (purePay d) d := by
  intro i j; refine ⟨by positivity,fun v x => ?_,fun ⟨_,_,he⟩ => ?_⟩
  · simpa only [Purse.price,Finset.prod_singleton,Purse.target,purePay, mul_one,one_mul,PNat.val_ofNat, Nat.cast_one,inv_one] using norm_le_pi_norm (d i) (x,j)
  change none=some _ at he; contradiction

lemma gross {κ : ℕ} (j : Fin κ → Dir G n) {f : Site n→Dir G n→ℝ} (x : Dir G n) (h : ∀ i, ContDiff ℝ ω (f i))
    (he : (purePay j).Jets Finset.univ j f x C) (i : Site n) :
    ‖iteratedFDeriv ℝ κ (f i) x j‖ ≤ C*∏ k, ‖j k‖ := by
  rw [← univEstimate _ _ _ (h _).contDiffAt]
  have hi := he.2.1 (show ¬ (purePay j).tagged Finset.univ from by simp [Purse.tagged,purePay]) i
  simpa [Purse.price,purePay,Purse.target] using hi

def down (σ : ℝ) (m : ℕ) := σ / (5*(m+1:ℝ))
lemma down_pos (m : ℕ) (h : 0 < σ) : 0 < down σ m := by unfold down; positivity
lemma uses_down (m : ℕ) (h : 0 < σ) : 5*m*down σ m ≤ σ := by
  rw [down,← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).mpr; nlinarith

def gift (G : Gauge) (η : ℝ) (m : ℕ) := max (2*ample G) (plan4 G η m)
def gratuity (G : Gauge) (η : ℝ) (m : ℕ) := mailCharge G η m* gift G η m
lemma gift_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0 < gift G η m := lt_max_of_lt_right (plan_pos G η m)
lemma gratuity_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0<gratuity G η m := mul_pos (mailCharge_pos ..) (gift_pos ..)

lemma nearby (d : Fin k → Dir G n) (x : Dir G n) (hx : ‖x‖ ≤ 1) (hh : 0<σ) (q : Slot) (m : ℕ) (hm : k ≤ m) :
    (purePay d).Jets Finset.univ d (spool q) x (gratuity G (down σ m) m*Real.exp (σ*q.length)) := by
  have hp := down_pos m hh; have hg : tollRate (purePay d) 1 (down σ m) := signs d hp.le
  have hv : (Finset.univ:Finset (Fin k)).card ≤ m := by simpa using hm
  apply (spool_pays (flex d) hg hp _ hv x hx q _ (fun T ht => post_pop (flex d) hg hp.le T _ ((Finset.card_le_card ht).trans hv) x hx _)).mono
  apply mul_le_mul_of_nonneg_left
    (fee_limit _ (l:=1) (by simpa using uses_down m hh)) (gratuity_pos G _ _).le

lemma stands (x : Dir G n) (hx : ‖x‖ ≤ 1) (hh : 0 < σ) (q : Slot) (m : ℕ) (hm : k ≤ m) (i : Site n) :
    ‖iteratedFDeriv ℝ k (spool q i) x‖ ≤ gratuity G (down σ m) m * Real.exp (σ*q.length) := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (gratuity_pos ..).le (Real.exp_pos _).le); intro d
  rw [← univEstimate _ _ _ (spinner ..).contDiffAt]
  have hi := (nearby d x hx hh q m hm).2.1 (show ¬ (purePay d).tagged Finset.univ from by simp [Purse.tagged,purePay]) i
  simpa [Purse.price,purePay,Purse.target] using hi

lemma neighbors {r : ℕ} (x : Dir G n) (hx : ‖x‖ ≤ 1) (hh : 0<σ) (A : Atom G r) (m : ℕ) (hm : k ≤ m) (i : Site n) :
    ‖iteratedFDeriv ℝ k (effect A i) x‖ ≤ ((2:ℝ)^m * gratuity G (down σ m) m)^r*A.budget σ := by
  have hp := down_pos m hh; have hi : (Finset.univ:Finset (Fin k)).card ≤ m := by simpa using hm
  apply ContinuousMultilinearMap.opNorm_le_bound (by have ht := gratuity_pos G (down σ m) m; unfold Atom.budget Atom.magnitude; positivity); intro d
  have hg : tollRate (purePay d) 1 (down σ m) := signs d hp.le
  exact gross d x (effective A) (levy (flex d) hg hp x hx Finset.univ m hi (show _ from by simpa using uses_down m hh) _
    (fun q T ht => post_pop (flex d) hg hp.le T _ ((Finset.card_le_card ht).trans hi) x hx q) A (gift_pos G _ _).le) i

def service (W : PathData G) (p : Face (Per n)) (i : ℕ) (a : Dir G n) := W.ellTerms p i (represent a)
def atend (A : ℕ→Atom G k) (i : Site n) (x : Dir G n) := ∑' j,effect (A j) i x

lemma application {κ : ℕ} (A : ℕ→Atom G κ) (x : Dir G n) (hx : ‖x‖ < 1) (hh : 0 < σ) (hm : SumBudget (fun i => (A i).budget σ) C) (i : Site n) (S : Finset ι) (d : ι→Dir G n) :
    HasSum (fun j => bill S d (effect (A j) i) x) (bill S d (atend A i) x) := by
  refine spends (honorable (f:=fun j => effect (A j) i) (fun _ => effective ..) (hm.2.1.mul_left (((2:ℝ)^S.card*gratuity G (down σ S.card) S.card)^κ))
    (m:=S.card) (Metric.ball (0:Dir G n) 1) Metric.isOpen_ball (convex_ball _ _).isPreconnected ?_ (by simpa using hx) _ le_rfl)
  intro i v hv l hl; exact neighbors v (show ‖v‖ ≤ 1 by exact le_of_lt (by simpa using hv)) hh _ _ hl _

lemma reception (W : PathData G) (i : Face (Per n)) (hx : SumBudget (fun j => |(W.row i.2 j).1| * Real.exp (σ * (W.row i.2 j).2.length)) C)
    (hh : 0<σ) (x : Dir G n) (hp : ‖x‖ < 1) (d : ι→Dir G n) (S : Finset ι) :
    HasSum (fun j => bill S d (service W i j) x) (bill S d (fun x => W.ell (represent x) i) x) := by
  let w := gratuity G (down σ S.card) S.card
  have hg (j) : ContDiff ℝ ω (service W i j) := (spinner (G:=G) _ _).const_smul _
  refine spends (honorable hg (hx.2.1.mul_left w) (m:=S.card) (Metric.ball (0:Dir G n) 1) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ (show x∈_ by simpa using hp) _ le_rfl)
  intro j x hp k hk
  let y := W.row i.2 j
  rw [show service W i j=y.1 • spool (G:=G) y.2 i.1 from rfl, iteratedFDeriv_const_smul_apply
    (by exact ((spinner (G:=G) y.2 _).contDiffAt).of_le le_top),norm_smul]
  apply (mul_le_mul_of_nonneg_left (stands x (le_of_lt (by simpa using hp)) hh _ _ hk _) (norm_nonneg y.1)).trans_eq
  rw [Real.norm_eq_abs]; change |y.1| * (w*_)=w* (|y.1| * _); ring
end pose
end YM.AnalyticNext.QuarticMatch.Estimate
