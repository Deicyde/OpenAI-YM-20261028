import YM.AnalyticBridge.VERIFIED_RESET_STEP.Residual
import YM.Push.LOCAL_SPLITTING.Orientation


/-! Actual paths of every signed channel oriented before deployment.
Negative positive-link derivatives charge the `LOCAL_SPLITTING` turn cost,
not naive preservation of ordered jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux UVNext.PricedKernels Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}

open Next.Foundations in
lemma regular_mapped {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) {f : Config G n → E} (h : p.Regular X f) : p.Regular X (L ∘ f) :=
  ⟨fun U V he => congrArg L (h.sites U V he), L.continuous.measurable.comp h.borel,fun t U => congrArg L (h.symmetry t U),
    fun U he => L.contDiff.contDiffAt.comp 0 (h.smooth U he),fun U he A _l hl => left_has A hl (L.contDiff.contDiffAt.comp 0 (h.smooth U he))⟩

-- Need left deriv commutation for L even at boundary.
open Next.Foundations in
lemma left_real (f : Pot G n) (U) {l : List (Dir G n)} {k : ℕ} (he : ContDiffAt ℝ k (f ∘ increment U) 0) (hl : l.length ≤ k) :
    leftDerivs (fun x => (f x:ℂ)) l U = ((leftDerivs f l U:ℝ):ℂ) := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih =>
    refine ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (left_has A (show l.length < k from hl) he)).congr_of_eventuallyEq
      (f₁:=fun t => leftDerivs (fun x => (f x:ℂ)) l (increment U (t • A))) ?_).deriv
    obtain ⟨c,hc,hC,hcc⟩ := Progress.DirectedRecipe.shifted (u:=Prod.fst (α:=Dir G n) (β:=Dir G n)) (v:=Prod.snd)
      (x:=0) (m:=↑k) rfl rfl contDiffAt_fst contDiffAt_snd
    have hb := (((hc.symm ▸ he).comp (f:=c) 0 hC).congr_of_eventuallyEq ((hcc U).fun_comp f)).eventually (by simp)
    let q (t : ℝ) := (t • A, (0:Dir G n)); have ht : Tendsto q (𝓝 0) (𝓝 0) := by
      rw [← show q 0=0 by simp [q, Prod.zero_eq_mk]]; exact (show Continuous q by unfold q; fun_prop).tendsto _
    filter_upwards [ht.eventually hb] with t h
    exact ih _ (h.comp 0 (f:=fun x => (t • A,x)) (contDiffAt_const.prodMk contDiffAt_id)) (by simp_all; omega)

lemma sup_real {f : Pot G n} {o a} (h : p.Regular X f) : p.supBounds o X (fun U => (f U : ℂ)) a ↔ p.supBounds o X f a :=
  and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun he => forall_congr' fun l => forall_congr' fun hl => by
    rw [left_real _ _ (h.smooth _ he) hl,Complex.norm_real]

abbrev Seat (n : Side) := Signed × Site n
namespace Seat
variable (x : Seat n)

def view : Config G n → Config G n := pull x.1 x.2
def spread (X : Support n) := X.image (affine x.1 x.2)
def reg (X : Support n) (hX : (0:Site n) ∈ X) : RegularAddress n := ⟨x.2,x.spread X,Finset.mem_image.mpr ⟨0,hX,by simp [affine]⟩⟩
lemma turn_zero : Push.Local.turnSites x.1 x.2 0 = x.2 := by change affine x.1 x.2 0 = x.2; simp [affine]
lemma healthy (t : ℝ) (X : Support n) (U : Config G n) : Healthy t (spread x X) U ↔ Healthy t X (view x U) := healthy_image ..
lemma distribute (t : ℝ) (X : Support n) (f : Pot G n) : masked t (x.spread X) (f ∘ x.view) = masked t X f ∘ x.view := by
  ext U
  by_cases he : Healthy t (spread x X) U
  · rw [masked_eq _ _ _ _ he,show ((masked t X f ∘ x.view) U) = masked t X f (x.view U) from rfl,masked_eq _ _ _ _ ((healthy ..).1 he)]; rfl
  rw [masked_ne _ _ _ _ he,show ((masked t X f ∘ x.view) U) = masked t X f (x.view U) from rfl, masked_ne _ _ _ _ (mt (healthy ..).2 he)]

lemma regular {f : Pot G n} (h : p.Regular X f) : p.Regular (spread x X) (f ∘ x.view) := by
  have h' := regular_mapped Complex.ofRealCLM h
  exact regular_mapped Complex.reCLM (Push.Local.regular_pull h' x.1 x.2)
lemma sup {a} {f : Pot G n} (h : p.Regular X f) (ha : p.supBounds 0 X f a) :
    p.supBounds x.2 (spread x X) (f ∘ view x) (Push.Local.turnCost p.order p.power * a) := by
  apply (sup_real (regular x h)).1
  exact x.turn_zero ▸ Push.Local.bound_pull (regular_mapped Complex.ofRealCLM h) ((sup_real h).2 ha) x.1 x.2

lemma unwrapped (h : Nonwrapping (spread x X) x.2) : Nonwrapping X 0 := by
  rw [← spin_wrap x.1 x.2]; simpa only [affine,Signed.act_zero,zero_add] using! h
lemma hessian (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) (hX : Nonwrapping (spread x X) x.2)
    (hn : 4 ≤ n.val) (a b : LinearJet G) : logHessian (f ∘ view x) (a.field x.2) (b.field x.2) =
      logHessian f ((a.turn x.1).field 0) ((b.turn x.1).field 0) := by
  simpa only [affine,Signed.act_zero,zero_add] using! a.hessian_turn x.1 x.2 _ (unwrapped x hX) hn b hG h

lemma visit_count (X : Support n) : coverNumber p.B (spread x X) = coverNumber p.B X :=
    Push.Local.cover_map (Push.Local.turnSites x.1 x.2) (Push.Local.turn_sep _ _) ..

def move (s : Signed) (b : Site n) : Equiv.Perm (Seat n) := (Equiv.mulLeft s).prodCongr (Push.Local.turnSites s b)
lemma spread_move (s : Signed) (b : Site n) (X : Support n) : spread (move s b x) X = (spread x X).image (affine s b) := by
  change X.image (affine (s*x.1) (affine s b x.2)) = _
  simp only [spread, Finset.image_image, affine]; congr 1; funext i; simp [affine,Signed.act_mul,add_assoc]
lemma view_move (s : Signed) (b : Site n) : view (move s b x) (G:=G) = view x ∘ pull s b := funext fun _ => (pull_pull ..).symm
end Seat
end YM.AnalyticBridge.VerifiedReset
