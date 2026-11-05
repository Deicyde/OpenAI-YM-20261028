import YM.AnalyticBridge.VERIFIED_RESET_STEP.Affine
import YM.Push.STRESS_FLUX.Jets


/-! Covariance of affine projections on an anchored nonwrapping support.
Reflection may move a positive link's base, hence turn includes a constant
term shift, before using the same curl-component rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}

lemma spin_separation (s : Signed) (b x y : Site n) : separation (affine s b x) (affine s b y) = separation x y := by simp [affine]
lemma spin_wrap (s : Signed) (b o : Site n) : Nonwrapping (X.image (affine s b)) (affine s b o) ↔ Nonwrapping X o := by
  simp only [Nonwrapping,Finset.forall_mem_image,spin_separation]

lemma spin_coord (s : Signed) (b x o : Site n) (i : Axis) (hx : 10*separation x o < n.val) :
    coord (affine s b o) (affine s b x) (s.perm i) = sign s i * coord o x i := by
  have he : lift (affine s b x - affine s b o) = s.act (lift (x-o)) := by
    apply lift_eq_iff.mpr
    refine ⟨?_,fun i => ?_⟩
    · rw [← wrap_signed,wrap_lift,s.act_sub,affine,affine]; abel
    obtain ⟨j,rfl⟩ := s.perm.surjective i
    have hi := component_le (x-o) j
    unfold separation at hx
    rw [Signed.act_at]; split <;> omega
  simp [coord,he,sign,ite_mul]

def pullDir (s : Signed) (b : Site n) : Dir G n →L[ℝ] Dir G n :=
    ContinuousLinearMap.pi (fun i => (sign s i.2) • ContinuousLinearMap.proj (R:=ℝ) (sendEdge s b i))
lemma pull_increment (s : Signed) (b : Site n) (u : Dir G n) : increment 1 (pullDir s b u) = pull s b (increment 1 u) := by
  funext i
  change G.lieExp (sign s i.2 • u (sendEdge s b i)) * 1 = _
  rw [mul_one]
  rcases hs : s.flip i.2 with _|_ <;> simp [sendEdge,pull,Step.rotate,Step.read,sign,hs,posDir,increment,Work.F03.exp_neg_color]

lemma hessian_pull (s : Signed) (b : Site n) {f : Pot G n} (hG : G.Simple) (h : p.Regular X f) (u v : Dir G n) :
    logHessian (f ∘ pull s b) u v = logHessian f (pullDir s b u) (pullDir s b v) := by
  have he : germ (f ∘ pull s b) = germ f ∘ pullDir s b := funext fun _ => congrArg f (pull_increment ..).symm
  have hh := (Work.F03.hessian_comp (pullDir (G:=G) s b).map_zero (germ_diff h) (pullDir s b).contDiff.contDiffAt
    (flat_critical hG h)).2 u v
  rw [← he,ContinuousLinearMap.fderiv] at hh
  exact hh

def orderedDir (w : Flux G) (i j : Axis) := if h : i < j then w ⟨(i,j),h⟩ else 0
/-- Pullback on the six independent slots. -/
def reframe (w : Flux G) (s : Signed) : Flux G := fun b =>
  (sign s b.val.1 * sign s b.val.2) •
    (orderedDir w (s.perm b.val.1) (s.perm b.val.2) - orderedDir w (s.perm b.val.2) (s.perm b.val.1))

namespace LinearJet
variable (a : LinearJet G) (s : Signed)

def turn : LinearJet G where
  slope i j := sign s i • sign s j • a.slope (s.perm i) (s.perm j)
  at0 i := sign s i • (a.at0 (s.perm i) - (if s.flip i then a.slope (s.perm i) (s.perm i) else 0))

private lemma coord_down (o x : Site n) (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (i j : Axis) :
    coord o (x-step i) j = coord o x j - if j=i then 1 else 0 := by
  unfold coord; rw [sub_eq_add_neg x (step i), ← Step.vec_neg, lift_step hx hn]; simp [sub_eq_add_neg]
private lemma field_down {o x : Site n} (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (i j : Axis) :
    a.field o (x-step i,j) = a.field o (x,j) - a.slope j i := by
  unfold field; simp_rw [coord_down o x hx hn,sub_smul,Finset.sum_sub_distrib]; simp [ite_smul]; abel
lemma pull_field (b o x : Site n) (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (i : Axis) :
    pullDir s b (a.field (affine s b o)) (x,i) = (a.turn s).field o (x,i) := by
  change (sign s i) • a.field (affine s b o) (sendEdge s b (x,i)) = _
  have hh : a.field (affine s b o) (affine s b x, s.perm i) = a.at0 (s.perm i) +
      ∑ j, coord o x j • sign s j • a.slope (s.perm i) (s.perm j) := by
    refine congrArg (a.at0 _ + ·) (((Equiv.sum_comp s.perm _).symm).trans ?_)
    simp_rw [spin_coord _ _ _ _ _ hx,mul_comm (sign s _),mul_smul]
  by_cases hp : s.flip i
  · rw [show sendEdge s b (x,i) = (affine s b x - step (s.perm i),s.perm i) by simp [sendEdge,posDir,Step.rotate,Step.used,hp],
      a.field_down (by simpa only [spin_separation] using hx) hn,hh,LinearJet.field]
    simp only [turn,sign,hp,↓reduceIte,neg_one_smul,neg_sub,smul_neg,Finset.sum_neg_distrib]; abel
  rw [show sendEdge s b (x,i) = (affine s b x,s.perm i) by simp [sendEdge,posDir,Step.rotate,Step.used,hp],hh,LinearJet.field]
  simp [turn,sign,hp]

private lemma curl_eq {i j : Axis} (h : i ≠ j) : a.curl i j = orderedDir a.positive i j - orderedDir a.positive j i := by
  rcases lt_or_gt_of_ne h with h|h
  · simp [curl,orderedDir,h,not_lt_of_gt h,positive]
  simp [curl,orderedDir,h,not_lt_of_gt h,positive]
lemma positive_turn : (a.turn s).positive = reframe a.positive s := by
  funext b; rw [reframe,← curl_eq a (s.perm.injective.ne b.property.ne),mul_smul]; unfold turn positive curl
  dsimp only; module

lemma hessian_turn (b o : Site n) (h : Nonwrapping X o) (hn : 4 ≤ n.val) (d : LinearJet G)
    {f : Pot G n} (hG : G.Simple) (hf : p.Regular X f) :
    logHessian (f ∘ pull s b) (a.field (affine s b o)) (d.field (affine s b o)) =
      logHessian f ((a.turn s).field o) ((d.turn s).field o) := by
  rw [hessian_pull _ _ hG hf]; exact hessian_agrees hG hf (fun e he _ => a.pull_field s b o e.1 (h _ he) hn _)
    (fun e he _ => d.pull_field s b o e.1 (h _ he) hn _)
end LinearJet

lemma flux_hessian_pull (s : Signed) (b o : Site n) {f : Pot G n} (hG : G.Simple) (hf : p.Regular X f)
    (h : Nonwrapping X o) (hn : 4 ≤ n.val) (c d : Flux G) :
    logHessian (f ∘ pull s b) ((primitive c).field (affine s b o)) ((primitive d).field (affine s b o)) =
      logHessian f ((primitive (reframe c s)).field o) ((primitive (reframe d s)).field o) := by
  rw [(primitive c).hessian_turn _ _ _ h hn (primitive d) hG hf]
  exact LinearJet.hessian_curl hG hf h hn (by simp [LinearJet.positive_turn]) (by simp [LinearJet.positive_turn])
end YM.AnalyticBridge.VerifiedReset
