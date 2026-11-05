import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Measure

/-!
# Fine plaquette and slot payroll

Both the expanded map and true path. Preserve two powers of μ at derivatives
as required in actual with-rough and without-rough price. Pay also cruder
nearby-a estimates useful later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Bloch
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n l : Side} {ι : Type*} [DecidableEq ι]
variable {P : Purse ι (Site n)} {η : ℝ}
open Purse Logfee
namespace Plaque

def plasty (q : PlaqAxes) (x : Site n) (a : Dir G n) := G.mat (faceValue (represent a) (x,q)) - 1
lemma order (q : PlaqAxes) (x : Site n) : ContDiff ℝ ω (plasty (G:=G) q x) :=
    (train_rate x (square q.val.1 q.val.2) (G:=G)).sub contDiff_const
lemma plastic (q : PlaqAxes) (x : Site n) : plasty q x (0:Dir G n)=0 := by simp only [plasty, faceValue, Push.stroll_zero,G.mat_one,sub_self]
lemma produces (a : Dir G n) (q : PlaqAxes) (x : Site n) : D a (plasty q x) 0 = G.colorMat (faceCurl (x,q) a) := by
  have hp := (face_deriv (x,q) a).sub_const 1; exact (Push.side (plasty q x) ((order _ _ (G:=G)).contDiffAt.differentiableAt (by simp)) a).unique hp

def BendBill (l : Side) (P : Purse ι (Site n)) (d : ι→Dir G n) := ∀ (i : ι) (q : PlaqAxes),
    P.Pays {i} (fun x => faceCurl (x,q) (d i)) ((l.val:ℝ)^2)⁻¹

def plan4 (G : Gauge) (η : ℝ) (m : ℕ) := ample G * ((unitPrice G m).C*(4*Real.exp (η*4)))^m
lemma plan_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0 < plan4 G η m := mul_pos (ample_pos _) (pow_pos
    (mul_pos (zero_lt_one.trans_le (unitPrice G m).used) (by positivity)) _)

lemma expenses {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 ≤ η) (w : Walk) (hw : w.length=4)
    (S : Finset ι) (m : ℕ) (hv : S.card ≤ m) (x : Dir G n) (hx : ‖x‖ ≤ 1) :
    P.Jets S d (Logfee.transport w) x (plan4 G η m/(l.val:ℝ)^S.card) := by
  apply (insured h he hp S w m hv x hx).mono
  unfold basicPay plan4; rw [hw, mul_div_assoc]; refine mul_le_mul_of_nonneg_left ?_ (ample_pos G).le
  have H : 0 < (l.val:ℝ) := side_pos l
  let u := (unitPrice G m).C; have hu : 1≤u := (unitPrice G m).used
  have hh : 1 ≤ Real.exp (η*4) := Real.one_le_exp (by positivity)
  have ha : 1 ≤ u*(4*Real.exp (η*4)) := one_le_mul_of_one_le_of_one_le hu (by linarith)
  change u^S.card*((↑(4:ℕ):ℝ)/ (l.val:ℝ)*guide l η 4)^S.card ≤ (u*(4*Real.exp (η*4)))^m/_
  rw [← mul_pow]
  apply le_trans _ (div_le_div_of_nonneg_right (pow_le_pow_right₀ ha hv) (by positivity)); rw [← div_pow]
  have hk := guide_pos l η 4; refine pow_le_pow_left₀ ?_ ?_ S.card; · positivity
  have he : guide l η 4 ≤ Real.exp (η*4) := by simpa using guide_le l 4 η hp
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity : 0 ≤ u)).trans_eq; push_cast; ring

def allotted (G : Gauge) (η : ℝ) (m : ℕ) := max G.colorScale (plan4 G η m)
lemma allotted_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0 < allotted G η m := lt_max_of_lt_left G.colorScale_pos

lemma collectBudget {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 ≤ η)
    (S : Finset ι) (m : ℕ) (hm : S.card ≤ m) (u : BendBill l P d) (q : PlaqAxes) :
    P.Jets S d (plasty q) 0 (allotted G η m/(l.val:ℝ)^2) := by
  have ht := allotted_pos G η m; have hL := side_pos l
  rcases Finset.eq_empty_or_nonempty S with hS|hS
  · rw [hS]; unfold Jets
    simp_rw [blank,plastic]; exact Pays.zero (by positivity)
  by_cases H : S.card=1
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp H
    let f := fun x => bill {i} d (plasty q x) 0
    have hh := (u i q).repay (g:=f) G.colorScale_pos.le (fun j => by
      unfold f; rw [alone _ _ _ (order _ _).contDiffAt, produces, G.colorMat_norm])
    exact hh.mono (by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
  have hD : 2 ≤ S.card := by have hc := Finset.card_pos.mpr hS; omega
  refine (((expenses h he hp (square q.val.1 q.val.2) rfl S m hm 0 (by simp)).mono ?_).under ?_)
  · apply (div_le_div_of_nonneg_right (le_max_right G.colorScale _) (by positivity)).trans
    exact div_le_div_of_nonneg_left ht.le (pow_pos hL _) (pow_le_pow_right₀ (by exact_mod_cast l.property) hD)
  intro i
  change ‖bill S d (fun a => Logfee.transport _ i a - _) 0‖ ≤ _
  rw [minor_rate S d ((train_rate ..).contDiffAt) contDiffAt_const,mute hS,sub_zero]

lemma post_pop {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 ≤ η)
    (S : Finset ι) (m : ℕ) (hm : S.card ≤ m) (x : Dir G n) (hx : ‖x‖ ≤ 1) (q : PlaqAxes) :
    P.Jets S d (plasty q) x (max (2*ample G) (plan4 G η m)) := by
  rcases Finset.eq_empty_or_nonempty S with H|H
  · rw [H]
    apply Pays.blank (le_max_of_le_right (plan_pos ..).le); intro i
    rw [blank]; apply le_trans _ (le_max_left ..)
    have hh := norm_sub_le (G.mat (faceValue (represent x) (i,q))) 1
    rw [unit_pay] at hh; unfold plasty; linarith [show ‖(1:G.Mat)‖ ≤ ample G from le_max_right ..]
  refine ((expenses h he hp (square q.val.1 q.val.2) rfl S m hm x hx).mono ((div_le_self (plan_pos ..).le (one_le_pow₀ (by exact_mod_cast l.property))).trans (le_max_right ..))).under ?_
  intro i
  change ‖bill S d (fun a => Logfee.transport _ i a-_) x‖ ≤ _
  rw [minor_rate S d ((train_rate ..).contDiffAt) contDiffAt_const,mute H,sub_zero]

def spool (p : Slot) (x : Site n) (a : Dir G n) := p.atSite (represent a) x
def launch (p : Slot) : Equiv.Perm (Site n) := Equiv.addLeft (wrap n p.offset)
lemma sooner (p : Slot) (x : Site n) : separation x (launch p x) ≤ p.walk.length := by
  have he : launch p x=stop x p.walk := by
    change wrap n (stop 0 _)+x=_; rw [wrap_stop_cover,map_zero]
    exact (by simpa [add_comm] using (Work.E03.stop_add_left x (0:Site n) p.walk).symm)
  rw [he]; exact advancing ..

def skim (G : Gauge) : G.Mat→L[ℝ] G.Color := G.projectColor.toContinuousLinearMap ∘L
    ((1/2:ℝ) • ((ContinuousLinearMap.id ℝ _) - (starL ℝ (A:=G.Mat)).toContinuousLinearMap))
lemma route (p : Slot) (x : Site n) (a : Dir G n) :
    spool p x a=skim G (Logfee.transport p.walk x a * plasty p.plaq (launch p x) a * star (Logfee.transport p.walk x a)) := by
  let V := travel (represent a) x p.walk
  let Q := faceValue (represent a) (launch p x,p.plaq)
  rw [spool,atSite_path, ← G.curvature_conjugate,Gauge.curvature]
  have he : G.mat V* (G.mat Q-1)*star (G.mat V) = G.mat (V*Q*V⁻¹) - 1 := by
    rw [G.mat_mul,G.mat_inv,G.mat_mul,mul_sub,sub_mul,mul_one,G.mat_mul_star]
  change G.projectColor ((1/2:ℝ) • (G.mat (V*Q*V⁻¹)-_))=skim G (G.mat V*(G.mat Q-1)*star (G.mat V))
  rw [he]; change _=G.projectColor ((1/2:ℝ) • ((G.mat _-1)-star (G.mat _-1)))
  rw [star_sub,G.mat_inv]; simp; rfl
lemma spool_start (p : Slot) (x : Site n) : spool p x (0:Dir G n)=0 := by rw [route,plastic,mul_zero,zero_mul,map_zero]
lemma spinner (p : Slot) (x : Site n) : ContDiff ℝ ω (spool (G:=G) p x) := by
  rw [show spool (G:=G) p x=skim G ∘ fun a => _ from funext fun i => route p x i]
  have hh := train_rate (G:=G) x p.walk
  exact (skim G).contDiff.comp ((hh.mul (order _ _)).mul ((show G.Mat≃L[ℝ] G.Mat from starL ℝ).contDiff.comp hh))

/-! Use cost for color projection, explicitly Frobenius. -/
lemma skim_norm (a : G.Mat) : ‖skim G a‖ ≤ G.colorScale⁻¹*‖a‖ := by
  refine (G.project_norm _).trans ?_; rw [inv_mul_eq_div]
  apply div_le_div_of_nonneg_right _ G.colorScale_pos.le
  change ‖(1/2:ℝ) • (a-star a)‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; have hx := norm_sub_le a (star a); rw [norm_star] at hx; linarith

/-- Keep the two legs of the transported group conjugation even post-L.
Use number of directions = m but S may be smaller. -/
def mailCharge (G : Gauge) (η : ℝ) (m : ℕ) := G.colorScale⁻¹*((2:ℝ)^m)^2*tollBound G η m^2
lemma mailCharge_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0<mailCharge G η m := mul_pos
    (mul_pos (inv_pos.mpr G.colorScale_pos) (by positivity)) (pow_pos (tollBound_pos ..) _)

lemma spool_pays {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 < η) (m : ℕ) {S : Finset ι} (hm : S.card ≤ m)
    (x : Dir G n) (hx : ‖x‖ ≤ 1) (q : Slot) (C : ℝ) (hb : ∀ S'⊆S, P.Jets S' d (plasty q.plaq) x C) :
    P.Jets S d (spool q) x (mailCharge G η m*C*guide l (5*m*η) q.length) := by
  let t := tollBound G η m
  let s := q.walk.length
  let u := guide l (2*m*η) s
  let v := guide l η s
  let r := guide l (5*m*η) s
  have hC := (hb S (fun _ hh => hh)).1
  have hv : 1 ≤ v := guide_ge l s η hp.le
  have hT (T : Finset ι) (ht : T⊆S) := book h he hp q.walk T m ((Finset.card_le_card ht).trans hm) x hx
  let W := Logfee.transport (G:=G) (n:=n) q.walk
  let p i := plasty (G:=G) q.plaq (launch q i) (n:=n)
  let U i := W i * p i
  let V : G.Mat→L[ℝ] G.Mat := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).toContinuousLinearMap
  let φ := ContinuousLinearMap.mul ℝ G.Mat
  have hh (i) : ContDiffAt ℝ ω (Logfee.transport (G:=G) q.walk i) x := (train_rate ..).contDiffAt
  have hj (i) : ContDiffAt ℝ ω (U i) x := (hh i).mul (order ..).contDiffAt
  let y := t*u
  have h1 (A) (ht : A⊆S) : P.Jets A d U x ((2:ℝ)^m*(y*(v^m*C))) := by
    apply Jets.priced φ (fun i j => norm_mul_le i j) hh (fun i => (show ContDiffAt ℝ ω (p i) x from (order (G:=G) q.plaq _).contDiffAt))
      (fun i hi => hT i (hi.trans ht)) _ m ((Finset.card_le_card ht).trans hm)
    intro i hi
    have h' := hi.trans ht
    apply (shifting P he hp.le (hb i h') _ (launch q) (sooner q)).mono
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hv ((Finset.card_le_card h').trans hm)) hC
  have h2 (A) (ht : A⊆S) : P.Jets A d (fun i => V ∘ W i) x y := by
    apply Jets.change_map (hT A ht) V hh
    intro i; exact (norm_star i).le
  let f i (a : Dir G n) := U i a * V (W i a)
  have hf i : ContDiffAt ℝ ω (f i) x := (hj i).mul (V.contDiff.contDiffAt.comp x (hh i))
  have h3 : P.Jets S d f x ((2:ℝ)^m*((2:ℝ)^m*(y*(v^m*C))*y)) := Jets.priced φ
    (fun i j => norm_mul_le i j) hj (fun i => V.contDiff.contDiffAt.comp x (hh i)) h1 h2 m hm
  rw [show (spool q (G:=G))=(fun i => skim G ∘ f i) from funext fun i => funext fun j => route q i j]
  apply (Jets.spend h3 (skim G) hf (inv_nonneg.mpr G.colorScale_pos.le) (skim_norm)).mono
  have hL : s ≤ q.length := by unfold s Slot.length; omega
  calc
    _ = mailCharge G η m*C*(u*u*v^m) := by unfold y t mailCharge; ring
    _ = mailCharge G η m*C*r := by unfold r u v guide; rw [← Real.exp_add,← Real.exp_nat_mul,← Real.exp_add]; congr 2; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mailCharge_pos ..).le hC)
      exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hL) (by positivity))
end Plaque
end YM.AnalyticNext.QuarticMatch.Estimate
