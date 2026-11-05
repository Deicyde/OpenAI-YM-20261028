import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Visit
import YM.AnalyticNext.QUARTIC_MATCH.Pre.Center
import YM.Next.FREE_KERNELS.Amend

/-!
# At the centered minimizer. Mixed jets via the mean-complement

No bare assumption on vertex-price directions; propagate to every h derivative
needed here. No Jacobian estimate or away-from-station curvature prices.

Method: a frame equal up to common left gauge to the one *actually used*
in the prediction on the minimizing branch. Use the matrix centroid choice,
so the weighted mass has constant Lie projection. Near zero each envelope
entry is the focus of a cloud based on the access paths and the frame values
(`splices`). At order >0 at flat, the potentially bad term in differentiating
`tape` is just the *unweighted mean* of frame derivatives of that same order;
show we can already price the difference (by lower-order costs and counting
path estimates). In `Volume`: apply the focus derivative (at zero fields)
which is exactly tangential projection. Thus all but constant Lie pieces of
those frame jets are paid for. Recover those pieces too by the weighted
mass condition (the weights themselves are bounded above by C_J times the
unweighted averaging weights, crucial for the mixed l²-l¹ cost here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Knot
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
namespace Yard
open Purse Logfee
variable {G : Gauge} {c f : Side} (S : StepData c f) {ι α : Type}
local notation "L" => S.patch.L
local notation "R" => S.patch.radius
local notation "l" => S.patch.L.val
local notation "Y" => S.patch.Points
local notation "X" => Dir G f
local notation "E" => G.Mat

section average
variable {β Z V : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype α] [Fintype β] [Nonempty β] [Nonempty α]
omit [Nonempty α] in
lemma smoother (x : α→Z→V) (y : Z) (h : ∀ i,ContDiffAt ℝ ω (x i) y) :
    ContDiffAt ℝ ω (fun w => avg fun i => x i w) y := (ContDiffAt.sum fun i _ => h i).const_smul _
omit [Nonempty α] in
lemma funds (x : α→Z→V) (y : Z) (h : ∀ i,ContDiffAt ℝ ω (x i) y) (T : Finset ι) (d) :
    bill T d (fun w => avg fun i => x i w) y= avg fun i => bill T d (x i) y := by
  unfold avg
  change bill T d ((Fintype.card α:ℝ)⁻¹ • (fun w => ∑ i, x i w)) y=_
  rw [smul_price _ _ (ContDiffAt.sum fun i _ => h i),sum_bill ..]; exact fun i _ => h i
omit [Nonempty α] [Nonempty β] in
lemma poolGeneral (x : α×β→Z) : avg x = avg fun i : α => avg fun j : β => x (i,j) := by
  unfold avg; rw [Fintype.card_prod,Fintype.sum_prod_type, ← Finset.smul_sum,smul_smul]
  rw [Nat.cast_mul,_root_.mul_inv_rev,mul_comm]
end average
variable [DecidableEq ι]

def envelope (a : S.SitesChoice) (i : Site c) (j : Y) (x : X) := matter S a x i j

def load (a : S.SitesChoice) (i : Site c) (j : cargo S) (x : X) := envelope S a i j.2.1 x * star (line S i j x)

def tape (a : S.SitesChoice) (i : Site c) (j : Y) (x : X) := avg fun k : Y × Lattice.Order => load S a i (j,k) x

def penny (G : Gauge) (v : G.Mat) := G.mat (G.focus v)
lemma compares (a : S.SitesChoice) (i : Site c) (j : Y) (x : X) : tape S a i j x=Push.cloud S i (x,matter S a x i) j := by
  unfold tape; rw [poolGeneral]; unfold Push.cloud load Push.product; simp_rw [travel_at]; rfl
variable (h : S.patch.Branches S.kernel G) (a : S.SitesChoice)
include h
lemma honest (i j) : ContDiffAt ℝ ω (envelope S a i j (G:=G)) 0 := Pre.Knot.germ S h a i j
lemma anchored (i j) : envelope S a i j (0:X)=1 := point_id S h a i j
lemma loaded (i j) : ContDiffAt ℝ ω (load S a i j (G:=G)) 0 := (honest S h a i j.2.1).mul
    ((show E ≃L[ℝ] E from starL ℝ).contDiff.contDiffAt.comp _ ((line_jet ..).contDiffAt))
lemma stamped (i j) : ContDiffAt ℝ ω (tape S a i j (G:=G)) 0 := smoother _ _ fun _ => loaded S h a ..
lemma swept (i j) : tape S a i j (0:X)=1 := by simp_rw [tape,load, anchored S h,line,transport, Push.stroll_zero,G.mat_one,star_one,mul_one,avg_const]
lemma splices (i j) : envelope S a i j =ᶠ[𝓝 (0:X)] penny G ∘ tape S a i j :=
    (rays S h a i j).mono fun x hx => hx.trans (by rw [Function.comp_apply,compares]; rfl)
omit [DecidableEq ι] in
lemma on_duty (i j) (T : Finset ι) (d) : bill T d (tape S a i j) (0:X) =
    avg fun k => bill T d (load S a i (j,k)) (0:X) := funds _ _ (fun _ => loaded S h a ..) T d
variable {η : ℝ} (he : 0 < η) (P : Purse ι (Site f)) (v : ι→Dir G f)
  (ht : tollRate P S.patch.L η) (hc : P.cap=(S.patch.L.val:ℝ)^2) (hL : Linkbill S.patch.L P v)
local notation "T" => cap S P

def sea (i m : ℕ) (G : Gauge) (η C : ℝ) := (2:ℝ)^m*(C*((2:ℝ)^4 * walkCash G i m η))
omit h in
lemma sea_pos (i m : ℕ) (G : Gauge) (η : ℝ) {C : ℝ} (hc : 0 ≤ C) : 0 ≤ sea i m G η C := by
  have h := cash_pos G i m η; unfold sea; positivity

omit [DecidableEq ι] h in
lemma prosperous (S' : Finset ι) {C} (hh : (cap S P).Many S' v (envelope S a) 0 C) :
    (cap S P).Many S' v (fun i j => envelope S a i (j : cargo S).2.1) 0 C := by
  let e : cargo S ≃ (Y×Lattice.Order)×Y := Equiv.prodComm ..
  exact (Spend.reshapes e (hh.reuses (γ:=Lattice.Order) |>.reuses (γ:=Y)))
omit h in
lemma bid (S' : Finset ι) (m : ℕ) (hs : S'.card ≤ m) (he : 0 < η) (ht : tollRate P L η)
    (hc : P.cap=(l:ℝ)^2) (hL : Linkbill L P v) :
    (cap S P).Many S' v (fun i j => fun x => star (line S i j x)) 0 ((2:ℝ)^4*walkCash G S.patch.J m η) :=
    Many.edit (couple S ht he hc v hL 0 (by simp) m S' hs) (fun i j => (line_jet ..).contDiffAt)
      ((show E≃L[ℝ] E from starL ℝ).toContinuousLinearMap) (fun y => (norm_star y).le)
include he ht hc hL
lemma tote (S' : Finset ι) (m : ℕ) (hs : S'.card ≤ m) {C} (hh : ∀ U⊆S',(cap S P).Many U v (envelope S a) 0 C) :
    (cap S P).Many S' v (tape S a) 0 (sea S.patch.J m G η C) := by
  let φ := ContinuousLinearMap.mul ℝ E
  have hg : (cap S P).Many S' v (load S a) 0 ((2:ℝ)^m * (C*((2:ℝ)^4*walkCash G S.patch.J m η))) :=
    Many.priced φ (fun x y => norm_mul_le x y) (fun i (j : cargo S) => honest S h a i j.2.1)
      (fun i j => (show ContDiffAt ℝ ω (fun x => star (line S i j x)) (0:X) from ((show E≃L[ℝ] E from starL ℝ).contDiff.contDiffAt.comp _
        ((line_jet (G:=G) S i j).contDiffAt)))) (fun i hi => prosperous S a P v i (hh i hi))
      (fun i hi => bid S P v i m ((Finset.card_le_card hi).trans hs) he ht hc hL) m hs
  refine (Spend.pooled (γ:=Y × Lattice.Order) hg).change fun i j => ?_
  change ‖bill S' v (tape S a i j) (0:X)‖ ≤ _; rw [on_duty S h a]

lemma compensate (S' : Finset ι) {m : ℕ} (hs : S'.card=m+1) {C : ℝ} (hp : 0 ≤ C)
    (hv : ∀ U⊆S',U.card ≤ m → (cap S P).Many U v (envelope S a) 0 C) :
    (cap S P).Spend S' (fun i j => bill S' v (tape S a i j) 0 - avg fun k : Y => bill S' v (envelope S a i k) 0)
      (sea S.patch.J (m+1) G η C) := by
  let F (i : Site c) (u : cargo S) := envelope S a i u.2.1 (G:=G)
  let W (i : Site c) (u : cargo S) (v : X) := star (line S i u v)
  let φ := ContinuousLinearMap.mul ℝ E
  let z (B : Finset ι) i j := φ (bill B v (F i j) 0) (bill (S'\B) v (W i j) 0)
  let D := (2:ℝ)^4*walkCash G S.patch.J (m+1) η
  let U := S'.powerset.erase S'
  have hb (B : Finset ι) (hB : B∈U) : (cap S P).Spend S' (z B) (C*D) := by
    obtain ⟨hh,hA⟩ := Finset.mem_erase.mp hB; have h' := Finset.mem_powerset.mp hA
    have hx := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h',hh⟩)
    have h1 := prosperous S a P v B (hv B h' (by omega))
    have h2 := bid S P v (S'\B) (m+1) ((Finset.card_le_card Finset.sdiff_subset).trans_eq hs) he ht hc hL
    have H := h1.times (u:=z B) h2 Finset.disjoint_sdiff (fun _ _ => norm_mul_le ..)
    rwa [Finset.union_sdiff_of_subset h'] at H
  have hh (i : Site c) (k : cargo S) : bill S' v (load S a i k) 0=(∑ B∈U,z B) i k+bill S' v (F i k) 0 := by
    have ht i j : ContDiffAt ℝ ω (W i j) 0 := (show E ≃L[ℝ] E from starL ℝ).contDiff.contDiffAt.comp _ ((line_jet (G:=G) S i j).contDiffAt)
    have he' := account φ S' v (F i k) (W i k) 0 (honest S h a i _) (ht i k)
    change _ = ∑ B∈S'.powerset,z B i k at he'
    change bill S' v (fun x => φ (F i k x) (W i k x)) 0=_
    have Ht : z S' i k=bill S' v (F i k) 0 := by
      unfold z; rw [Finset.sdiff_self,blank,show W i k 0=1 by unfold W line transport; rw [Push.stroll_zero,G.mat_one,star_one]]; exact mul_one _
    rw [he', ← Finset.sum_erase_add _ _ (show S'∈ S'.powerset from by simp),Ht]; simp only [Finset.sum_apply]; rfl
  apply Spend.change ((Spend.pooled (γ:=Y × Lattice.Order) (Spend.finite U hb)).mono ?_); swap
  · rw [Finset.sum_const,nsmul_eq_mul,sea]
    exact mul_le_mul_of_nonneg_right
      (show (U.card:ℝ) ≤ (2:ℝ)^(m+1) by exact_mod_cast (show U.card ≤ 2^(m+1) by
        apply (Finset.card_le_card (Finset.erase_subset ..)).trans_eq; rw [Finset.card_powerset, hs])) (mul_nonneg hp (mul_nonneg (by positivity) (cash_pos ..).le))
  intro i j
  rw [on_duty S h a, show (avg fun k : Y × Lattice.Order => bill S' v (load S a i (j,k)) 0)=_ from congr_arg avg (funext fun k => hh i (j,k)), avg_add]
  let g (k : Y) := bill S' v (envelope S a i k) 0
  have hp : avg (fun k : Y × Lattice.Order => g k.1)=avg g := by rw [poolGeneral]; simp
  rw [show (avg fun k : Y × Lattice.Order => bill S' v (F i (j,k)) 0)=avg g from hp]
  simp only [g,add_sub_cancel_right]; rfl
end Yard
end YM.AnalyticNext.QuarticMatch.Estimate
