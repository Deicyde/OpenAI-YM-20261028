import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Linger
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Measure
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Multi
import YM.Next.BOUNDARY.Stage
import YM.Next.SCHEDULE.SlotPay

/-!
# Collective bills on the actual frame patch and reads

Before all mesh sizes. Every order counts. Control rough contacts ALSO inside
path averages, using one rlen norm over translated anchors. This is a mixed
bill, not a ball-analytic uniform implicit radius argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
attribute [local instance] Gauge.frobInner
namespace Yard
open Purse Logfee
variable {G : Gauge} {c f : Side} (S : StepData c f) {ι α : Type}
local notation "L" => S.patch.L
local notation "R" => S.patch.radius
local notation "l" => S.patch.L.val
local notation "j" => S.patch.J
local notation "s" => S.patch.Points

def cap (P : Purse ι (Site f)) : Purse ι (Site c) := ⟨P.mark,1,by norm_num,P.amps,P.budget,
    fun i y => P.toll i (S.ratio.embed y),fun i y => P.toll_pos _ _⟩
lemma cap_price (P : Purse ι (Site f)) (T : Finset ι) (x : Site c) : (cap S P).price T x=P.price T (S.ratio.embed x) := rfl
lemma guide_bound (sL : Side) {w r : ℕ} (hr : w ≤ r*sL.val) {η : ℝ} (he : 0 ≤ η) : guide sL η w ≤ Real.exp (η*r) := by
  apply Real.exp_monotone; rw [div_mul_eq_mul_div, mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ he
  apply (div_le_iff₀ (side_pos _)).mpr; exact_mod_cast hr

def pushFee (i : ℕ) (η : ℝ) := Real.exp (η*(4*(i+3:ℝ)))
lemma push_ge (i : ℕ) {η : ℝ} (hp : 0 ≤ η) : 1 ≤ pushFee i η := Real.one_le_exp (by positivity)
lemma transport_weight {P : Purse ι (Site f)} {η : ℝ} (h : tollRate P L η) (he : 0 ≤ η) (T : Finset ι) {m : ℕ} (hv : T.card ≤ m)
    (x : Site c) (y : s) : (cap S P).price T x ≤ pushFee j η^m*P.price T (atPoint S x y) := by
  have hx : ∀ i : ι, P.toll i (S.ratio.embed x) ≤ pushFee S.patch.J η*P.toll i (atPoint S x y) := by
    intro i; apply (enters h he i _ _ _ (Response.at_point S x y)).trans
    have hm : 4*R = 4*(S.patch.J+3)*l := by unfold RG.Patch.radius; rw [Nat.mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (P.toll_pos _ _).le
    simpa [pushFee] using guide_bound S.patch.L hm.le he
  rw [cap_price]; unfold price; apply (Finset.prod_le_prod (fun i _ => (P.toll_pos _ _).le) (fun i _ => hx i)).trans
  simp only [Finset.prod_mul_distrib,Finset.prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (push_ge _ he) hv) (P.price_pos T _).le

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- convert from fine sup+l² to the actually reduced capacity on coarse. -/
lemma payment {X : Type} [NormedAddCommGroup X] {P : Purse ι (Site f)} {η : ℝ}
    (h : tollRate P S.patch.L η) (he : 0 ≤ η) (hc : P.cap=(l:ℝ)^2)
    (T : Finset ι) {m : ℕ} (hv : T.card ≤ m) (y : Site f→X) {C : ℝ} (hr : P.Pays T y C) :
    (cap S P).Spend T (fun x i => y (atPoint S x i)) (pushFee j η^m*give j*C) := by
  let r := pushFee S.patch.J η^m
  let q x := P.price T x * ‖y x‖
  have hq x i : (cap S P).price T x*‖y (atPoint S x i)‖ ≤ r*q (atPoint S x i) := ((mul_le_mul_of_nonneg_right (transport_weight S h he T hv x i) (norm_nonneg _)).trans_eq (mul_assoc ..))
  have hp : 0 ≤ r := pow_nonneg (le_trans zero_le_one (push_ge _ he)) _
  have hG := give_ge j
  refine ⟨mul_nonneg (mul_nonneg hp (zero_le_one.trans hG)) hr.1,fun ht x i => ?_, fun ht => ?_⟩
  · refine ((hq x i).trans ((mul_le_mul_of_nonneg_left (hr.2.1 ht _) hp).trans_eq (mul_assoc ..).symm)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hp hG) hr.1) (P.target_pos _)
  have hh i : avg (fun a => (cap S P).price T i*‖y (atPoint S i a)‖) ≤ r*pro S q i :=
    (avg_mono (hq i)).trans_eq (avg_mul ..)
  apply (rless (Purse.house (cap S P) T _) hh).trans
  have hv : rlen q ≤ (l:ℝ)^2*C*P.target T := by rw [← hc]; exact hr.2.2 ht
  have hg := (pro_ell S q).trans (mul_le_mul_of_nonneg_left hv (div_nonneg (zero_le_one.trans hG) (by positivity)))
  rw [rconstant hp]; refine (mul_le_mul_of_nonneg_left hg hp).trans_eq ?_
  change r*(give j/_*(_*(P.target T)))=1*(r*give j*C)*P.target T
  field_simp

def walkCash (G : Gauge) (i n : ℕ) (η : ℝ) :=
    (pushFee i η)^n*give i*(tollBound G η n*Real.exp ((2*n*η)*(8*(i+3:ℝ))))
lemma cash_pos (G : Gauge) (i m : ℕ) (η : ℝ) : 0<walkCash G i m η := by
  have h := tollBound_pos G η m; have ht := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (give_ge i)
  unfold walkCash pushFee; positivity

section single
variable {η : ℝ} {T : Purse ι (Site f)} (h : tollRate T S.patch.L η) (he : 0 < η) (hc : T.cap=(S.patch.L.val:ℝ)^2)
    (v : ι → Dir G f) (ht : Linkbill S.patch.L T v) (a : Dir G f) (ha : ‖a‖ ≤ 1) (n : ℕ) (q : Finset ι) (hq : q.card ≤ n)
include h he hc ht ha hq

lemma stroll (w : Walk) (hw : w.length ≤ 8*R) :
    (cap S T).Many q v (fun i u => Logfee.transport w (atPoint S i u)) a (walkCash G j n η) := by
  apply (payment S h he.le hc q hq _ ((book ht h he w q n hq a ha).mono ?_))
  have hu := guide_bound S.patch.L (r:=8*(S.patch.J+3)) (show w.length ≤ 8*(S.patch.J+3)*l from by unfold RG.Patch.radius at hw; rwa [Nat.mul_assoc])
    (by positivity : 0 ≤ (2*n:ℝ)*η)
  refine mul_le_mul_of_nonneg_left ?_ (tollBound_pos ..).le; push_cast at hu; exact hu
end single
section both

abbrev cargo := s×(s × Lattice.Order)
def line (x : Site c) (i : cargo S) := Logfee.transport (G:=G) (route i.1.val i.2.1.val i.2.2) (atPoint S x i.1)
lemma line_jet (x : Site c) (i : cargo S) : ContDiff ℝ ω (line S (G:=G) x i) := train_rate ..

abbrev CurlBox (S : StepData c f) := ↥(box (2*S.patch.radius))
lemma fits (v w : s) : w.val-v.val ∈ box (2*R) := by
  apply (box_iff_layers ..).mpr; intro i
  obtain ⟨hh,hp⟩ := box_test.mp v.property; obtain ⟨ha,hb⟩ := box_test.mp w.property
  rw [layers,Finset.mem_Icc]; specialize hh i; specialize hp i; specialize ha i; specialize hb i; simp only [Pi.sub_apply]; omega
lemma paths (x : CurlBox S) (o : Lattice.Order) : (route 0 x.val o).length ≤ 8*R := by
  have ht (l' : List Axis) : (axisRoute 0 x.val l').length ≤ l'.length * (2*R) := by
    induction l' with
    | nil => simp [axisRoute]
    | cons i v ih =>
      have hh := (box_iff_layers ..).mp x.property i
      rw [layers,Finset.mem_Icc] at hh
      rw [show axisRoute 0 x.val (i::v)=straight i (x.val i) ++ axisRoute 0 x.val v by simp [axisRoute], List.length_append,List.length_cons, Nat.add_mul,one_mul, add_comm];
      apply Nat.add_le_add ih; unfold straight; rw [List.length_replicate]; omega
  apply (ht (allAxes o)).trans_eq; simp [allAxes]; ring
lemma route_displaced (a b : Cover) (v : Lattice.Order) : route a b v = route 0 (b-a) v := by simp [route,axisRoute]

lemma patch_ratio : (Fintype.card (CurlBox S):ℝ)/(Fintype.card s:ℝ) ≤ (2:ℝ)^4 := by
  have hx : 0 < (Fintype.card s:ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hx).mpr; rw [cites S,Fintype.card_coe,Pressure.box_length,card_layers,← mul_pow]; push_cast; gcongr; linarith

lemma rolling {α : Type*} [Fintype α] [Nonempty α] (g : α→Site c→ℝ) (r' : ℝ) (h : ∀ i,rlen (g i) ≤ r') :
    rlen (fun e => avg fun i => g i e) ≤ r' := by
  have he (X : Finset α) : rlen (∑ i∈X,g i) ≤ ∑ _i∈X,r' := by
    classical
    induction X using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact ell_zero.le
    | insert i x hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (ell_tri ..).trans (add_le_add (h i) ih)
  have hx := mul_le_mul_of_nonneg_left (he Finset.univ) (show 0 ≤ (Fintype.card α:ℝ)⁻¹ by positivity)
  have hm : (fun e => avg fun i => g i e) = fun e => (Fintype.card α:ℝ)⁻¹ * (∑ i,g i) e := by ext i; simp only [avg,smul_eq_mul,Finset.sum_apply]
  rw [hm,rconstant (x:=∑ i,g i) (by positivity)]; exact hx.trans_eq (avg_const (n:=α) _)

lemma couple {η : ℝ} {T : Purse ι (Site f)} (h : tollRate T L η) (he : 0 < η) (hc : T.cap=(l:ℝ)^2)
    (v : ι→Dir G f) (ht : Linkbill L T v) (a : Dir G f) (ha : ‖a‖ ≤ 1) (n : ℕ) (q : Finset ι) (hq : q.card ≤ n) :
    (cap S T).Many q v (line S) a ((2:ℝ)^4*walkCash G j n η) := by
  let P := cap S T; let C := walkCash G j n η; have hC := (cash_pos G j n η).le
  let w (x : Site c) (y : cargo S) := bill q v (line S x y) a
  let V (z : CurlBox S×Lattice.Order) (x : Site c) (u : s) := bill q v (Logfee.transport (route 0 z.1.val z.2) (atPoint S x u)) a
  have hs z : P.Spend q (V z) C := stroll S h he hc v ht a ha n q hq _ (paths S z.1 z.2)
  let D (u v : s) : CurlBox S := ⟨v.val-u.val,fits S u v⟩
  have hh (x : Site c) (u : cargo S) : w x u=V (D u.1 u.2.1,u.2.2) x u.1 := by unfold w V D line; rw [route_displaced (u.1.val) (u.2.1.val)]
  change P.Spend q w _; refine ⟨by positivity,fun hp i k => ?_,fun hp => ?_⟩
  · rw [hh]; apply ((hs (D k.1 k.2.1,k.2.2)).2.1 hp i k.1).trans
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hC (by norm_num)) (P.target_pos _)
  let T' (z : CurlBox S×Lattice.Order) (x : Site c) (u : s) := P.price q x*‖V z x u‖
  let b z (x : Site c) := avg fun u => T' z x u
  let Y := Fintype.card (CurlBox S)
  let r₀ : ℝ := Y / (Fintype.card s:ℝ)
  have hi (x : Site c) : avg (fun u => P.price q x*‖w x u‖) ≤ r₀*avg (fun k => b k x) := by
    let N : s→(s × Lattice.Order)→ℝ := fun u p => P.price q x*‖w x (u,p)‖
    have hb u : ∑ k, N u k ≤ ∑ z, T' z x u := by
      let g (p : s × Lattice.Order) := (D u p.1, p.2)
      have hx : Injective g := by
        rintro ⟨a,i⟩ ⟨b,y⟩ h; refine Prod.ext (Subtype.ext ?_) (show i=y from (congr_arg (fun z : CurlBox S × Lattice.Order => z.2) h))
        exact sub_left_injective (congr_arg Subtype.val (congr_arg Prod.fst h))
      rw [show ∑ k, N u k=∑ z∈Finset.univ.image g,T' z x u by
        rw [Finset.sum_image (fun v _ p _ he => hx he)]; refine Finset.sum_congr rfl fun p _ => ?_; unfold N T'; rw [hh]]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)
    rw [show avg (fun u => P.price q x*‖w x u‖)=avg (fun i => avg (N i)) from poolAverage ..]
    unfold avg
    simp only [smul_eq_mul, ← Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u _ => hb u))
      (by positivity)) (by positivity : 0 ≤ (Fintype.card s:ℝ)⁻¹)).trans_eq
    unfold b avg r₀ Y; rw [Finset.sum_comm]; simp_rw [smul_eq_mul, ← Finset.mul_sum];
    rw [Fintype.card_prod,Fintype.card_prod]
    haveI : Nonempty (CurlBox S) := ⟨⟨0,center_box _⟩⟩
    field_simp; push_cast; ring
  apply (rless (house P q w) hi).trans
  haveI : Nonempty (CurlBox S) := ⟨⟨0,center_box _⟩⟩
  have hg : 0 ≤ r₀ := by unfold r₀; positivity
  rw [rconstant (x:=fun i => avg fun k => b k i) hg]
  apply (mul_le_mul_of_nonneg_left (rolling b _ (fun z => (hs z).2.2 hp)) hg).trans
  exact (mul_le_mul_of_nonneg_right (patch_ratio S) (mul_nonneg (mul_nonneg P.rooted hC) (P.target_pos _))).trans_eq (by ring)
end both
end Yard
end YM.AnalyticNext.QuarticMatch.Estimate
