import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Volume

/-!
# A one-link noise invoice before L
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
variable {G : Gauge} {c f : Side} (S : StepData c f) {ι : Type} [DecidableEq ι]
local notation "Y" => S.patch.Points
local notation "X" => Dir G f
local notation "E" => G.Mat
local notation "L" => S.patch.L

omit [DecidableEq ι] in
lemma travelsCost {η : ℝ} {y : Axis} (hp : 0<η) {P : Purse ι (Site f)} (h : tollRate P L η)
    (p : Finset ι) (m : ℕ) (hm : p.card ≤ m) (x : Site c) : (cap S P).price p x ≤ Real.exp η^m*((cap S P).price p (x+step y)) := by
  let t := cap S P
  have hh (i) : t.toll i x ≤ Real.exp η * t.toll i (x+step y) := by
    have hs : separation (S.ratio.embed x) (S.ratio.embed (x+step y)) ≤ 1*S.patch.L.val := by
      rw [one_mul]; apply (scaled_root S.ratio ..).trans
      have hw : separation x (x+step y) ≤ 1 := (Response.by_one x (posDir y)).1
      exact (Nat.mul_le_mul_left _ hw).trans_eq (Nat.mul_one _)
    have he := enters h hp.le i _ _ _ hs
    exact he.trans ((mul_le_mul_of_nonneg_right (guide_bound S.patch.L le_rfl hp.le)
      (P.toll_pos ..).le).trans (le_of_eq (by norm_num [t,cap])))
  change (∏ i∈p,_) ≤ _
  apply (Finset.prod_le_prod (fun i _ => (t.toll_pos i x).le) (fun i _ => hh i)).trans
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Real.one_le_exp hp.le) hm) (Purse.price_pos ..).le

omit [DecidableEq ι] in
lemma relocation {H : Type} [NormedAddCommGroup H] {η C} {y : Axis} (hp : 0<η) {P : Purse ι (Site f)}
    (h : tollRate P L η) {p : Finset ι} (m : ℕ) (hm : p.card ≤ m) {β : Type} [Fintype β] [Nonempty β]
    {u : Site c → β→ H} (hb : (cap S P).Spend p u C) : (cap S P).Spend p (fun i => u (i+step y)) (Real.exp η^m*C) :=
  hb.sending (pow_nonneg (Real.exp_pos _).le _) (Equiv.addRight (step y)) fun i j => (mul_le_mul_of_nonneg_right
    (travelsCost S hp h p m hm i) (norm_nonneg (u (i+step y) j))).trans_eq (mul_assoc ..)

def allotment (a : S.SitesChoice) (x : Axis) (y : Site c) (i : Y) (u : X) := ballot S (y,x) a u i

def releaseCost (G : Gauge) (η : ℝ) (n k : ℕ) (C : ℝ) := 2^n*((2^n*(C*walkCash G k n η))*(Real.exp η^n*C))


lemma release (h : S.patch.Branches S.kernel G) (a : S.SitesChoice) (x : Axis)
    {P : Purse ι (Site f)} (v : ι→X) {η C : ℝ} (he : 0<η) (ht : tollRate P L η) (hc : P.cap=(S.patch.L.val:ℝ)^2)
    (hL : Linkbill L P v) {T : Finset ι} {n : ℕ} (hp : T.card ≤ n) (hv : ∀ U⊆T,(cap S P).Many U v (envelope S a) 0 C) :
    (cap S P).Many T v (allotment S a x) 0 (releaseCost G η n S.patch.J C) := by
  let f y i := Logfee.transport (S.repath x) (G:=G) (atPoint S y i)
  have hr : (S.repath x).length ≤ 8*S.patch.radius := by rw [StepData.repath,List.length_replicate]; unfold Patch.radius; nlinarith only
      [show (0:ℕ) < S.patch.L.val from S.patch.L.property]
  have hq (U : Finset ι) (hu : U⊆T) : (cap S P).Many U v f 0 (walkCash G S.patch.J n η) := stroll S ht he hc v hL 0 (by simp) n U ((Finset.card_le_card hu).trans hp) _ hr
  let r y i := envelope S a (G:=G) y i
  let L' := ContinuousLinearMap.mul ℝ E
  let W i k := r (i+step x) k
  let d i k ξ := L' (r i k ξ) (f i k ξ); let z := (starL ℝ (A:=E)).toContinuousLinearMap
  have he1 (i k) : ContDiffAt ℝ ω (d i k) 0 := (honest S h a i k).mul (train_rate ..).contDiffAt
  have he2 (i k) : ContDiffAt ℝ ω (W i k) 0 := honest S h a (i+step x) k
  refine Many.priced L' (fun i j => norm_mul_le ..) he1 (fun i k => (z.contDiff.contDiffAt.comp 0 (he2 i k)))
    (fun i hi => Many.priced L' (fun i j => norm_mul_le i j) (honest S h a) (fun y k => (train_rate ..).contDiffAt) (fun U hU => hv _ (hU.trans hi))
      (fun U hU => hq _ (hU.trans hi)) n ((Finset.card_le_card hi).trans hp)) ?_ n hp
  intro i hi; apply Many.edit _ he2 z (fun y => (norm_star y).le)
  exact relocation S (y:=x) he ht _ ((Finset.card_le_card hi).trans hp) (hv _ hi)

lemma pools (h : S.patch.Branches S.kernel G) (a : S.SitesChoice) (x : Axis) (y : Site c) : ContDiffAt ℝ ω (pool S (y,x) a) (0:X) :=
    ContDiffAt.sum fun _i _ => (ballot_rate S h _ _ _).const_smul _
lemma mires (h : S.patch.Branches S.kernel G) (a : S.SitesChoice) (x : Axis)
    {P : Purse ι (Site f)} (v : ι→X) {η C : ℝ} (he : 0<η) (ht : tollRate P L η) (hc : P.cap=(S.patch.L.val:ℝ)^2)
    (hL : Linkbill L P v) {T : Finset ι} {n : ℕ} (hp : T.card ≤ n) (hv : ∀ U⊆T,(cap S P).Many U v (envelope S a) 0 C) :
    (cap S P).Jets T v (fun y => pool S (y,x) a) 0 (pScale S.patch.J*releaseCost G η n S.patch.J C) := by
  apply Pays.under ((release S h a x v he ht hc hL hp hv).heavy S.patch.weight S.patch.weight_sum S.patch.weight_nonneg (pScale_ge _) (earn S))
  intro i
  have ht (k : Y) := ballot_rate S h (i,x) a k
  exact (congr_arg (fun a : G.Mat => ‖a‖) (funds_more (allotment S a x i) ht T v S.patch.weight)).le

def channel (a : S.Choices) (x : Axis) (y : Site c) (z : Dir G f) := G.mat (send S a z (y,x))
theorem hires (G : Gauge) (n j : ℕ) (η : ℝ) (hp : 0<η) : ∃ C : ℝ,0≤C ∧
    ∀ (ι : Type) [DecidableEq ι] (c f : Side) (S : StepData c f) (a : S.Choices), S.patch.J=j →
    S.patch.Branches S.kernel G → ∀ (P : Purse ι (Site f)) (v : ι→Dir G f), tollRate P S.patch.L η →
    P.cap=(S.patch.L.val:ℝ)^2 → Linkbill S.patch.L P v → ∀ T : Finset ι,T.card ≤ n →
    ∀ x, (cap S P).Jets T v (channel S a x) 0 C := by
  obtain ⟨C,hC,H⟩ := heaps G n j η hp
  let K := pScale j*releaseCost G η n j C
  obtain ⟨D,hp',D'⟩ := ordered (penny G) 1 G.focus_diff n K
  refine ⟨D,hp',?_⟩; intro ι _ c f S a he h P v ht hc hL T hT x
  let b (y : Site c) (_ : Unit) := pool S (y,x) a.1 (G:=G)
  have hh s (hs : s⊆T) : (cap S P).Many s v b 0 K := by
    unfold K; rw [← he]; exact energize (β:=Unit) (mires S h a.1 x v hp ht hc hL ((Finset.card_le_card hs).trans hT) (fun U hU =>
      H ι c f S a.1 he h P v ht hc hL U ((Finset.card_le_card (hU.trans hs)).trans hT)))
  apply Pays.under (alonePay (z:=fun i : Site c => bill T v (penny G ∘ b i ()) 0) (D' _ _ _ _ b _ _ _ T hT
    (fun i _ => pools S h a.1 x i) (fun i _ => pool_start S h _ _ ) hh))
  intro y
  refine (congr_arg (fun a : G.Mat => ‖a‖) (Estimate.germ (S:=T) (d:=v) ?_)).le
  exact (deliver S h (y,x) a).mono fun i hi => congr_arg G.mat hi
end Yard
end YM.AnalyticNext.QuarticMatch.Estimate
