import YM.AnalyticNext.QUARTIC_MATCH.Cells.Entry
import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Review
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Gradient
import YM.Next.PHASE.Seats

/-!
# Axis coordinates from any stationary charts

Get uniform real costs. No contour gauge assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

lemma room {X : Type*} [NormedAddCommGroup X] {P : X→Prop} (h : ∀ᶠ x in 𝓝 0,P x) : ∃ r : ℝ,0<r ∧ ∀ q : X, ‖q‖≤r → P q := by
  obtain ⟨r,hp,ht⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨r/2,half_pos hp,fun q hq => ht (Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith))⟩
lemma ceilingD {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ X] [NormedSpace ℝ Y]
    [ProperSpace X] (f : X→Y) (r : ℝ) (h : ∀ x, ‖x‖≤ r → ContDiffAt ℝ ω f x) (n : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ x, ‖x‖ ≤ r → ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  let A : Set X := Metric.closedBall 0 r
  have he x (he : x∈A) : ContDiffAt ℝ ω f x := h x ((dist_zero_right x) ▸ he)
  have hf : ContinuousOn (iteratedFDeriv ℝ n f) A := fun i hi => ((he i hi).continuousAt_iteratedFDeriv le_top).continuousWithinAt
  obtain ⟨M,hm⟩ := (isCompact_closedBall (0:X) r).bddAbove_image hf.norm
  exact ⟨max 1 M,le_max_left ..,fun x hx => (hm (Set.mem_image_of_mem _ (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])))).trans (le_max_right ..)⟩

namespace Showroom
open Green (wt)
section along
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio)
abbrev outer (S : StepData c f) (G : Gauge) (t : ℝ) (i : Site f) : Ticket (Dir G c) := Amount t (S.ratio.embed ∘ Prod.fst) i
abbrev charge (H : Forest S.ratio) (G : Gauge) (t : ℝ) (i : Site f) : Ticket (AxisChart G H) := Amount t (fun p : H.Free=> p.val.1) i
abbrev On (H : Forest S.ratio) (G : Gauge) (t : ℝ) (i : Site f) : Ticket (ChartVars H G) := fun x c => outer S G t i x.1 c ∧ charge S H G t i x.2 c

lemma onward (t : ℝ) {x : ChartVars H G} {i : Site f} {p : ℝ} (h : On S H G t i x p)
    (s : ℝ) (he : t ≤ s) (hp : 0 ≤ p) : On S H G s i x p := ⟨seek he hp h.1,seek he hp h.2⟩
lemma move (t : ℝ) {x : ChartVars H G} {i : Site f} {p : ℝ} (h : On S H G t i x p)
    (z : Site f) (hp : 0 ≤ t) (hq : 0 ≤ p) : On S H G t z x (p*wt t z i) := ⟨Amount.origin h.1 z hp hq,Amount.origin h.2 z hp hq⟩
lemma stamped (t : ℝ) (hp : 0≤t) (x : ChartVars H G) (i : Site f) : On S H G t i x ‖x‖ :=
    ⟨Amount.elevate (Amount.constant t hp i x.1) (le_max_left ..),Amount.elevate (Amount.constant t hp i x.2) (le_max_right ..)⟩

def collects (e : Edge (Site f)) : ChartVars H G →L[ℝ] G.Color × G.Color :=
    if h : e∈ H.trunks then 0 else
    ((ContinuousLinearMap.proj (R:=ℝ) (⟨e,h⟩:H.Free)).comp (ContinuousLinearMap.snd ..)).prod (
    if S.ratio.parent (e.1+step e.2)=S.ratio.parent e.1 then 0 else (ContinuousLinearMap.proj (R:=ℝ) (S.ratio.parent e.1,coord e.2)).comp (ContinuousLinearMap.fst ..))

lemma presents (e : Edge (Site f)) (x : ChartVars H G) :
    live H x e=G.lieExp (collects S H e x).1 * G.lieExp (collects S H e x).2 := by
  unfold collects; split
  · next he => rw [show live H x e=1 from H.on_tree _ ⟨e,he⟩]; simp
  next he =>
    rw [show live H x e=G.lieExp (x.2 ⟨e,he⟩) * replica S.ratio (represent x.1) e from H.off_tree _ ⟨e,he⟩, replica]; split
    · simp_all
    next hz =>
      rw [represent_link]; rfl
lemma token (e : Edge (Site f)) (x : ChartVars H G) (t p : ℝ) (h : On S H G t e.1 x p) (ht : 0 ≤ t) (hp : 0 ≤ p) :
    ‖collects S H e x‖ ≤ Real.exp (t*S.ratio.count.val)*p := by
  let C := Real.exp (t*S.ratio.count.val); have hc : 1≤C := Real.one_le_exp (by positivity); have hd := hp.trans (le_mul_of_one_le_left hp hc)
  unfold collects; split
  · simpa using hd
  next he =>
    have hh : ‖x.2 ⟨e,he⟩‖ ≤ p := by
      have h := h.2 ⟨e,he⟩; simpa [Green.wt] using h
    split
    · rw [ContinuousLinearMap.prod_apply]; exact max_le (hh.trans (le_mul_of_one_le_left hp hc)) ((by simp only [_root_.zero_apply,norm_zero]; exact hd) : ‖(0 : ChartVars H G→L[ℝ] G.Color) x‖ ≤ _)
    change max _ ‖x.1 (S.ratio.parent e.1,coord e.2)‖ ≤ _
    refine max_le (hh.trans (le_mul_of_one_le_left hp hc)) ((h.1 (_,coord e.2)).trans ?_)
    rw [mul_comm p]; apply mul_le_mul_of_nonneg_right _ hp; dsimp only [Function.comp_apply]; apply Real.exp_monotone; gcongr
    have hh := Corona.near S.ratio e.1; rw [separation_comm]; omega
lemma collects_le (e : Edge (Site f)) (x : ChartVars H G) : ‖collects S H e x‖ ≤ ‖x‖ := by
  simpa only [zero_mul,Real.exp_zero,one_mul] using token S H e x 0 ‖x‖ (stamped S H _ le_rfl x e.1) le_rfl (norm_nonneg _)
end along

section template
variable (G : Gauge)
def pose (x : G.Color × G.Color) := G.lieExp x.1 * G.lieExp x.2
def express (x : G.Color × G.Color) := G.plog (G.mat (pose G x))

end template

section quotes
variable {G : Gauge} {b r : ℝ} {c f : Side} (S : StepData c f) (H : Forest S.ratio)

structure Shelf (G : Gauge) (r b : ℝ) where
  pos : 0 < r
  base : 0 < b
  earns x : ‖x‖≤r → ContDiffAt ℝ ω (express G) x ∧ G.lieExp (express G x)=pose G x ∧ ‖express G x‖ ≤ b
  rates : ℕ→ℝ
  prices k : 1 ≤ rates k
  cost n x : ‖x‖≤ r → ‖iteratedFDeriv ℝ n (express G) x‖ ≤ rates n

variable (P : Shelf G r b) {x : ChartVars H G} (he : ‖x‖≤r)
include he
include P
omit he P in
lemma home (e : Edge (Site f)) (x : ChartVars H G) : axisLog H x (e.1,coord e.2)=express G (collects S H e x) := by
  rw [axisLog, express, show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply e.2, presents S H e x]; rfl
lemma makes : represent (axisLog H x)=live H x := by
  funext e; rw [represent_link, home S H]; exact (P.earns _ ((collects_le S H e x).trans he)).2.1.trans (presents S H e x).symm
lemma priced : ContDiffAt ℝ ω (axisLog H (G:=G)) x := by
  refine contDiffAt_pi.mpr ?_; rintro ⟨i,j⟩; obtain ⟨k,rfl⟩ := axisEquiv.surjective j
  rw [show (fun x : ChartVars H G=> axisLog H x (i,axisEquiv k))=express G ∘ collects S H (i,k) from funext (home S H (i,k))]
  exact ((P.earns _ ((collects_le S H _ _).trans he)).1).comp _ (ContinuousLinearMap.contDiff .. |>.contDiffAt)
lemma inside : ‖axisLog H x‖ ≤ b := by
  refine (pi_norm_le_iff_of_nonneg P.base.le).mpr ?_; rintro ⟨i,j⟩; obtain ⟨k,rfl⟩ := axisEquiv.surjective j
  rw [show axisEquiv k=coord k from rfl, home (e:=(i,k))]; exact (P.earns _ ((collects_le S H (i,k) x).trans he)).2.2

def fetch (P : Shelf G r b) (l : Side) (t : ℝ) (m) := P.rates m * (Real.exp (t*l.val))^m
omit he in
lemma fetch_pos (l : Side) (t : ℝ) (k : ℕ) : 0 ≤ fetch P l t k := mul_nonneg (zero_le_one.trans (P.prices _)) (pow_nonneg (Real.exp_pos _).le _)
lemma rapid (z : Site f) (k : ℕ) (t : ℝ) (hp : 0 ≤ t) : Costs (On S H G t z) (trials G (k*t) z) (axisLog H) x k (fetch P S.patch.L t k) := by
  intro d c hc p
  rcases p with ⟨i,j⟩; obtain ⟨m,rfl⟩ := axisEquiv.surjective j; let e : Edge (Site f) := (i,m)
  let w := wt t i z
  let L := Real.exp (t*S.patch.L.val)
  let B := collects S H (G:=G) e
  have hx (j) : ‖B (d j)‖ ≤ L*(c j*w) := token S H e (d j) t (c j*w) (move S H t (hc j).2 i hp (hc j).1) hp
    (mul_nonneg (hc j).1 (Green.wt_pos ..).le)
  let V := axisLog H (G:=G)
  have hh : iteratedFDeriv ℝ k V x d (i,coord m)=iteratedFDeriv ℝ k (express G ∘ B) x d := by
    let E : Dir G f →L[ℝ] G.Color := ContinuousLinearMap.proj (e.1,coord e.2)
    rw [show express G ∘ B=E ∘ V from funext fun i => (home S H e i).symm,E.iteratedFDeriv_comp_left (priced S H P he) le_top]; rfl
  change ‖iteratedFDeriv ℝ k V x d (i,coord m)‖ ≤ _; rw [hh, lin_rate_at _ B x ((P.earns _ ((collects_le S H e _).trans he)).1)]
  apply ((iteratedFDeriv ℝ k (express G) (B x)).le_opNorm _).trans
  have ht := P.cost k _ ((collects_le S H e _).trans he)
  apply (mul_le_mul ht (Finset.prod_le_prod (fun i _ => norm_nonneg (B (d i))) (fun i _ => hx i)) (by positivity) ((norm_nonneg _).trans ht)).trans_eq
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]; rw [Finset.card_univ, Fintype.card_fin]; unfold fetch
  change _=P.rates k*L^k*_ * wt _ i z
  rw [show wt ((k:ℝ)*t) i z=w^k from (by unfold w Green.wt; rw [← Real.exp_nat_mul]; ring_nf)]; ring
end quotes
end Showroom
end YM.AnalyticNext.QuarticMatch.Radius
