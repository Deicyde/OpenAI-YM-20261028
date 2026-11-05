import YM.RemainderComparison.Access.Pulse
import YM.RemainderComparison.Gaussian.Bills

/-!
 # Interior germs for marked/conditional AUX calculations.

 In `Cloud U` the function U AFTER rendering is the INTEGRAND (relative on
 analytic chart). Full model determined independently (stationary Gaussian
 moments of any fixed order, full field-dependent normalization after that).
 Does not call or assume asymptotic expansion of S.push; do not infer it
 from germ estimates without INSURING the domain, lower bound and complement!
 The uncut germ at unrestricted z really matters. Use Lift for negative
 explicit exponents b on good-domain terms of stipulated valuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- open, includes the fiber at 0 when `v > 0`. Vertical costs on actual
 parameter marked germ will always purchase this much interior; not implying
 any input is analytic on the whole gauge domain or any chart curvature
 displacements beyond those listed. -/
def patch (E : Type) [NormedAddCommGroup E] (v u : ℝ) := ball (0:ℝ) v ×ˢ ball (0:E) u
omit [NormedSpace ℝ E] in
lemma patch_open (v u : ℝ) : IsOpen (patch E v u) := isOpen_ball.prod isOpen_ball
omit [NormedSpace ℝ E] in
lemma patch_test (v u : ℝ) (x : ℝ×E) : x∈patch E v u ↔ ‖x.1‖<v ∧ ‖x.2‖<u:= and_congr mem_ball_zero_iff mem_ball_zero_iff
variable {n j m k : ℕ} {v v' u u' x t D D' C C' : ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι
variable {U : ℝ×E → Poll.Body ι → F} {V : ℝ×E → Poll.Body ι → ℝ} {a : ℝ×E}
omit [NormedSpace ℝ E] in
lemma patch_mono (h : v'≤v) (hp : u'≤u) : patch E v' u' ⊆ patch E v u := Set.prod_mono (ball_subset_ball h) (ball_subset_ball hp)
omit [NormedSpace ℝ E] in
lemma patch_zero (h : a∈patch E v u) : 0<v ∧ 0<u := by rw [patch_test] at h; exact ⟨(norm_nonneg _).trans_lt h.1,(norm_nonneg _).trans_lt h.2⟩
lemma keeps (h : a∈patch E v u) (hp : t∈Set.Icc 0 1) : Trace.crossing t a∈patch E v u := by
  have hh := (patch_test ..).1 h; rw [patch_test]; refine ⟨?_,hh.2⟩
  change ‖t*a.1‖ < _; rw [norm_mul,Real.norm_of_nonneg hp.1]; exact (mul_le_of_le_one_left (norm_nonneg _) hp.2).trans_lt hh.1

variable (U) in
/-- Germ restricted to the analytic-interior cut and transverse chart. -/
structure Picture (D v u : ℝ) (n : ℕ) (C : ℝ) : Prop where
  expense : 0 ≤ C
  cut : ∀ x∈patch E v u, StronglyMeasurable ((closedBall (0:Poll.Body ι) D).indicator (U x))
  budget : ∀ x∈patch E v u,∀ z,‖z‖≤D → Brush n C 1 (fun x=> U x z) x
variable (U) in
/-- Input spec for Tayloring core Gauss moment integrals.
 Narrower `satellite` only used at b=0 for removing the fixed truncation
 from Taylor coefficients, never claiming all b and no tau extension in
 β. High jets *at* b=0 (not off-axis) charged by a true polynomial in z.
-/
structure Cloud (D v u : ℝ) (n m : ℕ) (C : ℝ) : Prop extends Picture U D v u n C where
  view : ∀ y : E, ‖y‖<u → ∀ z, Brush n (C*vat m z) 1 (fun x=> U x z) (0,y)
  satellite : ∀ R : ℝ, 0≤R → ∃ v'>0,∃ C', Picture U R v' u n C'


def velvet (U : ℰ → Ξ → F) (D : ℝ) (x : ℰ) := (closedBall (0:Ξ) D).indicator (U x)

omit [DecidableEq ι] in
lemma Picture.mend (h : Picture U D v u n C) (hp : n≥j) (hb : v'≤v) (hc:u'≤u) (hC:C ≤ C') : Picture U D v' u' j C' :=
  ⟨h.expense.trans hC, fun i hi=> h.cut i (patch_mono hb hc hi), fun i hi z hz=> (h.budget i (patch_mono hb hc hi) z hz|>.smaller hp).climb hC le_rfl⟩

section localP
omit [DecidableEq ι]
lemma vat_mono (hp:j≤n) (z:Ξ) : vat j z ≤ vat n z := pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) hp
lemma vat_nonneg (k:ℕ) (z:Ξ) : 0 ≤ vat k z := by unfold vat; positivity
lemma Cloud.raise (h : Cloud U D v u n j C) (hp : m≤n) (hb : v'≤v) (hc:u'≤u) (hd:C ≤ C') (hj : j≤k) : Cloud U D v' u' m k C' := by
  refine ⟨Picture.mend h.toPicture hp hb hc hd,fun x hx z=>?_ ,fun d he=>?_⟩
  · exact ((h.view x (hx.trans_le hc) z).smaller hp).climb (mul_le_mul hd (vat_mono hj z) (vat_nonneg _ _) (h.expense.trans hd)) le_rfl
  obtain ⟨b,hb,T,hT⟩:= h.satellite d he
  exact ⟨b,hb,T,hT.mend hp le_rfl hc le_rfl⟩
lemma Picture.stamp (h : Picture U D v u n C) (hx : a ∈ patch E v u) (z:Ξ) : Brush n C 1 (fun x=> velvet U D x z) a := by
  by_cases hp : z∈closedBall (0:Ξ) D
  · exact (h.budget _ hx z (mem_closedBall_zero_iff.mp hp)).shimmy (Eventually.of_forall fun i=> indicator_of_mem hp _)
  exact ((Brush.certified (k:=n) zero_le_one (x:=a) (0:F)).climb (by simpa using h.expense) le_rfl).shimmy (Eventually.of_forall fun i=> indicator_of_notMem hp _)
variable [FiniteDimensional ℝ E]
lemma Picture.vital (h : Picture U D v u n C) (hx : a∈patch E v u) :
    StronglyMeasurable (JetF (velvet U D) n a) :=
  Meristem.legs (f:=fun z x=> velvet U D x z) (patch_open ..) (fun z _ hx=> (h.stamp hx z).smooth) h.cut le_rfl hx
lemma Cloud.twilight (h : Cloud U D v u n j C) {x : E} (hx : ‖x‖ < u) (hm : k≤n) :
    StronglyMeasurable (JetF U k (0,x)) := by
  let f := JetF U k (0,x)
  let g (R:ℕ) := JetF (velvet U (R:ℝ)) k (0,x)
  have hh (R:ℕ): StronglyMeasurable (g R) := by
    obtain ⟨v',hp,A,h⟩:= h.satellite (R:ℝ) (Nat.cast_nonneg _)
    exact (h.mend hm le_rfl le_rfl le_rfl).vital ⟨mem_ball_self hp, mem_ball_zero_iff.mpr hx⟩
  apply stronglyMeasurable_of_tendsto atTop hh
  refine tendsto_pi_nhds.mpr fun i=> tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖i‖] with R hR
  exact congr_arg (fun f=> iteratedFDeriv ℝ k f (0,x)) (funext fun j=> Eq.symm (indicator_of_mem (mem_closedBall_zero_iff.mpr hR) _))
lemma Cloud.fine (h : Cloud U D v u n j C) {x : E} (hx : ‖x‖ < u) (hm : k≤n) :
    StronglyMeasurable fun z=> coefficient (fun x=> U x z) k x := by
  let L:= ContinuousMultilinearMap.apply ℝ (fun _:Fin k=> ℰ) F (fun _=> (1,0))
  exact StronglyMeasurable.smul (stronglyMeasurable_const (b:=(k.factorial:ℝ)⁻¹)) (L.continuous.comp_stronglyMeasurable (h.twilight hx hm))
end localP
end YM.RemainderComparison.Germ
