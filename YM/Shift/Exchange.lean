import YM.Shift.Swap

/-!
# Usability consumer: two germs, relative edge and Lorentz shards

Read partial boundaries on all compactly supported Schwartz tests (not
words), and all spectators. Exit to locality via supports including unbounded-
word probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Filter Set Function Distribution MeasureTheory Mink Probe Metric Surface
open scoped Topology ENNReal InnerProductSpace ContDiff unitInterval
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ} {W : Surface S} {D : ∀ i : ℕ, Blanket i}

namespace NearPair

def plain (x : Points n) (t : ℝ) := points fun i => position (spatial (x i)) (t*YM.time (x i))
variable (P : NearPair n)
@[simp] lemma tip (x : Points n) : plain x 1=x := by ext1; simp [plain]
lemma cont_plain (x : Points n) : Continuous (plain x) := by
  change Continuous fun t : ℝ => WithLp.toLp 2 (fun i => position _ _)
  simp_rw [show position = _ from funext fun x => funext fun t => (Mink.combine_at x t).symm]
  fun_prop
lemma north {x : Points n} (h : x∈P.gap) (t : unitInterval) : plain x t ∈ P.gap := by
  rw [gap, Set.mem_setOf,lateral] at h ⊢
  simp_rw [sub_eq_add_neg,clock_add,clock_neg,Mink.rest_add,Mink.rest_neg] at h ⊢
  simp only [plain, points_apply,time_position,spatial_position]
  rw [←mul_neg,←mul_add,abs_mul,abs_of_nonneg t.property.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) t.property.2) h

structure Panes (X : Aurora W D) (v : Fin n → S.Union) (y : Heights n) where
  permitted : P.Fleck y
  original (x : Points n) : x∈P.gap→ Pane (X.emit v) (tube n) (glow x (dawn y))
  tilted (x : Points n) : x∈P.gap→ Pane ((X.emit (v ∘ P.s)) ∘ P.name) (P.name ⁻¹' tube n) (glow x (dawn y))

variable {P} {y : Heights n} {X : Aurora W D} {v : Fin n → S.Union} (B : P.Panes X v y)
/-- On-Slice Taylor agreement; a substantive port; not implied by equality just at t=0 values! -/
def Panes.sameGround : Prop := ∀ x (h : x∈P.gap), (∀ i : Fin n, YM.time (x i)=0) →
    (B.original x h).extendF =ᶠ[𝓝 (glow x (dawn y))] (B.tilted x h).extendF

theorem Panes.reaches (hx : B.sameGround) (x : Points n) (p : x∈P.gap) :
    (B.original x p).extendF =ᶠ[𝓝 (glow x (dawn y))] (B.tilted x p).extendF := by
  have HH : Continuous (@name _ P) := (home n).comp ((P.switch.continuous.comp (cont_Re n)).prodMk (P.switch.continuous.comp (cont_sh n)))
  let q (t : unitInterval) := glow (plain x t) (dawn y)
  let w i := B.original _ (P.north p i)
  let z i := B.tilted _ (P.north p i)
  have he := Pane.propagate (south n) ((south n).preimage HH) q ((home n).comp
    (((cont_plain x).comp continuous_subtype_val).prodMk continuous_const))
    (fun t => ⟨B.permitted.first _,B.permitted.second _⟩) w z 0 1
  have hy := he.1 (hx _ _ (by simp [plain]))
  change (B.original (plain x 1) _).extendF =ᶠ[𝓝 (glow (plain x 1) (dawn y))] (B.tilted (plain x 1) _).extendF at hy
  let R (v : P.gap) : Prop := (B.original v.val v.2).extendF =ᶠ[𝓝 (glow v.val (dawn y))] (B.tilted v.val v.2).extendF
  change R (⟨x,p⟩ : P.gap); change R ⟨plain x 1,P.north p 1⟩ at hy
  rwa [show (⟨plain x 1,P.north p 1⟩ : P.gap)=(⟨x,p⟩ : P.gap) from Subtype.ext (tip x)] at hy

def flipW {n} (Q : Distn (Points n)) (P : NearPair n) := Q.comp (along (P.switch).toContinuousLinearEquiv)

/-- local realization from each pane (full argument). Both at original x,
after change of names in tilted contour including positions and tests. -/
structure Panes.Forms : Prop where
  body (x : Points n) (hx : x∈P.gap) : ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
    (D n).partialD (W.W n v) (dawn y) f= ∫ i, (B.original x hx).extendF (glow i (dawn y))*f i
  prime (x : Points n) (hx : x∈P.gap) : ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
    flipW ((D n).partialD (W.W n (v ∘ P.s)) (P.switch (dawn y))) P f= ∫ i,(B.tilted x hx).extendF (glow i (dawn y))*f i

theorem Panes.forgets (hp : B.sameGround) (hx : B.Forms) : IsVanishingOn (fun i =>
    ((D n).partialD (W.W n v) (dawn y)-flipW ((D n).partialD (W.W n (v ∘ P.s)) (P.switch (dawn y))) P) i) P.gap := by
  let Q := (D n).partialD (W.W n v) (dawn y)
  let R := flipW ((D n).partialD (W.W n (v ∘ P.s)) (P.switch (dawn y))) P
  apply (Distn.general_open (Q-R) P.open_gap).2
  apply Set.disjoint_left.2
  intro x H hI
  obtain ⟨r,hr,hR⟩ := hx.body x H
  obtain ⟨s,hs,hS⟩ := hx.prime x H
  let g (i : Points n) := glow i (dawn y)
  have hv : Continuous g := (home n).comp (continuous_id.prodMk continuous_const)
  obtain ⟨k,hk,ht⟩ := Metric.mem_nhds_iff.mp ((hv.tendsto x).eventually (B.reaches hp x H))
  let t := min k (min r s)
  have he := (mem_dsupport_iff_not_isVanishingOn x).mp hI (ball x t) (mem_ball_self (lt_min hk (lt_min hr hs))) isOpen_ball
  apply he; apply (Distn.from_compact (Q-R)).2
  intro f hl hf; change Q f-R f=0; apply sub_eq_zero.2
  rw [show Q f= _ from hR f hf (hl.trans (ball_subset_ball ((min_le_right ..).trans (min_le_left r s)))),
    show R f= _ from hS f hf (hl.trans (ball_subset_ball ((min_le_right ..).trans (min_le_right r s))))]
  classical
  apply integral_congr_ae; filter_upwards with i
  by_cases h : f i=0
  · simp [h]
  rw [show (B.original x H).extendF (g i)= _ from ht (ball_subset_ball (min_le_left k (min r s)) (hl (subset_tsupport _ h)))]

theorem actor (X : Aurora W D) (v : Fin n → S.Union) (P : NearPair n) (p : (D n).Modified)
    (hc : ∀ u : Fin n → S.Union, dsupport (Distn.fourier (W.W n u)) ⊆ coneM n)
    (h : ∃ y : ℕ → Heights n, Tendsto (dawn ∘ y) atTop (𝓝 0) ∧
      ∀ m : ℕ, ∃ B : P.Panes X v (y m), B.sameGround ∧ B.Forms) : IsVanishingOn (fun f =>
    (W.W n v - flipW (W.W n (v ∘ P.s)) P) f) P.gap := by
  obtain ⟨y,hy,hh⟩ := h
  choose B hb hB using hh
  have he : Tendsto (dawn ∘ y) atTop (𝓝[shores n] 0) := tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall (fun i => (B i).permitted.here)⟩
  have ht : Tendsto (fun i => P.switch (dawn (y i))) atTop (𝓝[shores n] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun i => (B i).permitted.there)⟩
    simpa only [Function.comp_def,map_zero] using (P.switch.continuous.tendsto 0 |>.comp hy)
  intro f hf
  let t : Joint n := along (P.switch).toContinuousLinearEquiv f
  have ha := ((D n).tends p (W.W n v) f _ (flat _)).tendsto.comp he
  have hw := ((D n).tends p (W.W n (v ∘ P.s)) t _ (flat _)).tendsto.comp ht
  change W.W n v f-W.W n _ _=0
  apply sub_eq_zero.2
  rw [(D n).flatD p (hc v)] at ha
  rw [(D n).flatD p (hc _)] at hw
  exact tendsto_nhds_unique_of_eventuallyEq ha hw (Eventually.of_forall (fun i =>
    sub_eq_zero.mp ((B i).forgets (hb i) (hB i) f hf)))
end NearPair

def Actor (W : Surface S) : Prop := ∀ n (v : Fin n → S.Union) (P : NearPair n), IsVanishingOn (fun f =>
    (W.W n v - P.flipW (W.W n (v ∘ P.s))) f) P.gap
end YM.Boundary
