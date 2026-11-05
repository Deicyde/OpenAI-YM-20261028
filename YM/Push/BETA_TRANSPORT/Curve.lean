import YM.Bid.Craft
import YM.Push.BETA_TRANSPORT.Activity
import YM.Push.BETA_TRANSPORT.Block

/-!
# Passing the **input** band tests to continuous unmarked push

For the exact `Curve` + `Lives` input from `Shoot`. Parameter x is not assumed
to be (Q x).beta, nor the only influence on regular or forced coefficients.
The actual evaluators have parameter-dependent values even at fixed U, with
hard thresholds on U. This component pays a local bound on a WHOLE gas (only
at fixed period), not on a single tuple. No positivity assumed for a general
lawful Rep on an arbitrary input band.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG RG.Activities RG.Shoot MeasureTheory Filter Function Set
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff
variable {n : Side} {G : Gauge} {P : BudgetPoint} {D : PathData G} {A : Clip}

def kinetic (D : PathData G) (A : Clip) (P : BudgetPoint) (U : Config G n) :=
  (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed,
    ((∑ p, D.baseTerm A P (pull s 0 U) p) + ∑ x : Site n,
      (PathData.atomSeries D.cubic P (pull s 0 U) x + PathData.atomSeries D.quartic P (pull s 0 U) x))
lemma channels_split (U : Config G n) (b : ℝ) :
    D.inChannels A P b U = b * kinetic D A P U + D.inChannels A P 0 U := by
  simp only [PathData.inChannels,PathData.principal,kinetic,zero_mul,zero_add,Finset.sum_add_distrib,← Finset.mul_sum]; ring
lemma kinetic_env {σ C Λ : ℝ} (h : D.Bounds A σ C Λ) : Envelope (kinetic (n:=n) D A P) := by
  rw [show kinetic (n:=n) D A P = (fun U => D.inChannels A P 1 U + -D.inChannels A P 0 U) from
    funext fun U => by rw [channels_split U 1]; ring]
  exact (PathData.channels_env h _ 1).add (PathData.channels_env h _ 0).neg

/-- Small part of the tested (band-free) recipe input or output at one level.
Only parameter-independent base data required; size witnesses not compared here. -/
structure FixedRepData (D : PathData G) (A : Clip) (P : BudgetPoint) (T : ℝ → Rep G n) (s : Set ℝ) : Prop where
  path x : x∈s → (T x).path = D
  clip x : x∈s → (T x).clip = A
  budget x : x∈s → (T x).p = P
  lawful x : x∈s → ∃ σ C Λ δ w : ℝ, (T x).Lawful σ C Λ δ w

lemma lives_fixed {a : Levels G} {R : Recipe a} {N m p : ℕ} {s : Set ℝ} {T : ℝ → Rep G (a.S.side m p)}
    (h : ∀ x ∈ s, Lives R N m p (T x)) : FixedRepData (R.path N m) (a.params m).clip (a.budget m) T s :=
  ⟨fun x hx => (h x hx).path,fun x hx => (h x hx).clip,fun x hx => (h x hx).point,
    fun x hx => ⟨_,_,_,_,_,(h x hx).valid⟩⟩

/-- Exactly the last three fields of `Curve`. Sufficient conditions in Census. -/
structure StableActivities (P : BudgetPoint) (T : ℝ → Rep G n) (s : Set ℝ) : Prop where
  reg : ∀ x ∈ s, ∀ y ∈ s, (T x).activities.reg = (T y).activities.reg
  forced : ∀ x ∈ s, ∀ y ∈ s, (T x).activities.forced = (T y).activities.forced
  continuous : ∀ ε > 0, ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, deviation P (T x).activities (T y).activities ε

variable {s : Set ℝ} {T : ℝ → Rep G n}
lemma curve_stable (h : Curve P T s) : StableActivities P T s := ⟨h.reg,h.forced,h.continuous⟩

namespace FixedRepData
variable (h : FixedRepData D A P T s)
include h
lemma paths {x : ℝ} (hx : x ∈ s) : ∃ σ C Λ, D.Bounds A σ C Λ := by
  obtain ⟨σ,C,Λ,_,_,hv⟩ := h.lawful x hx
  exact ⟨σ,C,Λ,by rw [← h.path x hx, ← h.clip x hx]; exact hv.paths⟩
lemma valid {x : ℝ} (hx : x ∈ s) : ∃ δ w, (T x).activities.Valid P δ w := by
  obtain ⟨_,_,_,δ,w,hv⟩ := h.lawful x hx
  exact ⟨δ,w,by rw [← h.budget x hx]; exact hv.labels⟩
lemma exponent_eq {x : ℝ} (hx : x ∈ s) (U : Config G n) : (T x).exponent U =
    (T x).v * Fintype.card (Site n) - ((T x).beta * kinetic D A P U + D.inChannels A P 0 U) -
        (T x).activities.additive P U := by simp [Rep.exponent,h.path x hx,h.budget x hx,h.clip x hx,
          channels_split U (T x).beta]
lemma envelope {x : ℝ} (hx : x ∈ s) : Envelope (T x).eval := by
  obtain ⟨_,_,_,_,_,hr⟩ := h.lawful x hx
  exact (T x).envelope hr
lemma uniform_activities (hc : StableActivities P T s) {x : ℝ} (hx : x ∈ s) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ y in 𝓝[s] x, ∀ U, ‖(T x).activities.additive P U - (T y).activities.additive P U‖ < ε ∧
      ‖(T x).activities.gas P U - (T y).activities.gas P U‖ < ε := by
  obtain ⟨_,_,hv⟩ := h.valid hx
  obtain ⟨k,hk,hK⟩ := K_total hv.boundK
  let B := Real.exp (2*((∑' i, k i)+1)); let δ := min 1 (ε / (1+B))
  have hB : 0 < B := Real.exp_pos _
  have hp : 0 < 1+B := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos he hp)
  have hl : δ*(1+B) ≤ ε := (le_div_iff₀ hp).mp (min_le_right ..)
  filter_upwards [hc.continuous δ hδ x hx,self_mem_nhdsWithin] with y hy hy' U
  obtain ⟨_,_,hw⟩ := h.valid hy'
  obtain ⟨ha,hb⟩ := deviation_diff hv hw (fun i => (hK i).2) hk (hc.reg x hx y hy') (hc.forced x hx y hy')
    hy hδ (min_le_left ..) U
  change _ ≤ δ*B at hb
  exact ⟨ha.trans_lt (by nlinarith), hb.trans_lt (by linarith)⟩
lemma continuous_activities (hc : StableActivities P T s) (U : Config G n) :
    ContinuousOn (fun x => (T x).activities.additive P U) s ∧ ContinuousOn (fun x => (T x).activities.gas P U) s := by
  constructor <;> (intro x hx; apply Metric.tendsto_nhds.mpr; intro ε he
                   filter_upwards [h.uniform_activities hc hx ε he] with y hy
                   rw [dist_eq_norm, norm_sub_rev]; first | exact (hy U).1 | exact (hy U).2)
lemma continuous_eval (hc : Curve P T s) (U : Config G n) : ContinuousOn (fun x => (T x).eval U) s := by
  have ⟨ha,hb⟩ := h.continuous_activities (curve_stable hc) U
  refine ContinuousOn.congr (((hc.v.mul (continuousOn_const (c:=(Fintype.card (Site n):ℝ))) |>.sub
    (hc.beta.mul (continuousOn_const (c:=kinetic D A P U)) |>.add (continuousOn_const (c:=D.inChannels A P 0 U)))).sub ha).rexp.mul hb) (fun x hx => ?_)
  rw [Rep.eval, h.exponent_eq hx,h.budget x hx]; rfl
lemma local_bound (hc : Curve P T s) {x : ℝ} (hx : x ∈ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝[s] x, ∀ U, ‖(T y).eval U‖ ≤ C := by
  obtain ⟨_,_,_,hv⟩ := h.paths hx
  obtain ⟨_,_,hw⟩ := h.valid hx
  obtain ⟨B,hB⟩ := (kinetic_env (P:=P) (n:=n) hv).cost
  obtain ⟨D₀,hD⟩ := (PathData.channels_env (n:=n) hv P 0).cost
  obtain ⟨e,he⟩ := (ESeries hw).bound
  obtain ⟨k,hk⟩ := (gasSeries hw).bound
  let ed := (|(T x).v|+1)*(Fintype.card (Site n):ℝ) + ((|(T x).beta|+1)*B + D₀) + (1+e)
  have hp : 0 < 1 + k := lt_add_of_pos_of_le zero_lt_one ((norm_nonneg _).trans (hk 1))
  refine ⟨Real.exp ed * (1+k),mul_pos (Real.exp_pos _) hp,?_⟩
  filter_upwards [h.uniform_activities (curve_stable hc) hx 1 zero_lt_one,
    hc.v x hx (eventually_abs_bound _),hc.beta x hx (eventually_abs_bound _),self_mem_nhdsWithin] with y hy h1 h2 h3 U
  have hs (f : ℝ → ℝ) (B : ℝ) (hb : ‖f x‖ ≤ B) (hy : ‖f x-f y‖ < 1) : ‖f y‖ ≤ 1+B := by
    have he := norm_sub_le (f x) (f x-f y); rw [sub_sub_cancel] at he; linarith
  have ha := hs (fun t => (T t).activities.additive P U) e (he U) (hy U).1
  have hb := hs (fun t => (T t).activities.gas P U) k (hk U) (hy U).2
  have ht : (T y).exponent U ≤ ed := by
    rw [h.exponent_eq h3]; apply (le_abs_self _).trans
    exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add
      (by rw [norm_mul,Real.norm_natCast]; gcongr; exact h1) ((norm_add_le ..).trans
      (add_le_add (by rw [norm_mul]; exact mul_le_mul h2 (hB U) (norm_nonneg _) (by positivity)) (hD U))))) ha)
  rw [Rep.eval,h.budget y h3,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul (Real.exp_le_exp.mpr ht) hb (norm_nonneg _) (Real.exp_pos _).le
lemma continuous_push {m : Side} (S : StepData m n) (hS : S.patch.Branches S.kernel G) (hc : Curve P T s) :
    ContinuousOn (fun p : ℝ × Config G m => S.push (T p.1).beta (T p.1).eval p.2) (s ×ˢ univ) := by
  intro p hp
  have hx : p.1∈s := hp.1
  have hv : Tendsto Prod.fst (𝓝[s ×ˢ univ] p) (𝓝[s] p.1) := continuousWithinAt_fst.tendsto_nhdsWithin fun _ h => h.1
  obtain ⟨C,_,hC⟩ := h.local_bound hc hx
  exact (push_continuousWithinAt S hS ((hc.beta p.1 hx).tendsto.comp hv) continuousWithinAt_snd ((h.envelope hx).integrable _)
    (hv.eventually (eventually_of_mem self_mem_nhdsWithin <| fun x hh => (h.envelope hh).meas.aestronglyMeasurable))
    (Eventually.of_forall fun U => (h.continuous_eval hc U p.1 hx).tendsto.comp hv)
    (integrable_const C) ((hv.eventually hC).mono fun x hh => Eventually.of_forall hh)).2
end FixedRepData
end YM.Push.BetaTransport
