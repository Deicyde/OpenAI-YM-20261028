import YM.RemainderComparison.Gaussian.Album
import YM.AnalyticNext.QUARTIC_MATCH.Residual

/-!
 # Scale valuation. Negative finite prefactors canceled in analytic chart.
 Masks inserted BEFORE the full-group integral. Use compensated factor only
 on x-interior; equality under `cleared` through real receipt, all factorials
 for uncut Gaussian prescription accounted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι]
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {n j m k i : ℕ} {v u D C A b : ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι
variable {U : ℝ × E → Poll.Body ι → F}

/-- Ordinary multiindex valuation at the original coordinates.
 Enough in nonlinear chart via Taylor on composed germ (below).
 This condition must actually hold (when using it on connected-completed
 Taylor monomials it is owned by their render producer). -/
def cleared (f : E→F) (m : ℕ) (x:E) : Prop:=
    ∀ i < m, iteratedFDeriv ℝ i f x=0
lemma chart_cleared (f : E→F) (h : cleared f m 0) (hS : ContDiffAt ℝ (↑m) f 0)
    (P : H→E) (x : H) (hx : P x=0) (hP : ContDiffAt ℝ (↑m) P x) :
    cleared (f ∘ P) m x := by
  intro i hi; let F' s:= P (x+s)
  have he : ContDiffAt ℝ (↑m) F' 0:= (show ContDiffAt ℝ (↑m) P (x+0) from (add_zero x).symm ▸ hP).comp _ (contDiffAt_const.add contDiffAt_id)
  have hx': F' 0=0:=by unfold F'; rw [add_zero,hx]
  have ht := AnalyticNext.QuarticMatch.first_comp (k:=i) (hS.of_le (by exact_mod_cast hi.le)) (fun j hj=> h j (hj.trans hi)) (he.of_le (by exact_mod_cast hi.le)) hx'
  rw [h i hi] at ht
  rw [show iteratedFDeriv ℝ i (f ∘ P) x=iteratedFDeriv ℝ i (f ∘ F') 0 from ?_,ht]
  · ext; simp
  change _ = iteratedFDeriv ℝ i (fun y => (f ∘ P) (x+y)) 0; rw [iteratedFDeriv_comp_add_left,add_zero]
lemma free (f:ℰ→F) {a:ℰ} (h : cleared f (m+1) ((0:ℝ),a.2)) : Trace.trunc m f a = 0 := by
  unfold Trace.trunc Trace.polyeval; exact Finset.sum_eq_zero (fun i hi=> by unfold Trace.coefficient Trace.plain; rw [h i (Finset.mem_range.mp hi)]; simp)

section appendages
variable [CompleteSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ E]
lemma suspension {x:E} {Q : ℰ→F} (h : Brush (j+(m+1)) C 1 Q (0,x)) :
    Brush j (C+1) 1 (Trace.pending Q m) (0,x) := by
  obtain ⟨d,hd,hD⟩:= Metric.mem_nhds_iff.mp (Trace.nearby h (lt_add_one C))
  refine Trace.work Q m ((0:ℝ),x) ?_
  filter_upwards [Metric.ball_mem_nhds ((0:ℝ),x) hd] with y hy t ht; apply hD
  have he : Trace.crossing t (0,x)=(0,x):= by change (t*(0:ℝ),x)= _; simp
  rw [mem_ball_iff_norm, ← he,← map_sub]
  exact ((Trace.crossing (E:=E) t).le_opNorm (y-(0,x))).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) (Trace.fare (E:=E) t ht)).trans_lt (mem_ball_iff_norm.mp hy))

def append (U : ℰ → Ξ→ F) (m : ℕ) (x : ℰ) (z : Ξ) := Trace.pending (fun x=> U x z) m x
lemma Picture.dipped (h : Picture U D v u (j+(m+1)) C) : Picture (append U m) D v u j C:= by
  let P:= patch E v u; let Z:= closedBall (0:Ξ) D
  let H x z:= Trace.pending (fun x=> U x z) m x; let K x:= Z.indicator (H x)
  have he (x) (hx:x∈P) := (show ∀ᶠ y in 𝓝 x, y∈P from (patch_open ..).mem_nhds hx)
  have hp (x) (hx:x∈P) (z:Ξ) (hz:‖z‖≤D) : Brush j C 1 (fun x => H x z) x := Trace.work _ _ _ ((he x hx).mono fun y hy t ht=> h.budget _ (keeps hy ht) z hz)
  have h' x z : K x z=Trace.pending (fun x=> velvet U D x z) m x := by
    by_cases hv : z∈Z
    · rw [show K x z= _ from indicator_of_mem hv (H x)]
      exact congr_arg (fun Q:ℰ→F=> Trace.pending Q m x) (funext fun i=> Eq.symm (indicator_of_mem hv _))
    rw [show K x z=0 from indicator_of_notMem hv (H x), show (fun x=> velvet U D x z)=(fun _=> (0:F)) from funext fun i=> indicator_of_notMem hv _]
    simp [Trace.pending,Trace.toll,Trace.plain]
  have hK (x:ℰ) (hx:x∈P) z : Brush j C 1 (fun x=> K x z) x:= by
    simp_rw [h']; exact Trace.work _ _ _ ((he _ hx).mono fun i hi t ht=> h.stamp (keeps hi ht) z)
  refine ⟨h.expense,fun x hx=> ?_,hp⟩
  have hb (b:ℝ) (j':E) (hx:(b,j')∈P) (hv:b≠0) : StronglyMeasurable (K (b,j')):= by
    have hc : (0,j')∈P:= ⟨mem_ball_self (patch_zero hx).1,hx.2⟩
    let H z:= fun x=> velvet U D x z
    let W (z:Ξ) := Trace.trunc m (H z) (b,j')
    have hw : StronglyMeasurable W:= by
      unfold W trunc polyeval; apply Finset.stronglyMeasurable_fun_sum; intro i hi
      let L:= ContinuousMultilinearMap.apply ℝ (fun _:Fin i=>ℰ) F (fun _=> (1,0)); have hi:= Finset.mem_range.mp hi
      exact StronglyMeasurable.smul (stronglyMeasurable_const (b:=b^i)) (StronglyMeasurable.smul (stronglyMeasurable_const (b:=(i.factorial:ℝ)⁻¹)) (L.continuous.comp_stronglyMeasurable ((h.mend (by omega : i≤j+(m+1)) le_rfl le_rfl le_rfl).vital hc)))
    have hk z : velvet U D (b,j') z= W z + b^(m+1) • K (b,j') z := by
      rw [h']; exact Trace.quote _ _ (fun i hi=> ((h.stamp (keeps hx hi) z).smaller (show m+1≤j+(m+1) from Nat.le_add_left ..)).smooth)
    rw [show K (b,j')=(fun z=> (b^(m+1))⁻¹ • (velvet U D (b,j') z-W z)) from funext fun z=> by rw [hk,add_sub_cancel_left,inv_smul_smul₀ (pow_ne_zero _ hv)]]
    exact StronglyMeasurable.smul (stronglyMeasurable_const (b:=(b^(m+1))⁻¹)) ((h.cut _ hx).sub hw)
  change StronglyMeasurable (K x)
  obtain ⟨b,i⟩:=x; by_cases hv : b=0
  swap; · exact hb _ _ hx hv
  subst b
  let k (y:ℝ):= if (y,i)∈P ∧ y≠0 then K (y,i) else 0
  have hk (y:ℝ) : StronglyMeasurable (k y):= by unfold k; split_ifs with h; exact hb _ _ h.1 h.2; exact stronglyMeasurable_const
  apply stronglyMeasurable_of_tendsto (𝓝[≠] (0:ℝ)) hk
  refine (tendsto_pi_nhds.2 (fun z=> (((hK _ hx z).smooth.continuousAt.comp (f:=fun (y:ℝ)=>(y,i)) (by fun_prop)).continuousWithinAt (s:={(0:ℝ)}ᶜ)).tendsto)).congr' ?_
  have hp := Tendsto.eventually (show Tendsto (fun y:ℝ=>(y,i)) (𝓝 (0:ℝ)) (𝓝 (0,i)) from by change ContinuousAt (fun y:ℝ=>(y,i)) 0; fun_prop) (he _ hx)
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy ht using Eq.symm (if_pos ⟨hy,ht⟩)
lemma Cloud.dipped (h : Cloud U D v u (j+(m+1)) n C) : Cloud (append U m) D v u j n (C+1):= by
  refine ⟨h.toPicture.dipped.mend le_rfl le_rfl le_rfl (le_add_of_nonneg_right zero_le_one),fun y hy z=> ?_,fun R hR=> ?_⟩
  · exact (suspension (Q:=fun x=> U x z) (h.view _ hy z)).climb (by rw [add_mul,one_mul]; exact add_le_add le_rfl (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))) le_rfl
  obtain ⟨d,hd,Q,hQ⟩:= h.satellite R hR; exact ⟨d,hd,_,hQ.dipped⟩
end appendages

section receipt
def reduced (U : ℰ → Ξ → F) : ℕ → ℰ → Ξ→F
    | 0=> U
    | m+1=> append U m
def promote (U : ℰ → Ξ→F) (m i : ℕ) (x : ℰ) (z : Ξ):=x.1^i • reduced U m x z

variable [CompleteSpace F]
lemma receipt (h : Picture U D v u (j+m) C) {a:ℰ} (hx : a∈patch E v u) (he:a.1≠0) {z:Ξ} (hv : ‖z‖≤D)
    (hr : cleared (fun x => U x z) m (0,a.2)) : promote U m i a z =a.1^i • (a.1^m)⁻¹ • U a z := by
  unfold promote; apply congr_arg (a.1^i • ·); cases m with
  | zero=> simp only [pow_zero,inv_one,one_smul]; rfl
  | succ m =>
    have hh : U a z = a.1^(m+1) • reduced U (m+1) a z := by
      calc
        _ = Trace.trunc m (fun x=> U x z) a + a.1^(m+1) • Trace.pending (fun x=> U x z) m a:= Trace.quote _ _
          (fun t ht=> ((h.budget _ (keeps hx ht) z hv).smaller (show m+1≤j+(m+1) from Nat.le_add_left ..)).smooth)
        _ = _:= by rw [free (a:=a) _ hr,zero_add]; rfl
    rw [hh,inv_smul_smul₀ (pow_ne_zero _ he)]
variable [FiniteDimensional ℝ E] [SecondCountableTopology F]
lemma promoted (h : Cloud U D v u (j+m) n C) (hi:v≤1) (i : ℕ) : Cloud (promote U m i) D v u j n ((3^j)^i*(C+1)*3^j) := by
  have hp: Cloud (reduced U m) D v u j n (C+1):= by
    cases m
    · exact h.raise le_rfl le_rfl le_rfl (le_add_of_nonneg_right zero_le_one) le_rfl
    exact h.dipped
  have hh := (powerCloud (E:=E) hi D u i j).mix hp; rw [zero_add] at hh
  exact hh
end receipt
end YM.RemainderComparison.Germ
