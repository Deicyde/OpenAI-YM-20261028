import YM.Extension.UV.Tail
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Abstract parameter control and analytic solution by two-end iteration.

Single parameter but Banach interaction data at each level.

The
recursions are only criteria until the same maps are constructed and checked on the Wilson family.
-/
noncomputable section
open Filter Topology Function Set
open scoped BigOperators ContDiff
set_option autoImplicit false
namespace YM.Extension.UV
section generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F]
variable {f : E→F} {U : Set E} {M r δ : ℝ} {x y : E}

lemma cauchy_bound (h : DifferentiableOn ℂ f (Metric.ball x r)) (hr : 0<r)
    (H : ∀ z∈Metric.ball x r, ‖f z‖ ≤ M) : ‖fderiv ℂ f x‖ ≤ M/r := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (H x (Metric.mem_ball_self hr))
  let L:= fderiv ℂ f x
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v=>?_
  by_cases hy : v=0
  · subst v; simp
  have hv : 0<‖v‖ := norm_pos_iff.mpr hy
  let t := ((‖v‖:ℂ)⁻¹ : ℂ)
  have ht : ‖t‖=‖v‖⁻¹ := by simp [t]
  let g (z:ℂ):E := (z*t) • v+x
  have hg (z) : HasDerivAt g (t • v) z := ((hasDerivAt_mul_const t).smul_const v).add_const x
  have hnorm (z:ℂ) : ‖g z-x‖=‖z‖ := by unfold g; rw [add_sub_cancel_right,norm_smul,norm_mul,ht,mul_assoc,inv_mul_cancel₀ hv.ne',mul_one]
  have h0 : g 0=x := by simp [g];
  have hx : HasFDerivAt f L (g 0) := by rw [h0]; exact (h.differentiableAt (Metric.ball_mem_nhds x hr)).hasFDerivAt
  have d (q:ℝ) (hq : 0<q) (hq' : q<r) : ‖v‖⁻¹ * ‖L v‖ ≤ M/q := by
    have maps {z : ℂ} (hz : z∈Metric.closedBall 0 q) : g z∈ Metric.ball x r := Metric.mem_ball.2 (by rw [dist_eq_norm,hnorm]; simpa [hnorm] using (lt_of_le_of_lt (show ‖z‖ ≤ q by simpa using hz) hq'))
    rw [← ht, ← norm_smul, ← (L.map_smul t), ← (hx.comp_hasDerivAt 0 (hg _)).deriv]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hq ((show DifferentiableOn ℂ (f ∘ g) (closure (Metric.ball _ _)) from ?_).diffContOnCl) (fun z hz=>H _ (maps (Metric.sphere_subset_closedBall hz)))
    exact h.comp (fun z _=>(hg z).differentiableAt.differentiableWithinAt) (fun a ha=> maps (Metric.closure_ball_subset_closedBall ha))
  have hd : (‖v‖)⁻¹ * ‖L v‖ * r ≤ M := le_of_forall_lt fun w hw=> by
     have he : Tendsto (fun q => ‖v‖⁻¹*‖L v‖*q) (𝓝[<] r) (𝓝 _) := ((continuous_const.mul continuous_id').tendsto r).mono_left nhdsWithin_le_nhds
     have hg : ∀ᶠ q in 𝓝[<]r, 0<q ∧ q<r ∧ w < ‖v‖⁻¹*‖L v‖*q := by
       filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ q in 𝓝 r, 0<q from Ioi_mem_nhds hr), (show ∀ᶠ q in 𝓝[<] r, q < r from self_mem_nhdsWithin), he.eventually (show ∀ᶠ q in 𝓝 _,w<q from Ioi_mem_nhds hw)] with q hq ha hb
       exact ⟨hq, ha, hb⟩
     obtain ⟨q,hq',hq,hW⟩ := hg.exists
     exact hW.trans_le ((le_div_iff₀ hq').mp (d _ hq' hq))
  calc _ = ((‖v‖⁻¹*‖L v‖*r)*‖v‖)/r  := by field_simp; rfl
       _ ≤ M*‖v‖/r := by gcongr
       _ = _ := by ring

-- spelling notations checked during compiling
variable [NormedSpace ℝ E]

lemma diam_lipschitz (hs : Convex ℝ U) (hU : ∀ x∈U,DifferentiableAt ℂ f x)
    (h : ∀ x∈U,DifferentiableOn ℂ f (Metric.ball x r)) (hM : ∀ x∈U, ∀ y ∈ Metric.ball x r,‖f y‖ ≤ M) (hr : 0<r) :
    ∀ x∈U,∀ y∈U,‖f x-f y‖ ≤ M/r * ‖x-y‖ := fun x hx y hy=> hs.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℂ) hU (fun x hx=>cauchy_bound (h x hx) hr (hM x hx)) hy hx

lemma on_smaller_ball (hs : DifferentiableOn ℂ f (Metric.ball x r))
    (hm : ∀ y∈Metric.ball x r,‖f y‖ ≤ M) (hr : δ<r) (z : E) (hz : ‖z-x‖ ≤ δ) (w : E) (hw : ‖w-x‖ ≤ δ) :
    ‖f z-f w‖ ≤ M/(r-δ)*‖z-w‖ := by
  have h (u) (hu : u∈Metric.closedBall x δ) v (hv : v∈Metric.ball u (r-δ)) : v∈Metric.ball x r:= by
    simp only [Metric.mem_ball,Metric.mem_closedBall] at *; linarith [dist_triangle v u x]
  refine diam_lipschitz (r:=r-δ) (M:=M) (convex_closedBall x δ) (fun u hu=> hs.differentiableAt (Metric.isOpen_ball.mem_nhds (h _ hu u (Metric.mem_ball_self (sub_pos.mpr hr))))) (fun u hu=> hs.mono (h u hu)) (fun u hu z hz=> hm _ (h u hu z hz)) (sub_pos.mpr hr) z ?_ w ?_
  · rwa [Metric.mem_closedBall,dist_eq_norm_sub]
  rwa [Metric.mem_closedBall,dist_eq_norm_sub]
end generic
namespace AnalyticTuning
universe u
variable (E : ℕ→ Type u) [∀i,NormedAddCommGroup (E i)] [∀i,NormedSpace ℂ (E i)]

structure Prescription where
  term (i : ℕ) : ℂ → E (i+1) → E i
  wobble (i : ℕ) : ℂ → E (i+1) → ℂ
  coefficient (i : ℕ) : ℂ
  start (i : ℕ) : ℂ → E i
  β₀ (i : ℕ) : ℂ
  radius (i : ℕ) : ℝ
  cost (i : ℕ) : ℝ

variable {E} (R : Prescription E)
variable {N : ℕ}

def down (z : ℕ→ℂ) : (k i : ℕ) → E i
  | 0, i => R.start i (z i)
  | k+1, i => R.term i (z (i+1)) (down z k (i+1))

def state (z : ℕ→ℂ) (N i : ℕ) : E i := down R z (N-i) i
omit [∀i,NormedSpace ℂ (E i)] in
lemma state_goes (z : ℕ→ℂ) (i : ℕ) (hi : i<N) : state R z N i=R.term i (z (i+1)) (state R z N (i+1)) := by
  unfold state; rw [show N-i=(N-(i+1))+1 by omega,down]
@[simp] lemma state_start (z : ℕ → ℂ) (i : ℕ) : state R z i i=R.start i (z i):= by simp [state,down]

abbrev region (i : ℕ) := Metric.ball (R.β₀ i) (R.radius i)
abbrev interaction (_R : Prescription E) (i : ℕ) := Metric.ball (0:E i) 1

structure Grant (N : ℕ) : Prop where
  grow : Monotone R.radius
  positive i : 0<R.radius i
  pay_pos i : 0≤R.cost i
  small : ∑ i∈Finset.range N,R.cost i / R.radius (i+1) ≤ 1/100
  maps i (hi : i<N) :
    DifferentiableOn ℂ (fun v:ℂ×E (i+1)=> R.term i v.1 v.2) ((region R (i+1)).prod (interaction R (i+1))) ∧
    DifferentiableOn ℂ (fun v:ℂ×E (i+1)=> R.wobble i v.1 v.2) ((region R (i+1)).prod (interaction R (i+1))) ∧
    ∀ x∈region R (i+1),∀ w∈interaction R (i+1), ‖R.term i x w‖ ≤ 1/4 ∧ ‖R.wobble i x w‖ ≤ R.cost i
  maps_start : DifferentiableOn ℂ (R.start N) (region R N)
  cap_start : ∀ z ∈region R N, ‖R.start N z‖ ≤ 1/4
  center_step i (hi : i<N) : R.β₀ i=R.β₀ (i+1)+R.coefficient i+R.wobble i (R.β₀ (i+1)) (state R R.β₀ N (i+1))

def Safe (z : ℕ → ℂ) : Prop := ∀ i, ‖z i -R.β₀ i‖ ≤ R.radius i / 8
def Similar (z v : ℕ → ℂ) (D : ℝ) : Prop := ∀ i, ‖z i-v i‖/R.radius i ≤ D

variable {R}
lemma Safe.at_mem (H : Grant R N) {z} (h : Safe R z) (i : ℕ) : z i∈ region R i := by
  apply Metric.mem_ball.mpr; rw [dist_eq_norm]; have := H.positive i; linarith [h i]
lemma Safe.center (H : Grant R N) : Safe R R.β₀ := fun i=> by simp; linarith [H.positive i]
lemma in_ball {i} {x:E i} (hx : ‖x‖ ≤ (1/4:ℝ)) : x∈ interaction R i := Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith)
lemma state_cap (H : Grant R N) (z : ℕ→ℂ) (hz : Safe R z) {i} (hi : i ≤ N) : ‖state R z N i‖ ≤ 1/4 := by
  induction hi using Nat.decreasingInduction with
  | self => rw [state_start]; exact H.cap_start _ (hz.at_mem H _)
  | of_succ i hi ih => rw [state_goes R z i hi]; exact ((H.maps i hi).2.2 _ (hz.at_mem H _) _ (in_ball ih (R:=R))).1

lemma left_maps {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {r : Set ℂ} {f : ℂ → X → F} {s : Set X} (h : DifferentiableOn ℂ (fun v : ℂ×X=> f v.1 v.2) (r.prod s)) (x : X) (hx : x∈s) : DifferentiableOn ℂ (fun i:ℂ=> f i x) r :=
  h.comp (differentiable_id.differentiableOn.prodMk (differentiable_const x).differentiableOn) (fun _ hi=> ⟨hi,by assumption⟩)
lemma right_maps {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {r : Set ℂ} {f : ℂ → X → F} {s : Set X} (h : DifferentiableOn ℂ (fun v : ℂ×X=> f v.1 v.2) (r.prod s)) (x : ℂ) (hx : x∈r) : DifferentiableOn ℂ (f x) s :=
  h.comp ((differentiable_const x).differentiableOn.prodMk differentiable_id.differentiableOn) (fun _ hi=> ⟨by assumption,hi⟩)

lemma estimates [∀i,NormedSpace ℝ (E i)] (H : Grant R N) (i : ℕ) (hi : i < N) {z z' : ℂ} {x x': E (i+1)}
    (hz : ‖z-R.β₀ (i+1)‖ ≤ R.radius (i+1) / 8) (hz': ‖z'-R.β₀ (i+1)‖ ≤ R.radius (i+1)/8) (hx : ‖x‖ ≤ 1/4) (hx' :‖x'‖ ≤ 1/4) :
    ‖R.term i z x -R.term i z' x'‖ ≤ (1/3)*‖x-x'‖ + ‖z-z'‖/(2*R.radius (i+1)) ∧ ‖R.wobble i z x -R.wobble i z' x'‖ ≤ R.cost i * ((4/3)*‖x-x'‖ + 2*‖z-z'‖/R.radius (i+1)) := by
  have hR := H.positive (i+1); let Y:= H.maps i hi
  have hm {x₁:E (i+1)} (hx₁: ‖x₁‖ ≤ 1/4) : x₁ ∈interaction R (i+1):= in_ball hx₁
  have hw {z₁ : ℂ} (hz₁ : ‖z₁-R.β₀ (i+1)‖ ≤ R.radius (i+1) / 8) : z₁ ∈ region R (i+1) := Metric.mem_ball.2 (by rw [dist_eq_norm]; linarith)
  have hh := fun w hw=> left_maps Y.1 w (hm hw)
  have hh' := fun f hf=> right_maps Y.1 f (hw hf)
  obtain ⟨h₁,h₂⟩ : ‖R.term i z x'-R.term i z' x'‖ ≤ ‖z-z'‖/(2*R.radius (i+1)) ∧ ‖R.term i z x- R.term i z x'‖ ≤ (4/3)*(1/4)*‖x-x'‖ := by
    constructor
    · have hc := on_smaller_ball (hh x' hx') (δ:=R.radius (i+1)/2) (fun y hy=>(Y.2.2 _ hy _ (hm hx')).1) (by linarith) z (by linarith) z' (by linarith)
      calc _ ≤ _ := hc
           _ = ‖z-z'‖/(2*R.radius (i+1)) := by field_simp; ring
    have hc := on_smaller_ball (hh' z hz) (fun y hy=> (Y.2.2 _ (hw hz) y hy).1) (by norm_num : (1/4:ℝ)<1) x (by simpa using hx) x' (by simpa using hx')
    linarith
  obtain ⟨h₃,h₄⟩ : ‖R.wobble i z x'-R.wobble i z' x'‖ ≤ R.cost i* (2*‖z-z'‖/R.radius (i+1)) ∧ ‖R.wobble i z x- R.wobble i z x'‖ ≤ (4/3)*R.cost i*‖x-x'‖ := by
    constructor
    · calc _ ≤ _ := on_smaller_ball (left_maps Y.2.1 x' (hm hx')) (δ:=R.radius (i+1)/2) (fun y hy=>(Y.2.2 _ hy _ (hm hx')).2) (by linarith) z (by linarith) z' (by linarith)
           _ = _ := by field_simp; ring
    have hc := on_smaller_ball (right_maps Y.2.1 _ (hw hz)) (fun y hy=> (Y.2.2 _ (hw hz) y hy).2) (by norm_num : (1/4:ℝ)<1) x (by simpa using hx) x' (by simpa using hx')
    convert hc using 1; ring
  exact ⟨by linarith [norm_sub_le_norm_sub_add_norm_sub (R.term i z x) (R.term i z x') (R.term i z' x')],by linarith [norm_sub_le_norm_sub_add_norm_sub (R.wobble i z x) (R.wobble i z x') (R.wobble i z' x')]⟩

variable [∀i,NormedSpace ℝ (E i)]

lemma state_estimates (H : Grant R N) {z z' : ℕ→ℂ} (hz : Safe R z) (hz' : Safe R z') {D : ℝ} (hd : Similar R z z' D) : (∀ i≤N, ‖state R z N i-state R z' N i‖≤D) ∧ (∀ i<N, ‖R.wobble i (z (i+1)) (state R z N (i+1))-R.wobble i (z' (i+1)) (state R z' N (i+1))‖ ≤ R.cost i * (4*D)) := by
  let f: ℕ→ Prop := fun i=> ‖state R z N i-state R z' N i‖ ≤ D
  have hE : 0 ≤ D:= le_trans (div_nonneg (norm_nonneg _) (H.positive 0).le) (hd 0)
  have hD i (hi:i<N):= estimates H i hi (hz (i+1)) (hz' (i+1)) (state_cap H z hz hi) (state_cap H z' hz' hi)
  have h₁ i (hi:i ≤ N) : f i:= by
    induction hi using Nat.decreasingInduction with
    | self =>
      have hc := on_smaller_ball H.maps_start H.cap_start (δ:=R.radius N/2) (by linarith [H.positive N]) (z N) (by linarith [hz N,H.positive N]) (z' N) (by linarith [hz' N,H.positive N])
      change ‖state _ _ _ _ - state _ _ _ _‖ ≤ _; simp only [state_start]
      apply hc.trans
      have H':(1/4:ℝ)/(R.radius N-R.radius N/2)*‖z N-z' N‖=(1/2)*(‖z N-z' N‖/R.radius N) := by field_simp; ring
      linarith [hd N]
    | of_succ i hi ih =>
      unfold f; rw [state_goes R z i hi, state_goes R z' i hi]
      refine (hD i hi).1.trans ?_
      have H' : ‖z (i+1)-z' (i+1)‖/(2*R.radius (i+1))=(1/2)*(‖z (i+1)-z' (i+1)‖ /R.radius (i+1)):= by ring
      unfold f at ih
      linarith [hd (i+1)]
  refine ⟨h₁,fun i hi=> (hD i hi).2.trans (mul_le_mul_of_nonneg_left ?_ (H.pay_pos i))⟩; have ht:= h₁ (i+1) hi; unfold f at ht
  have ha:=hd (i+1); unfold Similar at hd
  have he := (div_le_iff₀ (H.positive (i+1))).mp ha
  have h: 2 * ‖z (i+1)-z' (i+1)‖ / R.radius (i+1)=(2:ℝ)*(‖z (i+1)-z' (i+1)‖ / R.radius (i+1)) := by ring
  linarith only [h, ha, ht, hE]

variable (R) (N)
def nextPath (t : ℂ) (z : ℕ→ℂ) (j : ℕ) := if j≤N then t - ∑ i ∈ Finset.range j,(R.coefficient i+R.wobble i (z (i+1)) (state R z N (i+1))) else R.β₀ j

abbrev Near (t : ℂ) := ‖t-R.β₀ 0‖ ≤ R.radius 0 / 100

variable {R N}

omit [∀i,NormedSpace ℝ (E i)] in
lemma center_anchor (H : Grant R N) : nextPath R N (R.β₀ 0) R.β₀=R.β₀ := by
  funext j; unfold nextPath; split
  next hi=>
    induction j with
    | zero=>simp
    | succ j ih=>
      have hj:j<N:=hi
      simp only [Finset.sum_range_succ]
      rw [sub_add_eq_sub_sub _,ih (by omega)]
      rw [H.center_step j (by omega)]; ring
  rfl

lemma next_contracts (H : Grant R N) {s t : ℂ} {z z'} (hz : Safe R z) (hz' : Safe R z') {D : ℝ} (hd : Similar R z z' D): Similar R (nextPath R N s z) (nextPath R N t z') (D/20+ ‖s-t‖/R.radius 0):= by
  intro i; simp only [nextPath]
  have hR := H.positive i
  have hE : 0 ≤ D:= (div_nonneg (norm_nonneg _) hR.le).trans (hd i)
  split
  next hi=>
    let A (i:ℕ) z:= R.coefficient i+R.wobble i (z (i+1)) (state R z N (i+1))
    have hs (k:ℕ) (hk:k ≤ i) : ‖(∑j∈Finset.range k,A j z) -(∑j∈Finset.range k,A j z')‖/R.radius i ≤ (∑ j∈Finset.range k,R.cost j/R.radius (j+1)) * (4*D) := by
      induction k with
      | zero=>simp
      | succ j ih=>
        rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,add_mul,
            add_sub_add_comm]
        apply le_trans (div_le_div_of_nonneg_right (norm_add_le ..) hR.le)
        rw [add_div]
        refine add_le_add (ih (by omega)) ?_
        unfold A; rw [add_sub_add_left_eq_sub]
        calc _ ≤ R.cost j *(4*D)/R.radius i:= by gcongr; exact (state_estimates H hz hz' hd).2 j (by omega)
             _ ≤ _ := by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_left (by have := H.pay_pos j; positivity) (H.positive _) (H.grow hk)
    rw [sub_sub_sub_comm]
    apply le_trans (div_le_div_of_nonneg_right (norm_sub_le ..) hR.le)
    rw [add_div,add_comm (D/20)]
    apply add_le_add (div_le_div_of_nonneg_left (norm_nonneg _) (H.positive _) (H.grow (Nat.zero_le _))) ((hs i le_rfl).trans ?_)
    let sum' k := ∑ j∈Finset.range k,R.cost j/R.radius (j+1)
    have hsum (k) : sum' k ≤ sum' (k+1):= by unfold sum'; rw [Finset.sum_range_succ]; apply le_add_of_nonneg_right; exact div_nonneg (H.pay_pos _) (H.positive _).le
    have ha : sum' i ≤ 1/100:= ((monotone_nat_of_le_succ hsum) hi).trans H.small
    change sum' i * _ ≤ _
    nlinarith
  simp only [sub_self,norm_zero,zero_div]; have :=H.positive 0; positivity

lemma next_safe (H : Grant R N) {z} (hz : Safe R z) {t : ℂ} (ht : Near R t): Safe R (nextPath R N t z) := by
  have hs : Similar R z R.β₀ (1/8) := fun i=> (div_le_iff₀ (H.positive _)).mpr (by linarith [hz i])
  have hp : ‖t-R.β₀ 0‖/R.radius 0 ≤ 1/100:= (div_le_iff₀ (H.positive _)).mpr (by change Near _ _ at ht; linarith)
  have hc := next_contracts (s:=t) (t:=R.β₀ 0) H hz (Safe.center H) hs
  rw [center_anchor H] at hc
  exact fun i=> by have := (div_le_iff₀ (H.positive i)).mp ((hc i).trans (show _ ≤ 1/8 from by linarith)); linarith

variable (R N)
def tour : ℕ → ℂ → ℕ → ℂ
| 0, _ => R.β₀
| k+1, t => nextPath R N t (tour k t)

variable {R N}
lemma tour_safe (H : Grant R N) {t} (ht : Near R t) (i) : Safe R (tour R N i t) := by
  induction i with
  | zero => exact Safe.center H
  | succ i ih => exact next_safe H ih ht

lemma tour_step (H : Grant R N) {t} (ht : Near R t) (i) : Similar R (tour R N i t) (tour R N (i+1) t) ((1/20)^i):= by
  induction i with
  | zero =>
    rw [pow_zero]; intro i; have hp:= tour_safe H ht 1 i
    rw [tour, norm_sub_rev,div_le_iff₀ (H.positive i)]; linarith [H.positive i]
  | succ i ih=>
    have hc := next_contracts (s:=t) (t:=t) (R:=R) H (tour_safe H ht i) (tour_safe H ht (i+1)) ih
    intro m; simpa only [tour,pow_succ, sub_self, norm_zero, zero_div,zero_mul,add_zero,div_eq_mul_inv, one_mul] using hc m

lemma tour_close (H : Grant R N) {t} (ht : Near R t) {i j} (hi : i ≤ j) (m) : ‖tour R N i t m-tour R N j t m‖ ≤ (2*R.radius m)*((1/20)^i-(1/20)^j):= by
  induction j,hi using Nat.le_induction with
  | base => simp
  | succ j hij ih=>
    have hx:=tour_step H ht j m
    rw [div_le_iff₀ (H.positive _)] at hx
    have hp : 0 ≤ R.radius m *((1/20:ℝ)^j):= mul_nonneg (H.positive _).le (by positivity)
    rw [pow_succ]
    linarith only [ih,hx,hp,norm_sub_le_norm_sub_add_norm_sub (tour R N i t m) (tour R N j t m) (tour R N (j+1) t m)]

lemma tour_limit (H : Grant R N) : ∃ f : ℂ→ℕ→ℂ,∀{t}, Near R t → Safe R (f t) ∧ ∀ m, Tendsto (fun k=> tour R N k t m) atTop (𝓝 (f t m)) ∧ ∀ i, ‖tour R N i t m-f t m‖ ≤ (2*R.radius m)*((1/20)^i):= by
  have hlim (t : {t // Near R t}) (m) : ∃ y : ℂ, Tendsto (fun k=> tour R N k t.val m) atTop (𝓝 y):= by
    apply cauchySeq_tendsto_of_complete; apply Metric.cauchySeq_iff'.mpr
    rintro ε hε
    have hγ:= (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤ (1/20:ℝ) by norm_num) (by norm_num)).const_mul (2*R.radius m)
    obtain ⟨i,hi⟩:= (hγ.eventually (Iio_mem_nhds (by simpa only [mul_zero] using hε))).exists
    exact ⟨i,fun j hj=> by
      rw [dist_eq_norm,norm_sub_rev]; have hQ:= tour_close H t.property hj m
      have hb:= H.positive m; have hu : 0 < (1/20:ℝ)^j := by positivity
      change (2*R.radius m)*(1/20)^i < ε at hi
      nlinarith⟩
  choose f h₀ using fun t m=> hlim t m
  let F (t:ℂ) := if h: Near R t then f ⟨_,h⟩ else R.β₀
  refine ⟨F,fun {t} ht=>?_⟩
  dsimp [F]; rw [dif_pos ht]
  let hT (m:ℕ):= h₀ ⟨_,ht⟩ m
  exact ⟨fun m=> le_of_tendsto ((hT m).sub_const _).norm (Eventually.of_forall fun i=> tour_safe H ht i m),fun m=> ⟨hT _,fun i=> le_of_tendsto ((hT m).const_sub _).norm ((eventually_ge_atTop i).mono fun j hj=> by
    have h:=tour_close H ht hj m
    have h₁:= H.positive m
    have h₂ : 0 ≤ (1/20:ℝ)^j:= by positivity
    apply (le_trans h); nlinarith)⟩⟩

variable (R N)
noncomputable def answer (H : Grant R N) (t : ℂ) (i : ℕ) := (tour_limit H).choose t i
variable {R N}

lemma answer_spec (H : Grant R N) {t} (ht : Near R t) (m) : Safe R (answer R N H t) ∧ Tendsto (fun i=> tour R N i t m) atTop (𝓝 (answer R N H t m)):= ⟨((tour_limit H).choose_spec ht).1, ((tour_limit H).choose_spec ht).2 m|>.1⟩
lemma answer_uniform (H : Grant R N) m : TendstoUniformlyOn (fun i t=>tour R N i t m) (fun t=> answer R N H t m) atTop {t|Near R t}:= by
  apply Metric.tendstoUniformlyOn_iff.mpr; intro ε hε
  have hγ:= (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤ (1/20:ℝ) by norm_num) (by norm_num)).const_mul (2*R.radius m)
  filter_upwards [hγ.eventually (Iio_mem_nhds (by simpa only [mul_zero] using hε))] with i hi t ht
  rw [dist_eq_norm,norm_sub_rev]
  exact (((tour_limit H).choose_spec ht).2 _|>.2 i).trans_lt hi

lemma at_once_differentiable (H : Grant R N) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (D : Set X)
    (F : X→ℕ→ℂ) (hd : ∀ i,DifferentiableOn ℂ (fun w=>F w i) D) (he : ∀ w ∈ D,Safe R (F w)) (k:X→ℂ) (hk : DifferentiableOn ℂ k D) :
      (∀ i≤N,DifferentiableOn ℂ (fun w=>state R (F w) N i) D) ∧ ∀ i, DifferentiableOn ℂ (fun w=> nextPath R N (k w) (F w) i) D := by
  have hs i (hi:i≤N): DifferentiableOn ℂ (fun w=>state R (F w) N i) D:= by
    induction hi using Nat.decreasingInduction with
    | self => simp only [state_start]; exact H.maps_start.comp (hd N) (fun w hw=> (he w hw).at_mem H N)
    | of_succ i hi ih=> simp only [state_goes _ _ i hi]; apply (H.maps i hi).1.comp ((hd (i+1)).prodMk ih) (fun w hw=> ⟨(he w hw).at_mem H (i+1),in_ball (state_cap H _ (he w hw) hi)⟩)
  refine ⟨hs,fun i=>?_⟩
  simp only [nextPath]; split
  next hi=>
    refine hk.sub (DifferentiableOn.fun_sum (u:=Finset.range i) ?_)
    intro j hj; have hj' : j<N := (Finset.mem_range.1 hj).trans_le hi
    exact ((H.maps j hj').2.1.comp ((hd (j+1)).prodMk (hs (j+1) hj')) (fun w hw=> ⟨(he w hw).at_mem H (j+1),in_ball (state_cap H _ (he w hw) hj')⟩)).const_add _
  exact (differentiable_const _).differentiableOn

def disk (R : Prescription E) := Metric.ball (R.β₀ 0) (R.radius 0/100)

lemma near_of_disk {t} (ht : t∈ disk R): Near R t:= by
  unfold disk at ht; unfold Near; exact le_of_lt (by simpa [Metric.mem_ball,dist_eq_norm] using ht)

theorem calibrated_analytic (H : Grant R N) : (∀ i≤N, DifferentiableOn ℂ (fun w=> state R (answer R N H w) N i) (disk R)) ∧ (∀ i, AnalyticOnNhd ℂ (fun w => answer R N H w i) (disk R)) := by
  have hd q m : DifferentiableOn ℂ (fun t:ℂ => tour R N q t m) (disk R) := by
    induction q generalizing m with
    | zero => exact (differentiable_const _).differentiableOn
    | succ q ih=> exact (at_once_differentiable H (disk R) _ ih (fun t ht=> tour_safe H (near_of_disk ht) q) _ (differentiable_id.differentiableOn)).2 m
  have hy i : DifferentiableOn ℂ (fun t=> answer R N H t i) (disk R) := ((answer_uniform H i).mono (fun _ hx=> near_of_disk hx)).tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall fun q=> hd q i) Metric.isOpen_ball
  exact ⟨(at_once_differentiable H (disk R) _ hy (fun t ht=> (answer_spec H (near_of_disk ht) 0).1) _ differentiable_id.differentiableOn).1,fun i=> (hy i).analyticOnNhd Metric.isOpen_ball⟩

lemma similar_tour (H : Grant R N) {t} (ht : Near R t) (k) : Similar R (tour R N k t) (answer R N H t) (2*((1/20)^k)):= by
  intro i; have:= ((tour_limit H).choose_spec ht).2 i|>.2 k
  rw [div_le_iff₀ (H.positive _)]
  apply le_trans this (by linarith)

lemma next_solution (H : Grant R N) {t} (ht : Near R t): nextPath R N t (answer R N H t) = answer R N H t := by
  funext i
  have hx : ∀ᶠ k in atTop,‖tour R N (k+1) t i-nextPath R N t (answer R N H t) i‖ ≤ (R.radius i/10)*((1/20)^k) := by
    filter_upwards with k
    have h₀:= next_contracts (s:=t) (t:=t) H (tour_safe H ht k) ((answer_spec H ht i).1) (similar_tour H ht k)
    rw [sub_self,norm_zero,zero_div,add_zero] at h₀
    apply le_trans ((div_le_iff₀ (H.positive i)).1 (h₀ i)) (le_of_eq ?_)
    ring
  have ht' : Tendsto (fun k=> tour R N (k+1) t i) atTop (𝓝 (answer R N H t i)) := (answer_spec H ht i).2.comp (tendsto_add_atTop_nat 1)
  have hb:= (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤ (1/20:ℝ) by norm_num) (by norm_num)).const_mul (R.radius i/10)
  have h := le_of_tendsto_of_tendsto ((ht'.sub_const _).norm) hb hx
  apply Eq.symm
  rw [←sub_eq_zero]
  exact norm_le_zero_iff.mp (by simpa only [mul_zero] using h)

lemma answer_starts (H : Grant R N) {t} (ht : Near R t): answer R N H t 0=t:= by conv_lhs=> rw [← next_solution H ht]; unfold nextPath; simp

lemma answer_recursion (H : Grant R N) {t} (ht : Near R t) {i} (hi:i<N) : answer R N H t i= answer R N H t (i+1)+R.coefficient i+R.wobble i (answer R N H t (i+1)) (state R (answer R N H t) N (i+1)) := by
  let a:=congr_fun (next_solution H ht)
  conv_lhs=> rw [← a i]
  conv_rhs=> lhs; lhs; rw [← a (i+1)]
  unfold nextPath; simp only [if_pos hi,if_pos hi.le, if_pos (show i+1 ≤ N by omega), Finset.sum_range_succ]; ring

end AnalyticTuning
end YM.Extension.UV
