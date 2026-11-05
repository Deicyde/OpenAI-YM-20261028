import Mathlib.Analysis.Distribution.Support
import YM.Distribution.Product


/-!
# Compact testing and support assembly (in Probe convention)

Important when taking *intersections* of cone, half-space and Ward-transports.
Uses an explicit equalizing cutoff; does not silently use density without
support condition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary.Probe
open MeasureTheory Filter Set Function Distribution Metric
open scoped Topology BigOperators InnerProductSpace ContDiff
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {f : Probe X}

def stall : ContDiffBump (0 : X) := ⟨1,2,by norm_num,by norm_num⟩

def bud (x : X) (r : ℝ) (h : 0 < r) : ContDiffBump x := ⟨r,r+r,h,by linarith⟩
def tint {x : X} (B : ContDiffBump x) : Probe X := (B.hasCompactSupport.comp_left (show Complex.ofReal 0=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
@[simp] theorem tinted {x : X} (B : ContDiffBump x) (p : X) : tint B p=(B p : ℂ) := rfl
@[simp] theorem tint_support {x : X} (B : ContDiffBump x) : tsupport (tint B)=closedBall x B.rOut := by
  have he : Function.support (tint B) = Function.support B := by ext y;simp
  rw [tsupport,he,← tsupport,B.tsupport_eq]

def compress (k : ℕ) : X ≃L[ℝ] X := ContinuousLinearEquiv.smulLeft (Units.mk0 (k+1:ℝ)⁻¹ (by positivity))
def keeper (k : ℕ) : Probe X := along (compress k) (tint stall)

def sew {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g : Probe A) := (SchwartzMap.smulLeftCLM ℂ ⇑g : Probe A →L[ℂ] Probe A)
@[simp] theorem sews {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g w : Probe A) (x : A) : sew g w x=g x*w x := SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth w x
lemma shrinks {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g w : Probe A) : tsupport (sew g w) ⊆ tsupport g ∩ tsupport w := by
  apply closure_minimal _ ((isClosed_tsupport _).inter (isClosed_tsupport _))
  intro x hx; rw [Function.mem_support,sews] at hx
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx),subset_tsupport _ (right_ne_zero_of_mul hx)⟩

def cap (k : ℕ) := @sew X _ _ (keeper k)
lemma cap_support (k : ℕ) : tsupport (cap k f) ⊆ tsupport f := (shrinks _ f).trans inter_subset_right
lemma finite_cap (k : ℕ) : HasCompactSupport (cap k f : X→ℂ) := by
  have he : HasCompactSupport ((keeper k : Probe X) : X→ℂ) := by
    have hB : HasCompactSupport (tint (stall (X:=X)) : X→ℂ) := by rw [HasCompactSupport,tint_support]; exact isCompact_closedBall ..
    exact hB.comp_homeomorph (compress k).toHomeomorph
  exact he.of_isClosed_subset (isClosed_tsupport _) ((shrinks _ _).trans inter_subset_left)
@[simp] lemma compression {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    (k : ℕ) (x : A) : compress k x=(k+1:ℝ)⁻¹ • x := rfl

lemma keeper_one (k : ℕ) {x : X} (hk : ‖x‖ ≤ k+1) : keeper k x=1 := by
  simp only [keeper, along_at,tinted]
  have he : compress k x ∈ Metric.closedBall 0 (stall (X:=X)).rIn := by
    rw [Metric.mem_closedBall,dist_zero_right,compression,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    change _ ≤ 1; exact (mul_le_mul_of_nonneg_left hk (by positivity)).trans (by rw [inv_mul_cancel₀ (by positivity)])
  rw [stall.one_of_mem_closedBall he];norm_num
lemma even_keeper (k n : ℕ) (x : X) : ‖iteratedFDeriv ℝ n (keeper k) x‖ ≤ size 0 n (tint (stall (X:=X))) := by
  let L := (compress (X:=X) k).toContinuousLinearMap
  have he : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun u => by
    change ‖compress k u‖ ≤ _
    rw [compression,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (by simp)) (norm_nonneg _))
  rw [show ⇑(keeper k) = tint stall ∘ L from rfl]
  simpa only [pow_zero,one_mul] using via L he (tint stall) x 0 n

/-- uniform cap bound. -/
lemma cap_cost (v : Probe X) (i j k) : size i j (cap k v) ≤
    ∑ l ∈ Finset.range (j+1), (j.choose l:ℝ)*size 0 l (tint (stall (X:=X)))*size i (j-l) v := by
  refine (cap k v).seminorm_le_bound ℂ i j (by unfold size; positivity) fun x => ?_
  rw [show ⇑(cap k v)=(fun x => keeper k x*v x) from funext fun _ => sews ..]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le
      ((keeper k).smooth ⊤) (v.smooth ⊤) x (n := j) (by exact_mod_cast le_top)) (by positivity))
  rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro l _
  rw [mul_left_comm]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (even_keeper k l x) (by positivity)) (SchwartzMap.le_seminorm ℂ i _ v x) (by positivity) (by unfold size; positivity)

omit [FiniteDimensional ℝ X] in
lemma vanish_j {x : X} (t : Probe X) (j : ℕ) (h : (⇑t) =ᶠ[𝓝 x] 0) : iteratedFDeriv ℝ j t x = 0 := by
  rw [(h.iteratedFDeriv ℝ j).self_of_nhds]; simp

theorem persistent (v : Probe X) : Tendsto (fun k => cap k v) atTop (𝓝 v) := by
  apply (tendN atTop _ _).2
  intro i j ε he
  let C := size (i+1) j v+∑ l ∈ Finset.range (j+1), (j.choose l:ℝ)*size 0 l (tint (stall (X:=X)))*size (i+1) (j-l) v
  obtain ⟨K,hK⟩ := exists_nat_gt (C/(ε/2))
  filter_upwards [eventually_ge_atTop K] with k hk
  have ht : C<(ε/2)*((k:ℝ)+1) := (div_lt_iff₀ (by positivity)).1 (hK.trans (show (K:ℝ)<k+1 by exact_mod_cast Nat.lt_succ_of_le hk)) |>.trans_eq (by ring)
  refine lt_of_le_of_lt ((cap k v - v).seminorm_le_bound ℂ i j (M := ε/2) (by positivity) ?_) (by linarith)
  intro x; let z := cap k v - v
  have hv : ‖x‖^(i+1)*‖iteratedFDeriv ℝ j z x‖ ≤ C := (SchwartzMap.le_seminorm ℂ _ _ _ _).trans
    ((map_sub_le_add (SchwartzMap.seminorm ℂ (i+1) j) (cap k v) v).trans ((add_le_add_left (cap_cost v (i+1) j k) (size (i+1) j v)).trans_eq (add_comm ..)))
  by_cases h : ‖x‖ < (k:ℝ)+1
  · have hEq : (z : X → ℂ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [((continuous_norm.tendsto x).eventually (gt_mem_nhds h))] with u hu
      change cap k v u - v u = (0:ℂ); simp [cap,keeper_one k (show ‖u‖<(k:ℝ)+1 from hu).le]
    rw [show _-_ = z from rfl, vanish_j _ _ hEq,norm_zero,mul_zero]; positivity
  apply le_of_mul_le_mul_right (a := ‖x‖) _ (lt_of_lt_of_le (by positivity) (le_of_not_gt h))
  refine le_trans (b:=C) ?_ ?_
  · change ‖x‖^i*‖iteratedFDeriv ℝ j z x‖ * ‖x‖ ≤ _; rw [mul_right_comm,←pow_succ]; exact hv
  exact ht.le.trans (mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity))
end YM.Boundary.Probe

namespace YM.Boundary.Distn
open MeasureTheory Filter Set Function Distribution Metric Probe
open scoped Topology BigOperators InnerProductSpace ContDiff
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable (F : Distn X) {s : Set X}

theorem from_compact : IsVanishingOn F s ↔ ∀ f : Probe X, tsupport f ⊆ s → HasCompactSupport ⇑f → F f=0 := by
  refine ⟨fun h f hf _ => h f hf,fun h f hf => tendsto_nhds_unique ((F.continuous.tendsto f).comp (persistent f)) ?_⟩
  have he (k : ℕ) : F (cap k f)=0 := h _ ((cap_support k).trans hf) (finite_cap k)
  simpa only [Function.comp_def,he] using! (show Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0) from tendsto_const_nhds)

lemma trim_support (x : X) (r : ℝ) (h : 0 < r) (v : Probe X) :
    tsupport (v-sew (tint (bud x r h)) v) ⊆ tsupport v ∩ (ball x r)ᶜ := by
  apply closure_minimal _ ((isClosed_tsupport _).inter isOpen_ball.isClosed_compl)
  intro p hp
  change (v p- (sew _ v) p ≠ 0) at hp
  rw [sews] at hp
  refine ⟨?_,fun he => ?_⟩
  · refine subset_tsupport _ (fun H => hp ?_); change v p=0 at H; rw [H,mul_zero,sub_self]
  apply hp
  rw [tinted, (bud x r h).one_of_mem_closedBall (ball_subset_closedBall he)]; simp

theorem over_balls (u : Finset X) (r : X → ℝ) (h : ∀ x∈u, 0 < r x) (t : Probe X) (ht : HasCompactSupport ⇑t)
    (he : tsupport t ⊆ ⋃ x∈(u : Set X), Metric.ball x (r x))
    (hh : ∀ x∈u, IsVanishingOn F (closedBall x (r x+r x))) : F t=0 := by
  classical
  induction u using Finset.induction_on generalizing t with
  | empty =>
    replace he : tsupport t ⊆ ∅ := by simpa using he
    have hx : t=0 := by
      ext1 i; exact image_eq_zero_of_notMem_tsupport fun H => he H
    rw [hx,map_zero]
  | @insert x u hx IH =>
    let B := bud x (r x) (h x (Finset.mem_insert_self ..))
    let v := sew (tint B) t
    have hz : tsupport v ⊆ closedBall x B.rOut := (shrinks _ t).trans (inter_subset_left.trans (by rw [tint_support]))
    have hv := hh x (Finset.mem_insert_self ..) v hz
    let y := t-v
    have hy := trim_support x (r x) (h x (Finset.mem_insert_self ..)) t
    have hq : tsupport y ⊆ tsupport t := hy.trans inter_subset_left
    have hg : F y=0 := by
      refine IH (fun j hj => h j (Finset.mem_insert_of_mem hj)) y
        (ht.of_isClosed_subset (isClosed_tsupport _) hq) ?_ (fun j H => hh j (Finset.mem_insert_of_mem H))
      intro i hI
      obtain ⟨j,hj,H⟩ := Set.mem_iUnion₂.mp (he (hq hI))
      by_cases hw : j=x
      · rw [hw] at H; exact False.elim ((hy hI).2 H)
      exact Set.mem_iUnion₂.mpr ⟨_,Finset.mem_of_mem_insert_of_ne hj hw,H⟩
    change F (t-v)=0 at hg
    simpa [hv] using hg

lemma general_open (hs : IsOpen s) : IsVanishingOn F s ↔ Disjoint s (dsupport F) := by
  classical
  refine ⟨fun h => h.disjoint_dsupport hs,fun hx => ?_⟩
  rw [from_compact]; intro t ht he
  have hh (x : X) : ∃ r> (0:ℝ), x∈tsupport t → IsVanishingOn F (closedBall x (r+r)) := by
    by_cases h : x∈tsupport t
    · obtain ⟨w,hw,hW,H⟩ := (notMem_dsupport_iff x).1 (Set.disjoint_left.1 hx (ht h))
      obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds H)
      refine ⟨r/4,by positivity,fun _ => IsVanishingOn.mono (subset_trans ?_ hR) hw⟩
      exact closedBall_subset_ball (by linarith)
    exact ⟨1,by norm_num,fun H => False.elim (h H)⟩
  choose r hr hR using hh
  obtain ⟨p,hp,hFin,hq⟩ := he.elim_finite_subcover_image (b := tsupport t) (c := fun x => ball x (r x)) (fun _ _ => isOpen_ball)
    (fun x h => Set.mem_iUnion₂.mpr ⟨x,h,mem_ball_self (hr _)⟩)
  exact over_balls F hFin.toFinset r (fun i _ => hr i) t he (by rwa [Set.Finite.coe_toFinset]) (fun i hI => hR i (hp (by simpa using hI)))

/-- multiple intersecting carriers can be used DIRECTLY on Schwartz probes. -/
theorem due (M : Set X) (hm : IsClosed M) : dsupport F ⊆ M ↔ IsVanishingOn F Mᶜ := by
  rw [general_open F hm.isOpen_compl, disjoint_comm,← Set.subset_compl_iff_disjoint_right,compl_compl]
end YM.Boundary.Distn
