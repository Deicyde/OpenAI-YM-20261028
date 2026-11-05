import YM.Planned.PRIMARY_INTEGRAL_295.Nimbuses
import YM.Planned.PRIMARY_INTEGRAL_295.Oval



/-!
# Real relative inverse chart at normalization by positive covariance

IFT socket at Id for centered marginal of E.Jpr. At any base replace
by `rise` for tangent-standardized self-adjoint C near Id. Need only
C^k of moving data. Polynomial costs independent of dimension. This is
not a canonical globally assembled root. Only local *REPARAMETERIZATION*
of gaussian; will show equal law eventually at query, not assign a family
of alternative Gaussian histories/conventions globally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Kelps
open Nimbuses Function Filter Set Oval Metric
open scoped Topology ContDiff Classical BigOperators RightActions
variable {k n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section RingCosts
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : E → A}

lemma product_at (x:E) (hf:ContDiffAt ℝ n f x) (hg:ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y=> f y*g y) x‖ ≤ ∑ i∈Finset.range (n+1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
      ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  have he := (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨s,hs,hS,hx⟩:= _root_.mem_nhds_iff.mp he
  have hf' : ContDiffOn ℝ n f s:= fun z hz=> (hs hz).1.contDiffWithinAt
  have hg' : ContDiffOn ℝ n g s:= fun z hz=> (hs hz).2.contDiffWithinAt
  simpa only [iteratedFDerivWithin_of_isOpen _ hS hx] using
    (norm_iteratedFDerivWithin_mul_le hf' hg' hS.uniqueDiffOn hx (n:=n) (le_refl _))

def heats (c : ℝ) : ℕ → ℝ
  | 0 => 1+c
  | n+1 => heats c n + c + (∑ i∈Finset.range (n+2), ((n+1).choose i : ℝ))*heats c n^2
lemma heats_pos {c : ℝ} (hc : 0≤c) (n : ℕ) : 1≤heats c n := by
  induction n with
  | zero => apply le_add_of_nonneg_right hc
  | succ n ih => apply ih.trans; rw [heats,add_assoc]; apply le_add_of_nonneg_right; positivity


-- sqrt C =1+q, argument of relative point. q(0)=0
-- normalized to a real plate type so no M dimension.
lemma deposits (x:E) {c:ℝ} (hf:ContDiffAt ℝ n f x) (hg:ContDiffAt ℝ n g x) (h : Envelope x n f c)
    (hF : (fun z=>g z*g z+(2:ℝ) • g z+1) =ᶠ[𝓝 x] f) (he:g x=0): Envelope x n g (heats c n) := by
  have hC:=h.1
  induction n with
  | zero => exact ⟨zero_le_one.trans (heats_pos hC 0),fun n hn=>by
      have hg:n=0:=Nat.le_zero.mp hn; subst n; rw [norm_iteratedFDeriv_zero,he,norm_zero]; exact zero_le_one.trans (heats_pos hC 0)⟩
  | succ n ih =>
    let k:=n+1
    let r:= heats c n
    let m:=∑ i∈Finset.range (n+2), ((n+1).choose i : ℝ)
    have hm : 0≤m := by unfold m; positivity
    have hv : r ≤ heats c k := by rw [heats]; change r≤r+c+m*r^2; nlinarith
    have hN : (n:WithTop ℕ∞)≤((n+1:ℕ):WithTop ℕ∞):=Nat.cast_le.mpr (Nat.le_succ n)
    have hq := ih (hf.of_le hN) (hg.of_le hN) ⟨h.1,fun i hi=>h.2 i (Nat.le.step hi)⟩
    refine ⟨hq.1.trans hv,fun i hi=>?_⟩
    rcases Nat.eq_or_lt_of_le hi with rfl|h'
    swap; · exact (hq.2 i (Nat.le_of_lt_succ h')).trans hv
    let B (f:E→A):=iteratedFDeriv ℝ k f x
    let q := fun z=>g z*g z
    have hy (i:ℕ) (hi : i≤ k) : ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (k-i) g x‖ ≤ r^2 := by
      by_cases hz : i=0
      · rw [hz,norm_iteratedFDeriv_zero]; rw [he,norm_zero,zero_mul]; positivity
      by_cases ha : i=k
      · rw [ha,Nat.sub_self,norm_iteratedFDeriv_zero,he,norm_zero,mul_zero]; positivity
      rw [sq]; apply mul_le_mul (hq.2 i (by unfold k at *; omega)) (hq.2 (k-i) (by unfold k at *; omega)) (norm_nonneg _) hq.1
    have hl : ‖B q‖ ≤ m * r^2 := by
      unfold m; rw [Finset.sum_mul]; apply (product_at x hg hg).trans (Finset.sum_le_sum (fun i hi=>?_))
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hy i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (by positivity)
    have hs:=hg.const_smul (2:ℝ)
    let u : E→A:=fun _=>1
    have hz:= show ContDiffAt ℝ (↑k) u x from contDiffAt_const
    have hw : B q+(2:ℝ) • B g=B f := by
      have hd : B (q+(2:ℝ)•g+u)=B f:= (EventuallyEq.iteratedFDeriv ℝ hF k).eq_of_nhds
      have hv : B u=0 := by unfold B u; rw [iteratedFDeriv_const_of_ne (by omega : k≠0)]; rfl
      rw [show B (q+(2:ℝ)•g+u)=B q+(2:ℝ) • B g from by
        rw [show B (_+u)=B (q+(2:ℝ)•g)+B u from iteratedFDeriv_add_apply ((hg.mul hg).add hs) hz,hv,add_zero];
        rw [show B (q+(2:ℝ)•g)=B q+B ((2:ℝ) • g) from iteratedFDeriv_add_apply (hg.mul hg) hs];
        rw [show B ((2:ℝ) • g)=(2:ℝ) • B g from iteratedFDeriv_const_smul_apply hg]] at hd
      exact hd
    have ha : (2:ℝ)*‖B g‖≤c+m*r^2 := by
      have hs: (2:ℝ) • B g=B f-B q:=eq_sub_of_add_eq' hw
      have hn : ‖B f‖≤c:=h.2 k le_rfl
      rw [← Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2), ←norm_smul (2:ℝ),hs]; exact (norm_sub_le ..).trans (add_le_add hn hl)
    have hp :=hq.1; change 0≤r at hp
    change ‖B g‖ ≤ r+c+m*r^2; nlinarith [norm_nonneg (B g)]
end RingCosts

section Chart
variable {ι : Type*} [Fintype ι]
abbrev Plate (ι:Type*) [Fintype ι] := Sky ι→L[ℝ] Sky ι

/-- q solves (1+q)^2=given at Id eventual. use q=0 base. -/
def film (x:Plate ι) := x + (1/2:ℝ) • (x*x)
lemma film_smooth : ContDiffAt ℝ ∞ (film (ι:=ι)) 0 := contDiffAt_id.add ((contDiffAt_id.mul contDiffAt_id).const_smul (1/2:ℝ))
lemma film_speed : HasFDerivAt film ((ContinuousLinearEquiv.refl ℝ (Plate ι)) : Plate ι →L[ℝ] Plate ι) 0 := by
  have h:=hasFDerivAt_id (𝕜:=ℝ) (0:Plate ι)
  convert! h.add ((h.mul' h).const_smul (1/2:ℝ)) using 1
  ext; simp

private lemma notStop : (∞:WithTop ℕ∞)≠0:=by simp

def flow : Plate ι → Plate ι := film_smooth.localInverse film_speed notStop
lemma first : flow (0:Plate ι)=0 := by
  have h:=film_smooth.localInverse_apply_image (a:=(0:Plate ι)) film_speed notStop
  rw [show film (0:Plate ι)=0 from by simp [film]] at h; exact h
lemma flow_smooth : ContDiffAt ℝ ∞ (flow (ι:=ι)) 0 := by
  have h:=film_smooth.to_localInverse (a:=(0:Plate ι)) film_speed notStop
  rw [show film (0:Plate ι)=0 from by simp [film]] at h; exact h
lemma right : ∀ᶠ x in 𝓝 (0:Plate ι), film (flow x)=x := by
  have h := (film_smooth.hasStrictFDerivAt' (x:=(0:Plate ι)) film_speed notStop).eventually_right_inverse
  rw [show film (0:Plate ι)=0 from by simp [film]] at h; exact h
lemma left : ∀ᶠ x in 𝓝 (0:Plate ι), flow (film x)=x :=
    (ContDiffAt.hasStrictFDerivAt' film_smooth (film_speed (ι:=ι)) notStop).eventually_left_inverse

def start (x:Plate ι):=(1/2:ℝ) • (x-1)
def height (x:Plate ι) := flow (start x)
def rise (x:Plate ι) := 1+height x
@[simp] lemma starts : height (1:Plate ι)=0:= by simp [height,start,first]
lemma starPad (a b:Plate ι) : star (a+b)=star a +star b := map_add ContinuousLinearMap.adjoint a b
lemma starNot (a b:Plate ι) : star (a-b)=star a - star b := map_sub ContinuousLinearMap.adjoint a b
lemma starBoth (a b:Plate ι) : star (a*b)=star b * star a := ContinuousLinearMap.adjoint_comp a b
lemma starPlate : star (1:Plate ι)=1:= ContinuousLinearMap.adjoint_id
lemma costs (F:E→Plate ι) {c:ℝ} (x:E) (hf:ContDiffAt ℝ k F x) (hF:F x=1) (h: Envelope x k F c)
    (hH : ∀ᶠ y in 𝓝 x, star (F y)=F y) :
    ContDiffAt ℝ k (rise ∘ F) x ∧ rise (F x)=1 ∧ Envelope x k (rise ∘ F) (heats c k) ∧
      ∀ᶠ y in 𝓝 x, rise (F y)*star (rise (F y))=F y := by
  let φ:=start ∘ F
  let r:=flow ∘ φ
  have hφ : ContDiffAt ℝ k φ x := (hf.sub contDiffAt_const).const_smul (1/2:ℝ)
  have hx : φ x=0 := by simp [φ,start,hF]
  have hr : ContDiffAt ℝ k r x:= by
    have hz:= flow_smooth (ι:=ι); rw [←hx] at hz; exact (hz.of_le (show (k:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)).comp _ hφ
  have hX : r x=0 := by simp [r,hx,first]
  have hR : ∀ᶠ y in 𝓝 x, film (r y)=φ y := by
     have hw:= hφ.continuousAt.tendsto; rw [hx] at hw; exact hw.eventually right
  have he : (fun z => r z*r z+(2:ℝ) • r z+1) =ᶠ[𝓝 x] F := by
    filter_upwards [hR] with y hy
    have hf := congr_arg ((2:ℝ) • ·) hy; unfold film at hf
    change _=(2:ℝ) • ((1/2:ℝ) • (F y-1)) at hf
    rw [smul_add,smul_smul,smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul,one_smul] at hf
    rw [add_comm (r y*r y), hf,sub_add_cancel]
  have hE:=deposits x hf hr h he hX
  let p : E→Plate ι:=fun _=>1
  have hc : 1 ≤ heats c k :=heats_pos h.1 k
  change ContDiffAt ℝ k (p+r) x ∧ _ ∧ Envelope x k (p+r) (heats c k) ∧ _
  refine ⟨contDiffAt_const.add hr,by simp [rise,hF],⟨hE.1,fun n hn=>?_⟩,?_⟩
  · by_cases hw : n=0
    · rw [hw,norm_iteratedFDeriv_zero, Pi.add_apply,hX,add_zero]; exact ContinuousLinearMap.norm_id_le.trans hc
    rw [iteratedFDeriv_add_apply (f:=p) (g:=r) contDiffAt_const (hr.of_le (Nat.cast_le.mpr hn)),show iteratedFDeriv ℝ n p x=0 by unfold p; rw [iteratedFDeriv_const_of_ne hw]; rfl,zero_add]
    exact hE.2 n hn
  letI : ContinuousStar (Plate ι):= ⟨ContinuousLinearMap.adjoint.continuous⟩
  have hu := hr.continuousAt.star.tendsto
  rw [hX] at hu; rw [show star (0:Plate ι)=0 from map_zero ContinuousLinearMap.adjoint] at hu
  filter_upwards [hR, he, hH,hu.eventually left] with y hy hy' ha ht
  have hg : star (r y)=r y := by
    rw [←ht]; change flow _=flow _; congr 1
    have he:= congr_arg star hy
    unfold film at *
    change _=star ((1/2:ℝ) • (F y-1)) at he
    simp only [starPad,star_smul,starBoth,starNot,star_trivial,ha,starPlate] at he
    exact he
  change (1+r y)*star (1+r y)=F y
  rw [starPad,starPlate,hg,←hy']; simp only [add_mul,mul_add,one_mul,mul_one]
  rw [show (2:ℝ) • r y=r y+r y from two_smul ℝ (r y)]; abel
end Chart
end YM.Planned.PrimaryIntegral295.Kelps
