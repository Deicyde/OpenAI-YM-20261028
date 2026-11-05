import YM.Planned.PRIMARY_INTEGRAL_295.Melt
import YM.Planned.PRIMARY_INTEGRAL_295.Water

/-!
# One-clock Gaussian moment budget payment

Actual varying square root. Γ-scores are restricted on the moving
hulls; all transition directions charged via tails, including threshold
and variation of density. Polynomial powers allowed here at POST-L
costs; don't sum unweighted trigger nodes or omit fine gas label scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Porous
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place Emits Ripple Purse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {S : Finset Cover} {k n m l : ℕ} {t ξ s M : ℝ}

def sleepCost (k:ℕ) (M:ℝ) := (1+k*(k.factorial*M*(1+M)^k))*M^2 -- uniform mass error and small slide slip
lemma sleepy (M:ℝ) (h:1≤M) (k:ℕ) : 1 ≤ sleepCost k M := by
  unfold sleepCost; refine one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) (one_le_pow₀ h)

def thick (k m : ℕ) := creep k*(m+1)

def sailPrice (B : Roof S G) (k m : ℕ) (M : ℝ) := (sleepCost k M + oasis B k M)*(1+3*oasis B k M)^m
lemma sail_ge (B : Roof S G) (k m : ℕ) (hp : 1≤M) : 1≤sailPrice B k m M := by
  have he:=oasis_gold B k hp; have hh:=sleepy M hp k; unfold sailPrice
  exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))

-- post L+height & exponent+section costs. Need multiply by t+ξ+s later.

def flask (B : Roof S G) (k l : ℕ) (M : ℝ) :=
    sailPrice B k (l+k) M * outsize (thick k (l+k)) * (1+M)^((thick k (l+k))+1)
lemma flask_ge (B : Roof S G) (k l : ℕ) (h:1≤M) : 1≤flask B k l M := by
  have ht:=sail_ge B k (l+k) h; have hp:=outsize_ge (thick k (l+k)); unfold flask
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht hp) (one_le_pow₀ (by linarith))

namespace Stand
variable (h : Stand I E S G) (B : Roof S G) {Q:E→Dev S G} (hc : h.Calls B Q t ξ s k M)
include hc
lemma rho_cont : Continuous (fun x:Sky I=> h.rho x 0) := continuous_iff_continuousAt.mpr fun x =>
  (h.weightJoint B hc x).continuousAt.comp (f:=fun x:Sky I=> (x,(0:E))) (continuousAt_id.prodMk continuousAt_const)

lemma rho_price (x : Sky I) :
    ‖h.rho x 0-1‖ ≤ sleepCost k M * ξ * breath x ^ creep k ∧
    Purse.slip (h.rho x) 0 k ≤ sleepCost k M * ξ * breath x ^ creep k := by
  classical
  let q:=h.square 0 x; let r:=breath x; let C:=sleepCost k M * ξ * breath x ^ creep k
  have hg:=hc.noise.1; have hm:=hc.paid; have hp := sleepy M hm k; have ht := show 1≤r from breath_ge x
  have hT:=breath_ge x
  have he : 0≤C:=by unfold C; positivity
  by_cases hz : M*ξ*‖q‖ < 1
  · have H : h.rho x =ᶠ[𝓝 (0:E)] 1 := by
      have hb : ContinuousAt (fun y=> M*ξ*‖h.square y x‖) 0 := continuousAt_const.mul (h.sphere B hc x).1.continuousAt.norm
      exact (hb.eventually (gt_mem_nhds hz)).mono (fun y hy=> (hc.cover _).2.1 hy.le)
    change ‖_-1‖≤ C ∧ _≤ C; rw [H.self_of_nhds]; simp only [Pi.one_apply,sub_self,norm_zero]; refine ⟨he,?_⟩
    rw [Purse.slip, Finset.sum_eq_zero]; swap
    · intro i _; rw [(H.iteratedFDeriv ℝ _).self_of_nhds];
      change ‖iteratedFDeriv ℝ (i+1) (fun _ : E=> (1:ℝ)) 0‖=0
      rw [iteratedFDeriv_const_of_ne (by simp)]; simp
    exact he
  let F:=(k.factorial:ℝ)*M*(1+M)^k
  have hF := show 1 ≤ F from one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast k.factorial_pos) hm) (one_le_pow₀ (by linarith))
  have hz : 1 ≤ M^2*ξ*r := (le_of_not_gt hz).trans ((mul_le_mul_of_nonneg_left
    ((h.sphere B hc x).2.value.trans (mul_le_mul_of_nonneg_left (show ‖x‖ ≤ r from le_add_of_nonneg_left zero_le_one) (zero_le_one.trans hm)))
      (mul_nonneg (zero_le_one.trans hm) hg.le)).trans_eq (by ring))
  have h1 : 1 ≤ r^k := one_le_pow₀ ht
  have hh : (1+k*F) * r^k ≤ C := by
    calc
      _ ≤ ((1+k*F)*r^k)*(M^2*ξ*r) := le_mul_of_one_le_right (by positivity) hz
      _ = sleepCost k M*ξ*r^(k+1) := by unfold sleepCost F; ring
      _ ≤ C := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (Nat.le_succ _)) (by positivity)
  obtain ⟨hL,hR⟩:= (hc.cover q).1
  have hl': ‖h.rho x 0-1‖ ≤ 1 := by change ‖h.gamma q-1‖ ≤ _; rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith,by linarith⟩
  refine ⟨hl'.trans ((_root_.one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) h1).trans hh),?_⟩
  apply le_trans _ hh; unfold Purse.slip
  have hs j (hj:j∈Finset.range k) : ‖iteratedFDeriv ℝ (j+1) (h.rho x) 0‖≤ F*r^k := (h.exposed B hc x).2.2 _ (Finset.mem_range.mp hj)
  apply (Finset.sum_le_sum hs).trans; simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)

lemma gums (x : Sky I) (m : ℕ) : Purse.due (h.rho x) 0 k m (ore B k M t ξ s x)
      ≤ (t+ξ+s)*sailPrice B k m M*breath x ^ (thick k m) ∧
    ‖h.rho x 0-1‖ ≤ (t+ξ+s)*sailPrice B k m M*breath x ^ (thick k m) := by
  let q:= t+ξ+s
  have hq : ξ ≤ q ∧ q ≤ 3 := by have ht:=hc.rate; have hh:=hc.noise; have he:=hc.error; simp only [Set.mem_Ioc,Set.mem_Icc] at ht hh he; constructor <;> unfold q <;> linarith
  let a:=creep k; let v:= breath x^a; let C:=oasis B k M; let D:=sleepCost k M; let r:=C+D; let e:=q*C*v
  have hp:=hc.noise.1; have hP : 0<q:=hp.trans_le hq.1
  have hv : 1 ≤ v:=one_le_pow₀ (breath_ge _)
  have hC : 1≤C:=oasis_gold B k hc.paid; have hD : 1≤D:=sleepy _ hc.paid k
  obtain ⟨h₁,h₂⟩:=h.rho_price B hc x
  have ht : D*ξ*v ≤ D*q*v := by gcongr; exact hq.1
  have hγ : ‖h.rho x 0‖≤1:= by
    obtain ⟨hg,hg'⟩:= (hc.cover (h.square 0 x)).1; unfold rho; rwa [Real.norm_of_nonneg hg]
  let w:=(1+3*C)*v; have hW : 1≤w:=one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) hv
  have he : q*r*v*w^m=(t+ξ+s)*sailPrice B k m M*breath x ^ (thick k m) := by
    unfold r w q v D C a sailPrice thick; rw [pow_mul,mul_pow]; ring
  have hr : ‖h.rho x 0‖*e + Purse.slip (h.rho x) 0 k ≤ q*r*v := calc
    _ ≤ 1*e + D*q*v := add_le_add (mul_le_mul_of_nonneg_right hγ (show 0≤e by unfold e; positivity)) (h₂.trans ht)
    _ = _ := by unfold r e; ring
  rw [← he]; constructor
  · unfold Purse.due
    have hh : 1+e≤w := by unfold w e; nlinarith [mul_le_mul_of_nonneg_right hq.2 (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hv))]
    apply mul_le_mul hr (pow_le_pow_left₀ (show 0 ≤ 1+e by unfold e; positivity) hh _) (pow_nonneg (show 0 ≤ 1+e by unfold e; positivity) m)
       (show 0≤q*r*v by unfold r; positivity)
  exact (h₁.trans ht).trans (le_trans (show D*q*v ≤ q*r*v from by unfold r; nlinarith [mul_nonneg (show 0≤q*C by positivity) (show 0≤v by positivity)])
    (le_mul_of_one_le_right (by unfold r; positivity) (one_le_pow₀ hW)))

lemma due_meas (m : ℕ) : AEStronglyMeasurable (fun x:Sky I=> Purse.due (h.rho x) 0 k m (ore B k M t ξ s x)) (stdGaussian (Sky I)) := by
  let g (x:Sky I):= h.rho x
  have ht i (hi:i∈Finset.range k) : Continuous (fun x=>‖iteratedFDeriv ℝ (i+1) (g x) 0‖) := by
    apply Continuous.norm; apply continuous_iff_continuousAt.mpr; intro x
    exact (vert_cont (weightJoint h B hc x) (Finset.mem_range.mp hi)).comp (f:=fun x=> (x,(0:E)))
      (continuousAt_id.prodMk continuousAt_const)
  have hu : Continuous (fun x:Sky I=>ore B k M t ξ s x) := continuous_const.mul ((continuous_breath _).pow _)
  unfold Purse.due; apply Continuous.aestronglyMeasurable
  refine (((rho_cont h B hc).norm.mul hu).add (continuous_finsetSum _ ht)).mul ((continuous_const.add hu).pow _)

/-- The `δ` currency simultaneously charges moving Γ pay and errors. -/
theorem shoot_clock (l:ℕ) : Emits.Clock (stdGaussian (Sky I)) k l Q (h.skyW B ξ t) h.rho 0 t 1 (ore B k M t ξ s) ((t+ξ+s)*flask B k l M) := by
  classical
  let q:=t+ξ+s; let m:=l+k
  let D := sailPrice B k m M; let n:=thick k m; let φ (x:Sky I):= breath x^n
  let L:=(stdGaussian (Sky I)); let t':=1+(Fintype.card I:ℝ)
  obtain ⟨hk,hZ⟩:= rains I n
  have hp:=sail_ge B k m hc.paid; have ht:=hc.rate.1; have hh:=hc.noise.1; have hs:=hc.error.1
  have hq : 0≤q:=add_nonneg (add_nonneg ht.le hh.le) hs
  let r x:=q*D*φ x
  have he : Integrable r L := hk.const_mul _
  have hy : (∫ x, r x ∂L) ≤ (t+ξ+s)*flask B k l M := by
    unfold r; rw [integral_const_mul]; have hD:0≤D:=zero_le_one.trans hp
    refine (mul_le_mul_of_nonneg_left hZ (show 0 ≤ q*D by positivity)).trans ?_
    change q*D*(outsize n*t'^(n+1)) ≤ q*(D*outsize n*(1+M)^(n+1))
    rw [mul_assoc q D, mul_assoc D];
    gcongr; swap; exact add_le_add_right hc.size _
    exact zero_le_one.trans (outsize_ge _)
  let f(x:Sky I):= h.rho x 0
  have hz := h.rho_price B hc
  have hF : Integrable f L := by
    apply Integrable.of_bound (rho_cont h B hc|>.aestronglyMeasurable) 1; refine Eventually.of_forall fun x=> ?_
    unfold rho; obtain ⟨hg,hg'⟩:= (hc.cover (h.square 0 x)).1; rwa [Real.norm_of_nonneg hg]
  let p x:= Purse.due (h.rho x) 0 k m (ore B k M t ξ s x)
  have hg x : p x≤r x:=(h.gums B hc x m).1
  have hi : Integrable p L := he.mono' (h.due_meas B hc m) (Eventually.of_forall fun x=>
    (Real.norm_of_nonneg (tab _ _ _ _ _ (h.ore_nonneg B hc x))).trans_le (hg x))
  refine ⟨Eventually.of_forall (fun i=> ⟨h.W_clean B hc i,(h.exposed B hc i).1⟩),Eventually.of_forall (fun i=>⟨h.ore_nonneg B hc i,h.gem B hc i⟩),
    mul_nonneg hq (zero_le_one.trans (flask_ge B k l hc.paid)),⟨hi,(integral_mono hi he hg).trans hy⟩,hF,?_⟩
  change ‖(∫ x, f x ∂stdGaussian (Sky I))-1‖ ≤ _
  have he : (∫ x:Sky I, f x-1 ∂stdGaussian (Sky I)) = (∫ x,f x ∂L)-1 := by rw [integral_sub (g:=fun _=>1) hF (integrable_const _)]; simp [L]
  rw [← he]; apply (norm_integral_le_of_norm_le (g:=r) (hk.const_mul _) (Eventually.of_forall fun x=> (h.gums B hc x m).2)).trans hy
end Stand
end YM.Planned.PrimaryIntegral295.Porous
