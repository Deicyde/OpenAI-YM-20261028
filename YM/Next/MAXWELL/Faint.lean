import YM.Next.MAXWELL.Leading

/-! # One power of angular regularity missing -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {r s j l n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma rad_add (s t : ℕ) : rad (s+t)=rad s * rad t := funext fun x => pow_add (‖x‖^2) _ _
lemma rad_pos (r : ℕ) {x : E4} (hx : x ∈ away) : 0 < rad r x := by have ht := norm_pos_iff.mpr (show x ≠ 0 from hx); unfold rad; positivity

lemma rad_grad {x : E4} (i : Axis) : grad i (rad 1) x=2*x i := by
  rw [show rad 1 = fun x : E4 => ‖x‖^2 from funext fun x => pow_one _]
  simp only [grad,D,(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp [inner4,two_smul,two_mul]
lemma rad_lap (x : E4) : lap (rad 1) x=8 := by
  unfold lap
  have ht (i : Axis) : grad i (grad i (rad 1)) x = 2 := by
    let L := (2:ℝ) • compAxis i
    have hh : grad i (rad 1)=L := funext fun _ => rad_grad i
    rw [hh,grad,D,L.fderiv]; change (2:ℝ)*basis i i=2; simp
  simp_rw [ht]; simp [Axis]; ring

lemma rad_derive {x : E4} (i : ℕ) (hx : x ∈ away) : D x (rad i) x = 2*i*rad i x := by
  have he := Pole.rad_D i x x
  apply mul_left_cancel₀ (rad_pos 1 hx).ne'
  rw [he,show D x (rad 1) x = 2*rad 1 x from ?_]; ring
  rw [show rad 1 = fun x : E4 => ‖x‖^2 from funext fun x => pow_one _]
  simp [D,two_mul, (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv, two_smul]

lemma spread_at {x : E4} (f : E4 → F) : ∑ i, x i • grad i f x = D x f x := by
  conv_rhs => arg 1; rw [show x=∑ i : Axis,x i • basis i by ext i; simp]
  rw [D,map_sum]; simp only [map_smul]; rfl

lemma lap_multiply {f : E4 → F} {x : E4} (hf : ContDiffAt ℝ ω f x) :
    lap (rad 1 • f) x = (8:ℝ) • f x + (4:ℝ) • D x f x + rad 1 x • lap f x := by
  let F' := rad 1
  have ht {h : E4 → ℝ} {f : E4 → F} (i : Axis) {x : E4} (hh : DifferentiableAt ℝ h x) (hw : DifferentiableAt ℝ f x) :
      grad i (h • f) x=h x • grad i f x+grad i h x • f x := by simp [grad,D,fderiv_smul hh hw]
  have hF := rad_diff 1
  have he (i) : grad i (grad i (rad 1 • f)) x=grad i (grad i (rad 1)) x • f x +
      (4:ℝ) • x i • grad i f x + rad 1 x • grad i (grad i f) x := by
    have hK : grad i (rad 1 • f) =ᶠ[𝓝 x] rad 1 • grad i f + grad i (rad 1) • f := by
      filter_upwards [hf.eventually (by simp)] with y hy; exact ht i (hF.differentiable (by simp) _) (hy.differentiableAt (by simp))
    have hL : DifferentiableAt ℝ (rad 1) x := hF.differentiable (by simp) _
    have hg : DifferentiableAt ℝ (grad i (rad 1)) x := (grad_smooth i hF.contDiffAt (m:=ω) le_top).differentiableAt (by simp)
    have hv := hf.differentiableAt (by simp)
    have hu := (grad_smooth i hf (m:=ω) le_top).differentiableAt (by simp)
    change D _ _ _=_
    rw [GermD _ hK, D,fderiv_add (hL.smul hu) (hg.smul hv)]
    change grad i (rad 1 • grad i f) x + grad i (grad i (rad 1) • f) x=_
    rw [ht i hL hu,ht i hg hv,rad_grad]
    let T := x i • grad i f x
    rw [show (4:ℝ) • T=(2:ℝ) • T+(2:ℝ) • T from by rw [← add_smul,show (2:ℝ)+2=4 by norm_num],show (2 * x i) • grad i f x=(2:ℝ) • T from (smul_smul (2:ℝ) ..).symm]; abel
  unfold lap; simp_rw [he,Finset.sum_add_distrib, ← Finset.sum_smul,← Finset.smul_sum]
  rw [spread_at,show (∑ i, grad i (grad i (rad 1)) x)=8 from rad_lap x]

lemma lap_valued {r : ℕ} {f : E4 → F} (H : Pole r f) (s : ℕ) {x} (hx : x∈away) :
    lap (rad (s+1) • f) x = (4*(s+1:ℕ)*((s:ℝ)+2 - (r:ℝ)):ℝ) • rad s x • f x := by
  have L : lap f x=0 := H.Laplace hx
  have ht : rad 0 • f=f := funext fun i => by simp [rad]
  induction s with
  | zero => rw [ht.symm] -- beware replacing f on both
            change lap (rad 1 • rad 0 • f) x=_
            rw [lap_multiply ((rad_diff _).contDiffAt.smul (H.diff x hx)),ht,pole_power H hx,L]
            norm_num [rad]; rw [smul_smul, ← neg_smul, ← add_smul]; congr 1; ring
  | succ s ih =>
    let k := s+1
    have hh : rad (s+1+1) • f=rad 1 • rad k • f := by
      funext y; change rad (s+1+1) y • f y=rad 1 y • (rad k y • f y)
      rw [smul_smul]; congr 1; simp [rad,k]; ring
    rw [hh,lap_multiply ((rad_diff _).contDiffAt.smul (H.diff x hx)),show (rad k • f) x=rad k x • f x from rfl]
    have he : D x (rad k • f) x = (rad k x) • D x f x + D x (rad k) x • f x := by
      rw [D,fderiv_smul ((rad_diff _).differentiable (by simp) x) ((H.diff x hx).differentiableAt (by simp))]; rfl
    rw [he,show k=s+1 from rfl,ih, rad_derive _ hx,pole_power H hx]; simp only [smul_add,smul_smul]; simp_rw [← add_smul]
    congr 1; push_cast; simp only [rad_add, Pi.mul_apply]; ring

lemma clears_faint {f : E4 → F} (H : Pole r f) (hr : 2 ≤ r) (S : Clears (r-2) f) : EqOn f 0 away := by
  have he {s : ℕ} (B : Clears s f) (h : s < r-1) : Clears 0 f := by
    induction s with
    | zero => exact B
    | succ s ih =>
      apply ih _ (by omega)
      obtain ⟨g,hg,hv⟩ := B
      let w := (4*(s+1:ℕ)*((s:ℝ)+2 - (r:ℝ)):ℝ)
      have hw : w≠0 := by
        have ht : s+2 < r := by omega
        apply mul_ne_zero (by positivity); apply sub_ne_zero.mpr
        exact (by exact_mod_cast Nat.ne_of_lt ht : (s:ℝ)+2≠r)
      refine ⟨w⁻¹ • lap g,(contDiff_iff_contDiffAt.mpr fun y => lap_smooth hg.contDiffAt).const_smul _,fun x hx => ?_⟩
      have he : g =ᶠ[𝓝 x] rad (s+1) • f := (show EqOn g _ away from fun y h => (hv y h).symm).eventuallyEq_of_mem (open_away.mem_nhds hx)
      rw [Pi.smul_apply, lap_local he, lap_valued H s hx]; exact (inv_smul_smul₀ hw _).symm
  obtain ⟨g,hg,hv⟩ := he S (by omega)
  intro x hx
  let y (t : ℝ) := t • x
  have ht : Tendsto id little (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hm := (ht.pow r).smul ((hg.continuous.continuousAt (x:=(0:ℝ) • x)).tendsto.comp (ht.smul tendsto_const_nhds))
  rw [zero_pow (n:=r) (by omega),zero_smul] at hm
  have hv : Tendsto (fun _ : ℝ => f x) little (𝓝 0) := by
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t hl
    change t^r • g (y t)=f x
    have h : 0 < t := hl
    rw [← hv _ (show y t∈away from smul_ne_zero h.ne' hx),show rad 0 _=1 from pow_zero _,one_smul]
    unfold y; rw [H.degree _ h _ hx,inv_pow,smul_inv_smul₀ (by positivity : t^r≠0)]
  exact tendsto_nhds_unique tendsto_const_nhds hv
end YM.Maxwell.Free
