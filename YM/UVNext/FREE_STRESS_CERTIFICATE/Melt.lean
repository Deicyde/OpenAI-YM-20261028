import YM.UVNext.FREE_STRESS_CERTIFICATE.Mass

/-! Smooth unit-mass regularization. Joint continuity only required
off unregularized pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Set MeasureTheory Filter Analysis
open scoped Topology ContDiff RealInnerProductSpace

def melting (r : ℝ) (x : E4) := normal * (‖x‖^2 + r^2)⁻¹
lemma denom_ready (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) : ‖x‖^2+r^2 ≠ 0 := by
  rcases h with h|h
  all_goals apply ne_of_gt; positivity
lemma smooth_melt (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) : ContDiffAt ℝ ∞ (melting r) x := by
  unfold melting; exact contDiffAt_const.mul (((contDiff_norm_sq ℝ).contDiffAt.add contDiffAt_const).inv (denom_ready _ _ h))

lemma melt_first (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) (i : Axis) :
    grad i (melting r) x = -2*normal * x i * (‖x‖^2 + r^2)⁻¹^2 := by
  have hd := (((hasFDerivAt_inv (denom_ready _ _ h)).comp x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (r^2))).const_mul normal).fderiv
  change fderiv ℝ (melting r) x = _ at hd
  rw [grad,D,hd]; simp [two_smul,← inv_pow]
  rw [← real_inner_comm x,basis_inner]; ring
lemma melt_second (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) (i j : Axis) :
    grad j (grad i (melting r)) x = -2*normal * (basis j i) * (‖x‖^2+r^2)⁻¹^2 +
    8*normal*x j*x i*(‖x‖^2+r^2)⁻¹^3 := by
  let u (x : E4) := -2*normal * x i * (‖x‖^2 + r^2)⁻¹^2
  have hO : IsOpen {x : E4| r ≠ 0 ∨ x ≠ 0} := by
    rcases eq_or_ne r 0 with rfl|h
    · simpa [away] using open_away
    simp [h]
  have he : grad i (melting r) =ᶠ[𝓝 x] u := (show ∀ᶠ y in 𝓝 x, y∈{x : E4| r ≠ 0 ∨ x≠0} from hO.mem_nhds h).mono fun y hy => melt_first r y hy i
  rw [grad,GermD _ he]
  have ht := (((compAxis i).hasFDerivAt.const_mul (-2*normal)).mul
    (((hasFDerivAt_inv (denom_ready _ _ h)).comp x ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (r^2))).pow 2)).fderiv
  change fderiv ℝ u x = _ at ht
  rw [D,ht]; simp [two_smul,compAxis,-basis_eq,← inv_pow]
  rw [← real_inner_comm x,basis_inner]; ring
lemma melt_trace (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) : ∑ i : Axis, grad i (grad i (melting r)) x = -droplet r x := by
  have ht (i : Axis) : basis i i = 1 := by simp
  have he (i : Axis) : 8*normal*x i*x i = 8*normal*(x i)^2 := by ring
  simp_rw [melt_second r x h,ht,he,Finset.sum_add_distrib, mul_one, ← Finset.sum_mul,← Finset.mul_sum]
  rw [← EuclideanSpace.real_norm_sq_eq]; unfold droplet; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  have h := denom_ready r x h; field_simp; ring
lemma melt_harm (r : ℝ) (x : E4) (h : r ≠ 0) (j) :
    ∑ i : Axis, grad i (grad i (grad j (melting r))) x = - grad j (droplet r) x := by
  have hv i j : grad i (grad j (melting r)) = grad j (grad i (melting r)) := funext fun z =>
    grad_comm ((smooth_melt _ _ (Or.inl h)).of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) ..
  have hc (i z) : ContDiffAt ℝ ∞ (grad i (melting r)) z := grad_smooth i (smooth_melt _ _ (Or.inl h)) (by simp)
  have hh (i k l) : grad k (grad l (grad i (melting r))) x = grad l (grad k (grad i (melting r))) x :=
    grad_comm ((hc i x).of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) ..
  simp_rw [show ∀ i, grad i (grad i (grad j (melting r))) x = grad j (grad i (grad i (melting r))) x from
    fun i => by nth_rw 1 [hv i j]; exact hh i i j, ← grad_sum (f:=fun i => grad i (grad i (melting r)))
      (fun i => grad_smooth i (hc i _) (by simp)),show (fun y : E4 => ∑ i : Axis, grad i (grad i (melting r)) y)=-droplet r from
        funext fun _ => melt_trace _ _ (Or.inl h)]
  unfold grad D; rw [fderiv_neg]; rfl

-- regularized opposite curl
def partnerG (r : ℝ) (b k m : Axis) : E4 → ℝ :=
  (if k=b then grad m (melting r) else 0) - (if m=b then grad k (melting r) else 0)
def material (r : ℝ) (k m : Axis) : Maxwell.Field ℝ :=
  fun a b => grad a (partnerG r b k m) - grad b (partnerG r a k m)

lemma partner_smooth (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) (b _k m i : Axis) :
    ContDiffAt ℝ ∞ (if i=b then grad m (melting r) else (0:E4→ℝ)) x := by
  split
  · exact grad_smooth _ (smooth_melt _ _ h) (by simp)
  exact contDiffAt_const (𝕜:=ℝ) (x:=x) (c:=(0:ℝ))
lemma partner_patch (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) (b k m : Axis) : ContDiffAt ℝ ∞ (partnerG r b k m) x :=
  (partner_smooth r x h b k m k).sub (partner_smooth r x h b m k m)
lemma material_smooth (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) (k m a b : Axis) :
    ContDiffAt ℝ ∞ (material r k m a b) x :=
  (grad_smooth _ (partner_patch r x h b k m) (m:=∞) (by simp)).sub
    (grad_smooth _ (partner_patch r x h a k m) (m:=∞) (by simp))

lemma material_odd (r : ℝ) (k m a b : Axis) (x) : material r k m a b x = - material r k m b a x := by simp [material]
lemma material_cycle (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x≠0) (k m a b c : Axis) :
    grad a (material r k m b c) x + grad b (material r k m c a) x + grad c (material r k m a b) x = 0 := by
  have hd (a i : Axis) : ContDiffAt ℝ ∞ (grad a (partnerG r i k m)) x := grad_smooth _ (partner_patch r x h i k m) (by simp)
  unfold material
  rw [Bare.grad_sub (hd b c) (hd c b), Bare.grad_sub (hd c a) (hd a c), Bare.grad_sub (hd a b) (hd b a)]
  have hw (i) : ContDiffAt ℝ 2 (partnerG r i k m) x := (partner_patch r x h i k m).of_le
    (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  nth_rw 1 [grad_comm (hw c) a b]
  nth_rw 1 [grad_comm (hw b) a c]
  nth_rw 1 [grad_comm (hw a) b c]
  abel

lemma partner_at (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x ≠ 0) (k m a b : Axis) :
    grad a (partnerG r b k m) x = (if k=b then grad a (grad m (melting r)) x else 0) -
    (if m=b then grad a (grad k (melting r)) x else 0) := by
  rw [partnerG,Bare.grad_sub (partner_smooth r x h b k m k) (partner_smooth r x h b m k m)]
  split_ifs <;> simp [grad,D]
lemma partner_mute (r : ℝ) (x : E4) (h : r ≠ 0 ∨ x ≠0) (k m : Axis) :
    ∑ i : Axis, grad i (partnerG r i k m) x = 0 := by
  simp_rw [partner_at r x h,Finset.sum_sub_distrib]; simp
  apply sub_eq_zero.mpr; exact grad_comm ((smooth_melt _ _ h).of_le (show ((↑(2 : ℕ)):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) ..

lemma material_div (r : ℝ) (x : E4) (h : r ≠ 0) (k m b : Axis) :
    ∑ i : Axis, grad i (material r k m i b) x = (if m=b then grad k (droplet r) x else 0)-
      (if k=b then grad m (droplet r) x else 0) := by
  have ht (a b : Axis) := partner_patch r x (Or.inl h) a k m
  have hc (a i) : ContDiffAt ℝ ∞ (grad a (partnerG r i k m)) x := grad_smooth a (ht i m) (by simp)
  simp_rw [material,Bare.grad_sub (hc _ b) (hc b _),Finset.sum_sub_distrib, grad_comm
    ((ht _ m).of_le (show ((↑(2:ℕ)):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) _ b]
  have he (i) : grad i (partnerG r b k m) =
      (if k=b then grad i (grad m (melting r)) else 0)-(if m=b then grad i (grad k (melting r)) else 0) := by
    funext z; rw [partner_at r z (Or.inl h)]; split_ifs <;> rfl
  rw [← grad_sum (fun i => grad i (partnerG r i k m)) (fun i => hc i i),
    show (fun y => ∑ i : Axis, grad i (partnerG r i k m) y)=(fun _ => 0) from funext fun _ => partner_mute r _ (Or.inl h) ..]
  have hz (a) : grad a (fun _ : E4 => (0:ℝ)) x=0 := by simp [grad,D]
  rw [hz,sub_zero]
  have hw (a i c d : Axis) : ContDiffAt ℝ ∞ (if i=b then grad a (grad d (melting r)) else (0:E4→ℝ)) x := by
    split
    · exact grad_smooth _ (grad_smooth d (smooth_melt r x (Or.inl h)) (m:=∞) (by simp)) (by simp)
    exact contDiffAt_const (𝕜:=ℝ) (x:=x) (c:=(0:ℝ))
  simp_rw [he,Bare.grad_sub (hw _ k m m) (hw _ m k k),Finset.sum_sub_distrib]
  split_ifs <;> try simp_rw [melt_harm r x h] -- progress
  all_goals simp [grad,D]
  ring

lemma stillGreen (k m a b) : material 0 k m a b = bareCurl a b k m := by
  rw [material,partnerG,partnerG,show melting 0 = Green from by funext z; simp [melting,Green]]; rfl

-- Uniform enough for shell integrals: joint continuity, including r=0 if
-- not at origin.
lemma jointly {r : ℝ} {x : E4} (hx : x ≠ 0) (k m a b : Axis) :
    ContinuousAt (fun w : ℝ × E4 => material w.1 k m a b w.2) (r,x) := by
  let f (a b : Axis) (w : ℝ × E4) := -2*normal*basis a b*(‖w.2‖^2+w.1^2)⁻¹^2 +
    8*normal*w.2 a*w.2 b*(‖w.2‖^2+w.1^2)⁻¹^3
  have hc j i : ContinuousAt (f j i) (r,x) := by
    have he : ContinuousAt (fun w : ℝ × E4 => (‖w.2‖^2+w.1^2)⁻¹) (r,x) :=
      ((continuous_snd.norm.pow 2).add (continuous_fst.pow 2)).continuousAt.inv₀ (denom_ready r x (Or.inr hx))
    have h (i : Axis) : ContinuousAt (fun w : ℝ × E4 => w.2 i) (r,x) := by fun_prop
    exact (continuousAt_const.mul (he.pow 2)).add (((continuousAt_const.mul (h _)).mul (h _)).mul (he.pow 3))
  let g (a b i j : Axis) := fun w => if i=b then f a j w else 0
  apply ContinuousAt.congr_of_eventuallyEq (f:=fun w => (g a b k m w-g a b m k w)-(g b a k m w-g b a m k w))
  · have he (a b i j) : ContinuousAt (g a b i j) (r,x) := by
      unfold g; by_cases ht : i=b; simpa [ht] using hc a j; simpa [ht] using (continuousAt_const (x:=(r,x)) (y:=(0:ℝ)))
    exact ((he _ _ _ _).sub (he _ _ _ _)).sub ((he _ _ _ _).sub (he _ _ _ _))
  filter_upwards [continuousAt_snd.tendsto.eventually (Maxwell.open_away.mem_nhds (x:=x) hx)] with w hw
  unfold material; simp only [Pi.sub_apply]; rw [partner_at _ _ (Or.inr hw),partner_at _ _ (Or.inr hw)]
  simp_rw [melt_second _ _ (Or.inr hw)]
  rfl

end YM.UVNext.FreeStress
