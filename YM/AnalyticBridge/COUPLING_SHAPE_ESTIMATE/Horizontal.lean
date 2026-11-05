import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Pricing
import YM.Push.PRICE_COMPILER.Flows

/-!
# Zero affine Hessian after response subtraction at a row pair

Only asks this on nonwrapping supports in their **final** coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice Wilson RG Next.Scheduling.Wages Work Push.Local ProjectorNext.Equivariance Precision Exterior
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} (P : PathData G) (c : Clip) (b : BudgetPoint)

lemma turns_zero (w : Walk) (x : Site n) : travel (1:Config G n) x w = 1 := by induction w generalizing x <;> simp_all [travel,Step.read]
lemma stub (P : PathData G) (c : Clip) (j : Sequence) : raw (n:=n) P c j 1=0 ∧ response (n:=n) P c j 1=0 := by
  have h (s : Slot) : s.atSite (1:Config G n) 0=0 := by rw [F03.atSite_path,faceValue,turns_zero,turns_zero, G.curvature_unit,map_zero]
  rcases j with ⟨x, w|d⟩
  · simp [raw,response, faceValue,turns_zero,clover_zero]
  simp [raw,response,h,clover_zero]

lemma routeAt (s : Slot) : touched (F03.slotFace s (0:Site n)) ⊆ walkCuts s 0 := by
  have he (x : Cover) (l : Walk) : visits (wrap n x) l=(visits x l).map (wrap n) := by
    induction l generalizing x with
    | nil => rfl
    | cons a l ih => simp only [visits,List.map_cons,← ih (x+a.vec),map_add,wrap_vec]
  unfold touched F03.slotFace; rw [add_zero, he s.offset]
  intro i hi; obtain ⟨x,hx,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hi); exact Finset.mem_image.mpr ⟨x,Finset.mem_union_right _ (List.mem_toFinset.mpr hx),add_zero _⟩

private lemma needle_rate {f : ℝ → G.Color} {x} (hh : HasDerivAt f x 0) (hz : f 0=0) :
    Tendsto (fun t : ℝ => t⁻¹ • f t) (𝓝[≠] 0) (𝓝 x) := by simpa [hz] using (hasDerivAt_iff_tendsto_slope_zero.mp hh)
private lemma pair_rate {α β : ℝ → G.Color} {m F L} (H₁ : Tendsto (fun t : ℝ => t⁻¹ • α t) (𝓝[≠] 0) (𝓝 F))
    (H₂ : Tendsto (fun t : ℝ => t⁻¹ • β t) (𝓝[≠] 0) (𝓝 L)) :
    Tendsto (fun t : ℝ => (m * ⟪α t,β t⟫_ℝ) / t^2) (𝓝[≠] 0) (𝓝 (m*⟪F,L⟫_ℝ)) := by
  apply ((H₁.inner H₂).const_mul m).congr'; filter_upwards with t
  rw [real_inner_smul_left, real_inner_smul_right]; ring

lemma raw_respond (hn : 2 ≤ n.val) (j : Sequence) {D : Leaning G} {e : Offset G} {A : Directions G n}
    (hA : OnStencil 0 (imageOf P b j) e D A) (hs : G.Simple) (hx : Nonwrapping (imageOf (n:=n) P b j) 0) :
    H (raw P c j) A A=H (response P c j) A A := by
  let w (t : ℝ) := increment 1 (t • A)
  have he (x : PlaqAxes) : Tendsto (fun t : ℝ => t⁻¹ • needles 0 (w t) x) (𝓝[≠] 0) (𝓝 (skew D x)) :=
    needle_rate ((hasDerivAt_pi ..).mp (clover_jet 0 hn hx hA (ringlet_sub ..)) x) (by simp only [w,zero_smul,G07.at_zero_increment,clover_zero,Pi.zero_apply])
  have hu (t : ℝ) : represent (t • windDir A)=w t := by
    unfold represent; rw [show collect G (t • windDir A)=t • collect G (windDir A) from rfl, collect_wind]
  have hh:= raw_reg (n:=n) P c b j; have hl := response_reg (n:=n) P c b j
  rcases j with ⟨x,l|d⟩
  · have h := F03.face_deriv (directWord x) (windDir A)
    have hE : F03.faceCurl (directWord x) (windDir A)=skew D x := by
      rw [F03.faceCurl,← fundamental,collect_wind]
      exact curl_square hn hx hA _ _ (local_square (directWord x))
    simp_rw [hE,hu] at h
    have hp := F03.price_limit (V:=fun t => faceValue (w t) (directWord x)) (by simp [w,G07.at_zero_increment,faceValue,square,travel]) h
    let m:=weight*c.direct
    have hy : Tendsto (fun t : ℝ => (raw P c (x,Sum.inl l) (w t))/t^2) (𝓝[≠] 0) (𝓝 (m* (‖skew D x‖^2/2))) := by simpa [m,raw,mul_div_assoc] using! hp.const_mul m
    have ht : Tendsto (fun t : ℝ => (response P c (x,Sum.inl l) (w t))/t^2) (𝓝[≠] 0) (𝓝 (m/2* ⟪skew D x,skew D x⟫_ℝ)) :=
      pair_rate (α:=fun t => needles 0 (w t) x) (β:=fun t => needles 0 (w t) x) (he x) (he x)
    rw [from_ray hs hh hy, from_ray hs hl ht,real_inner_self_eq_norm_sq]; ring
  have h (v : Slot) (hv : walkCuts v 0⊆imageOf (n:=n) P b (x,Sum.inr d)) :
      Tendsto (fun t : ℝ => t⁻¹ • v.atSite (w t) 0) (𝓝[≠] 0) (𝓝 (skew D v.plaq)) := by
    have hs := F03.slot_limit v 0 (windDir A)
    have he : F03.faceCurl (F03.slotFace v 0) (windDir A)=skew D v.plaq := by
      rw [F03.faceCurl,← fundamental,collect_wind]; exact curl_square hn hx hA _ v.plaq ((routeAt v).trans hv)
    simpa only [he,hu] using hs
  let l:= first P x d.1; let r:=first P x d.2; let a:=copper P x d* ⟪skew D l.plaq,skew D r.plaq⟫_ℝ
  have h₁ : Tendsto (fun t : ℝ => raw P c (x,Sum.inr d) (w t)/t^2) (𝓝[≠] 0) (𝓝 a) :=
    pair_rate (α:=fun t => l.atSite (w t) 0) (β:=fun t => r.atSite (w t) 0) (h l (zone_left ..)) (h r (zone_right ..))
  have h₂ : Tendsto (fun t : ℝ => response P c (x,Sum.inr d) (w t)/t^2) (𝓝[≠] 0) (𝓝 a) :=
    pair_rate (α:=fun t => needles 0 (w t) l.plaq) (β:=fun t=>needles 0 (w t) r.plaq) (he _) (he _)
  rw [from_ray hs hh h₁, from_ray hs hl h₂]

lemma cardResponds (hn : 2 ≤ n.val) (j : Card n) (hs : G.Simple) (hx : Nonwrapping (cardSite P b j).support j.1)
    {A B a d e u} (hA : OnStencil j.1 (cardSite P b j).support a d A) (hB : OnStencil j.1 (cardSite P b j).support e u B) :
    H (j.read (raw P c j.token)) A B = H (j.read (response P c j.token)) A B := by
  let s:=j.turns; let x:=j.1; let X:= imageOf (n:=n) P b j.token
  have ht : Nonwrapping X 0 := (nonwrapping_turn ..).mp (show Nonwrapping _ (affine s x 0) from j.pull_home.symm ▸ hx)
  have transfer (f : Wilson.Config G n→ℝ) (h : b.Regular X f) (B : Directions G n) :
      H (j.read f) B B=H f (pulledDirection s x 1 B) (pulledDirection s x 1 B) := by
    change H (f ∘ pull s x) B B=_
    rw [diagonal hs (WardBin.Wheels.regular_carry s x h),diagonal hs h]
    simp_rw [comp_apply, pull_increment,pull_empty,map_smul]
  let f := raw (n:=n) P c j.token; let g:=response (n:=n) P c j.token
  have hf : b.Regular X f := raw_reg ..; have hg : b.Regular X g := reg_extend (response_reg ..) (ringlet_sub ..)
  have he {C w b'} (hh : OnStencil j.1 (cardSite P b j).support w b' C) : H (j.read f) C C=H (j.read g) C C := by
    obtain ⟨c',d',h'⟩:=pull_onSt s x hn ht (show OnStencil (affine s x 0) (X.image (affine s x)) w b' C from by rwa [show affine s x 0=j.1 from j.pull_home])
    rw [transfer f hf,transfer g hg]; exact raw_respond P c b hn _ h' hs ht
  have hp := he (hA.add hB)
  have hh : b.Regular (cardSite P b j).support (j.read f) := WardBin.Wheels.regular_carry s x hf
  have hh' : b.Regular (cardSite P b j).support (j.read g) := WardBin.Wheels.regular_carry s x hg
  rw [polar hh,polar hh',he hA,he hB] at hp
  change H (j.read f) A B=H (j.read g) A B; linarith
end YM.AnalyticBridge.CouplingShape
