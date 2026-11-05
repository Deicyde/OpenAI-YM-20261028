import YM.Next.MAXWELL.Casting

/-!
# Actual Lorentz representation on fields and their union

Contour sign fixed: parameter evaluates at `-I t`; adjoint includes
reflection of time even after descent. No Lie-group integration theorem assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis Complex Mink
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder

private lemma time_reversal (x : E4) (a : Axis) :
    Ortho.move (Signed.reflect timeAxis) x a=if a=timeAxis then -x timeAxis else x a := by
  by_cases h : a=timeAxis <;> simp [h]

lemma negates_angle (a : SpaceAxis) (t : ℝ) :
    let U := Ortho.plane timeAxis a.castSucc
    let V := Signed.reflect timeAxis
    V * Ortho.oneParameter U t = Ortho.oneParameter U (-t) * V := by
  intro U V
  have ha : timeAxis ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last _)
  let F r := Ortho.oneParameter U r
  apply Ortho.ext; intro x; ext1 b
  rw [Ortho.move_mul, Ortho.move_mul]
  have hl (y : E4) (r : ℝ) : (F r).move y timeAxis = Real.cos r * y timeAxis + Real.sin r * y a.castSucc :=
    (Work.A13.plane_givens ha y r).1
  have hm (y : E4) (r : ℝ) : (F r).move y a.castSucc = Real.cos r*y a.castSucc - Real.sin r*y timeAxis := (Work.A13.plane_givens ha y r).2.1
  have hk (y : E4) (r : ℝ) : ∀ b, b≠timeAxis → b≠a.castSucc → (F r).move y b=y b := (Work.A13.plane_givens ha y r).2.2
  change Ortho.move (Signed.reflect timeAxis) ((F t).move _) b=(F (-t)).move _ b
  by_cases he : b=timeAxis
  · subst b; simp only [time_reversal, if_true,hl]; unfold V; rw [time_reversal,time_reversal]; simp [ha.symm]; ring
  rw [time_reversal,if_neg he]
  unfold V
  by_cases hw : b=a.castSucc
  · subst b; rw [hm,hm,time_reversal,time_reversal]; simp [ha.symm]
  rw [hk _ t b he hw,hk _ _ b he hw]; simp [he]

lemma commuted (s : Ortho) (h : Lorentz.spatialTurn s) :
    Signed.reflect timeAxis * s = s * Signed.reflect timeAxis := by
  apply Ortho.ext; intro x
  have hf (x) : Ortho.move (Signed.reflect timeAxis) x = x - (2*time x) • basis timeAxis := by
    ext a; rw [time_reversal x]
    by_cases ht : a=timeAxis
    · subst a; simp [time]; ring
    simp [ht]
  rw [Ortho.move_mul,Ortho.move_mul,hf,h.2,hf]
  symm; change s.motion _ = _
  rw [map_sub,map_smul, Ortho.motion_at, Ortho.motion_at,spatial_axis s h]

variable {G : Gauge} (F : Labels.Frames G) (d : ℕ)

lemma hop_spatial (U : Ortho) (h : Lorentz.spatialTurn U) (p : (Model F).Field d) :
    hop F d (Lorentz.room U h) p=(gear F).act d U p := by rw [hop_eval,photos U h, lit]

lemma hop_boost (p : (Model F).Field d) (i : SpaceAxis) : HasDerivAt
    (fun t => hop F d ((Ray.fromAxis i).boost t) p) ((-I) • (gear F).lie d (Ortho.plane timeAxis i.castSucc) p) (0:ℝ) := by
  let X t := hop F d ((Ray.fromAxis i).boost t) p
  let u := Ortho.plane timeAxis i.castSucc
  let B := Module.finBasis ℂ ((Model F).Field d)
  let H := (gear F).lie d u p
  have ht (v : Module.Dual ℂ ((Model F).Field d)) :
      HasDerivAt (fun t : ℝ => v (X t)) (v ((-I) • H)) (0:ℝ) := by
    let f (z : ℂ) := v (tracks F d (stroll i z) p)
    have he (t : ℝ) : f t=v ((gear F).act d (Ortho.oneParameter u t) p) := by
      unfold f u; rw [← writes_axes,lit]
    have hp : ContDiff ℂ ω f := v.toContinuousLinearMap.contDiff.comp ((lampCurve F p).comp (stroll_diff i))
    have hw : HasDerivAt f (v H) 0 := by
      let t := fderiv ℂ f 0
      have ht := (hp.differentiable (by simp) (0:ℂ)).hasDerivAt
      refine ht.congr_deriv ?_
      have hh : HasDerivAt (fun y : ℝ => f ↑y) (deriv f 0) 0 := (by
        apply HasDerivAt.comp_ofReal
        simpa only [Complex.ofReal_zero] using ht)
      simp_rw [he] at hh
      exact hh.unique (actual_generator F d v p _)
    have hs : HasDerivAt (fun z : ℂ => f (z*(-I))) ((-I) • v H) ((0:ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      have hh : HasDerivAt f (v H) ((0:ℂ)*(-I)) := by simpa
      refine (hh.comp (𝕜:=ℂ) 0 ((hasDerivAt_id' (0:ℂ)).mul_const (-I))).congr_deriv ?_
      simp [mul_comm]
    have hx := hs.comp_ofReal
    simp only [X,hop_eval,night,map_smul]; exact hx
  change HasDerivAt X ((-I) • H) 0
  rw [show X=(fun t => ∑ j, B.coord j (X t) • B j) from funext fun t => (B.sum_repr (X t)).symm,
    show ((-I) • H)=∑ j, B.coord j ((-I) • H) • B j from (B.sum_repr _).symm]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (ht _).smul_const (B i)

section Adjoint
abbrev sideStar := (Model F).adj (hierarchy F).spin d timeAxis

lemma twist (s t : Ortho) (hx : Signed.reflect timeAxis * s=t * Signed.reflect timeAxis) (p : (Model F).Field d) :
    sideStar F d ((gear F).act d s p) = (gear F).act d t (sideStar F d p) := by
  have H := gear_laws F
  have hp := H.signed d (Signed.mirror timeAxis)
  unfold sideStar Table.adj; rw [LinearMap.comp_apply,LinearMap.comp_apply,H.real,← hp,← hp]
  change (gear F).act d (Signed.reflect timeAxis) _ = (gear F).act d t ((gear F).act d (Signed.reflect timeAxis) _)
  rw [← H.group, ← H.group, hx]

lemma conj_boost (p : (Model F).Field d) (i : SpaceAxis) (t : ℝ) :
    sideStar F d (hop F d ((Ray.fromAxis i).boost t) p) = hop F d ((Ray.fromAxis i).boost t) (sideStar F d p) := by
  simp only [hop_eval,night]
  let B := Module.finBasis ℂ ((Model F).Field d)
  apply B.equivFun.injective
  funext j
  let L := B.coord j
  let J := sideStar F d
  let K : Module.Dual ℂ ((Model F).Field d) :=
    { toFun p := star (L (J p)), map_add' p q := by rw [map_add,map_add,star_add]
      map_smul' c p := by rw [map_smulₛₗ,map_smul]; simp }
  let f (z : ℂ) := tracks F d (stroll i z) p
  let g (z : ℂ) := tracks F d (stroll i z) (J p)
  let k := K ∘ f
  let u (z : ℂ) := star (k (-star z))
  have hk : Differentiable ℂ k := K.toContinuousLinearMap.differentiable.comp (f := f) (((lampCurve F p).comp (stroll_diff i)).differentiable
    (by simp))
  have hu : Differentiable ℂ u := by
    let r := fun z => k (-z)
    have h : Differentiable ℂ r := hk.comp differentiable_id.neg
    intro x; exact differentiableAt_conj_conj_iff.mpr (h _)
  have hp : u = L ∘ g := by
    refine from_real_parameter (fun z _ => hu.analyticAt _) (fun z _ => (L.toContinuousLinearMap.contDiff.comp (show ContDiff ℂ ω g from (lampCurve F (J p)).comp (stroll_diff i))).contDiffAt.analyticAt) ?_
    intro t
    unfold u k f g
    change star (star (L (J (tracks F d (stroll i (- star (t:ℂ))) p))))= L (tracks F d (stroll i (t:ℂ)) (J p))
    rw [star_star, show -star (t:ℂ)=↑(-t) by simp, ← writes_axes,lit,← writes_axes,lit]
    rw [twist _ _ _ _ (by
      have h := negates_angle i (-t); simpa using h)]
  have he := congr_fun hp ((↑t:ℂ) * (-I));
  change star (star (L (J (f _))))=L (g _) at he
  rw [star_star,show (-(star ((↑t:ℂ)*(-I))))=_ from ?_] at he
  · exact he
  · simp [mul_comm]

lemma star_in (p : (Model F).Field d) (L : Lorentz) : sideStar F d (hop F d L p) = hop F d L (sideStar F d p) := by
  have hm (g k : Lorentz) x : hop F d (g*k) x=hop F d g (hop F d k x) := drives_mul ..
  have he : L∈Bid.beamGens := by rw [show Bid.beamGens=⊤ from Work.A16.answer]; exact Subgroup.mem_top L
  induction he using Subgroup.closure_induction generalizing p with
  | mem g hg =>
    rcases hg with ⟨s,hs,rfl⟩|⟨i,t,rfl⟩
    · rw [hop_spatial F d _ _, hop_spatial F d _ _]; exact twist F d _ _ (commuted s hs) p
    exact conj_boost F d p i t
  | one => change sideStar F d (routine F d 1 p) = routine F d 1 (sideStar F d p)
           simp
  | mul g k hg hk hp hq => rw [hm,hp,hq,hm]
  | inv g hg H =>
    apply (hop F d g).injective
    rw [← H,← hm,← hm,mul_inv_cancel]; simp [hop_eval,stencil_one,lit,(gear_port F).fixes]
end Adjoint

section Union
private theorem bands (g : Lorentz) :
    ∃ f : Module.End ℂ ((Model F).Union), ∀ n p, f ((Model F).pin n p) =
      (Model F).pin n (hop F n g p) := ((scheme F).uniqueLift (table_sym F) (scheme_filters F)
    (fun n => ((Model F).pin n).comp (hop F n g).toLinearMap)
    (by
      intro d e h p; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
      rw [← hop_coherent F h g,(scheme F).stays (table_sym F) (scheme_filters F)])).exists

def rails (g : Lorentz) := (bands F g).choose
@[simp] theorem onRails (g : Lorentz) d p : rails F g ((Model F).pin d p)=(Model F).pin d (hop F d g p) :=
  (bands F g).choose_spec d p

lemma trip (g k : Lorentz) v : rails F (g*k) v=rails F g (rails F k v) := by
  obtain ⟨d,p,rfl⟩ := (scheme F).covered (table_sym F) (scheme_filters F) v
  simp only [onRails]; rw [show hop _ _ (g*k) p=_ from (show _=hop _ _ g (hop _ _ k p) from drives_mul ..)]
lemma home (v) : rails F 1 v=v := by
  obtain ⟨d,p,rfl⟩ := (scheme F).covered (table_sym F) (scheme_filters F) v
  rw [onRails,show hop _ _ 1 p=p from drives_one ..]

def voyage : Boundary.Spins (Model F) where
  shell := hop F
  rail g := LinearEquiv.ofLinear (rails F g) (rails F g⁻¹)
    (by apply LinearMap.ext; intro v; rw [LinearMap.comp_apply,← trip,mul_inv_cancel]; exact home ..)
    (by apply LinearMap.ext; intro v; rw [LinearMap.comp_apply,← trip,inv_mul_cancel]; exact home ..)

theorem launched : (voyage F).Descends (gear F) (hierarchy F).spin :=
  ⟨onRails F,home F,trip F,hop_cont F,fun n i p => hop_boost F n p i,
    fun U h d p => hop_spatial F d U h p,fun g d p => star_in F d p g⟩
end Union
end YM.Maxwell.Free
