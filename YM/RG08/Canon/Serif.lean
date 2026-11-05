import YM.RG08.Canon.Shore
/-! # Integration of odd residual in either valuation
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter Set Metric MeasureTheory YM.PertExtension.Series Tested
open Function Radial YM.PertExtension.Chart RG08.Reflect Finset
open scoped BigOperators Topology Real ContDiff Classical
section calmM
variable {V : Type*} [NormedAddCommGroup V][NormedSpace ℝ V]
variable {F G A B : V×ℝ→ℝ}{q : V→ℝ}{c : ℝ}
local notation "P[" t "," x "," y "," z "]" => fun t':ℝ=> Radial.projection t x t' (y,(z:ℝ))
abbrev hymn (c : ℝ)(q:V→ℝ)(A F : V×ℝ→ℝ)(x:V)(t:ℝ) := Real.exp (-(1+q x))*((c+t*bandit A x 1 t+t^2*bandit A x 2 0) * (1-t*bandit F x 3 t+t^2*(bandit F x 3 t^2/2-bandit F x 4 0)))
lemma pas_theme [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (h : Passive F q) (hp : ContDiffAt ℝ ω A 0) (he : ∀ᶠ t in 𝓝 0,A (0,t)=c)(x : V) :
    Fit 3 P[A,F,x,1] (hymn c q A F x) := by
  rw [show (P[A,F,x,1]) = (fun t:ℝ=> A (t • (x,(1:ℝ))))*(fun t:ℝ=> Real.exp (-F (t • (x,(1:ℝ)))/t^2)) from funext fun t=> Radial.projection_eq ..]
  refine (Fit.groups (pas_amp hp he x) (pas_exp h x) (life_price ((show ContDiffAt ℝ ω (fun t:ℝ=>c+t*bandit A x 1 t+t^2*bandit A x 2 0) 0 from
         (contDiffAt_const.add (contDiffAt_id.mul (bands_wig x hp))).add ((contDiffAt_id.pow _).mul contDiffAt_const)).continuousAt.mono_left nhdsWithin_le_nhds)) ?_).join ?_
  · let D:=Real.exp (-(1+q x)); let b:=bandit F x 3; let s:= bandit F x 4 0
    exact life_price (f:=fun t:ℝ=>D*(1-t*b t+t^2*(b t^2/2-s))) ((show ContDiffAt ℝ ω (fun t:ℝ=>D*(1-t*b t+t^2*(b t^2/2-s))) 0 from contDiffAt_const.mul ((contDiffAt_const.sub (contDiffAt_id.mul (bands_wig x h.regular))).add ((contDiffAt_id.pow 2).mul (((bands_wig x h.regular).pow 2|>.div_const (2:ℝ)).sub (contDiffAt_const (c:=s)))))).continuousAt.mono_left nhdsWithin_le_nhds)
  apply Fit.supply; apply Eventually.of_forall; intro t
  unfold hymn; dsimp only [Pi.mul_apply]; ring
lemma band_sign (F : V×ℝ→ℝ)(x : V)(t : ℝ)(k) : bandit F (-x) k t=(-1:ℝ)^k*bandit F x k t := by simpa [bandit] using jet_smul (fun u:V=> F (u,t)) k (-1) x
abbrev season (W a B b k L t : ℝ) := W*(a*(b^2-2*k)+2*L-2*b*B+L*(t^2)*(b^2-2*k))
lemma pas_even [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (h : Passive F q) (hp : ContDiffAt ℝ ω A 0) (he : ∀ᶠ t in 𝓝 0,A (0,t)=c)(x : V) :
    let W:= Real.exp (-(1+q x)); let a:=bandit F x 3; let m:=bandit F x 4 0; let b:= bandit A x 1; let L:= bandit A x 2 0
    Fit 3 (P[A,F,x,1]+P[A,F,-x,1]) (fun t:ℝ=>2*c*W+t^2*season W c (b 0) (a 0) m L 0) := by
  intro W a m b L
  have hm : q (-x)=q x := by simpa [← (h.partials.self_of_nhds.2 x).2, ← (h.partials.self_of_nhds.2 (-x)).2,bandit] using band_sign F x 0 2
  let C : ℝ→ℝ := fun _=>2*c*W
  let p (t:ℝ):= season W c (b t) (a t) m L t
  have hi : (hymn c q A F x+hymn c q A F (-x))= C+(fun t:ℝ=>t^2)*p := by
    funext t; simp only [hymn,W,a,m,b,p,L,season,Pi.add_apply,Pi.mul_apply,C,band_sign,hm]; ring
  refine ((pas_theme h hp he x).pair (pas_theme h hp he (-x))).join ?_
  rw [hi]; have hB : ContDiffAt ℝ ω b 0:=bands_wig x hp; have hA:ContDiffAt ℝ ω a 0:=bands_wig x h.regular
  have ht : ContDiffAt ℝ ω p 0 := by unfold p season; fun_prop
  exact (Fit.same C _).pair ((priced0 ht).right (ruler 2 2 le_rfl))
lemma pas_agree [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (h : Passive F q)(hp : Passive G q) (hA: ContDiffAt ℝ ω A 0) (hB : ContDiffAt ℝ ω B 0)
    (he : ∀ᶠ t in 𝓝 0,A (0,t)=c)(hs : ∀ᶠ t in 𝓝 0,B (0,t)=c) (hG : (fun u:V=>F (u,0))=ᶠ[𝓝 0](fun u:V=> G (u,0))) (hT : (fun u:V=>A (u,0))=ᶠ[𝓝 0](fun u:V=> B (u,0)))(x : V) :
    Fit 3 (P[A,F,x,1]+P[A,F,-x,1]) (P[B,G,x,1]+P[B,G,-x,1]) := by
  have hb i : bandit F x i 0=bandit G x i 0 := by unfold bandit jet; rw [(hG.iteratedFDeriv ℝ _).eq_of_nhds]
  have hL i : bandit A x i 0=bandit B x i 0 := by unfold bandit jet; rw [(hT.iteratedFDeriv ℝ _).eq_of_nhds]
  have ht:= pas_even h hA he x; dsimp only at ht; simp_rw [hL,hb] at ht; exact Fit.join ht (Fit.turn (pas_even hp hB hs x))
end calmM
section live
variable (G : Gauge) (U : Type)[Fintype U]
local notation "V" => U→G.Color
local notation "Z" => (U→G.Color) × ℝ
-- moment projection on genuine plate
lemma both_moments {F Y A B : (Z)→ℝ} {n : ℕ}
    (h : ∃ δ>0,∀ u:Z,δ*‖u‖^2 ≤ jet F 2 u) (hx : ∃ δ>0,∀ u:Z,δ*‖u‖^2 ≤ jet Y 2 u)
    (hF : Radial.Stationary F) (hY : Radial.Stationary Y) (hA : ContDiffAt ℝ ω A 0)(hB : ContDiffAt ℝ ω B 0)
    (p : ∀ x:V, Fit (n+1) (fun t:ℝ=> Radial.projection A F t (plates G U x)+Radial.projection A F t (plates G U (-x))) (fun t:ℝ=> Radial.projection B Y t (plates G U x)+Radial.projection B Y t (plates G U (-x)))) (j : ℕ)(hj:j≤ n) :
    moment (hold G U) A F j=moment (hold G U) B Y j := by
  let P x:=normTerm A F j (plates G U x); let T x:=normTerm B Y j (plates G U x)
  have hv (x:V): P x+P (-x)=T x+T (-x) := aspiredV (p _) ((ink_cross hF (hA.of_le le_top) _).add (ink_cross hF (hA.of_le le_top) _)) ((ink_cross hY (hB.of_le le_top) _).add (ink_cross hY (hB.of_le le_top) _)) hj
  let μ:= tangent G U
  haveI : μ.IsNegInvariant := by unfold μ; exact Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have ht {F A : (Z)→ℝ} (hF : Radial.Stationary F) (hA : ContDiffAt ℝ ω A 0) (h : ∃ δ>0,∀ u:Z,δ*‖u‖^2≤jet F 2 u) :
      2*moment (hold G U) A F j=(∫ x:V, normTerm A F j (plates G U x)+normTerm A F j (plates G U (-x)) ∂μ) := by
    let C x:= normTerm A F j (plates G U x); have hi : Integrable C μ := (integrable_map_measure (g:=normTerm A F j) (Smooth.continuousTerms ..|>.measurable.aestronglyMeasurable) (plates_meas ..|>.aemeasurable)).1 (hF.integrableTerm (hold G U) (hA.of_le le_top) h)
    unfold moment hold; rw [integral_map ((plates_meas G U).aemeasurable) ((Smooth.continuousTerms ..).measurable.aestronglyMeasurable)]
    change 2*(∫ x,C x∂μ)=(∫ a,C a+(C ∘ Neg.neg) a∂μ)
    rw [integral_add hi (show Integrable (C ∘ Neg.neg) μ from (Measure.measurePreserving_neg μ).integrable_comp_of_integrable hi)]
    change 2*(∫ x,C x∂μ)=(∫ x,C x∂μ)+∫ x,C (-x) ∂μ
    rw [two_mul, integral_neg_eq_self]
  apply mul_left_cancel₀ (show (2:ℝ)≠0 by norm_num); rw [ht hF hA h,ht hY hB hx]; exact integral_congr_ae (Eventually.of_forall hv)
end live
end YM.RG08.Canon
