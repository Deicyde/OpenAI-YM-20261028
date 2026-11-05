import YM.RG08.Canon.Strand
/-! # Fixed metric Hessian, two-grade centered Laplace coefficients.
 Price not global in the metric and period. Odd terms from the genuine
 modifications of the mean/Haar don't survive the normalized ratio, by real
 Gaussian integrals, not by diagram reindexing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open Function YM.PertExtension.Series.Radial YM.PertExtension.Chart RG08.Reflect Finset
open scoped BigOperators Topology Real ContDiff Classical
variable {V : Type*} [NormedAddCommGroup V][NormedSpace ℝ V]

private lemma paid0 {f : ℝ→ℝ}(h : ContDiffAt ℝ ω f 0) : Bill 0 f := life_price (h.continuousAt.mono_left nhdsWithin_le_nhds)
lemma priced0 {f : ℝ→ℝ} (hp : ContDiffAt ℝ ω f 0) : Fit 1 f (fun _=> f 0) := by
  refine Fit.join (ink_aspire (hp.of_le le_top) (0:ℕ) : Fit 1 f (peval (ink f) 0)) (Fit.supply (Eventually.of_forall fun t=> by simp [peval,ink,PertExtension.Series.Zone.eval]) _)
lemma priced1 {f : ℝ→ℝ} (hp : ContDiffAt ℝ ω f 0) (hz : f 0=0) : Bill 1 f := by
  have hv:=priced0 hp; unfold Fit at hv; rw [hz,show (fun _ : ℝ=>(0:ℝ))=0 from rfl, sub_zero] at hv; exact hv

structure Passive (F : V × ℝ→ℝ) (q : V→ℝ) : Prop where
  regular : ContDiffAt ℝ ω F 0
  partials : ∀ᶠ t in 𝓝 0, F (0,t)=t^2 ∧ ∀ x:V, jet (fun u=> F (u,t)) 1 x=0 ∧ jet (fun u=> F (u,t)) 2 x=q x
  gap : ∀ x,x≠0 → 0<q x

variable {F G A B W : V×ℝ→ℝ} {q : V→ℝ} {c : ℝ}
lemma passive_two (h : Passive F q) (x : V)(z : ℝ) : Fit 3 (fun t:ℝ=> F (t • (x,z))) (fun t=> t^2*(q x+z^2)) := by
  have hp:= strand F x z h.regular 2
  have he : Tendsto (fun t:ℝ=>t*z) (𝓝[>] 0) (𝓝 0):= by apply Tendsto.mono_left _ nhdsWithin_le_nhds; simpa using (show Continuous (fun t:ℝ=>t*z) by fun_prop).tendsto 0
  refine hp.join (Fit.supply ?_ _); filter_upwards [he.eventually h.partials] with t ⟨ht,hH⟩; simp only [year,Finset.sum_range_succ, Finset.sum_range_zero,jet_zero, pow_zero,one_smul, ht, (hH x).1,(hH x).2 ]; simp only [smul_eq_mul]; ring
lemma calm (h : Passive F q) [FiniteDimensional ℝ V] : Stationary F ∧ ∃ δ>0,∀ u:V×ℝ,δ*‖u‖^2 ≤ jet F 2 u := by
  have hf : ContDiffAt ℝ ∞ F 0 := h.regular.of_le le_top
  have hw (u:V)(z:ℝ)(j) (hj:j≤2) : jet F j (u,z)=if j=2 then q u+z^2 else 0 := aspiredV (passive_two h u z) (directions hf (u,z)) (Aspiration.single _ _) hj
  refine ⟨⟨hf,?_,?_⟩,?_⟩
  · change F (0,0)=0; simpa using h.partials.self_of_nhds.1
  · rintro ⟨x,z⟩; rw [hw _ _ _ (by decide), if_neg (by decide)]
  apply quadratic_min; rintro ⟨x,z⟩ hn; rw [hw _ _ _ le_rfl, if_pos rfl]; by_cases hh:x=0
  · subst x; have hu : q 0=0 := by rw [← (h.partials.self_of_nhds.2 0).2, ← zero_smul ℝ (0:V),jet_smul]; simp
    have hv : z≠0 := fun hp=> hn (by rw [hp]; rfl); rw [hu,zero_add]; exact sq_pos_of_ne_zero hv
  exact add_pos_of_pos_of_nonneg (h.gap _ hh) (sq_nonneg ..)

local notation "℘" => YM.PertExtension.Series.Radial.projection
-- exp factor polynomial at fixed plate. $b$ varying and odd.
def bandit (F : V×ℝ→ℝ) (x : V)(j : ℕ)(t : ℝ):= jet (fun u=> F (u,t)) j x
lemma bands_wig {j} (x : V) (h : ContDiffAt ℝ ω F 0) : ContDiffAt ℝ ω (bandit F x j) 0 := strands_fit F x h j
lemma expBill (s : ℝ) (b : ℝ→ℝ)(d : ℝ)(h : ContDiffAt ℝ ω b 0) :
   Fit 3 (fun t:ℝ=> Real.exp (-(s+t*b t+t^2*d))) (fun t=> Real.exp (-s)*(1-t*b t+t^2*((b t)^2/2-d))) := by
  let f (t:ℝ):= -(t*b t+t^2*d); let C:=Real.exp (-s)
  have hf : Bill 1 f := priced1 ((contDiffAt_id.mul h).add ((contDiffAt_id.pow 2).mul contDiffAt_const)|>.neg) (by simp [f])
  have hh : (fun t:ℝ=> Real.exp (-(s+t*b t+t^2*d)))=C • (Real.exp ∘ f) := funext (fun t=> by rw [show -(s+t*b t+t^2*d)= -s+f t by dsimp [f]; ring,Real.exp_add]; rfl)
  rw [hh]; apply ((exp_fits hf 2).scale C).join
  let A(t:ℝ):= t^3*(C*(d*b t+t*d^2/2))
  have ha : Bill 3 A := bill_mul (ruler 3 3 le_rfl) (paid0 (contDiffAt_const.mul ( (contDiffAt_const.mul h).add ((contDiffAt_id.mul contDiffAt_const).div_const _))))
  unfold Fit; apply bill_flip ha
  apply Eventually.of_forall; intro t
  dsimp only [A,Pi.smul_apply,year,f,Pi.sub_apply]; norm_num [Finset.sum_range_succ]; unfold C; ring
lemma pas_exp (h : Passive F q)(x : V) :
   let b:=bandit F x 3; let D:=bandit F x 4 0; let s:=1+q x
   Fit 3 (fun t:ℝ=> Real.exp (-F (t•(x,(1:ℝ)))/t^2)) (fun t=> Real.exp (-s)*(1-t*b t+t^2*(b t^2/2-D))) := by
  intro b D s
  let g:=bandit F x 4
  have ht: ContDiffAt ℝ ω b 0:= bands_wig x h.regular
  have hE := (strand F x 1 h.regular 4).shorten (k:=2) (n:=3)
  let v (t:ℝ) := s+t*b t+t^2*g t; let u (t:ℝ):= s+t*b t+t^2*D
  have hv : Fit 3 v u := (Fit.same _ 3).pair ((priced0 (bands_wig x (j:=4) h.regular)).right (p:=fun t:ℝ=> t^2) (ruler 2 2 le_rfl))
  have hQ : ContDiffAt ℝ ω u 0 := (contDiffAt_const.add (contDiffAt_id.mul ht)).add ((contDiffAt_id.pow _).mul contDiffAt_const)
  refine Fit.join ?_ (expBill s b D ht)
  have hp : Fit 3 (fun t:ℝ=> F (t•(x,(1:ℝ)))/t^2) v := by
    refine Fit.join hE (Fit.supply ?_ _)
    filter_upwards [h.partials.filter_mono nhdsWithin_le_nhds,eventually_pos] with t ⟨he,H⟩ hy
    unfold v year; simp only [sum_range_succ,sum_range_zero,pow_zero,one_smul,jet_zero,mul_one,he,(H x).1,(H x).2]; change _=1+q x+t*b t+t^2*g t; unfold b g bandit; simp only [smul_eq_mul]; field_simp; ring
  simpa only [neg_div,Pi.neg_apply,Function.comp_def,u, s] using! ((hp.join hv).negate.elevate (paid0 hQ.neg))
lemma pas_amp (h : ContDiffAt ℝ ω A 0)(he : ∀ᶠ t in 𝓝 0,A (0,t)=c)(x : V) :
   Fit 3 (fun t:ℝ=> A (t • (x,(1:ℝ)))) (fun t=> c+t*bandit A x 1 t+t^2*bandit A x 2 0) := by
  let v(t:ℝ):=c+t*bandit A x 1 t
  refine (strand A x 1 h 2).join (Fit.join (g:=v+(fun t:ℝ=> t^2*bandit A x 2 t)) (Fit.supply ?_ _) ((Fit.same v 3).pair ((priced0 (bands_wig x h (j:=2))).right (ruler 2 2 le_rfl))))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht; simp [v,year,ht, Finset.sum_range_succ,bandit]
end YM.RG08.Canon
