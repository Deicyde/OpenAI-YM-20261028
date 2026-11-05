import YM.SectorNext.LARGE_FIELD_REMAINDERS.Leases
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Minimize



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Retain the fluctuation scale without surrendering the cut V factor

Independent of k, but here each A has its own center so we don't assert a
rent sum over A with those centers. This is still at fixed V and with all
hypotheses of the intact Allocation. No deduction from Gaussian stationarity
of any contour continued measure. All probes carry their valuations after real
sector splitting, with another explicit halo cost. Unlike the `Mode.clipped`
estimate in Lease, pays the actual link $g$ scale though still with $D_L^vol$.
Crucial limitation: not a uniform bound *relative to* the precise blocked
Gaussian density; but including the kernel prefactor it is more than enough for
volume-uniform pre-change bounds up to the necessary explicit R scalar. Keep this
distinction in all downstream uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Center
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

private lemma inactive (L : Side) (κ H : ℝ) (n : ℕ) (hk : 0<κ) (hH : 0≤H) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f), S.patch.L=L → ∀ (A : Stores S) (F : Forest S.ratio) (β : ℝ),
      y G L x/2 ≤ β →
      Real.exp (coin G L H n x * A.shares) * ((g G L x)⁻¹ ^ dim G)^(frozen A (2*radiusB x) F).card ≤
        Real.exp (seed G L x κ β A.shares / 2) := by
  let D := (dim G:ℝ)
  let a : ℝ := (L.val:ℝ)^4*Fintype.card Axis*4*17^4
  have ha : 0 ≤ a := by unfold a; positivity
  let f x := 1+Real.log (y G L x)
  have hh : Tendsto (fun x => (coin G L H n x +(a*(b x)^4)*D*f x)/(p G L x)^ (2:ℕ)) atTop (𝓝 0) := by
    have ht := ((inactive_price G L n (a:=2) (by norm_num)).const_mul H).add
      ((inactive_price G L 4 (a:=2) (by norm_num)).const_mul (a*D))
    simp only [mul_zero,add_zero,Real.rpow_two] at ht
    exact ht.congr fun x => by dsimp only [Function.comp_apply,coin,f,a,D]; ring
  filter_upwards [(year G L).eventually_gt_atTop 1, hh.eventually (ge_mem_nhds (show 0<κ/4 by positivity))] with x he hx
  intro c f' S hl A F β hβ
  have hf : 0≤f x := by unfold f; have := Real.log_nonneg he.le; positivity
  let m := (frozen A (2*radiusB x) F).card
  have hcount : (m:ℝ) ≤ a*(b x)^4 * A.shares := by
    have hi := frozen_card A (2*radiusB x) F; rw [hl] at hi
    apply le_trans (Nat.cast_le (α:=ℝ).mpr hi)
    push_cast; unfold a
    have hh : 8*(2*(radiusB x:ℝ))+1 ≤ 17*b x := by unfold b; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
    rw [mul_assoc ((L.val:ℝ)^4*(Fintype.card Axis:ℝ)*4) (17^4),← mul_pow 17]; gcongr
  let p := p G L x
  have hc := (div_le_iff₀ (show 0 < p^ (2:ℕ) by unfold p; have := Scales.pos G L x; positivity)).mp hx
  have hg : (g G L x)⁻¹ ≤ Real.exp (f x) := by
    unfold g Next.Scheduling.Clock.gap; rw [inv_inv]; unfold f; rw [Real.exp_add,Real.exp_log (by linarith)]
    have hi := Real.one_le_exp (show (0:ℝ)≤1 by norm_num)
    have hr := Real.sqrt_pos.mpr (show 0<y G L x by linarith)
    have hw := Real.sq_sqrt (show 0≤y G L x by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hi (show 0≤y G L x by linarith)]
  have hw := earned G L (zero_lt_one.trans he) hk.le (m:=A.shares) hβ
  have hsize : 0 < g G L x := (g01 G L he).1
  have hD : 0≤D := by unfold D; positivity
  calc
    _ ≤ Real.exp (coin G L H n x * A.shares) * ((Real.exp (f x)) ^ dim G)^m := by gcongr
    _ = Real.exp (coin G L H n x * A.shares+(m:ℝ)*(D*f x)) := by
      rw [Real.exp_add (coin G L H n x * A.shares),Real.exp_nat_mul,show Real.exp (D*f x) = _ from Real.exp_nat_mul (f x) (dim G)]
    _ ≤ _ := by
      apply Real.exp_monotone
      change κ/2*p^2* (A.shares:ℝ) ≤ _ at hw
      have he' := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α:=ℝ) A.shares)
      have hx' := mul_le_mul_of_nonneg_right hcount (mul_nonneg hD hf)
      linarith only [he',hx',hw]

variable {T : Tube G S} {x W : ℝ} (d : Allocation G S x W) (F : Forest S.ratio)
  (V : Config G c) (A : Stores S)

def shine (i : F.Slice G) (γ g : ℝ) (k : S.Choices) : ℝ :=
  ∫ a : F.Slice G, d.bill A k (F.drape a) V * (S.likelihood (F.drape a) k *
    Mode.shielded.lamp (fun t => i t) 1 (γ/2) g a) ∂F.order G
lemma shine_int (i : F.Slice G) (γ g : ℝ) (k : S.Choices) (hb : S.patch.Branches S.kernel G) :
    Integrable (fun a => d.bill A k (F.drape a) V * (S.likelihood (F.drape a) k *
      Mode.shielded.lamp (fun t => i t) 1 (γ/2) g a)) (F.order G) := by
  exact ((d.envelope hb (V:=fun _ => V) F.continuous_drape.measurable measurable_const A k).mul
    ((env_likelihood k hb F.continuous_drape.measurable).mul (Mode.shielded.lamp_env _ ..))).integrable _



lemma shines_sum (G : Gauge) (γ : ℝ) (hγ : 0 < γ) : ∃ D : ℝ, 1 ≤ D ∧
    ∀ {c f : Side} (S : StepData c f) (x W : ℝ) (d : Allocation G S x W)
    (F : Forest S.ratio) (V : Config G c), S.patch.Branches S.kernel G → ∀ (A : Stores S) (i : F.Slice G) (s : ℝ), 0<s →
    ∑ k, shine d F V A i γ s k ≤ (D*s^dim G)^nt F := by
  obtain ⟨D,hD,h⟩ := Mode.lamp_price (G:=G) .shielded 1 (γ/2) zero_lt_one (half_pos hγ)
  refine ⟨D,hD,fun {c f} S x W d F V hB A i s hs => ?_⟩
  apply le_trans ?_ (h F.Free (fun t => i t) s hs)
  let L a := Mode.shielded.lamp (fun t => i t) 1 (γ/2) s a
  have hL := Mode.shielded.lamp_env (fun t => i t) 1 (γ/2) s
  unfold shine; rw [← integral_finsetSum _ (fun k _ => shine_int d F V A _ _ _ k hB)]
  refine integral_mono (integrable_finsetSum _ fun k _ => shine_int d F V A _ _ _ k hB)
    (μ:=F.order G) (hL.integrable _) fun a => ?_
  have hp : 0≤L a := Mode.shielded.lamp_nonneg (fun t => i t) _ _ _ hs.le _
  change _ ≤ L a; rw [← one_mul (L a), ← S.chosen hB (F.drape a), Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => mul_le_of_le_one_left (by have := S.likelihood_pos (F.drape a) k; exact mul_nonneg this hp) (d.range ..)

private lemma restored (o : Bool) {k : S.Choices} (a ξ : F.Slice G) {β L γ : ℝ}
    (hy : 1<y G S.patch.L x) (hβ : y G S.patch.L x/2 ≤ β) (hγ : 0<γ)
    (h : γ*pairCost A x (F.drape a) (F.drape ξ)-L*(nf c:ℝ) ≤ rest o T A x (F.drape a) k V) :
    let g := g G S.patch.L x
    Real.exp (-β*(rest o T A x (F.drape a) k V)) ≤
      Real.exp (β*L*(nf c:ℝ)) * (g⁻¹ ^ dim G)^(frozen A (2*radiusB x) F).card *
        Mode.shielded.lamp (fun t => ξ t) 1 (γ/2) g a := by
  intro g
  have hg : 0<g := (g01 G S.patch.L hy).1
  let Y := y G S.patch.L x
  have hY : 0<Y := zero_lt_one.trans hy
  have hb : 0≤β := by linarith only [hy,hβ]
  let Z := regular A (2*radiusB x) F
  let v := fun i => G.chord (a i*(ξ i)⁻¹)
  refine le_trans (b:=Real.exp (β*L*(nf c:ℝ)) * ∏ i∈Z, candle (γ/2) g (v i)) ?_ ?_
  · unfold candle; rw [← Real.exp_sum, ← Real.exp_add]; apply Real.exp_monotone
    have hdiv u : -(γ/2)*(u/g)^2=-(Y/2)*γ*u^2 := by
      have h := Scales.yg2 G S.patch.L hY
      rw [div_pow]; apply mul_right_cancel₀ (b:=g^2) (pow_ne_zero _ hg.ne')
      change _ * g^2 = -(Y/2)*γ*u^2*g^2
      calc
        _ = -(γ/2)*u^2 := by field_simp
        _ = -(γ/2)*u^2*(Y*g^2) := by rw [show Y*g^2=1 from h,mul_one]
        _ = _ := by ring
    simp_rw [hdiv, ← Finset.mul_sum]
    let P := pairCost A x (F.drape a) (F.drape ξ)
    have hp : 0≤P := pairCost_nn ..
    have hm := drape_pair A x F a ξ
    change ∑ i∈Z,v i ^2 ≤ P at hm
    nlinarith only [mul_le_mul_of_nonneg_left hm (show 0≤Y/2*γ by positivity),
      mul_le_mul_of_nonneg_left h hb,mul_le_mul_of_nonneg_right hβ (show 0≤γ*P by positivity)]
  have hl := Mode.shielded.floor_cost (fun t => ξ t) 1 (γ/2) g hg a Z
  rw [← Finset.card_compl Z] at hl
  rw [mul_assoc (Real.exp (β*L*(nf c:ℝ)))]; exact mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g' : S.Choices → F.Slice G → E)
private lemma centered (o : Bool) (ξ : F.Slice G) {β L γ D : ℝ} (hT : S.patch.Branches S.kernel G)
    {P : Teller G} (he : P.Funds S T) (hi : ∀ i, Integrable (g' i) (F.order G)) (hD : 0≤D)
    (hy : 1<y G S.patch.L x) (hβ : y G S.patch.L x/2 ≤ β) (hγ : 0<γ)
    (h : ∀ k, ∀ᵐ a ∂F.order G, d.bill A k (F.drape a) V ≠0 → Alive S (F.drape a) k → ‖g' k a‖ ≤ D)
    (H : ∀ a k, d.bill A k (F.drape a) V ≠0 → Alive S (F.drape a) k →
      γ*pairCost A x (F.drape a) (F.drape ξ)-L*(nf c:ℝ) ≤ rest o T A x (F.drape a) k V) :
    let g := g G S.patch.L x
    let u k a := d.bill A k (F.drape a) V * kernel .clipped o T A x β (F.drape a) k V
    let E := Real.exp (β*L*(nf c:ℝ)) * (g⁻¹ ^ dim G)^(frozen A (2*radiusB x) F).card
    ∀ k, Integrable (fun a => u k a • g' k a) (F.order G) ∧
      ∫ a, ‖u k a • g' k a‖ ∂F.order G ≤ E * D * shine d F V A ξ γ g k := by
  intro g u e k
  have hl : Measurable (F.drape (G:=G)) := F.continuous_drape.measurable
  have hu : Envelope (u k) := (d.envelope hT hl measurable_const A k).mul (by
    cases o
    · simpa only [clip_single] using env_outgoing he β x k hl (V:=fun _ => V) measurable_const A
    simpa only [clip_mean] using env_leaves he A β x k hl (V:=fun _ => V) measurable_const)
  obtain hf := Env.smul_L1 hu (hi _)
  refine ⟨hf,?_⟩
  rw [shine,← integral_const_mul]
  apply integral_mono_ae hf.norm ((shine_int d F V A _ _ _ k hT).const_mul _)
  filter_upwards [h k] with a h
  let U := F.drape a
  let K := d.bill A k U V
  let M := S.likelihood U k
  have hv : 0≤K*M := mul_nonneg (d.nonneg ..) (S.likelihood_pos ..)
  unfold u
  rw [norm_smul,norm_mul,Real.norm_of_nonneg (d.nonneg ..),Real.norm_of_nonneg (kernel_nonnegative ..)]
  unfold kernel Mode.cleared; rw [add_zero]
  change K*(M*Real.exp _) * ‖g' k a‖ ≤ e*D*(K*(M*_))
  by_cases hd : K=0
  · rw [hd]; simp
  by_cases hm : Alive S U k
  swap
  · rw [show M=0 from dead hm]; simp
  have hp : Real.exp (-β*rest o T A x U k V) ≤ e * Mode.shielded.lamp (fun t => ξ t) 1 (γ/2) g a := restored F V A o a ξ hy hβ hγ (H a k hd hm)
  have hw := mul_le_mul_of_nonneg_left (mul_le_mul (h hd hm) hp (Real.exp_pos _).le hD) hv
  linarith only [hw]

/-- Use in either orientation-mode on actual multipliers,
with probe/geometry reserve K if paid. Does NOT multiply the sieve/shield
into this bill. Still costs constants per site if comparing at sharp normalization;
varying centers per A: don't just sum this excusing the bill because d was an Allocation!
Use with an actual summability estimate, e.g. in Hit dialect of `Invoices`. -/
theorem no_sieve (P : Teller G) (L : Side) (W : ℝ) (hw : 0<W) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (κ H : ℝ) (n : ℕ), 0<κ → 0≤H → ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
    ∀ (d : Allocation G S x W) (F : Forest S.ratio) (V : Config G c) (A : Stores S) (o : Bool)
      (β Λ : ℝ) (g : S.Choices → F.Slice G → E),
      0≤Λ → β∈Set.Icc (y G L x/2) (2*y G L x) → (∀ i, Integrable (g i) (F.order G)) →
      (∀ k, ∀ᵐ a ∂F.order G, d.bill A k (F.drape a) V≠0 → Alive S (F.drape a) k →
        ‖g k a‖ ≤ Λ * Real.exp (coin G L H n x * A.shares)) →
      earn S G x κ β A.shares * (∑ k, ∫ a, ‖d.bill A k (F.drape a) V • (kernel .clipped o T A x β (F.drape a) k V • g k a)‖ ∂F.order G) ≤
        Λ * shore S G F .shielded β x D * Real.exp (-seed G L x κ β A.shares / 2) := by
  obtain ⟨γ,l,hγ,hl,h⟩ := away P L W hw
  obtain ⟨D,hD,H⟩ := shines_sum G γ hγ
  refine ⟨D,hD,fun κ q n hk hq => ?_⟩
  have he := hl 0; rw [show (fun x => _)= (fun x => y G L x*l x) from funext fun x => by rw [pow_zero,one_mul]] at he
  have he' := he.eventually (ge_mem_nhds zero_lt_one)
  filter_upwards [he',h,inactive L κ q n hk hq,(year G L).eventually_gt_atTop 1] with x hx hL hI hz
  intro c f S T hv hB hf d F V A o β Λ g' hΛ hβ hi h'
  obtain ⟨h0,h⟩ := hL
  obtain ⟨u,hU⟩ := h c f S T hv hB hf F A V
  let α := Real.exp (coin G L q n x * A.shares)
  let B := Λ*α
  have ha : 0<α := Real.exp_pos _
  rw [← hv] at hz hβ
  obtain hh := centered d F V A g' o u (β:=β) (funds_branch hf) hf hi (mul_nonneg hΛ ha.le) hz hβ.1 hγ h' (fun i j hk hh =>
    hU _ _ (fun z h => F.on_tree i ⟨z,h⟩) (d.actual _ _ _ _ hk) hh o)
  let s := g G S.patch.L x
  have hs := (g01 G S.patch.L hz).1
  have hS := H S _ _ d F V (funds_branch hf) A u s hs
  simp_rw [smul_smul]
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i (_:i∈Finset.univ) => (hh i).2) (earn_pos ..).le).trans
  let b := (s⁻¹ ^ dim G)^(frozen A (2*radiusB x) F).card
  have hb : 0≤b := by unfold b; positivity
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS
    (show 0 ≤ Real.exp (β*l x * (nf c:ℝ))*b * B by unfold B; positivity)) (earn_pos ..).le).trans
  rw [← hv] at hI hx
  have hh : α*b ≤ Real.exp (seed G L x κ β A.shares / 2) := by
    rw [← hv]; unfold α; rw [← hv]; exact hI S rfl A F β hβ.1
  have ht : Real.exp (β*l x * (nf c:ℝ)) ≤ Real.exp (2*(nf f:ℝ)) := by
    have hh : β*l x ≤ 2 := by nlinarith only [hx,mul_le_mul_of_nonneg_right hβ.2 h0]
    have hf' : (nf c:ℝ) ≤ nf f := by exact_mod_cast nf_le S
    apply Real.exp_monotone; linarith [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) (nf c))]
  let e := seed G L x κ β A.shares
  have hu : earn S G x κ β A.shares = prefactor S G β * Real.exp (-e) := by unfold earn e seed; rw [hv]; ring_nf
  have he : 0 ≤ prefactor S G β := (prefactor_pos _).le
  let t := (D*s^dim G)^nt F
  have hD' : 0 < D := by linarith
  have hT : 0≤t := by unfold t; positivity
  rw [hu]
  unfold shore; change prefactor S G β*Real.exp (-e) * (Real.exp _ * b * B * t) ≤ Λ*(prefactor S G β*Real.exp _*t)*Real.exp (-e/2)
  have hv := mul_le_mul hh ht (Real.exp_pos _).le (Real.exp_pos _).le
  change _*Real.exp (β*l x * (nf c:ℝ)) ≤ Real.exp (e/2)*Real.exp _ at hv
  have hx := mul_le_mul_of_nonneg_left hv (show 0 ≤ prefactor S G β*Λ*t*Real.exp (-e) by positivity)
  rw [show -e/2=-e+e/2 by ring,Real.exp_add (-e)]
  unfold B; unfold nf at *; linarith only [hx]
end YM.SectorNext.Remainder.Center
