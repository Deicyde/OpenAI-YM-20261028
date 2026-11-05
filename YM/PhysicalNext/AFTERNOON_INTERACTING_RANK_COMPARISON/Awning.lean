import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Images
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds

/-!
# Central guard event on *this* extended mask

Using the actual joint Gaussian, not one in a different pose or with
independent colors. Test size set at Rank threshold (so it subsequently
permits genuine curvature reads), but live windows will be on the retimed
auxiliary allocation. `shade_auth`: post-L, accounts even for dimension
growth, small complement across the extended mask. Includes temperature
changes between hats; keep β costs explicit too. No bound implies
matching densities there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     Next.Rank Tapes Perch Paint Spindle
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x u g β : ℝ} {A : Stores S} {F : Forest S.ratio}

section margins
-- extend by 8 for all four flags. Not requiring wind corridor on this W,
-- only earlier B extent does require it. Reads at cost even in halo.
def parasol (i : Site f) (W : ℕ) := Room i (W+8)

lemma Room_advances {i : Site f} {L L' : ℕ} (h : L ≤ L') : Room i L ⊆ Room i L' := by
  intro j he; have hv:=(mem_filter.mp he).2
  exact mem_filter.mpr ⟨mem_univ _,(Spindle.doors _).2 (((Spindle.doors _).1 hv.1).trans h), (Spindle.doors _).2 (((Spindle.doors _).1 hv.2).trans h)⟩
lemma shade_heel {i : Site f} {W : ℕ} : Covers (Spindle.patch W i) (parasol i W) := by
  let z : Finset (Bond f) := parasol i W
  have hb (j : Bond f) (hh : separation i j.1+1 ≤ W+8) : j∈z := by
    have hu := (separation_triangle i j.1 (j.1+Lattice.step j.2)).trans (Nat.add_le_add_left (Work.E01.sep_step_le ..) _)
    exact mem_filter.mpr ⟨mem_univ _, (Spindle.doors _).mpr (by omega),(Spindle.doors _).2 (hu.trans hh)⟩
  refine ⟨fun j hj=>hb _ (by have ht := (Spindle.doors _).mp hj; omega),?_⟩
  rintro p ⟨a,ha,he⟩ b hb'
  have hf : separation a p.1 ≤ 2 := (separation_comm ..).trans_le (Work.E01.sep_touched p a he)
  have hv : separation i p.1 ≤ W+2 := (separation_triangle _ a _).trans (add_le_add ((Spindle.doors _).1 ha) hf)
  refine hb b ?_
  have hx (k : Axis) : separation i (p.1+step k) ≤ W+2+1 := (separation_triangle _ p.1 _).trans (Nat.add_le_add hv (Work.E01.sep_step_le ..))
  simp only [bones,mem_insert,mem_singleton] at hb'; rcases hb' with hb'|hb'|hb'|hb' <;> subst b
  · exact le_trans (Nat.add_le_add_right hv 1) (by omega)
  · exact le_trans (Nat.add_le_add_right (hx _) 1) (by omega)
  · exact le_trans (Nat.add_le_add_right (hx _) 1) (by omega)
  exact le_trans (Nat.add_le_add_right hv 1) (by omega)

def parasolPrice (W : ℕ) (G : Gauge) := ((W+8 + (W+8)+1)^4*4)*Fintype.card G.ColorIndex
lemma parasol_p (i : Site f) W : Fintype.card (SlotsW A F x (parasol i W) G) ≤ parasolPrice W G := by
  let u : Window A F x (parasol i W) → ↥(parasol i W) := fun y=>⟨y.1.val.val,y.2⟩
  have he := Fintype.card_le_of_injective u (fun a b h=> Subtype.ext (Subtype.ext (Subtype.ext (congr_arg (Subtype.val : (↥(parasol i W)) → Bond f) h))))
  rw [Fintype.card_coe] at he
  unfold SlotsW; rw [Fintype.card_prod]; exact Nat.mul_le_mul_right _ (he.trans (Spindle.broad i _))
end margins

-- luminosity threshold uses Rank tolerance, not `fiery`.
def haze (G : Gauge) (x β : ℝ) (L : Side) := coolFraction*(phase (betaF G x L) / coupling β)
lemma haze_pos (hx : 0<x) (hb : 0<β) : ∀ L, 0<haze G x β L := fun L=> mul_pos coolFraction_pos (div_pos (alpha_phase _ (add_pos_of_pos_of_nonneg hx (Work.E04.shift_nonneg G L))) (coupling_pos hb))

-- height receipts; x,v in same epoch
lemma across_heat (G : Gauge) (L : Side) : ∀ᶠ x in atTop,
    phase x ≤ 2*phase (betaF G x L) ∧
    Vac.Numbers.Hat x ≤ 2* Vac.Numbers.Hat (betaF G x L) := by
  let d := G.slopeConstant*Real.log L.val; have hd : 0≤d:=Work.E04.shift_nonneg G L
  filter_upwards [eventually_ge_atTop d,eventually_ge_atTop (Real.exp 1)] with x he hx
  let y := betaF G x L; have h : x≤y := le_add_of_nonneg_right hd
  have h1:= (Real.exp_pos _).trans_le hx; have h2:= h1.trans_le h
  have h3 : Vac.Numbers.Hat x ≤ 2* Vac.Numbers.Hat y := by
    have hg : Real.sqrt y ≤ 2 * Real.sqrt x := by
      have h0 : y≤2*x := by change x+d ≤ _; linarith only [he]
      nlinarith only [Real.sq_sqrt h1.le,Real.sq_sqrt h2.le, h0,Real.sqrt_pos.mpr h1,Real.sqrt_pos.mpr h2]
    unfold Vac.Numbers.Hat; rw [← one_div,le_mul_inv_iff₀ (Real.sqrt_pos.mpr h2),one_div_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr h1)]
    exact hg
  have hy : (0:ℝ) ≤ Vac.Numbers.Hat y := by unfold Vac.Numbers.Hat; positivity
  exact ⟨(mul_le_mul h3 (hot_mono hx h) (Real.exp_pos _).le (by positivity)).trans_eq (mul_assoc ..),h3⟩

lemma tent_crowd (w : ℕ) (G : Gauge) : ∃ D : ℝ, 0≤D ∧ ∀ᶠ y : ℝ in atTop,
    (parasolPrice (w*walls y) G : ℝ) ≤ D*(Real.log y)^16 := by
  let W:=4*(w:ℝ)+8; let K:=(Fintype.card G.ColorIndex:ℝ); let V:= (W+W+1)^4*4*K
  refine ⟨V,by unfold V K; positivity,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with y hy
  let t:= Real.log y
  have hs : (M y:ℝ) ≤ 2*t^2 := by have hr : (M y:ℝ)<t^2+1:=Nat.ceil_lt_add_one (sq_nonneg _); linarith only [hr,one_le_pow₀ hy (n:=2)]
  have ht : 1≤t:=hy
  have he : (walls y:ℝ) ≤ 4*t^4 := by
    unfold walls; push_cast; exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2).trans_eq (by ring)
  unfold parasolPrice; push_cast
  have hv : w*(walls y:ℝ)+8 ≤ W*t^4 := by
    unfold W; linarith only [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg w),one_le_pow₀ ht (n:=4)]
  change _ ≤ V*t^16
  calc
    _ ≤ ((W+W+1)*t^4)^4*4*K := by unfold K; gcongr; linarith only [hv,one_le_pow₀ ht (n:=4)]
    _ = _ := by unfold V; ring

lemma hotspot (n : ℕ) (D : ℝ) (p : ℝ) (hp : 0<p) : ∀ᶠ y in atTop, D*(Real.log y)^n ≤ p^2*(hot y)^2 := by
  filter_upwards [y_rate.eventually_gt_atTop 0,(Real.tendsto_sqrt_atTop.comp y_rate).eventually_ge_atTop (n:ℝ),
    surge.eventually_ge_atTop (D/p^2),Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx hu hv he
  let t:=Perch.y x
  have hh : (n:ℝ)*t ≤ t^((3:ℝ)/2) := by
    rw [show (3:ℝ)/2=1+1/(2:ℝ) by ring, Real.rpow_add hx,Real.rpow_one,← Real.sqrt_eq_rpow]
    rw [mul_comm t]; exact mul_le_mul_of_nonneg_right hu hx.le
  have ht : Real.log x^n ≤ hot x := by
    rw [show Real.log x=Real.exp t from (Real.exp_log he).symm,← Real.exp_nat_mul]; exact Real.exp_monotone hh
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos hp 2)).mp hv) (pow_nonneg he.le n)
  exact h.trans ((mul_le_mul_of_nonneg_left ht (by unfold hot; positivity : 0 ≤ hot x*p^2)).trans_eq (by ring))

structure ShadePay (w : ℕ) (U : ℝ) (G : Gauge) (L : Side) (p : ℝ) (x β : ℝ) : Prop where
  fund : Real.exp 2 * Real.exp (-reservation (parasolPrice (w*walls (betaF G x L)) G) U * (haze G x β L/2)^2) ≤ x^(-p)
lemma buys_shade (w : ℕ) (G : Gauge) (L : Side) (U : ℝ) (hu : 0≤U) (p : ℝ) (hp : 0≤p) :
    ∀ᶠ x in atTop,∀ β : ℝ,x/2 ≤ β → β ≤ 3*x → ShadePay w U G L p x β := by
  let δ:=coolFraction/8; have hε : 0<δ:=div_pos coolFraction_pos (by norm_num)
  obtain ⟨D,hD,h⟩:=tent_crowd w G
  let A:=8*(1+D*U); have hA : 0<A:=by unfold A; positivity
  have hb:= (Work.E01.betaF_tendsto G L)
  filter_upwards [hb.eventually h,hb.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1),
    hb.eventually (hotspot 17 ((2+p)*A) _ hε),band G L,across_heat G L,eventually_gt_atTop (1:ℝ)] with x hx he hp0 ht hf hc
  intro β hl hu'; apply ShadePay.mk
  let z:=betaF G x L; let V:= hot z; let v:=haze G x β L/2; let κ:=parasolPrice (w*walls z) G
  let r:=8*(1+κ*U); let y:= Real.log z
  obtain ⟨hβ,hg,hT,-⟩:=ht β hl hu'
  have hs : 0<x:=zero_lt_one.trans hc; have hy:=le_add_of_nonneg_right (a:=x) (Work.E04.shift_nonneg G L)
  change x ≤ z at hy
  have hq : 0<V:=Real.exp_pos _; have hδ:=mul_pos hε hq
  have hh : δ*V ≤ v := by
    let g:=coupling β; let t:=Vac.Numbers.Hat z
    have hx : g ≤4*t := hT.trans (show 2*Vac.Numbers.Hat x ≤ 4*t by linarith only [hf.2])
    have ht : V/4 ≤ phase z/g := (le_div_iff₀ hg).2 (by
      change _ ≤ t*V; linarith only [mul_le_mul_of_nonneg_right hx hq.le])
    change coolFraction/8*V ≤ coolFraction*(phase z/g)/2
    linarith only [mul_le_mul_of_nonneg_left ht coolFraction_pos.le]
  have hr : 0 < r:= by unfold r; positivity
  have hz : r ≤ A*y^16 := by
    unfold r A
    change 1≤y at he
    have hx : (κ:ℝ) ≤ D*y^16:=hx
    linarith only [mul_le_mul_of_nonneg_right hx hu,one_le_pow₀ he (n:=16)]
  have he' : 2+Real.log x*p ≤ (2+p)*y := by
    have h := Real.log_le_log hs hy
    change 1≤y at he
    linarith only [mul_le_mul_of_nonneg_right h hp,he]
  have hs' : 2 + Real.log x * p ≤ reservation κ U*v^2 := by
    rw [show reservation κ U*v^2=v^2/r from div_eq_inv_mul ..|>.symm]
    rw [le_div_iff₀ hr]
    calc
      _ ≤ ((2+p)*y)*(A*y^16) := mul_le_mul he' hz hr.le (by change 1≤y at he; positivity)
      _ = ((2+p)*A)*y^17 := by ring
      _ ≤ δ^2*V^2 := hp0
      _ ≤ _ := by rw [← mul_pow]; gcongr
  rw [← Real.exp_add,Real.rpow_def_of_pos hs]
  apply Real.exp_monotone
  change 2+ -reservation κ U*v^2 ≤ _
  linarith only [hs']

def shade (A : Stores S) (F : Forest S.ratio) (x β : ℝ) (q : Chi) (u : Site f) (W : ℕ)
    {βρ : ℝ} (Y : RoomView A βρ F G) : ℝ := PhysicalGuard7f546.Curved.veil (parasol u W) q (haze G x β S.patch.L) Y.2

lemma shade_auth (A : Stores S) (F : Forest S.ratio) (x : ℝ) (q : Chi) (u : Site f) (w) (V : Config G c) (T : Tube G S)
    (k : S.Choices) {βρ U : ℝ} {β t p : ℝ} (hx : 0<x) (he : 0<β) (hU : 1≤U) (hP : ShadePay w U G S.patch.L p x β) (ht : x^(-p) ≤ t)
    (hQ : (palette T A F k βρ V .endpoint).PosDef ∧ ∀ i j, |palette T A F k βρ V .endpoint i j| ≤ U) :
    let s:= w*walls (betaF G x S.patch.L)
    let K := viewer T A βρ F k V
    Guarded (shade A F x β q u s) t K ∧ K.real (Prod.snd ⁻¹' away (parasol u s) (haze G x β S.patch.L/2)) ≤ t := by
  intro s K
  let Z:= parasol u s; let ε:= haze G x β S.patch.L; let p:= away (A:=A) (F:=F) (x:=βρ) (G:=G) Z (ε/2)
  let Q := palette T A F k βρ V .endpoint
  have h:=haze_pos hx he (S.patch.L) (G:=G)
  have hv := (reserve_away Z (ε/2) (by positivity) hU (parasol_p u s) hQ.1.posSemidef _ rfl (fun i j=> hQ.2 _ _)).trans (hP.fund.trans ht)
  let P := paid_veil (A:=A) (F:=F) (x:=βρ) (G:=G) Z q ε h
  let W:= shade A F x β q u s (G:=G) (βρ:=βρ)
  have hκ : MeasurePreserving Prod.snd K (cloud Q) := measurePreserving_snd
  let v : Set (RoomView A βρ F G):=Prod.snd ⁻¹' p
  have ha : K.real v ≤ t := Eq.trans_le (congr_arg ENNReal.toReal (hκ.measure_preimage (away_meas Z (ε/2)).nullMeasurableSet)) hv
  have hi : MeasurableSet v:=hκ.measurable (away_meas ..)
  have hp : Measurable W:= P.borel.comp measurable_snd
  refine ⟨⟨fun i=> (P.probability i.2).1,fun i=> (P.probability i.2).2,hp, ?_⟩,ha⟩
  letI : IsProbabilityMeasure K:=by unfold K; infer_instance
  have hh i : ‖W i‖≤1 := by rw [Real.norm_of_nonneg (show 0 ≤ W i from (P.probability i.2).1)]; exact (P.probability _).2
  have he : Integrable W K := Integrable.of_bound hp.aestronglyMeasurable 1 (Eventually.of_forall hh)
  let Y := v.indicator fun _=> (1:ℝ)
  have hy i : 1-W i≤ Y i := by
    by_cases hM : i∈v
    · unfold Y; rw [Set.indicator_of_mem hM]; exact sub_le_self _ (P.probability _).1
    have hN : Guards Z (Prod.snd i) (ε/2) := not_not.mp hM
    unfold Y; rw [show W i=1 from P.plateau i.2 hN, Set.indicator_of_notMem hM,sub_self]
  refine (integral_mono ((integrable_const _).sub he) ((integrable_const _).indicator hi) hy).trans ?_
  rw [integral_indicator hi,setIntegral_const,smul_eq_mul,mul_one]; exact ha
end YM.PhysicalNext.InteractingRank
