import YM.PertExtension.BareChart
import YM.PertExtension.Aspiration
import YM.PertExtension.OrbHaar

/-! Fixed positive-cutoff Laplace--diagram prescription at the inversion saddle.
Constants need not yet be uniform in a spacing limit. Two equivalent ways of
writing coefficients: finite radial Taylor polynomials times Gaussian density,
or their Gaussian moments. This file uses moments with full quadratic kernel (see
`Orb.fiscal_grades`) prior to any position subtractions or blocking. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.PertExtension.Orb
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory
open scoped ContDiff Topology Classical BigOperators ENNReal
open Chart Series.Radial Series.Tested
local notation "Rφ" => Precision.ChartRatio
variable {G : Gauge} {n : Side}

abbrev Slice (G : Gauge) (n : Side):= Cotree n → G.El
abbrev Observable (G : Gauge)(n : Side):=Slice G n→ℝ

def tray (G : Gauge) : Rφ G := (LocalH.actual G).choose
lemma traySpec (G : Gauge):LocalRatio (tray G) := (LocalH.actual G).choose_spec

structure LocalTest (O : Observable G n): Prop where
  boundedness : Continuous O
  germ : ContDiffAt ℝ ∞ (O ∘ expLinks G _) 0

def accountingWith (P : Rφ G)(O : Observable G n)(x:Dir G n) := jacobian P x * O (expLinks G _ x)
def account : Slice G n→ℝ := fun x=>Wilson.energy (links 1 x)/2
abbrev entryMeasure (G : Gauge)(n:Side):=physical G (Cotree n)
def entries (O : Observable G n)(t : ℝ)(x) := O x*Real.exp (-account x/t^2)
def numerator (O : Observable G n)(t:ℝ) := ∫ x, entries O t x ∂entryMeasure G n
def scaledNum (O : Observable G n)(t : ℝ) := (t^Module.finrank ℝ (Dir G n))⁻¹ * numerator O t
def rowsWith (P : Rφ G)(O : Observable G n) := fun k => Series.Radial.moment (tangent G (Cotree n)) (accountingWith P O) fiscal k
def rows (O : Observable G n) := rowsWith (tray G) O

-- Formal prescription as a quotient of two series after extracting the common power t^(dim Slice).
def diagonalWith (P : Rφ G)(O : Observable G n) := divide (rowsWith P O) (rowsWith P (n:=n) 1)
def diag (O : Observable G n) := diagonalWith (tray G) O

def expectation (O : Observable G n) : ℝ→ℝ := numerator O/numerator (n:=n) (G:=G) 1

lemma account_link (x : Dir G n) : account (expLinks G _ x)=fiscal x := rfl
@[fun_prop] lemma continuous_links : Continuous fun u=>links (K:=G.El) (n:=n) 1 u := by
  apply continuous_pi; intro i; dsimp only [links,liftLinks,splitLink];split<;>split<;>fun_prop
@[fun_prop] lemma continuous_account : Continuous (account (G:=G) (n:=n)) := ((energy_cont).comp continuous_links).div_const 2
lemma entries_cont {O : Observable G n}(h:Continuous O)(t : ℝ):Continuous (entries O t) := h.mul (Real.continuous_exp.comp ((continuous_account (G:=G) (n:=n)).neg.div_const _))
lemma entries_integrable {O : Observable G n}(h:Continuous O)(t : ℝ) : Integrable (entries O t) (entryMeasure G n) := (entries_cont h ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable {P : Rφ G}
local notation "W" => tangent G (Cotree n)
lemma inner (R : LocalRatio P) {O : Observable G n}(h : LocalTest O){r : ℝ}(hr : r<small G P)(hr':0<r) {t:ℝ}(ht : 0≤t):
   (t^Module.finrank ℝ (Dir G n))⁻¹ * (∫ x in chamber G (Cotree n) r,entries O t x ∂entryMeasure G n)=
     Series.Radial.partialSum W (accountingWith P O) fiscal r t := by
  have he := Chart.Ratio.chamber_integral R (entries O t) (entries_cont h.boundedness t).measurable hr hr'
  rw [he]
  let f (x : Dir G n):= jacobian P x * entries O t (expLinks G _ x)
  have hs (x : Dir G n) : Series.Radial.projection (accountingWith P O) fiscal t x= f (t • x) := by
    rw [projection_eq];unfold accountingWith f entries;change (jacobian _ (t • x)*_)*_ = jacobian _ (t • x)*_;simp only [account_link]; ring
  let A: Set (Dir G n):=ball 0 r
  let D:= Series.Radial.disc (E:=Dir G n) t r
  let g:= A.indicator f
  have hg x : g (t • x) = D.indicator (fun x=>f (t • x)) x := by
    by_cases hx : t•x∈A
    · rw [show g (t • x)=f _ from indicator_of_mem hx _, indicator_of_mem (s:=D) hx]
    rw [show g (t • x)=0 from indicator_of_notMem hx _, indicator_of_notMem (s:=D) hx]
  change _ * (∫ x in A,f x ∂W)= ∫ x in D,_ ∂W
  have hd := Measure.integral_comp_smul_of_nonneg W g t (hR:=ht)
  simp only [hg] at hd
  unfold g at hd; rw [integral_indicator (isOpen_ball (x:=(0:Dir G n))).measurableSet,smul_eq_mul] at hd
  rw [← hd]; simp_rw [hs];exact integral_indicator (Series.Radial.disc_meas (E:=Dir G n) t r)

lemma unit_mem {r:ℝ}(hr : 0<r) : (1:Slice G n)∈ chamber G (Cotree n) r := fun i hi=>⟨0,mem_ball_self hr,G.mat_lieExp_zero⟩
lemma account_positive (even : Even n.val) (R : LocalRatio P) {r:ℝ}(hr : r<small G P)(hr':0<r) :
    ∃ b>0,∀ u : Slice G n,u∈(chamber G _ r)ᶜ → b≤account u := by
  let U:=(chamber G (Cotree n) r)ᶜ
  by_cases hx : U.Nonempty
  · obtain ⟨a,ha,hq⟩:=(Chart.Ratio.chamber_open R hr.le (U:=Cotree n)|>.isClosed_compl.isCompact).exists_isMinOn hx continuous_account.continuousOn
    have hb : account a ≠ 0 := by intro h
                                  rw [show account a=energy (links 1 a)/2 from rfl,div_eq_zero_iff] at h
                                  have h := h.resolve_right (by norm_num)
                                  exact ha (flat_unique even h ▸ unit_mem hr')
    have hb' := eq_or_lt_of_le (div_nonneg (energy_nonneg (links 1 a)) (by norm_num:(0:ℝ)≤2))
    exact ⟨account a,hb'.resolve_left hb.symm,hq⟩
  exact ⟨1,one_pos,fun u hu=> (hx ⟨u,hu⟩).elim⟩

lemma outer (even : Even n.val)(R : LocalRatio P){O : Observable G n}(h : LocalTest O)
    {r : ℝ}(hr : r<small G P)(hr':0<r)(N:ℕ):∃ C,0≤C ∧ ∀ t > 0,
      ‖(t^Module.finrank ℝ (Dir G n))⁻¹*∫ x in (chamber G _ r)ᶜ, entries O t x ∂entryMeasure G n‖≤ C*t^N := by
  obtain ⟨M,hM⟩:=isCompact_univ.exists_bound_of_continuousOn h.boundedness.continuousOn
  obtain ⟨b,hb,hB⟩:=account_positive (P:=P) even R hr hr'
  let d:=Module.finrank ℝ (Dir G n)
  obtain ⟨C,hC,hD⟩:=bounded_exp hb (d+N)
  refine ⟨|M| *C,by positivity,fun t ht=>?_⟩
  have ht' : 0<t⁻¹:= inv_pos.mpr ht
  have hD:=hD (t⁻¹) ht'.le
  let μ := entryMeasure G n
  let S:=(chamber G (Cotree n) r)ᶜ
  let B := |M| *Real.exp (-b/t^2)
  let F := fun u : Slice G n=> B
  have hi : Integrable F μ:= integrable_const _
  have he : ∀ᵐ x ∂μ.restrict S, ‖entries O t x‖≤ F x := by
    filter_upwards [ae_restrict_mem (Chart.Ratio.chamber_open R (U:=Cotree n) hr.le |>.measurableSet.compl)] with x hx
    change ‖O x*Real.exp _‖≤_
    simp only [norm_mul,Real.norm_eq_abs (Real.exp ..),abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul ((hM x (mem_univ _)).trans (le_abs_self _)) (Real.exp_le_exp.mpr (by grw [hB x hx])) (Real.exp_pos _).le (abs_nonneg _)
  have ho₁ : ‖∫ x in S, entries O t x ∂μ‖ ≤ B := (norm_integral_le_of_norm_le hi.integrableOn he).trans ((setIntegral_le_integral hi (Eventually.of_forall (p:=fun x=>0 ≤ F x) ?_)).trans_eq ?_)
  · change ‖(t^d)⁻¹*_‖≤ _
    rw [norm_mul, Real.norm_eq_abs ((t^d)⁻¹),abs_of_nonneg (by positivity)]
    calc
        _ ≤ (t⁻¹)^d * (|M| *Real.exp (-b*(t⁻¹)^2)) := by rw [inv_pow,inv_pow,← div_eq_mul_inv];gcongr
        _ = |M| *((t⁻¹)^d*Real.exp (-b * t⁻¹^2)):=by ring
        _ ≤ _ := by rw [mul_assoc];apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg M)
                    apply le_of_mul_le_mul_right (a:=(t⁻¹)^N) ?_ (pow_pos ht' N)
                    grw [show (t⁻¹)^d * Real.exp (-b*t⁻¹^2)*(t⁻¹)^N=(t⁻¹)^(d+N)*Real.exp (-b*t⁻¹^2) by rw [pow_add]; ring]; rw [show C*t^N*(t⁻¹)^N=C by rw [mul_assoc, ←mul_pow,mul_inv_cancel₀ ht.ne',one_pow,mul_one]]
                    refine le_trans ?_ hD
                    gcongr
                    linarith
  · exact fun _=>mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  unfold F; simp

lemma fiscal_stationary : Series.Radial.Stationary (fiscal (G:=G) (n:=n)) where
  smooth := (fiscal_smooth.of_le le_top).contDiffAt
  base0 := fiscal_zero
  base1 x := by rw [homogeneous_derivative _ _ _ ((fiscal_smooth.of_le le_top).contDiffAt),fiscal_grades x|>.2,mul_zero]

lemma coercion (even : Even n.val) : ∃ c>0,∀ u : Dir G n,c*‖u‖^2 ≤ Series.Radial.jet fiscal 2 u := by
  apply quadratic_min;intro u hu
  rw [homogeneous_derivative fiscal u 2 (fiscal_smooth.of_le le_top).contDiffAt, (fiscal_grades u).1]
  exact mul_pos (by norm_num [Nat.factorial]) (Q_pos even hu)
lemma chart_integrand (R : LocalRatio P){O : Observable G n}(h : LocalTest O) : ContDiffAt ℝ ∞ (accountingWith P O) 0 := (Chart.Ratio.jacobian_smooth R).of_le le_top |>.mul h.germ
lemma chart_meas (R : LocalRatio P){O : Observable G n}(h : LocalTest O) : Measurable (accountingWith P O) := (Chart.Ratio.jacobian_meas R).mul (h.boundedness.measurable.comp expLinks_meas)

open Series
lemma laplace (even : Even n.val) (R : LocalRatio P){O : Observable G n}(h : LocalTest O) :
    Series.Tested.Aspiration (scaledNum O) (rowsWith P O) := by
  intro k
  let K:=accountingWith P O
  obtain ⟨δ,hδ,H⟩ := Stationary.rescale_estimate W (F:=fiscal_stationary (G:=G) (n:=n)) (hf:=chart_integrand R h) (K:=K) (chart_meas R h) fiscal_smooth.continuous.measurable (coercion even) k
  let r := min δ (small G P)/2
  have ht : 0<r := half_pos (lt_min hδ (Chart.Ratio.small_pos R))
  have hs : r<small G P:=by unfold r;have he:=min_le_right δ (small G P);linarith [Chart.Ratio.small_pos R]
  obtain ⟨C,H⟩ := H r ⟨ht,by unfold r;have he:=min_le_left δ (small G P);linarith⟩
  obtain ⟨D,hD,H'⟩ := outer even R h hs ht (k+1)
  refine ⟨|C|+D,by positivity,?_⟩
  filter_upwards [H,Tested.eventually_pos] with t he ht'
  unfold scaledNum numerator
  simp only [Pi.sub_apply]
  let A:= chamber G (Cotree n) r
  rw [← integral_add_compl (s:=A) (Chart.Ratio.chamber_open R hs.le|>.measurableSet) (entries_integrable h.boundedness t),mul_add,show A=chamber G (Cotree n) r from rfl, inner R h hs ht ht'.le]
  let μ:=entryMeasure G n
  have htq (a b c:ℝ): ‖a+b-c‖≤‖a-c‖+‖b‖ := by rw [show a+b-c=a-c+b by ring];exact norm_add_le ..
  refine (htq ..).trans ((add_le_add (b:=C*t^(k+1)) ?_ (H' t ht')).trans ?_)
  · simpa [Tested.peval,Zone.eval,smul_eq_mul,rowsWith,K] using he
  rw [add_mul];gcongr;apply le_abs_self

lemma one_test : LocalTest (1 : Observable G n) := ⟨continuous_const,contDiffAt_const⟩


end YM.PertExtension.Orb
