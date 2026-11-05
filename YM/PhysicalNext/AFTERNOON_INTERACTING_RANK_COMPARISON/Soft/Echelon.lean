import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Change
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Petiole
/-!
# Pay the true-length path terms used in the new ancillary E
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Pump Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum Station Perch
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}
private lemma est_box (A : Stage) : ∀ᶠ x:ℝ in atTop,∀ β:ℝ,0<β→ β ≤ 4*x → ∀ Γ:ℝ,Γ ≤ x^(1/4:ℝ) → 0 ≤ Γ →
    ∀ p : BudgetPoint,p.threshold=Paint.phase x → p.supportExponent=A.supportExponent →
      boxesCost p β A.paths Γ ≤ x^(-(1/8):ℝ):=by
  let E (k:ℕ):=Real.exp (A.supportExponent * (1+2*k:ℝ))
  let c:=4*(E 3*A.paths+E 4*A.paths)+E 2
  filter_upwards [burst_limit,tall_limit.eventually (Work.E09.temp_cost (1/12) (by norm_num)),slack c (by norm_num:(-(1/4):ℝ)< -(1/8)), eventually_ge_atTop (1:ℝ)] with x hz he ht hp β h hb Γ hΓ hg p hQ hE
  have hx:0<x:=zero_lt_one.trans_le hp
  let t:=x^(-(5/12):ℝ); have hh_ζ:p.threshold ≤ t:= by
    have h:=Real.rpow_le_rpow_of_nonpos hx hz.1 (by norm_num:(-(1/2):ℝ)+1/12≤0)
    rw [hQ,← hz.2.2]; apply he.trans (h.trans_eq ?_); unfold t; norm_num
  unfold boxesCost detail; rw [hE,abs_of_nonneg h.le]; let K:=x^(-(1/4):ℝ)
  have hu n : E n * p.threshold^3*A.paths ≤ E n *t^3*A.paths:= by
    have hv := p.threshold_pos; have hy:=A.paths_pos; have hw := Real.exp_pos (A.supportExponent*(1+2*n)); gcongr
  have hZ : x*t^3=K:= by
    conv_lhs => arg 1; rw [← Real.rpow_one x]
    unfold t K; rw [← Real.rpow_natCast (_:ℝ) 3, ←Real.rpow_mul hx.le,← Real.rpow_add hx]; norm_num
  have hL:t^2*x^(1/4:ℝ)≤K:= by unfold t K; rw [← Real.rpow_natCast (_:ℝ) 2,←Real.rpow_mul hx.le,← Real.rpow_add hx]; apply Real.rpow_le_rpow_of_exponent_le hp; norm_num
  have hh n : 0≤ E n:= (Real.exp_pos _).le
  have h1 n (k:ℕ) (hk:3≤k): β*(E n*p.threshold^k*A.paths) ≤4*E n*A.paths*K:= by
    have he := A.paths_pos; have ht' := p.threshold_pos
    have ht := pow_le_pow_of_le_one p.threshold_pos.le p.threshold_le hk
    refine (mul_le_mul hb (le_trans ?_ (hu n)) (by have := hh n; positivity) (show 0≤4*x by positivity)).trans_eq ?_
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (hh n)) he.le
    rw [← hZ]; ring
  have h2:E 2*p.threshold^2*Γ≤ E 2*K:= by
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (hh _)
    exact (mul_le_mul (pow_le_pow_left₀ p.threshold_pos.le hh_ζ 2) hΓ hg (sq_nonneg t)).trans hL
  apply le_trans _ ht
  change β*(E 3*p.threshold^3*A.paths)+(β*(E 4*p.threshold^4*A.paths)+E 2*p.threshold^2*Γ) ≤ c*K; unfold c; linarith only [h1 3 3 le_rfl,h1 4 4 (show 3≤ (4:ℕ) by norm_num),h2]

private lemma gamma_house : ∀ᶠ x:ℝ in atTop, ∀ (a : Levels G) i, Atlas.clim a i=x →
    a.clock.loopCap i ≤ x^(1/4:ℝ) ∧ a.clock.allowance i ≤ spray x:= by
  filter_upwards [YM.Vac.Numbers.cost 1 (1/8) (by norm_num),slack 2 (by norm_num : (1/8:ℝ)<1/4), eventually_ge_atTop (1:ℝ)] with x hx ht hh a i hi
  let A:=a.clock; let B:=A.monitor i; have hB : B=YM.Vac.Numbers.P x:=hi ▸ rfl
  have he : 1≤ B:=Real.one_le_exp (sq_nonneg _); have ha : A.theta (A.J i) ≤ 1:= by
    have hp : (1:ℝ) ≤ A.J i:= by exact_mod_cast (by have ht:= A.adm i; omega : 1 ≤ A.J i)
    exact le_trans (a.fits.thetaRange i).2 (inv_le_one_of_one_le₀ hp)
  have hz : 0<x:= zero_lt_one.trans_le hh; let g:=A.hatCoupling i; have hg:g=(Real.sqrt x)⁻¹:= hi ▸ rfl
  refine ⟨?_,?_⟩
  · refine (mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le he ha).trans ((hB.symm ▸ hx) : B^ (1:ℝ)≤_)) (show (0:ℝ)≤2 by norm_num)).trans ht
  have hH:0<g:= hg.symm ▸ inv_pos.mpr (Real.sqrt_pos.mpr hz); have hk:g≤1:= hg.symm ▸ inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hh)
  change g^((11:ℝ)/5)≤_; apply (Real.rpow_le_rpow_of_exponent_ge hH hk (show (2:ℝ) ≤ 11/5 by norm_num)).trans
  rw [Real.rpow_two,hg,inv_pow,Real.sq_sqrt hz.le,← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hh (by norm_num)
structure Costs (A : Stage) (G : Gauge) (s : ℝ):Prop where
  permit (a : Levels G) (i : ℕ) : Atlas.clim a i=s → a.clock.allowance i ≤ spray s
  prices (a : Levels G) (i : ℕ) :
    let x:=Atlas.clim a i; x∈Set.Icc (s/2) s → ∀ t:ℝ, t>0 → t≤4*x → ∀ p : BudgetPoint,
      p.B=walls x → p.supportExponent=A.supportExponent → p.threshold=Paint.phase x →
        boxesCost p t A.paths (a.clock.loopCap i)≤ spray s ∧ p.supportExponent / p.B ≤ A.width
lemma prediction (G : Gauge) (A : Stage) : ∀ᶠ s in atTop,Costs A G s:=by
  let t:=A.width; let f:=A.supportExponent
  have hM: Tendsto (fun x=>(walls x:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp big
  obtain ⟨v,hv⟩:=eventually_atTop.mp ((gamma_house (G:=G)).and ((est_box A).and (hM.eventually_ge_atTop (f/t))))
  filter_upwards [gamma_house (G:=G),Perch.half.eventually_ge_atTop v,spray_side (-(1/8)) (by norm_num)] with s hp h he
  refine ⟨fun a i hi=> (hp a i hi).2,fun a i=> ?_⟩
  intro x hx β hβ hz p hb hf ht; obtain ⟨hh,hy,hu⟩:= hv x (h.trans hx.1)
  constructor
  · have hh':0 ≤ a.clock.loopCap i:= by unfold Calendar.loopCap Calendar.monitor; positivity
    exact (hy β hβ hz _ (hh a i rfl).1 hh' _ ht hf).trans (he x hx)
  have hk: 0 < (p.B:ℝ):= by exact_mod_cast p.B_pos
  rw [hf, div_le_iff₀ hk]; rw [hb]; rw [mul_comm]; exact (div_le_iff₀ A.width_pos).1 hu
end YM.PhysicalNext.InteractingRank.Soft
