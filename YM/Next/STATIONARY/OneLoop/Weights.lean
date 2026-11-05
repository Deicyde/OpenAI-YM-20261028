import YM.Next.STATIONARY.OneLoop.Leading

set_option autoImplicit false
/-!
# Taylor in real variable τ at 0. Entry units only. Infrared tariffs
use multiplication inequalities of `vflux` positive. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] {G : Gauge} {V U : Jar G} {σ C D A r a : ℝ} {n : ℕ}

abbrev ReelF (α β : Type) := ℝ→ CompM α β
def Prick (v : ReelF α β) := ∀ i j,AnalyticAt ℝ (fun t=>v t i j) 0
def flareY (n : ℕ) (u : ℝ→ℂ) := iteratedFDeriv ℝ n u 0 1
def jarY (n : ℕ) (u : ReelF α β) := of fun i j=> flareY n (fun z => u z i j)

namespace Prick
variable {U V : ReelF α β} {X Y : ReelF α α} {Z : ReelF β γ}
lemma plus (hU : Prick U) (hv : Prick V) : Prick (U+V) := fun i j=> (hU i j).add (hv i j)

lemma scale (hu : Prick U) (a : ℂ) : Prick (a • U) := fun i j=> (analyticAt_const.mul (hu i j))
lemma mult (h : Prick U) (he : Prick Z) : Prick (fun z=> U z*Z z) := by
  intro i j; simp only [Matrix.mul_apply]; apply ContDiffAt.analyticAt; exact ContDiffAt.sum fun k _ => ((h i k).mul (he k j)).contDiffAt
lemma holds (u : CompM α β) : Prick (fun _=>u) := fun i j=> analyticAt_const
lemma det (h : Prick X) : AnalyticAt ℝ (fun t=> (X t).det) 0 := by
  simp only [Matrix.det_apply,Units.smul_def,zsmul_eq_mul]
  -- product
  apply ContDiffAt.analyticAt; apply ContDiffAt.sum; intro i _
  apply ContDiffAt.mul contDiffAt_const
  suffices ht : ∀ S : Finset α,ContDiffAt ℝ ω (fun z=> ∏ j∈S,X z (i j) j) 0 from ht univ
  intro S; induction S using Finset.induction with
  | empty => simpa using (show ContDiffAt ℝ ω (fun _ : ℝ=> (1:ℂ)) 0 from contDiffAt_const)
  | insert a s hs ih => simp_rw [prod_insert hs]; exact (h _ _).contDiffAt.mul ih
lemma poles (h : Prick X) (hp : IsUnit (X 0).det) : Prick (fun z=> (X z)⁻¹) := by
  intro i j; simp_rw [Matrix.inv_def, Ring.inverse_eq_inv,Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.analyticAt; apply ContDiffAt.mul (h.det.contDiffAt.inv hp.ne_zero)
  simp_rw [Matrix.adjugate_apply]; refine AnalyticAt.contDiffAt (Prick.det (X:= fun z=> _) ?_)
  intro k l; simp_rw [Matrix.updateRow_apply]; split
  next e => exact analyticAt_const
  exact h k l
end Prick

section cast
variable {U V : ReelF α β} {T : ReelF β γ} {x y : ℝ→ℂ}
lemma flare_sum {δ : Type} (S : Finset δ) (f : δ→ℝ→ℂ) (h : ∀ i∈S,AnalyticAt ℝ (f i) 0) : flareY n (fun p=>∑ i∈S,f i p)=∑ i∈S,flareY n (f i) := by
  rw [flareY, iteratedFDeriv_fun_sum_apply (fun i hi => (h i hi).contDiffAt),_root_.sum_apply]; rfl
lemma flare_second (h : AnalyticAt ℝ x 0) (he : AnalyticAt ℝ y 0) : flareY 2 (x*y)= x 0* flareY 2 y + flareY 1 x*flareY 1 y+ (flareY 1 x*flareY 1 y + flareY 2 x*y 0) := by
  simp only [flareY]; rw [show (1:Fin 2→ℝ)=![1,1] by ext1 i; fin_cases i <;> rfl,furtive x y h he]; simp only [iteratedFDeriv_one_apply]; rfl
lemma jar_multi (h : Prick U) (he : Prick T) : jarY 2 (fun z=> U z*T z) = U 0 * jarY 2 T+ jarY 1 U * jarY 1 T+(jarY 1 U*jarY 1 T+jarY 2 U*T 0) := by
  ext1 i j; unfold jarY; rw [Matrix.of_apply]; simp only [Matrix.mul_apply,Matrix.add_apply]
  rw [flare_sum]; swap; · exact fun k _=> (h i k).mul (he k j)
  simp only [Matrix.mul_apply, ← sum_add_distrib]; apply sum_congr rfl; intro k _; exact flare_second (h i k) (he k j)
lemma flare_first (h : AnalyticAt ℝ x 0) (he : AnalyticAt ℝ y 0) : flareY 1 (x*y)= x 0* flareY 1 y+ flareY 1 x*y 0 := by simp only [flareY,iteratedFDeriv_one_apply]; exact furtiveP x y 0 h.differentiableAt he.differentiableAt _
lemma jar_ini (h : Prick U) (he : Prick T) : jarY 1 (fun z=>U z*T z)= U 0 *jarY 1 T +jarY 1 U*T 0 := by
  ext1 i j; unfold jarY; rw [Matrix.of_apply]; simp only [Matrix.mul_apply,Matrix.add_apply]; rw [flare_sum]; swap; · exact fun k _=> (h i k).mul (he k j)
  simp only [Matrix.mul_apply, ← sum_add_distrib]; exact sum_congr rfl fun k _=> flare_first (h i k) (he k j)
lemma flare_add (h : AnalyticAt ℝ x 0) (he : AnalyticAt ℝ y 0) : flareY n (x+y)= flareY n x + flareY n y := by unfold flareY; rw [iteratedFDeriv_add_apply h.contDiffAt he.contDiffAt,_root_.add_apply]
lemma flare_dec (h : AnalyticAt ℝ x 0) (he : AnalyticAt ℝ y 0) : flareY n (x-y)= flareY n x- flareY n y := by rw [eq_sub_iff_add_eq,← flare_add (h.sub he) he, sub_add_cancel]
lemma flare_scale (h : AnalyticAt ℝ x 0) (a : ℂ) : flareY n (fun y=>a*x y)= a * flareY n x := by
  exact DFunLike.congr_fun ((ContinuousLinearMap.mul ℝ ℂ a).iteratedFDeriv_comp_left h.contDiffAt (by exact (show (↑n : WithTop ℕ∞) ≤ ω from le_top))) (1:Fin n →ℝ)
lemma jar_add (h : Prick U) (ht : Prick V) : jarY n (U+V)=jarY n U+jarY n V := by ext1 i j; exact flare_add (h i j) (ht i j)

lemma jar_scale (h : Prick U) (a : ℂ) : jarY n (a • U) = a • jarY n U := by ext1 i j; exact flare_scale (h i j) _
lemma jar_const (h : 0<n) (U : CompM α β) : jarY n (fun _=>U)=0 := by ext1 i j; simp only [jarY,flareY,Matrix.of_apply,iteratedFDeriv_const_of_ne (Nat.ne_of_gt h)]; rfl
lemma jar_tape (h : U =ᶠ[𝓝 0] V) : jarY n U=jarY n V := by
  ext i j; unfold jarY; simp only [Matrix.of_apply]
  have hp : (fun z => U z i j)=ᶠ[𝓝 0] fun z => V z i j:= by filter_upwards [h] with z hz; rw [hz]
  unfold flareY; rw [(hp.iteratedFDeriv ℝ n).eq_of_nhds]
lemma flare_oneZ (a : ℂ) (h : 0<n) : flareY n (fun _=>a)=0 := by simp [flareY,iteratedFDeriv_const_of_ne (Nat.ne_of_gt h)]
@[simp] lemma jar_now (U : ReelF α β) : jarY 0 U=U 0 := by ext; simp [jarY,flareY]
end cast
end YM.Stationary
end

/-!
# Weighted path cost. `r^n` x EXTERNAL derivatives, raw. For flat inverse
provide `I*k_path ≤ A`, `k_path⁻¹*flat ≤ C` separately. Products ex.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] {G : Gauge} {σ C D A r a : ℝ} {n : ℕ}

structure Jam (r : ℝ) (U : ReelF α β) (A : ℝ) : Prop where
    run : Prick U
    prices i : i≤ 2 → r^i*vflux (jarY i U)≤A

def inverseBill (A B : ℝ) :=
    (B + A*B^2)+(2*A^2*B^3+B^2*A)

namespace Jam
variable {U V : ReelF α β} {T : ReelF β γ}
lemma ipay (h : Jam r U A) : vflux (U 0) ≤ A := by simpa only [jar_now,pow_zero,one_mul] using h.prices 0 (by decide)
lemma units (h : Jam r U A) : 0≤ A := (flux_nonneg _).trans h.ipay
lemma mono (h : Jam r U A) (he : A ≤ C) : Jam r U C := ⟨h.run,fun i hi => (h.prices i hi).trans he⟩

lemma both (h : Jam r U C) (hv : Jam r V D) (he : 0≤r) : Jam r (U+V) (C+D) := by
  refine ⟨h.run.plus hv.run,fun i hi=>?_⟩; rw [jar_add h.run hv.run]; exact (mul_le_mul_of_nonneg_left (flux_plus ..) (by positivity)).trans ((mul_add ..).trans_le (add_le_add (h.prices i hi) (hv.prices i hi)))
lemma costs (h : Jam r U C) (a : ℂ) : Jam r (a • U) (‖a‖*C) := ⟨h.run.scale a, fun i hi=> by
    rw [jar_scale h.run,flux_cost,mul_left_comm]; exact mul_le_mul_of_nonneg_left (h.prices i hi) (norm_nonneg _)⟩
lemma negative (h : Jam r U C) : Jam r (-U) C := by simpa using h.costs (-1)
lemma seats (r : ℝ) (U : CompM α β) : Jam r (fun _=>U) (vflux U) := ⟨Prick.holds _, fun i hi=> by
    interval_cases i; · simp
    all_goals rw [jar_const (by decide) U,flux_zero]; simp [flux_nonneg ..]⟩
-- congr eventually. use on inverse product tests
lemma foreignM (h : Jam r U A) (hz : U =ᶠ[𝓝 0] V) : Jam r V A := ⟨fun i j=> (h.run i j).congr (by filter_upwards [hz] with x hx; rw [hx]),fun i hi=> by rw [← jar_tape hz]; exact h.prices i hi⟩
lemma summer {U V : CompM α β} (h : r^n*vflux U ≤ A) (hv : r^n*vflux V ≤ C) (hr : 0≤r) : r^n*vflux (U+V)≤ A+C := (mul_le_mul_of_nonneg_left (flux_plus ..) (by positivity)).trans ((mul_add ..).trans_le (add_le_add h hv))
lemma sweeter {U : CompM α β} {V : CompM β γ} {k} (h : r^n*vflux U ≤ A) (hv : r^k*vflux V ≤ C) (hr : 0≤r) : r^(n+k)*vflux (U*V)≤ A*C := by
  apply le_trans (mul_le_mul_of_nonneg_left (flux_power ..) (by positivity)) _; rw [pow_add,mul_mul_mul_comm]
  exact mul_le_mul h hv (mul_nonneg (by positivity) (flux_nonneg _)) ((mul_nonneg (by positivity) (flux_nonneg _)).trans h)
lemma sweet (h : Jam r U A) (hv : Jam r T C) (he : 0≤r) : Jam r (fun z=> U z*T z) (4*A*C) := by
  refine ⟨h.run.mult hv.run, fun i hi=>?_⟩
  let W := fun z=> U z*T z
  have hp j k (he' : j≤ 2) (hk:k≤2) := sweeter (h.prices j he') (hv.prices k hk) he
  have hL : 0 ≤ A*C := mul_nonneg h.units hv.units
  interval_cases i
  · rw [jar_now]; exact (show _≤A*C from (by simpa only [jar_now] using hp 0 0 (by decide) (by decide))).trans (by linarith)
  · rw [jar_ini h.run hv.run, ← jar_now U,← jar_now T]; exact (summer (hp 0 1 (by decide) (by decide)) (hp 1 0 (by decide) (by decide)) he).trans (by linarith)
  rw [jar_multi h.run hv.run, ← jar_now U, ← jar_now T]; exact (summer (summer (hp 0 2 (by decide) le_rfl) (hp 1 1 (by decide) (by decide)) he) (summer (hp 1 1 (by decide) (by decide)) (hp 2 0 le_rfl (by decide)) he) he).trans_eq (by ring)

lemma rebounds {X : ReelF α α} (h : Jam r X (A*a)) (he : IsUnit (X 0).det) (hv : vflux (X 0)⁻¹≤ C/a) (ha : 0<a) (hr : 0≤r) : Jam r (fun x=> (X x)⁻¹) ((inverseBill A C)/a) := by
  let Y x := (X x)⁻¹
  have hE : Prick Y := h.run.poles he
  have hh : (fun x=> Y x*X x)=ᶠ[𝓝 0] fun _=>1 := by filter_upwards [(h.run.det.continuousAt).eventually_ne he.ne_zero] with x hx; exact Matrix.nonsing_inv_mul _ hx.isUnit
  have hY := eq_neg_of_add_eq_zero_right ((jar_ini hE h.run).symm.trans ((jar_tape (n:=1) hh).trans (jar_const one_pos _)))
  have hV : jarY 1 Y= -(Y 0 *jarY 1 X*Y 0) := by
    have hh := congr_arg (· * Y 0) hY
    rw [← Matrix.mul_nonsing_inv_cancel_right (X 0) (jarY 1 Y) he];
    exact hh.trans (Matrix.neg_mul ..)
  have ht' := h.prices 0 (by decide); rw [jar_now] at ht'
  have hz : r^0 *vflux (Y 0) ≤ C/a := by simpa using hv
  have h1 : r^1*vflux (jarY 1 Y) ≤ A*C^2/a := by rw [hV,flux_neg]; refine (sweeter (sweeter hz (h.prices 1 (by decide)) hr) hz hr).trans_eq (?_); field_simp
  have hl : r^2*vflux (jarY 2 Y)≤ (2*A^2*C^3+C^2*A)/a := by
    let U := Y 0*jarY 2 X +jarY 1 Y*jarY 1 X +jarY 1 Y * jarY 1 X
    have ht : U + jarY 2 Y * X 0=0 := Eq.trans (by unfold U; rw [add_assoc (_ + _), ← jar_multi hE h.run]) ((jar_tape (n:=2) hh).trans (jar_const (by decide : 0<2) _))
    have hx : jarY 2 Y= -(U*Y 0) := by
      have hh := congr_arg (· * Y 0) (eq_neg_of_add_eq_zero_right ht); rw [← Matrix.mul_nonsing_inv_cancel_right (X 0) (jarY 2 Y) he]; exact hh.trans (Matrix.neg_mul ..)
    have hL := sweeter h1 (h.prices 1 (by decide)) hr
    rw [hx, flux_neg]; refine (sweeter (summer (summer (sweeter hz (h.prices 2 le_rfl) hr) hL hr) hL hr) hz hr).trans_eq ?_; field_simp; ring
  have hA : 0≤ A := nonneg_of_mul_nonneg_left h.units ha
  have hC : 0 ≤ C := by have hh : 0 ≤ C/a := ((flux_nonneg _).trans hv); rwa [le_div_iff₀ ha, zero_mul] at hh
  have hp : 0≤2*A^2*C^3+C^2*A := by positivity
  have hP : 0≤ A*C^2 := by positivity
  change Jam r Y _; refine ⟨hE,fun i hi =>?_⟩; interval_cases i
  · rw [jar_now]; exact hz.trans (div_le_div_of_nonneg_right (by unfold inverseBill; linarith) ha.le)
  · exact h1.trans (div_le_div_of_nonneg_right (by unfold inverseBill; linarith) ha.le)
  exact hl.trans (div_le_div_of_nonneg_right (by unfold inverseBill; linarith) ha.le)
end Jam
end YM.Stationary
end

/-!
# Shellwise prices. Param `ι` allows carrying Ward data and heights without
coupling to any graph choice. Rates from same atmosphere along three paths.
 `cost*default`, require rates nonnegative to polar organ.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι ν α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] {G : Gauge} {T Z L M ρ : ι →ℝ}

def Fiesta (ρ T : ι → ℝ) (U : ι → ReelF α β) := ∃ C : ℝ,0≤C ∧ (∀ i,0≤ρ i ∧ 0≤T i) ∧ ∀ i, Jam (ρ i) (U i) (C*T i)
namespace Fiesta
variable {U V : ι → ReelF α β} {W : ι → ReelF β γ}
lemma grows (h : Fiesta ρ L U) (he : L ≤ M) : Fiesta ρ M U := by
  obtain ⟨A,hA,hp,hU⟩ := h; exact ⟨A,hA,fun i=> ⟨(hp i).1,(hp i).2.trans (he i)⟩,fun i=> (hU i).mono (mul_le_mul_of_nonneg_left (he _) hA)⟩
lemma dilutes (h : Fiesta ρ L U) (a : ℝ) (ha : 0 ≤ a) (hM : ∀ i,0 ≤ M i) (he : ∀ i,L i ≤ a*M i) : Fiesta ρ M U := by
  obtain ⟨A,hA,hp,hU⟩ := h; exact ⟨A*a,mul_nonneg hA ha,fun i=> ⟨(hp i).1, hM _⟩,fun i=> (hU i).mono ((mul_le_mul_of_nonneg_left (he _) hA).trans_eq (mul_assoc ..).symm)⟩
lemma introp (h : Fiesta ρ L U) (he : ∀ i,U i =ᶠ[𝓝 0] V i) : Fiesta ρ L V := by obtain ⟨A,hA,hp,hU⟩ := h; exact ⟨A,hA,hp,fun i=> (hU i).foreignM (he i)⟩
lemma costsP (h : Fiesta ρ L U) (f : ι→ℂ) (hx : ∀ i, ‖f i‖≤M i) : Fiesta ρ (fun i=> M i* L i) (fun i=> f i • U i) := by
  obtain ⟨A,hA,hp,hU⟩ := h
  refine ⟨A,hA,fun i=>⟨(hp i).1,mul_nonneg ((norm_nonneg _).trans (hx i)) (hp i).2⟩,fun i => Jam.mono ((hU i).costs (f i)) ((mul_le_mul_of_nonneg_right (hx i) (mul_nonneg hA (hp i).2)).trans_eq (mul_left_comm ..))⟩
lemma pair (h : Fiesta ρ L U) (hw : Fiesta ρ M W) : Fiesta ρ (L*M) (fun i z=> U i z*W i z) := by
  obtain ⟨A,hA,hp,hU⟩ := h; obtain ⟨B,hB,hq,hV⟩ := hw
  refine ⟨4*A*B,by positivity,fun i => ⟨(hp i).1,mul_nonneg (hp i).2 (hq i).2⟩,fun i=> (Jam.sweet (hU i) (hV i) (hp i).1).mono (by rw [Pi.mul_apply]; exact le_of_eq (by ring))⟩
lemma plus (h : Fiesta ρ L U) (hv : Fiesta ρ L V) : Fiesta ρ L (U+V) := by
  obtain ⟨A,hA,hp,hU⟩ := h; obtain ⟨B,hB,hq,hV⟩ := hv
  exact ⟨A+B,add_nonneg hA hB,hp,fun i=>by rw [add_mul]; exact (hU i).both (hV i) (hp i).1⟩

lemma neg (h : Fiesta ρ L U) : Fiesta ρ L (-U) := by obtain ⟨A,hA,hp,hU⟩ := h; exact ⟨A,hA,hp,fun i=> (hU i).negative⟩
lemma seats (h : ∀ i, 0 ≤ ρ i ∧ 0≤T i) (U : CompM α β) (hi : U=0) : Fiesta ρ T (fun _ _=>U) := by
  refine ⟨0,le_rfl,h,fun i=>?_⟩; rw [hi,zero_mul]; exact flux_zero (α:=α) (β:=β) ▸ Jam.seats _ _
lemma subs (hu : ∀ i,0≤ρ i) (U : CompM α β) : Fiesta ρ 1 (fun _ _=>U) := by
  exact ⟨vflux U,flux_nonneg _, fun i => ⟨hu i,zero_le_one⟩,fun i=> by rw [Pi.one_apply,mul_one]; exact Jam.seats _ _⟩
-- inverse when pos bound supplied along family
variable {X Y : ι→ReelF α α}
lemma inv (h : Fiesta ρ T X) (hp : ∀ i,0<T i ∧ IsUnit (X i 0).det) (hx : ∃ A : ℝ,0≤A∧ ∀ i,vflux (X i 0)⁻¹≤ A / T i) : Fiesta ρ (fun i => (T i)⁻¹) (fun i z=> (X i z)⁻¹) := by
  obtain ⟨A,hA,hk,hU⟩ := h; obtain ⟨B,hB,hX⟩ := hx; refine ⟨inverseBill A B,by unfold inverseBill; positivity,fun i=>⟨(hk i).1,inv_nonneg.mpr (hk i).2⟩,fun i=>?_⟩
  rw [← div_eq_mul_inv]; exact (hU i).rebounds (hp i).2 (hX i) (hp i).1 (hk i).1
section compar
-- telescoping insertion precision on differences. Make sure differences
-- on ACTUAL sig for near edges.
variable {W J : ι→ReelF β γ}
lemma pairDif (h : Fiesta ρ L U) (ht : Fiesta ρ M J) (hv : Fiesta ρ (T*L) (U-V)) (hh : Fiesta ρ (T*M) (W-J)) : Fiesta ρ (T*(L*M)) ((fun i z=>U i z*W i z) - (fun i z=>V i z*J i z)) := by
  let F : ι→ReelF α γ := fun i z=> U i z* ((W-J) i z)
  have h1 : Fiesta ρ (T*(L*M)) F := mul_left_comm L T M ▸ h.pair hh
  let E i z := (U-V) i z * J i z
  have h2 : Fiesta ρ (T*(L*M)) E := mul_assoc T L M ▸ hv.pair ht
  refine (h1.plus h2).introp (fun i=> Eventually.of_forall (fun x => ?_)); change U i x*(W i x-J i x)+(U i x-V i x)*J i x= U i x*W i x- V i x*J i x; rw [Matrix.mul_sub,Matrix.sub_mul]; abel
lemma invDiff (h : Fiesta ρ T X) (he : Fiesta ρ T Y) (hf : Fiesta ρ T⁻¹ (fun i x=> (X i x)⁻¹)) (hg : Fiesta ρ T⁻¹ (fun i x=> (Y i x)⁻¹)) (hv : ∀ i,0<T i ∧ IsUnit (X i 0).det ∧ IsUnit (Y i 0).det) (hp : Fiesta ρ (L*T) (X-Y)) : Fiesta ρ (L*T⁻¹) ((fun i x=> (X i x)⁻¹)-(fun i x=> (Y i x)⁻¹)) := by
  have hh := (hf.pair hp).pair hg|>.neg
  rw [show T⁻¹*(L*T)*T⁻¹=L*T⁻¹ by congr 1; funext i; dsimp; field_simp [(hv i).1.ne']] at hh
  refine hh.introp fun i=> ?_
  obtain ⟨A,hA,hZ,H⟩ := h; obtain ⟨B,hB,hW,K⟩ := he
  filter_upwards [((H i).run.det.continuousAt.eventually_ne (hv i).2.1.ne_zero),((K i).run.det.continuousAt.eventually_ne (hv i).2.2.ne_zero)] with x hx he
  change - ((X i x)⁻¹ * (X i x-Y i x) * (Y i x)⁻¹)= (X i x)⁻¹-(Y i x)⁻¹
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.nonsing_inv_mul _ (Ne.isUnit hx),Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit he),mul_one,neg_sub]
end compar
end Fiesta
end YM.Stationary
end

/-!
# PreL scalar contour supplies input denominator vertices. Domain
real Ball at origin fixed radius. Derivative along elastic real rays.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] {G : Gauge} {p : Clip} {u : ℕ} {σ η A K C D r a : ℝ}
section cost
variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : X→E}
lemma fare_lefter (X E : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X→E) (n : ℕ) (x) : ‖fderiv ℝ (iteratedFDeriv ℝ n f) x‖=‖iteratedFDeriv ℝ (n+1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]
-- Mark if given analyticity in X positions. compact r permits all shift directions <=∞.
lemma dawn (h : AnalyticOnNhd ℝ f (closedBall 0 r)) (he : Rays u f)
    (hr : 0≤r) (ha : 0≤A) (hv : ∀ x∈ closedBall 0 r, ‖iteratedFDeriv ℝ u f x‖≤A) (b : X) (hk : b∈closedBall 0 r) (n) (hn : n ≤ u) : ‖iteratedFDeriv ℝ n f b‖ ≤ A* ‖b‖^(u-n) := by
  have hs : (closedBall (0:X) ‖b‖) ⊆ closedBall 0 r := closedBall_subset_closedBall (by simpa using hk)
  suffices ht : ∀ (i j : ℕ),j+i=u → ∀ b'∈ closedBall (0:X) ‖b‖, ‖iteratedFDeriv ℝ j f b'‖ ≤ A*‖b‖^i from ht _ _ (by omega) _ (by simp)
  intro i; induction i with
  | zero => intro j h b hb; rw [show j=u from h,pow_zero,mul_one]; exact hv b (hs hb)
  | succ i ih =>
    intro j hz v heq
    let S := closedBall (0:X) ‖b‖
    let T := iteratedFDeriv ℝ j f
    have ht t (ht : t∈ S) := ih (j+1) (by omega) t ht
    have hh : T 0=0 := (rays_jet (h _ (mem_closedBall_self hr)) u).1 he j (by omega)
    have hu := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (s:=S) (f:=T) (C:=A*‖b‖^i) (fun x hx => (show ContDiffAt ℝ ω f x from (h x (hs hx)).contDiffAt).differentiableAt_iteratedFDeriv (by simp)) (fun x hx => (fare_lefter X E f j x).trans_le (ht x hx)) (convex_closedBall (0:X) _) (mem_closedBall_self (norm_nonneg _)) heq
    unfold T at *; rw [hh, sub_zero, sub_zero] at hu
    exact hu.trans ((mul_le_mul_of_nonneg_left (by simpa using heq) (by positivity : 0 ≤ A*‖b‖^i)).trans_eq (by rw [pow_succ,mul_assoc]))
end cost

lemma toasty {f : Phase α→ ℂ} (h : Firm σ A f) (x : Phase α) (hx : star x=x) (n) : ∀ y ∈ ball x (σ/2^n), ‖iteratedFDeriv ℂ n f y‖ ≤ A*circleTax σ n := by
  have hs := h.width_pos
  have ht {p : Phase α} (hp : p ∈ ball x σ) : p∈ strip σ := by
    intro i; have hz := norm_le_pi_norm (p-x) i
    rw [mem_ball,dist_eq_norm] at hp
    have hh : ((p-x) i).im=(p i).im := by rw [Pi.sub_apply,Complex.sub_im,Complex.conj_eq_iff_im.mp (congr_fun hx i),sub_zero]
    exact hh ▸ (Complex.abs_im_le_norm _ |>.trans_lt (hz.trans_lt hp))
  induction n with
  | zero => simpa [circleTax,norm_iteratedFDeriv_zero] using fun y (hy : y∈ ball x σ) => h.2 y (ht hy)
  | succ n ih =>
    intro p hp; let R := σ/2^n
    have hr : 0<R := by unfold R; positivity
    have hi : σ/2^(n+1)=R/2 := by unfold R; rw [pow_succ]; ring
    have he : R ≤ σ := div_le_self hs.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    have hD v (hv : v∈ ball x R) : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) v :=
      ((h.analytic (ht (ball_subset_ball he hv))).contDiffAt (n:=ω)).differentiableAt_iteratedFDeriv (by simp)
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply, LinearIsometryEquiv.norm_map,circleTax,hi, ← mul_div_assoc]; exact chord hr hD ih (hi ▸ hp)

section atCost
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : Phase α→ℂ}
-- cost differentiating P∘... by CLM no ambient shape. Real radial chords.
lemma toast_into (h : Firm σ A f) (S : X→L[ℝ] Phase α) (p : X) (hp : star (S p)=S p) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ S) p‖ ≤ A*circleTax σ j * ‖S‖^j := by
  have hs := h.analytic (h.in_range hp); have hr : 0<σ := h.width_pos
  have he : ContDiffAt ℝ ω f (S p) := (hs.contDiffAt (n:=ω)).restrict_scalars ℝ
  let T := iteratedFDeriv ℂ j f (S p)
  have hv : ∀ v : Fin j→ X, iteratedFDeriv ℝ j (f ∘ S) p v=T (S ∘ v) := by
    intro v; unfold T
    have hu := (hs.contDiffAt (n:=(↑j:WithTop ℕ∞))).restrictScalars_iteratedFDeriv (𝕜:=ℝ)
    rw [wired S he.analyticAt,← hu]; rfl
  have ht : ‖T‖ ≤ A*circleTax σ j := toasty h (S p) hp _ _ (mem_ball_self (by positivity))
  have hA : 0≤ A := h.budget_nonneg
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg ((norm_nonneg _).trans ht) (by positivity)); intro v; rw [hv];
  refine (ContinuousMultilinearMap.le_opNorm T (S ∘ v)).trans ?_
  trans A*circleTax σ j * (∏ i,‖S‖ * ‖v i‖)
  · refine mul_le_mul ht ?_ (by exact Finset.prod_nonneg (fun k _=> norm_nonneg _)) ((norm_nonneg T).trans ht)
    exact prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => S.le_opNorm _
  simp [prod_mul_distrib,mul_assoc]
-- sum compact caps. ceiling.
variable [ProperSpace X]
lemma balconyC {Y : Type} [Fintype Y] (v : ℝ) (n : ℕ) (f : Y→X→CompM α α) (hf : ∀ y i j p,AnalyticAt ℝ (fun z=> f y z i j) p) : ∃ A : ℝ,0≤A ∧ ∀ l, l≤n → ∀ y i j,∀ p∈closedBall 0 v, ‖iteratedFDeriv ℝ l (fun z=> f y z i j) p‖ ≤ A := by
  let V (y : Fin (n+1)×Y×α×α) p := ‖iteratedFDeriv ℝ y.1.val (fun z=> f y.2.1 z y.2.2.1 y.2.2.2) p‖
  have hp y : Continuous (V y) := by
    let H z := f y.2.1 z y.2.2.1 y.2.2.2
    apply Continuous.norm (f:=iteratedFDeriv ℝ y.1.val H); rw [continuous_iff_continuousAt]; intro p; exact ((hf y.2.1 y.2.2.1 y.2.2.2 p).contDiffAt (n:=ω)).continuousAt_iteratedFDeriv le_top
  choose A hA using fun y => ((isCompact_closedBall _ v).image (hp y)).bddAbove
  refine ⟨∑ y,|A y|,sum_nonneg (fun i _=> abs_nonneg _), fun l hl y i j p hh => ?_⟩; let k : Fin (n+1) := ⟨l, by omega⟩
  exact (hA (k,y,i,j) ⟨p,hh,rfl⟩).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=> |A i|) (fun _ _=> abs_nonneg _) (mem_univ _)))
end atCost
end YM.Stationary
end

/-!
# Bottle supplies Film phase caps BEFORE µ: weighted drawing outputs. The
p informs three insertions (with double tag restricted p,p of opposite signs)
on actual Track. No split margins at Fourier-cut radii. Arch Y geometry
through Brill style.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α] {G : Gauge} {P : Patch} {V U : Jar G} {σ η A D C ρ μ : ℝ} {b : Track} {k : ℕ}

section stitch
-- pour projections. let rather than make `Leagues`.
def coax (v : Track) : Space 1 := caftan (t:=1) (wineShift (![]:Fin 0→_) (axes v))
def cento (v : GlideTrack) : Space 2 := caftan (wineShift (![axes v.1]:Fin 1→_) (axes v.2))
def cinch (v : GlideTrack) : Space 3 := caftan (wineShift (![-axes v.1,axes v.1]:Fin 2→_) (axes v.2))

def coaxes : Track→L[ℝ] Space 1 := LinearMap.toContinuousLinearMap {
  toFun := coax
  map_add' x y := by ext1 ⟨i,j⟩; fin_cases i; simp [coax,caftan,wineShift,duoTop,axes]
  map_smul' t x := by ext1 ⟨i,j⟩; fin_cases i; simp [coax,caftan,wineShift,duoTop,axes,Complex.real_smul] }
def centaur : GlideTrack→L[ℝ] Space 2 := LinearMap.toContinuousLinearMap {
  toFun := cento
  map_add' x y := by ext1 ⟨i,j⟩; fin_cases i <;> simp [cento,caftan,wineShift,duoTop,axes]; ring
  map_smul' t x := by ext1 ⟨i,j⟩; fin_cases i <;> simp [cento,caftan,wineShift,duoTop,axes,Complex.real_smul]  }
def cinnamon : GlideTrack→L[ℝ] Space 3 := LinearMap.toContinuousLinearMap {
  toFun := cinch
  map_add' x y := by ext1 ⟨i,j⟩; fin_cases i <;> simp [cinch,caftan,wineShift,duoTop,axes, Fin.sum_univ_succ]; all_goals ring
  map_smul' t x := by ext1 ⟨i,j⟩; fin_cases i <;> simp [cinch,caftan,wineShift,duoTop,axes,Complex.real_smul,Fin.sum_univ_succ] }

lemma coaxR p : star (coaxes p)=coaxes p := by ext1 ⟨i,j⟩; fin_cases i; simp [coaxes,coax,caftan,wineShift,duoTop,axes]
lemma centR_act p : star (centaur p)=centaur p := by ext1 ⟨i,j⟩; fin_cases i <;> simp [centaur,cento,caftan,wineShift,duoTop,axes]
lemma cinnamon_act p : star (cinnamon p)=cinnamon p := by ext1 ⟨i,j⟩; fin_cases i <;> simp [cinnamon,cinch,caftan,wineShift,duoTop,axes,Fin.sum_univ_succ]
end stitch

abbrev ashP {ι : Type} (T : Film ι α α) (x : Track) := T.tab (axes x)
abbrev ashQ {ι : Type} (T : Film ι α α) (b : ι) (x : GlideTrack) := T.spot b (axes x.1) (axes x.2)
abbrev ashR {ι : Type} (T : Film ι α α) (b : ι) (x : GlideTrack) := T.arch b b (-axes x.1) (axes x.1) (axes x.2)
-- real local differentiability in G
variable {U : Jar G}
lemma ashCost1 (h : V.fees σ C) (x i j n) : ‖iteratedFDeriv ℝ n (fun z : Track=> ashP V.cast z i j) x‖ ≤ C *circleTax σ n* ‖coaxes‖^n := by
  exact toast_into (h.1 _ _) coaxes _ (coaxR _) _
lemma ashCost2 (h : V.fees σ C) (x b i j n) : ‖iteratedFDeriv ℝ n (fun z : GlideTrack=> ashQ V.cast b z i j) x‖ ≤ C*circleTax σ n * ‖centaur‖^n := by
  exact toast_into (h.2.1 _ _) centaur _ (centR_act _) _
lemma ashCost3 (h : V.fees σ C) (x b i j n) : ‖iteratedFDeriv ℝ n (fun z : GlideTrack=> ashR V.cast b z i j) x‖≤ C *circleTax σ n* ‖cinnamon‖^n := by
  exact toast_into (h.2.2 _ _) cinnamon _ (cinnamon_act _) _
lemma Poster.craft {f : Momentum→CompM α α} (h : Poster σ f) (hp : 0<σ) (x : Track) (i j) : AnalyticAt ℝ (fun u=>f (axes u) i j) x := by
  have hx : AnalyticAt ℂ (fun y=> f y i j) (axes x) := by
    apply formish
    filter_upwards [(Work.F07.stripOpen σ).mem_nhds (Work.F07.realStrip σ hp (axes_real x))] with x hx; exact h.shape hx i j
  exact (hx.contDiffAt (n:=ω)|>.restrict_scalars ℝ|>.comp (f:=axes) x axes_maps.contDiffAt).analyticAt
lemma archiveR {ι : Type} {T : Film ι α α} (h : Play T σ) (hp : 0<σ) (x b i j) : AnalyticAt ℝ (fun z=>ashR T b z i j) x := by
  let F := fun z : Momentum×Momentum => T.arch b b (-z.1) z.1 z.2 i j
  let p := axes x.1; let q:=axes x.2
  have hf : AnalyticAt ℂ F (p,q) := by
    let S := strip (α:=Axis) (σ/2)
    have he : (p,q) ∈ S ×ˢ S := ⟨Work.F07.realStrip _ (by positivity) (axes_real _), Work.F07.realStrip _ (by positivity) (axes_real _)⟩
    apply formish
    filter_upwards [(IsOpen.mem_nhds (show IsOpen (S ×ˢ S) from (Work.F07.stripOpen _).prod (Work.F07.stripOpen _)) he)] with z hz
    let x := z.1; let y:=z.2
    let H w := T.arch b b (w:Momentum×Momentum×Momentum).1 w.2.1 w.2.2 i j
    have hp : DifferentiableAt ℂ H (-x,x,y) := (h.arch b b).shape (duo _ _ hp hz.1 hz.2) i j
    exact hp.comp (f:=fun w : Momentum×Momentum => (-w.1,w.1,w.2)) z (by fun_prop)
  exact (((hf.contDiffAt (n:=ω)).restrict_scalars ℝ).comp (f:=fun z:GlideTrack=> (axes z.1,axes z.2)) x ((axes_maps.comp (f:=Prod.fst) contDiff_fst|>.prodMk (axes_maps.comp contDiff_snd)).contDiffAt)).analyticAt
end YM.Stationary
end

/-!
# Geometry of ball tariffs for derivative-only estimators. May assemble
with no high on-shell predictions. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] {G : Gauge} {P : Patch} {V U : Jar G} {M σ η A D C ζ r ρ μ : ℝ} {T : ι→ℝ} {b : Track} {u v : ℕ}

section balls
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {F Q : ι→ X →CompM α β}
    (R : X→X)
-- including actual contour width, real zeros provided independently

def Patrol (v : ℕ) (r : ℝ) (F : ι→ X→CompM α β) : Prop := ∃ A : ℝ,0≤A ∧ ∀ i a b,
    let g := fun x=>F i x a b
    (∀ x, AnalyticAt ℝ g x) ∧ ∀ x∈closedBall 0 r, ∀ j,j≤v → ‖iteratedFDeriv ℝ j g x‖ ≤ A
namespace Patrol
lemma plus (h : Patrol v r F) (he : Patrol v r Q) : Patrol v r (F+Q) := by
  obtain ⟨A,hA,h⟩ := h; obtain ⟨B,hB,he⟩ := he
  refine ⟨A+B,add_nonneg hA hB,fun i a b=> ⟨fun x=> ((h i a b).1 x).add ((he i a b).1 x),?_⟩⟩
  intro x hx j hj
  change ‖iteratedFDeriv ℝ j ((fun z=>F i z a b)+(fun z=>Q i z a b)) x‖≤_
  rw [iteratedFDeriv_add_apply ((h i a b).1 x|>.contDiffAt) ((he i a b).1 x|>.contDiffAt)]; exact (norm_add_le ..).trans (add_le_add ((h i a b).2 x hx j hj) ((he i a b).2 x hx j hj))
lemma neg (h : Patrol v r F) : Patrol v r (-F) := by
  obtain ⟨A,hA,h⟩ := h; refine ⟨A,hA,fun i a b=> ⟨fun x=> ((h i a b).1 x).neg,?_⟩⟩; intro x hx j hj; change ‖iteratedFDeriv ℝ j (-(fun z=> F i z a b)) x‖ ≤ A; rw [iteratedFDeriv_neg_apply,norm_neg]; exact (h i a b).2 x hx j hj
lemma marries {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] (Y : γ→X→CompM α α) (hg : ∀ i x j k, AnalyticAt ℝ (fun x => Y i x j k) x) (y : ι→γ) (r : ℝ) (v) : Patrol v r (Y ∘ y) := by
  obtain ⟨A,hA,h⟩ := balconyC r v Y (fun i j k x => hg i x j k)
  exact ⟨A,hA,fun i a b=>⟨fun x=> hg _ x a b,fun x hx j hj=> h j hj _ _ _ _ hx⟩⟩
end Patrol

-- estimate band-rays under lens near any center. Estimate n=0..2 uniformly at given T(x) even >Γ-c. local.
lemma sipRay (a b : X) {R : X→ℂ} (h : AnalyticAt ℝ R a) : flareY u (fun t : ℝ=> R (a+t • b))=iteratedFDeriv ℝ u R a (fun _=>b) := by
  let U : ℝ→L[ℝ] X := (ContinuousLinearMap.id ℝ ℝ).smulRight b
  let H y := R (a+y)
  have he : AnalyticAt ℝ H 0 := AnalyticAt.comp (x:=0) (g:=R) (f:=fun y=> a+y) (by rw [add_zero]; exact h) (ContDiffAt.analyticAt (by fun_prop))
  rw [show (fun t : ℝ=> R (a+t • b))=H ∘ U from rfl,flareY, wired U (by rw [map_zero]; exact he),map_zero, show U ∘ (1:Fin u→ℝ)=(fun _=>b) from funext (fun i=>by simp [U])]; unfold H; rw [iteratedFDeriv_comp_add_left,add_zero]
lemma limo_cast (U : ReelF α β) (h : Prick U) (hp : 0≤A) (hr : 0<r) (he : ∀ i j n,n≤ 2 → r^n*‖flareY n (fun z=> U z i j)‖ ≤ A) : Jam r U (fest α β*A) := by
  refine ⟨h,fun n hn => ?_⟩
  have ht : 0 < r^n := pow_pos hr _
  have hh : vflux (jarY n U) ≤ fest α β*(A/r^n) := flux_fest _ (div_nonneg hp ht.le) fun i j=> (le_div_iff₀ ht).2 (by rw [mul_comm]; exact he i j n hn)
  exact (mul_le_mul_of_nonneg_left hh ht.le).trans_eq (by field_simp)
-- uses Patrol and administrative T budgets. degree u≥2. Needs ‖v‖≤1 on glide line, since exactly tangent test.
lemma sipPatrol (h : Patrol u r F) (hu : 2≤u) (hp : 0≤r) (hv : ∀ i a b, Rays u (fun x=>F i x a b)) (a b : ι→X)
    (ht : ∀ i, 0<T i ∧ ‖a i‖ ≤ T i ∧ a i∈closedBall 0 r) (hb : ∀ i,‖b i‖≤1) : Fiesta T (fun i=> T i^u) (fun i t=> F i (a i+t • b i)) := by
  obtain ⟨A,hA,h⟩ := h; refine ⟨fest α β*A,mul_nonneg fest_pos hA,fun i=>⟨(ht i).1.le,pow_nonneg (ht i).1.le _⟩,fun i=>?_⟩; rw [mul_assoc]
  have hi := (ht i).1
  apply limo_cast _ _ (mul_nonneg hA (by positivity)) hi
  · intro x y n hn
    let f z := F i z x y
    obtain ⟨hX,HX⟩ := h i x y
    have hN : n≤u := hn.trans hu
    have hz := dawn (X:=X) (h:=fun x _ => hX x) (f:=f) (hv i x y) hp hA (fun x hx => HX x hx u le_rfl) (a i) (ht i).2.2 n hN
    change T i^n * ‖flareY n (fun t:ℝ => f (a i+t • b i))‖ ≤ _
    rw [sipRay _ _ (hX _)]
    let L := iteratedFDeriv ℝ n f (a i)
    have he : ‖L (fun _=> b i)‖ ≤ A*T i^(u-n) := by
      refine ((L.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)).trans (hz.trans ?_)
      · simp only [prod_const,card_univ,Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) (hb i)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ht i).2.1 _) hA
    exact (mul_le_mul_of_nonneg_left he (pow_nonneg hi.le _)).trans_eq (by rw [mul_left_comm, ← pow_add,Nat.add_sub_of_le hN])
  intro x y; refine (ContDiffAt.comp (g:= fun z => F i z x y) (f:=fun t : ℝ => a i+t • b i) _ ((h _ _ _).1 _ |>.contDiffAt) (by fun_prop)).analyticAt
-- need u=1 or 0, bounds n≥u with T≤κ; all ≤2 and budget for any u'≤. general.
lemma sipLight (h : Patrol 2 r F) (hu : u≤2) (hC : 0≤ C) (hp : 0≤r) (hv : ∀ i a b,Rays u (fun x=>F i x a b)) (a b : ι→X) (ht : ∀ i,0<T i ∧ ‖a i‖≤T i ∧ a i∈closedBall 0 r ∧ T i≤C) (hb : ∀ i,‖b i‖≤1) : Fiesta T (fun i=> T i^u) (fun i t=>F i (a i+t • b i)) := by
  obtain ⟨A,hA,h⟩ := h; let K := (1+C)^2
  have hk : 1 ≤ K := one_le_pow₀ (by linarith)
  refine ⟨fest α β*(A*K),mul_nonneg fest_pos (by positivity),fun i=> ⟨(ht i).1.le,pow_nonneg (ht i).1.le _⟩,fun i=>?_⟩; rw [mul_assoc]; have hI:= (ht i).1
  apply limo_cast _ _ (by positivity) hI
  · intro x y n hn; let f z:= F i z x y
    let L := iteratedFDeriv ℝ n f (a i)
    obtain ⟨hX,HX⟩ := h i x y
    have he : ‖flareY n (fun t:ℝ=> f (a i+t • b i))‖≤‖L‖ := by rw [sipRay _ _ (hX _)]; exact (L.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (by simpa using pow_le_one₀ (norm_nonneg _) (hb i) (n:=n)))
    apply (mul_le_mul_of_nonneg_left he (pow_nonneg hI.le n)).trans
    rcases le_total u n with hU|hU
    · have hp' := HX _ (ht i).2.2.1 n hn
      calc
       T i^n*‖L‖ ≤ T i^n*A := mul_le_mul_of_nonneg_left hp' (pow_nonneg hI.le n)
       _ = (A * T i^(n-u)) * T i^u := by rw [mul_assoc, ← pow_add,Nat.sub_add_cancel hU,mul_comm]
       _ ≤ _ := by
         have hy := pow_le_pow_left₀ hI.le (show T i≤1+C by linarith [(ht i).2.2.2]) (n-u)
         have hb : (1+C)^(n-u)≤K := pow_le_pow_right₀ (by linarith) (by omega : n-u ≤ 2)
         exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hy.trans hb) hA) (by positivity)
    have hz := dawn (X:=X) (f:=f) (h:=fun x _ => hX x) (hv i x y) hp hA (fun x hx => HX x hx u hu) (a i) (ht i).2.2.1 n hU
    calc
     _ ≤ T i^n *(A*T i^(u-n)) := mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ht i).2.1 _) hA)) (pow_nonneg hI.le _)
     _ ≤ _ := by rw [mul_left_comm,← pow_add,Nat.add_sub_of_le hU]; gcongr; exact le_mul_of_one_le_right hA hk
  intro x y; exact (ContDiffAt.comp (g:=fun z => F i z x y) (f:=fun t:ℝ=>a i+t • b i) _ ((h i x y).1 _|>.contDiffAt) (by fun_prop)).analyticAt
end balls
end YM.Stationary
end
