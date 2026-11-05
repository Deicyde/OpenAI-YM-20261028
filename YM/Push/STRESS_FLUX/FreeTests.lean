import YM.Push.STRESS_FLUX.Lift
import YM.Push.STRESS_FLUX.Pairing
import YM.Work.B06


/-! Rank and normalization tests at fixed weight, arity and position in the exact
`Climb.Bel`. This argument doesn't need classification of free nulls in general, or to
postulate MaxwellData with stress of a specific form for these calculations. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Set Filter Gauge Maxwell Analysis Table Labels Climb
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff

variable {G : Gauge} {L : Register G} {S : Table L}

def quad {n : ℕ} (S : Table L) (x : Points n) (v : Fin n → S.Field 4) := S.useAt S x (fun i => ⟨4,v i⟩)

lemma free_polynomials {n : ℕ} {x : Points n} (hx : x ∈ conf _) (p : Fin n → Label G 4) :
    quad (Bel L) x (fun i => fromPol (Bel L) (p i)) = Wick.moment G x (fun i => reduceEq (p i).val) := by
  rw [quad,show (fun i => (⟨4,fromPol (Bel L) (p i)⟩ : (Bel L).Tag)) =
      (Bel L).classTokens ∘ (fun i => (⟨4,(L.coord 4).coords (p i)⟩ : (standard L.grid).Token)) from rfl,
    Table.at_project _ _ (table_sym L.grid) (fun _ => le_rfl) hx,decodes]
  simp [Register.coord]; rfl

abbrev oneStress (S : Table L) (J : S.Stress) := fun (x : Points 1) (a b : Axis) => quad S x (fun _ => J a b)

lemma oneStress_formula (w : Coeff) (a b : Axis) (x : Points 1) : oneStress (Bel L) (material (Bel L) w) x a b =
    if a=b then (w 0:ℂ) else (0:ℂ) := by
  have he (p) := free_polynomials (L:=L) (x:=x) (show x∈ conf _ from fun _ _ _ => Subsingleton.elim ..) (fun _ => p)
  unfold oneStress material; rw [he, ← onePoint_at, stress_of]; split <;> simp [vacuum_pair,Labels.unit,
    show ∀ a : ℝ, ∀ x : Pol G, reduceEq (a • x) = a • reduceEq x from fun a x => (reduceEq.toLinearMap.restrictScalars ℝ).map_smul a x,
    show ∀ a : ℝ, ∀ z : WickPol G, onePoint x (a • z) = a • onePoint x z from fun a z => ((onePoint x).restrictScalars ℝ).map_smul a z,
    show onePoint (G:=G) x 1=1 by rw [onePoint_at,Wick.constants]]

def axisLine (z : E4) := points ![z,0]
lemma axisLine_in {z : E4} (hz : z ≠ 0) : axisLine z ∈ conf _ := by
  intro i j h; change ![z, (0:E4)] i = ![z,0] j at h
  fin_cases i <;> fin_cases j <;> simp_all

private def data (w : Coeff) (a b : Axis) (f : Axis → Axis → Axis → Axis → ℝ) :=
    if a=b then w 1 * (∑ i, f a i a i) + w 2 * (∑ i, ∑ j, f i j i j) else w 3 * ∑ i, f a i b i

def signal (L : Register G) (w : Coeff) (p q r s a b : Axis) (z : E4) := quad (Bel L) (axisLine z)
  ![material (Bel L) w a b,fromPol (Bel L) (pair G p q r s)]
lemma signal_formula (w : Coeff) {z : E4} (hz : z ≠ 0) (p q r s a b : Axis) : signal L w p q r s a b z =
    ((G.lieDim * data w a b (fun i j k l => chains z i j k l p q r s) : ℝ) : ℂ) := by
  let x := axisLine z
  let Q := reduceEq (pair G p q r s).val
  let f := (![stress G w a b,pair G p q r s] : Fin 2 → Label G 4)
  have ht : signal L w p q r s a b z = head x Q (reduceEq (stress G w a b).val) := by
    rw [signal,show (![material (Bel L) w a b,fromPol (Bel L) (pair G p q r s)] : Fin 2 → _) = fun i => fromPol (Bel L) (f i) from
      funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩),free_polynomials (axisLine_in hz), head_at]; congr! 1; exact funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
  have hx1 : Points.tail x ∈ conf _ := Points.tail_in (axisLine_in hz)
  have h1 : head x Q 1 = 0 := by
    have he := Wick.adjoin hx1 (x 0) (![Q] : Fin 1 → WickPol G)
    rw [show Points.cons (x 0) (Points.tail x) = x by ext1 i; fin_cases i <;> rfl] at he
    rw [head_at, show (![1,Q] : Fin 2 → WickPol G) = Fin.cons (α:=fun _ => WickPol G) 1 (![Q] : Fin 1 → WickPol G) from rfl, ← he]
    rw [Matrix.vec_single_eq_const, ← onePoint_at]; exact vacuum_pair ..
  have he (a b i j : Axis) : head x Q (reduceEq (pair G a b i j).val) = G.lieDim * (chains z a b i j p q r s : ℂ) := by
    unfold Q; rw [chains_read G (show x 0 ≠ x 1 from hz),show x 0 - x 1=z from sub_zero _]
  rw [ht,stress_of]; dsimp only [data]; split <;>
    simp [he,Labels.unit,h1,
      show ∀ a : ℝ, ∀ y : Pol G, reduceEq (a • y) = a • reduceEq y from fun a y => (reduceEq.toLinearMap.restrictScalars ℝ).map_smul a y,
      show ∀ a : ℝ, ∀ y : WickPol G, head x Q (a • y) = a • head x Q y from fun a y => ((head x Q).restrictScalars ℝ).map_smul a y,
      Complex.real_smul, ← Finset.mul_sum, mul_left_comm, mul_add]

private abbrev base := basis (0:Axis)
lemma base_ne : base ≠ 0 := by intro h; simpa using congr_arg (fun x : E4 => x 0) h
private def hess (i j : Axis) := Maxwell.grad i (Maxwell.grad j Green)
private lemma hbase (i j : Axis) : hess i j base = -2*normal*basis i j + 8*normal*(base i * base j) := by
  rw [hess, second_Green base_ne]; simp
private lemma dhbase (k i j : Axis) : Maxwell.grad k (hess i j) base =
    8*normal*(basis i j * base k + basis k i * base j + base i * basis k j) - 48*normal*(base i * base j * base k) := by
  let A := fun x : E4 => (‖x‖^2)⁻¹
  have hA := (hasFDerivAt_inv (show ‖base‖^2 ≠ 0 by simp)).comp base (hasStrictFDerivAt_norm_sq base).hasFDerivAt
  have ht := (((hA.pow 2).const_mul (-2*normal*basis i j)).add ((((Maxwell.compAxis i).hasFDerivAt.mul (Maxwell.compAxis j).hasFDerivAt).const_mul (8*normal)).mul (hA.pow 3)))
  change HasFDerivAt (fun z => -2*normal*basis i j * A z^2 + 8*normal*(z i*z j)*A z^3) _ _ at ht
  have he : hess i j =ᶠ[𝓝 base] (fun z => -2*normal*basis i j * A z^2 + 8*normal*(z i*z j)*A z^3) := by
    filter_upwards [open_away.mem_nhds (show base∈away from base_ne)] with z hz
    exact second_Green hz j i
  rw [Maxwell.grad, Analysis.GermD _ he, D,ht.fderiv]
  have hzero : basis k 0 = base k := by simp [eq_comm]
  simp [-basis_eq,innerSL_apply_apply,hzero]; ring

private def hcurl (A : Axis → Axis → ℝ) (a b k m : Axis) :=
    ((if k=b then A a m else 0) - (if m=b then A a k else 0)) - ((if k=a then A b m else 0) - (if m=a then A b k else 0))
private lemma bare_eq {x : E4} (hx : x ≠ 0) (a b k m : Axis) : bareCurl a b k m x = hcurl (fun i j => hess i j x) a b k m := by
  simp only [bareCurl,Pi.sub_apply,Bare.opp_grad hx]; rfl
private lemma dbare_eq {x : E4} (hx : x ≠ 0) (u a b k m : Axis) : Maxwell.grad u (bareCurl a b k m) x = hcurl (fun i j => Maxwell.grad u (hess i j) x) a b k m := by
  have ht : bareCurl a b k m =ᶠ[𝓝 x] fun z => hcurl (fun i j => hess i j z) a b k m := by
    filter_upwards [open_away.mem_nhds (show x∈away from hx)] with z hz; exact bare_eq hz ..
  have hi (a b) : DifferentiableAt ℝ (hess a b) x := (HessSmooth hx _ _).differentiableAt (by simp)
  have hs := differentiableAt_const (𝕜:=ℝ) (x:=x) (0:ℝ)
  rw [Maxwell.grad,GermD _ ht]; unfold hcurl D; split_ifs <;> simp only [fderiv_fun_sub, hi,hi _ _ |>.fun_sub, hs, hs.fun_sub,
    fderiv_const_apply, sub_apply, _root_.zero_apply]

private def dchain (x : E4) (u a b c d i j k l : Axis) :=
    Maxwell.grad u (bareCurl c d k l) x * bareCurl a b i j x + Maxwell.grad u (bareCurl a b i j) x * bareCurl c d k l x +
    Maxwell.grad u (bareCurl c d i j) x * bareCurl a b k l x + Maxwell.grad u (bareCurl a b k l) x * bareCurl c d i j x
private lemma chains_diff {x : E4} (hx : x ≠ 0) (a b c d i j k l : Axis) : DifferentiableAt ℝ (fun z => chains z a b c d i j k l) x :=
  let h a b c d := (Bare.curl_diff hx a b c d).differentiableAt (by simp)
  ((h a b i j).mul (h c d k l)).add ((h a b k l).mul (h c d i j))
private lemma chains_D {x : E4} (hx : x ≠ 0) (u a b c d i j k l : Axis) : Maxwell.grad u (fun z => chains z a b c d i j k l) x = dchain x u a b c d i j k l := by
  have h a b c d := (Bare.curl_diff hx a b c d).differentiableAt (by simp)
  unfold chains dchain Maxwell.grad D
  rw [fderiv_fun_add ((h ..).fun_mul (h ..)) ((h ..).fun_mul (h ..)), fderiv_fun_mul (h ..) (h ..),fderiv_fun_mul (h ..) (h ..)]; simp only [add_apply, smul_apply,smul_eq_mul]; ring

private lemma grad_data {x : E4} (u : Axis) (w : Coeff) (a b : Axis) (Y : Axis → Axis → Axis → Axis → E4 → ℝ)
    (h : ∀ i j k l, DifferentiableAt ℝ (Y i j k l) x) :
    let f := fun z => data w a b (fun i j k l => Y i j k l z)
    DifferentiableAt ℝ f x ∧ Maxwell.grad u f x = data w a b (fun i j k l => Maxwell.grad u (Y i j k l) x) := by
  dsimp only [data]
  split_ifs
  · have he i : DifferentiableAt ℝ (fun z => ∑ j, Y i j i j z) x := DifferentiableAt.fun_sum fun _ _ => h ..
    have ht : DifferentiableAt ℝ (fun z => ∑ i, ∑ j, Y i j i j z) x := DifferentiableAt.fun_sum fun _ _ => he _
    refine ⟨((he _).const_mul _).add (ht.const_mul _), ?_⟩
    unfold Maxwell.grad D
    rw [fderiv_fun_add ((he _).const_mul _) (ht.const_mul _), fderiv_fun_mul (differentiableAt_const _) (he _), fderiv_fun_mul (differentiableAt_const _) ht]
    simp_rw [fderiv_fun_sum (u:=Finset.univ) (fun i _ => he i), fderiv_fun_sum (u:=Finset.univ) (fun _ _ => h _ _ _ _)]
    simp [sum_apply]
  have he := DifferentiableAt.fun_sum (u:=Finset.univ) (fun i _ => h a i b i)
  refine ⟨he.const_mul _,?_⟩
  unfold Maxwell.grad D
  rw [fderiv_fun_mul (differentiableAt_const _) he, fderiv_fun_sum (fun _ _ => h ..)]; simp [sum_apply]

lemma signal_grad (w : Coeff) (u i j k l a b : Axis) : Maxwell.grad u (signal L w i j k l a b) base =
    (↑((G.lieDim:ℝ)*data w a b (fun p q r s => dchain base u p q r s i j k l)) : ℂ) := by
  let Y (z : E4) := data w a b (fun p q r s => chains z p q r s i j k l)
  have he : signal L w i j k l a b =ᶠ[𝓝 base] fun z => (↑(G.lieDim * Y z : ℝ) : ℂ) := by
    filter_upwards [open_away.mem_nhds (show base∈away from base_ne)] with z hz; exact signal_formula w hz ..
  obtain ⟨ht,hq⟩ := grad_data u w a b (fun p q r s z => chains z p q r s i j k l) (fun _ _ _ _ => chains_diff base_ne ..)
  change Maxwell.grad u Y base = _ at hq; simp_rw [chains_D base_ne] at hq
  rw [Maxwell.grad,GermD _ he]; unfold D
  simp_rw [Complex.ofReal_mul]
  rw [show (fun z => (↑(↑G.lieDim:ℝ):ℂ)*(Y z:ℂ))=(((G.lieDim:ℝ) • Complex.ofRealCLM) ∘ Y) by ext1 z; simp [Complex.real_smul]]
  change fderiv ℝ (((G.lieDim:ℝ) • Complex.ofRealCLM) ∘ Y) base (basis u) = _
  rw [fderiv_comp base (ContinuousLinearMap.differentiableAt _) ht,ContinuousLinearMap.fderiv];
  change (G.lieDim:ℝ) • (↑(Maxwell.grad u Y base) : ℂ) = _
  rw [hq,Complex.real_smul]

private def factor (G : Gauge) : ℝ := G.lieDim * normal^2
lemma factor_ne (H : G.Simple) : factor G ≠ 0 := by
  haveI := H.nontrivial_color
  have he : G.lieDim ≠ 0 := by rw [lieDim, ← G.colorIso.finrank_eq]; exact Module.finrank_pos.ne'
  exact mul_ne_zero (by exact_mod_cast he) (pow_ne_zero _ normal_pos.ne')

set_option maxRecDepth 4000 in
lemma vacuum_tests (w : Coeff) :
    signal L w 0 1 0 1 0 0 base = (↑(factor G * (32 * w 1 + 64*w 2)) : ℂ) ∧
    signal L w 1 2 1 2 0 0 base = (↑(factor G * (64*w 2)) : ℂ) ∧
    signal L w 0 2 1 2 0 1 base = (↑(factor G * (-16*w 3)) : ℂ) := by
  simp only [signal_formula w base_ne, factor]
  simp only [Fin.sum_univ_four,data]
  simp +decide only [reduceIte]
  simp_rw [chains, bare_eq base_ne,hcurl,hbase]
  simp +decide only [basis_eq,reduceIte,mul_zero,mul_one,sub_zero,sub_self,add_zero,zero_add,
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_pow,
    Complex.ofReal_zero,Complex.ofReal_neg, Complex.ofReal_ofNat]
  constructor; ring
  constructor <;> ring

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4000 in
lemma divergence_tests (w : Coeff) :
    (∑ a, Maxwell.grad a (signal L w 0 1 0 1 a 0) base) = (↑(factor G * (-256*w 1 -512*w 2+128*w 3)) : ℂ) ∧
    (∑ a, Maxwell.grad a (signal L w 1 2 1 2 a 0) base) = (↑(factor G * (-512*w 2 -128*w 3)) : ℂ) := by
  simp only [signal_grad, factor]
  simp only [Fin.sum_univ_four,data]
  simp +decide only [reduceIte]
  simp_rw [dchain,dbare_eq base_ne,bare_eq base_ne,hcurl,hbase,dhbase]
  simp +decide only [basis_eq,reduceIte,mul_zero,zero_mul,mul_one,sub_zero,sub_self,add_zero,zero_add,
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_pow,
    Complex.ofReal_one,Complex.ofReal_zero,Complex.ofReal_neg, Complex.ofReal_ofNat]
  constructor <;> ring

lemma div_kernel (H : G.Simple) (w : Coeff) (hc : w 0 = 0)
    (hd : ∀ (i j : Axis), (∑ a, Maxwell.grad a (signal L w i j i j a 0) base) = 0) : w = w 3 • weyl := by
  obtain ⟨h₁,h₂⟩ := divergence_tests (L:=L) w
  rw [hd] at h₁ h₂
  have he : -512*w 2 - 128*w 3 = 0 := (mul_eq_zero.mp (Complex.ofReal_eq_zero.mp h₂.symm)).resolve_left (factor_ne H)
  have ht : -256*w 1 -512*w 2+128*w 3 = 0 := (mul_eq_zero.mp (Complex.ofReal_eq_zero.mp h₁.symm)).resolve_left (factor_ne H)
  ext1 i
  fin_cases i <;> simp [hc,weyl] <;> linarith

lemma quad_test_zero (v : (Bel L).Field 4) (z : E4) : quad (Bel L) (axisLine z) ![0,v] = 0 :=
  ((Bel L).classMoment _ _ _).map_coord_zero 0 rfl
lemma oneStress_zero (S : Table L) (x a b) : oneStress S 0 x a b = 0 :=
  (S.classMoment _ _ _).map_coord_zero (0:Fin 1) rfl

theorem free_stress_inj (H : G.Simple) : Injective (material (Bel L)) := by
  have hv (w : Coeff) (hz : material (Bel L) w = 0) : w=0 := by
    have hc : (↑(w 0) : ℂ) = 0 := by
      have he := oneStress_formula (L:=L) w 0 0 0
      rw [hz, if_pos rfl, oneStress_zero] at he; exact he.symm
    have he (p q r s a b : Axis) : signal L w p q r s a b base = 0 := by rw [signal,hz]; exact quad_test_zero ..
    obtain ⟨h1,h2,h3⟩ := vacuum_tests (L:=L) w
    rw [he] at h1 h2 h3
    have hf {r : ℝ} (he : ↑(factor G * r) = (0:ℂ)) : r=0 := (mul_eq_zero.mp (Complex.ofReal_eq_zero.mp he)).resolve_left (factor_ne H)
    ext1 i; change w i = 0; fin_cases i
    · exact Complex.ofReal_eq_zero.mp hc
    · change w 1=0
      linarith [hf h1.symm,hf h2.symm]
    · change w 2=0; linarith [hf h2.symm]
    change w 3=0
    all_goals linarith [hf h1.symm,hf h2.symm,hf h3.symm]
  intro v w he
  suffices ht : v-w=0 from sub_eq_zero.mp ht
  exact hv (v-w) (funext fun a => funext fun b => by simpa [material] using (sub_eq_zero.mpr (congr_fun (congr_fun he a) b)))

lemma bij_of_inj {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {A : V →ₗ[ℝ] W} (h : Injective A) (he : Module.finrank ℝ W ≤ Module.finrank ℝ V) : Bijective A :=
  ⟨h, LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (Submodule.finrank_le _ |>.antisymm ((LinearMap.finrank_range_of_inj h).symm ▸ he)))⟩

theorem free_stress_bij (H : G.Simple) (A : (Bel L).RealSpin) : Bijective (tableStress A) := by
  refine bij_of_inj (fun x y hh => free_stress_inj (L:=L) H (congr_arg Subtype.val hh)) ?_
  rw [Module.finrank_fin_fun]; exact dim_four H A

theorem labelStress_onto (H : G.Simple) : Surjective (labelStress (G:=G)) := by
  let L := Maxwell.standard (Labels.frames G)
  have ht : Function.Injective (labelStress (G:=G)) := fun x y hh => free_stress_inj (L:=L) H
    (funext fun a => funext fun b => congr_arg (fun v : RawTwo G => fromPol (Bel L) (v.val a b)) hh)
  haveI : FiniteDimensional ℝ (Label G 4) := Module.Finite.trans ℂ _
  refine (bij_of_inj (V:=Coeff) (W:=↥(RawTwo G)) (A:=labelStress) ht ?_).2
  rw [Module.finrank_fin_fun]; exact finrank_two H

theorem stress_bijective {H : S.RealSpin} {A : (Bel L).RealSpin} (h : G.Simple) (U : Spin.change S 4) (hz : Spin.realH H A U) :
    Bijective (tableStress H) := by
  have ht : Module.finrank ℝ (TableTwo H) = 4 := dim_four_eq h U hz (by
    rw [← (LinearEquiv.ofBijective (tableStress A) (free_stress_bij h A)).finrank_eq,Module.finrank_fin_fun])
  have ho := (tensorProjection_onto H).comp (labelStress_onto (G:=G) h)
  change Surjective (tableStress H) at ho
  have he := LinearMap.finrank_range_add_finrank_ker (K:=ℝ) (V:=Coeff) (V₂:=↥(TableTwo H)) (tableStress H)
  rw [LinearMap.range_eq_top.mpr ho,finrank_top,Module.finrank_fin_fun, ht, Nat.add_eq_left] at he
  exact ⟨(LinearMap.ker_eq_bot (R:=ℝ) (R₂:=ℝ) (M:=Coeff) (M₂:=↥(TableTwo H)) (f:=tableStress H)).mp ((Submodule.finrank_eq_zero (R:=ℝ) (M:=Coeff)).mp he),ho⟩
end YM.StressFlux
