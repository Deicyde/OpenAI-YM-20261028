import YM.RG08.Dew.Leaf

/-!
# Counting-basis covariance gives heat moments with true factor of two

Γ positive OR arbitrary Γ giving slope. An identity of polynomial operators on
ANY E-valued ambient with linear push (next module). Not inferring that
physical measure admits all derivative exchanges. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG PertExtension PertExtension.Series GaussianScore Stationary Tensor
open Lattice Wilson Filter MeasureTheory Analysis Function Finset Matrix
open scoped Topology ContDiff Classical
variable {X : Type} {k n : ℕ} [Fintype X]
local notation "E" => X → ℝ
private def paidR (M : Matrix X X ℝ) : E →ₗ[ℝ] Module.Dual ℝ E := LinearMap.mk₂ ℝ (fun x y=> (M*ᵥ x) ⬝ᵥ y) (fun _ _ _=> by rw [Matrix.mulVec_add,add_dotProduct]) (fun _ _ _=> by rw [Matrix.mulVec_smul,smul_dotProduct]) (fun _ _ _=> by rw [dotProduct_add]) (fun _ _ _=> by rw [dotProduct_smul])
private lemma paid_smooth (M : Matrix X X ℝ) : ContDiff ℝ ω (fun x : E=> paidR M x x) := by
  change ContDiff ℝ ω (fun x => dotProduct (M *ᵥ x) x)
  unfold dotProduct Matrix.mulVec dotProduct; exact ContDiff.sum fun i _=> ((ContDiff.sum fun j _=> contDiff_const.mul (contDiff_apply ℝ ℝ j)).mul (contDiff_apply ℝ ℝ i))
private lemma pay_min {M : Matrix X X ℝ} (h : PosDef M) : ∃ c>0,∀ x:E,c*‖x‖^2≤paidR M x x/2 := by
  let f : E → ℝ := fun x => paidR M x x/2
  have he : Hemi 2 f := start_hemi ((paid_smooth M).div_const 2|>.contDiffAt|>.analyticAt) fun x t=> by unfold f; rw [map_smul,map_smul, LinearMap.smul_apply]; simp only [smul_eq_mul]; ring
  have hx : PertExtension.Series.Radial.jet f 2= f := by
    obtain ⟨F,hF,hE⟩:=he
    rw [hE]; ext x
    rw [show PertExtension.Series.Radial.jet _ _ x=Tensor.diagonal (Tensor.coeff (Tensor.diagonal F) 2 0) x from ?_,coeff_at_diagonal F hF]; rfl
  change ∃ c>0,∀ x:E,c*‖x‖^2≤f x; nth_rw 1 [← hx]; apply PertExtension.Series.Radial.quadratic_min
  intro u hu
  rw [hx]; unfold f
  apply div_pos _ (by norm_num); change 0 < M*ᵥ u ⬝ᵥ u; rw [dotProduct_comm]
  exact h.dotProduct_mulVec_pos hu

def crownM {M : Matrix X X ℝ} (h : PosDef M) : Law E where
  P:=paidR M
  slope := pay_min h
  turns := fun x y=> by change M*ᵥ x ⬝ᵥ y=M*ᵥ y ⬝ᵥ x; rw [dotProduct_comm _ y,Matrix.dotProduct_mulVec,show y ᵥ* M= M*ᵥ y from ((show y ᵥ* M = y ᵥ* Mᵀ by rw [show Mᵀ=M from h.isHermitian.eq]).trans (vecMul_transpose ..))]
  smooth := (paid_smooth M).continuous

variable [DecidableEq X]
variable {M : Matrix X X ℝ} (h : PosDef M)
include h
private lemma tariff (i : X) (x : E) : paidR M (M⁻¹ *ᵥ zpk i) x = x i := by
  have hh := h.isUnit
  change ((M*ᵥ(M⁻¹ *ᵥ zpk i)) ⬝ᵥ x)= _; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hh), one_mulVec]; simp [dotProduct,zpk,Pi.single_apply,ite_mul]

variable (μ : Measure (X→ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant]
omit [DecidableEq X] [μ.IsAddRightInvariant] in
lemma sun_add {F H : Psalm X} (hf : Grass F) (he : Grass H) : (crownM h).average μ (F+H)= (crownM h).average μ F+(crownM h).average μ H := by
  unfold Law.average; rw [add_mul]; simp only [integral_add ((crownM h).integrable_entry μ hf.invoiced hf.smooth.continuous) ((crownM h).integrable_entry μ he.invoiced he.smooth.continuous),Pi.add_apply,add_div]
omit [DecidableEq X] [μ.IsAddRightInvariant] [μ.HasTemperateGrowth] in
lemma sun_stem (t : ℝ) (F : Psalm X) : (crownM h).average μ (t • F)= t* (crownM h).average μ F := by
  unfold Law.average; change (∫ x, t*F x * (crownM h).kern x ∂μ)/_=t*_ ; simp_rw [mul_assoc]; rw [integral_const_mul]; simp only [Pi.mul_apply]; ring
omit [DecidableEq X] [μ.IsAddRightInvariant] in
lemma sun_list {I : Type} {s : Finset I} {F : I→Psalm X} (hf : ∀ i∈s, Grass (F i)) : (crownM h).average μ (∑ i∈s,F i)=∑ i∈s,(crownM h).average μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Law.average]
  | insert i s hi ih =>
    have hv j hj:= hf j (mem_insert_of_mem (s:=s) hj)
    rw [sum_insert hi,sum_insert hi,sun_add h μ (hf i (mem_insert_self ..)) (Grass.list hv),ih hv]

omit [DecidableEq X] in
private lemma ibp (i : X) {F : Psalm X} (hf : Grass F) {v : E} (hV : ∀ x, (crownM h).P v x = x i) (hx : Grass (Analysis.D v F)) :
    (crownM h).average μ (Analysis.D v F)=(crownM h).average μ (fun x=>F x*x i) := by
  let P := crownM h
  have he x t : HasDerivAt (fun r : ℝ => F (x+r•v)) ((Analysis.D v F) (x+t•v)) t := by
    apply ((hf.smooth.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t -- defeq D?
    have ht : HasDerivAt (fun r : ℝ=> r • v) v t := by simpa using! (hasDerivAt_id' t).smul_const v
    exact ht.const_add x
  have hw := P.translation_lemma v hf.invoiced hf.smooth.continuous hx.invoiced hx.smooth.continuous he μ
  let L := Analysis.D v F
  have hh : Integrable (L*P.kern) μ := P.integrable_entry μ hx.invoiced hx.smooth.continuous
  have hu : Integrable ((F*(fun x => P.P v x))*P.kern) μ := P.integrable_entry μ (hf.invoiced.mul (Law.linearInvoice ..)) (hf.smooth.continuous.mul ((P.P v).continuous_of_finiteDimensional))
  rw [_root_.sub_mul] at hw
  have hz := integral_sub (μ:=μ) hh hu
  change ∫ a, (L*P.kern-(F*(fun x => P.P v x))*P.kern) a ∂μ=_ at hz
  unfold Law.average; congr 1
  rw [show (fun x=>(F x)*(x i))=F*(fun x => P.P v x) from funext fun x=> by simp only [Pi.mul_apply];exact congr_arg (F x*·) (hV x).symm]
  exact sub_eq_zero.mp (hz.symm.trans hw)
omit [DecidableEq X] h in
private lemma cropG (F : Psalm X) (v : E) (hF : Hemi k F) : Grass (Analysis.D v F) := by
  cases k with
  | zero => rw [hF.dry_zero]; exact Grass.const 0
  | succ k => exact Grass.base (hF.lower v)
omit h in
private lemma dotsV (x : E) : x=∑ i, x i • zpk i := funext fun i=> by rw [Finset.sum_apply]; simp [zpk,Pi.single_apply,mul_ite]

theorem wake_even (F : Psalm X) (hp : Hemi k F) :
    k*(crownM h).average μ F=2*(crownM h).average μ (lap M⁻¹ F) := by
  let v i := M⁻¹*ᵥ zpk i; let f i:=Analysis.D (zpk i) F
  have hs : (k:ℝ) • F=∑ i,f i * fun x:E=>x i := by
    funext x
    have ht : ((k:ℝ) • F x) = Analysis.D x F x := by obtain ⟨A,hA,rfl⟩:=hp; exact (Tensor.Euler A hA x).symm
    rw [Pi.smul_apply,ht, Analysis.D];
    have he := congr_arg (fderiv ℝ F x) (dotsV x)
    simp only [map_sum,map_smul] at he
    rw [show (fderiv ℝ F x) x= _ from he,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
  have hi i j : v i j=M⁻¹ i j := by
    calc
      _ = M⁻¹ j i := by unfold v Matrix.mulVec dotProduct zpk; simp [Pi.single_apply,mul_ite]
      _ = _ := congr_fun (congr_fun (show (M⁻¹)ᵀ=M⁻¹ from h.inv.isHermitian.eq) i) j
  have Hf i : Grass (f i) := cropG F _ hp
  have hx i : Grass (fun x : E=> x i) := Grass.base (start_hemi (k:=1)
      (show AnalyticAt ℝ (fun x:E=> x i) 0 from (contDiff_apply ℝ ℝ i).contDiffAt (n:=ω)|>.analyticAt) (fun x v=> by simp))
  have hq i v : Grass (Analysis.D v (f i)) := by
    cases k with
    | zero=> rw [show f i=0 from hp.dry_zero _]; exact Grass.base (show Hemi 0 _ from by rw [(show Hemi 0 (0:Psalm X) from Hemi.const 0).dry_zero]; exact Hemi.const 0)
    | succ k=> exact cropG _ _ (hp.lower _)
  have he i : (crownM h).average μ (f i*fun x:E=>x i)=(crownM h).average μ (Analysis.D (v i) (f i)) := Eq.symm (ibp h μ _ (Hf i) (tariff h i) (hq i _))
  rw [← sun_stem, hs,sun_list h μ (fun i _=> (Hf i).times (hx i))]; simp_rw [he]
  rw [← sun_list h μ (fun i _=>hq i (v i))]
  have hx i (u : E) : Analysis.D (v i) (f i) u=∑ j,M⁻¹ i j* D (zpk j) (f i) u := by
    unfold Analysis.D; conv_lhs => arg 2; rw [dotsV (v i)];
    simp_rw [map_sum,map_smul,hi]; rfl
  rw [show (∑ i,Analysis.D (v i) (f i))=(2:ℝ) • lap M⁻¹ F by
    funext x; rw [Finset.sum_apply]; simp_rw [hx]; unfold lap; simp; unfold f; ring, sun_stem]
end YM.RG08
