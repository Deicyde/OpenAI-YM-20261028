import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment


/-!
# Pass repeated actual critical station invoice --- same paths/t/d

 including its real thermal subtractions. Here exact Match field up to 4;
 inflation then uses the canonical chart, including zeroth. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Set Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Further.PhysicalPeriodLimitF933 Gauge Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Matrix Finset
open Push Push.Uniform Shingle Pitch Extra.Iteration Extra.Iteration.Calibration Bid
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c C f F : Side} {P : Patch} {Z : KernelChoices} {T : RG.Stage} {n : ℕ}
    {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} (hC : C.val=c.val*n) (h₂ : 2 ≤ c.val)

lemma critical_single {S : StepData c f} {U : Forest S.ratio} {A E : Dir G c→ AxisChart G U} {p : Clip} {R : PathData G}
    (u : S.Choices) (hp : Critical U p R A) (ht : Critical U p R E) {η : ℝ} (hη : 0<η) (hR : PriceGap U p R η): A=ᶠ[𝓝 0] E := by
  apply Work.F05.station_unique (F:=tested U u p R) (hp.2.2 u).1 (fun i hi=> by
    by_contra h; exact (Work.F05.tested_diag hη hR u i h).ne' hi)
    (hp.1 ▸ hp.2.1.continuousAt.tendsto) (ht.1 ▸ ht.2.1.continuousAt.tendsto)
    (((hp.2.2 u).2).mono fun _ h=>h.fderiv) (((ht.2.2 u).2).mono fun _ h=>h.fderiv)

section A
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
lemma jet_liner (Q : X→L[ℝ] Y) (F : Y→ℝ) (h : ContDiffAt ℝ ω F 0) (k : ℕ) : iteratedFDeriv ℝ k (F ∘ Q) 0=(iteratedFDeriv ℝ k F 0).compContinuousLinearMap (fun _=> Q) := by rw [WardBin.Lies.liner _ (by rw [map_zero]; exact h.of_le le_top),map_zero]
lemma compensate {a : X→ℝ} {b : Y→ℝ} (Q : X→L[ℝ] Y) {ε : ℝ} (he : b ∘ Q=ᶠ[𝓝 0] ε • a) (hh : ε≠ 0) (hb : ContDiffAt ℝ ω b 0) : ContDiffAt ℝ ω a 0 ∧ ∀ k : ℕ,
    iteratedFDeriv ℝ k (b ∘ Q) 0=ε • iteratedFDeriv ℝ k a 0 := by
  have h : ContDiffAt ℝ ω b (Q 0) := map_zero Q ▸ hb
  have ht := h.comp (f:=Q) 0 Q.contDiff.contDiffAt
  have hf : ContDiffAt ℝ ω a 0 := (ht.congr_of_eventuallyEq he.symm).const_smul ε⁻¹ |> fun h=> by change ContDiffAt ℝ ω (ε⁻¹ • ε • a) 0 at h; rwa [smul_smul,inv_mul_cancel₀ hh,one_smul] at h
  exact ⟨hf, fun k=>by rw [(he.iteratedFDeriv ℝ k).eq_of_nhds,iteratedFDeriv_const_smul_apply (hf.of_le le_top)]⟩
end A

local notation "L" => project (h:=h) (H:=H) hC h₂
local notation "B" => stepped Z h
local notation "E" => stepped Z H

def coverC : Dir G c →L[ℝ] Dir G C := (tint G (Body 1 C)).toContinuousLinearMap ∘L (onpass (Fitted.narrow L)) ∘L (tint G (Body 1 c)).symm.toContinuousLinearMap
lemma coverC_exp (v : Dir G c) : represent (coverC (h:=h) (H:=H) hC h₂ v)=(L).low.links (represent v) := rfl
lemma pays_main (W : PathData G) (q : Clip) (v : Dir G c) :
    mainTerm q W (represent (coverC (h:=h) (H:=H) hC h₂ v))=(↑(n^4):ℝ)*mainTerm q W (represent v) := (L).low.revenue q W (represent v)
lemma loops_copy {j k : Side} {n} (W:PathData G) (Zl : Window j k n) (x : Config G j) : Precision.loop W (Zl.links x)=(n:ℝ)*Precision.loop W x := by
  unfold Precision.loop RG.Patch.average; rw [← mul_assoc, mul_comm (n:ℝ),mul_assoc,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Zl.signed,Window.unc]
lemma second_copy {j k : Side} {n} (W:PathData G) (p : Clip) (Zl : Macrame.Window j k n) (x : Config G j) :
    secondTerm p W (Zl.links x)=(n:ℝ)*secondTerm p W x := by unfold secondTerm RG.Patch.average; rw [← mul_assoc, mul_comm (n:ℝ),mul_assoc,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Zl.signed, Window.quadratic_price]
lemma pays_pile (W : PathData G) (q : Clip) (u : Dir G c) (α : ℝ) : draft α W q (coverC (h:=h) (H:=H) hC h₂ u)= (↑(n^4):ℝ)*draft α W q u := by
  unfold draft; rw [coverC_exp,second_copy,loops_copy]; ring

variable (Q : Paintings.Supply G P Z T) (t : Forest (decreed h)) {p : PathData G} {u : Dir G c → AxisChart G t}
local notation "R" => circuit (H:=H) hC h₂ t
variable {v : Dir G C→AxisChart G (circuit (H:=H) hC h₂ t)} (hv : Q.h.Service (S:=stepped Z H) (circuit (H:=H) hC h₂ t) T.clip p v)
    (hu : Critical (S:=stepped Z h) t T.clip p u)
include hv hu
lemma roots_travel : let X := coverC (h:=h) (H:=H) (G:=G) hC h₂
                     let Y := Fitted.track (G:=G) (crown (H:=H) hC h₂ t)
                     ∀ᶠ x : Dir G c in 𝓝 0, v (X x)=tint G (R).Free (onpass Y ((tint G t.Free).symm (u x))) := by
  -- quotation test from same alphabet
  let K := (tint G (Body 1 c)).symm; intro X Y
  have hU := Enrobe.cover_germ Z hC h₂ t (crown hC h₂ t) hu hv (Enrobe.assesses Z hC h₂ t T.clip p)
  filter_upwards [(show Tendsto K (𝓝 0) (𝓝 0) from map_zero K ▸ K.continuous.continuousAt.tendsto).eventually hU] with x hx
  have hh := hx.1
  change (tint G _).symm (v (X x))= onpass Y ((tint G _).symm (u ((tint G (Body 1 c)) (K x)))) at hh
  rw [show tint G _ (K x)= x from (tint ..).apply_symm_apply _] at hh
  exact ((tint ..).apply_symm_apply _).symm.trans (congr_arg _ hh)
omit hv hu in
lemma laid (x : Dir G c) (b : AxisChart G t) : let K := coverC (h:=h) (H:=H) (G:=G) hC h₂
    let Y:= Fitted.track (G:=G) (crown (H:=H) hC h₂ t)
    lifting R (represent (K x)) (tint G (R).Free (onpass Y ((tint G t.Free).symm b)))=(L).high.links (lifting t (represent x) b) := (crown (H:=H) hC h₂ t).governs (meetVar ((tint G (Body 1 c)).symm x) ((tint G t.Free).symm b)) -- rfl?
lemma piles : let X := coverC (h:=h) (H:=H) (G:=G) hC h₂
              (fun x=>Precision.loop p (lifting R (represent (X x)) (v (X x)))) =ᶠ[𝓝 0]
                fun x=> (↑(n^4):ℝ)*Precision.loop p (lifting t (represent x) (u x)) := by
  intro X; filter_upwards [roots_travel hC h₂ Q t hv hu] with x hx; rw [show v (X x)= _ from hx, laid hC h₂ t, loops_copy]
lemma expressed (W : PathData G) (S : Clip) (hq : ClassicalMatch (S:=stepped Z H) R T.clip S p W v) : ClassicalMatch (S:=stepped Z h) t T.clip S p W u := by
  let X := coverC (h:=h) (H:=H) (G:=G) hC h₂; intro j hj κ; let Ft x:=tested (S:=stepped Z h) t κ T.clip p x (u x); let A x:=mainTerm S W (represent (x:Dir G C)); let A' (x:Dir G c):= mainTerm S W (represent x)
  let k:= (L).pullTag Z κ; let g x:=tested (S:=stepped Z H) R k T.clip p x (v x)
  have h':g ∘ X =ᶠ[𝓝 0] (↑(n^4):ℝ) • Ft := by
    filter_upwards [roots_travel hC h₂ Q t hv hu] with x hx
    let a:= meetVar ((tint G (Body 1 c)).symm x) ((tint G t.Free).symm (u x))
    have ha := (crown (H:=H) hC h₂ t).appraisal Z a κ T.clip p
    unfold Function.comp g; rw [show v (X x)=_ from hx]; exact ha
  have ht := hq j hj k
  have he : n≠0 := Nat.ne_of_gt (Nat.pos_of_mul_pos_left (show 0<c.val*n from hC ▸ C.pos))
  have hb : (↑(n^4):ℝ)≠0:= by exact_mod_cast (pow_ne_zero _ he)
  obtain ⟨hf,hg⟩:=compensate X h' hb ht.1
  obtain ⟨hA,hr⟩:=compensate (a:=A') (b:=A) X (ε:=(↑(n^4):ℝ)) (Eventually.of_forall (fun x=> pays_main hC h₂ W S (h:=h) (H:=H) x)) hb ht.2.1
  have hp : iteratedFDeriv ℝ j (g ∘ X) 0=iteratedFDeriv ℝ j (A ∘ X) 0 := by
    rw [jet_liner _ _ ht.1 _,jet_liner _ _ ht.2.1 _,ht.2.2]
  rw [hg,hr] at hp; exact ⟨hf,hA,smul_right_injective _ hb hp⟩
end YM.PhysicalNext.Repeat.Pane
