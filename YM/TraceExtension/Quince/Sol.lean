import YM.TraceExtension.Quince.Pose
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Summer
/-! # Stochastic minus route at reference phase. one more derivative than order being sampled. In a genuine Neighborhood. -/
set_option autoImplicit false
-- adaptation Cub.Summer, expanded radius.
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open JointLoad JointLoad.Heir Lyre
open Cub
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
section its
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f}
    {Q C M r x y : ℝ} {j l n : ℕ} {A : Slab G c l} {w : Directions G f}

variable {m:ℕ} (hq : Canvas P (S.ratio.parent o) m V g n C)
    (ht : temp x ≤ 2*B.threshold) (hP : P.threshold=temp x) (hB : P.power ≤ B.power) (hC : 1 ≤ C) (hl : l ≤ n)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (A i)) (hu : loom P m C ≤ 1)
include hq ht hP hB hC hl h hu
lemma launchFund (hj : j ≤ n) (v : Fin j → Panels l) (hv : ∀ i, ‖v i‖ ≤ 1) :
    Limb B.power (S.ratio.parent o) (iteratedFDeriv ℝ j (launch V (S.ratio.parent o) m g A) 0 v) (2*C*B.threshold) := by
  have ht : C*P.threshold ≤ 2*C*B.threshold := by rw [hP]; nlinarith only [mul_le_mul_of_nonneg_left ht (zero_le_one.trans hC)]
  intro i; apply le_trans (b:=C*P.threshold*spine B.power i.1 (S.ratio.parent o)) ?_ (mul_le_mul_of_nonneg_right ht (spine_pos ..).le)
  by_cases he : j=0
  · subst j; rw [iteratedFDeriv_zero_apply,launch_zero]; exact hq.visible hC hB i
  exact hq.individual h hC hl hj (by omega) v hv hB (Or.inr ⟨rfl,le_trans (by
    apply mul_le_mul_of_nonneg_right (le_mul_of_one_le_left P.threshold_pos.le hC) (by positivity)) hu⟩) i

end its
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {F : Forest S.ratio}
    {P B : BudgetPoint} {X : Support f} {Y : Support c} {t r x τ : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {D' : Slab G c l} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}
    {o : Site f}{C : Libretto G n}{D : Record}
variable (h : Plays C D P B Pt T x)
local notation "V₀"=> (1:Config G c)
local notation "G₀"=> (1:Site c→G.El)

section pT
-- det log.slope guard accepted.P.Catalog.
variable {z:ℝ}{w :Directions G f}
variable (F k)
variable (m:ℕ)
def paintW (C:Libretto G n)(D:Record)(P B:BudgetPoint)(m:ℕ)(y:ℝ):= (clinicFee n D.Q*(loom P m C.C)^2+y)/B.threshold
lemma painted (C:Libretto G n) (D:Record)(P B:BudgetPoint)(m:ℕ)(y:ℝ)(h : y≥0):0≤paintW C D P B m y:=by unfold paintW; have ht:=D.majorant; have hg:0≤ clinicFee n D.Q:=(mul_nonneg zero_le_two (zero_le_one.trans D.majorant)).trans (clinicFee_le n (zero_le_one.trans D.majorant)); have hv:=B.threshold_pos; positivity
abbrev lotW (o:Site f)(m:ℕ)(T:Tube G S)(l:ℕ) (A:Slab G c l) := (Heir.route T) ∘ launch (1:Config G c) (S.ratio.parent o) m 1 A
lemma lotW_zero : lotW o m T l D' 0=0:=by unfold lotW; rw [Function.comp_apply, launch_zero D',blankBirth,map_zero]
local notation "s0"=> loom P m C.C
variable (hx:0 ≤ loom P m C.C) (hs:D.Q*loom P m C.C≤1)(hi:loom P m C.C < D.r)
variable (hl:l ≤ n) (hU:∀ i,P.dirBound (S.ratio.parent o) (D' i))
include F h hl hU hx hs
lemma opticW (j:ℕ)(hj:j ≤ n)(v:Fin j→ Panels l)(hv:∀ i, ‖v i‖ ≤ 1):Sized (wealth C) (iteratedFDeriv ℝ j (lotW o m T l D') 0 v) B o:=by
   have hp:=h.rehearsed; have ht:=hp.tensions; let u₀:=s0
   let A:= launch V₀ (S.ratio.parent o) m G₀ D'
   have h0:= C.C_one; have hD:= D.majorant; have hP: u₀≥0:=by unfold u₀ loom; have hp:= P.threshold_pos; positivity
   have hq : Canvas P (S.ratio.parent o) m V₀ G₀ n C.C:= posedW C.Z
   have hx := launchFund hq ht.coarse hp.temp_eq hp.powers h0 hl hU ((le_mul_of_one_le_left hP hD).trans hs) hj v hv
   let y:=(S.patch.L.val:ℝ); have hy : 1≤ y:= Nat.one_le_cast.mpr S.patch.L.property
   have he := (h.stages F).taper B {o} o _ rfl hx
   have hc : C.M ≥ 1:= C.matins
   unfold lotW; rw [(Heir.route T).iteratedFDeriv_comp_left (hq.ready _) (Nat.cast_le.mpr hj)]; change Sized (wealth C) (Heir.route T _) B o
   apply higher (he.shot (by positivity) (inv_le_one_of_one_le₀ hy) (zero_le_one.trans hc)); exact mul_le_of_le_one_right (by unfold wealth; positivity : 0≤wealth C) (inv_le_one_of_one_le₀ hy)

include hi
lemma earnW (hj : j ≤ n) (v : Fin j → Panels l) (hv : ∀ i, ‖v i‖ ≤ 1) (hw:‖w‖≤ s0) (hz:‖w‖ ≤ z):
    let a := enters V₀ (S.ratio.parent o) m G₀ D' w
    let b := lotW o m T l D'
    Sized (paintW C D P B m z) ((iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v)-(iteratedFDeriv ℝ j b 0 v)) B o:=by
  intro a b; let u₀:= loom P m C.C
  have hZ:0≤z:= (norm_nonneg _).trans hz
  let A₀ := launch V₀ (S.ratio.parent o) m G₀ D'
  let Z := iteratedFDeriv ℝ j A₀ 0 v
  have hp:= h.rehearsed; have ht:=hp.tensions
  have hD:= D.majorant; have hC:= C.C_one
  have hT : 2≤ n:=by have h:=hp.test; have he:= P.order_ge; omega
  have hM : u₀ ≤ 1:= (le_mul_of_one_le_left ((norm_nonneg _).trans hw) hD).trans hs
  have hq : Canvas P (S.ratio.parent o) m V₀ G₀ n C.C:= posedW C.Z
  have hfee := (timesEnter hq (h.acts F k) hp.temp_eq hT hU hC hl hD hM hi.le hw true).2 j hj v hv
  rw [spine_self,one_pow,mul_one] at hfee
  let U:=iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v
  let a₀ := mainStroke T F true (iteratedFDeriv ℝ j a 0 v)
  have h : ‖a₀-Heir.route T Z‖ ≤ z := by
    by_cases hi : j=0
    · subst j; unfold a₀ Z; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; change ‖(Heir.route T (A₀ 0)+w)-Heir.route T (A₀ 0)‖ ≤ _; simpa only [add_sub_cancel_left] using hz
    unfold a₀ a; rw [enter_pos hq hj (by omega) v]; change ‖(Heir.route T Z+0)-Heir.route T Z‖ ≤ _; simpa
  have h := ((norm_sub_le_norm_sub_add_norm_sub U a₀ (Heir.route T Z)).trans (add_le_add hfee h))
  have hp:= painted C D P B m z hZ
  refine ⟨hp,fun i => ?_⟩
  unfold b lotW; rw [(Heir.route T).iteratedFDeriv_comp_left (hq.ready _) (Nat.cast_le.mpr hj)]
  change ‖(U-Heir.route T Z) i‖ ≤ _
  apply ((norm_le_pi_norm ..).trans h).trans
  let S:=paintW C D P B m z
  have hv:=B.threshold_pos.ne'
  calc
    _ = S * B.threshold := by unfold S paintW; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right B.threshold_pos.le (spine_one B.power i.1 o)) hp
end pT
end YM.PhysicalNext.Repeat.Quince
