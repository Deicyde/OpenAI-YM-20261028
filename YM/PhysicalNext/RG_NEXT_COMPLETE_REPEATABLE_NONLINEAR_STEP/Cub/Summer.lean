import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Listened
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Pose
/-! # Stochastic minus route at reference phase. one more derivative than order being sampled. In a genuine Neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open JointLoad JointLoad.Heir Lyre
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
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
def paint (C:Libretto G n)(D:Record)(P B:BudgetPoint)(x y:ℝ):= (clinicFee n D.Q*(loom P (reach x) C.C)^2+y)/B.threshold
lemma painting_pos (C:Libretto G n) (D:Record)(P B:BudgetPoint)(x y:ℝ)(h : y≥0):0≤paint C D P B x y:=by unfold paint; have ht:=D.majorant; have hg:0≤ clinicFee n D.Q:=(mul_nonneg zero_le_two (zero_le_one.trans D.majorant)).trans (clinicFee_le n (zero_le_one.trans D.majorant)); have hv:=B.threshold_pos; positivity
local notation "s"=> loom P (reach x) C.C -- may C.C unknown
abbrev wealth (C:Libretto G n):= (2+1:ℝ)*C.M
abbrev lot (o:Site f)(x:ℝ)(T:Tube G S)(l:ℕ) (A:Slab G c l) := (Heir.route T) ∘ launch (1:Config G c) (S.ratio.parent o) (reach x) 1 A
lemma lot_zero : lot o x T l D' 0=0:=by unfold lot; rw [Function.comp_apply, launch_zero D',blankBirth,map_zero]
variable (hl:l ≤ n) (hU:∀ i,P.dirBound (S.ratio.parent o) (D' i))
include F h hl hU
lemma optic (j:ℕ)(hj:j ≤ n)(v:Fin j→ Panels l)(hv:∀ i, ‖v i‖ ≤ 1):Sized (wealth C) (iteratedFDeriv ℝ j (lot o x T l D') 0 v) B o:=by
   have hp:=h.rehearsed; have ht:=hp.tensions; let u₀:=s
   let A:= launch V₀ (S.ratio.parent o) (reach x) G₀ D'
   have h0:= C.C_one; have hD:= D.majorant; have hP: u₀≥0:=by unfold u₀ loom; have hp:= P.threshold_pos; positivity
   have hq : Canvas P (S.ratio.parent o) (reach x) V₀ G₀ n C.C:= posed C.Z hp.wire
   have hx := launch_cost hq ht.coarse hp.temp_eq hp.powers h0 hl hU ((le_mul_of_one_le_left hP hD).trans (ht.small.trans (min_le_right ..))) hj v hv
   let y:=(S.patch.L.val:ℝ); have hy : 1≤ y:= Nat.one_le_cast.mpr S.patch.L.property
   have he := (h.stages F).taper B {o} o _ rfl hx
   have hc : C.M ≥ 1:= C.matins
   unfold lot; rw [(Heir.route T).iteratedFDeriv_comp_left (hq.ready _) (Nat.cast_le.mpr hj)]; change Sized (wealth C) (Heir.route T _) B o
   apply higher (he.shot (by positivity) (inv_le_one_of_one_le₀ hy) (zero_le_one.trans hc)); exact mul_le_of_le_one_right (by unfold wealth; positivity : 0≤wealth C) (inv_le_one_of_one_le₀ hy)

lemma earnFirst (hj : j ≤ n) (v : Fin j → Panels l) (hv : ∀ i, ‖v i‖ ≤ 1) (hw:‖w‖≤ s) (hz:‖w‖ ≤ z):
    let a := enters V₀ (S.ratio.parent o) (reach x) G₀ D' w
    let b := lot o x T l D'
    Sized (paint C D P B x z) ((iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v)-(iteratedFDeriv ℝ j b 0 v)) B o:=by
  intro a b; let u₀:= loom P (reach x) C.C
  have hZ:0≤z:= (norm_nonneg _).trans hz
  let A₀ := launch V₀ (S.ratio.parent o) (reach x) G₀ D'
  let Z := iteratedFDeriv ℝ j A₀ 0 v
  have hp:= h.rehearsed; have ht:=hp.tensions
  have hD:= D.majorant; have hC:= C.C_one
  have hT : 2≤ n:=by have h:=hp.test; have he:= P.order_ge; omega
  have hM : u₀ ≤ 1:= (le_mul_of_one_le_left ((norm_nonneg _).trans hw) hD).trans (ht.small.trans (min_le_right ..))
  have hq : Canvas P (S.ratio.parent o) (reach x) V₀ G₀ n C.C:= posed C.Z hp.wire
  have hfee := (timesEnter hq (h.acts F k) hp.temp_eq hT hU hC hl hD hM ht.allows.le hw true).2 j hj v hv
  rw [spine_self,one_pow,mul_one] at hfee
  let U:=iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v
  let a₀ := mainStroke T F true (iteratedFDeriv ℝ j a 0 v)
  have h : ‖a₀-Heir.route T Z‖ ≤ z := by
    by_cases hi : j=0
    · subst j; unfold a₀ Z; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; change ‖(Heir.route T (A₀ 0)+w)-Heir.route T (A₀ 0)‖ ≤ _; simpa only [add_sub_cancel_left] using hz
    unfold a₀ a; rw [enter_pos hq hj (by omega) v]; change ‖(Heir.route T Z+0)-Heir.route T Z‖ ≤ _; simpa
  have h := ((norm_sub_le_norm_sub_add_norm_sub U a₀ (Heir.route T Z)).trans (add_le_add hfee h))
  have hp:= painting_pos C D P B x z hZ
  refine ⟨hp,fun i => ?_⟩
  unfold b lot; rw [(Heir.route T).iteratedFDeriv_comp_left (hq.ready _) (Nat.cast_le.mpr hj)]
  change ‖(U-Heir.route T Z) i‖ ≤ _
  apply ((norm_le_pi_norm ..).trans h).trans
  let S:=paint C D P B x z
  have hv:=B.threshold_pos.ne'
  calc
    _ = S * B.threshold := by unfold S paint; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right B.threshold_pos.le (spine_one B.power i.1 o)) hp
end pT
end YM.PhysicalNext.Repeat.Cub
