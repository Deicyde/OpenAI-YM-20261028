import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Dolls
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Estate
/-! # Retain all old marker-free activities and marks on unpriced region. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Baler Thirst
open scoped Topology BigOperators Classical
variable {G : Gauge} {n f : Side} {S : StepData n f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W V ι κ α β : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site n} {v : V→Site n}

section
variable (R : Rep G n) (u : W→Site n)
    {o m Λ δ e w r : ℝ} (hr : R.Lawful o m Λ δ w)
local notation "B"=> Gel.archived R u hr
lemma conservation : Background R B := by
  intro i U; unfold column; rw [Finset.sum_eq_single i]; exact if_pos ⟨rfl,rfl⟩
  exact fun a _ he=> if_neg (fun H => he (Subtype.ext H.2)); simp
lemma sticker (y : W→ℝ) : Stripes R.p B y R.p.supportExponent w:= by
  let A:=R.activities;let P:=R.p
  let Q:= orig R.activities R.p hr.labels.forced; let T:= bareBurst ∘ B
  have hx i U: (T i).value U=Archive A i U:=rfl
  have he i U: (T i).value U=∑' j, if (Q j).city=i then (Q j).value U else 0 := by
    rw [hx]; unfold Q Archive; apply tsum_congr; intro j; split_ifs <;> first|rfl|contradiction
  have hl : SumHit (p:=P) T P.supportExponent w:= maintain Q (old_cost hr.labels) P.exponent_pos.le T (fun _=>rfl) he
  obtain ⟨z,h,H⟩:=hl
  let f i:=charge P P.supportExponent (T i).city.val.1
  let v i:= z i*f i; have hv i:0≤v i:=mul_nonneg (h i).1 (Real.exp_pos _).le
  refine ⟨v,fun i=> ⟨hv i,fun U=>?_⟩,fun i=> ?_⟩
  · have h' : Poly.toll y (quiet W)=1:= by simp only [Poly.toll,Glyph.quiet,Census.quiet,prod_empty]
    change f i*Poly.toll _ (quiet W)*‖((B i).value U)‖ ≤ _
    rw [h',mul_one,mul_comm]; apply mul_le_mul_of_nonneg_right _ (show 0≤ f i from (Real.exp_pos _).le)
    change ‖(↑(Archive A i U):ℂ)‖≤ _; rw [Complex.norm_real];exact (h i).2 U
  refine le_trans ?_ ((tsum_fintype ..).symm.trans_le (H i).2.2)
  apply Finset.sum_le_sum; intro j _; unfold Thirst.pay; split_ifs <;> first|exact le_rfl|contradiction
end
section
variable (R : Rep G n) {o m Λ δ w : ℝ} (hr : R.Lawful o m Λ δ w)
include hr
lemma read_left (U) (K : ι → Lifted G u R.p.threshold) [Fintype ι] (h : Background R K) (hp : ∀ i,(K i).fires=quiet W) :
    RAIDage K U=scalar W (R.activities.gas R.p U):= by
  let P:=R.p; let A:=R.activities; let Q:=orig A P hr.labels.forced; let K₀:=fun j : ℕ=> (Q j).city; let f := fun j=> (Q j).value U; let Z:= flags R.p.threshold U
  let K':=fun j=> Gel.calls (K j)
  let e:=fun j=>(K j).value U
  have ht : A.gas P U= ∑ i,peeled id (piece K₀ f) Z i := by
    unfold Activities.gas; simp_rw [gas_at A P hr.labels.forced]; let v j:= peeled K₀ f Z j
    have hh : Summable v:= ((Activities.gasSeries hr.labels).summable U).congr fun j=>gas_at A P hr.labels.forced _ _
    have he : Summable f := summable_present Q (old_cost hr.labels) P.exponent_pos.le U
    apply Baler.all K₀ f Z hh
    intro i; exact (he.indicator (s:={j|K₀ j=i})).congr (fun b=> by by_cases h : K₀ b=i <;> simp [Set.indicator,h])
  have hz (p : Finset ι) : Lifted.pack K p U= Poly.send (quiet W) (peeled K' e Z p):= by
    unfold Lifted.pack peeled
    have he : Lifted.gather K p U ↔ ripe K' p Z:= Iff.rfl
    split_ifs with hm hh hh
    · unfold Lifted.amount; simp_rw [hp,show Poly.send (quiet W)=algebraMap ℂ (veil W) from rfl]; exact (map_prod (algebraMap ℂ (veil W)) _ p).symm
    · exact (hh (he.1 hm)).elim
    · exact (hm (he.2 hh)).elim
    exact (Poly.send_zero _).symm
  have hw i : piece K' e i= (↑(piece K₀ f i):ℂ):= by
    let C':addressKey n:=i
    have hp : piece K' e i=column K i U:= by
      unfold piece column; rw [tsum_fintype]; apply sum_congr rfl; intro j _; simp_rw [hp,true_and]
      exact if_congr (Subtype.ext_iff) rfl rfl
    rw [hp,h i U]; congr
  unfold RAIDage; simp_rw [hz,show Poly.send (quiet W)=algebraMap ℂ (veil W) from rfl]; rw [← map_sum]
  rw [← tsum_fintype (L:=SummationFilter.unconditional (Finset ι)), Baler.all K' _ Z ((hasSum_fintype _).summable) (fun _=> (hasSum_fintype _).summable)]
  rw [ht]
  rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _
  unfold peeled; split_ifs; swap; · rw [map_zero,map_zero]
  simp_rw [hw]; rw [← Complex.ofReal_prod]; rfl

-- Bout leger ONLY when no H (e.g. Empty). exact all quiet pores.
lemma darkDust [Fintype α] [IsEmpty α] [Fintype ι] (H : α→ SourceAt G u) (K : ι→Lifted G u R.p.threshold) (he : Background R K) (hp : ∀ i,(K i).fires=quiet W): Value.dust R H K= (scalar W) ∘ R.eval:=by
  funext U; unfold Value.dust; rw [Fintype.sum_empty,Exponential.pass_zero, one_mul]; change (_) • RAIDage K U=_; rw [read_left R hr U K he hp, Function.comp_apply, Rep.eval,map_mul,Algebra.smul_def]; rfl
end
end YM.PhysicalNext.InteractingRank.Display.Sew
