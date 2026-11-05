import YM.Next.RANK.Flux.Grader
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pictures


/-!
# Sizes through the visual call

Infer the radius reweight and preserve the MARKER ROOT sum. Uses no
per-step Ḻ-dependent growth factor for R SourceAt -- large L and
post-L beta spends on this trajectory remain mandatory. K site→site
through parent counts post-L. Combined later with the time-of-day prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Docking
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Filter Corona Thirst
open scoped Topology BigOperators Classical ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ e Λ κ σ : ℝ} {L : Lantern G S} {F : Orchard S} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι α : Type} [Fintype W] [DecidableEq W] {θ : W→Site f} {u : W→Site c}
    {r : W→ℝ} {C R : BudgetPoint}

def increment (e : ℝ) := Flux.ucap e+1+1
-- τ_A at source, Q on output
structure Towering (s : Side) (C R : BudgetPoint) (e eF : ℝ) : Prop where
  square : C.B ≤ 2*R.B
  tallies : 0 ≤ e
  lift : 10*(15:ℝ)^4 * Docking.increment e ≤ s.val*eF
abbrev Tailprice (s : Side) (C R : BudgetPoint) (e : ℝ) := Towering s C R e e

def salary (e : ℝ) := Real.exp ((15:ℝ)^4 * Docking.increment e)
lemma forsaken (X : Support f) (S : StepData c f) (h : Towering S.patch.L C R e σ) :
    Value.charge R (Docking.increment e) (wings S R.B X) ≤ salary e*Value.charge C σ X:= by
  let s:ℝ:= S.ratio.count.val; let p:= C.B; let b:= R.B
  have hs:0<s:= Nat.cast_pos.mpr S.ratio.count.property
  let Y:= wings S b X
  have he:s*coverNumber b Y ≤ (s+10 * coverNumber p X)*(15:ℝ)^4:= by
    have hc:= Corona.collapse S.ratio X p b R.B_pos h.square 1
    rw [one_mul] at hc
    have hp : (S.ratio.count.val*coverNumber b Y:ℕ) ≤ (S.ratio.count.val+10*coverNumber p X)*15^4:=hc
    unfold s; exact_mod_cast hp
  let f := Docking.increment e
  have hp:0≤f:=by unfold f Docking.increment Flux.ucap; linarith only [h.tallies]
  unfold Value.charge salary; rw [← Real.exp_add]; apply Real.exp_monotone
  apply le_of_mul_le_mul_left _ hs
  have hx : 10 * 15^4 * f ≤ s*σ:= h.lift
  change s*(f*↑(coverNumber b Y))≤ s*(15^4*f+σ*↑(coverNumber p X))
  linarith only [mul_le_mul_of_nonneg_left he hp,mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (coverNumber p X) (α:=ℝ))]

def penny (X : Support f) (C : BudgetPoint) (e b : ℝ) := b / Value.charge C e X
lemma penny_nn (X : Support f) (C : BudgetPoint) {e b : ℝ} (h : 0≤b) : 0≤ penny X C e b:= div_nonneg h (Real.exp_pos _).le

structure Parachute (S : StepData c f) (C R : BudgetPoint) (e σ : ℝ) (n : ℕ) (Z : ℝ) : Prop where
  tallies : 0 ≤ e
  price : 0 ≤ Z
  hits X : Value.charge R (Docking.increment e) (wings S n X) ≤ Z*Value.charge C σ X
lemma Towering.covers (S : StepData c f) (h : Towering S.patch.L C R e σ) : Parachute S C R e σ R.B (salary e):= ⟨h.tallies,(Real.exp_pos _).le,fun X=>forsaken X S h⟩
variable {Υ : ℕ} {Z : ℝ}
lemma lent (i : ι) (X : ι→ Support f) (S : StepData c f) {T : ℝ} (hT : 0≤T) (A : ι→ℝ) (h : Parachute S C R e σ Υ Z) (hm : 0 ≤ A i) {x : ℝ} (hx : x ≤ Docking.increment e): alarm (wings S Υ ∘ X) (fun i=>T * penny (X i) C σ (A i)) R.B x i ≤ (T * Z)* A i:= by
  unfold alarm penny; let k:= Value.charge C σ (X i); let Y:=wings S Υ (X i);have hk : 0<k:= Real.exp_pos _
  have hp : Value.charge R x Y ≤ Value.charge R (Docking.increment e) Y:= by unfold Value.charge;gcongr
  apply (mul_le_mul_of_nonneg_left (hp.trans (h.hits _)) (show 0 ≤ T * (A i/k) by positivity)).trans_eq; change _ * (Z*k) = _; field_simp
variable [Fintype ι]

private lemma pricing (S : StepData c f) {A : ι → ℝ} (X : ι → Support f) (hA : ∀ i,0 ≤ A i) (p : ι→Prop) [DecidablePred p] {u t} (ht : 0≤t) (hp : Parachute S C R e σ Υ Z)
    {v : ℝ} (hv : u ≤ Docking.increment e) (he : (∑ i,if p i then A i else 0) ≤ v) :
    strike (wings S Υ∘X) (fun i=>t*penny (X i) C σ (A i)) R p u ≤ t*Z*v:= by
  unfold strike; rw [Finset.sum_filter]
  apply le_trans _ (mul_le_mul_of_nonneg_left he (mul_nonneg ht hp.price))
  rw [Finset.mul_sum]; apply sum_le_sum; intro i _; split_ifs; exact lent i X S ht A hp (hA i) hv
  rw [mul_zero]

lemma price_wave (S : StepData c f) (H : ι→ SourceAt G θ) (A : ι → ℝ) (hA : ∀ i,0≤ A i) {u v : ℝ}
    (hp : Parachute S C R e σ Υ Z) {t : ℝ} (ht : 0≤t) (hv : u ≤ Docking.increment e)
    (hl : ∀ (w : W),(∑ i,if w∈(H i).fires.val then A i else 0) ≤ v) :
    ∀ w,strike (fun i=> wings S Υ (H i).extent) (fun i=> t * penny (H i).extent C σ (A i)) R
      (fun i=>w∈(H i).fires.val) u ≤ t*Z*v:= by
  intro w; exact pricing S _ hA _ ht hp hv (hl w)
lemma accum {H : ι → Flake S G x F u τ} {D : ι→ℝ} (h : ∀ i,0 ≤ D i) {v z : ℝ} {m : ℕ} (hp : Pertains u m) (hz : 0≤z)
    (hr : ∀ w,strike (fun i=>(H i).space) D R (fun i=>w∈(H i).notes.val) (v+1)≤ z) : Hits (fun i=>(H i).space) D R v (wilt R.B*(m*z)):= by
  let f (i : ι):SourceAt G u:= ⟨(H i).space,(H i).notes,(H i).nontrivial,(H i).placed,fun _=>0,measurable_const,fun _ _ _=>rfl,fun _ _=>rfl⟩
  exact Flux.valve f R D h hp hz hr

private lemma tariff (S : StepData c f) (K : ι→ Lifted G θ C.threshold) (A : ι→ℝ) (hA : ∀ i,0≤ A i) {u z : ℝ}
    (hp : Parachute S C R e σ Υ Z) (hv : u ≤ Docking.increment e) (x : Site f)
    (hl : (∑ i,if x∈(K i).extent then A i else 0) ≤ z):
    strike (fun i=> wings S Υ (K i).extent) (fun i=>penny (K i).extent C σ (A i)) R (fun i=>x∈(K i).extent) u ≤ Z*z := by
  simpa only [Function.comp_def,one_mul] using pricing S (fun i=> (K i).extent) hA (fun i=>x∈(K i).extent) zero_le_one hp hv hl
lemma price_lift (S : StepData c f) (K : ι→ Lifted G θ C.threshold) (A : ι→ℝ) (hA : ∀ i,0≤ A i) {u z : ℝ}
    (hp : Parachute S C R e σ Υ Z) (hv : u ≤ Docking.increment e)
    (hl : ∀ (x : Site f),(∑ i,if x∈(K i).extent then A i else 0) ≤ z):
    ∀ i,strike (fun i=> wings S Υ (K i).extent) (fun i=>penny (K i).extent C σ (A i)) R (fun j=> i∈(K j).fires.val) u ≤ Z*z := by
  intro i; exact (Flux.supple _ _ _ _ _ _ (fun j hj=>(K j).remembers i hj) (fun j=> penny_nn _ _ (hA j))).trans (tariff S K A hA hp hv (θ i) (hl _))

-- Synthetic provenance grouping: anchor of each K is one true inside
-- position in fine supported inventory, and pay that position with valve
-- at OUTPUT support. Parent multiplicity only impacts SITE bill. -/
lemma packs_lift (S : StepData c f) (K : ι→ Lifted G θ C.threshold) (A : ι→ℝ) (hA : ∀ i,0≤ A i) {u z : ℝ}
    (hp : Parachute S C R e σ Υ Z) (hv : u+1 ≤ Docking.increment e) (hz : 0≤z)
    (hl : ∀ (x : Site f),(∑ i,if x∈(K i).extent then A i else 0) ≤ z):
    Hits (fun i=> wings S Υ (K i).extent) (fun i=>penny (K i).extent C σ (A i)) R u (Thirst.wilt R.B*((Fintype.card (Site S.patch.L):ℝ)*(Z*z))):= by
  choose b hb using fun i=>(K i).needed.mono (K i).records
  let m:=Fintype.card (Site S.patch.L); let p:=S.ratio.parent
  let H (i : ι) : SourceAt G p:= {
    extent:=wings S Υ (K i).extent
    fires:= Glyph.slot (b i)
    chosen:=singleton_nonempty _
    remembers j he := Finset.mem_singleton.mp he |>.symm ▸ involved (S:=S) _ _ (hb i)
    value _:=0, meas:=measurable_const, loc _ _ _:=rfl, inv _ _:=rfl }
  let f i := penny (K i).extent C σ (A i)
  have hf i : 0≤f i:= penny_nn _ _ (hA i)
  have hy : Pertains p m:= by
    intro i
    let Z(x:Site c) : ℝ:= if x=i then 1 else 0
    have hh := Work.F01.sum_parent S.ratio Z
    unfold Z at hh
    -- map cardinal
    rw [← Finset.sum_filter] at hh; simp only [Finset.sum_const, nsmul_eq_mul, mul_one,Finset.sum_ite_eq', mem_univ, ↓reduceIte] at hh
    unfold p m; change (_ ≤ (Fintype.card (Site S.ratio.count))); exact_mod_cast hh.le
  exact Flux.valve H R f hf hy (mul_nonneg hp.price hz) (fun i=> (supple _ f _ _ _ _ (fun j h=> show i∈(K j).extent from (show i=b j from Finset.mem_singleton.mp h).symm ▸ hb j) hf).trans (tariff S K A hA hp hv i (hl i)))
end YM.PhysicalNext.InteractingRank.Display.Docking
