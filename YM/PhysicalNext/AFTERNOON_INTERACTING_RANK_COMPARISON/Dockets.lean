import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Seals

/-!
# Paying first-system club integrals

Use Tilt receipts on unmarked material. Every probe tested.
In `refund` a forced club can always extract the deep `m` payment from
somebody, and even an unforced club containing unmarked material can
take at least l. Without unmarked material the K marks can't occur
(see `solo`). The remaining step, paying l even on club integrals with
no unmarked material but requiring a remainder, uses Shadow (e.g.
the W-bad integral still tested on the real fields, costs a larger l).
Unforced all-leading clubs don't take either extra payment. Keeps
complete geometry including Fine flags at Y. Per-query leaf goods
from Wares and Pole/Launch costs in later modules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Filter
open scoped Topology BigOperators Classical ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} {J : ChartRatio G}
    {x τ σ w : ℝ} {L : Lantern G S} {F : Forest S.ratio} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι κ α : Type} [Fintype W] [DecidableEq W] {θ : W → Site f} {u : W → Site c}
    {r : W → ℝ} {l m : ℝ}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (K : κ→ Lifted G θ R.p.threshold)
    (H : α → Flake S G x L.park u R'.p.threshold)
    (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ) (C : α→Prop)
    (z : ι → ℝ) (v : κ→ ℝ) (w : α→ℝ)
local notation "Q" => picture R R' p K H ht hs hv

def Shadow (f : RoomView A x F G→ℝ) (μ : Measure (RoomView A x F G)) (l w : ℝ) : Prop:= (∀ y,l*f y≤ w) ∨
    ∃ s : Set (RoomView A x F G), MeasurableSet s∧ l*μ.real s≤1 ∧ ∀ y,y ∉ s → f y=0

/-- Obtained from price/tolerance of flakes, p Wares.
Note K lifted to densities only by BEFORE-threshold logic. -/
structure LetterCost (l m : ℝ) (r : W→ℝ) : Prop where
  charged i : (p i).Wares T m l (z i)
  stellar i : 0≤ v i
  favorable i : 0≤ w i
  paid i U A k y : Positioned x A U → stroke (Q (.inl (.inr i))) r A k U y ≤ v i
  illumined i U A k y : Positioned x A U → stroke (Q (.inr i)) r A k U y ≤ w i
  shaded i : ¬ C i → ∀ U A k, Positioned x A U→ Shadow (stroke (Q (.inr i)) r A k U) (viewer T A x k.wood k.tag U) l (w i)

local notation "HCost" => LetterCost R R' p K H ht hs hv C z v w
lemma incomes (hx : HCost l m r) i : 0≤ bid z v w i:= by rcases i with (i|i)|i; exacts [(hx.charged i).1,hx.stellar i,hx.favorable i]

def tune (s : Club Q) (l m : ℝ):= if (cardGoal Q s.val).Nonempty then m else Flux.factor (¬Gathered R R' p K H ht hs hv C s) l
lemma tune_safe (hl : 1≤l) (hm : 1≤m) (s : Club Q) : 1≤tune R R' p K H ht hs hv C s l m:= by unfold tune factor; split_ifs <;> first|assumption| exact le_rfl

lemma breakdown (s : Finset (Spectrum ι κ α)) {A : Type*} [CommMonoid A] (f : Spectrum ι κ α→A) :
    ∏ i∈s,f i=(∏ i∈s.toLeft.toLeft,f (.inl (.inl i)))*(∏ i∈s.toLeft.toRight,f (.inl (.inr i)))*(∏ i∈s.toRight,f (.inr i)):= by
  nth_rw 1 [← s.toLeft_disjSum_toRight];rw [prod_disjSum]; congr 1; nth_rw 1 [← s.toLeft.toLeft_disjSum_toRight]; rw [prod_disjSum]
lemma solo (s : Club Q) (hh : ¬ s.val.toLeft.toLeft.Nonempty) : s.val.toLeft=∅ ∧ ¬(cardGoal Q s.val).Nonempty:= by
  have hz := on_film R R' p K H ht hs hv s.val
  have h := Finset.not_nonempty_iff_eq_empty.mp hh
  have hp:= ((hz.2.2.mp s.property.2.1).2.2); rw [h, Finset.biUnion_empty] at hp
  constructor
  · have hx : s.val.toLeft.toRight=∅:= eq_empty_iff_forall_notMem.mpr fun i hi=>not_nonempty_empty (α:=Site f) (hp.symm ▸ ((K i).needed.mono (fun j hj=>Finset.mem_biUnion.mpr ⟨_,hi,hj⟩)))
    rw [← Finset.toLeft_disjSum_toRight (u:=s.val.toLeft), hx,h]; ext (j|j)<;>simp
  rw [hz.1,h, Finset.biUnion_empty]; exact not_nonempty_empty
section
set_option maxHeartbeats 500000 in
theorem refund (hx : HCost l m r) (hr : ∀ i,0<r i) (hl : 1≤l) (hm : 1≤m) (s : Club Q) (U : Config G c) (k : Streak L.park)
    (hp : validArea Q s U) :
    let A:=stapled x (glow Q s.val) U; let t:= tune R R' p K H ht hs hv C s l m
    Integrable (stage Q s.val A k U) (viewer T A x k.wood k.tag U) ∧
      (t* Poly.toll r (fires Q s.val)) * (∫ y, ‖stage Q s.val A k U y‖ ∂viewer T A x k.wood k.tag U) ≤ ∏ i∈s.val,bid z v w i:= by
  intro A t; let μ :=viewer T A x k.wood k.tag U
  let f:= stage Q s.val A k U; let q:=Poly.toll r (fires Q s.val)
  let g x:= q*‖f x‖; let b:=s.val.toLeft.toLeft; let S':=s.val.toLeft.toRight ; let d:=s.val.toRight
  let B := ∏ i∈b,z i; let Y:=∏ i∈S', v i; let W':=∏ i∈d,w i
  let X y := ∏ i∈b,stroke (lowTone u (p i)) r A k U y
  let c i := stroke (Q (.inl (.inr i))) r A k U; let h i:= stroke (Q (.inr i)) r A k U
  obtain ⟨h1,h2⟩:= earning_base R R' p K H ht hs hv s U A k rfl hp z (hx.charged) hm hl (r:=r)
  let M:=∏ i∈b,(p i).infl m l
  change Integrable X μ at h1; change M*(∫ y,X y∂μ) ≤ B at h2
  have hs' y : g y=X y*((∏ i∈ S',c i y) *(∏ i∈ d,h i y)):= (earmark s.val s.property.2 U A k y).trans (Eq.trans (breakdown _ _) (mul_assoc ..))
  have hα := hx.paid; have hβ:=hx.illumined
  have hB : 0≤B:= prod_nonneg fun i _=>(hx.charged i).1
  have hY : 0≤Y:=prod_nonneg fun i _=>hx.stellar i
  have hW : 0≤W':=prod_nonneg fun i _=>hx.favorable i
  have hh y (s: Finset α) : ∏ i∈s,h i y ≤ ∏ i∈s,w i:= Finset.prod_le_prod (fun i _=>stroke_nonneg hr _ _ _ _ _) fun i _=>hβ _ U _ _ _ (position ..)
  let a y:= X y*(Y*W')
  have he : Integrable a μ:=h1.mul_const _
  have ha y:g y ≤ a y:= by rw [hs']; apply mul_le_mul_of_nonneg_left (mul_le_mul (Finset.prod_le_prod (fun i _=>stroke_nonneg hr _ _ _ _ _) (fun i _=>hα i U _ _ _ (position ..))) (hh y d) (prod_nonneg fun i _=>stroke_nonneg hr _ _ _ _ _) hY) (prod_nonneg fun _ _=> stroke_nonneg hr _ _ _ _ _)
  have hq : 0<q:= Poly.worth hr _; have hT:1≤t:= tune_safe R R' p K H ht hs hv C hl hm s
  have hF:Integrable f μ:= by
    have hg (y) : ‖f y‖ ≤ q⁻¹*a y:= (le_inv_mul_iff₀ hq).2 (ha y)
    exact (he.const_mul _).mono' (((observer Q s).placed A k).atLens (position ..)).aestronglyMeasurable (Eventually.of_forall hg)
  have hg : Integrable g μ:= hF.norm.const_mul _
  refine ⟨hF,?_⟩
  rw [show (∏ i∈s.val,bid z v w i)=B*(Y*W') from (breakdown ..).trans (mul_assoc ..),mul_assoc,← integral_const_mul]; change t*(∫ y,g y∂μ)≤ _
  have hHx i (hi:i∈b): (p i).infl m l ≤ M:= by unfold M; rw [← Finset.mul_prod_erase b _ hi]; exact le_mul_of_one_le_right (zero_le_one.trans ((p i).infl_one hm hl)) (Finset.one_le_prod (fun i _=>(p i).infl_one hm hl))
  by_cases hv' : b.Nonempty
  · have hh:t≤ M := by
      unfold t tune; split
      next hx=>
        obtain ⟨hu,hz⟩:=hx; rw [(on_film R R' p K H ht hs hv s.val).1] at hz
        obtain ⟨i,hi,hz⟩:=mem_biUnion.mp hz
        rw [← show (p i).infl m l=m from if_pos (show (p i).down.Nonempty from ⟨hu,hz⟩)]
        exact hHx _ hi
      next he=>
        unfold factor; split
        next hC=>
          obtain ⟨i,hi⟩:= hv'
          have hz : ¬(p i).down.Nonempty := fun ⟨x,h⟩=> he ⟨x, (on_film R R' p K H ht hs hv s.val).1.symm ▸ (Finset.mem_biUnion.mpr ⟨_,hi,h⟩: x∈ s.val.toLeft.toLeft.biUnion _)⟩
          rw [← show (p i).infl m l=l from if_neg hz]
          exact hHx _ hi
        exact one_le_prod (fun j _=> (p j).infl_one hm hl)
    have hh' := integral_mono hg he ha
    unfold a at hh'; rw [integral_mul_const] at hh'; apply (mul_le_mul hh hh' (integral_nonneg fun i=>mul_nonneg hq.le (norm_nonneg _)) ((zero_le_one.trans hT).trans hh)).trans; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 (mul_nonneg hY hW)
  obtain ⟨hp',hh'⟩:=solo R R' p K H ht hs hv s hv'
  have hX : b=∅:=not_nonempty_iff_eq_empty.mp hv'; have hS : S'=∅:=by unfold S'; rw [hp']; rfl
  have hz t : g t=∏ i∈d,h i t:= by rw [hs']; unfold X; rw [hX,hS]; simp
  have hy : B*(Y*W')= W' := by unfold B Y; rw [hX,hS]; simp
  letI : IsProbabilityMeasure μ:=by unfold μ;infer_instance
  rw [hy]
  by_cases hZ:Gathered R R' p K H ht hs hv C s
  · rw [show t=1 from Eq.trans (if_neg hh') (if_neg (not_not_intro hZ)),one_mul]
    apply (integral_mono hg (integrable_const (μ:=μ) W') (fun y=> (hz y).trans_le (hh y d))).trans; simp
  have hD : t=l := Eq.trans (if_neg hh') (if_pos hZ); rw [hD]
  obtain ⟨i,hi,hi'⟩ : ∃ i∈ d, ¬ C i:= not_forall.mp (show ¬∀ i, i∈d→ C i from fun h=> hZ ⟨hp',h⟩)|>.imp fun _=>Classical.not_imp.mp
  rcases hx.shaded i hi' _ _ k (position x (glow Q s.val) U) with hh'|⟨V,HZ,HC,hE⟩
  · have ht y : l*g y≤ W':= by
      rw [hz,← mul_prod_erase _ _ hi, ← mul_assoc]; unfold W'; rw [← mul_prod_erase _ w hi]; exact mul_le_mul (hh' _) (hh _ _) (prod_nonneg fun i _=>stroke_nonneg hr _ _ _ _ _) (hx.favorable _)
    rw [← integral_const_mul]; exact (integral_mono (hg.const_mul l) (integrable_const (μ:=μ) W') ht).trans (le_of_eq (by simp))
  let P':= V.indicator fun _=> W'
  have hb (z) : g z ≤ P' z := by
    unfold P'
    by_cases H : z∈V
    · rw [Set.indicator_of_mem H]; exact (hz z).trans_le (hh z d)
    rw [Set.indicator_of_notMem H,hz,Finset.prod_eq_zero hi (hE z H)]
  refine (mul_le_mul_of_nonneg_left (integral_mono hg ((integrable_const (μ:=μ) W').indicator HZ) hb) (zero_le_one.trans hl)).trans ?_
  rw [integral_indicator HZ,setIntegral_const]; change l*(μ.real _ * W') ≤ _; rw [← mul_assoc]; exact mul_le_of_le_one_left hW HC
end
end YM.PhysicalNext.InteractingRank.Display
