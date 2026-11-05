import YM.FullVolume.Sector.Aster
/-! Through knotUnt. Canonical rows on actual labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Greenbelt Gas Ursell Trees Blaze.March
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "B₀" => radiusB x₀
local notation "Q'"=> stella Q
variable {V:ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V k)
variable {p:Signal j} {ν α β':ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν) (hM:Margin G L x₀ α δ)
local notation "F₀" => M.mouth ν p
local notation "π"=> spicesF G r L' (V x₀) K j
local notation "Ψp"=> M.payment (k+j) (π) ν α p
set_option quotPrecheck false
local notation "rD"=> M.wonder (π) ν α p (k+j)
local notation "rS" => Captain.reachability (H:=H)
local notation "rL" => stamina (U:=U) (χ:=χ)
abbrev pounds (p: Signal j) (ν V α:ℝ) (k m : ℕ) (i:H.fragrances):ℝ := (shiftG x₀*(1+coverNumber (radiusB x₀) (Captain.reachability i)))^(m*j) * (M.wonder V ν α p k i) * FullVolume.Ray.Weigh.pattern j
variable (ht:2≤v)
-- unforced token interpolation and identification at shared Shot. Note W' powers.
include W' hM hc
lemma w_norm (z:H.fragrances):0≤ rD z:= Ursell.clusters_nonneg _ (fun i=> mul_nonneg (by positivity) (mul_nonneg (by norm_num) (M.paid_sky ..))) _
-- hit at any α below. Need ordinary Ready on these Strong terms. scalar gate
abbrev eureka (Q:Target G P) (G':ℝ) (L:Side) (μ x:ℝ)(j k:ℕ):= (1+2^j*2*G')*(stella Q|>.overture L μ x k)
local notation "Y"=> eureka Q (π) L μ x₀ j (k+j)
lemma edition (m : ℕ) {e:ℝ} (he:0≤e)(hs : e+3*α ≤ Q.exp) (hv: Trees.degreePrice B₀ Y α ≤ 1/2) :
    Ac.Hit rS B₀ (M.pounds p ν (π) α (k+j) m) e (FullVolume.Ray.Weigh.pattern j*(March.collars G α x₀ j m *(Y * (1-1/2)⁻¹))):=by
  let f (i:H.ThinP):= 2^j*(2*Ψp i.val); let y:=Y; let x:= ((Q').overture L μ x₀ (k+j))
  have hp:= H.laws.data; have hg := hp.μ_pos
  have hF : 0<betaF G x₀ L:= (by have h:=H.laws.intake.height; rw [hp.funds.length_eq] at h; linarith)
  have hx:0<x:= (Q').overture_pos _ _ hF
  let z:ℝ:= 2^j*2; have hC:0≤z:=by unfold z; positivity
  have hf i : 0 ≤ f i:= mul_nonneg (by positivity) (mul_nonneg (by norm_num) (M.paid_sky ..)); have hy:=M.spicesF_sound (V x₀); have hh:=hM.hp
  have hr: Trees.Ready H.smallAt B₀ f (e+α) y α (1/2):=by
    have hu' :0 < y:=by unfold y eureka; unfold x at hx; positivity
    refine ⟨hu',hh,hv,by norm_num,hf,fun i=> ?_⟩; have ht := budget_scale hC (M.purchases (α:=α) (k:=k) (V:=V) hc i)
    refine budget_loosen (budget_mono ht ?_ ?_) ?_
    · intro i; split; exact mul_nonneg (hf _) (Real.exp_nonneg _); rfl
    · intro t; split
      next hz =>
        have he : f t=z*(Ψp t.val):=by unfold f z; ring
        rw [he]
        change z*(Ψp _)* Real.exp _ ≤ z*(Ψp _ * _)
        rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left _ (M.paid_sky ..)) hC
        apply Real.exp_monotone; apply mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      rw [mul_zero]
    change z*(π*x)≤(1+z*π)*x; rw [← mul_assoc,add_mul]; exact le_add_of_nonneg_left (by rw [one_mul]; exact hx.le)
  have ht:=add_nonneg he hh.le; let P:=FullVolume.Ray.Weigh.pattern j
  have hZ:0≤ P := by unfold P FullVolume.Ray.Weigh.pattern; exact sum_nonneg fun i _=>zero_le_one.trans (Planned.AtomRegular.polar_one i)
  intro i; let U := March.collars G α x₀ j m; have hb:0≤ shiftG x₀:= by unfold shiftG; positivity
  have hP:0≤ U:=by unfold U March.collars Reserves.polyPrice; positivity
  have hi:=Ursell.log_hit_tail _ _ _ H.testS hr ht 0 i
  rw [pow_zero,mul_one] at hi
  refine budget_mono (budget_scale hZ (budget_scale hP hi)) (fun v=>?_ ) fun v=>?_
  · split; next => unfold pounds; exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (M.w_norm W' hc hM _)) hZ) (Real.exp_nonneg _)
    rfl
  split
  next hz =>
    rw [if_pos (show 0≤v.fst∧i∈ unionOf H.smallAt v.2 from ⟨Nat.zero_le _,hz⟩)]; let d:ℝ:= coverNumber B₀ (rS v); have hD: 0≤d:= Nat.cast_nonneg _
    change (shiftG x₀ * (1+d))^(m*j)* (rD v)*P*Real.exp (e*d) ≤ P*(U*(rD v * Real.exp ((e+α)*d)))
    rw [mul_pow]; unfold U March.collars; rw [add_mul,Real.exp_add]
    have hv : (1+d)^(m*j) ≤ Reserves.polyPrice α (m*j)* Real.exp (α*d):= polynomial_cost hh hD (m*j)
    apply le_trans _ (le_of_eq (show (shiftG x₀^(m*j)*(Reserves.polyPrice α (m*j) * Real.exp (α*d)))*(rD v)*P*Real.exp (e*d)=_ from (by ring))); have hΦ:= w_norm (V:=V) (α:=α) M W' hc hM v; gcongr
  exact (budget_scale hZ (budget_scale hP hi)).1 _
omit W' hM hc
lemma octopus (i:H.fragrances)(V:Config G c) {t:ℝ} (J:Cash W x₀ μ L Q o C T (U.notes t)) (A:Match.Alliance H J 1 0) (hx:A.units=Equiv.refl _) :
    rL i t V= Blaze.March.stream J χ V (A.furrow i):= Match.sale A.bearing (fun i=> fruit (χ:=χ) i t V) _ A.sec (fun i=> light J A hx i V) i
-- Ties use omega at Fleet.
variable {cv:ℝ} {B : BudgetPoint} (hb:B.threshold=Pressure.temp x₀) (hp : B.order≤j) (hV: 0≤cv) (hn:j*cv ≤ u) (hg:Sailor G B.threshold cv j)
include W' hM hc hr M ht hV hn hg hp hb
lemma hailed (i:H.fragrances) (z : Site c) (h:z ∈ rS i) (w:Rung)(η:ℝ) (hh:∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/(v/2))^i)‖≤η):
    B.supBounds z (rS i) (fun V =>FullVolume.Ray.trace w (fun t=>rL i t V)) ((M.pounds p ν (π) α (k+j) B.power i)*η) := by
  let f V := FullVolume.Ray.trace w (fun t=>rL i t V); let r:=coverNumber B₀ (rS i); let z':= (shiftG x₀*(1+r)); have hs :1≤ shiftG x₀:=by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x₀)]
  have hz:1≤z':= one_le_mul_of_one_le_of_one_le hs (by simp); have hh':0≤η:= (norm_nonneg _).trans (hh 0)
  have hQ:0≤FullVolume.Ray.Weigh.pattern j := Finset.sum_nonneg fun i _=> zero_le_one.trans (Planned.AtomRegular.polar_one i)
  refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hz) _) (M.w_norm W' hc hM i)) hQ) hh',?_⟩
  intro A hA l hl hx; have hu:= M.tour W' hc hr hM ht w η hh i A (hb ▸ hA)
  refine (March.costsD (g:=f) (Z:=rS i) ?_ hg hV z _ hn hu («Y»:=z') ?_ hz l (hl.trans hp) hx).trans_eq ?_
  · intro C D ha; apply Finset.sum_congr rfl; intro t _; let J:= U.beams t (U.lay t.property); let hθ:= U.seats t (U.lay t.property); let a:= Match.staple (H:=H) (J:=J) hθ.3 hθ.reg hθ.forced
    -- locality of stamina via leaflet and supports
    refine congr_arg (fun x:ℝ=> w t * x) ?_
    change Gas.term H.seam _ _=Gas.term H.seam _ _; unfold Gas.term; apply congr_arg₂ HDiv.hDiv _ rfl; apply congr_arg; apply prod_congr rfl; intro j' hv
    change fruit _ _ _=fruit _ _ _; rw [light (U:=U) J a rfl _ C, light (U:=U) J a rfl _ D]
    have hx:= a.young (i.2 j'); rw [show Lattice.affine 1 (0:Site c)=id from funext fun u=> by simp [Lattice.affine],image_id] at hx
    apply (Captain.arrived _).2.1 C D
    rw [hx]; exact agrees_mono ha (Finset.coe_subset.mpr (subset_biUnion_of_mem (H.smallAt ∘ i.2) hv))
  · intro x hx; have ht':(separation x z:ℝ) ≤ r * (4*(radiusB x₀:ℝ)+2)+2*(radiusB x₀:ℝ) := by unfold r; exact_mod_cast Lattice.Corona.extent _ _ hx h
    unfold z' shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) (radiusB x₀)]
  unfold pounds z' r; ring
end Lyre
end YM.ConnectedActivityE6.Empire
