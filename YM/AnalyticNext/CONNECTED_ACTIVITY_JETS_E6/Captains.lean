import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern

/-!
# Unforced angular budget at calibrated Calendar

First polymer, *before* mask. All ordered-left derivatives at
 arbitrarily anchored costs. Preserve calibration order; Lean budget
allows smaller given order AND likewise branch arbitrary. Includes Brush ore
for further Uri variants including repeated cluster derivatives.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

structure Captain (H : Cash W s μ L Q o C T R) (j : ℕ) (C' d v W' A b r B q : ℝ) (k : ℕ) (χ:Chi) where
  conduit : Utopia H j v d r C' χ
  oboe : Oboe H j v B k A b conduit
  income : 0 ≤ q
  pot : 0 ≤ W' -- larger than temp
  talent : Pressure.temp s ≤ W'
  position : 0 < v
  balance : 0 ≤ B
  weigh : Sailor G W' q j
  near : j*q ≤ v

variable (N : Captain H j C' d v Y A b r B q k χ)

lemma Captain.sextant (N : Captain H j C' d v Y A b r B q k χ) (i : Molecule S) (hX:X.x=s) (hk:X.width=o.K) (he:X.χ=χ)
    (hv : (roster i).flags=∅) :
    let L (V:Config G c):= fringe (vary X V) W o.a i R Q.table Q.halo
    ∀ V, H.emerging (vary X V) i=masked (Pressure.temp s) (H.unionP i) L V ∧
      (Healthy (Pressure.temp s) (H.unionP i) V → Ore V L v (B*N.conduit.meant i k) j) := by
  intro L V; let Y':= vary X V
  have ht:Y'.x=s:=hX
  have hA := Stained.vows i N.oboe N.position.le ht hk he hv
  have hz (U:Config G c): vary Y' U=vary X U:=rfl
  change (H.emerging Y' i=_) ∧ _; simp_rw [hz] at hA
  refine ⟨hA,fun hy E n m l' U x ha h=>?_⟩
  have hw:= Stained.scenic (X:=Y') i N.oboe N.balance ht hk he hv hy (x:=x) (show Mode U x j v from h) ha
  simp_rw [hz] at hw; exact hw





lemma entrance (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (k:ℕ), Rate G L 0 B ∧
      (∀ m z:ℕ, Rate G L Q.rate (fun x=>shiftG x^(m*i)* B x * Q.overture L μ x (k+m*i+z))) ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        Nonempty (Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) k χ) := by
  obtain ⟨n,h⟩:= Oboe.ell P Q; refine ⟨n, fun L hL D hD i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,B,k,hB,ht⟩:= h L hL D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,k,hb',?_,?_⟩
  · intro m z
    have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    have hh := ((he.pow (m*i)).mul hb').mul (Q.rate_none L hm 0 (k+m*i+z) 0)
    rw [zero_mul,zero_add, zero_add] at hh; exact hh
  filter_upwards [hp,ht] with x hx hD' c f S T hS hT R B' H
  obtain ⟨Ξ,hF⟩:=hD' c f S T hS hT R _ H; have hZ := hZ; have h:= H.laws.data
  exact ⟨Ξ,hF,mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩
end YM.ConnectedActivityE6.Blaze.March
