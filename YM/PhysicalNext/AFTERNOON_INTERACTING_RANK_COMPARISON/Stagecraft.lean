import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Furnace
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Station
import YM.SectorNext.RECONNECTED_LOCALITY.Pinned

/-!
# Exact step venue, on actual Families

Both day and night receipts. `commission_epoch` works when
keeping; more generally consume purchases of Poles across actual step
calls in `conductors`, deriving complete Choir. This still needs Heaters
on the indicated Reps, preferably at a restarted stretch from assembling
earlier receipts -- no asserting these on the Bolt automatically,
nor after changing schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws Local RG.Supply Next.Rank.Station Tree
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} (B : Binding C) {N i k p : ℕ}
    {g : Course C N p k} (J : ChartRatio G) (ξ : Purse)
local notation "xK" => Atlas.clim C.path.levels k
local notation "τ" => Atlas.clim C.path.levels i
local notation "u" => Atlas.clim C.path.levels (i+1)
local notation "Z"=> Line ξ.era ξ.goal 0 xK
local notation "T"=> tunnel B N i p
local notation "v"=> ξ.cash xK
local notation "GAS" => Perch.gas ξ.era.coast
local notation "St" => C.path.levels.clock.op i p
local notation "xℓ" => C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "K" => kinetics xK
set_option quotPrecheck false

/-- Numeric admission on Epoch. Inputs § Paid, not later observers. -/
def Ceremony (j : ℕ) (l d : ℝ) := Posts J B.prices C.path.levels.clock.stage C.path.levels.clock.kernel
      (C.path.levels.clock.J j) ξ (C.path.levels.clock.factor (C.path.levels.clock.J j)) l d (Atlas.clim C.path.levels j)

def dressing (G : Gauge) (A : Levels G) (i p : ℕ) (d : ℝ) := d * fiery G (retime (Atlas.clim A i)) (A.clock.op i p).patch.L

/-- Existential gate on unmarked data, at prepared `P,R` on a stretch.

Use the selected
Lantern for Choir. -/
def GalaBurn (l d : ℝ) (k : ℕ) (P : Rep G (C.side (i+1) p)) (R : Rep G (C.side i p)):=
    ∀ A : Boosted T (tell B i) (retime τ), ∃ Y : Lantern G St,Y.χ=Chi.canonical ∧ Y.hood= dressing G C.path.levels i p d ∧
      (∀ (hs : 25*radiusB (retime τ)+30 ≤ R.p.B),∃ D : Allocation G St (retime τ) l,
        Fireplace P R A hs J Y D (ξ.cash (Atlas.clim C.path.levels k)) (load ξ.era) (GAS τ^2)⁻¹
          (Line ξ.era ξ.goal 0 (Atlas.clim C.path.levels k)) (kinetics (Atlas.clim C.path.levels k)/16) (kinetics (Atlas.clim C.path.levels k)/4) (kinetics (Atlas.clim C.path.levels k)))
def ShadingBurn (l d : ℝ) (k : ℕ) (P : Rep G (C.side (i+1) p)) (R : Rep G (C.side i p)):=
    ∀ A : Boosted T (tell B i) (retime τ), ∃ Y : Lantern G St,Y.χ=Chi.canonical ∧ Y.hood=dressing G C.path.levels i p d ∧
      (∀ (hs : 25*radiusB (retime τ)+30 ≤ R.p.B), ∃ D : Allocation G St (retime τ) l,
        Fireplace P R A hs J Y D (Ship.allowance C.path.levels 2 k) ξ.era.coast.e (GAS u)⁻¹ 1 (kinetics (Atlas.clim C.path.levels k)/16) (kinetics (Atlas.clim C.path.levels k)/4) (kinetics (Atlas.clim C.path.levels k)))
-- call assembler
section
variable (c : Course C N p k) (V : (i : ℕ)→ Rep G (C.side i p)) (l d : ℝ)
structure Heaters : Prop where
  dawn i (h : middle C.path.levels ξ.band k ≤ i) (he : i<k): GalaBurn (N:=N) B J ξ l d k (V (i+1)) (V i)
  eve i (_ : Station.width C.path.levels ξ.band k ≤ i) (_ : i<middle C.path.levels ξ.band k) : ShadingBurn (N:=N) B J ξ l d k (V (i+1)) (V i)
-- no Purchase; knows next
end

section volume
-- not requiring a modified scale supposition in lower, purchases eventually for every paid schedule independently
open Asymptotics
def Waxroom (A : Levels G) (ξ : Purse) (k : ℕ) := ∀ i, Station.width A ξ.band k ≤ i→ i<k → ∀ p,100*(1+radiusB (retime (Atlas.clim A i)))≤ (A.S.side i p).val
lemma vault_size (A : Levels G) (hs : G.Simple) : ∀ᶠ k in atTop,∀ (p : Purse), Corridor A p.band p k → Waxroom A p k:= by
  let b:= A.clock.hatBeta; let B:=A.clock.bar
  let d:= G.slopeConstant
  have ht := hat_rate A hs; have hu:= brims
  have hQ (x) : 0 ≤ d * Real.log ((A.S.block x).val):= Work.E04.shift_nonneg G _
  have hZ : Monotone b:= monotone_nat_of_le_succ (fun i=>by unfold b Calendar.hatBeta; rw [Schedule.scale_succ,mul_add]; linarith only [hQ i])
  have hv:∀ᶠ i in atTop, ∀ j,100*(1+radiusB (retime (b i)))≤(A.S.side i j).val:= by
    let w := fun t:ℝ=> (100*(1+4*(B+d*t)))*Real.exp (-t)
    have he : Tendsto w atTop (𝓝 0):= by
      have hp:Tendsto (fun pA:ℝ=> pA * Real.exp (-pA)) atTop (𝓝 0):= by simpa only [pow_one,one_mul,Real.exp_neg, div_eq_mul_inv] using! (isLittleO_pow_exp_pos_mul_atTop 1 zero_lt_one).tendsto_div_nhds_zero
      have hv:Tendsto (fun pA:ℝ=> Real.exp (-pA)) atTop (𝓝 0):=Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr tendsto_id)
      have hx:=(hp.const_mul (400*d)).add (hv.const_mul (100*(1+4*B))); rw [mul_zero,mul_zero,add_zero] at hx
      exact hx.congr fun a=>show _= w a from (by unfold w; ring)
    filter_upwards [he.comp A.S.divergent |>.eventually (ge_mem_nhds zero_lt_one), ht.eventually ((Work.E09.radiusB_small 1 zero_lt_one 1).def zero_lt_one), ht.eventually hu] with i hi hf hv p
    let pA:= A.S.denominator i
    have h':0<b i:=zero_lt_one.trans (A.fits.delayed i)
    have h0 : (radiusB (b i):ℝ) ≤ b i:= by change 0<A.clock.hatBeta i at h'; unfold b; simpa only [Real.rpow_one,pow_one,one_mul,Real.norm_of_nonneg h'.le,Real.norm_of_nonneg (Nat.cast_nonneg _)] using! hf
    have hp:(100:ℝ)*(1+4*b i) ≤ (pA.val:ℝ):= by
      let w:= A.S.scale i
      change 100*(1+4*b i)*Real.exp (-w)≤ 1 at hi
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _),one_mul] at hi
      have hh : Real.exp w=(pA.val:ℝ):= by
        unfold w Schedule.scale; rw [Real.exp_log (inv_pos.mpr (A.S.a_pos _)),Schedule.a,inv_inv]
      rw [← hh]; exact hi
    have hx : (radiusB (retime (b i)):ℝ) ≤ 4 * b i:= le_trans (show _ ≤ (4:ℝ)*(radiusB (b i):ℝ) by exact_mod_cast hv.2) (mul_le_mul_of_nonneg_left h0 (by norm_num))
    refine le_trans (b:=pA.val) ?_ (Nat.le_mul_of_pos_left _ (A.S.period p).property)
    exact_mod_cast (show (100:ℝ)*(1+radiusB (retime (b i))) ≤ pA.val from by linarith only [hx,hp])
  obtain ⟨j,hj⟩:= eventually_atTop.mp hv
  filter_upwards [ht.eventually (eventually_gt_atTop (2*b j))] with k hk p hp i hi hi' pA
  refine hj i ?_ pA; by_contra! h; have hh:b i ≤ b j:= hZ h.le
  have hf:b k/2 ≤ b i:= hp.court i hi hi'.le |>.1; change _<b k at hk; linarith only [hh,hf,hk]
end volume

variable (m : C.Makes)
section access
variable (hP : Corridor C.path.levels ξ.band ξ k)
include hP
lemma sizes_at (hh : Station.width C.path.levels ξ.band k ≤ i) (ht : i<k) (p : ℕ) : (C.path.levels.clock.op i p).patch.L=xℓ ∧ (C.path.levels.clock.op i p).patch.J=C.path.levels.clock.J k := by
  have hx:=hP.heft.plateau (i+1) (hh.trans (Nat.le_succ _)) ht
  exact ⟨hx ▸ (C.path.levels.fits.sameFactor _).symm,hx⟩

variable {l d : ℝ}
include m hP
structure Mast (g : Course C N p k) (V : (i : ℕ)→ Rep G (C.side i p)) (J : ChartRatio G) (l d : ℝ) (ξ : Purse) (n i : ℕ) : Prop where
  A : Boosted (tunnel B N i p) (tell B i) (retime (Atlas.clim C.path.levels i))
  height : 0< dressing G C.path.levels i p d ∧ 2 * dressing G C.path.levels i p d < firstRadius G
  chimes : TimeBand ξ.era ξ.goal (C.path.levels.clock.op i p).patch.L (V (i+1)).p (V i).p (Atlas.clim C.path.levels i) (Atlas.clim C.path.levels (i+1)) xK n
  feasible (Y : Lantern G (C.path.levels.clock.op i p)) (hf : Y.hood=dressing G C.path.levels i p d) (D : Allocation G (C.path.levels.clock.op i p) (retime (Atlas.clim C.path.levels i)) l) : Coupler (tunnel B N i p) Y J D (V (i+1)).beta




end access
section assemblage
variable (V : (i : ℕ)→ Rep G (C.side i p)) {n : ℕ} (X : Points n) (hf : Fit C.path.levels ξ.band k X) (hP : Corridor C.path.levels ξ.band ξ k)
include m hP hf
-- same Course, enough if from any purchaser of its m-moment/Dawn (see commission_epoch when keeping).

end assemblage
end YM.PhysicalNext.InteractingRank
