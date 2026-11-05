import YM.MergeProof.Dollars
import YM.MergeProof.StrawS

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D){f:Extraction.Order}
set_option quotPrecheck false
variable {N p d:ℕ}
-- issue from afterL delay and permits. actual
structure Fridge (C:Family G) (u:ℕ→ℝ)(ζ:ℕ→ℕ→ℝ):Prop where
    full:∀ N p,Nonempty (Keeper (C.path.rep N p N).p (C.path.rep N p N).activities)
    candle : ∀ i, 0 < u i
    path : ∀ f,Slow C f fun i=> (u i.1)⁻¹
    smoke d : ∀ f,Slow C f fun i=> ζ d i.1
    shifts : ∀ f,shiftCosts C f
variable (hG:G.Simple)
include hG
lemma freezes (h:∀ N p:ℕ,Nonempty (Keeper (C.path.rep N p N).p (C.path.rep N p N).activities))(hp:∀ i,jump (C.path.levels.budget i) ≤ C.path.levels.clock.hatBeta i) : Fridge C (far C.path.levels) (fly C.path.levels):=by
    let a:=C.path.levels; let b:= a.clock.hatBeta; have hx(i:ℕ):0 < b i:= zero_lt_one.trans (a.fits.delayed _); have hP (i:ℕ):0 < far a i:= div_pos (inv_pos.mpr (Real.sqrt_pos.mpr (hx i))) (by norm_num); refine ⟨h,hP,fun f=> ?_,fun d f=> ?_,fun f=>?_⟩
    · 
      have he:= (Slow.const (C:=C) (f:=f) (4:ℝ)).mul (coupling_price hG); apply he.reduce; refine Eventually.of_forall fun i=> le_of_eq ?_
      change ‖((Real.sqrt (b i.1))⁻¹/4)⁻¹‖= ‖4*(Real.sqrt (b i.1))⁻¹⁻¹‖
      simp only [inv_inv,inv_div]; field_simp
    · apply (Slow.const (C:=C) (f:=f) (1:ℝ)).reduce; refine Eventually.of_forall fun i=> ?_
      have hv:0 < fly a d i.1:=inv_pos.mpr (pow_pos (hx _) _); rw [Real.norm_of_nonneg hv.le,norm_one]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (a.fits.delayed _|>.le))
    exact (beta_slow hG).below (Eventually.of_forall fun i=>⟨by unfold RelayDifference.jump; positivity,hp i.1⟩)
include H B h
variable (hF:Fridge C u ζ)
include hF
lemma onions (Z:Trial C) (hp:RawProtected C f Z d)(hZ:Stencilled f Z)(hz:∀ᶠ i in f.fuse,Continuous (Z i.1 i.2 0)) : vet C f d Z:=by
    obtain ⟨E,hE,HZ⟩:= persists H hG hF.full (roof_of_tabs B) hF.candle (hF.path _) (hF.smoke d _) (fun i hi=>(h.grows d i hi).le) hp hz; obtain ⟨v,hv,hV⟩:= served_dollar H B h hE hZ HZ; exact ⟨v,hv,hV.closes H (by norm_num)⟩
theorem thyme (x:C.label d)(k:ℕ)(hk:d ≤ k):vet C f k (visits C d x):= onions H B h hG hF _ (RawProtected.visits H hG x hk) (Stencilled.visits H x) (Eventually.of_forall fun i=> C.continuousO ..)
theorem lofty (x:C.label d)(a:Axis):vet C f (d+1) (heighten C d x a):= onions H B h hG hF _ (RawProtected.heighten H hG x (hF.shifts f) a) (Stencilled.heighten H x a) (Eventually.of_forall fun i=> ((C.continuousO i.1 i.2 _ _ (0+step a)).sub (C.continuousO ..)).const_smul _)
end YM.MergeProof
