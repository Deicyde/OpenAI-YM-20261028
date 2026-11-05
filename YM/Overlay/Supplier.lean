import YM.Cells.Proximity
import YM.Extraction.Center
import YM.Overlay.Terminal

/-!
Counters: `Targets` for actual Family C; no p in costs on requested full-grid
bound, but witnesses of transfer needed for every admitted p. Feasibility of
the cost scaling as m increases is testable here on the ACTUAL program. Do not
assume from any estimate with constant depending on N,p or arity. Lanes needn't
project singleton correspondence for this application (do use that separately
for discrepancy/calibration). Transfer from hierarchically aligned center.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Stock
open Lattice Wilson RG Marker Cells MeasureTheory Filter Set Function Overlay Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal ContDiff

variable {G : Gauge} {C : Family G}

structure Foot where
  stop : ℕ
  w : ℝ
  u : ℝ
  c : ℝ
  d : ℝ
  b : ℝ
  reserve : 0 < w

namespace Foot

def bill (x : Foot) (C : Family G) (m d : ℕ) := expPrice C m x.stop d x.w x.u x.c x.d x.b

/-- The producer from E needs to deliver such lanes before extraction. Calls
with arbitrary center alignment *not* needed for this first bound. Embedded
origins in Bands included so L may use mix step and test positions/placement.
If constructing with larger arrays or marker alternatives, prove covers from
those (needed in other applications). -/
def services (x : Foot) (C : Family G) (d m : ℕ) (r : ℝ) := m ≤ x.stop ∧
    ∀ᶠ N in atTop, ∃ hN : m≤N, ∀ (p) (v : C.book.Ref d), ‖v‖ ≤ r →
    ∃ L : Lane C.path (census (Site (C.side m p))) N p,
      L.Works x.stop ∧ (L.sites x.stop).Radial (fun _ => x.w) x.u x.c x.d x.b ∧
      ∀ i,L.load i=d ∧ L.uses i=(Cells.center C.S p hN 0).copy i (C.O N p (d:=d) v 0) ∧
        (L.sites N).origins i=(Cells.center C.S p hN 0).copyMap i 0
end Foot

structure Stops (C : Family G) : Prop where
  works (d) (r : ℝ) (h : 0<r) : ∃ F : ℕ → Foot,
    (∀ m, C.ref d≤m → (F m).services C d m r) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,(F m).bill C m d ≤ ((d:ℝ)+ε)*C.S.scale m

lemma centered_margin {S : Schedule} {m N} (p : ℕ) (hn : m ≤ N) (o : Site (S.side N p)) :
    o ∈ (Cells.center S p hn o).margin 0 ((S.toDepth hn p).count.val/2) := by
  refine ⟨base_point S hn o,fun i => ?_⟩
  let T:= Cells.center S p hn o
  let H:= S.toDepth hn p
  change _≤T.coordinated 0 o i ∧ T.coordinated 0 o i+_+1≤H.count.val
  rw [Tiling.coordinated,Tiling.starts_zero]
  rw [show o i -T.base i= ((H.count.val/2:ℕ):Per (S.side N p)) by unfold T Cells.center; simp; rfl]
  have he : H.count.val≤(S.side N p).val := T.narrow.le
  have hh := S.toDepth_odd hn p; change Odd H.count.val at hh
  obtain ⟨u,H1⟩ := hh
  have HH := H.count.property
  rw [ZMod.val_natCast_of_lt (by omega)]; change H.count.val/2 ≤ _ ∧ _+H.count.val/2+1≤H.count.val;omega

lemma clear_interior (C : Family G) (H : C.Makes) (m d : ℕ) : ∀ᶠ N in atTop, ∃ hn : m≤N,
    ∀ p : ℕ, ∀ x : Site (C.side N p), ∀ F : C.book.Ref d, Interior ((Cells.center C.S p hn x).chamber 0) (C.O N p (d:=d) F x) := by
  have he (z) (_ : z∈(C.localSection d).stencil) (j : Axis) : ∀ᶠ N in atTop,
      C.S.a N*(2*((z j).natAbs+1):ℝ)<C.S.a m := (show Tendsto (fun N => C.S.a N*(2*((z j).natAbs+1):ℝ)) atTop (𝓝 0) from by
        simpa only [zero_mul] using C.S.shrinks.mul_const _).eventually (gt_mem_nhds (C.S.a_pos _))
  have hv := eventually_all_finset _ |>.mpr (fun z (hz:z∈(C.localSection d).stencil) => eventually_all.mpr (he z hz))
  filter_upwards [hv,eventually_ge_atTop m] with N HN hn; refine ⟨hn,fun p x F => ?_⟩
  have hc := C.continuousO N p _ F x
  refine ⟨C.invariant H _ _ _ _ _,hc.measurable,fun u U H => ?_,hc.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
  refine C.localO N _ _ _ _ _ _ (agrees_mono H ?_)
  intro z hz; obtain ⟨y,hY,rfl⟩ := Finset.mem_image.mp hz
  refine Tiling.fits_stencil _ (centered_margin p hn x) fun j => ?_
  let t := C.S.toDepth hn p
  have hh := (HN y hY j).trans_eq (C.S.embeds_scale t).symm
  change C.S.a N*(2*((y j).natAbs+1):ℝ)< _ at hh
  have he := lt_of_mul_lt_mul_left hh (C.S.a_pos _).le
  have hx : 2*((y j).natAbs+1)<t.count.val := by exact_mod_cast he
  change _< t.count.val/2;omega

lemma Stops.centering (Y : Stops C) (H : C.Makes) : Wcmain C := by
  intro d A ε hA hε
  obtain ⟨F,hτ,he⟩ := Y.works d A hA
  obtain ⟨m,hm⟩ := eventually_atTop.1 (he ε hε)
  have zone (p : ℕ) : Real.exp (((d:ℝ)+ε)*C.S.scale p) = C.S.a p^(-(d:ℝ)-ε) := by
    rw [Real.rpow_def_of_pos (C.S.a_pos _)]; unfold Schedule.scale; rw [Real.log_inv]; ring_nf
  let X := Finset.range m
  let R (i) := Real.exp ((F i).bill C i d) / Real.exp (((d:ℝ)+ε)*C.S.scale i)
  let W := 1+∑ i∈X,R i
  have hr (i) : 0 ≤ R i := by unfold R; positivity
  have hw : 1≤ W := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hr i)
  refine ⟨W,zero_le_one.trans hw,fun M ha => ?_⟩
  obtain ⟨_,h⟩ := hτ M ha
  have he : Real.exp ((F M).bill C M d) ≤ W*C.S.a M ^(-(d:ℝ)-ε) := by
    rw [← zone]
    rcases lt_or_ge M m with h|h
    · rw [← div_le_iff₀ (Real.exp_pos _)]
      change R M ≤ W
      exact (Finset.single_le_sum (fun i _ => hr i) (Finset.mem_range.2 h)).trans (le_add_of_nonneg_left zero_le_one)
    exact (Real.exp_monotone (hm M h)).trans (le_mul_of_one_le_left (Real.exp_pos _).le hw)
  filter_upwards [h,clear_interior C H M d] with N hN hh p v hv
  obtain ⟨hn,hu⟩ := hh
  obtain ⟨L,hx,hY,hW⟩ := hN.choose_spec p v hv
  refine ⟨hn,ha.trans hn,fun i => ⟨hu p i v,?_⟩⟩
  change Tiling.rootTest (Cells.center C.S p hn i) (C.beta N p) (C.O N p v i) ≤ _
  rw [translate_s hn i ⟨d,v⟩ (hu p 0 v)]
  exact (est hn H ⟨d,v⟩ L hx _ _ _ _ _ hY (F M).reserve (fun i => (hW i).1) (fun i => (hW i).2.1)).trans he
end YM.Stock
