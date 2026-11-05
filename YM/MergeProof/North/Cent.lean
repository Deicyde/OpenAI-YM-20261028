import YM.MergeProof.North.Vert
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories  Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {G:Gauge} {n:Side} (C:Family G) (J p N j d:ℕ)
local notation "H"=> C.path
variable (a:Site (C.side j p))(hj:j≤N) (hJ:J ≤ N)
local notation "ε"=> C.S.a J
local notation "y"=> (C.S.place a)
include hJ
local notation "T"=> center C.S p hJ 0
-- Margin at given site physical
lemma lat_inside (a : Site (C.side N p))(ha:8*‖C.S.place a‖≤ C.S.a J) : a ∈(T).margin 0 ((T).side.val/8):=by
    let q := (T).side.val
    let w:= lift a
    have hK(i:Axis):8*(w i).natAbs ≤ q:=by
       have hh : (T).units.count=(T).side:=rfl
       have hl (i:Axis): |(C.S.place a) i| ≤ ‖C.S.place a‖:=by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (C.S.place a) i
       have he:= hl i; rw [locC C N p a i] at he
       rw [← C.S.embeds_scale (T).units] at ha; have hy : C.S.a N*((8:ℝ)*(w i).natAbs) ≤ C.S.a N*q:=by linarith only [ha,he]
       exact_mod_cast (le_of_mul_le_mul_left hy (C.S.a_pos N))
    rw [← show wrap (C.side N p) w = a from wrap_lift a] -- use Fit.margin method
    have he (i : Axis) :
        q/8 ≤ (T).coordinated 0 (wrap _ w) i ∧ (T).coordinated 0 (wrap _ w) i+q/8+1≤q := by
      have hp : 0<q := (T).side.property; have hz:= hK i; let z : ℤ := w i + (↑(q/2 : ℕ) : ℤ)
      have ht : 0 ≤ z := by unfold z;omega
      obtain ⟨p₀,hp'⟩ := C.S.toDepth_odd hJ p; change q = _ at hp'
      have hs : q/8 ≤ z.toNat ∧ z.toNat+q/8+1≤q := by unfold z; omega
      have hv : (T).coordinated 0 (wrap _ w) i=z.toNat := by
        unfold Tiling.coordinated; rw [(T).starts_zero]; let B := C.side N p
        have h₀ : wrap B w i - (T).base i = ((z.toNat:ℕ) : Per B) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg ht]
          change (w i : Per B) - (0-((q/2:ℕ):Per B)) = ((w i + (↑(q/2 : ℕ) : ℤ):ℤ): Per B)
          simp only [Int.cast_add,Int.cast_natCast]; ring
        have hm : q<B.val := (T).narrow
        rw [h₀, ZMod.val_natCast_of_lt (by omega : z.toNat < B.val)]
      rw [hv]; exact hs
    refine ⟨fun j => ?_,fun j => he j⟩
    change (T).coordinated 0 (wrap _ w) j < q; have hh := (he j).2; omega
omit hJ
lemma near_center (hC:C.Makes) : ∀ᶠ N:ℕ in atTop,∀ (h:J ≤ N) p (a:Site (C.side N p)),8*‖C.S.place a‖≤ C.S.a J → ∀ v:C.label d,Interior ((center C.S p h 0).chamber 0) (C.O N p v a):=by
    have he (z : Cover) (i : Axis) : ∀ᶠ N in atTop, C.S.a N * (↑(8*((z i).natAbs+1)):ℝ) ≤ C.S.a J := by
       have hv := C.S.shrinks.mul_const ((8*((z i).natAbs+1):ℕ) : ℝ); rw [zero_mul] at hv
       exact hv.eventually (ge_mem_nhds (C.S.a_pos J))
    have hs := eventually_all_finset _|>.2 (fun z (_:z∈(C.localSection d).stencil) => eventually_all.mpr (he z)); filter_upwards [hs] with N h ht p a hp v; let Z:= center C.S p ht 0
    refine Extraction.Around.figure hC Z ⟨_,v⟩ _ _ (lat_inside C J p N ht a hp) (fun z hz i=> ?_)
    have he := h z hz i; have hh : C.S.a N * ((8*((z i).natAbs+1):ℕ):ℝ) ≤ C.S.a N*Z.side.val := he.trans_eq (C.S.embeds_scale Z.units).symm
    have hv : 8*((z i).natAbs+1) ≤ Z.side.val := by exact_mod_cast (le_of_mul_le_mul_left hh (C.S.a_pos N))
    change (z i).natAbs < Z.side.val/8; omega
lemma latzero {p}: C.S.place (0:Site (C.side N p))= 0:=by
    suffices h:‖C.S.place (0:Site (C.side N p))‖=0 from norm_eq_zero.mp h
    refine le_antisymm ((normC C _ _ (0:Site (C.side N p))).2.trans_eq ?_) (norm_nonneg _); simp [separation_self]
end
end YM.MergeProof.Ribbons
