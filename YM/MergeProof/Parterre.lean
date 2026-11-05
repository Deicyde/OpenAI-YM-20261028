import YM.MergeProof.Matter
/-! second section on REAL history & params. stencil union. Fix orientation upstream in ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes){B:Stock.Tabs C.path.levels}{W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D){f:Extraction.Order} {N p d:ℕ} (V:SectionData (C.labels.level d)) (hV:V.Sound C.params)
set_option quotPrecheck false
local notation "K"=> C.path.levels.budget N
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "X"=> V.stencil∪(C.localSection d).stencil
local notation "o"=> (0:Site (C.side N p))
include hV
lemma inviting {b:ℝ} (h:C.Makes)(hN:C.ref d  ≤  N)(he : ∀ y∈ V.stencil∪(C.localSection d).stencil,∀ i:Axis,20*((y i).natAbs+1)  ≤  (C.side N p).val)(hb:Credit V (K).order (K).power b) (hv:0  ≤  b) (u:ℕ→ℝ)(ζ:ℕ→ℕ→ℝ)
    (ha:0 < u N)(hz:0  ≤  ζ d N) (c:Keeper (C.path.rep N p N).p (C.path.rep N p N).activities)
    (hr:let D:=regional X o; D.card*C.path.levels.clock.forcedAllowance N ≤ 1∧coverNumber (K).B D ≤ 81)
    (hs:Real.sqrt (C.path.levels.clock.forcedAllowance N)*storms (BasisCost.price V) (BasisCost.price (C.localSection d)) C N d ≤ 1) (j:(C.labels.level d).Index) :
    let Q:= sphere (C.path.levels.params N) ((V.stencil ∪ (C.localSection d).stencil).card) b; let s:= storms (BasisCost.price V) (BasisCost.price (C.localSection d)) C N d
    let E:=4*(1+(C.path.levels.params N).columns)*Q + Real.exp (((K).supportExponent+2)*81)*s*(ζ d N)*(u N)⁻¹
    ∃ Z t, Cream C N p d u ζ (initial V C.path N p (Size.axis F j) 0) Z Q t E ∧ Z.x= Size.axis F j:=by
   intro Q s E
   let T':= T; let M:= regional X o; let P:=C.path.rep N p N; let R:= K; let J:= C.path.levels.params N; let x:=Size.axis F j; let t':= (C.path.levels.budget N).threshold; let L:=F; let a:=L.scaled t'⁻¹ x; let z:= L.coords.symm a; let y:=V.places a o
   have hp:R.threshold=t':=rfl; have he' : Reads C.params o M z y:=by
      have hu : V.footprint o⊆ M:=Finset.image_subset_image Finset.subset_union_left
      have hx : Nonwrapping M o:=by
         let Y:SectionData L:= ⟨X,0⟩; exact nonwrapping_placement Y o he
      have hz:= fun i h=> he i (Finset.mem_union_left _ h); unfold Reads; rw [if_pos hx]
      have hh:= placed_reads V o hz hV a
      rw [Reads,if_pos (nonwrapping_placement V o hz)] at hh; exact hh
   have hc : T'.footprint o⊆ M:= Finset.image_subset_image Finset.subset_union_right; have hQ : R.Regular (V.footprint o) y ∧ R.supBounds o (V.footprint o) y b :=by
      have he:= BasisCost.analytic V R x o (hb R rfl rfl _ o); rw [show L.coeffSize x=1 from Size.size_axis .., mul_one] at he; exact he
   have hT:(C.path.levels.budget N).Regular (T'.footprint o) (T'.places (L.coords z) o) ∧ R.supBounds o (T'.footprint o) (T'.places (L.coords z) o) J.columns:=by
      have he:= BasisCost.analytic T' R x o (h.priced d N p hN 0); rw [show L.coeffSize x=1 from Size.size_axis ..,mul_one] at he; rw [show L.coords z = a from L.coords.apply_symm_apply _]; exact he
   have hE : V.footprint o⊆ M:= Finset.image_subset_image Finset.subset_union_left
   let i := BasisCost.price V; let w := BasisCost.price T'; let c':= b+J.columns; let v:=Opening.seats C d N; have hi : 0 ≤ i:=zero_le_one.trans (BasisCost.price_pos _); have hw : 0  ≤  w:= zero_le_one.trans (BasisCost.price_pos _); have hZ : 0 ≤  s:= add_nonneg (mul_nonneg hi (seats_nonneg ..)) (mul_nonneg (mul_nonneg zero_le_two hw) (seats_nonneg ..))
   have hPt :0 ≤ c':= add_nonneg hv (zero_le_one.trans J.columns_ge)
   have hα:∀ U,‖y U‖ ≤ i*v:= fun U=> (BasisCost.full V a o U).trans (mul_le_mul_of_nonneg_left ((sits C d N x).trans_eq (by rw [Size.size_axis,mul_one])) hi)
   have hc' : L.scaled t' (L.coords z)=x:= by rw [show L.coords z=a from L.coords.apply_symm_apply _]; exact L.scaled_inv R.threshold_pos.ne' _
   obtain ⟨Y,hY,ht,Hx,hx,hF⟩:= presses N d p M o y c h hN z he' hc (BasisCost.price_pos T') (fun v _ i U=> BasisCost.full T' v i U) hr.1 (regular_larger hQ.1 hE) (mul_nonneg hi (show 0  ≤  v from Opening.seats_nonneg ..)) hα (score:=1) (show L.coeffSize (L.scaled t' (L.coords z))  ≤  1 from hc'.symm ▸ (Size.size_axis ..).le) (bound_sub (regular_larger hQ.1 hE) (regular_larger hT.1 hc) (bound_larger hQ.2 hE) (bound_larger hT.2 hc)) -- wrong equality
   rw [show badCost C d N _ _ _=s from by unfold badCost s storms i v T'; rw [mul_one]] at hx hF; have hy:Y.x=x:=hY.trans hc'; obtain ⟨y',hA,hL⟩:= hF
   let B0:= C.path.levels.clock.forcedAllowance N; refine ⟨Y,quicksilver R M c' s B0,⟨ht,hx,?_,sphere_pos J _ hv, ?_,⟨y',_,hA,?_,hL⟩, ?_,?_⟩,hy⟩
   · rw [hy, show L.coeffSize x=1 from Size.size_axis L j]; have hf : (M.card:ℝ)  ≤  ((X).card:ℝ):=by exact_mod_cast Finset.card_image_le
     let S:= Real.exp (R.supportExponent* (coverNumber R.B M)); let Z:= Real.exp (81*R.supportExponent)
     have hS:S  ≤  Z:=Real.exp_monotone (le_trans (mul_le_mul_of_nonneg_left (show (coverNumber R.B M:ℝ) ≤ 81 from by exact_mod_cast hr.2) R.exponent_pos.le) (mul_comm ..).le)
     change 1+(S*c'+2*(M.card:ℝ)*Real.sqrt B0*(S*s))  ≤  2 + Z*(c'+2*((X).card:ℝ))
     have hz := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg M.card); change (M.card:ℝ)*(Real.sqrt B0*s)  ≤  _ at hz; nlinarith only [hz,mul_le_mul_of_nonneg_left hz (Real.exp_pos (R.supportExponent* (coverNumber R.B M))).le,hf,mul_le_mul hS hf (Nat.cast_nonneg _) (Real.exp_pos _|>.le), mul_le_mul_of_nonneg_right hS hPt]
   · apply le_add_of_nonneg_right; positivity
   · have hR: (YM.Push.Local.reservedMass R M s)  ≤  Real.exp ((R.supportExponent+2)*81)*s:= mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr; exact add_nonneg R.exponent_pos.le zero_le_two; exact_mod_cast hr.2)) hZ
     apply (mul_le_mul_of_nonneg_right hR hz).trans; unfold E; rw [mul_add]; let x:= Real.exp ((R.supportExponent+2)*81)*s
     rw [show u N * (x* ζ d N*(u N)⁻¹) = x*ζ d N from by field_simp]; exact le_add_of_nonneg_left (mul_nonneg ha.le (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one (zero_le_one.trans J.columns_ge))) (sphere_pos _ _ hv).le))
   · intro U; rw [Hx]; let z:ℂ:=(C.S.a N:ℂ)^d; change _ = z*_* (z⁻¹*y U); rw [mul_comm z _,mul_assoc,mul_inv_cancel_left₀]; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
   unfold initial; apply Continuous.const_smul; exact (V.continuous_evaluate _).comp (continuous_pi fun _=>continuous_apply _)
end YM.MergeProof
