import YM.RG05Readout.Address.Forum
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}
variable {C:Family G} {N m p d:ℕ}{δ:E4}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {s t K u τ α c β a:ℝ}{D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hp:Cursor C N m p d s K) (h:C.Makes)(hm:m<N)(hx:SoundDoor (C.path.levels.clock.op m p) D)(hδ: δ∈Native.box)
/-!
# Composing all charges on a physical snapshot
-/
/-!
# Snapshot recurrence per-child

This costs in threshold field column convention, including script letters on
root test. Each inequality holds for the ONE same represented history. Underlying
valuation paths pay separate addressed root counts in the outer application.
-/
variable (o:Site (C.side (m+1) p)) (ho:(C.path.levels.clock.op m p).ratio.parent o=0)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))}(hw:Plot D s K c α β T) (he:MapsTo (fun x=>δ+(((C.path.S.block m).val:ℝ)⁻¹) • x) Native.box Native.box)
local notation "r"=> Native.pull δ ℓ
local notation "Pr"=> Printed C d R 0 (κ m)
local notation "acc"=> aCost d K
local notation "sta"=> stCost d K
include hw he h hm ho
lemma minted {X y:Palette C d} (F':Tape G (C.side (m+1) p))(A:Printed C d M o (κ (m+1)) F' X y t) :
     let W:=F'-Slide X (fun i=>micro C i o M)
     ∃ U:Tape G (C.side m p),∃ x z:Palette C d, Course (D:=D) o (W.comp r) U x z (decay d L K c α*t) (tollV d L K c α β*t) ∧ size x≤ decay d L K c α*t:=by
    intro W
    rcases A with @⟨V,Gp,w,b,T',hV,ht,hp,ht₀,hy,hC⟩; let W'(i:Letter d):=glyph (readJ i 0) (invoice (remove (V i)) o (S (kept i)) M)
    have hK:0 ≤ K:=zero_le_one.trans hw.cursor.fits
    let f i:= sta*(α*w i); let z i :=acc*((2+α)*w i+K*(α*w i)); let Δ:=decay d L K c α
    have hh(i:Letter d):∃ (Z':Tape G (C.side m p))(x y:Palette C d),Course (D:=D) o ((W' i).comp r) Z' x y (f i) (z i) ∧ size x ≤ aCost d K*(α*w i):=by
       obtain ⟨a,hY,-⟩:= hw.star i; let f:= V i
       exact regular_curve hw.cursor h hm (by simpa using he Native.box0) i o ho hY (remove f) (removable o (M) f Y (hV i)) (ht i) rfl hw.a_pos hw.enter
    choose U x y H hF using hh
    have hV(i):0 ≤ w i:=rem_nonneg (ht i)
    let W₁:=∑ i:Letter d,w i; let V₀:=∑ i:Letter d,U i; let V':=∑ i,x i; let Y':=∑ i,y i
    have h0:0 ≤ W₁:=Finset.sum_nonneg (fun i _=>hV i); have hT:= T'.nonneg; have ha:= hw.a_pos; have hb:= hw.b_pos; have hc:= zero_le_one.trans hw.posp; have heK:= aCpos (d:=d) hK; have huK:=sCpos (d:=d) hK; have hℓ :0 ≤ ℓ:=by positivity
    obtain ⟨P,hP⟩:=jewels h hm o ho hw he Gp b T'; have he:= Course.faith hw.cursor h hm hw.door Finset.univ (fun i _=> H i)
    have heq:W.comp r=(∑ i,(W' i).comp r)+(Gp.comp r):=by
       suffices hf: W = (∑ i,W' i)+Gp by rw [hf,LinearMap.add_comp]; congr 1; ext1 φ; simp only [LinearMap.comp_apply,LinearMap.sum_apply]
       unfold W; rw [← hp,add_sub_right_comm]; apply congr_arg (·+Gp); rw [sub_eq_iff_eq_add]; unfold Slide; conv_rhs => rhs; rw [Fintype.sum_sigma]
       unfold together W'; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
       rw [bundle o (S (kept i)) (M) (V i), glyph_plus, core_expands]
       rw [add_comm (glyph (readJ i 0) (∑ _, _))]; apply congr_arg; ext1 φ; rw [glyph_apply,Finset.smul_sum,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [LinearMap.smul_apply]; unfold micro; rw [glyph_apply, ht₀]; exact smul_comm ..
    let s₁:=tollV d L K c α β
    rw [heq]
    have hv:∑ i,f i= (sta*α)*W₁:= by unfold W₁; rw [Finset.mul_sum]; unfold f; simp only [mul_assoc]
    have hz:∑ i,z i =acc*((2+α)+K*α)*W₁ :=by unfold W₁; rw [Finset.mul_sum]; apply Finset.sum_congr rfl (fun i _=> by unfold z; ring)
    rw [hv,hz] at he
    refine ⟨V₀+P,V'+0,Y'+0,(Course.dual hw.cursor h hm hw.door he hP).rise ?_ ?_,?_⟩
    · let x₁:=ℓ*(2*(c+α)); have hx : 0 ≤ Δ:=decays (L) hK hc ha
      apply le_trans _ (mul_le_mul_of_nonneg_left hC hx); rw [mul_add Δ]; apply add_le_add _ (mul_le_mul_of_nonneg_right (show x₁ ≤ Δ from le_add_of_nonneg_left (mul_nonneg (add_nonneg huK heK) ha)) hT); apply mul_le_mul_of_nonneg_right _ h0
      exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right heK) ha).trans (le_add_of_nonneg_right (mul_nonneg hℓ (mul_nonneg zero_le_two (add_nonneg hc ha))))
    · have hz' : 0≤ acc*((2+α)+K*α):=by positivity
      have hb' :0 ≤ℓ*((1+c+β)+(2+α)) :=by positivity
      apply le_trans _ (mul_le_mul_of_nonneg_left hC (add_nonneg hz' hb')); rw [mul_add (acc*((2+α)+K*α)+ℓ*((1+c+β)+(2+α)))]; exact add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb') h0) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hz') hT)
    rw [add_zero]; have hh₁: size V'≤ aCost d K*α*W₁:=by
       refine (size_sum ..).trans ((Finset.sum_le_sum (fun i _=> hF i)).trans_eq ?_); unfold W₁; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> (mul_assoc ..).symm)
    have ht' : aCost d K*α ≤ Δ:= le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left huK) ha) (le_add_of_nonneg_right (mul_nonneg hℓ (mul_nonneg zero_le_two (add_nonneg hc ha))))
    exact hh₁.trans (mul_le_mul ht' ((le_add_of_nonneg_right hT).trans hC) h0 (decays (L) hK hc ha))

-- calibrated per primary stamp choice. Pure add with invariants
lemma stitch (F':Tape G (C.side (m+1) p)) (f f':Palette C d)(θ:ℝ) (hb:Printed C d M o (κ (m+1)) F' f f' θ) {X:Mark C d→Tape G (C.side m p)} {x y:Mark C d→Palette C d} (hs: Swells (D:=D) (T:=T) (δ:=δ) (K:=K) (α:=α) (c:=c) (β:=β) o X x y) :
      let g:=decay d L K c α*θ; let w:=size (amplify d C L f)
      ∃ V:Tape G (C.side m p),∃ l z:Palette C d,Course (D:=D) o (F'.comp r) V l z (margin d c K*w+g) (tollP d K c β*w+tollV d L K c α β*θ) ∧ size (l-Slide f x) ≤ g:=by
     intro g w; obtain ⟨U,u,w',hU,hK⟩:=minted h hm o ho hw he F' hb
     obtain ⟨ha,hp⟩:=all_sheet h hm o hw f hs -- maybe args
     refine ⟨Slide f X+U,Slide f x+u,Slide f y+w',?_,?_⟩ -- Lean infer
     convert ha.dual hw.cursor h hm hw.door hU using 1
     · simp [LinearMap.sub_comp]
     simpa only [add_sub_cancel_left] using hK
end YM.RG05Readout.Address
