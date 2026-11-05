import YM.RG05Readout.Weave.Graph
/-!
# Physical marked density evaluated on all preimages

Test-address evaluation by pullback at centered residue. No assuming
multiplicative replacements through this step. Full-volume lift pinned to
original `M` even across these equality-based arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical Offsets OPE Copper
open Push Local MergeProof
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}
section
variable (C:Family G)
variable (p m N d:ℕ)
set_option quotPrecheck false
local notation "Φ"=> C.path
local notation "M"=> C.path.rep N p
local notation "L"=> C.path.S.block m
local notation "W"=> C.path.levels.clock.op m p
local notation "H" => Bud C p m
-- use only on actual `F : Body`.
def pulseOut {n:Side} (P:Tape G n) (f:Native.Body): Goods G n:= (P f).1

def journey (P:Native.Body→ Goods G (C.side (m+1) p)) (f : Native.Body) : Goods G (C.side m p):=
   average (fun i:Bud C p m=> blast C.path N p m d ((P ((Native.pull (displacement C p m i) (((L).val:ℝ)⁻¹)) f)) ∘ Lattice.pull (1:Signed) (child C p m i)))
lemma proceeds (P:Tape G (C.side (m+1) p))(Q:Tape G (C.side m p))(f : Native.Body)
    {D:GaugeDoor (M (m+1)) (M m)} {u:billStart C p m N} {x:ℝ}(hp:Train (d:=d) D u P Q x):pulseOut Q f=journey C p m N d (pulseOut P) f:=by
   obtain ⟨c,hc,hq⟩:=hp; obtain ⟨b,hb,Hf⟩:= Native.Cap.cost f (d+2); have hi(i):=((hc i) f b Hf).exactStep -- i notation
   rw [hq]; have he:pulseOut (average c) f=average (fun i=>pulseOut (c i) f):=by
     unfold average pulseOut; simp only [LinearMap.smul_apply,LinearMap.sum_apply]; change (Fintype.card (H):ℂ)⁻¹ • (∑ i, c i f).1= _; rw [Prod.fst_sum]
   rw [he]; unfold journey; exact congr_arg average (funext hi)
end
section graph
variable {C:Family G} {p b m N d:ℕ}
variable (h:C.Makes){D:Rail C}{B:ℕ→ℕ→ℝ}{V:Sight C d p} {r:Emblems C d} (ht:Spine D B h b p d N V r)
include ht
lemma travels (hm:m<N)(hp:b ≤ m)(f:Native.Body)(x:Palette C d) : pulseOut (V m (r m x)) f=journey C p m N d (pulseOut (V (m+1) x)) f:= proceeds C p m N d _ _ f ((ht.follows m hp hm).goes x)
end graph
end YM.RG05Readout.Address
