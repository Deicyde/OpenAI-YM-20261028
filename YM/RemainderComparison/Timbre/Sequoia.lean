import YM.RemainderComparison.Hymnal.Fair
import YM.RemainderComparison.Timbre.Spect
import YM.RemainderComparison.Nursery.Award
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Hymnal
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler Bid Legato Stagehands
open Aux Funk Herbal Cadenza Chron
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural RG.Shoot Opera Roost Roof
open JointLoad JointLoad.Heir
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (F:Factor A)
variable {N m n :ℕ}
-- ALL output geometry R certificates apply
local notation "i" => A.B.a.clock.J m
local notation "j" => A.B.a.clock.J (m+1)
local notation "K₀" => F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "p" => A.B.a.clock.op m n
local notation "G'" => ships A.B N m n
local notation "P₀" => slot A m
local notation "σ" => F.span j i
local notation "Z" => F.prices j i
local notation "Y" => F.shape.o j i
local notation "B" => A.B.a.budget m
local notation "V" => A.B.a.budget (m+1)
local notation "δ" => A.B.a.clock.hatBeta m

variable {T: Contemple G}
local notation "W'"=> Stagehands.atlas F T
local notation "L" => D.L (A.B.a.clock.J (m+1))
set_option quotPrecheck false
local notation "E'"=> X.p.profile (A.B.a.clock.J m)
variable (y:Book (Stagehands.atlas F T))
variable (hG:Pillar (Stagehands.atlas F T) F.prices F.span F.recordP F.shape T A.delay y)
variable (w : Fin ((Stagehands.atlas F T).count (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)))
local notation "x" => (W').slots j i w
local notation "t"=> (x).scope
local notation "r" => Glint.award (x) E' (Glint.partition E' (K₀).exp)
variable {R : Rep G (A.B.a.S.side (m+1) n)}(hm:m<N) (hl:Lives A.B.bake N (m+1) n R)(hβ:R.beta∈band A.B.a (m+1))
variable {c f:Side} (h : f.val=c.val*(A.B.a.S.block m).val)
local notation "Ω" => Pane.orchestra A N h
local notation "Ω'" => Pane.panel A m h
local notation "Y'" => F.target j i

open Seedlings BoxOf Timbre WickReps
-- concrete ROOTS certificate on all auxiliary + real under orientation-general allocations. R₀ actual unmarked. Supply material from formal Atlas.
variable {C f' : Side} (hk : f'.val=C.val*(A.B.a.S.block m).val) (r' N' : ℕ)
variable {U : Rep G f} {U' :Rep G f'} (H:Chartlet F.shape A N m h U) (K:Chartlet F.shape A N m hk U')
variable (hx: U'.path=U.path) (hb':U'.beta=U.beta) (he:U.path=A.B.kin.path N (m+1)) (ha:U'.p=U.p) (hv: U.p=A.B.a.budget (m+1))(hp:U.beta∈ band A.B.a (m+1))
variable (hc:2*(2*r'+3)< c.val)(hC:2*(2*r'+3)<C.val)
local notation "τ"=> Deck.Mint.width (K₀).halo (radiusB δ) (radiusB δ)
variable (hpA:2*(r'+Deck.Mint.width (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m)) (radiusB (A.B.a.clock.hatBeta m)))<c.val)(hpB:2*(r'+Deck.Mint.width (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m)) (radiusB (A.B.a.clock.hatBeta m)))< C.val)
variable {α:Type*}{ι κ:Type}(J:ι→Typeface.Portrait U' α)(D':κ→Typeface.Portrait U α)(z':α)(l:ι→ℝ)(l':κ→ℝ)(o':Site c)(d:Site C)(P:Set ι)(Yb:Set κ)(Z₁ Z₂:ℝ) -- D' notation conflict
local notation "Sg"=> Timbre.trumpets K
local notation "Sc"=> Timbre.trumpets H
local notation "Ph"=> (A.B.a.clock.op m 0).patch
local notation "Kh"=> A.B.a.clock.kernel
include hm hx hb' he ha hv hp hc hC hpA hpB
set_option maxHeartbeats 900000 in
lemma quintet : BoxOf.ShapeP (P₀) X.p.kernel K H J D' z' Sg Sc ∅ ∅ o' r' N' l l' P Yb Z₁ Z₂ d 1:=by
    rw [← patchA (n:=0),← A.B.valid.kernel]
    have he':U'.path=A.B.kin.path N (m+1):= hx.trans he
    let Cb:= c*C; let Fk:=Cb*A.B.a.S.block m
    have hh : Fk.val=Cb.val*(A.B.a.S.block m).val:=rfl; have h₁: Cb.val=c.val*C.val:=rfl; have h₂: Cb.val=C.val*c.val:= mul_comm ..
    let u₀:=Pane.virgin (Pane.orchestra A N hh) V U.beta
    obtain ⟨k,hK⟩:= modelAffords F hm hh (H.laws.data.room.buys.trans (show c.val≤ Cb.val from Nat.le_mul_of_pos_right _ C.pos)) hp
    have heA :2≤c.val:=by omega
    have heB : 2≤ C.val:=by omega
    let S': PEmpty→ Typeface.Portrait u₀ α:= fun q=> q.elim
    have ht₀: BoxOf.Mesh (Q:=Kh) (P:=Ph) (h:=show f.val=c.val*(Ph).L.val from h) (H:=show f'.val=C.val*(Ph).L.val from hk) (T:=Pane.orchestra A N h) (T':=Pane.orchestra A N hk) K H J D' z' Sg Sc ∅ ∅ o' r' N' l l' P Yb Z₁ Z₂ d 1 := by
       refine ⟨Cb,Fk,C.val,c.val,hh,h₁,h₂,hC,hc,heA,heB,u₀,Pane.orchestra A N hh,_,k,Timbre.trumpets k,PEmpty,S',∅,fun _=>0,∅,0,?_,?_,stampAux F hm hh⟩
       · exact Timbre.ports h₂ heB k K rfl he'.symm (ha.trans hv).symm hb'.symm S' J z' r' N' _ _ _ _ _ _ hpB _ -- args inspect
       exact Timbre.ports h₁ heA k H rfl he.symm hv.symm rfl S' D' z' r' N' _ _ _ _ _ _ hpA _
    exact ⟨h,hk,rfl,rfl,Pane.orchestra A N h,Pane.orchestra A N hk,rfl,rfl,K,H,Timbre.trumpets K,Timbre.trumpets H,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,ht₀⟩
end YM.RemainderComparison.Hymnal
