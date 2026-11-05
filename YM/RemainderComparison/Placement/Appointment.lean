import YM.RemainderComparison.Placement.Geometry
import YM.RemainderComparison.Timbre.Sequoia
/-!
# Suppliers of a PERIOD aperture (per MARK page)

Uses both same intake at REAL and a genuine unmarked process on the enlarged torus
with the same launch α,K.PathData,P.kernel.Point. No assumption of agreements of
measures/densities at this or the intermediate comparison period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler Bid Legato Stagehands
open Aux Funk Herbal Cadenza Chron
open Further.PhysicalPeriodLimitF933 Macrame Further.PhysicalPeriodLimitF933.Mural RG.Shoot Opera Roost Roof
open JointLoad JointLoad.Heir Deck
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Seedlings BoxOf Timbre WickReps Hymnal
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (F:Factor A)
variable {N m n :ℕ}
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

variable {c f:Side} (h : f.val=c.val*(A.B.a.S.block m).val)
local notation "Ω" => Pane.orchestra A N h
local notation "Ω'" => Pane.panel A m h
local notation "Y'" => F.target j i
set_option quotPrecheck false
variable {ι: Type}[Countable ι]{q e:ℕ} {W:ℝ}
variable (e ι)
-- Model preparation LABEL Texture on AUX receives any paid intake.Assets.R.P. (no movement from original required except H.laws.intake)
variable {R:Rep G f} (H:Chartlet F.shape A N m h R) (hm:m<N)
 include hm H in
lemma bookAux : ∃ He: Chartlet F.shape A N m h (Placement.file R e ι), SeekR F.shape A N m h He:=by
    exact Hymnal.textureAffords F hm h (H.laws.data.room.buys) _ (Placement.attends R _ _ H.laws.intake)
variable {C f' :Side} (hk : f'.val=C.val*(A.B.a.S.block m).val) (r' N' : ℕ)
variable {U : Rep G f} {U' :Rep G f'}(H₀:Chartlet F.shape A N m h U)(K:Chartlet F.shape A N m hk U')
variable (Hu:Chartlet F.shape A N m h (Placement.file U e ι))(Hv:Chartlet F.shape A N m hk (Placement.file U' e ι))
variable (hx: U'.path=U.path) (hb':U'.beta=U.beta) (he:U.path=A.B.kin.path N (m+1)) (ha:U'.p=U.p) (hv: U.p=A.B.a.budget (m+1))(hp:U.beta∈ band A.B.a (m+1))(hβ:0<U.beta)(hβ':0<U'.beta)
variable {W:ℝ}{ι e}
variable (hc:2*(2*r'+3)< c.val)(hC:2*(2*r'+3)<C.val)
local notation "τ"=> Deck.Mint.width (K₀).halo (radiusB δ) (radiusB δ)
variable {α:Type*} (t:α) (D':ι→Tile G α q e W)(o: ι→Site f)(o':ι→Site f')
variable (hpA:2*(r'+Deck.Mint.width (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m)) (radiusB (A.B.a.clock.hatBeta m)))<c.val)(hpB:2*(r'+Deck.Mint.width (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m)) (radiusB (A.B.a.clock.hatBeta m)))< C.val)
local notation "ξ"=> Deck.Mint.width (K₀).halo (radiusB δ) e
local notation "M₀"=> Placement.plants U t D' hβ o
local notation "M₁"=> Placement.plants U' t D' hβ' o'
local notation "Sg"=> Timbre.trumpets Hv
local notation "Sc"=> Timbre.trumpets Hu
local notation "Ph"=> (A.B.a.clock.op m 0).patch
local notation "Kh"=> A.B.a.clock.kernel
variable (u:Site c)(x₁:Site C)
variable (b:Finset ι)(l:ι→ℝ)
-- MARK all on b. offsets in units CORE.
variable (oH: Placement.Center (A.B.a.S.block m) ι)(k:ℕ)
variable (hr: k+Deck.Mint.width (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m)) e ≤ r')
variable (hkn:∀ i'∈b,∀ j',(oH.coarseOff i' j').natAbs ≤ k)
variable (hv₁:∀ iK∈b,Center.atCore (V₀:=(A.B.a.clock.op m 0).patch) oH h u iK=o iK)
variable (hv₂:∀ iK∈b,Center.atCore (V₀:=(A.B.a.clock.op m 0).patch) oH hk x₁ iK=o' iK)
include hm H₀ K hx hb' he ha hv hp hc hC hpA hpB hr hkn hv₁ hv₂
-- Ph.MARK Mesh
set_option maxHeartbeats 600000 in
lemma pointing : BoxOf.ShapeP (P₀) X.p.kernel Hv Hu M₁ M₀ t Sg Sc b b u r' N' l l Set.univ Set.univ 0 0 x₁ 1:=by
    rw [← patchA (n:=0),← A.B.valid.kernel]
    let Cb:= c*C; let Fk:=Cb*A.B.a.S.block m; have he':U'.path=A.B.kin.path N (m+1):= hx.trans he
    have hh : Fk.val=Cb.val*(A.B.a.S.block m).val:=rfl; have h₁: Cb.val=c.val*C.val:=rfl; have h₂: Cb.val=C.val*c.val:= mul_comm ..
    let R:=Pane.virgin (Pane.orchestra A N hh) V U.beta
    obtain ⟨k₁,hK⟩:= Hymnal.modelAffords F hm hh (H₀.laws.data.room.buys.trans (show c.val≤ Cb.val from Nat.le_mul_of_pos_right _ C.pos)) hp
    obtain ⟨ξ',hξ⟩:= Placement.bookAux F hh ι e k₁ hm
    have hz:2≤c.val:=by omega
    have hy:2 ≤ C.val:=by omega -- syntax
    let d:= Center.atCore (V₀:=Ph) oH hh 0
    have hi(iK:ι)(h:iK∈b): separation 0 ((decreed (P:=Ph) hh).parent (d iK))≤ k:= Center.reaches _ _ (hkn iK h) _
    let I:= Placement.plants R t D' hβ d
    obtain ⟨π₁⟩:= H₀.laws.intake.cap.labels.moves 1 ((decreed (P:=Ph) h).embed u); obtain ⟨π₂⟩:= K.laws.intake.cap.labels.moves 1 ((decreed (P:=Ph) hk).embed x₁)
    have hf (n c:Side)(h:n.val=c.val*(A.B.a.S.block m).val)(he:2*(2*r'+3)< c.val):4<n.val:= lt_of_lt_of_le (by omega : 4<c.val) ((Nat.le_mul_of_pos_right _ (A.B.a.S.block m).pos).trans_eq h.symm)
    have ht₀: BoxOf.Mesh (Q:=Kh) (P:=Ph) (h:=show f.val=c.val*(Ph).L.val from h) (H:=show f'.val=C.val*(Ph).L.val from hk) (T:=Pane.orchestra A N h) (T':=Pane.orchestra A N hk) Hv Hu M₁ M₀ t Sg Sc b b u r' N' l l Set.univ Set.univ 0 0 x₁ 1 := by
       refine ⟨Cb,Fk,C.val,c.val,hh,h₁,h₂,hC,hc,hz,hy,Placement.file R e ι,Pane.orchestra A N hh,_,ξ',Timbre.trumpets ξ',ι,I,b,l,Set.univ,0,?_,?_,stampAux F hm hh⟩
       · exact Placement.ports U' R t D' o' d hβ' hβ h₂ Hv ξ' b x₁ l hy (hf _ _ hk hC) (show U'.p=R.p from ha.trans hv) he'.symm hb' rfl hC hpB hr hi (fun iK ht=> (hv₂ iK ht).symm.trans (Center.landing ..|>.symm)) π₂ N' -- arg verify
       exact Placement.ports U R t D' o d hβ hβ h₁ Hu ξ' b u l hz (hf _ _ h hc) hv he.symm rfl rfl hc hpA hr hi (fun iK ht=> (hv₁ iK ht).symm.trans (Placement.Center.landing ..|>.symm)) π₁ N'
    exact ⟨h,hk,rfl,rfl,Pane.orchestra A N h,Pane.orchestra A N hk,rfl,rfl,Hv,Hu,Timbre.trumpets Hv,Timbre.trumpets Hu,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,ht₀⟩
end YM.RemainderComparison.Placement
