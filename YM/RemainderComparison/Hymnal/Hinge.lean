import YM.RemainderComparison.Hymnal.Club
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
local notation "D'" => y j i w
variable (b:ℕ) (hp:(Orbit F (T:=T) w).scope=standard b G (D.L (A.B.a.clock.J (m+1)))) (hm:m<N)
open Trio
include hG hp hm

-- all apertures authorized at post. On any trims pure enough. Actually contains dictionary sector.KP occupancy & AP anchored glyph.View.R.E etc from earlier. Can read plug in PROPOSAL. Epoch. Sail scope a standard profile any b.
variable (S:Stars)
local notation "C" => Trio.fence b (radiusB (A.B.a.clock.hatBeta m)) S
local notation "K"=> (Trio.fence b (radiusB (A.B.a.clock.hatBeta m)) S)*(A.B.a.S.block m)
omit hG hp hm in
lemma alter : (K).val=(C).val* (A.B.a.S.block m).val:=rfl -- unnecessary consumes includes? Lean drops
local notation "Ω"=> Hymnal.alter (A:=A) (m:=m) b S -- order Lean inspect
variable (Ω' : Tree.Forest (Pane.panel A m (show ((Trio.fence b (radiusB (A.B.a.clock.hatBeta m)) S)*(A.B.a.S.block m)).val=(Trio.fence b (radiusB (A.B.a.clock.hatBeta m)) S).val*(A.B.a.S.block m).val from rfl)).ratio)
local notation "W₀"=> Pane.orchestra A N Ω
variable {β:ℝ}(hb:β∈band A.B.a (m+1))
include hb
lemma wings : (∃ H:Chartlet F.shape A N m Ω (Pane.virgin (W₀) V β), SeekR F.shape A N m Ω H) ∧ (Fintype.card (Site C):ℝ) ≤ ((x).scope.siteBill δ)∧
    ∃ ρ:Bid.Dir G C→AxisChart G Ω', Critical Ω' (W₀).high (W₀).up ρ∧ClassicalMatch Ω' (W₀).high (W₀).low (W₀).up (W₀).down ρ∧
     ∀ β, Chartlet F.shape A N m Ω (Pane.virgin W₀ V β)→ ∀ (k:(Pane.panel A m Ω).Choices) (z:Positions (Uniform.Primary C G)), ‖z‖ ≤ (D').R δ → Arc.route G β z∈ Boulevard.sunny B→ Weather W₀ Ω' (K₀).table k ρ (V) β (D').d δ (D').gap (((x).scope).volume δ) (2*(D').R δ) ((D').charge δ) X.p.kernel (asks A m) (r).wind z L:=by
    obtain ⟨I,hI⟩:= Hymnal.modelAffords F hm Ω (Trio.highChair ..|>.2) hb
    obtain ⟨hr,hS⟩:= Hymnal.region b δ C K (Pane.panel A m Ω) (Pane.orchestra A N Ω) (PriceCompiler.block_eq A.B.valid m) Ω' (Trio.taller ..) I.laws.data.room.larger
    have he:(t)=standard b G (D.L j):=hp
    rw [← he] at hS hr
    exact ⟨⟨I,hI⟩,hS,Hymnal.care F y hG w hm Ω Ω' hr⟩
end YM.RemainderComparison.Hymnal
