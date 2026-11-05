import YM.RemainderComparison.Hymnal.Hinge
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
open JointLoad.Heir.Suite
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (F:Factor A)
variable {N m n :ℕ}
-- ALL scales calendar with any sequence of L-post producer estimates. For unmanifest authorization.Taxis.Solo.γ inherited.L independently chosen by this consultant using profiles and J. Salient exposures ph.Sync.
-- any fixed marker roster level.Internal r chooses companions through actual parameters. Inputs rendered by macrophys RU+RG02 using these ranks/walls etc.
structure Aims (G:Gauge)(L: Side) where
   scope : ℕ
   songs : Songbook G L
   arity : ℕ
   rumors : ℕ
   rank : ℕ
   ε : ℝ -- absolute stiffness target for older e (additional share besides C0 gate)
   fee : ℝ→ℝ
   heat : Reserve G L fee
   crucial : 0<ε
   bonus : Chron.Boost G L
structure Dynamics (G:Gauge) where
   ν : ℕ→ℕ→RG.Stage→RG.Stage→ℝ
   tall : ∀ i j E E',0<ν i j E E'
   lighting {M: Sheet G}{K:MapPrices}{D:Rolls M}{V:Targets M K}{X:Expenses V}{p:ℕ→ℝ}{v:Return.Wages}(F:PhysicalNext.Repeat.Register D X v p)(Y:PostCost D)(C:Programs M)(k:ℕ→ℕ→ℕ) (d:ℕ→ℕ→JointLoad.Heir.Record) (h:Protection D)(j i:ℕ) (x: Fin (i+1)): Aims G (D.L j)
-- provide default camp later
namespace Dynamics
variable (V : Dynamics G)
def cultivate : Chron.Contemple G:= ⟨V.ν,V.tall,fun F Y C r d h=> ⟨fun _ i=>i+1,fun j i k=>
   let p:= V.lighting F Y C r d h j i k
   ⟨standard p.scope G _,p.songs,k.val,p.arity, i+1,p.rank,p.rumors,(i+1:ℝ)⁻¹,p.ε,p.fee,p.heat,by positivity,p.crucial,p.bonus⟩⟩⟩
local notation "P"=> V.cultivate
local notation "J"=> A.B.a.clock.J m
local notation "I"=> A.B.a.clock.J (m+1)
def rose (V:Dynamics G) (p:ℕ)(hp:p ≤ A.B.a.clock.J m) : Fin ((Stagehands.atlas F V.cultivate).count (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)):= ⟨p,(by exact Nat.lt_succ_iff.mpr hp)⟩
local notation "Y"=> F.shape
local notation "δ"=> A.B.a.clock.hatBeta m
local notation "Z"=> F.target I J
variable {p :ℕ} (hp:p ≤ A.B.a.clock.J m)
variable {R:Rep G (A.B.a.S.side (m+1) n)}
set_option quotPrecheck false
local notation "₰"=> rose F V p hp
local notation "U"=> V.lighting F.shape A.post F.prices F.span F.recordP A.θ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (⟨p,Nat.lt_succ_iff.mpr hp⟩)
lemma lit : (Orbit F (T:=V.cultivate) ₰).scope= standard (U).scope G _ ∧ (Hymnal.Rental F (T:=V.cultivate) ₰).p=p:=⟨rfl,rfl⟩
variable (b:Book (Stagehands.atlas F V.cultivate))(h: Pillar (Stagehands.atlas F V.cultivate) F.prices F.span F.recordP F.shape V.cultivate A.delay b)
local notation "ϕ"=> b I J ₰
local notation "Υ"=> Hymnal.Rental F (T:=V.cultivate) ₰
local notation "X₀"=> Hymnal.Orbit F (T:=V.cultivate) ₰
local notation "Πx"=> Cadenza.royale (slot A m) Υ (X₀).propAim (X₀).scope (X.p.profile J) ϕ δ
variable (hl:m<N)(he:Lives A.B.bake N (m+1) n R) (hc:R.beta∈band A.B.a (m+1)) {η :ℝ}
include h hl he hc
lemma affording :
    ∀ ε:ℝ, (A.B.a.clock.J m+1:ℝ)⁻¹ ≤ ε→ 0 < gStep R.beta ∧
     (gStep R.beta) ≤ 1 ∧ 0< Πx ∧ Πx * (gStep R.beta)^(p+1) ≤ gStep R.beta^(((p+1:ℕ):ℝ)-ε) := by
   intro ε hε
   have ht := (Hymnal.pref F b h ₰).2.2.2.expenses _ (A.B.valid.pays m)
   have hD : inBand (betaF G δ (slot A m).L) R.beta:= by change inBand (betaF G δ (D.L I)) _; rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hc
   obtain ⟨hb,hp',hf,hV⟩:=ht.active R.beta _ (Hymnal.budgets F hl he hc).2.2 hD
   obtain ⟨I',hI⟩:=Beacon.begins F hl he hc
   let g:=gStep R.beta; have hg: 0<g:= (Fare.gS _ I'.laws.intake.positive).1
   have hu := hV.shade; have hz := hV.gains
   refine ⟨hg,hb.coup,hz,le_trans ?_ (le_trans hu ?_)⟩
   · have hl : Πx*g^(p+1)≤ g^(p+1)*(1+|(U).fee δ|) * Πx:= by
        rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ hz.le; exact le_mul_of_one_le_right (pow_nonneg hg.le _) (le_add_of_nonneg_right (abs_nonneg _))
     exact hl
   apply Real.rpow_le_rpow_of_exponent_ge hg hb.coup (show ((p+1:ℕ):ℝ)-ε ≤ ((p+1:ℕ):ℝ)-(A.B.a.clock.J m+1:ℝ)⁻¹ from sub_le_sub_left hε _)

omit h hl he hc
lemma arches (η:ℝ) (hη:0<η)(p:ℕ)(A: Alloy X D): ∀ᶠ m in atTop, p ≤ A.B.a.clock.J m ∧ (A.B.a.clock.J m+1:ℝ)⁻¹ ≤ η :=by
  have h:= A.B.a.fits.deep; have hc : Tendsto (fun n:ℕ=> (A.B.a.clock.J n+1:ℝ)) atTop atTop:= tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp h) -- check
  exact (h.eventually_ge_atTop p).and ((tendsto_inv_atTop_zero.comp hc).eventually_le_const hη) -- check
end Dynamics

-- load obtainable on SAME family.Traversal cards "+ Origin" global.
open UVExtension Oasis Mast Orchard Spire
variable {C:Family G} {hG:G.Simple}
lemma instruments {Q: Chron.Contemple G} (h:Stagehands.Origin hG Q C) : ∃ (M:Metals G) (D: Rolls M.p) (A:Alloy M D) (F:Factor A)(S:Uses F hG),
      C.path=A.B.bake.make (S.realBeat 0) ∧ (∃ b:Book (Stagehands.atlas F Q), Pillar (Stagehands.atlas F Q) F.prices F.span F.recordP F.shape Q A.delay b) ∧
      ∀ m N n,m<N → let u:= S.realBeat 0 N n (m+1);
                     u.beta=C.path.β N n (m+1) ∧ gStep u.beta=Pert.Asymptotics.regulatorRun C N n (m+1) ∧ Lives A.B.bake N (m+1) n u ∧ u.beta∈band A.B.a (m+1):=by
   obtain ⟨M,D,A,F,K,w,X',p,H,Y,e,hX,rfl,hQ⟩:= h.provenance
   refine ⟨M,D,A,F,H,rfl,hQ.library,?_⟩; intro m N n h u
   exact ⟨rfl,rfl,(H.ticking N n (Uses.centerP _)).prices (m+1) (by omega) h⟩
end YM.RemainderComparison.Hymnal
