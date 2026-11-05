import YM.RemainderComparison.Musicology.Bluff
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
open JointLoad JointLoad.Heir JointLoad.Heir.Suite
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (F:Factor A)
variable {N m n :ℕ}
lemma exceeds (b k s ℓ : ℕ) : ∃ n:ℕ, ∀ x:ℕ,1 ≤ x→ Sleet.cortex b x k s ℓ ≤ Meadow.studio n x:= by
    refine ⟨Sleet.cortex b 1 k s ℓ,fun x hx=>?_⟩
    apply le_trans (b:=Sleet.cortex b 1 k s ℓ * x)
    · unfold Sleet.cortex Deck.Mint.width -- prove via twin
      nlinarith only [hx,Nat.zero_le (Lyric.region k s),Nat.mul_le_mul_left (Lyric.region k s) hx]
    dsimp only [Meadow.studio,Meadow.roomSize,Deck.Mint.width]; omega
lemma presents {L:Side} (B:Songbook G L): ∃ D:Songbook G L, D.Delta=B.Delta∧D.chord=B.chord∧ D.B=B.B ∧ D.unsigned=B.unsigned ∧ D.uptake=B.uptake∧ D.post=B.post ∧ D.Y ≥ B.Y ∧ D.pV ≥ B.pV ∧ D.kernel ≥ B.kernel ∧ ∀ x, D.Y x≥0 ∧ D.pV x≥0 ∧ D.kernel x≥0:=by
    refine ⟨{B with Y:=fun x=>|B.Y x|, pV:=fun x=>|B.pV x|, kernel:=fun x=> |B.kernel x|, rend:= B.rend.absolute, bills:=?_, sea:= B.sea.absolute},rfl,rfl,rfl,rfl,rfl,rfl, fun _=>le_abs_self _,fun _=>le_abs_self _,fun _=>le_abs_self _,fun _=>⟨abs_nonneg _,abs_nonneg _,abs_nonneg _⟩⟩ -- syntax update likely indentation
    obtain ⟨r,h⟩:= B.bills; exact ⟨r,Brim.absolut h⟩
namespace Aims
def buffer {L:Side} (D:Aims G L) (b p s :ℕ): Aims G L:=
   {D with scope:= max D.scope (Classical.choose (exceeds b D.arity s p)), songs:= Classical.choose (presents D.songs) }
lemma length {b c:ℕ} (h:b ≤ c)(k:ℕ) : Meadow.studio b k ≤ Meadow.studio c k:=by unfold Meadow.studio Meadow.roomSize Deck.Mint.width; gcongr
lemma wages {L:Side} (D:Aims G L)(b p s :ℕ): ∀ x:ℕ,1≤ x → Sleet.cortex b x (D.buffer b p s).arity s p ≤ Meadow.studio (D.buffer b p s).scope x:= fun x hx=> ((Classical.choose_spec (exceeds b D.arity s p)) x hx).trans (length (le_max_right ..) _)
end Aims
namespace Dynamics
variable (V:Dynamics G) (z:ℕ)

def high : Dynamics G := ⟨V.ν,V.tall, @fun _ _ _ X _ _ _ F Y C k d h j i t=> (V.lighting F Y C k d h j i t).buffer (X j i|>.halo) z (max t.val (i+1)+1) ⟩
def note (j i:ℕ) (u:Fin (i+1)) := V.lighting F.shape A.post F.prices F.span F.recordP A.θ j i u
local notation "V'"=> V.high z
local notation "J"=> A.B.a.clock.J m
local notation "I"=> A.B.a.clock.J (m+1)
variable {p:ℕ}(hp:p≤ A.B.a.clock.J m)
local notation "w"=> Dynamics.rose F V' p hp
local notation "W₀"=> (w)
set_option quotPrecheck false
local notation "b"=> (V.high z).note F I J (⟨p,Nat.lt_succ_iff.mpr hp⟩) -- field order test
-- need V lights amplitude.D.R
local notation "r" => Hymnal.Rental F (T:=(V').cultivate) w
variable (y:Book (Stagehands.atlas F (V.high z).cultivate))
local notation "δ"=> A.B.a.clock.hatBeta m
local notation "s"=> Hymnal.exclaim F y w
lemma scopes : (Orbit F (T:=(V').cultivate) w|>.scope)=Hymnal.standard (b).scope G _ ∧
      (∀ x:ℕ,1 ≤ x→ Sleet.cortex (F.target I J).halo x (s).k (s).s z ≤ Meadow.studio (b).scope x)∧ (0≤(s).Y ∧ 0≤(s).pV∧ 0 ≤ (Orbit F (T:=(V').cultivate) w).propAim.kernel δ) ∧ (r).p=p:=by
   let p':= Dynamics.note F V I J (⟨p,Nat.lt_succ_iff.mpr hp⟩)
   have hκ: (b)=(p').buffer (F.target I J|>.halo) z (max p (J+1)+1):=rfl
   have hp': V'=V.high z:=rfl
   refine ⟨rfl, Aims.wages p' _ _ _, ?_, rfl⟩
   exact (Classical.choose_spec (presents p'.songs)).2.2.2.2.2.2.2.2.2 _ -- cond count
-- dummy policies only for commissions and high projections. Doesn't assert MODEL.
def root (G:Gauge)(L:Side): Aims G L:= ⟨0,
  ⟨1,fun _=>0,fun _=> 0,fun _=>1,1,fun _=>0,fun x=> betaF G x L ^(-(1:ℝ)), -1,fun _=>0,fun _ _ _ _ _=>1,fun _ _ _ _ _=>1,
   zero_lt_one,zero_lt_one, (by norm_num),Reserve.const _,Reserve.const _,⟨0,(Reserve.const (G:=G) (L:=L) 0).rate⟩,fun _ _ _ _ _ _ _ _ => ⟨Reserve.const _,Reserve.const _⟩,Reserve.const _,Rate.power,Reserve.const _⟩,
   0,0,0,1,fun _=>0, Reserve.const _,zero_lt_one,Boost.trivial ..⟩
abbrev moon (G:Gauge): Dynamics G:= ⟨fun _ _ _ _=>1,fun _ _ _ _=>zero_lt_one,fun _ _ _ _ _ _ _ _ _=>root G _⟩ -- abbrev private? use def
end Dynamics
end YM.RemainderComparison.Hymnal
