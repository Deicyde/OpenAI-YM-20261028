import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Dais

/-! # All funded, one physical Script and prosody on it

Concrete dictionary, retained early payments. Not reweighted setter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {M : Metals G} {D : Rolls M.p} {U : Alloy M D} {bt : Baton G} {v w t : Return.Wages}
    {L : Targets M.p M.K} {p : ℕ→ℕ→JointLoad.Heir.Record} {V : Programs M.p} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {r : ℕ→ℕ→ℕ} {b : ℕ→ℕ→Booth} {E : Expenses L} {H : ℕ→ℕ→Cafe} {Q : ℕ→ℕ→Clockwork.Menu} {a : ℕ→ℝ} {Y : Register D E w a}
    {J : ℕ→ℕ→Folio.Aux} {c c₁ c₂ : ℝ} {E₀ : ℕ→ℕ→Next.Scheduling.Exchange} {η : ℕ→ℝ} {q : UVNext.CouplingReset.ResetPrices}
    (h : Touring (C:=V) (B:=H) U bt v t r b Q p J Y S c E₀ q η)

local notation "X" => U.B
local notation "W" => U.delay
local notation "P" => M.p
variable {N m n : ℕ} (R : ℝ → RG.Rep G (U.B.a.S.side (m+1) n)) (θ : Set ℝ) (y : ℝ)

structure Embrasure where
  houses (i: θ) : Guide U.B Y N m n (R i)
  honors (i:θ) : Price U.B Y N m n (R i) (houses i)
  he : y ∈ θ
  sister (i:θ) : Alliance (houses ⟨y,he⟩) (houses i) 1 0
  agrees i : (sister i).units=Equiv.refl _

variable {θ R y}
variable (T : Embrasure (N:=N) (Y:=Y) R θ y)
namespace Embrasure
abbrev base:= T.houses ⟨y,T.he⟩
def doors:= Beam.marquee T.base (U.B.a.budget m)
def old:=posting (U.B.a.budget m) T.base
def latch (x : ℝ) : θ:= if h:x∈θ then ⟨x,h⟩ else ⟨y,T.he⟩
lemma click (x) (hx:x∈θ) : T.latch x=⟨x,hx⟩:=dif_pos hx

def fullSong (x : ℝ) := plusone T.base (T.sister (T.latch x)) Chi.canonical (U.B.kin.alpha N m)
def payment (A : Return.Wood U.B m n) (x : ℝ) := weighty (T.houses (T.latch x)) Chi.canonical A
def known (x : ℝ) := Height.serve T.base (T.sister (T.latch x)) Chi.canonical (Beam.lit T.base)
def dark (x : ℝ) := Height.sleeping T.base (T.sister (T.latch x)) Chi.canonical (Beam.lit T.base) (U.B.kin.alpha N m)

variable (hL : ∀ x∈θ,Lives U.B.bake N (m+1) n (R x) ∧ (R x).beta∈band U.B.a (m+1)) (hc : Curve (U.B.a.budget (m+1)) R θ)
    (hF : ∀ j i,StepStages j i → (M.p.profile i).supportExponent+3 ≤ (E j i).earn ∧ (M.p.profile i).supportExponent+3 ≤ t j i ∧ (L j i).halo+5 ≤ r j i)
    (hh : Height.Rich Y c₁ U.delay) (hy : Height.Tenement Y U.delay) (hW : Pew v t V p r Y (wind Q) U.delay c₂) (ht : Opera.Treble U.delay)
    (hm : m<N) {x : ℝ} (hx : x∈θ)
include h hm hF hL hx ht
lemma patrons (O : Return.Wood U.B m n) (d : Return.Bookings U.B m n w) :
    Return.atlas U.B N O d Chi.canonical (radiusW H) (R x) T.doors (T.fullSong x) (T.payment O x) ∧
    Collection.Local T.old (U.B.a.budget m) (T.fullSong x) (Opera.earlyFee (p:=E) U.B N m (R x).beta) (c*forecastK U.B.a m S (R x).beta) := by
  obtain ⟨hr,hv⟩:=hL x hx
  unfold fullSong payment; rw [click _ _ hx]
  obtain ⟨he,hH⟩:= Opera.symphony U.B Y hm h.full h.income (fun j i hij=> (hF _ _ hij).1) h.machine ht hr hv O d T.base (T.houses ⟨x,hx⟩) (T.honors ⟨x,hx⟩) (T.sister ⟨x,hx⟩)
  exact ⟨he.trans (funext fun V=> (Beam.travels _ _ _ _ _ _ V).symm), hH⟩

omit ht
include hc hh hy hW

set_option maxHeartbeats 500000 in
lemma society : Collection.Local T.doors (U.B.a.budget m) (T.known x) ((c₁+2*c₂)*Time.forecastE U.B.a m) (c*Time.forecastK U.B.a m S (R x).beta) := by
  obtain ⟨hr,hv⟩:=hL x hx; obtain ⟨hf,_⟩:= hL y T.he
  unfold known; rw [click _ _ hx]
  exact chairs h hh hy hW hF hm hr hv T.base (T.houses ⟨x,hx⟩) (T.honors ⟨x,hx⟩) _ (T.agrees ⟨x,hx⟩) (hf.path.trans hr.path.symm) (hc.reg _ T.he _ hx) (hc.forced _ T.he _ hx)

omit hx h hm hL hF hc hh hy hW
-- actual residue ALL fields. Dark gas identical though not copied twice into downstream.
def residue (x : ℝ) := (T.doors.read (T.dark x)).additive (U.B.a.budget m)
lemma throttle (x : ℝ) (J : Config G (U.B.a.S.side m n)) : (T.doors.read (T.known x)).gas (U.B.a.budget m) J=(T.doors.read (T.fullSong x)).gas (U.B.a.budget m) J := rfl
lemma pitches (x : ℝ) (j : ℕ) (A : Config G (U.B.a.S.side m n)) :
    (T.doors.read (T.known x)).regularOccurrence (U.B.a.budget m) j A+(T.doors.read (T.dark x)).regularOccurrence (U.B.a.budget m) j A=(T.doors.read (T.fullSong x)).regularOccurrence (U.B.a.budget m) j A := by
  let B:=U.B.a.budget m; let D:=T.doors; let w₀:=(D.reg j).support
  obtain ⟨he,hh⟩:= bolted _ (T.sister (T.latch x)) _ (Beam.lit T.base) (U.B.kin.alpha N m) j -- order edit
  change masked B.threshold w₀ ((T.known x).logRead j) A+ masked B.threshold w₀ ((T.dark x).logRead j) A= _
  unfold known dark; rw [he,hh]; have h:masked B.threshold w₀ (0:Config G _ → ℝ) A=0:= by by_cases h:Healthy B.threshold w₀ A; exact masked_eq _ _ _ _ h; exact masked_ne _ _ _ _ h
  split <;> simp only [h,zero_add,add_zero] <;> rfl

lemma front (x : ℝ) (j : ℕ) (A : Config G (U.B.a.S.side m n)) : (T.old.read (T.fullSong x)).regularOccurrence (U.B.a.budget m) j A=(T.doors.read (T.fullSong x)).regularOccurrence (U.B.a.budget m) j A := by
  change masked _ (Song.posting _ T.base|>.reg j).support _ _=masked _ (Beam.marquee _ _|>.reg j).support _ _; rw [Beam.rewrite_rule]; rfl

include hL hx hc -- characterize dark
lemma awakens (i : T.base.fragrances) (hk : ¬Beam.Kid ((T.sister (T.latch x)).furrow i)) : Height.lower T.base (T.sister (T.latch x)) Chi.canonical (Beam.lit T.base) (U.B.kin.alpha N m) (.inl i)=0 := by
  have hf := (hL y T.he).1; have ht:=(hL x hx).1
  rw [click _ x hx] at hk ⊢
  exact Beam.rooting Chi.canonical _ (hp:=hf.path.trans ht.path.symm) (hr:=hc.reg _ T.he _ hx) (hk:=hc.forced _ T.he _ hx) (ha:= T.agrees _) i hk

omit hL hx hc in
lemma series {G : Gauge} {c : Side} {p : BudgetPoint} (L : Listing G c) (V : Collection.Source G c) {a b : ℝ} (h : Collection.Local L p V a b) (U : Config G c) : Summable fun i=> (L.read V).regularOccurrence p i U := by
  obtain ⟨c,hc,hE⟩:= Activities.E_total h.unweighted
  refine hc.of_norm_bounded fun i=>?_ ; unfold Activities.regularOccurrence
  by_cases he : Healthy p.threshold (L.read V|>.reg i).support U
  · rw [masked_eq _ _ _ _ he]; exact (hE i).2 U he [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact (hE i).1

include h hm hF hh hy hW ht
lemma divided (A : Return.Wood U.B m n) (d : Return.Bookings U.B m n w) (W₀ : Config G (U.B.a.S.side m n)) :
    HasSum (fun i => (T.doors.read (T.dark x)).regularOccurrence (U.B.a.budget m) i W₀) (T.residue x W₀) ∧
      Return.gaussian U.B N A d Chi.canonical (radiusW H) (R x) W₀ = Real.exp (-(T.residue x W₀)) * earlyValue T.doors (U.B.kin.path N m) (U.B.a.params m).clip (U.B.a.budget m) (T.known x) (R x).beta (T.payment A x) (U.B.kin.alpha N m) W₀ := by
  let p:=U.B.a.budget m; let D:=T.doors
  let Z (f : Collection.Source G _):=(D.read f).additive p W₀
  let Y (f : Collection.Source G _):= fun i=> (D.read f).regularOccurrence p i W₀
  obtain ⟨hp,hK⟩ := patrons h T hL hF ht hm hx A d
  have he : Summable (Y (T.fullSong x)):= (series _ _ hK W₀).congr (fun i=>front T x i W₀)
  have ht:= ((he.hasSum).sub (series _ _ (society h T hL hc hF hh hy hW hm hx) W₀).hasSum)
  have hv : HasSum (Y (T.dark x)) (Z (T.fullSong x)-Z (T.known x)) := (ht.congr_fun (fun i=> by linarith only [pitches T x i W₀])) -- direction?
  have hz : Z (T.fullSong x) = Z (T.known x) +T.residue x W₀ := by
    have he := hv.tsum_eq; change T.residue x W₀=_ at he; linarith
  refine ⟨hv.summable.hasSum,(congr_fun hp W₀).trans ?_⟩
  unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only
  rw [← throttle, (show (T.doors.read (T.fullSong x)).additive p W₀ = _ from hz)]
  rw [sub_add_eq_sub_sub, sub_eq_add_neg (b:=T.residue x W₀),Real.exp_add]; ring
end Embrasure

variable (hm : m<N) (hL : ∀ x∈θ,Lives U.B.bake N (m+1) n (R x) ∧ (R x).beta∈band U.B.a (m+1)) (hc : Curve (U.B.a.budget (m+1)) R θ)
include h hm hL hc
lemma arches (he : y∈θ) : Nonempty (Embrasure (N:=N) (Y:=Y) R θ y) := by
  choose f H using fun (t:θ) => Opera.feature U.B Y hm h.full h.income (hL t t.2).1 (hL t t.2).2
  refine ⟨⟨f,H,he,fun z=> staple (R:=R y) (((hL y he).1.path).trans (hL z z.2).1.path.symm) (hc.reg y he z z.2) (hc.forced y he z z.2),fun i=>rfl⟩⟩
end YM.PhysicalNext.Repeat.Roof
