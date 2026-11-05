import YM.UVExtension.Upland.Plinth
/-!
 # Clarify success.

 Launch-frame choices are fixed even for the other trial b.  In this
 below version of trial success put only the actual scalar coupling and
 recurrence in the criterion.  The activity-side stubs and work are not
 tests to throw out e.g. a trial on norm or future-germ failures. They are
 calculated and proved under bands. Different step/renormalization
 prescriptions in general not claimed to have the same beta reading.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
namespace Fitted
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
-- Fitted launch here read irrespective of port padding. See topper, moving.
local notation "L"=> A.B.a
variable (β:ℕ→ℝ)
-- book calculates actual starting activities + steps on these fixed choices; then ask that they stayed in bands AND the actual scalar outputs also match that path

def bounty := H.graceT (port R N β)
def gate (i:ℕ)(hi:i<N) := β (i+1)+A.B.kin.alpha N i + (H.charts i hi).claim R (H.W (i+1)) (H.bounty β (i+1)) (β (i+1))
structure Plotted (b:ℝ): Prop where
    bands i (hi:i≤N): β i∈RG.Shoot.band A.B.a i
    agrees i (hi:i<N): β i= H.gate β i hi
    wants : β 0=A.B.a.clock.bar+b
variable (i:ℕ) (p:i<N)
private lemma filed (i)(hi:i≤N): H.bounty β i=H.file (port R N β) i hi:=dif_pos hi
-- This lets one start with beta_N and simply keep going while in band
lemma topper (hb:β N∈ band L N): H.bounty β N=city R (hp N) hk hb H.start:=by rw [filed H β N le_rfl, file, Nat.decreasingInduction_self,here (R:=R) (β:=β) _ le_rfl,singleA,dif_pos hb]
lemma moving: H.bounty β i = Tour.choiceV R hG t (H.charts i p) _ (H.shirts i p) (H.bounty β (i+1)) (β (i+1)):=by
    let v:= port R N β; rw [filed H β i p.le,filed H β _ p, ← here (R:=R) (N:=N) _ p (β:=β)]; exact Nat.decreasingInduction_succ_left _ _ _ _
lemma ready (v)(hv:v≤N)(h:∀ i,v ≤ i→ i≤N → β i∈ band L i): Reality L v n (H.W v) (H.bounty β v) (β v):=by
    induction hv using Nat.decreasingInduction with
    | self=>rw [H.topper β (h _ le_rfl le_rfl)]; exact attune ..
    | of_succ i hi IH=>
       have he:= IH (fun k hk h'=> h _ (i.le_succ.trans hk) h'); rw [moving H β i hi,Tour.choiceV,dif_pos he]; exact ⟨h _ le_rfl hi.le,Tour.new_mem ..⟩
lemma gear (he: Reality L (i+1) n (H.W (i+1)) (H.bounty β (i+1)) (β (i+1))): H.gate β i p=(H.charts i p).newB R _ he:=by unfold gate Tour.claim; rw [dif_pos he]
variable {b:ℝ}
lemma permits : H.Plotted β b ↔ ∃ f s,H.Shot f β s ∧ β 0=A.B.a.clock.bar + b:=by
    constructor
    · intro h; let s:= H.cash (port R N β)
      have hh(i)(hi:i≤ N) := H.ready β i hi (fun j _=>h.bands j)
      refine ⟨bounty H β,s,⟨hh,?_,fun i hi=>?_⟩,h.wants⟩
      · unfold race; rw [topper H β (h.bands N le_rfl), high_s]; unfold s cash; rw [dif_pos le_rfl,Nat.decreasingInduction_self]
      have hx: H.bounty β i= Tour.royals R hG t (H.charts i hi) _ (hh _ hi) (H.shirts i hi):= (moving H β i hi).trans (dif_pos (hh _ hi))
      have hp := (h.agrees i hi).trans (gear H β _ hi (hh _ hi)); unfold race; refine Eq.trans ?_ ((H.charts i hi).around R _ (hh _ hi) _).symm
      refine (congr_fun (congr_arg₂ (mount R N i n) (congr_arg Subtype.val hx) hp) _).trans (congr_arg _ (?_))
      nth_rw 1 [show β (i+1)= _ from (here (R:=R) (N:=N) (β:=β) _ hi).symm]
      unfold s cash; rw [dif_pos hi.le,dif_pos (show i+1≤N from hi)]; exact Nat.decreasingInduction_succ_left ..
    rintro ⟨f,s,h,hP⟩; refine ⟨fun i hi=> (h.alive i hi).1,fun i hi=> ?_,hP⟩
    have hx:= h.alive _ hi; have hk: H.bounty β (i+1)=f (i+1):= (H.filed β _ hi).trans (H.files h _ hi); unfold gate; rw [hk,Tour.claim, dif_pos hx]; exact (H.doors h i hi).1
end Fitted
namespace Uses
variable {R hG t hk hp N n} (S: Uses R hG)
def Success (b:ℝ)(N p:ℕ)(bare:ℝ):= ∃ β:ℕ→ℝ, β N=bare ∧ (S.fits N p).Plotted β b
lemma genuine (b:ℝ)(N p:ℕ)(bare:ℝ):Success S b N p bare↔ S.Trial N p b bare:= by
    unfold Success; simp_rw [Fitted.permits]; constructor
    · rintro ⟨β,h, f,s,hp,hF⟩; exact ⟨f,β,s,hp,h,hF⟩
    rintro ⟨f,β,s,h,H,hP⟩; exact ⟨β,H,f,s,h,hP⟩
-- In particular there is not an additional contact/remainder test needed.
-- This is uniqueness and existence for this one prescription in these bands.
end Uses
end YM.UVExtension.Spire
