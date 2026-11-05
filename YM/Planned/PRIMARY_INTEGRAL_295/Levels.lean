import YM.Extra.SOURCE_HISTORIES.Issue
import YM.Planned.PRIMARY_INTEGRAL_295.Colas
import YM.Planned.PRIMARY_INTEGRAL_295.Edens
import YM.Planned.PRIMARY_INTEGRAL_295.Release
/-!
# Producer-compatible forecast scratch, unaltered Kinematic Roll

Page from ANY Bolt.H with this Scratch.Q.S using Horizon all.Move paths.
Do NOT claim equality of arbitrary V.tube.R.A0 to canonical flight.A0. Happens
only if B.H.Present; but it's not used in a *single* evaluation of Dawn!
This scratch therefore allows the same theorem on true evaluation data
and epoch analysis of genuine H with any A0 assignment satisfying earlier.
Compares exact rows & transforms as previous.Ar. All Q*T changes forecast
at pages and re-certified earlier gifts. No new origins or family levels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.WaterLevels
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions Decks Castles Ritual Solves Piers Gleams
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations Racks Dials WardBin WardBin.Lies Spurs Vintage Atrium Colas Gala 
open Triumph Release Thrift Warehouse Folio Next.Foundations Extra.Histories Input Laurent Work.F08 Next.Free Edens
open Push.Local (Slots Raw joint ForceFormat)
open Org RG.Supply RG.Shoot
open  Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical NNReal
variable {G:Gauge} {d :ℕ}

def forecast {M : Metals G}{D : Rolls M.p}{A : Alloy M D} (B:Bolt A)(i N p:ℕ):Tube G (A.B.a.clock.op i p):=
   let U:=Pressure.Testing.ships A.B N i p
   {U with R:={U.R with A0:= linesOf (Warehouse.flight (Issue.trail B) N i) A.B.a.clock.kernel.penalty} }

-- Scope: Σ only before Books.I etc No stamps implied. Pre all Q.Λ independent.
structure Capital (P:Sheet G)(K:MapPrices)(Q:ℕ→ℕ→ Teller G) :Prop where
   setup : Squad P.profile P.kernel Q
   costs j i (hj:4 ≤ j)(hi:4 ≤ i) : let R:=Q j i;
      R.η ≤ K.α j ∧ K.Ω j≤R.C ∧ ∀ (B:Flight j i) (l:List Axis), l.length≤j-2 →
        (advanceC B.L (linesOf B P.kernel.penalty) l).strip R.η (R.C/(B.L.val:ℝ)^(1+l.length))

lemma invest (P:Sheet G)(K:MapPrices):∃ Q:ℕ→ℕ→Teller G, Capital P K Q:=by
    choose! s c hs hC H using fun j i (hj:4 ≤ j) (hi:4 ≤ i) => Carrier.priced _ P.kernel.penalty_pos hj hi --syntax
    let y(j i:ℕ) := min (K.α j) (if 0 < s j i then s j i else 1)
    have he j i :0 < y j i:=lt_min (K.alpha_pos j) (by split <;> first| assumption| norm_num) --fallback
    let Q(j i:ℕ): Teller G:= ⟨P.kernel,P.profile j,P.profile i,j,y j i,max (K.Ω j) (c j i),he j i⟩
    refine ⟨Q, ⟨fun _ _=>⟨rfl,rfl,rfl,rfl⟩⟩,fun j i hj hi=> ?_⟩
    intro R
    refine ⟨min_le_left .., le_max_left ..,fun B l hl=> ?_⟩
    have hc : R.η ≤ s j i := by change y _ _ ≤ _; unfold y; rw [if_pos (hs j i hj hi)]; exact min_le_right ..
    exact strip_mono (H j i hj hi B l hl) hc (div_le_div_of_nonneg_right (le_max_right ..) (by positivity))

section
variable {M : Metals G}{D : Rolls M.p}{A : Alloy M D}(B:Bolt A){i N p:ℕ}
variable {Q:ℕ→ℕ→ Teller G} (hc:Capital M.p M.K Q)
include hc

lemma piper (h:i<N): Page (Issue.trail B) i N p (Q (now (Issue.trail B) (i+1)) (now (Issue.trail B) i)) (forecast B i N p):=by
   let K:=A.B.a; let S:=K.clock.op i p; let σ:=Pressure.Testing.ships A.B N i p; let R:=forecast B i N p
   let W:=A.B.M; let U:=W.H N (i+1); let V:=W.H N i; let j:=K.clock.J (i+1); let t:= K.clock.J i; let Q':=Q j t
   have hP : Towers.Roll S U V R.R (K.params (i+1)).clip (K.params i).clip ∧ Towers.Diagonal S U V R.R ∧ Bid.Sworn V (K.S.side i p) G:=
       laureates K W A.B.plan N i p h
   obtain ⟨ha,hO,hq⟩:= hc.costs j t (K.clock.adm _) (K.clock.adm _)
   have hf (n:ℕ)(hn:n≤N) : ((Issue.trail B).rep N p n).path=A.B.kin.path N n:=by
        have hx:= ((B.sticks N p).prices n (Nat.zero_le _) hn).1.path
        rw [A.B.bases] at hx; exact hx
   have ht:=B.choice.represents N p
   refine ⟨⟨(hf (i+1) h).symm, (ht (i+1) h).clip.symm⟩,⟨(hf i h.le).symm,(ht i h.le).clip.symm⟩,
     ⟨U,V,A.B.support.links N (i+1) h, A.B.support.links N i h.le,hP.2.1,hP.1,hP.2.2⟩,?_ ,rfl⟩
   obtain ⟨h1,h2,h3,hL⟩:= A.B.plan.costs N i h
   let L:= K.S.block i; have hd(n:ℕ):0≤(L.val:ℝ)^n:=by positivity
   refine ⟨strip_mono h1 ha hO,strip_mono h2 ha hO, strip_mono h3 ha (div_le_div_of_nonneg_right hO (hd 2)),fun l hl=> ⟨?_,?_⟩⟩
   · change (advanceC _ (linesOf (destination K N i) K.clock.kernel.penalty) l).strip Q'.η _; rw [show K.clock.kernel=M.p.kernel from A.B.valid.kernel]; exact hq _ l hl
   exact strip_mono (hL l hl).2 ha (div_le_div_of_nonneg_right hO (hd _))

omit hc in
lemma same_chart {F:Labels.Frame G d} (T:SectionData F)(i N p:ℕ) : let K:=A.B.a; let S:=K.clock.op i p; let x:=K.clock.hatBeta i
   ∀ (h:Date T x S.patch)(V:Bloom G){θ:Type}[Fintype θ] (J:θ→Forest S.ratio)(W:θ→ S.Choices)(φ:θ→ℝ≥0) t t' ξ,
     Colas.dawn (fun j=> lantern S T x (Pressure.Testing.ships A.B N i p) (J j) (W j) V.ε V.avatar h) φ T (hitch x) t t' ξ =
       Colas.dawn (fun j=> lantern S T x (forecast B i N p) (J j) (W j) V.ε V.avatar h) φ T (hitch x) t t' ξ:=by
    intro K S x h V θ inst J W φ t t' ξ
    -- likely defeq, fder etc differ R record only definitional reduction.
    rfl

-- practical main beta body.Start with unmodified H.Tube(`ships`) from true Book.levels.
-- Q.Colors scratch.Account caps only for proof not for existing Budget.G. 




end
end YM.Planned.PrimaryIntegral295.WaterLevels
