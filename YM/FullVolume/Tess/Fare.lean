import YM.FullVolume.Tess.Vista
import YM.FullVolume.Tess.Scope
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
namespace Fan
variable (F:Fan T W p){n:ℕ}(V₀:Fin n→ R.family.book.Token)
local notation "δ"=> intervalClock R
open Tess
local notation "S!"=>R.family.S
local notation "C"=> Beam ℂ
open Tess Tess.Scroll
-- Real and holomorphic family test / quanta
variable {w:sun} {K K':Set (Points n)}
abbrev shiftH (l:List (Reach n))(w:sun)(N:ℕ)(s:sun) : Positions n→ℂ:= squall ((R.family.S).a N) l (plainK F V₀ N (scaleSun w s))
abbrev Pearl (l:List (Reach n))(f:ℂ→ Points n→ℂ)(x:Points n)(z:ℂ):= derive (f z) (l.map Reach.where_) x
abbrev LowerDisk (xQ:sun)(K:Set (Points n))(l:List (Reach n))(V:ℕ→Positions n→ Beam ℂ): Prop:= ∀ᶠ N in atTop,∀ x:Positions n,tag ((R.family.S).a N) x∈ K→ ∀ s:sun, shiftH F V₀ l xQ N s x=read ℂ s (V N x)
variable (l:List (Reach n))
lemma polaris {U:ℕ→Positions n→Beam ℂ}{P:Points n→Beam ℂ}(h:Bows F V₀ w K (l.map Reach.where_) U P)(hK:IsCompact K')(hv:K' ⊆ interior K): LowerDisk F V₀ w K' l (fun j=>waves l (U j))∧ Scroll (R.family.S) K' (fun j=>waves l (U j)) P:=by
    refine ⟨?_,(h.sycamore F V₀ _).voyages hK hv l⟩
    let f (s:sun)(i:ℕ):= kFilm F V₀ (l.map Reach.where_) i (scaleSun w s)
    have he:∀ᶠ i:ℕ in atTop,∀ x:Positions n,tag ((R.family.S).a i) x∈K→∀ s:sun,f s i x= read ℂ s (U i x):=h.song.mono fun m hm x hx s=>(hm x hx s).symm
    have hh(i s):shiftH F V₀ l w i s=tides l (f s i):= applies _ _ l
    unfold LowerDisk; simp_rw [hh]; exact readsWave hK hv l he
-- public amplitudes. Endpoint P:Points→ℂ→ℂ is possibly arbitrary outside optics and at early cutoffs. Does not claim continuity there -- actual verification with reparam discs.
structure Polar (w:sun) (K:Set (Points n)) (l:List (Reach n))(D:ℂ→Points n→ℂ): Prop where
  sky : ∃ (Q:Points n→ℂ→ℂ),
     (∀ z∈ optics, ContinuousOn (fun x:Points n=> Q x z) K) ∧ (∀ x∈K,AnalyticOnNhd ℂ (Q x) optics ∧ EqOn (Q x) (Pearl l D x) optics) ∧
     ∃ (Y:ℕ→Positions n→ℂ→ℂ)(X:ℕ→Points n→ℂ→ℂ),
      -- Continuation of finite kernels means eventual on each fixed K p stencil.
      (∀ i:ℕ,(∀ y,AnalyticOnNhd ℂ (Y i y) optics) ∧ ∀ x,AnalyticOnNhd ℂ (X i x) optics) ∧
      (∀ᶠ N in atTop, (∀ x:Positions n,tag ((R.family.S).a N) x∈K→∀ s:sun,Y N x (s.val:ℂ)=shiftH F V₀ l w N s x)∧
                    (∀ x∈K,∀ s:sun,X N x (s.val:ℂ)=interpolated R.family.S N (shiftH F V₀ l w N s) x))∧
      (∀ d:ℕ,∀ J:Set ℂ,IsCompact J→ J⊆ optics→ ∀ ε:ℝ,0< ε → ∀ᶠ i in atTop,(∀ x:Positions n,tag ((R.family.S).a i) x∈K→∀ z∈J,dist (iteratedDeriv d (Y i x) z) (iteratedDeriv d (Q (tag ((R.family.S).a i) x)) z)< ε)∧
        ∀ x∈K,∀ z∈J,dist (iteratedDeriv d (X i x) z) (iteratedDeriv d (Q x) z)< ε)∧
      ∀ t:Test n, suitable R.family.S p t→ tsupport t ⊆ K →
        ∃ (A:ℕ→ℂ→ℂ) (e:ℂ→ℂ), (∀ᶠ i in atTop,∀ s:sun,A i (s.val:ℂ)=sumOn (fun i=>shiftH F V₀ l w i s) R.family.S p i t)∧
          (∀ i,AnalyticOnNhd ℂ (A i) optics)∧ AnalyticOnNhd ℂ e optics ∧
          (∀ z∈ optics, Integrable (fun x:Points n=> t x * Q x z) ∧ e z=t.applyTo (fun x=> Q x z))∧
          ∀ d:ℕ,∀ J:Set ℂ, IsCompact J→J⊆optics→ TendstoUniformlyOn (fun i=> iteratedDeriv d (A i)) (iteratedDeriv d e) atTop J
-- stronger knots. Umbra painting. proof
set_option maxHeartbeats 430000
variable {U:ℕ→Positions n→ Beam ℂ}{P:Points n→ Beam ℂ}
variable (h:IsCompact K) (hp:IsCompact K') (hV:K⊆ interior K')
include h hp hV
local notation "A!"=> R.family.S.a
lemma peaking (D:ℂ→Points n→ℂ) (hf:∀ z∈optics,EqOn (fun y=> heartX (P y) z) (fun y=>Pearl l D y z) K)(h':LowerDisk F V₀ w K' l U)(hk:Scroll R.family.S K' U P): Polar F V₀ w K l D:=by
    let Q(x:Points n)(z:ℂ):=heartX (P x) z
    have hx := hk.land.mono (hV.trans interior_subset); let X(i:ℕ)(y:Points n):=heartX (Tess.Scroll.cruise (S!) (U i) i y)
    refine ⟨⟨Q,fun z hz=> (hk.hatch hz).land.mono (hV.trans interior_subset),fun y hy=> ⟨hearts _,fun z hz=> hf z hz hy⟩,fun i j=>heartX (U i j),X,fun i=>⟨fun _=>hearts _, fun _=>hearts _⟩, ?_,?_,?_⟩⟩
    · filter_upwards [inked («S»:=R.family.S) h hV,h'] with i hi hv; refine ⟨fun x hx s=> (heartL ..).trans (hv x (interior_subset (hV hx)) s).symm,fun x hx s=>?_⟩
      unfold X; rw [heartL]; symm; exact sync s x fun a=> hv _ (hi x hx a) s
    · intro d J hJ hz ε he; exact (((hk.restrict (hV.trans interior_subset)).galaxy h hJ hz d) ε he).and (merger (hk.ether h hV) h hx J hJ hz d ε he)
    intro t ht hx
    obtain ⟨hL,hB⟩:=hk.elected t hp (hx.trans hV) ht
    let V:=∫ x, olive t P x
    refine ⟨fun j=>heartX (treats (S!) U j p t),heartX V,?_,fun i=>hearts _,hearts _,?_,fun d J hz hJ=>deluge _ hB J hz hJ d⟩
    · filter_upwards [h'] with i hi s; rw [heartL,viewport]; unfold sumOn; refine congr_arg (fun (x:ℂ)=>_*x) (Finset.sum_congr rfl ?_) -- issues
      intro y _; let z:= Lattice.lift ∘ y; let u:= tag (A! i) z
      by_cases he:t u=0
      · change t u*_=t u*_; rw [he]; ring
      dsimp only; rw [hi z (interior_subset (hV (hx (subset_closure he)))) s] -- orientation rw
    intro z hz
    let g:= (haloC hz).restrictScalars ℝ; have he(y): g (olive t P y)= t y * Q y z:=(haloC hz).map_smul (t y) _
    have hi:=g.integrable_comp hL
    refine ⟨hi.congr (Eventually.of_forall fun y=>he y),?_⟩
    change g V= _; unfold V Test.applyTo; rw [← g.integral_comp_comm hL]; exact integral_congr_ae (Eventually.of_forall fun y=>he y)
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.peaking
