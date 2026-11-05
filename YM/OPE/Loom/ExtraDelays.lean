import YM.OPE.Loom.Funds
import YM.OPE.Rough.Gate
import YM.OPE.Rough.Factory
/-! # Bind Throws receipts and retain static exponent
No prototype-stage oracle. The delays work on the actual post-L path, compatible
with the arbitrary product supplies in `Services`. (`supportExp=100` will be
used for Repegs & grouping with polynomial β costs.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.MergeProof MergeProof.Ribbons Mallow
variable {G : Gauge} {s : Sheet G} {D:Rolls s} {T:Protection D}

def Subsidize (a : Levels G) := ∀ i d : ℕ, d ≤ a.clock.J i → Upgrade G (a.params i) (a.S.block i) d (a.clock.hatBeta i)

lemma subsidize_feasible (V : Delays T) : ∃ W, DelayLe V W ∧ ∀ W', DelayLe W W' →
    ∀ {X : Bar W'} (P : Wait X) (Q : Levels G), Paid P Q → Subsidize Q := by
   -- post priorities through two neighboring J possibilities
   let p (j i d : ℕ) (x : ℝ) := Upgrade G (s.profile i) (D.L j) d x
   obtain ⟨u,-,hv,H⟩:=collect_upper V.betaEntry (fun j x=> ∀ i ∈ Finset.range (j+1), ∀ d ∈ Finset.range (i+1), p j i d x)
     (fun j=> ((Finset.range (j+1)).eventually_all.mpr fun i _=> (Finset.range (i+1)).eventually_all.mpr (fun d _=> enhanced ..)))
   refine ⟨{ V with betaEntry:=u}, ⟨hv,le_rfl,le_rfl,le_rfl⟩, fun W hW X P Q h i d hd=>?_⟩
   have he := H (Q.clock.J (i+1)) _ ((hW.beta _).trans (h.pays i)) _ (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr (Q.fits.mono i.le_succ))) _ (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hd)) -- which i'?
   rw [params_eq h i, Extra.Iteration.block_eq h]; exact he

section
variable (hG:G.Simple) {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}(b: Bandage X Y K)(Q:ℕ→ℕ) (Y': Bolt A)
variable (t:ℕ→ℕ)(Z:∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail Y') N p) (D0:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y').rep N p (m+1)) ((Issue.trail Y').rep N p m))
local notation "C"=> Family.mk (Issue.trail Y') (hol G) (Labels.frames G) (localSection G) t Z
local notation "x" => A.B.a
set_option quotPrecheck false
variable (hN:Chateau b Q Y' t Z D0)
/- Need hV exp margin? `thaw` includes first component Runs already; to derive 2nd Throws can skip first proof maybe access `Graces.respects` directly without p₀ inequality. -/
open Mallow Lotus Accent Menu
variable {j n m:ℕ}
private lemma duetF {E:Rep G (A.B.a.S.side m j)} {Z:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor Z E)(hk:(Issue.trail Y').rep n j m=E)(h:(Issue.trail Y').rep n j (m+1)=Z)(d:ℕ)(u:ℝ) (hp:∀ (q:Set Wing)(M:Lotus.Leaf Z), M.turn∈q → 0∈ M.crest→ MergeProof.Coupon (localSection G d) (Issue.trail Y') n j m (hol G) (MergeProof.prose M) (entry M) 0 (duet _ _ _ _ hk h D) q (Complex.ofReal ∘ M.cicada) 0 (u*load M) (u*load M) (2*load M)) : MergeProof.Throws (Issue.trail Y') n j m (duet _ _ _ _ hk h D) (hol G) (localSection G d) u :=by subst E Z; exact hp
include hN hG
lemma further (hv:Subsidize x) (m N j d:ℕ) (he:t d ≤ m) (hp:m<N) : Throws (Issue.trail Y') N j m (D0 N j m hp) (hol G) (localSection G d) ((x).clock.hatBeta (m+1)) := by
   have hc:= Upgrade.pays G _ _ d (hv m d ((Nat.le_add_right ..).trans ((hN.opens d).trans ((x).fits.mono he)))) (X.target ((x).clock.J (m+1)) ((x).clock.J m))
   rw [Extra.Iteration.block_eq A.B.valid m, params_eq A.B.valid m] at hc
   rw [Extra.Iteration.block_beta m, Extra.Iteration.block_eq A.B.valid m]; -- proof `Throws` needs decompose Climbs
   let D1:= D0 N j m hp
   have hC:Climbs X Y' N m j D1:=hN.motion _ _ _ hp
   generalize hy:D0 N j m hp=D1' at * -- hC refers let?
   have hE:Climbs X Y' N m j D1':= hy ▸ hC
   obtain ⟨l,v,R,S,x₀,hQ,hW,rfl⟩:= hE
   -- cast
   let k:= A.B.a.clock.J (m+1); let u0:= Pressure.betaF G (A.B.a.clock.hatBeta m) (P.L k)
   refine duetF Y' _ hQ hW d _ fun q V hV hq=> Graces.respects hG hp hN.nest b.r S x₀ hQ hW b.clock b.stamp ?_ V _ hc q hV hq -- Ω t'
   have := ((hN.opens d).trans ((x).fits.mono he))
   omega

end
end YM.PhysicalNext.Repeat.Legato
