import YM.FullVolume.Auvi.Cadence
import YM.FullVolume.Gain.Resolve
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
abbrev Hall (a: Levels G)(i p:ℕ):= Show (stageP a i p)
abbrev cloud (a:Levels G)(i p:ℕ) := Completion (Hall a i p)
abbrev suites (O:Ops L N p)(i:ℕ)(h:i≤N):= Home (O.plan i h)
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
variable {Y O}
namespace Window
variable (O)
abbrev booth (m p:ℕ)(r:Levels G): Type:=cloud r m p
def room {t:ℕ}{h:t ≤ N}(x:suites O t h): booth t p B:= (((x.val:Hall B t p)):Completion (Hall B t p))
lemma firm {h} (x y: suites O m h): dist (room O x) (room O y)= dist x y:=Completion.dist_eq ..
lemma normP {h}(x:suites O m h): ‖room O x‖=‖x‖:= Completion.norm_coe _
-- actual ready.Use defeq uniform direct
variable (Y)
abbrev wish (O:Ops L N p)(i:ℕ)(hi:i<N):=ℝ × (suites (A:=A) O (i+1) hi)
section step
set_option quotPrecheck false
variable {h:m<N}(x: ℝ×Home (O.plan (m+1) h))
local notation "T"=> L.prim N m p h
def offer (O:Ops L N p) {i:ℕ}(h:i<N)(x: ℝ × Home (O.plan (i+1) h)): Home (O.plan i h.le) := (chooseR _ (O.walks i h) (Pass.invitation (L.prim N i p h) x)).val
def costP (O:Ops L N p) {i:ℕ}(h:i<N)(x:ℝ×Home (O.plan (i+1) h)):= drum (L.prim N i p h) x
variable (ht:mild (A.B.a.clock.hatBeta (m+1)) x.1)(hp:‖x.2‖ ≤ 1/8)
include Y ht hp
lemma compass : ‖offer O h x‖ ≤ 1/8∧‖costP O h x‖ ≤ fn A.B.a m w:=by
     obtain ⟨hv,hh⟩:= termsN Y.SimpleR T Y.Shears Y.Saved (O.walks m h) (Y.largeG.scale _) Y.voices (x:=x) ht (hp.trans (by norm_num))
     have he:= (Completion.norm_coe (offer O h x)).symm.trans_le hv; exact ⟨by have h:= Y.earn; rw [show glint=1/128 from rfl] at h; linarith,hh⟩
lemma curls (z: ℝ × Home (O.plan (m+1) h))(hs:mild (A.B.a.clock.hatBeta (m+1)) z.1)(hy:‖z.2‖ ≤1/8):
       dist (room O (offer O h x)) (room O (offer O h z)) ≤ (8*glint)*max (dist x.1 z.1) (dist (room O x.2) (room O z.2)) ∧ ‖costP O h x-costP O h z‖ ≤ (8*fn A.B.a m w)* max (dist x.1 z.1) (dist (room O x.2) (room O z.2)) :=by
    rw [firm,firm,←Prod.dist_eq]; simp only [dist_eq_norm]
    obtain ⟨he,h⟩:= ticket Y.SimpleR T Y.Shears Y.Saved (O.walks _ h) (Y.largeG.scale _) Y.voices Y.earn hs hy x ht hp; exact ⟨(Completion.norm_coe _).symm.trans_le ((congr_arg (fun z:Completion (Home (O.plan m ‹m < N›.le))=> ‖z‖) (Completion.coe_sub (offer O _ x) (offer O _ z))).trans_le he),h⟩ -- norm notation
lemma filled : let f:= (Pass.invitation (L.prim N m p h) x|>.val).val; f.beta=fromLambda (Ω (m+1)) x.1∧ f.activities=x.2.val.proper:=by
     have hh:=Y.largeG.scale (m+1); have he:= Pass.simple_full _ hh (Pass.samples hh ht (by rw [sub_self]; norm_num))
     intro f; unfold f; rw [Pass.vers T x he (hp.trans (by norm_num))]; exact ⟨rfl,rfl⟩
end step
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
