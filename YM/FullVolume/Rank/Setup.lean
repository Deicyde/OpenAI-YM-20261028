import YM.FullVolume.Auvi.Orleans
import YM.FullVolume.Panel.Park
import YM.FullVolume.Umbra.Bale

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
namespace Boutique
set_option quotPrecheck false
variable {q:ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {f:ℕ→ℕ} {p m:ℕ}
local notation "Z₀"=> (A.B.a.S.oneStep m p).exact_size
local notation "z"=> A.B.a.S.side m p
local notation "Z"=> A.B.a.S.side (m+1) p
local notation "W!"=> A.B.a.clock.op m p
local notation "Q"=> A.B.a.budget m
local notation "t'"=> A.B.a.budget (m+1)
abbrev Stack (X:Factor A)(m p:ℕ)(q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p)(f:ℕ→ℕ):=∀ n, Boutique X (q n) (f n) p m
abbrev player {q:ℕ→∀ p,Shoot.Trail A.B.a p}{N p m:ℕ} (_:Boutique X q N p m): Rep G (A.B.a.S.side (m+1) p):= (A.B.bake.make q).rep N p (m+1)
abbrev heroB (F:Stack X m p q f)(n:ℕ): Rep G Z:= (A.B.bake.make (q n)).rep (f n) p (m+1)
local notation "W₁"=> FullVolume.Urns.layout G Z t'
open RG.Shoot Lark Rain Blush
abbrev epoch (F:Stack X m p q f)(n:ℕ):= Lark.book m (A:=A) Z₀ W₁ (f n) (F n|>.player)
lemma holding (U:Stack X m p q f)(i:ℕ) (hi:Lark.Near A m f) : (epoch U i).kin=(U i).player:=by
    let F:= U i; have hh:= F.stock.knows (0:ℝ) Boutique.center.2; have he: Lives A.B.bake (f i) (m+1) p F.player ∧ F.player.beta∈RG.Shoot.band A.B.a (m+1):= hh
    have hg: F.player.path=A.B.kin.path (f i) (m+1):= he.1.path.trans (congr_fun (congr_fun A.B.bases (f i)) _)
    apply Lark.reads _ Z₀ W₁ (f i) (hi i).2 _ he.1.point he.1.clip hg
    have hp:= F.up; let P:=F.player; have hP : HasSlots P.p P.activities:= hp; unfold Rain.listIn; have hr: P.activities.reg=(W₁).reg:= by rw [hP.reg]; rfl
    have hD: P.activities.forced=(W₁).hard:= by rw [hP.forced,he.1.point]; rfl
    cases hK:(W₁) with | mk p q=> rw [hK] at hr hD; congr
abbrev loop (F:Stack X m p q f)(h:Lark.Near A m f)(i:ℕ):= Lark.safeTrans X Z₀ (epoch F i) (Lark.seats m _ _ (f i) (h i).2 _ ) (holding F i h) (F i).sale
lemma orbital {f c:Side} {S:StepData c f}{v v':Tube G S}{K K':Rep G f}{P:Teller G}{U:ConnectedActivityE6.Target G P}{W x r μ:ℝ}{o: Target.Order G W}{L:Side}{F:Cash W x μ L U o r v K}{D: Cash W x μ L U o r v' K'} (he:v=v')(hf:K=K')(h:HEq F D): ∀ (V:Cloud K)(S:Cloud K'), HEq V S → ∀ (w:BudgetPoint) (X: ℝ)(i:ℕ)(A: Slide.Stars→Side)(l y:ℕ)(ha:∀ i,(A i).val=2*(l+i.val))(g:∀ i,Trio.Offer G (A i)) (p:PathData G)(e:Clip)(k:ℂ),
   let f(M:Lotus.Leaf K):= prismK F w X i ha y g p e M; let d(M:Lotus.Leaf K'):= prismK D w X i ha y g p e M
   f V.live=d S.live ∧ f V.pale=d S.pale ∧ Blush.scope F V 0=Blush.scope D S 0 ∧ Blush.fields F V k=Blush.fields D S k:=by subst v' K'; intro V S' he; have h:= eq_of_heq h; have he:= eq_of_heq he; subst D S'; intros; exact ⟨rfl,rfl,rfl,rfl⟩
-- tuple. tactic equality
local notation "w" => Rain.lint X.target A m
local notation "v"=> A.B.a.clock.hatBeta m
local notation "κ"=> Trio.base w (Pressure.radiusB v)
local notation "Λ"=> (A.B.a.params m).clip
local notation "b"=> A.B.a.clock.J m
variable (U:Stack X m p q f)(V:∀ n,Cloud (heroB U n))
def panelT (he:Lark.Near A m f)(i:ℕ): Cloud (epoch U i|>.kin):= (holding U i he).symm ▸ V i
lemma talent {G:Gauge}{f:Side}{P P':Rep G f}{T:Cloud P}{W:Cloud P'}(ha:P=P')(he:HEq T W): T.live.turn=W.live.turn ∧ T.live.weight=W.live.weight∧ T.live.ingredient=W.live.ingredient ∧ T.pale.ingredient=W.pale.ingredient:=by subst P'; have he:= eq_of_heq he; subst W; exact ⟨rfl,rfl,rfl,rfl⟩ -- edit
variable (he:Lark.Near A m f)
lemma accordV (n): HEq (V n) (panelT U V he n):=HEq.symm (eqRec_heq _ _)
lemma plates (i:ℕ)(k:ℂ):
   let A':=loop U he i; let Z':= U i; let F:=panelT U V he i
   let f₀:=prismK A' Q (A.B.kin.alpha (f i) m) Z'.stock.ordinal (Rain.screens X.target A m) κ Z'.rent ((epoch U i).down.path) Λ
   f₀ F.live=pupil Z'.stock center (V i|>.live) ∧ f₀ F.pale=pupil Z'.stock center (V i|>.pale) ∧ Blush.scope A' F 0=Blush.scope Z'.sale (V i) 0∧ Blush.fields A' F k=Blush.fields Z'.sale (V i) k:=by
    intro Y C P f₀; unfold f₀; rw [show ((epoch U i).down.path)=A.B.kin.path (f i) m from (he i).2.1]
    rw [C.fresh,C.fresh]; exact orbital (Lark.seats m _ _ _ (he i).2 _) (holding U i he) (Lark.bank X Z₀ _ _ _ _) _ _ (accordV U V he i).symm _ _ _ _ _ _ _ _ _ _ _
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
