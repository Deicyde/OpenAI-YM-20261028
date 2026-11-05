import YM.FullVolume.Auvi.Rails
import YM.FullVolume.Auvi.Broom
/- point of departure -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Beacon Stationary.Shade Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
open Rain Pane Roof ConnectedActivityE6.Lim FullVolume.Shadow
variable {m:ℕ}{Z:f.val=c.val*(A.B.a.S.block m).val}{W:Listing G f}{N:ℕ}
local notation "K"=> A.B.kin
local notation "B"=> A.B.a
local notation "Q"=> A.B.a.budget m
local notation "Ω"=> A.B.a.budget (m+1)
abbrev Near (A:Alloy X D)(m:ℕ)(φ:ℕ→ℕ):=∀ n,m<φ n∧ Ionic (φ n) m A
lemma nearby {φ:ℕ→ℕ} (h:Near A m φ)(n:ℕ): ((Cad.pure (K|>.path (φ n) m)).path).Bounds ((B).params m).clip ((B).params m).width ((B).params m).paths ((B).clock.loopCap m):=(h n|>.2.1|>.symm) ▸ A.B.support.cap _ _ (h n).1.le
lemma sweep {Λ:Era G (panel A m Z)}{X:ℕ→Epoch Λ} (V: Vented fun n=> (X n).kin.activities.regularOccurrence Λ.p) (B': Vented fun n=>(X n).k): Sweep X:=by
   obtain ⟨a,hp,H⟩:=V.sup; obtain ⟨b,hB,h⟩:=B'.sup; exact ⟨⟨a,hp,fun i k x=> H i x k⟩,b,hB,fun i k x=> h i x k⟩
lemma wilt {ι:Type}[TopologicalSpace ι]{f g:ℕ→ι}{φ χ:Filter ℕ}(h:Glints φ f g)(he:χ≤φ):Glints χ f g:= glitters h he he -- identity
variable {u v:ℕ→ℕ}(h:Artes.Cadre A.post A.B.kin)(ht:Next.Free.Amplify A.B.M)(hu:Tendsto u atTop atTop)(hv:Tendsto v atTop atTop)(hX:Near A m u)(hV:Near A m v)(hd:WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
set_option quotPrecheck false
local notation "γ"=> fun n=> K|>.alpha (u n) m
local notation "δ"=> fun n=> K|>.alpha (v n) m
include h hu hv
lemma landhold : Glints atTop γ δ:= by obtain ⟨X,H⟩:= h.accounts m; exact ⟨X,H.comp hu,H.comp hv⟩ -- m inclusion
include hX hV ht hd
lemma allies (Z:f.val=c.val*((B).S.block m).val) (W:Listing G f) (V X:ℕ→ Rep G f)(hp:∀ n,(book m Z W (u n) (V n)).kin=V n)(hw:∀ n,(book m Z W (v n) (X n)).kin=X n)(hk:Angel (fun n=> (V n).activities.regularOccurrence Ω) (fun n=> (X n).activities.regularOccurrence Ω)) (ha:Angel (fun n=> (V n).activities.K) (fun n=>(X n).activities.K)) (hB:Glints atTop (fun n=>(V n).beta) (fun n=>(X n).beta)) : let M n:= book m Z W (u n) (V n); let L n:=book m Z W (v n) (X n); Accord M L Q γ δ:=by
    intro M L
    have hG:Angel (fun n=> (M n).kin.activities.regularOccurrence Ω) (fun n=> (L n).kin.activities.regularOccurrence Ω):=by
         have ha:(fun n=> (M n).kin)=V:=funext hp; have he:(fun n=> (L n).kin)= X:=funext hw; change Angel ((fun x:RG.Rep G f=> x.activities.regularOccurrence Ω)∘ fun n=>(M n).kin) ((fun x:RG.Rep G f=> x.activities.regularOccurrence Ω)∘fun n=> (L n).kin); rw [ha,he]; exact hk
    have hT:Soul atTop (fun n=>(M n).down) (fun n=>(L n).down):= souls (slots h m) hu hv
    refine ⟨sweep hG.a ha.a,sweep hG.b ha.b,fun J hj=>?_,⟨_,_,_,nearby hX,nearby hV⟩,hT,hd,landhold h hu hv,hB⟩
    have hpX:= hu.mono_left hj; have hpL:= hv.mono_left hj
    refine ⟨souls (slots h (m+1)) hpX hpL,souls (slots h m) hpX hpL,fun i j k=> glitters (cylinders (ht.mf m) i j k) hpX hpL,fun i j k=>glitters (cylinders (ht.mn m) i j k) hpX hpL,fun i j k=>glitters (cylinders (ht.o m) i j k) hpX hpL,wilt hB hj,fun i V=> hG.glints hj i V,fun i V=> ha.glints hj i V⟩
section oasis
omit ht hd h hX hV hu hv
variable (R)
def safeTrans {S:Rep G f}(P:f.val=c.val*((B).S.block m).val)(Y: Epoch (plan m (A:=A) P W))(h:Y.tubes=orchestra A N P)(hp:Y.kin=S) (U: Boulevard.Chartlet R.shape A N m P S): Epoch.Port (x:=(B).clock.hatBeta m) (L:=D.L ((B).clock.J (m+1))) (μ:=R.shape.μ ((B).clock.J (m+1)) ((B).clock.J m)) (C:= R.shape.c ((B).clock.J (m+1)) ((B).clock.J m)) (R:=R.target ((B).clock.J (m+1)) ((B).clock.J m)) (o:=R.shape.o ((B).clock.J (m+1)) ((B).clock.J m)) Y:= cast (by unfold Epoch.Port Boulevard.Chartlet; rw [hp,h]) U
lemma bank {S:Rep G f}(P:f.val=c.val*((B).S.block m).val)(Y:Epoch (plan m (A:=A) P W))(h:Y.tubes=orchestra A N P)(hp:Y.kin=S)(U:Boulevard.Chartlet R.shape A N m P S): HEq (safeTrans R P Y h hp U) U:= by exact cast_heq _ U
local notation "q"=> R.target ((B).clock.J (m+1)) ((B).clock.J m)
local notation "C"=> R.shape.c ((B).clock.J (m+1)) ((B).clock.J m)
local notation "x"=> A.B.a.clock.hatBeta m
local notation "b"=>R.shape.o ((B).clock.J (m+1)) ((B).clock.J m)
local notation "μ"=>R.shape.μ ((B).clock.J (m+1)) ((B).clock.J m)
local notation "D'"=> D.L ((B).clock.J (m+1))
local notation "Z'"=> (X.p.profile ((B).clock.J m)).order
local notation "c'"=> R.walls ((B).clock.J (m+1)) ((B).clock.J m)
def deposits (M:Bank)(Y:Jams.Zoo («Q»:=q) («x»:=x) («C»:=C) («μ»:=μ) (L:= D') b M Z')
   {P:f.val=c.val*((B).S.block m).val}{Y': Epoch (plan m P W)} (_:Rep G f)(h:Y'.tubes=orchestra A N P)(hz:N>m)(g: ∀ i j k,j ≤ i → Bid.Sworn (A.B.M.H i j) k G) (U:Epoch.Port («x»:=x) (L:=D') («μ»:=μ) («C»:=C) (R:=q) (o:=b) Y'): Station M Chi.canonical U Z':= Classical.choice (Y c f _ _ U.laws.data.funds (h ▸ Pane.ovation A _ P hz g) _ U)
lemma spirit {P: StepData c f} {T V:Tube G P} {S W: Rep G f} {U: Cash c' x μ D' q b C T S} {X': Cash c' x μ D' q b C V W} (he:T=V)(hx:S=W)(ht:HEq U X') (i:ℕ) (w:ℝ): Meadow.barony U Chi.canonical i w=Meadow.barony X' Chi.canonical i w:= by subst V; subst W; rw [eq_of_heq ht]
variable {t t':ℝ}(hw:Jams.Wild R.shape A.delay)
variable {E F:ℕ→ℕ}
include hw h ht hd hX hV hu hv
open Slide
lemma swaths (H:∀ n, Rain.Zeal R.target R.shape A (u n) m)(T:∀ n,Rain.Zeal R.target R.shape A (v n) m)(huX:Tendsto E atTop atTop)(hvY:Tendsto F atTop atTop)(U W:ℕ→ Rain.lands A m)(hB:Glints atTop (fun n=>(U n).val) (fun n=>(W n).val))(g: ∀ i j k,j ≤ i → Bid.Sworn (A.B.M.H i j) k G) (s:Stars) (r: Site (Rain.moor R.target A m s)) : Yard.Loom Q 0 Finset.univ (fun n=> (H n).offers (E n) (U n) s r) (fun n=>(T n).offers (F n) (W n) s r):=by
     let P:= Rain.panes R.target A m s; let Z(n):= Racks R.target A (u n) m s (U n).val; let Y(n):= Racks R.target A (v n) m s (W n).val; let K':= listIn (Z 0); let D n:= book m P K' (u n) (Z n); let X' n:= book m P K' (v n) (Y n)
     have hz n:(D n).kin=Z n:= reads _ _ _ _ (hX n).2 rfl rfl rfl rfl
     have hy n: (X' n).kin= Y n:= reads _ _ _ _ (hV n).2 rfl rfl rfl rfl
     let I n:= safeTrans R P (D n) (seats m P K' _ (hX n).2 _) (hz n) ((H n).tiers s (U n)); let X n:= safeTrans R P (X' n) (seats m P K' _ (hV n).2 _) (hy n) ((T n).tiers s (W n)); obtain ⟨k,hk⟩:= quarters hw m
     have he: Accord D X' Q γ δ:= by
         refine allies h ht hu hv hX hV hd P K' Z Y hz hy ?_ Angel.empty hB
         change Angel (fun _=> (Pane.pale _ _).regularOccurrence Ω) (fun _=> (Pane.pale _ _).regularOccurrence Ω)
         rw [show (Pane.pale (pink R.target A m s) G).regularOccurrence Ω=0 from funext fun i=>funext fun j=> by simp [Activities.regularOccurrence,masked,Set.indicator,Pane.pale]]; exact Angel.empty
     let R' n:= deposits R k hk (Z n) (P:=P) (N:=u n) (seats m _ K' _ (hX n).2 _) (hX n).1 g (I n); let C' n:=deposits R k hk (Y n) (P:=P) (N:=v n) (seats m _ K' _ (hV n).2 _) (hV n).1 g (X n)
     have ha:= bannersL I X R' C' he rfl (Rain.jersey (A:=A) (m:=m)|>.1.le) huX hvY r 0
     have hf n: Meadow.barony (I n) Chi.canonical (E n) (γ n)= (H n).offers (E n) (U n) s:= spirit R (seats m P K' _ (hX n).2 _) (hz n) (bank R P _ _ _ _) (E n) _
     have hb n: Meadow.barony (X n) Chi.canonical (F n) (δ n)= (T n).offers (F n) (W n) s:= spirit R (seats m P K' _ (hV n).2 _) (hy n) (bank R P _ _ _ _) (F n) _
     simp_rw [hf,hb] at ha
     exact ha
end oasis
end YM.PhysicalNext.Repeat.Lark
