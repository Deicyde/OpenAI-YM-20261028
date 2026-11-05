import YM.FullVolume.Auvi.Entries
import YM.FullVolume.Renew.Ready
import YM.FullVolume.Sym.Chill
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
variable (m:ℕ)(Z:f.val=c.val*(A.B.a.S.block m).val)(W:Listing G f)(N:ℕ)
local notation "K"=> A.B.kin
local notation "B"=> A.B.a
abbrev plan := (⟨(A.B.a.params (m+1)).clip,(A.B.a.params m).clip,(A.B.a.budget (m+1)),W.reg,W.hard⟩ : Era G (panel A m Z))
abbrev book (S: Rep G f): Epoch (plan m Z W) := ⟨(Pane.orchestra A N Z).R,Cad.pure (A.B.kin.path N (m+1)),Cad.pure (A.B.kin.path N m), S.activities.E,S.activities.K,S.beta,S.v⟩ -- R name check
abbrev Prairie (H: PathData G):Prop:= (Cad.pure H).path=H
private lemma paths {P Q:PathData G} (h:P.row=Q.row)(g:P.loop=Q.loop)(x:P.cubic=Q.cubic)(w:P.quartic=Q.quartic):P=Q:=by rcases P; rcases Q; congr
lemma shallows (h:Stationary.Artes.Cadre A.post K):∀ᶠ n:ℕ in atTop, Prairie ((K).path n m):=by
   obtain ⟨X,V,vx,hp,H⟩:= h.evolution m; obtain ⟨f,T,p,q,hp,hK,hT⟩:=H.stars
   filter_upwards [hT,H.hearth.flit] with n hn hA
   refine paths (funext fun j=> funext fun i=> Prod.ext rfl (hA j i|>.symm)) (funext fun i=>?_) (funext fun i=>?_) (funext fun i=> ?_)
   · change (⟨_,(((K).path n m).loop i).coeff⟩ : Atom G 2)=_; rw [hn.1]; rfl
   · change (⟨_,(((K).path n m).cubic i).coeff⟩ : Atom G 3)=_; rw [hn.2.1]; rfl
   change (⟨_,(((K).path n m).quartic i).coeff⟩ : Atom G 4)=_; rw [hn.2.2]; rfl
abbrev Ionic (N m:ℕ)(A :Alloy X D):= Prairie (A.B.kin.path N m)∧ Prairie (A.B.kin.path N (m+1))
lemma follows(h:Stationary.Artes.Cadre A.post K){φ:ℕ→ℕ}(he:Tendsto φ atTop atTop)(M:ℕ): ∀ᶠ k in atTop,Ionic (φ k) M A:=he.eventually ((shallows M h).and (shallows _ h))
private lemma repex {S T: Rep G f} (h:S.path=T.path)(hm:S.clip=T.clip)(hp:S.p=T.p)(ha:listIn S=listIn T)(hb:S.beta=T.beta)(hv:S.v=T.v)(hE:S.activities.E=T.activities.E)(hK:S.activities.K=T.activities.K): S=T:=by
   rcases S with ⟨_,_,⟨_,_,_,_⟩,_⟩; rcases T with ⟨_,_,⟨_,_,_,_⟩,_⟩; dsimp only [listIn] at *; congr 2; all_goals injection ha
lemma seats (h:Ionic N m A)(S:Rep G f) : (book m Z W N S).tubes=orchestra A N Z:=by
    unfold book Epoch.tubes orchestra; dsimp only; rw [h.1,h.2]
lemma reads (h:Ionic N m A){S:Rep G f}(hw:listIn S=W)(hp:S.p=(B).budget (m+1))(hx:S.clip=((B).params (m+1)).clip)(ht:S.path=(K).path N (m+1)): (book m Z W N S).kin=S:=by
    subst W; exact repex (h.2.trans ht.symm) hx.symm hp.symm rfl rfl rfl rfl rfl
variable {W m N}{Z}
lemma slots (h: Stationary.Artes.Cadre A.post K)(m:ℕ) : Soul atTop (fun i=> Cad.pure ((K).path i m)) (fun i=> Cad.pure ((K).path i m)) :=by
   obtain ⟨X,V,vx,hp,H⟩:= h.evolution m; obtain ⟨f,T,p,q,hp,hK,hT⟩:=H.stars
   refine ⟨fun i j=>⟨_,H.hearth.ink i j,H.hearth.ink i j⟩,fun i j=>?_,fun i j=>?_,fun i j=>?_⟩
   · have ht : Tendsto (fun n=> (((K).path n m).loop i).coeff j) atTop (𝓝 ((ringT V.e2.δ T.a i).coeff j)):= ((hp.a.hinge (i,j)).div_const _).congr' (hT.mono fun n hn=>by dsimp only; rw [hn.1]; rfl)
     exact ⟨_,ht,ht⟩
   · have ht : Tendsto (fun n=> (((K).path n m).cubic i).coeff j) atTop (𝓝 ((ringT V.e3.δ T.b i).coeff j)):= ((hp.b.hinge (i,j)).div_const _).congr' (hT.mono fun n hn=>by dsimp only; rw [hn.2.1]; rfl)
     exact ⟨_,ht,ht⟩
   have ht : Tendsto (fun n=> (((K).path n m).quartic i).coeff j) atTop (𝓝 ((ringT V.e4.δ T.c i).coeff j)):= ((hp.c.hinge (i,j)).div_const _).congr' (hT.mono fun n hn=>by dsimp only; rw [hn.2.2]; rfl)
   exact ⟨_,ht,ht⟩
variable {φ χ:Filter ℕ} {β γ:ℕ→ℕ}{S T:ℕ→ Cad G}
lemma glitters {ι:Type}[TopologicalSpace ι]{f g:ℕ→ι}(he:Glints φ f g)(ha:Tendsto β χ φ)(hb:Tendsto γ χ φ): Glints χ (f∘β) (g∘γ):=by obtain ⟨x,h,e⟩:=he; exact ⟨x,h.comp ha,e.comp hb⟩
lemma souls (he:Soul φ S T)(ha:Tendsto β χ φ)(hb:Tendsto γ χ φ): Soul χ (S∘β) (T∘γ):= ⟨fun i j=>glitters (he.1 i j) ha hb,fun i j=>glitters (he.2.1 i j) ha hb,fun i j=> glitters (he.2.2.1 i j) ha hb,fun i j=>glitters (he.2.2.2 i j) ha hb⟩
lemma cylinders {X Y:Type}{C:ℕ→Row X Y}(h:Next.Free.Loom C)(i j k) : Glints atTop (fun n=> C n i j k) (fun n=> C n i j k):= by
    obtain ⟨V,H⟩:=h; have he:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp H i) j) k; exact ⟨_,he,he⟩
lemma quarters (h:Jams.Wild R.shape A.delay)(m:ℕ): ∃ k,Jams.Zoo (Q:=R.target ((B).clock.J (m+1)) ((B).clock.J m)) (x:=(B).clock.hatBeta m) (C:=R.shape.c ((B).clock.J (m+1)) ((B).clock.J m)) (μ:=R.shape.μ ((B).clock.J (m+1)) ((B).clock.J m)) (L:=D.L ((B).clock.J (m+1))) (R.shape.o ((B).clock.J (m+1)) ((B).clock.J m)) k (X.p.profile ((B).clock.J m)).order:= h _ _ (A.B.valid.pays m) _ (step_paid B m)
end YM.PhysicalNext.Repeat.Lark
