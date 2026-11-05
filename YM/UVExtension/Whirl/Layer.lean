import YM.UVExtension.Whirl.Arch
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Whirl
open PhysicalNext PhysicalNext.Repeat
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    (H : Cash W s μ L Q o α T I) (p : BudgetPoint) {J : Cash W s μ L Q o α T R} (χ : Chi)
    (X : Alliance H J 1 0)

def wheelK (s: Signed)(t: Site c)(π:R.activities.Moves s (S.ratio.embed t)) : Equiv.Perm (Leaf H):= Refrain.congo (gate H X) (gate J (swing J π))
def spinK (s: Signed)(t: Site c)(π:R.activities.Moves s (S.ratio.embed t)) : Equiv.Perm (Annual H):=
    Equiv.sumCongr (wheelK H X s t π) (Equiv.prodCongr (Equiv.refl ℕ) (StepData.sendSites s t))
lemma duty (s : Signed) (t : Site c) (π : R.activities.Moves s (S.ratio.embed t)) (f:Equiv.Perm (Leaf H))(hf:∀ i,gate H X (f i)=gate J (swing J π) (gate H X i)): let z:= (Equiv.sumCongr f (Equiv.prodCongr (Equiv.refl ℕ) (StepData.sendSites s t)))
    ∀ i,
    (reserve H (z i)).support=(reserve H i).support.image (affine s t) ∧ (reserve H (z i)).inventory=(reserve H i).inventory.image (affine s t) ∧
      ∀ U, ((reserve H (z i)).extraTest U↔(reserve H i).extraTest (pull s t U)) ∧ fuse H X χ (z i) U=fuse H X χ i (pull s t U) :=by
  intro z
  unfold z
  rintro (i|⟨i,b⟩)
  · have hk U := buoyant H X χ s t π f i U (hf i)
    simp only [Equiv.sumCongr_apply,Sum.map_inl]
    exact ⟨(hk 1).1,(hk 1).2.1,fun U=> ⟨Iff.rfl,(hk U).2.2⟩⟩
  simp only [Equiv.sumCongr_apply,Sum.map_inr]
  simp [reserve,Refrain.fuse,Lattice.affine]; rfl
lemma linch (s : Signed) (t : Site c) (π : R.activities.Moves s (S.ratio.embed t)) : let z:= spinK H X s t π
    ∀ i,
    (reserve H (z i)).support=(reserve H i).support.image (affine s t) ∧ (reserve H (z i)).inventory=(reserve H i).inventory.image (affine s t) ∧
      ∀ U, ((reserve H (z i)).extraTest U↔(reserve H i).extraTest (pull s t U)) ∧ fuse H X χ (z i) U=fuse H X χ i (pull s t U) :=by
  have hp(i:Leaf H): (gate H X) ((wheelK H X s t π) i)= (gate J (swing J π)) ((gate H X) i):= by unfold wheelK; rw [perch (gate H X)]
  unfold spinK; exact duty H χ X s t π (wheelK H X s t π) hp
private def tip (s : Signed) (t : Site c) (π:R.activities.Moves s (S.ratio.embed t)) (f : Magazine H→ Config G c→ℝ) :
    let a:= Refrain.read H X χ (Beam.marquee H p).reg (choir f ∘ pennant H)
    a.Moves s t := by
  intro V; let η:=spinK H X s t π; have hη i:= linch H χ X s t π i
  let e:=Song.whirl (ι:=Magazine H) s t; let a:=pennant H; let k:=badge H
  have hk i : k (congo k η i)=_ := perch k η i; have ha i : a (congo a e i)=_ := perch a e i
  let h x:= spirit (Beam.contents H p) f s t x
  refine ⟨congo a e,congo k η,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩
  · change (revolve _ (a (congo a e i))).site=_; rw [ha]; exact (h _).1
  · change (revolve _ (a (congo a e i))).support=_; rw [ha]; exact (h _).2.1
  · change (reserve H (k (congo k η i))).support=_; rw [hk]; exact (hη _).1
  · change (reserve H (k (congo k η i))).inventory=_; rw [hk]; exact (hη _).2.1
  · change (reserve H (k (congo k η i))).extraTest V ↔ _; rw [hk]; exact ((hη (k i)).2.2 V).1
  · change choir f (a (congo a e i)) V=_; rw [ha]; exact congr_fun (h (a i)).2.2 V
  change fuse H X χ (k (congo k η i)) V=_; rw [hk]; exact ((hη (k i)).2.2 V).2


variable {V: RG.Rep G f} {J':Cash W s μ L Q o α T V}
lemma shot {σ:Signed}{τ:Site c}(X' : Match.Alliance H J' 1 0)(π:R.activities.Moves σ (S.ratio.embed τ))(φ:V.activities.Moves σ (S.ratio.embed τ))(h:Concert.KinBase R V)(he:Twins π φ)(ht:X.units=X'.units): spinK H X σ τ π=spinK H X' σ τ φ:=by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=V; obtain ⟨hy,hp,hq,hg,hH⟩:=h; dsimp only at hy hp hq hg hH; subst_vars
  rcases X with ⟨v,hv,hz⟩; rcases X' with ⟨w,hW,hP⟩; dsimp only at ht; subst_vars
  rcases π with ⟨ep,kp,u,v,w,t,y,a,b⟩; rcases φ with ⟨ep',kp',A,H,F,G,T,X,Y⟩; obtain ⟨he,ht⟩:=he; dsimp only at he ht; subst_vars; rfl
lemma taps {σ:Signed}{τ:Site c}(X' : Match.Alliance H J' 1 0)(π:R.activities.Moves σ (S.ratio.embed τ))(φ:V.activities.Moves σ (S.ratio.embed τ))(h:Concert.KinBase R V)(he:Twins π φ)(ht:X.units=X'.units)(F F': Magazine H→ Config G c→ℝ):
    Twins (tip H p χ X σ τ π F) (tip H p χ X' σ τ φ F'):= by refine ⟨rfl,?_⟩; exact congr_arg (Refrain.congo (badge H)) (shot H X X' π φ h he ht)
-- export defs with arities
def tips (s:Signed) (t:Site c)(π:R.activities.Moves s (S.ratio.embed t))(k:ℕ)(γ:ℝ): ((Beam.marquee H p).read (Meadow.timbres X (χ:=χ) γ k)).Moves s t:= tip H p χ X s t π _
lemma tips_twin {σ:Signed}{τ:Site c}(X':Match.Alliance H J' 1 0)(π:R.activities.Moves σ (S.ratio.embed τ))(φ:V.activities.Moves σ (S.ratio.embed τ))(h:Concert.KinBase R V)(he:Twins π φ)(ht:X.units=X'.units) (k:ℕ)(u w:ℝ):
    Twins (tips H p χ X σ τ π k u) (tips H p χ X' σ τ φ k w):= taps H p χ X X' π φ h he ht _ _
end YM.UVExtension.Whirl
