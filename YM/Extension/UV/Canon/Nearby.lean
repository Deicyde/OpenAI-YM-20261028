import YM.Extension.UV.Canon.Producer
noncomputable section
set_option autoImplicit false
namespace YM.Extension.UV
open Function Filter Set Lattice Wilson Pressure RG RG.Supply RG.Shoot Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open PhysicalNext ThroughLaunch Repeat Graces Roost Mallow PhysicalNext.Repeat.Legato
open WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset Time
open Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology BigOperators Classical
variable {G:Gauge}
variable {X: Metals G} {D:Rolls X.p}{A:Alloy X D} (R : Factor A) (h:Archive A.B)
include h R
lemma nearCanonical (g:G.Simple) (N p) {b} (hb: NearTarget A.B.a b) : ∃ F : Trail A.B.a p, Competes A.B.bake p N 0 F ∧ (F 0).beta=b ∧ (∀ m (_hm:m<N), A.B.Move N m p (F m) (F (m+1)) ∧ Protected R N m p (F m) (F (m+1))) ∧ F N=Startup.canonical A.B.kin N p (F N).beta:=by
  let B:= A.B
  let Y := { A.B.bake with next:=fun N m p u v=> A.B.Move N m p u v ∧ Protected R N m p u v∧Accurate A.B R.post N m p u v,
                           first:=fun N p v=> A.B.bake.first N p v∧ HasSlots v.p v.activities ∧ v=Startup.canonical A.B.kin N p v.beta }
  have he N m p u: Lives Y N m p u ↔ Lives A.B.bake N m p u := by constructor <;> rintro ⟨a,b,c,d,e⟩ <;> exact ⟨a,b,c,d,e⟩
  have hp N p:Y.Issues N p:=by
    constructor
    · have hX := topmenu h N p
      refine ⟨_,hX.starts,?_⟩; intro x hx
      obtain ⟨hv,hB,ht,hZ⟩:= canStart R h N p x hx; exact ⟨hv,(he ..).2 hB,ht.scalars,ht.raw,ht.inits,hZ,rfl⟩
    intro m hm l t hl Q hc hx
    obtain ⟨H⟩:= faces R Q hl hc (fun x hy=> ⟨(he ..).1 (hx x hy).1,(hx x hy).2⟩) hm
    obtain ⟨hq,hp⟩:= H.moves g hm
    refine ⟨H.result,hq,fun x hy=>?_⟩; obtain ⟨hx,hK,-,-⟩:= hp x hy; exact ⟨(he ..).2 hx.bundle,hx.ident,(A.B.links hm hx).drift,hx,⟨l,t,Q,H,x,hy,rfl,rfl⟩,(by rw [show Accurate A.B R.post N m p (H.result x) (Q x)= (|(H.result x).beta - UVNext.CouplingReset.predictor A.B N Q x| ≤ UVNext.CouplingReset.width A.B.a m R.post) from by unfold Accurate UVNext.CouplingReset.predictor; rw [sub_add_eq_sub_sub]]; exact hK)⟩
  obtain ⟨T,hT,H⟩:= trial (p:=p) (R:=Y) hb g (Drifting.pay A.B.valid) (hp N p)
  have hM (m:ℕ)(hm:m<N): A.B.Move N m p (T m) (T (m+1)):= ((hT).persists m (Nat.zero_le _) hm).continues.1
  have hf := hT.fromTop
  exact ⟨T,⟨fun i hi hj=>⟨(he ..).mp ((hT.prices i hi hj).1),(hT.prices i hi hj).2⟩,⟨hf.scalars,hf.raw,hf.inits.1⟩,fun i _ hi'=>A.B.links hi' (hM i hi')⟩,H, fun m hm=> ⟨hM m hm, ((hT.persists m (Nat.zero_le _) hm).continues).2.1⟩,hf.inits.2.2⟩
omit h R

structure GoodRace (X:UVBuild G) (t:ℝ) (f:ℕ→∀ p,Trail X.tower.a p): Prop where
   stays : X.tower.bake.Stays f
   target N p : (f N p 0).beta=t
   advances N m p (hm:m < N): X.tower.Move N m p (f N p m) (f N p (m+1)) ∧ Protected X.works N m p (f N p m) (f N p (m+1))
   canonical N p : (f N p N)=Startup.canonical X.tower.kin N p (f N p N).beta
variable {X:UVBuild G} (hs:X.Shared) (hz:Secure X) (ht:AttachedStart X) (g:G.Simple)
omit hz
include hs ht g
lemma goodRaces b (hb:NearTarget X.tower.a b) : ∃ f, GoodRace X b f ∧ (b=X.tower.a.clock.bar → f=X.engine.history) := by
  let B:=X.tower
  by_cases he : b=B.a.clock.bar
  · exact ⟨X.engine.history,⟨X.engine.sticks,fun _ _=> he ▸ X.engine.choice.reaches ..,fun N m p hm => ⟨X.engine.moves _ _ _ hm, (hs.same.nest.held _ _ _ hm).1⟩,ht.2⟩,fun _=>rfl⟩
  · choose f h₁ h₂ h₃ h₄ using fun N p=> nearCanonical X.works ht.1 g N p hb
    exact ⟨f, ⟨h₁,h₂,fun N m p=> h₃ N p m,h₄⟩, fun ha => (he ha).elim⟩

include hs ht g
lemma chooseGoodRaces : ∃ f : ℝ→ℕ→∀ p,Trail X.tower.a p, f X.tower.a.clock.bar=X.engine.history ∧ ∀ b,NearTarget X.tower.a b → GoodRace X b (f b):= by
  choose f h' using fun b : {b:ℝ//NearTarget X.tower.a b}=>goodRaces hs ht g b.1 b.2
  let t b : {b:ℝ//NearTarget X.tower.a b} := ⟨if NearTarget X.tower.a b then b else X.tower.a.clock.bar, by split_ifs with hh <;> [exact hh; simpa only [NearTarget,sub_self,abs_zero] using (margin_pos (a:=X.tower.a) g).le]⟩
  have ha b (hx:NearTarget X.tower.a b): (t b).1=b:= by exact if_pos hx -- simplify
  refine ⟨fun b=> f (t b), (h' _).2 (by dsimp [t]; split_ifs <;> rfl),fun b hb=> ?_⟩
  exact Eq.mp (congr_arg (fun v=> GoodRace X v (f (t b))) (ha b hb)) (h' (t b)).1
omit hs ht
namespace GoodRace
variable {b f} (H:GoodRace X b f)
include H
omit g in
lemma drift (N p i) (hi:i ≤ N) : |(f N p i).beta-X.tower.a.clock.hatBeta i| ≤ (G.slopeConstant/4)*X.tower.a.S.scale i + |b-X.tower.a.clock.bar|:= by
  induction i with
  | zero => rw [H.target]; simp [Calendar.hatBeta]
  | succ i ih=>
    have ht := ((H.stays N p).persists i (by omega) hi).drift
    calc
      _ = |(f N p i).beta-X.tower.a.clock.hatBeta i + ((f N p (i+1)).beta-(f N p i).beta-jump X.tower.a i)| := by congr 1; rw [step_hat]; ring
      _ ≤ _ := (abs_add_le ..).trans ((add_le_add (ih (by omega)) ht).trans (by have h := (Drifting.pay X.tower.valid) i; have hu := (div_le_iff₀ (block_positive X.tower.a i)).mp h; rw [Schedule.scale_succ]; linarith))
lemma domainMargin (hb: |b-X.tower.a.clock.bar| ≤ X.tower.a.clock.bar/8) (N p i : ℕ) (hi:i ≤ N) {x:ℝ} (hx:|x-(f N p i).beta| ≤ contour (X.tower.a.clock.hatBeta i)/8): x ∈ Startup.strictBand X.tower.a i:= by
  have hd:= H.drift _ p _ hi
  have h₁ := contour_bound X.tower.a i
  unfold Startup.strictBand; rw [mem_Icc]
  have h₂ := scale_nn X.tower.a i
  have hg := Gauge.slopeConstant_pos g
  unfold Calendar.hatBeta Levels.S at *
  constructor <;> nlinarith [h₁.2,X.tower.a.clock.bar_pos,(abs_le.mp hd).1,(abs_le.mp hd).2,(abs_le.mp hx).1,(abs_le.mp hx).2]
-- two abs add to ≤ (1/4+1/8)*slope scale + 1/4 bar <=3/8 of hat yes.
end GoodRace

end YM.Extension.UV
