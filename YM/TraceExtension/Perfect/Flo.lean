import YM.TraceExtension.Perfect.Native
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Planned.PrimaryIntegral295 Next.Free Org Input Extra.Histories
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A: Alloy M D} {W:Type} {F:Filter W}
section
variable (N p: W→ℕ) {m:ℕ} (hk:∀ w:W,m+1<N w) (E:Ember A.B.a m)(hf:Tendsto (fun w=>(A.B.a.S.side (m+1) (p w)).val) F atTop)
set_option quotPrecheck false
local notation "K"=>A.B.kin
local notation "P"=> (A.B.a.params (m+1))
local notation "x!"=>A.B.a.clock.hatBeta
local notation "Y!"=>x! (m+1)
include hk E hf
lemma stanch :∃ k:∀ w,Dart G (A.B.a.S.side (m+1) (p w)),(∀ w,(k w).Sound ((K).path (N w) (m+1)) (P).clip) ∧ Saving F k (east Y!) (reed Y!) (vista 0 Y!):=by
 let D(w):=(A.B.a.S.side (m+1) (p w)); let R(w):=(K).path (N w) (m+1); let k(w):= dawn (P).clip (R w) (D w); let b(w):=A.B.M.H (N w) (m+1)
 have hx(w):=(A.B.support.cap _ _ (hk w).le); have hh(w):=A.B.plan.all _ _ (hk w).le (D w); have hz(w):=A.B.support.links _ _ (hk w).le
 have hr(w):Bid.Sworn (b w) (D w) G:= (Edens.laureates A.B.a A.B.M A.B.plan (N w) (m+1) (p w) (hk w)).2.2
 have h0 w: (k w).Sound (R w) (P).clip:= ivy (hx w) (hh w) (hz w) (hr w)
 obtain ⟨hT,⟨C,c,H,s⟩,Q⟩:= E.stem; have ho i :2 ≤ i → C ≤ reed Y! i:= fun h=>s.trans (pow_le_pow_right₀ hT h)
 refine ⟨k,h0,fun a b x i hP hi=>?_,fun a x i hv hi=>?_,fun a x i he h=>?_,fun a x i he h=> Ear.empty (c.trans (ho i h)),fun a b j i v _ h=> Ear.empty (c.trans (ho v h)),fun a b x=>⟨fun w=>(loom_read ((h0 w).heart ..)).2.2,verdant x hf a b⟩,fun a x=>⟨fun w=>(rain_read ((h0 w).palm ..)).2.2.1, varsity x hf a⟩,fun a x=>?_⟩
 · exact ⟨fun w=>(loom_read ((h0 w).heart ..)).2.2, earns.eventually (Eventually.of_forall fun w=>(H.J (D w) (x w) a b i hP).trans (ho i hi))⟩
 · exact ⟨fun w=>(rain_read ((h0 w).palm ..)).2.2.1, earns.eventually (Eventually.of_forall fun w=>(H.Y (D w) (x w) a i hv).trans (ho i hi))⟩
 · refine ⟨fun w=>(loom_read ((h0 w).plum ..)).2.2, earns.eventually (Eventually.of_forall fun w=> ?_)⟩
   rw [vista,pow_zero,one_mul]; exact Q _ _ (hx w) _ _ _ i he h
 refine ⟨fun w=>(loom_read ((h0 w).plum ..)).2.2, ?_⟩
 rcases isEmpty_or_nonempty W with hw|hw
 · have hb:F=⊥:= Subsingleton.elim ..; subst F;exact ⟨fun i j _=> tendsto_bot⟩
 have hH(w):=(A.B.plan.rows _ _ (hk w).le).2.1
 let w:= Classical.arbitrary W; let X:= hH w (plaquette ⟨(0,1),by decide⟩) (plaquette ⟨(0,1),by decide⟩); have hv:= (tsum_nonneg X.1).trans X.2.2
 exact dust_race x hf b hh (M.K.alpha_pos _) hv hH R (fun _=>A.B.a.clock.loopCap _) hx hz hr a
end

variable (N p: W→ℕ) (A) (h:Vigil A.B.a) (F:Filter W) (hP:∀ m:ℕ,Tendsto (fun w=> (A.B.a.S.side m (p w)).val) F atTop)
set_option quotPrecheck false
local notation "K!"=> A.B.kin
local notation "x!"=> A.B.a.clock.hatBeta
local notation "j!"=> A.B.a.params
include h hP
lemma through (m n:ℕ)(hE:∀ k,m≤k→Nonempty (Ember A.B.a k))(hk:∀ w:W,m+(n+1)<N w) : ∃ k :∀ w,Dart G (A.B.a.S.side m (p w)),(∀ w,(k w).Sound (A.B.kin.path (N w) m) (A.B.a.params m).clip)∧Saving F k (east (x! m)) (reed (x! m)) (vista (n+1) (x! m)) :=by
 induction n generalizing m with
 | zero => obtain ⟨E⟩:= hE m le_rfl; obtain ⟨k,hs,hV⟩:= stanch N p hk E (hP _); exact pay_step _ _ _ _ hk E (hP m) hs 0 hV
 | succ n ih=>
   obtain ⟨k,hk',H⟩:= ih (m+1) (fun i hi=>hE i (by omega)) (fun w=>by have hp:=hk w; omega)
   obtain ⟨E⟩:=hE m le_rfl; exact pay_step _ _ _ _ (fun w=> lt_trans (b:=m+(n+1+1)) (by omega) (hk w)) E (hP _) hk' (n+1) H
end YM.Trace.Perfect
