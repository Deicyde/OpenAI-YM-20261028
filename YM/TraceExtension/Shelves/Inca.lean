import YM.TraceExtension.Slate.Pave
import YM.TraceExtension.Anchor.Bleed
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate Next.UVStress
open ProofPorts.GridRealModelsEstimates20261012
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}(I:Watch C) (k N p d:ℕ)
set_option quotPrecheck false
local notation "n"=> C.side k p
local notation "T"=> C.path
local notation "b!"=> C.beta N p
def Fold (F:Peat G (C.side k p)) (z:Cover):= if h:k≤ N then moment (C.beta N p) (fun U=> backTo C.path N p h (alto C.path k d • filmR F) U * I.plot N p (Lattice.translate (- location C.S k N p z) U)) else 0
lemma Fold_eq(f:Guilds C)(x:Cover)(hp:k≤ N): Pull.smoke I x (beamC C d (Tales f)) k N p= Fold I k N p d (f k N p) x:=by unfold Pull.smoke Fold beamC; rw [dif_pos hp]; simp only [dif_pos hp];rfl
variable {k N p d}
lemma Fold_null (u:Cover)(h:k≤ N): Fold I k N p d 0 u=0:=by
   rw[Fold,dif_pos h]; simp_rw [show filmR (0:Peat G (C.side k p))=0 from funext fun i=> by simp[filmR], smul_zero, show backTo C.path N p h (0:Film G (C.side k p))=0 from backTo_const C.path N p h 0]; simp[Wilson.moment]
def beamA (I:Watch C)(l k N p d:ℕ)(u:Cover)(f:Film G (C.side N p)):=fun U=>f U* I.plot N p (Lattice.translate (-location C.S k N p u) U)
lemma beam_env (u:Cover){f:Film G (C.side N p)}(hf:Envelope f): Envelope (beamA I k k N p d u f):=hf.mulC (by
    apply Envelope.compactC; unfold Watch.plot; apply continuous_finsetProd; intro j _; exact (C.continuousO ..).comp (show Continuous (Lattice.translate _ : Config G _→ Config G _) from by unfold Lattice.translate; fun_prop))
lemma EnvAlto {F:Peat G (C.side k p)}(d:ℕ)(hp:Envelope (filmR F)): Envelope (alto C.path k d • filmR F):= (Envelope.constC _).mulC hp
lemma Fold_add (u:Cover)(h:k≤N){f g:Peat G (C.side k p)}(hf:Envelope (filmR f))(hg:Envelope (filmR g)): Fold I k N p d (f+g) u=Fold I k N p d f u+Fold I k N p d g u:=by
    unfold Fold; simp only [dif_pos h]; rw[ (plush ∅ f g (C.path.rep N p k) 0).1,smul_add]; let v:= alto C.path k d; let F:= v • filmR f; let Q:=v • filmR g
    have hp:Envelope F:=EnvAlto d hf;have ht: Envelope Q:=EnvAlto d hg; rw [backTo_add C.path N p h hp ht]; unfold Wilson.moment; simp only [Pi.add_apply,add_mul]; exact integral_add ( (beam_env I (k:=k) (d:=d) u (backTo_env C.path N p h hp)).integrableC _) ((beam_env I (k:=k) (d:=d) u (backTo_env C.path N p h ht)).integrableC _)
lemma coatsS (x:ℝ)(f:Peat G n): filmR (x • f)= (x:ℂ) • filmR f:=by ext1 u;simp [filmR]
lemma CoatShift (x:Site n)(f:Peat G n): filmR (rj x f)= (filmR f) ∘ Lattice.translate x:=rfl
lemma book_s (x:ℝ)(u:Cover)(hk:k≤N)(f:Peat G (C.side k p)): Fold I k N p d (x • f) u=x • Fold I k N p d f u:=by
   unfold Fold; simp only [dif_pos hk]; rw[coatsS,smul_comm (alto ..), backTo_linear (C:=C)]; unfold Wilson.moment; simp only[Pi.smul_apply,smul_eq_mul, mul_assoc, integral_const_mul];rfl
lemma locator (hk:k ≤ N)(x y:Cover): location C.S k N p (x+y)=location C.S k N p x+location C.S k N p y:=by
   unfold Cells.location; simp only[dif_pos hk,map_add]; exact (C.S.toDepth hk p).root.map_add ..
lemma back_long (hk:k≤N)(u:Cover)(f:Peat G n)(v:ℂ)(hp:Envelope (filmR f)):
    let x:=wrap (C.side k p) u; backTo C.path N p hk (v • filmR (rj x f)) = (backTo C.path N p hk (v • filmR f)) ∘ Lattice.translate (location C.S k N p u) :=by
    intro x; have he:=backTo_orient (F:=v • filmR f) C.path N p (le_refl k) hk x 1 ((Envelope.constC _).mulC hp);
    have hs : anchor C.S p (le_refl k) x=x:=by unfold anchor; change (C.S.toDepth (le_refl k) p).embed x=x; unfold Ratio.embed Schedule.toDepth; simp only[tsub_self,Schedule.steps]; rw[show (1:Side).val=1 from rfl,one_smul,wrap_lift]
    rw[hs] at he; rw[show location C.S k N p u=anchor C.S p hk x from ?_]; swap; · rw [Cells.location,dif_pos hk]
    rw [show v • filmR (rj x f)= (v • filmR f) ∘ pull 1 x from funext fun i=> by simp only[CoatShift,comp_apply,pull_one];rfl,he]; ext1 U; rw [Function.comp_apply,pull_one];rfl
lemma Fold_step (u z:Cover)(h:k≤N){f:Peat G (C.side k p)} (hf:Envelope (filmR f)) : Fold I k N p d (rj (wrap _ z) f) u = Fold I k N p d f (u+z):=by
   unfold Fold; simp only [dif_pos h]; rw [back_long h z f _ hf]; let Q(x:Cover):=location C.S k N p x
   let F':= backTo C.path N p h (alto C.path k d • filmR f); let F:=beamA I k k N p d (u+z) F'; let P(U):= F' (Lattice.translate (Q z) U) * I.plot N p (Lattice.translate (- Q u) U)
   change moment (b!) P=moment _ F
   have hv : Envelope F:= beam_env I _ (backTo_env C.path N p h (EnvAlto d hf))
   rw [←moment_pull (C.beta N p) 1 (Q z) F (hv.integrableC _)]
   apply congr_arg (moment _);ext1 i; unfold P F beamA; simp only [Function.comp_apply,pull_one]
   rw [locator h]; refine congr_arg (F' (Lattice.translate (Q z) i) * ·) (congr_arg (I.plot N p) (show Lattice.translate _ i=Lattice.translate _ _ from ?_));
   have he : Perfect.ride (- (Q u + Q z)) (Perfect.ride (Q z) i)=Perfect.ride (-Q u) i:=by rw [pace_add,show -(Q u + Q z) + Q z= -Q u from by abel]
   exact he.symm
end YM.Trace.Shelves
