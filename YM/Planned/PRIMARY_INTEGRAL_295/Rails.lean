import YM.Planned.PRIMARY_INTEGRAL_295.Bunks
import YM.Planned.PRIMARY_INTEGRAL_295.Villa

/-!
Equalities not relating to changing μ. Uses q transfers `Diagonal` & `Roll`
in same Banks-to-Path Ledger and H.S.A0 from `flight`. Pre/post numbers
from exact r/Teller. All signs physical. This defines what cold comparison
is used by CONTACT transfer for post σ estimates. No existence L assertions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Rails
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place Matrix
open Bid (pulled bills Sworn stretch)
open Next.Free Next.Fluctuations Bunks
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {T : Finset Cover} {c f n : Side} {S : StepData c f} (s:Signed)

-- sampler structural setting. Need equality of imported colors, stage clips,
-- T trajectory and localization separately.
structure Ringlets (Q : Teller G) (B:Tube G S) (H H':Bed) :Prop where
   high : Teller.Funds Q S B
   tracks : Towers.Diagonal S H H' B.R
   turns : Spins (S:=S) (G:=G) B.R.A0
   tied : Attached H B.up ∧ Attached H' B.down ∧ Towers.Roll S H H' B.R B.high B.low
   axial : Bid.Sworn H' c G

namespace Ringlets
variable (A:Forest S.ratio) (B:Tube G S) {Q : Teller G} {H H':Bed} (b:Dir G c) (h:Ringlets Q B H H')

-- Tot relative + replica. True prediction at linear order.
def runway (W:Lines S.ratio.count): Dir G f:= Bid.stretch A (b,crick S A W b)

omit s in
lemma runway_rays (W:Lines S.ratio.count) (i:G.ColorIndex): parts G 1 (runway A b W) i = extracted S A (installed S.ratio W) *ᵥ parts G 1 b i:=by
   unfold runway; rw [crick_relative]; apply Work.F04.parts_stretch
include h
lemma luminous (i:G.ColorIndex):
    d 1 f *ᵥ parts G 1 (pulled (runway A b B.R.A0) s) i =
     (d 1 f * installed S.ratio B.R.A0) *ᵥ parts G 1 (pulled b s) i:=by
   let W:=B.R.A0; let X:=installed S.ratio W; let v:=Streets.pledge X b; let u:=runway A b W
   have hu : d 1 f *ᵥ parts G 1 u i=d 1 f *ᵥ parts G 1 v i:=by
      rw [show parts G 1 u i= _ from runway_rays A b W _, mulVec_mulVec]
      have he : d 1 f*extracted S A X=d 1 f*X := by
         unfold extracted; rw [Matrix.mul_add,← Matrix.mul_assoc (d 1 f) (d 0 f),Exterior.closed 0 f]; simp
      rw [he, ← mulVec_mulVec]; exact congr_arg ((d 1 f).mulVec ·) (funext fun j=>(Streets.code ..).symm)
   rw [← mulVec_mulVec, show (installed S.ratio B.R.A0) *ᵥ parts G 1 (pulled b s) i=parts G 1 (pulled v s) i from ?eqn]
   · change d 1 f *ᵥ parts G 1 (pulled u s) i=d 1 f*ᵥ parts G 1 (pulled v s) i
     rw [colored_turn,colored_turn]; funext p; obtain ⟨x,p⟩:=p; obtain ⟨p,rfl⟩:=plaqEquiv.surjective p; rw [show plaqEquiv p = plaquette p from rfl, rotations_d, rotations_d,hu]
   rw [show pulled v s=Streets.pledge X (pulled b s) from (h.turns s b).symm]; exact funext (fun j=> (Streets.code ..).symm)

lemma wavy (k:S.Choices) : pulled b s - bills S (pulled (runway A b B.R.A0) s)=S.kernel.penalty⁻¹ • land H' (pulled b s):=by
   have he := (stationed A (installed S.ratio B.R.A0) _ _ h.tracks.trial).1
   let u:=runway A b B.R.A0
   have hx : S.patch.Branches S.kernel G:= h.high.knobs.symm ▸ h.high.kernel
   rw [← pred_fibre s hx k, ←split_cost]
   have ht : b-bills S u=S.kernel.penalty⁻¹ • land H' b:=by
     ext i j
     have hp := runway_rays A b B.R.A0 j
     have hv: probe S*ᵥ parts G 1 u j=parts G 1 b j-S.kernel.penalty⁻¹ • (K (H'.metric.acts c)*ᵥ parts G 1 b j) := by
        rw [show parts G 1 u j=_ from hp,mulVec_mulVec,he,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
     change b i j - ((probe S)*ᵥ parts G 1 u j) i = _ * (land H' b i) j
     rw [hv, show (land H' b i) j= (K (H'.metric.acts c)*ᵥ parts G 1 b j) i from Streets.code ..]
     change b i j-(b i j- _ *_)=_; abel
   change pulled (b-bills S u) s=S.kernel.penalty⁻¹ • land H' (pulled b s); rw [ht,scaled,swapped s H' h.axial]

-- every signed row. even if physical negative edges occur from canonical, don't
-- appeal to microscopic symmetry of shifted curvature coefficient.

theorem cool_row (k:S.Choices):
    let a := pulled (runway A b B.R.A0) s; let g:=pulled b s; let y:= xLin B.low B.down g
    (∀ p,xLin B.high B.up a p - Pressure.zip (flatF B) y p=0) ∧
      ∀ i,zLin S a g i - Pressure.zip (flatI B) y i = 0:=by
   intro a g y
   obtain ⟨R,R',hr,hr'⟩:=h.high.feeds; rw [← h.high.low,← h.high.high] at * -- revise
   obtain ⟨hf,hc,hA⟩:=h.tied
   let E:=Work.E03.meshEquiv c
   let D:=Work.E03.meshEquiv f; let F:=Work.E03.poleEquiv c
   let Y:= H'.full B.low c; let Z:= H.full B.high f; let M:= installed S.ratio B.R.mf; let L:=B.R.mn.acts c
   let X:= installed S.ratio B.R.A0
   have hY(j:G.ColorIndex):(fun i=> y (E.symm i) j)=(Y*d 1 c)*ᵥ parts G 1 g j:=by
     funext i; have he := xLin_component B.low B.down H' hr' hc g (E.symm i) j
     change _=((Y*d 1 c)*ᵥ parts G 1 g j) (E (E.symm i)) at he; rwa [Equiv.apply_symm_apply] at he
   constructor
   · intro p; apply sub_eq_zero.mpr; ext j
     have hx:=scalar_zip M D E y p j; rw [hY,mulVec_mulVec, ←Matrix.mul_assoc,show M*Y*d 1 c=Z*d 1 f*X from hA.fPart] at hx
     rw [xLin_component B.high B.up H hr hf]; rw [← mulVec_mulVec, show d 1 f *ᵥ parts G 1 a j=_ from luminous s A B b h _,mulVec_mulVec]
     rw [←Matrix.mul_assoc]; exact hx.symm
   intro p; apply sub_eq_zero.mpr; ext j
   let u:= Real.sqrt S.kernel.penalty
   have hx:= scalar_zip L F E y p j; rw [hY, mulVec_mulVec, ← Matrix.mul_assoc, show L*Y*d 1 c=u⁻¹ • K (H'.metric.acts c) from hA.nPart,Matrix.smul_mulVec] at hx
   have hv : u*S.kernel.penalty⁻¹=u⁻¹:=by
      have ht:= S.kernel.penalty_pos; have h1 :0<u:= Real.sqrt_pos.mpr ht; have hU:=show u^2=S.kernel.penalty from Real.sq_sqrt ht.le; field_simp; nlinarith
   calc
    _ = u * (g-bills S a) (F p) j := rfl
    _ = u⁻¹*((K (H'.metric.acts c)*ᵥ parts G 1 g j) (F p)) := by
      rw [show g-bills S a=_ from wavy s A B b h k]; change u*(_*(land H' g (F p)) j)=_
      rw [← mul_assoc,hv, show (land H' g (F p)) j=_ from Streets.code ..]; rfl
    _ = _:= hx.symm
end Ringlets
end YM.Planned.PrimaryIntegral295.Rails
