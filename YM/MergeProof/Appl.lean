import YM.MergeProof.MixLaw
import YM.MergeProof.Record


/-!
# Exact consumable record of the signed unmarked branch and switching probes
-/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0) {y' ex dk:ℝ}(h: Usable M Y χ A rA K dk ex y')
def given (U: Config G f) : Poly B:=∑ i : Tickets (Palette.sign M S),(↑((team M i).cicada U * ∏ j∈i.val,rA j):ℂ) • (∏ j∈i.val,z j)
-- Requires Kept.Scalar exact. scale not scaled.
include Y
lemma which (U:Config G c) : S.push R.beta (given (S:=S) M rA B z) U=sound z (fun t p=> S.push R.beta (buy M (ways rA t p) S) U):=by
   let f(i:Tickets (Palette.sign M S)) U := (team M i).cicada U * ∏ j∈i.val, rA j
   let m i:= S.push R.beta (f i) U
   let g (i:Tickets (Palette.sign M S)) := click i.val (m i)
   have ht:S.IsKernel R.beta G:=S.isKernel (funds_branch Y.laws.intake.ready) _ -- namespace
   have hp i:Integrable (f i) (prior G _) := ((team M i).sells Y.laws.intake.cap|>.1.integrable _).mul_const _
   have hl t p : buy M (ways rA t p) S=fun U=>∑ i:Tickets (Palette.sign M S),click i.val 1 t p*f i U:=by
     ext U; unfold buy; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Palette.sale; rw [amplitudes]; unfold click; split <;> simp [f]; ring
   have he(t p): S.push R.beta (buy M (ways rA t p) S) U=∑ i, g i t p:=by
     unfold StepData.push; rw [hl]; simp_rw [smul_eq_mul,Finset.mul_sum, mul_left_comm (S.density _ _ _) (click ..)]
     rw [integral_finsetSum]; refine sum_congr rfl fun i _=>?_; rw [integral_const_mul]; change _*m i=_; unfold g click; split_ifs<;>ring
     intro i _; exact (StepData.push_slice ht U (f i) (hp i)).const_mul _
   rw [show (fun t p=> S.push R.beta _ _)=(∑ i,g i) from funext fun t=>funext fun p=>by rw [he]; simp only [Finset.sum_apply],Switch.summed z univ g (fun i=>‖m i‖) (fun i _=> paidClick _ (norm_nonneg _) (fun _=>le_rfl))]
   unfold StepData.push given; simp_rw [Finset.smul_sum]; rw [integral_finsetSum]
   · refine sum_congr rfl fun i _=>?_ ; rw [show g i=click _ _ from rfl,gather]; let Z:=∏j∈i.val,z j
     have hx (U'): S.density R.beta U' U • ((↑(f i U'):ℂ) • Z) = (S.density R.beta U' U * f i U') • Z := (mul_smul _ _ Z).symm
     change ∫ x,S.density R.beta x U • ((↑(f i x):ℂ) • Z) ∂prior G _ = _ -- f shadow
     simp_rw [hx, integral_smul_const]; rfl
   intro i _; exact StepData.push_slice ht U _ ((hp i).smul_const _)

include h hZ
variable [Fintype V] (ho : ∀ i, (z i).part B.quiet=0)
local notation "f0"=> Photo.tones M Y χ rA
include ho
lemma acts (U: Config G c) : (Real.exp (A.exponent U):ℂ) • (Poly.pass (∑' i,sound z (f0 i U))*∑' p,fronts A.activities (fun i=> sound z (fun t p=>K t p i U)) U A.p p) = S.push R.beta (given (S:=S) M rA B z) U :=by
   obtain ⟨f,hp,hF,hc⟩:=h.exponent
   let u (p : Y.fragrances)(t:ℝ)(V:Finset _):=f0 p U t V
   let L: Ways ι:=fun t p=> ∑' i,u i t p
   have hp' p: Paid (fun _:Unit=> u p) (f p):=Paid.toPoint _ (hp p) _
   have hh : HasSum (fun i=>sound z (f0 i U)) (sound z L):= soundSum z u hp' hF (fun _ _ _=>rfl)
   have hL : Paid (fun _: Unit=>L) (∑' i,f i):= (Switch.issue hp' hF).1
   have h0 : (sound z L).part B.quiet=0:=by rw [Switch.sunset (fun _:Unit=>L) hL z () ho]; unfold L; simp [u,Photo.tones]
   let E: Ways ι:=fun t p => Real.exp (L t p); let V:Ways ι:=fun _ _=>Real.exp (A.exponent U)
   let t i (u:ℝ)(p:Finset ι):= tomes A.activities K (P:=A.p) i U u p
   let Z : Ways ι:=fun s p=> ∑' i,t i s p
   obtain ⟨b,hb,hB⟩:= tomes_budget _ _ h.gas;
   have hZ': Paid (fun _:Unit=>Z) (∑' i,b i) := (Switch.issue (fun i=>show Paid (fun _:Unit=> t i) _ from (hB i).toPoint _ U) hb).1
   let a:=Real.exp (A.exponent U)
   have hv : Paid (fun _:Unit=>V) ‖a‖:=Switch.constant _ (norm_nonneg a) (fun _=>le_rfl)
   rw [which M Y, hh.tsum_eq, (Photo.holds z hZ A.activities K h.gas U).tsum_eq, ← GridRenewal.Rain.passes (sound z L) h0]
   change (↑a:ℂ) • (cyclone (sound z L)*sound z Z)=sound z _
   rw [← show sound z (V*(E*Z))= sound z (fun t p=> S.push R.beta (buy M (ways rA t p) S) U) from congr_arg (mapScores B z) (Switch.cong (Switch.approached.mono fun i hi=> funext fun j=> (by rw [← h.closed _ i j ⟨hi.1.le,hi.2⟩]; change a*(_* _) = a *_* Z i j; ring))) ]
   have hE : Paid (fun _:Unit=>E) _:=hL.exponential
   rw [mul_sounds z hZ (show Models V _ from (hv.works ()).choose_spec) (show Models (E*Z) _ from ((hE.mul hZ').works ()).choose_spec),mul_sounds z hZ (show Models E _ from (hE.works ()).choose_spec) (show Models Z _ from (hZ'.works ()).choose_spec), show sound z E= _ from soundExp z hZ hL,const_sounds,Poly.product_bead]
end YM.Merge.Photo
