import YM.UVExtension.Fallow.Fife
import YM.UVExtension.Harvest.Oats
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) (hF:Fridge C u ζ) {d N p:ℕ}
open Extra.Histories Motion
open Next.Extract Harvest
-- Choose line-wise projector since proof at actual p unaffected by extraction choices (K budget). Spectrometer independent of its gauge.
abbrev Cuts (C:Family G)(d:ℕ) := ℕ→ CoordMap C d

structure Yards (C:Family G)(d p:ℕ)(T:Cuts C d) : Prop where
    spends : Spar T
    changes : ∀ i y,T i (T i y)=T i y
    slots (i:ℕ): Module.finrank ℂ (LinearMap.ker (T i).toLinearMap)= Harvest.charge G d
    signal (x:ℕ→ C.label d): Bleak p x → (∀ᶠ i in atTop,x i∈ LinearMap.ker (T i).toLinearMap) → ∃ G:Stem C p, Cloud C G∧ Faded C (thor x p-G)

namespace Yards
include h hG H B
lemma bedroll (ht:Harvest.Harrow C u ζ)(d p:ℕ): ∃ T:Cuts C d, Yards C d p T:=by
   obtain ⟨V,R,E,hV,hE⟩:= ht.wage d; obtain ⟨W,P,U,hP⟩:=Vintage.YM.MergeProof.solaris H B h ht.lab V hV.valid hG hE
   obtain ⟨M,hM,H0⟩:=Mark.potage (C.labels.level d)
   choose X hX hT hS using fun i=> H0 (catalog C R d i p (P i p)); refine ⟨X,⟨M,Eventually.of_forall hT⟩,fun i x=> (hX i).stable x, fun i=>?_,fun x he hx=>?_⟩
   · rw [(hX i).ker]; exact (LinearEquiv.finrank_eq ((bindP C R d i p _).submoduleMap _)).symm
   let y(i):= (P i p).symm ((C.factory d i p).terminal.symm (x i)); let z i:= (C.factory d i p).terminal (P i p (y i)); have hZ i:z i=x i:= by simp only [z,y,LinearEquiv.apply_symm_apply]
   have hp : Rested C y:=by
      have hc: Rested C (fun i=>2*(C.labels.level d).coeffSize ((C.factory d i p).terminal.symm (x i))):= (Slow.const (C:=C) (2:ℝ)).mul (coords_slow (fun i=> (C.factory d i.1 p).terminal.symm (x i.1)) he)
      apply Slow.reduce hc; filter_upwards [(cutoff_grows _).eventually hP.stamped] with i hi; exact (((Size.norm_le _ _).trans ((hi p).2.1 ((C.factory d i.1 p).terminal.symm (x i.1)))).trans (Real.le_norm_self _))
   have hy:Faded C (thor z p - badge V y p):= drawn H B V hV.valid y P hP hp p
   refine ⟨badge V y p,paper H V y R hV ?_,(funext hZ: z=x) ▸ hy⟩; filter_upwards [hx] with i hi
   have hl : x i∈ catalog C R d i p (P i p):= (hX i).ker ▸ hi
   obtain ⟨v,hv,hr⟩:= hl; change bindP _ _ _ _ _ _ v=x i at hr; unfold y; rw [← hr,bindP,Astar,LinearEquiv.trans_apply,LinearEquiv.trans_apply, LinearEquiv.trans_apply]; simp only [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]; exact Mark.entry_mem C R d i p _ hv
omit h hG H B
variable {T:Cuts C d}(ht:Yards C d p T)(K:Extraction.Wcmain C) {x:ℕ→ C.label d}
include H K ht
lemma nullTest (hx:Bleak p x)(hh:∀ᶠ i in atTop,x i∈ LinearMap.ker (T i).toLinearMap)(I:Shot C.book)(hI:suitable C.S p I.f): Tendsto (fun i=> Dash.Shot.scan (C:=C) I d i p (x i)) atTop (𝓝 0):=by
   obtain ⟨V,hc,hQ⟩:=ht.signal x hx hh; apply (Fallow.faded H K I hI hQ).congr'; filter_upwards [ghost H I hI hc, smear_sub _ (thor x p) _ (thorP H x) hc.same] with i hi he; rw [he,hi,sub_zero,scanning]
end Yards
end YM.UVExtension.Fallow
