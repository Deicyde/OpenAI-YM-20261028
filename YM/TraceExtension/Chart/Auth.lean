import YM.TraceExtension.Chart.Stage
import YM.UVNext.FREE_STRESS_CERTIFICATE.Pressure
import YM.Work.A05
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Over
open Function Filter Labels Maxwell Next.UVStress StressFlux UVNext.FreeStress Org Climb Extraction Ward
open Table Shelves
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{C:Family G}
local notation "F₁"=> (Climb.Bel C.book)
lemma ff_pair(s t u v:Axis): ff G 4 le_rfl s t u v=StressFlux.pair G s t u v:=by
    apply StressFlux.label_ext; intro J
    rw [pair_value]; change Labels.read J (tape ..) = _; rw [eval_tape];
    have hx(i j:Axis): component (initialPlace i j) (J 0)=curl0 i j (J 0):=by
        apply congr_arg (Maxwell.takeCurl (J 0) i j); exact Subsingleton.elim ..
    rw[hx,hx]
lemma pair_bill(s t u v:Axis): flat C.book.grid s t u v = fromPol (Climb.Bel C.book) (pair G s t u v):=by
    change embed C.book.grid 4 (ff ..)=_; rw[ff_pair];rfl
lemma target_sign(i j:Axis) : canonicalStress C.book.grid i j=material (Climb.Bel C.book) weyl i j:=by
    unfold canonicalStress UVNext.FreeStress.panel StressFlux.material; simp_rw[pair_bill (C:=C)]; rw[stress_of]; split; next h=>
      subst j; rw [show weyl 2= -(1/4:ℝ) from (by change (-1)/4=-(1/4:ℝ); ring)]; change _ - (1/4:ℂ) • _ = fromPol (Bel C.book) (((0:ℝ) • Labels.unit G 4)+(1:ℝ) • (∑ k:Axis,pair G i k i k)+(-(1/4:ℝ)) • (∑ u:Axis,∑ k:Axis,pair G u k u k)); rw [zero_smul,one_smul,zero_add,map_add,map_sum,map_smul]; unfold total; simp_rw [map_sum, show ∀ a b c d, flat C.labels a b c d=_ from fun a b c d=>pair_bill (C:=C) a b c d]; rw[RCLike.real_smul_eq_coe_smul (K:=ℂ), sub_eq_add_neg]; push_cast; rw[neg_smul]
    next h=> rw[sub_zero,map_smul,map_sum]; exact (one_smul ℝ _).symm
lemma canonical_meter : materialB C none = torch C.book.grid (-1):=by
    unfold materialB; rw [show Fin.cons _ _= -weyl from FZone_c G, material_neg]; rw [torch,neg_one_smul, funext (fun i=>funext fun j=> target_sign (C:=C) i j)]
-- lighthouse witness exact.Reader signal.Tr.
structure Marvel {L:Register G}(S:Table L)(H:S.RealSpin) (J:S.Stress) (X:DiffPlan S):Prop where
   currents : J∈ KernelSpace H ∧ Conserved X H J
   flux : ∃ T,StressLaws S J X.deriv T
lemma Litpay (h:G.Simple): ∃ T: MaxwellData C,T.T.J=materialB C none∧T.T.κ=1∧ Marvel (Climb.Bel C.book) T.hT.spin T.T.J T.T.W:=by
   obtain ⟨P,hP,hK⟩:= Maxwell.Free.maxwell_supplies C h 1 one_ne_zero
   obtain ⟨Q,hQ,hE,hW,hV,ht,hR,hL⟩:=UVNext.FreeStress.names (-1) h P (by norm_num)
   norm_num at hE; have he := Q.lit.delta; rw [hE,one_smul] at he
   exact ⟨Q,hQ.trans canonical_meter.symm,hE,⟨hL.enters,hL.origin⟩,_,he⟩
end YM.Trace.Over
