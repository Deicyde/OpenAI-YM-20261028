import YM.TraceExtension.Sundial.Eve
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith Asymptotics
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
variable {P P':ℝ→change S 4}(hP:PlotX F H 𝓛 h P)(hQ:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)
variable {χ:E4→ℝ}{x y:ℝ→ℝ}(p:Posed H h P P' x y)(q: ShellNorm P' χ)
include H
include h in
lemma signed_remainder(g d:ℝ→ℝ)(f:ℝ)(hg: Coupling G g)(he: (fun i=> d i-f*g i^2) =O[trail] fun i=>g i^4): Tendsto (fun i=> (d i-f*g i^2) / g i^(3:ℕ)) trail (𝓝 0):=by
    obtain ⟨c,hc⟩:= isBigO_iff.mp he; have hv:= (hg.conforms h).const_mul c
    rw [mul_zero] at hv; apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (g:=fun i=>c*g i) (Eventually.of_forall (fun i=> norm_nonneg ((d i-f*g i^2) / g i^(3:ℕ)))) _ hv
    filter_upwards[hg.positive,hc] with i hi hu; rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero _ hi.ne'))]; apply hu.trans_eq; rw [pow_succ,norm_mul, Real.norm_of_nonneg hi.le];ring
lemma remember {d a e: ℝ→ℝ}(hv:∀ᶠ t in trail, Measures F t (P t) (a t) (d t) (e t))(hp:∀ᶠ t in trail,AlignV F.room.kernel F.sector H (P t)) :
    let E:=F.sector.energy
    let v := expectation S 4 (TraceExtension.stressTrace E)
    (∀ᶠ s in trail,e s=s^4*v.re/4):=by
   intro E w
   let H':=F.room.kernel; filter_upwards [hv,hp] with i hi hp; have hx:= hi.codes F; have hu:=congr_arg (fun R:Stress S=>TraceExtension.stressTrace R) hx; dsimp only at hu; unfold TraceExtension.stressTrace at hu; simp only [Pi.add_apply,Pi.smul_apply,Pith.post, Finset.sum_add_distrib,Pith.erase,if_true, ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin] at hu
   rw [← map_sum (P i),trace_none,map_zero, smul_zero, zero_add] at hu
   let P':=(expectation S 4).restrictScalars ℝ; have hp':= congr_arg P' hu; rw [map_smul,map_add,P'.map_smul (d i),map_nsmul,P'.map_smul (e i),map_nsmul] at hp'
   change i^(4:ℕ) • w=d i • (4:ℕ) • expectation S 4 (P i (stepField C))+ e i • (4:ℕ) • expectation S 4 (P i _) at hp'
   rw [hp.cent,hp.cent, mean_unit H.laws, sceneV H,smul_zero,smul_zero,zero_add] at hp'; have ht:= congr_arg Complex.re hp'; simp [Complex.real_smul] at ht; norm_cast at ht; linarith
end YM.Trace.Sundial
