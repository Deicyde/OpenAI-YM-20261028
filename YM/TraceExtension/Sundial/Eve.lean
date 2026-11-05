import YM.TraceExtension.Sundial.Herb
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
variable {P P':ℝ→change S 4}(hP:PlotX F H 𝓛 h P)(hQ:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)
variable {χ:E4→ℝ}{x y:ℝ→ℝ}(p:Posed H h P P' x y)(q: ShellNorm P' χ)
include hP hQ hp p q
lemma august : Tendsto (fun t=>moveV (S:=S) 4 (P t) (P' t)) Pilot.trail (𝓝 1):=by
    obtain ⟨hx,hy⟩:= anneal F H h hp hP hQ q.valid p q
    apply (esprit H h hx hy).congr'; filter_upwards [p.eq F H h] with i hi
    obtain ⟨ha,hb,hc⟩:=hi; rw[hc]; ext1 z;exact ((P i).symm_apply_apply _).symm
lemma meadow : (∀ m:ℕ,∀ᶠ r in trail, chores r (P' r) m)∧ Month (𝓛:=𝓛) F H P':=by
    have he:= august F H h hp hP hQ p q; let K:= F.room.kernel; have hp'(m:ℕ):∀ᶠ r in trail, chores r (P' r) m:=by
       apply eventually_all.mpr; intro n; apply eventually_all.mpr; intro v; apply eventually_all.mpr; intro j; exact reconst H K hQ he (fun i=> (PoleC C 4) (v i)) j (Scaling.window (sizeHint m) n) (window_closed _ _) (fun x hx=> spaced_conf (cost_pos _) hx.1) (costHint m) (cost_pos _)
    have hV:=(avatar F H h hp hP hQ q.valid p q).spun; let u:=stepField C
    have hw:∀ᶠ i in trail, centering S 4 (P' i u)=P' i u:= hV.mono fun i hi=> zero_center (⟨P' i u,(show expectation S 4 _=0 by rw [hi.cent]; exact sceneV H)⟩:Active S)
    refine ⟨hp',hV.mono (fun i hi=>hi.align),?_,?_⟩
    · filter_upwards [hw,hP,p.polls,p.positiveX] with i hi hE hx hv; rw [hi,hx.lands F H h hp (P i) (P' i)]; exact illuminated F hE.2 _ hv.1
    have ht: centering (F₀) 4 u=u:=zero_center (⟨u, sceneV H⟩: Active (F₀))
    apply Metric.tendsto_nhds.mpr; intro ε hε; filter_upwards[hw,Pilot.jets F.room.kernel H _ hp' (fun _:Fin 2=>u) 0 {sail} isCompact_singleton (singleton_subset_iff.mpr sail_at) ε hε] with s hs hV; specialize hV _ (mem_singleton _); rw [dist_eq_norm]; unfold WickS oval; rw[hs,ht]; rw [show ∀ F G:Points 2→ℂ, iteratedFDeriv ℝ 0 F sail-iteratedFDeriv ℝ 0 G sail=iteratedFDeriv ℝ 0 (F-G) sail from fun F G =>ContinuousMultilinearMap.ext (fun p=>by simp),norm_iteratedFDeriv_zero] at hV; exact hV
end YM.Trace.Sundial
