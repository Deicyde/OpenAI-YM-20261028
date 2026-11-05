import YM.RG08.Orison.Race
/-! # .Cloak on analytic limiting charts - pointwise closed transfers. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{p n:ℕ}
lemma guard {F:ℕ→Rudder.Raw G.ColorIndex n}{V:Rudder.Raw G.ColorIndex n}(h:∀ t,Tendsto (fun i=> F i t) atTop (𝓝 (V t)))(he:∀ᶠ i in atTop,Cloak (Symmetry.dressed G n) p (F i)):Cloak (Symmetry.dressed G n) p V:=by
 refine ⟨fun x q=>tendsto_nhds_unique (h (Forms.sway x q)) ((h q).congr' (he.mono fun i hi=>(hi.path x q).symm)),?_,fun f=>funext fun x=>tendsto_nhds_unique (h _) ((h _).congr' (he.mono fun i hi=>(congrFun (hi.beam f) x).symm)),?_,?_⟩
 · apply graded_iff.mpr;intro i x hx;exact tendsto_nhds_unique (h x) (tendsto_const_nhds.congr' (he.mono fun j hj=> (graded_iff.mp hj.field' i x hx).symm))
 · intro s;funext x;rw [orbit_apply]
   apply tendsto_nhds_unique (tendsto_const_nhds.mul (h _)) ((h _).congr' _)
   exact he.mono (fun i hi=>(show Symmetry.levy s x*F i (markTape s x)=F i x from congrFun (hi.firm s) x).symm)
 intro x
 -- Submodule closed finite dimensional
 exact (Submodule.closed_of_finiteDimensional _).mem_of_tendsto (f:=fun i=>hat (F i) x) (tendsto_pi_nhds.mpr (fun _=>h _)) (he.mono fun _ hi=>hi.hair x)
end YM.RG08.Orison
