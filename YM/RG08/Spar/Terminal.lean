import YM.RG08.Spar.Air

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows
open scoped Topology BigOperators Classical ENNReal Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type}[Fintype I]{n:ℕ}{σ τ θ C B W Q:ℝ}{L:Side}{l u:ℕ→Side}

/-- `he` IS the same-shift stationarity on curvature, with shift on evaluation map whatever
the joint Gaussian setup actually computes on finite period (includes color). No ambient
lattice derivative estimates. Supplies may be given on only the diagonal of the schedule;
Q,hv are any costs/width on the once-produced analytic curvature precursor at output.
The conclusion itself is independent of all these choices and compares literal tensors.
-/
theorem finish {μ:Kernel (Kind I 1) (Kind I 1)}{K:Kernel (Kind I 2) (Kind I 2)}{F:Raw I n}(S:∀ m,StepData (l m) (u m))
    {A:∀ m,Matrix (Co (u m) (Kind I 1)) (Co (l m) (Kind I 1)) ℝ}{D:∀ m,Matrix (Co (u m) (Kind I 2)) (Co (l m) (Kind I 2)) ℝ}
    (ht:climb l)(i:Fin n)(hL:∀ m,(S m).patch.L=L)
    (h: Held (carpet (Tone I)) σ C F)(hc:Cohort F)(hC:0≤C)(hs:0<σ)
    (hv:0<θ)(hz:θ ≤ L.val * (σ/2))
    (hμ:Priced θ W (clover L μ))(hκ:Priced θ B (clover L K))
    (hA:∀ m, Matches μ (A m))(hD:∀ m,Matches K (D m))
    (he:∀ m,shaded (u m) (u m) I ((cobound 1).acts _) * A m=D m*shaded (l m) (l m) I ((cobound 1).acts _))
    (hp:city L K)(ho: Held (carpet _) τ Q (braces K (compress 2 F)))(hτ:0<τ)(hq:0≤Q):
    braces μ (compress 1 (picture I n F)) = compress 1 (picture I n (Anchor.extend 2 (braces K (compress 2 F)))):=by
 let X:=braces K (compress 2 F); let Y:= Anchor.extend 2 X
 let T:=compress 1 (picture I n F)
 have hF:= NextTo.unit hs hC hc h (Fin.pos i)
 have hT:=photograph hF
 have hx:Cohort X:=braces_path hp (compress_path 2 hc)
 have hY:NextTo Y τ Q:=NextTo.unit hτ hq (expand_path hx) (expand_cost ho) (Fin.pos i)
 have hs':θ ≤ L.val * σ:=hz.trans (by gcongr;nlinarith)
 have HA: Appears l (braces μ T) (fun m=>query (A m) (pour T i)):=tilt_stencil S ht i hL (compress_path 1 hT.cohort) (mul_nonneg (flame_pos hs (Fin.pos i)) hC) (compress_cost _ (encode (Fin.pos i) hs hC hc h)) hv hz hμ hA
 have HD: Appears l X (fun m=>query (D m) (pour (compress 2 F) i)):=tilt_stencil S ht i hL (compress_path 2 hc) hC (compress_cost _ h) hv hs' hκ hD
 have heq(m:ℕ): query (A m) (pour T i)=query (shaded (l m) (l m) I ((cobound 1).acts _)) (query (D m) (pour (compress 2 F) i)):=by
    unfold T; rw [descend i hF,transitive,he m,transitive]
 obtain ⟨V,t,hv'⟩:=coboundHoles l I
 have hh:=appears_holes hv' HD
 have hh' : Appears l X (fun m=>pour X i):=cofinal hx _ _ hτ hq ho i ht
 have Hk:=appears_holes hv' hh'
 let Z:=compress 1 (picture I n Y)
 have hy:=photograph hY
 have hz:Appears l Z (fun m=>pour Z i):=cofinal (compress_path _ hy.cohort) _ _ (half_pos hτ) (mul_nonneg (flame_pos hτ (Fin.pos i)) hq) (compress_cost _ (encode (Fin.pos i) hτ hq (expand_path hx) (expand_cost ho))) i ht
 ext x
 calc
 _ = rafters V t X x:=by
    unfold Appears at *; simp_rw [heq] at HA;exact tendsto_nhds_unique (HA x) (hh x)
 _ = Z x:=by
    unfold Z at hz; unfold Appears at *; simp_rw [descend i hY,show compress 2 Y=X from funext fun w=> extend_top X w] at hz;exact tendsto_nhds_unique (Hk x) (hz x)

end YM.RG08.Spar
