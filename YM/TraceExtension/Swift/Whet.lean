import YM.TraceExtension.Swift.Helot
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side} (m:ℕ){P:Support n}{F:Peat G n}{Y:Gal G n} {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
-- global CP only finite cuts
lemma thunder (h: Drift _ F)(hp:Drift _ Y)(U:X→ Config G n)(V:X→ G.Color)(s:X→ℝ) (x:X) (hx:Army U x)(ht:ContDiffAt ℝ ω V x)(hs:ContDiffAt ℝ ω s x) (o:Bond n): ContDiffAt ℝ ω (fun x=> orbC Y F (U x) o (V x) (s x)) x:=by
   let L z:= phB o (V z); let K z:= rung (U z) o (V z) (s z); have ha:ContDiffAt ℝ ω L x:=(phB o).contDiff.contDiffAt.comp _ ht; have he: Army K x:= (Army.powL (hs.smul ha)).mul hx
   have hP: ContDiffAt ℝ ω (fun x=> (Y (K x)) ⬝ᵥ L x) x:=by simp_rw [← fast_dot]; exact (dotB.contDiff.contDiffAt.comp _ (hp X K x he)).clm_apply ha
   exact hP.mul (((h X K x he).sub (h X U x hx)).exp)
lemma leot (h:Drift _ F)(hp:Drift _ Y)(U:X→ Config G n)(V:X→G.Color)(o:Bond n)(x:X)(t:ℝ)(hx:Army U x)(hv:ContDiffAt ℝ ω V x): ContDiffAt ℝ ω (fun x=>rumba m Y F t o (V x) (U x)) x:=by
   unfold rumba duel; refine ContDiffAt.sub (ContDiffAt.sum (fun i _=> ContDiffAt.const_smul (c:=wage m i) ((thunder h hp U V (fun _=> Outer.Nodes.loc i *t) x hx hv contDiffAt_const o).sub (thunder h hp U V (fun _=>0) x hx hv contDiffAt_const o)))) (ContDiffAt.const_smul (c:=t) ?_)
   let p(y:X)(t:ℝ):= orbC Y F (U y) o (V y) t; have he: ContDiffAt ℝ ω (uncurry p) (x,0):= thunder h hp (U ∘ Prod.fst) (V ∘ Prod.fst) Prod.snd _ (fun i=> ((hx i).comp (g:=fun y=>G.mat (U y i)) (f:=Prod.fst) (x,(0:ℝ)) contDiffAt_fst)) (hv.comp (x,(0:ℝ)) contDiffAt_fst) contDiffAt_snd o
   obtain ⟨T,hT,H⟩:= exists_allows (s:={(x,(0:ℝ))}) isCompact_singleton (f:=uncurry p) (fun i hi=>hi.symm ▸ he) 1
   exact (priced_partial (f:=uncurry p) (x:=x) (n:=0) (H _ (Set.mem_singleton _)) 1 norm_one.le).analytic
lemma tuneH (e: Lines G n 1): Continuous (tuna e) :=by
    let c:= chrom e.2.2; let f:=fun v:G.El=> G.adjoint v c
    have h(v:G.El):f v= Planned.PrimaryIntegral295.Drupes.jetAd G (G.mat v) c:= congr_arg (fun M:G.Color→L[ℝ]G.Color=> M c) (Planned.PrimaryIntegral295.Drupes.turned v)
    obtain ⟨C,hC,H⟩:=Planned.PrimaryIntegral295.Drupes.shaders G 0
    change Continuous f; rw[funext h]; apply continuous_iff_continuousAt.mpr; intro x; exact (((H _).analytic.continuousAt.comp G.continuous_mat.continuousAt).clm_apply continuousAt_const)
lemma rumba_r(h:Clouded Y P)(hp:GaugeInvariant F)(U:Config G n)(o:Bond n)(h':ℝ)(x:G.Color)(W:Coats G n): rumba m Y F h' o (G.adjoint (W o.1) x) (Lattice.gauge W U) = rumba m Y F h' o x U:=by
   unfold rumba; rw [funext fun i=> clam_turn Y F P h hp W U o x i]
lemma orb_local (o:Bond n)(x:G.Color)(hf:LocalOn P F)(hy:LocalOn P Y)(U V:Config G n)(h:Agrees P U V)(s:ℝ) : orbC Y F U o x s=orbC Y F V o x s:=by
   let Z:= rung U o x s; let Z':=rung V o x s; have hh:Agrees P Z Z':=fun j hp hv=> congr_arg ((input G n (s • phB o x)) j *·) (h j hp hv)
   unfold orbC science clamor; rw [hf _ _ h,show F Z=F Z' from hf _ _ hh, show Y Z=Y Z' from hy _ _ hh]
def atune(F: Bond n→ G.Color→ Config G n→ℝ)(P: Support n)(U:Config G n):ℝ:=∑ e∈ (P ×ˢ (univ:Finset (Loc G 1))),∫ u,F (beaconR e) (tuna e u) U ∂G.probHaar
abbrev atuneU(m:ℕ)(Y:Gal G n)(F:Peat G n)(h:ℝ)(P:Support n):=atune (rumba m Y F h) P
end YM.Trace.Swift
