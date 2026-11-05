import YM.TraceExtension.Swift.Rope
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Analysis Matrix
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side}
def clamor(o:Bond n)(Y:Gal G n)(x:G.Color)(U:Config G n):= (Y U) ⬝ᵥ phB o x
def science(o:Bond n)(x:G.Color)(F:Peat G n)(U:Config G n)(s:ℝ):= F (rung U o x s)-F U
def orbC (Y:Gal G n)(F:Peat G n)(U:Config G n)(o:Bond n)(x:G.Color)(s:ℝ):= clamor o Y x (rung U o x s)*Real.exp (science o x F U s)
abbrev beaconR (e:Lines G n 1): Bond n:= edgeOf (e.1,e.2.1)
abbrev tuna (e:Lines G n 1)(u:G.El):= G.adjoint u (chrom e.2.2)
lemma pitchB (i :Lines G n 1)(u:G.El) : armor (fun _=>u) (bolt i) = phB (beaconR i) (tuna i u):=by
    let p:=beaconR i; let c:=chrom i.2.2; have hv:bolt i=phB p c:=by
        rw [bStep]; unfold p beaconR edgeOf; dsimp only; rw [show Exterior.coord _=i.2.1 from axisEquiv.apply_symm_apply _]
    rw[hv, loy]
lemma clam_turn (Y:Gal G n)(F:Peat G n)(P:Support n)(h:Clouded Y P)(he:GaugeInvariant F)(W:Coats G n)(U:Config G n)(o:Bond n)(x:G.Color)(s:ℝ): orbC Y F (Lattice.gauge W U) o (G.adjoint (W o.1) x) s= orbC Y F U o x s:=by
    let w:= W o.1; let g:=rung U o x s; have hz:rung (Lattice.gauge W U) o (G.adjoint w x) s=Lattice.gauge W g:=by unfold g; rw [seatB,seatB, ← map_smul
      ,adjoint_exp,modify_g];
    unfold orbC clamor science; rw [hz,h.paints,he,he,← loy,loyS]
lemma claret (Y:Gal G n)(F:Peat G n)(U:Config G n) (h: Drift _ Y)(he:Drift _ F)(o:Bond n)(x:G.Color):
    let y:= phB o x; let K(z:Link G n):=Y (input _ _ z*U); HasDerivAt (orbC Y F U o x) ( (fderiv ℝ K 0 y) ⬝ᵥ y+ (Y U ⬝ᵥ y)*(fderiv ℝ (bal U F) 0 y)) 0:=by
    intro y K; let T (z:Link G n):= input _ _ z*U; have hT:Army T 0:= (Army.powL (v:=id) contDiffAt_id).mul (Army.park U _); have hx:= Push.side (bal U F) (he _ T _ hT|>.differentiableAt (by simp)) y; have hy: HasDerivAt (fun t:ℝ=> K (t • y)) _ 0:= Push.side K (h _ _ _ hT|>.differentiableAt (by simp)) y
    let L:= dotB.flip y; have he(Z:Link G n):Z ⬝ᵥ y = L Z:= (fast_dot ..).symm
    have ha := (L.hasFDerivAt (x:=K ((0:ℝ) • y))|>.comp_hasDerivAt _ hy)
    let f(s:ℝ):=K (s • y) ⬝ᵥ y; let g(s:ℝ):= Real.exp (bal U F (s • y)- F U)
    have hp:g 0=1:=by unfold g; simp[bal];
    have hb:f 0= Y U ⬝ᵥ y:=by unfold f K;simp
    have hq: HasDerivAt g (fderiv ℝ (bal U F) 0 y) 0:=by
        apply ((hx.sub_const (F U)).exp).congr_deriv; exact (show g 0*_=_ from by rw[hp,one_mul])
    have hm:HasDerivAt f ((fderiv ℝ K 0 y) ⬝ᵥ y) 0:=by unfold f; simp_rw [he]; exact ha
    apply (hm.mul hq).congr_deriv; rw[hp,hb,mul_one]
lemma astro (Y:Gal G n)(F:Peat G n)(U:Config G n) (h:Drift _ Y)(he:Drift _ F)(V:G.El) :
    ∑ i:Lines G n 1,deriv (orbC Y F U (beaconR i) (tuna i V)) 0= lush Y U + rill F Y U:=by
    let Z(i:Lines G n 1):= armor (fun _=>V) (bolt i); let P:= maroon G n U; let L:= fderiv ℝ (Y ∘ P) 0; let H:= beamG F U
    have ht(i): deriv (orbC Y F U (beaconR i) (tuna i V)) 0=dotProduct (L (Z i)) (Z i)+(Y U ⬝ᵥ Z i)*H (Z i):=by rw[(claret Y F U h he (beaconR i) (tuna i V)).deriv, ← pitchB];rfl
    simp_rw [ht,sum_add_distrib]; apply congr_arg₂ (·+·)
    · have hh: ContDiffAt ℝ ω (Y ∘ P) 0:=h _ P _ ((Army.powL (v:=id) contDiffAt_id).mul (Army.park U _)); rw [tether _ _ hh]; rw [show ∑ i,_= _ from lumin V (fun _:Site n=>V) rfl L]; refine sum_congr rfl fun i _=>?_ ; unfold outD
      let Q:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Lines G n 1=>ℝ) i; change _ = fderiv ℝ (Q∘ (Y ∘ P)) 0 (bolt i); rw[fderiv_comp _ Q.differentiableAt (hh.differentiableAt (by simp)),Q.fderiv]; rfl
    change _ = H _; apply Eq.trans (b:=H (∑ i:Lines G n 1,(Y U ⬝ᵥ Z i) • Z i)) ?_ (congr_arg H (colours (Y U) V _ rfl)); rw[map_sum]; refine sum_congr rfl (fun i _ => ?_); rw[map_smul]; rfl
lemma toeW (Y:Gal G n){P:Support n}(h:Clouded Y P)(U:Config G n)(o:Bond n)(x:G.Color)(he:o.1∉P): clamor o Y x U=0:=by rw [clamor,zeal,show edgeColor (Y U) o=0 from ?_,inner_zero_left]; ext i; exact h.toes (o.1,coord o.2,i) U he
lemma astrolabe (Y:Gal G n) (F:Peat G n) (U:Config G n)(P:Support n)(h:Clouded Y P) (he:Drift _ F)(V:G.El) :
    ∑ i ∈ (P ×ˢ (univ:Finset (Loc G 1))), deriv (orbC Y F U (beaconR i) (tuna i V)) 0= lush Y U + rill F Y U:=by
    rw [← astro Y F U h.wakes he V]; refine sum_subset (subset_univ _) (fun i _ hi=> ?_); have hp:i.1 ∉ P:= fun h=> hi (mem_product.mpr ⟨h,mem_univ _⟩); rw [show orbC Y F U (beaconR i) (tuna i V)=fun _=> 0 from funext (fun x=>by unfold orbC; rw [toeW _ h _ _ _ (show _ from hp),zero_mul])]; simp
end YM.Trace.Swift
