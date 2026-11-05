import YM.TraceExtension.Pi.Book
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft
open Source Source.Drops Labels Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {d n k:ℕ}{G:Gauge}{s:Side}{F: Peat G s}
set_option synthInstance.maxHeartbeats 45000
section pivot
-- Snap energy on active lattice coordinates. not requiring gauge covariance of road lift beyond chart.
def stepC (o:Site s)(u:Potential G):Link G s:= edgeColor.symm (fun i=> u (seat (lift (i.1-o))) i.2)
def pulseC (o:Site s)(H:Hol G)(d:ℕ)(v:Snap G d): Config G s:= H.testLinks d o (expand d v) 1
def folk (o:Site s)(H:Hol G)(d:ℕ)(v:Snap G d): Link G s:= content (pulseC o H d v)
lemma flash_c (o:Site s)(H:Hol G)(i:Edge (Site s))(v:Snap G d): pulseC o H d v i= Place.flight (road (Place.seat (lift (i.1-o))) i.2 v) 1:=by
   exact (congr_fun (flight_test H (lift (i.1-o),i.2) v) 1).symm
lemma pulseC_zero (H: Hol G)(o:Site s)(d:ℕ): pulseC o H d 0 =1:=by ext1 i; rw [flash_c,show Place.road (seat (lift (i.1-o))) i.2 (G:=G) (d:=d) 0=(0:Place.Route G d) from (Place.road ..).map_zero,no_flight]; rfl
lemma pulseC_safe (H:Hol G)(o:Site s)(d:ℕ): Army (pulseC o H d) 0:=by
   let V:=pulseC o H d
   intro i; let Z:= road (G:=G) (d:=d) (Place.seat (lift (i.1-o))) i.2
   simp_rw[flash_c]; exact ContDiffAt.comp (g:=fun X:Place.Route G d=> G.mat (Place.flight X 1)) (f:=Z) (0:Snap G d) (by rw[show Z 0=(0:Place.Route G d) from Z.map_zero]; exact (arrival G d).1.contDiffAt) Z.contDiff.contDiffAt
lemma folk_safe (H:Hol G)(o:Site s)(d:ℕ): ContDiffAt ℝ ω (folk o H d) 0:= Army.logL (pulseC_safe H o d) (pulseC_zero H o d)
set_option maxHeartbeats 450000 in
lemma folk_pay (H:Hol G)(o:Site s)(v:Snap G d): fderiv ℝ (folk o H d) 0 v= stepC o (sampled v):=by
   let M:= edgeColor (n:=s) (G:=G)
   have hp: HasDerivAt (fun t:ℝ=> folk o H d (t • v)) (fderiv ℝ (folk o H d) 0 v) 0:=by
       have hz: HasFDerivAt (folk o H d) (fderiv ℝ (folk o H d) 0) ((0:ℝ) • v):=by rw[zero_smul]; exact ((folk_safe H o d).differentiableAt (by simp)).hasFDerivAt
       exact HasFDerivAt.comp_hasDerivAt (0:ℝ) hz (ray_id v)
   apply M.injective; ext1 i; rw [show M (stepC o _) i=_ from congr_fun (M.apply_symm_apply _) i]
   change M (fderiv _ _ _ _) i=Place.steady _
   let p:=road (G:=G) (Place.seat (lift (i.1-o))) i.2 v; let z:= Place.steady p
   let L:= ContinuousLinearMap.proj (R:=ℝ) i ∘L M.toContinuousLinearMap
   apply HasDerivAt.unique (show HasDerivAt (fun t:ℝ=>L (folk o H d (t • v))) _ _ from L.hasFDerivAt.comp_hasDerivAt (0:ℝ) hp)
   have hx:= (arrival G d).2.2 p
   have hz:HasDerivAt (fun t:ℝ=> G.plog (G.mat (Place.flight (t • p) 1))) (Place.steady p) 0 := by
       have he: HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (Place.flight ((0:ℝ) • p) 1)):=by rw[zero_smul,no_flight,G.mat_one]; exact (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
       have hc:HasDerivAt (fun t:ℝ=> G.plog (G.mat (Place.flight (t • p) 1))) (fderiv ℝ G.plog 1 (G.colorMat (Place.steady p))) 0:= he.comp_hasDerivAt (l:=G.plog) (0:ℝ) hx
       rwa [Place.plog_velocity] at hc
   apply hz.congr_of_eventuallyEq (Eventually.of_forall (fun t=>?_)); change edgeColor (folk _ _ _ _) i=G.plog (G.mat (Place.flight (t • p) 1)); unfold folk; rw [show edgeColor (content _) i=_ from content_at _ i.1 i.2]; rw [flash_c,map_smul]
set_option maxHeartbeats 500000 in
lemma artist (H:Hol G)(o:Site s)(hd:2 ≤ d)(h: Cleric F)(hp:G.Simple): let g:=pulseC o H d; let U: Snap G d→ℂ:= Complex.ofRealCLM ∘ F ∘ g
    ContDiffAt ℝ ω U 0 ∧ fderiv ℝ U 0=0 ∧ ∀ i j (X:Taylor G (i:Fin (d-1)).val)(Y:Taylor G (j:Fin (d-1)).val),
    iteratedFDeriv ℝ 2 U 0 ![(Pi.single i X : Snap G d),Pi.single j Y]=(↑(iteratedFDeriv ℝ 2 (F ∘ input G s) 0 ![stepC o (variation X),stepC o (variation Y)]):ℂ):=by
    intro g U; let R:= folk o H d; let W:= F∘ input G s
    have hx: (F∘g)=ᶠ[𝓝 0] W∘R:=by filter_upwards [(show Tendsto g (𝓝 0) (𝓝 1) from pulseC_zero H o d ▸ (pulseC_safe H o d).cont.tendsto).eventually content_encodes] with x hx; exact congr_arg F hx.symm
    have hR: R 0=0:=by simp[R,folk,pulseC_zero,content_one]
    have hw: ContDiffAt ℝ ω W (R 0):=hR.symm ▸ h.dye
    have ht:=folk_safe H o d; have hF : ContDiffAt ℝ ω (F ∘ g) 0:= ((hw.comp _ ht).congr_of_eventuallyEq hx)
    have h₀:fderiv ℝ W 0=0:= dyed_hold h hp
    have hm:fderiv ℝ (F ∘ g) 0=0:=by rw[hx.fderiv_eq, fderiv_comp (0:Snap G d) (hw.differentiableAt (by simp)) (ht.differentiableAt (by simp)),hR,h₀]; simp
    refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=F ∘ g) 0 hF,?_ ,fun i j x y=>?_⟩; · unfold U; rw [fderiv_comp (f:=F ∘ g) (0:Snap G d) Complex.ofRealCLM.differentiableAt (hF.differentiableAt (by simp)), hm]; simp
    let a:Snap G d:= Pi.single i x; let b:Snap G d:= Pi.single j y
    have hp:iteratedFDeriv ℝ 2 (W ∘ R) 0 ![a,b]= iteratedFDeriv ℝ 2 W 0 ![stepC o (variation x),stepC o (variation y)]:=by
       have he:= pay_second (H:=R) hw ht a b
       rw [he]; rw[hR,h₀]; simp [R,folk_pay, a,b, sampled_slot]
    rw[show U=Complex.ofRealCLM ∘ (F ∘ g) from rfl,Complex.ofRealCLM.iteratedFDeriv_comp_left hF le_top]
    change (↑(iteratedFDeriv ℝ 2 (F ∘ g) 0 ![a,b]):ℂ)= _; exact congr_arg ((↑):ℝ→ℂ) ((show iteratedFDeriv ℝ 2 (F ∘ g) 0 ![a,b]=iteratedFDeriv ℝ 2 (W ∘ R) 0 ![a,b] from congr($( (hx.iteratedFDeriv ℝ 2).eq_of_nhds) ![a,b])).trans hp)
end pivot
end YM.Trace.Kits
