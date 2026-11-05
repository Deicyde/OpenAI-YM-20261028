import YM.TraceExtension.Terrace.Prism
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set MeasureTheory Extraction
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
section continuity
-- fit_plane in real.Top
variable {E H:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup H][NormedSpace ℝ H][FiniteDimensional ℝ H]
lemma fitV {S:Type*}{F:Filter S} (A:S→E→L[ℝ] H)(g:E→L[ℝ] H) (h:∀ x:E,Tendsto (fun i=>A i x) F (𝓝 (g x))): Tendsto A F (𝓝 g):=by
    let b := Module.finBasis ℝ E; let I:=Fin (Module.finrank ℝ E); let L : (I → H) →ₗ[ℝ] E→L[ℝ] H := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℝ).toLinearMap
    have he (g : E→L[ℝ] H) : L (fun i => g (b i))=g:=by apply ContinuousLinearMap.coe_injective; exact b.ext fun i=> b.constr_basis ..
    have hh:= L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ i,Tendsto (fun t=> (fun j:I=> A t (b j)) i) F (𝓝 ((fun j:I=>g (b j)) i)) from fun i=>h _))
    refine Tendsto.congr' (f₂:=A) ?_ (he g ▸ hh); exact Eventually.of_forall fun i=> he (A i)
-- triangular repair on near-kernel
variable (f:E→L[ℝ] H)(v:ℕ→ E→L[ℝ] H)(U:H→L[ℝ] E)(u:ℕ→ H→L[ℝ] E)(x:E)(w:ℕ→E)
variable (he:Tendsto u atTop (𝓝 U))(hr: f.comp U=ContinuousLinearMap.id ℝ H)(hR:∀ᶠ i in atTop,(v i).comp (u i)=ContinuousLinearMap.id ℝ H)
variable (hp:Tendsto w atTop (𝓝 x)) (hx:Tendsto (fun i=> v i (w i)) atTop (𝓝 0))(h:x≠0)
-- continuous kernel detector for decomposition. classical polarization instead of projection onto kernel.
lemma plumage (h:x≠0)(hh:∀ y:E,f y=0↔ ∃ a:ℝ,y=a • x) (hr: f.comp U=ContinuousLinearMap.id ℝ H) : ∃ A:E→L[ℝ] ℝ,∀ y, y=U (f y)+ A y • x:=by
    let P:ℝ→L[ℝ] E:= (ContinuousLinearMap.id ℝ ℝ).smulRight x
    have he:Injective P:= (smul_left_injective ℝ h)
    obtain ⟨A,hA⟩:=(P.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr he));
    refine ⟨A.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E-U.comp f),fun y=>?_⟩
    have hz : f (y-U (f y))=0:=by rw [map_sub,show f (U (f y))= f y from DFunLike.congr_fun hr (f y),sub_self]
    obtain ⟨a,ha⟩:= (hh _).1 hz
    have hp: A (y-U (f y))=a:=by rw [ha]; exact LinearMap.congr_fun hA a
    change y=U (f y)+ A (y-U (f y)) • x; rw [hp,← ha]; abel
lemma beak {S:Type*}{F:Filter S}(A:S→ E→L[ℝ] H) (v:S→E)(g:E→L[ℝ] H)(p:E)(he:Tendsto A F (𝓝 g))(hp:Tendsto v F (𝓝 p)): Tendsto (fun i=>A i (v i)) F (𝓝 (g p)):= (show Continuous (fun x:(E→L[ℝ] H) × E=> x.1 x.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (he.prodMk_nhds hp)
include hR hr he hp hx h
lemma scout (hh:∀ y:E,f y=0↔ ∃ a:ℝ,y=a • x) : Tendsto v atTop (𝓝 f):=by
    obtain ⟨A,hA⟩:= plumage f U x h hh hr
    let V(i):= (u i).comp f + A.smulRight (w i)
    have he₁ : Tendsto V atTop (𝓝 (1:E→L[ℝ] E)):=by
       refine fitV _ _ (fun y=>?_)
       exact (by change Tendsto (fun i=>(u i) (f y)+A y • (w i)) atTop (𝓝 y); nth_rw 3 [hA y]; exact (beak u (fun _=>f y) U (f y) he tendsto_const_nhds).add (hp.const_smul _))
    refine revise V v f he₁ ?_
    apply fitV; intro y; have hz:= hx.const_smul (A y); have hu: Tendsto (fun i=> f y+ A y • v i (w i)) atTop (𝓝 (f y)):=by simpa only[smul_zero,add_zero] using hz.const_add (f y)
    refine hu.congr' (hR.mono fun i hi=>?_)
    change _=v i (u i (f y)+ A y • w i); rw [map_add,map_smul,show v i (u i (f y))= _ from DFunLike.congr_fun hi (f y)]; rfl
omit hx -- within boom requires eps pays.
-- size of contraction corruptor in sectors with a *marker* money `e → ∞` and required leak.
omit he hR hp hr h
-- estimates abstract from complete chart
lemma permute (L: E→L[ℝ] ℝ) (e : ℕ→ℝ)(he:Tendsto u atTop (𝓝 U))(hR:∀ᶠ i in atTop,(v i).comp (u i)=ContinuousLinearMap.id ℝ H)
    (hp:Tendsto w atTop (𝓝 x))(hv:Tendsto v atTop (𝓝 f))(h:x≠ 0)(hh:∀ y:E,f y=0↔ ∃ a:ℝ,y=a • x)(hr:f.comp U=ContinuousLinearMap.id ℝ H)
    (hV: Tendsto (fun i=> e i • v i (w i)) atTop (𝓝 0))(hL:Tendsto (fun i=> e i * L (w i)) atTop (𝓝 0)):
      Tendsto (fun i=>e i • ((L.comp (u i)).comp (v i)-L)) atTop (𝓝 0) := by
    obtain ⟨A,hA⟩:= plumage f U x h hh hr
    let V(j):= (u j).comp f+A.smulRight (w j); let D(j):=e j • ((L.comp (u j)).comp (v j)-L)
    have he₁:Tendsto V atTop (𝓝 (1:E→L[ℝ] E)):=by
       refine fitV _ _ (fun y=>?_)
       have h₀:=beak u (fun _=>f y) U (f y) he tendsto_const_nhds; exact (show (1:E→L[ℝ] E) y=U (f y)+ A y • x by exact hA y) ▸ h₀.add (hp.const_smul (A y))
    have hw:Tendsto (fun i=> e i * L (u i (v i (w i)))) atTop (𝓝 0):=by
        have hw:=L.continuous.continuousAt.tendsto.comp (beak u _ U 0 he hV)
        simpa only[Function.comp_def,map_zero,map_smul,smul_eq_mul] using! hw
    refine revise V D 0 he₁ (fitV _ _ fun y=>?_)
    have hZ:Tendsto (fun i=> A y*(e i * L (u i (v i (w i)))- e i * L (w i))) atTop (𝓝 0):=by simpa only[sub_zero,mul_zero] using! (hw.sub hL).const_mul (A y)
    refine hZ.congr' (hR.mono fun i hi=>?_)
    change _=e i*((L (u i (v i (u i (f y)+A y • w i)))) - L (u i (f y)+A y • w i)); rw [map_add,show v i (u i (f y))=f y from DFunLike.congr_fun hi (f y)]; simp only [map_add,map_smul,smul_eq_mul]; ring
lemma spend (e:ℕ→ℝ)(ρ:E→L[ℝ]ℝ) (he:Tendsto u atTop (𝓝 U))(hR:∀ᶠ i in atTop,(v i).comp (u i)=ContinuousLinearMap.id ℝ H) (hp:Tendsto w atTop (𝓝 x))(hv:Tendsto v atTop (𝓝 f))(h:x≠0)(hh:∀ y:E,f y=0 ↔ ∃ a:ℝ,y=a • x)(hr:f.comp U=ContinuousLinearMap.id ℝ H) (hV:Tendsto (fun i=>e i • v i (w i)) atTop (𝓝 0))(hL:Tendsto (fun i=> e i*ρ (w i)) atTop (𝓝 0)): ∃ (μ:ℕ → H →L[ℝ] ℝ) (m:H →L[ℝ] ℝ), Tendsto μ atTop (𝓝 m) ∧ Tendsto (fun i=>e i • ((μ i).comp (v i)-ρ)) atTop (𝓝 0) :=by
    exact ⟨fun i=>ρ.comp (u i),ρ.comp U,((show Continuous (fun x:H→L[ℝ] E=>ρ.comp x) from continuous_const.clm_comp continuous_id)).continuousAt.tendsto.comp he,permute f v U u x w _ e he hR hp hv h hh hr hV hL⟩
lemma expenses (e:ℕ→ℝ)(ρ:E→L[ℝ]ℝ) (he:Tendsto u atTop (𝓝 U))(hR:∀ᶠ i in atTop,(v i).comp (u i)=ContinuousLinearMap.id ℝ H) (hp:Tendsto w atTop (𝓝 x))(hv:Tendsto v atTop (𝓝 f))(h:x≠0)(hh:∀ y:E,f y=0 ↔ ∃ a:ℝ,y=a • x)(hr:f.comp U=ContinuousLinearMap.id ℝ H) (hV:Tendsto (fun i=>e i • v i (w i)) atTop (𝓝 0))(hL:Tendsto (fun i=> e i*ρ (w i)) atTop (𝓝 0)): ∃ μ:ℕ→ H→ₗ[ℝ]ℝ, ∃ C:ℝ,0≤C∧ (∀ᶠ i in atTop,∀ y:H,‖μ i y‖ ≤ C*‖y‖) ∧ (∀ z:ℝ,0<z→∀ᶠ i in atTop,∀ y:E, ‖e i*(μ i (v i y)-ρ y)‖ ≤ z*‖y‖):=by
    obtain ⟨μ,m,hM,hv'⟩:= spend f v U u x w e ρ he hR hp hv h hh hr hV hL
    refine ⟨fun i=> (μ i).toLinearMap, ‖m‖+1,(by positivity),?_ , fun z hz=> ?_⟩
    · filter_upwards[hM.norm.eventually (ge_mem_nhds (show ‖m‖ < ‖m‖+1 by linarith))] with i hi w
      exact ((μ i).le_opNorm w).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    let P(i):=e i • ((μ i).comp (v i)-ρ); filter_upwards[ hv'.norm.eventually (ge_mem_nhds (by simpa using hz : ‖(0 : E→L[ℝ] ℝ)‖ < z))] with i hi t
    exact ((P i).le_opNorm t).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))

end continuity
end YM.Trace.Terrace
