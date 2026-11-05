import YM.TraceExtension.Lamp.Meal
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i:Axis)(q:G.ColorIndex)
variable {V:∀ w,Peat G (g w)} {R:W→PathData G}{μ:W→ℝ}
lemma hearth_pk (h:Pico (fun _=>0) (fun w=> V w ∘ input G (g w)) 4) (hw:Parked (fun w=>shellB p (R w) (μ w) ∘ input G (g w)) 2): Pico (fun _=>0) (fun w=> sailM p (R w) (μ w) (V w)) 2:=by
    obtain ⟨A,T,hA,hT,H⟩:= h.top
    obtain ⟨E,hE,h⟩:= beamer G 2
    have ht : Pella (fun _=>0) (fun w=> beamH (V w) ∘ input G (g w)) 2:= ⟨_,_,div_pos hA (by exact (show 0 < ((↑(2:ℕ):ℝ)+2+1) from by positivity)),mul_nonneg hE hT, fun w=>h _ _ _ _ _ hA.le hT (H w)⟩
    exact (ht.leftM hw).trace
lemma pet_hush {E:W→ℝ}(Tn:Tendsto (fun w=>(g w).val) L atTop) (w:∀ v, Maze G (g v))(ha:0<a)(h:∀ z, Pet Prod.fst (0:Site (g z)) (w z) a (E z) 2)(hp:∀ z,0≤E z)(p:Tendsto E L (𝓝 0))(M':ℝ)(he:∀ z,E z≤M')(hM:0≤ M')(b:Axis): Rose L (fun z=> lux d i q b (w z)) 0:=by
    apply Rose.chain (lux_neap d i q Tn w (show Pico _ _ _ from ⟨a,M',ha,hM,fun z=> (h z).tilt (he z) le_rfl le_rfl⟩) b)
    let A z:=molt (0:Site (g z)) (![mood G i q,mood G i q]) (w z)
    have ht(x:Dish) : Rose L (fun z=> neap 3 (A z) 0 (lawn d b x)) 0:=by
       unfold Rose; rw[sub_zero]
       let f z := ((3:ℕ).factorial:ℝ)⁻¹ * (ramt 3 (Fin 2) a* E z)* ‖lawn d b x‖^ (3:ℕ)
       refine squeeze_zero_norm' ?_ (show Tendsto f L (𝓝 0) from ?_)
       · exact Eventually.of_forall fun z=> norm_neap (malt (h z) ha (hp z) _ 0 3) le_rfl
       unfold f; simpa using (((p.const_mul (ramt 3 (Fin 2) a)).const_mul (((3:ℕ).factorial:ℝ)⁻¹)).mul_const (‖lawn d b x‖^(3:ℕ)))
    exact (disk_coh (F:=fun z x=> neap 3 (A z) 0 (lawn d b x)) (H:=fun _=>0) ht).chain (Rose.skip (Eventually.of_forall fun _ =>(show Deb 0=0 from map_zero _)))
lemma hearth_hush {E:W→ℝ}(Tn:Tendsto (fun w=>(g w).val) L atTop) (ha:0<a)(h:∀ z,Pet Prod.fst (0:Site (g z)) (V z∘ input G (g z)) a (E z) 4) (hp:∀ z,0≤ E z) (p':Tendsto E L (𝓝 0))(M':ℝ)(he:∀ z,E z≤M')(hM:0≤M')(b:Axis) (hw:Parked (fun w=>shellB p (R w) (μ w) ∘ input G (g w)) 2): Rose L (fun z=> lux d i q b (sailM p (R z) (μ z) (V z))) 0:=by
    obtain ⟨T,hT,H⟩:= beamer G 2
    obtain ⟨η,C,hη,hC,g'⟩:= hw.spins.top
    let v:= min (a/(2+2+1:ℝ)) η; have hv:0<v:=lt_min (by positivity) hη
    let u:=v/((↑(2:ℕ):ℝ)+2);have hu:0<u:=by unfold u; positivity
    let D:ℝ:= (Fintype.card (Loc G 1):ℝ)*countCost u; have hD:0≤D:=mul_nonneg (by positivity) (count_pos hu).le
    let U(t:ℝ):=((2:ℝ)^(2:ℕ)*‖ContinuousLinearMap.mul ℝ ℝ‖*(T*t)*C*D)*D; have hx(t)(ht:0≤t):0≤U t:=by unfold U; positivity
    apply pet_hush d i q Tn (a:=u) (fun z=>sailM p (R z) (μ z) (V z)) hu (E:=U∘ E) _ (fun z=>hx _ (hp z)) ?_ (U M') _ (hx _ hM) b
    · intro z; let Z:=shellB p (R z) (μ z)∘ input G (g z); let F:=beamH (V z) ∘ input G (g z)
      have he : PetW (0:Site (g z)) (fun q=>F q) v (T*E z) 2:=by
         have hp' := H _ _ _ _ _ ha.le (hp z) (h z); refine hp'.tiny ?_ (mul_nonneg hT (hp z)) le_rfl le_rfl; exact (min_le_left ..)
      have hz:= (he.spotV.cross_r ((g' z).tiny (show v≤η from min_le_right ..) hC le_rfl le_rfl) hv (mul_nonneg hT (hp z)) hC).spotV; have hh:= hz.grade hu (by change 0 ≤ (2:ℝ)^(2:ℕ)*_*_*_*D; have ht:=hp z; positivity)
      simp_rw [transpose_mul,transpose_transpose] at hh; rw [mul_assoc _ (Fintype.card _:ℝ) (countCost _)] at hh; exact hh
    · have hv : Continuous U:=by unfold U; fun_prop
      have hz: U 0=0:=by simp [U]
      exact (show Tendsto U (𝓝 0) (𝓝 0) from by simpa only [hz] using hv.tendsto 0).comp p'
    intro z; change U (E z) ≤ U M'; unfold U;
    gcongr; exact he z
-- ∆ response actually sampled on torus
lemma pilots (d i:Axis)(q:G.ColorIndex){Z: Peat G f}{μ:ℝ}(b:Axis) (A:Axis→Site f→Peat G f)(h:∀ a x, Cleric (A a x))(he:Memo (shellB p M μ ∘ input G f) 0)(hp: Cleric Z):
    lux d i q b (sailM p M μ ((∑ a, elm a (A a) 0)-Z))= (∑ a, lux d i q b (elm a (fun x=> sailM p M μ (A a x)) 0))-lux d i q b (sailM p M μ Z):=by
    let J(a):= elm a (A a) 0
    have hh(a):Cleric (J a):= elm_cleric (A a) a (h a) _
    have hf: Cleric (∑ i,J i):= (clergy G f).sum_mem (fun i _=>hh i)
    let X:= ∑ i,J i
    change lux d i q b (sailM p M μ ((∑ i,J i)-Z))=_; rw[lux_far d i b q (arm_sail_s hf hp),lux_s d i b q (hearth_s hf he) (hearth_s hp he)]; congr 1
    rw[lux_far d i b q (arm_sail_t (p:=p) _ (fun i _=> hh i)), lux_t d i b q (fun i=>hearth_s (hh i) he)]; exact sum_congr rfl fun a _=> lux_far _ _ _ _ (arm_sail_e (A a) a (h a) _)
lemma traverse_pay {μ:ℝ}(h:M.Bounds p α C D)(hμ:0<μ)(he:(stock p M μ (1:Config G f)).det≠0)(X:Site f → Peat G f)(hx:X 0∈ loom G f)(ht:∀ i,X i= rj i (X 0)):
    Traverse (fun i=>sailM p M μ (X i)):=by
    obtain ⟨ha,hb⟩:=hx; refine ⟨hearth_s ha ((gate_shell h hμ he (Army.powL (v:=id) contDiffAt_id) (input_zero ..)).1),?_⟩
    intro s; have hp': sailM p M μ (X s)=sailM p M μ (rj s (X 0)):= by rw[ht s]
    change sailM p M μ (X s) =ᶠ[𝓝 0] _; rw[hp']; exact hearth_trans ha s h hμ he
end YM.Trace.Lamp
