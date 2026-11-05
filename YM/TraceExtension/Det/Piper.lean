import YM.TraceExtension.Det.Prism

/-! # Local lyre slope derived in a single cell. Column bounds to degree three on time derivative with full moves. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{Y:Gal G f}
    {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
    {o:Site f}{F:Acr G f→ X}{m n:ℕ}{α β C D A:ℝ}

def loft (a:G.Color)(v:G.Color × G.Color):= G.plog (G.mat (G.lieExp v.1*G.lieExp a*(G.lieExp v.2)⁻¹))
lemma loft_be (G:Gauge): ContDiffAt ℝ ω (uncurry (loft (G:=G))) 0:=by
    unfold uncurry loft; simp_rw[G.mat_mul,G.mat_inv]; apply G.plog_diff.comp_of_eq
    · apply ContDiffAt.mul
      · exact ((catexp G).comp (f:=fun z:G.Color×G.Color×G.Color=> z.2.1) 0 (by fun_prop)).mul ((catexp G).comp (f:=Prod.fst) 0 (contDiffAt_fst (p:=(0:G.Color×G.Color×G.Color))))
      exact (show G.Mat≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ ((catexp G).comp (f:=fun z:G.Color×G.Color×G.Color=> z.2.2) 0 (by fun_prop))
    · simp
    change G.mat (G.lieExp 0)*G.mat (G.lieExp 0)*star (G.mat (G.lieExp 0))= _; simp [G.mat_lieExp_zero]
def larch (Y:Gal G f)(z:Acr G f): Link G f:= lyre Y (input G f (aleft G f z)) (aright G f z)
lemma piper_l (e:Edge (Site f))(h:Cloaked Y):
    edgeColor.toContinuousLinearMap ∘ larch Y=ᶠ[𝓝 0] edgeColor ∘ larch Y ∧
    (fun z=>edgeColor (larch Y z) e)=ᶠ[𝓝 0] fun z=> fderiv ℝ (loft (edgeColor (aright G f z) e)) 0 (edgeColor (Y (splitp G f z)) e,edgeColor (Y (input G f (aleft G f z))) e):=by
    constructor; · rfl
    let L(z:Acr G f):=edgeColor (aright G f z) e; let P:= fun z:Acr G f=>input G f (aleft G f z); let Z(z:Acr G f):=(edgeColor (Y (splitp G f z)) e,edgeColor (Y (P z)) e)
    let F(s:ℝ)(z:Acr G f):= lyr Y (P z) s (aright G f z)
    have ht(s z): edgeColor (F s z) e= loft (L z) (s • Z z):=by
        unfold F lyr psm tendr; rw [show edgeColor (content _) e=_ from content_at _ e.1 e.2]; simp only [Pi.mul_apply,Pi.inv_apply,input_color,map_smul];
        unfold loft; congr 2; change G.lieExp (s • (Z z).1)*(G.lieExp (L z)*P z e)*(G.lieExp (s • (Z z).2)*P z e)⁻¹=G.lieExp (s • (Z z).1)*G.lieExp (L z)*(G.lieExp (s • (Z z).2))⁻¹; group
    have hh: ContDiffAt ℝ ω L 0:= (ContinuousLinearMap.proj e ∘L edgeColor.toContinuousLinearMap ∘L aright G f).contDiff.contDiffAt
    have hL:L 0=0:=by simp [L]
    have hp:=nod_z h P (Army.powL (aleft G f).contDiff.contDiffAt) (show P 0=1 by simp[P])
    have hF: ContDiffAt ℝ ω (uncurry F) 0:=by
       have he: ContDiffAt ℝ ω (fun z:Acr G f × (ℝ × Link G f)=> lyr Y (P z.1) z.2.1 z.2.2) 0:= hp.logL (ps_z ..)
       let M(z:ℝ× Acr G f):=(z.2,z.1,aright G f z.2)
       have hv:M 0=0:=by unfold M; simp
       exact ContDiffAt.comp 0 (f:=M) (g:=fun z:Acr G f × (ℝ × Link G f)=> lyr Y (P z.1) z.2.1 z.2.2) (hv.symm ▸ he) (by unfold M; fun_prop)
    have hd:Tendsto (fun z=> (L z,(0:G.Color × G.Color))) (𝓝 0) (𝓝 0):= (show Tendsto L (𝓝 0) (𝓝 0) from hL ▸ hh.continuousAt.tendsto).prodMk_nhds tendsto_const_nhds
    filter_upwards [ hd.eventually ((loft_be G).eventually (by simp)), (show Tendsto (fun z:Acr G f=> ((0:ℝ),z)) (𝓝 0) (𝓝 0) from tendsto_const_nhds.prodMk_nhds tendsto_id).eventually (hF.eventually (by simp))] with z hz hx
    let T: Link G f→L[ℝ] G.Color:=ContinuousLinearMap.proj (R:=ℝ) e ∘L edgeColor.toContinuousLinearMap
    let g(s):= F s z
    have hp' : ContDiffAt ℝ ω g 0:= hx.comp (f:=fun s:ℝ=>(s,z)) 0 (by fun_prop)
    let U:=loft (L z); have hu: ContDiffAt ℝ ω U 0:= hz.comp (f:=fun u:G.Color × G.Color=> (L z,u)) 0 (by fun_prop)
    change T (fderiv ℝ g 0 1)=fderiv ℝ U 0 (Z z)
    have hj: HasDerivAt (T ∘ g) (T (fderiv ℝ g 0 1)) 0:= T.hasFDerivAt.comp_hasDerivAt _ (hp'.differentiableAt (by simp)).hasDerivAt
    apply hj.unique
    rw[show T ∘ g= U ∘ (fun s:ℝ=> s • Z z) from funext fun i=> ht i z]
    apply HasFDerivAt.comp_hasDerivAt _ ?_ (ray_id _); rw[zero_smul]; exact (hu.differentiableAt (by simp)).hasFDerivAt
lemma piper_m (G:Gauge)(k:ℕ): ∃ C:ℝ,0 ≤ C∧∀ (f:Side)(e:Edge (Site f))(a:ℝ),0≤a→ Pet (af G f) e.1 (fun z=> fderiv ℝ (loft (edgeColor (aright G f z) e)) 0) a C k:=by
    obtain ⟨P,hP,h⟩:=spike_m G k
    let X(z:G.Color):= fderiv ℝ (loft z) 0; let L:= fun z:G.Color×G.Color=>X z.2
    have hx : ContDiffAt ℝ ω X 0:= (Work.F05.curve_partial (loft_be G)).comp (f:=fun z:G.Color=> (z,0)) 0 (by fun_prop)
    have hL: ContDiffAt ℝ ω L 0:= ContDiffAt.comp (g:=X) (f:=(Prod.snd:G.Color × G.Color→ G.Color)) 0 hx contDiffAt_snd
    obtain ⟨C,hC,hV⟩:= exists_allows (f:=L) (s:={(0:G.Color×G.Color)}) isCompact_singleton (fun x hx=> hx.symm ▸ hL) k
    let Q:= composeCost k C P; have hQ: 0≤Q:=by unfold Q composeCost; positivity
    refine ⟨Q,hQ,fun f e a ha=>?_⟩
    let A(z:Acr G f):=(edgeColor (aleft G f z) e,edgeColor (aright G f z) e)
    have hv : A 0=0:=Prod.ext (by simp [A]) (by simp [A])
    have hp:= (show Allows k L (A 0) C from hv.symm ▸ hV _ (Set.mem_singleton _)).comp (h f e _ (rfl:A=A))
    change Pet _ _ (L ∘ A) _ Q _
    have ht: Requests Set.univ (L ∘ A) (af G f) e.1 0:=fun v _ w _ h=> by obtain ⟨he,hh⟩:=spoke0 _ _ _ h; exact congr_arg L (Prod.ext he hh)
    refine ⟨hp.analytic,?_⟩; have hz := Allows.beacon hp (f:=fun v=> L (A v)) ht univ_mem ha; simp only [Nat.mul_zero,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hz; exact hz
lemma drain_fee (α:ℝ)(a b : Site f)(k:ℕ):
    Decay α a b * Real.exp ((α/(k+1:ℝ))*(k:ℝ)*(separation a b)) = Decay (α/(k+1:ℝ)) a b:=by
    unfold Decay; rw [←Real.exp_add]; congr 1; field_simp; ring
-- relative components path plog. q radius drops
lemma pipe_w (G:Gauge)(k:ℕ): ∃ T:ℝ,0 ≤ T∧∀ (f:Side)(Y:Gal G f)(x:Site f)(A α:ℝ),0≤α→0≤A → Cloaked Y→ (∀ i:Lines G f 1, Pet Prod.fst x (fun z=> Y (input G f z) i) α (A*Decay α x i.1) k) →∀ i:Lines G f 1, Pet (af G f) x (fun z=> larch Y z i) (α/(k+1:ℝ)/(k+2:ℝ)) (T*A*Decay (α/(k+1:ℝ)/(k+2:ℝ)) x i.1) k:=by
    obtain ⟨R,hR,h⟩:= color_tale G; obtain ⟨T,hT,h'⟩:= cocoa_m (X:=G.Color) G k; obtain ⟨C,hC,hV⟩:= piper_m G k
    let P:= ContinuousLinearMap.id ℝ (G.Color×G.Color→L[ℝ]G.Color)
    let N(i:G.ColorIndex): G.Color →L[ℝ] ℝ:= EuclideanSpace.proj i
    let U:ℝ:=∑ i:G.ColorIndex,‖N i‖
    refine ⟨U*((2:ℝ)^k*‖P‖*C*(R*(1+T))),by unfold U; positivity,fun f Y x D α ha hD hc he i=>?_⟩
    rcases i with ⟨i,r,b⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective r; let e:Edge (Site f):=(i,a)
    let F(v:Acr G f):= (edgeColor (Y (splitp G f v)) e, edgeColor (Y (input _ _ (aleft G f v))) e)
    let K(v:Acr G f):= fderiv ℝ (loft (edgeColor (aright G f v) e)) 0
    let a₀:= α/(k+1:ℝ); let Z:= a₀/(k+2:ℝ); have ht : a₀ ≤ α:= div_le_self ha (by simp)
    have hZ: 0≤Z:= by unfold Z a₀; positivity
    have hx: Pet (af G f) x F a₀ (D*R*(1+T)*Decay α x i) k:=by
       let X:= h f _ _ _ _ _ hD he e
       have hh:0≤D*R*Decay α x i:=mul_nonneg (mul_nonneg hD hR) (decay_pos ..).le
       have hf:=h' f x (fun v=> edgeColor (Y v) e) α _ hh ha X
       apply (hf.pair (X.left_z hh|>.tilt le_rfl ht le_rfl)).tilt _ le_rfl le_rfl; dsimp only[e]; nlinarith only[]
    have hr:= (hV f e Z hZ).switch hC x hZ; have hE:= hx.tilt le_rfl (show Z≤a₀ from div_le_self (by unfold a₀; positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) k])) le_rfl
    have hd:= show 0 ≤ Decay α x i from (decay_pos ..).le
    have hh:= (hr.bins P hE (mul_nonneg hC (Real.exp_pos _).le) (by positivity)).monoL (N b)
    apply (hh.tilt ?_ le_rfl le_rfl).grows
    swap
    · have hN : ‖N b‖ ≤ U:= Finset.single_le_sum (fun i _=>norm_nonneg (N i)) (mem_univ b)
      have hu: Decay α x i * Real.exp (Z*k*separation x i) ≤ Decay Z x i:=by
        unfold Decay; rw[← Real.exp_add, Real.exp_le_exp]; have hv: (k+1:ℝ)*Z ≤ α:= (show (k+1:ℝ)*Z ≤ (k+2:ℝ)*Z by nlinarith only[hZ]).trans (le_trans (le_of_eq (by unfold Z; field_simp)) ht)
        have hy:= mul_le_mul_of_nonneg_right hv (show 0 ≤ (separation x i:ℝ) by positivity); linarith
      dsimp only [e]; apply le_trans (mul_le_mul_of_nonneg_right hN (by positivity)); calc
       _ = U*((2:ℝ)^k*‖P‖*C*(R*(1+T)))*D*(Decay α x i* Real.exp (Z*k*separation x i)):= by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hu (by unfold U; positivity)
    filter_upwards[(piper_l e hc).2] with z hz; exact congr_arg (N b) hz.symm
end YM.Trace.Det
