import YM.TraceExtension.Perfect.Grid

/-! # Pack p0 & radius envelopes on ordinary and flux readers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
section
variable {W:Type*} {I J:W→Type} [∀ w,Fintype (I w)][∀ w,DecidableEq (I w)][∀ w,Fintype (J w)][∀ w,DecidableEq (J w)]
    {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X] {N:ℕ}
/-- When replacing the domain and sym lift readers. Costs even though zeros inside Faa at noncoherent index. -/
lemma Calm.thin {A:∀ w,I w→ℕ} {v:∀ w,Rays (I w)→ X} (h: Calm A v N) (Z:∀ w,J w→ℕ)
    (g:∀ w,I w↪ J w)(T:∀ w,Rays (J w) →L[ℝ] Rays (I w)) (H:∀ w j,T w (desk (g w j))=desk j) (he:∀ w j, j ∉ Set.range (g w) → T w (desk j)=0)(hx:∀ w j,Z w (g w j)= A w j) : Calm Z (fun w x=>v w (T w x)) N:=by
 classical
 obtain ⟨a,C,c,y,U⟩:= h.shape
 refine ⟨fun w=>(show ContDiffAt ℝ ω (v w) (T w 0) by rw [map_zero]; exact h.velvet w).comp _ (T w).contDiff.contDiffAt,a,C,c,y,fun w n hn=>?_⟩
 refine le_trans (le_of_eq (b:=cost (A w) a 0 0 (leaf (v w) 0 n)) ?_) (U _ _ hn)
 let E : (Fin n→I w)↪ (Fin n→J w):= ⟨fun x=> g w ∘ x, fun x y ht=> funext (fun i=> (g w).injective (congr_fun ht i))⟩
 let f := fun x: Fin n→J w=> spot a 0 0 (limitN (Z w) x)* ‖iteratedFDeriv ℝ n (fun z:Rays (J w)=> v w (T w z)) 0 (desk ∘ x)‖
 have hY x : f x= spot a 0 0 (limitN (Z w) x)* ‖iteratedFDeriv ℝ n (v w) 0 (T w ∘ (desk ∘ x))‖:= by
      unfold f; change _= _
      rw [show (fun z: Rays (J w)=> v w (T w z))=v w ∘ T w from rfl, wired (T w) (by rw [map_zero]; exact (h.velvet w).analyticAt),map_zero]
 change ∑ i,f i=_
 rw [show (∑ i,f i)=∑ i∈univ.map E,f i from Eq.symm (Finset.sum_subset (Finset.subset_univ _) ?_), Finset.sum_map]; swap
 · intro i _ hx; rw [hY]; obtain ⟨j,hq⟩: ∃ j, i j ∉ Set.range (g w):=by
       by_contra! hp; choose g hg using hp; exact hx (Finset.mem_map.mpr ⟨g,mem_univ _,funext hg⟩)
   let f :=iteratedFDeriv ℝ n (v w) 0; rw [show f (T w ∘(desk ∘ i))=0 from f.map_coord_zero j (he _ _ hq),norm_zero,mul_zero]
 apply Finset.sum_congr rfl; intro i _; rw [hY, show (T w ∘ (desk ∘ E i))=desk ∘ i from funext (fun x=> H w _)]
 rw [show limitN (Z w) (E i)=limitN (A w) i from ?_]
 unfold limitN; congr 1; exact funext fun k=>hx w _
lemma Calm.finitude {D:∀ w,I w→ℕ}(q:∀ w,Finset (J w))(M:ℕ)(f:∀ w, J w→Rays (I w)→X)(h:Calm (fun w:Σ w,↥(q w) =>D w.1) (fun w=>f w.1 w.2.val) N)(ht:∀ i,(q i).card≤M): Calm D (fun w x=>∑ i∈q w,f w i x) N:=by
 classical
 obtain ⟨a,C,c,y,H⟩:=h.shape
 let z (w:W)(x:Rays (I w)):=∑ i: (q w), f w i.val x; have hu w i : ContDiffAt ℝ ω (fun x=> f w (i:↥(q w)) x) 0:= h.velvet ⟨w,i⟩
 have hZ(w:W)(i:ℕ): leaf (z w) 0 i=(fun v=>∑ j:(q w), leaf (f w j.val) 0 i v):=by
      ext1 p; unfold leaf bank; rw [show z w=(∑ i : q w,f w i.val) from funext (fun x=> by rw [Finset.sum_apply])]
      rw [iteratedFDeriv_sum_apply (f:=fun i:q w=> f w i.val) (fun i _=> (hu w i).of_le le_top), _root_.sum_apply]
 apply Calm.near (f:=z) (Calm.mk (D:=D) (m:=N) (fun w=>ContDiffAt.sum (f:=fun i : q w=> f w i.val) (s:=univ) (fun i _=> hu w i)) ?_) _
 · refine ⟨a,M*C,c,by positivity,fun i n hn=>?_⟩; rw [hZ]
   refine ((cost_sum ..).trans (Finset.sum_le_sum (fun (j:↥(q i)) _=> H ⟨_,j⟩ n hn))).trans ?_; simp; gcongr;exact ht i
 intro w; exact Eventually.of_forall fun x=> by change ∑ i∈(q w).attach,_ =_; exact Finset.sum_attach _ (fun i=> f w i x)
end

variable {c f:Side}
-- Aux slots
abbrev pairA (G : Gauge)(n:Side):= Lines G n 1 ⊕ Lines G n 1
abbrev Acr (G : Gauge)(n:Side):= Rays (pairA G n)
abbrev bite (G: Gauge)(n: Side): Acr G n ≃L[ℝ] (Link G n × Link G n):= Push.Uniform.partSpace ..

def bottom (Y:Config G f→Link G f)(z:Acr G f):= (Y (input G f (bite G f z).1)) ⬝ᵥ (bite G f z).2

def stampA (S:StepData c f)(t:S.Choices)(Z:Link G c→Stationary.Joint G c f)(x:Acr G c):Acr G f:=
  let V:= bite G c x; let Q:=Z V.1; let T:= ribbon S t Q; let C:= Stationary.billsM (Stationary.pocket _) (Stationary.pocket _) (shuttle S t Q (input G c V.1))
  (bite G f).symm (content Q.1,C.transpose *ᵥ V.2)

-- assembly scalar reader
variable {S:StepData c f}{F : Forest S.ratio}{ρ:Bid.Dir G c→AxisChart G F} {W: Matrix (Body 1 f) (Body 1 c) ℝ}
lemma grants_pin {p:Clip}{M:PathData G}{η α D:ℝ}(t:S.Choices)(h:Critical F p M ρ) (hv:S.patch.Branches S.kernel G)(m:Site f)(hy:M.Bounds p η α D)(Y:Config G f→Link G f)(hY:Cloaked Y):
    bottom (inheritY F ρ t Y)=ᶠ[𝓝 0] bottom Y ∘ stampA S t (fresh F ρ W m):=by
    let f' :Acr G c→ Link G c:=fun x=> (bite G c x).1
    let U:= fresh F ρ W m
    have he : Tendsto f' (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto.comp (show Tendsto (bite G c) (𝓝 0) (𝓝 0) from by simpa using (bite G c).continuous.tendsto 0)
    filter_upwards [he.eventually (port (W:=W) h hv t m hY hy)] with x hp
    dsimp only [Function.comp_apply] at *
    unfold bottom stampA; simp only [ContinuousLinearEquiv.apply_symm_apply]; rw [show (bite G c x).1=f' x from rfl,hp]
    let T:= shuttle S t (U (f' x)) (input G c (f' x))
    let v:= Y (input G f (content (U (f' x)).1)); let z:= (bite G c x).2
    change (T v) ⬝ᵥ z=v ⬝ᵥ (_ *ᵥ z)
    rw [Stationary.transposes,bill_pay]
    -- see orientation from lapel
end YM.Trace.Perfect
