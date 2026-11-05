import YM.Push.LOOP_COEFFICIENT.Ghost
import YM.Push.LOOP_COEFFICIENT.LogDet

/-!
# Vector matrices of the prescription and their real regularity

Cell estimates are separate (nothing uniform asserted here). Fine and joint
entities all depend on the *actual* `mainTerm` etc of these same W,p.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice RG Exterior Wilson Precision Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {c f n : Side} {G : Gauge} {S : StepData c f} {p : Clip} {W : PathData G} {σ C Λ : ℝ}

/-- Transfer a site operator diagonally onto link directions at INITIAL sites. -/
def parallel {R : Type} [Zero R] (M : Matrix (SiteKey G n) (SiteKey G n) R) : Matrix (BondKey G n) (BondKey G n) R :=
  of fun i j => if i.1.2=j.1.2 then M (i.1.1,i.2) (j.1.1,j.2) else 0

def reference (μ : ℝ) (p : Clip) (W : PathData G) (U : Config G n) :=
  cost (mainTerm p W) U + R_g U * regulation μ U ^2 * (R_g U).transpose + μ^2 • (parallel (dressing μ U)^depth)

/-- Full logarithmic vector operator . Rooted notation for all group maps. -/
def vector (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) :=
  cost (completed p W t V) U + (completion t U).transpose * completion t U

/-- Base version `N_b`, which lacks the map drift only. -/
def baseVector (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) :=
  cost (mainTerm p W ∘ positions) U +
    (rate (Zmap t) U).transpose * cost (penalty S V) (Zmap t U) * rate (Zmap t) U +
    (completion t U).transpose * completion t U

/-- Exact scalar functions. -/
def scalar (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) :=
  (1/2 : ℝ) * Real.log (vector p W t V U).det - Real.log (ghost (mu S) (positions U)).det

def scalarRef (μ : ℝ) (p : Clip) (W : PathData G) (U : Config G n) :=
  (1/2 : ℝ) * Real.log (reference μ p W U).det - Real.log (ghost μ U).det

def Yresp (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) (v : Loops.Links G c) :=
  ((baseVector p W t V U)⁻¹ * acceleration (Zmap t) U v).trace

lemma vector_eq (hw : W.Bounds p σ C Λ) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f)
    (hu : MatDiffAt (Zmap t ∘ vary U) 0) : vector p W t V U = baseVector p W t V U +
      acceleration (Zmap t) U (first (penalty S V) (Zmap t U)) := by
  have hp : ContDiffAt ℝ ω (penalty S V ∘ vary (Zmap t U)) 0 := penalty_diff S (matDiffAt_const _) vary_diff
  rw [vector, show completed p W t V = (mainTerm p W ∘ positions) + penalty S V ∘ Zmap t from rfl,
    cost_add (Work.F02.mainTerm_contDiffAt hw (A:=positions ∘ vary U) (x:=0) (fun _ => vary_diff _))
      (hu.along (by simp) hp), cost_comp hu hp, baseVector]; abel

lemma vector_flat (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices) :
    vector p W t 1 (1:Loops.Inputs G c f) = baseVector p W t 1 1 := by
  rw [vector_eq hw t 1 _ (Zmap_diff h t (by simp) vary_diff),Zmap_one h]
  have he : fderiv ℝ (penalty S (1:Config G c) ∘ vary 1) 0 = 0 := by
    have hf : HasFDerivAt (𝕜:=ℝ) (fun a : Loops.Links G c => ∑ i, G.price (G.lieExp (paint G _ a i))) 0 0 := by
      have ht (i : Bonds c) : HasFDerivAt (𝕜:=ℝ) (fun a : Loops.Links G c => G.price (G.lieExp (paint G _ a i))) 0 0 := by
        let L := ((LinearMap.proj i).comp (paint G (Bonds c)).toLinearMap).toContinuousLinearMap
        have he := ((Work.F03.price_smooth (A:=G.lieExp) G.exp_jet.contDiffAt).differentiableAt (by simp)).hasFDerivAt
        rw [exp_price_rate.1,← L.map_zero] at he
        exact (he.comp 0 L.hasFDerivAt).congr_fderiv (ContinuousLinearMap.zero_comp _)
      simpa using HasFDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => ht i)
    have eq : penalty S (1:Config G c) ∘ vary 1 = (fun a : Loops.Links G c => S.kernel.penalty • (∑ i,G.price (G.lieExp (paint G _ a i)))) := by
      ext a; simp [penalty,smul_eq_mul]
    rw [eq]; simpa using! (hf.const_smul S.kernel.penalty).fderiv
  unfold acceleration first grad
  rw [he]; change _ + twist _ _ 0 = _
  rw [twist_zero,add_zero]

/-- `mainTerm` piece sees no frame slots. -/
lemma cost_input (hw : W.Bounds p σ C Λ) (U : Loops.Inputs G c f) :
    cost (mainTerm p W ∘ positions) U = (projectFine G c f).transpose * cost (mainTerm p W) (positions U) * projectFine G c f := by
  let P := ((projectFine G c f).mulVecLin).toContinuousLinearMap
  have he : positions ∘ vary U = vary (positions U) ∘ P := by
    funext v i; unfold positions; simp only [Function.comp_apply,vary]; congr 1
    apply PiLp.ext; intro j
    change v (.inl i,j) = (projectFine G c f *ᵥ v) (i,j)
    rw [projectFine,LinearMap.toMatrix'_mulVec]; rfl
  have hp := Work.F02.mainTerm_contDiffAt hw (A:=vary (positions U)) (x:=0) vary_diff
  rw [cost, Function.comp_assoc, he, ← Function.comp_assoc, bilinearAt_chain (P.map_zero.symm ▸ hp) P.contDiff.contDiffAt, P.map_zero,
    linearAt,P.fderiv, show LinearMap.toMatrix' (P : _ →ₗ[_] _) = projectFine G c f by exact LinearMap.toMatrix'_toLin' _, cost, show twist (P : _ → Loops.Links G f) 0 _ = 0 from ?_,add_zero]
  apply Finset.sum_eq_zero; intro i _; suffices bilinearAt (fun z => P z i) 0 = 0 by rw [this, smul_zero]
  let L := ((LinearMap.proj i).comp P.toLinearMap).toContinuousLinearMap
  ext m n
  change bilinearAt (L : _ → ℝ) 0 m n = _
  rw [bilinearAt_apply,iteratedFDeriv_two_apply,
    show fderiv ℝ (L : _ → ℝ) = fun _ => L by ext1; rw [L.fderiv], fderiv_fun_const]; rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {m k l : Type} [Fintype m] [Fintype k] [Fintype l]

lemma matrix_component {f : E → Matrix m k ℝ} (hf : ContDiffAt ℝ ω f x) (i j) :
    ContDiffAt ℝ ω (fun y => f y i j) x :=
  (contDiff_apply ℝ _ j).contDiffAt.comp _ ((contDiff_apply ℝ _ i).contDiffAt.comp
    (f := fun y => (Matrix.ofLinearEquiv ℝ).symm (f y)) _
    ((Matrix.ofLinearEquiv ℝ (m:=m) (n:=k) (α:=ℝ)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp (f:=f) x hf))

lemma smooth_transpose {f : E → Matrix m k ℝ} (hf : ContDiffAt ℝ ω f x) :
    ContDiffAt ℝ ω (fun t => (f t).transpose) x := matrix_diff (fun i j => matrix_component hf j i)

lemma smooth_mul {f : E → Matrix m k ℝ} {g : E → Matrix k l ℝ} (hf : ContDiffAt ℝ ω f x)
    (hg : ContDiffAt ℝ ω g x) : ContDiffAt ℝ ω (fun t => f t * g t) x := matrix_diff
  (fun i j => ContDiffAt.sum (fun k _ => (matrix_component hf i k).mul (matrix_component hg k j)))

lemma smooth_R {U : E → Config G n} (h : MatDiffAt U x) : ContDiffAt ℝ ω (fun y => R_g (U y)) x := by
  refine matrix_diff (fun ⟨i,k⟩ j => ?_)
  let a := (Pi.single j 1 : Nodes G n)
  change ContDiffAt ℝ ω (fun y => paint G _ (brace (U y) a) i k) x
  simp_rw [paint_brace]
  have hd := adjoint_diff (a:=fun _ => paint G _ a (i.1+step i.2)) (h i) contDiffAt_const
  exact (PiLp.proj (𝕜:=ℝ) 2 _ k).contDiff.contDiffAt.comp (f:=fun y => _ - G.adjoint (U y i) _) x (contDiffAt_const.sub hd)

lemma smooth_ghost {U : E → Config G n} (μ : ℝ) (h : MatDiffAt U x) :
    ContDiffAt ℝ ω (fun t => ghost μ (U t)) x := (smooth_mul (smooth_transpose (smooth_R h)) (smooth_R h)).add contDiffAt_const

lemma smooth_dressing {U : E → Config G n} {μ : ℝ} (hμ : 0 < μ) (h : MatDiffAt U x) :
    ContDiffAt ℝ ω (fun t => dressing μ (U t)) x :=
  ((inv_contDiffAt _ (isUnit_iff_ne_zero.mpr (ghost_pos _ μ hμ).det_pos.ne')).comp x (smooth_ghost μ h)).const_smul _

lemma smooth_regulation {U : E → Config G n} {μ : ℝ} (hμ : 0 < μ) (h : MatDiffAt U x) :
    ContDiffAt ℝ ω (fun t => regulation μ (U t)) x := ContDiffAt.sum (s:=Finset.range (depth+1)) fun i _ => (smooth_dressing hμ h).pow i

variable [DecidableEq m] [DecidableEq k]

omit [DecidableEq k] in
lemma smooth_rate {U : E → PatchField G m} {f : PatchField G m → PatchField G k} (hu : MatDiffAt U x) (h : MatDiffAt (f ∘ vary (U x)) 0) :
    ContDiffAt ℝ ω (fun t => rate f (U t)) x := by
  have he : MatDiffAt (f ∘ U) x := fun i => hu.along (g:=fun v => G.mat (f v i)) rfl (h i)
  have hw := (hu.comp (show ContDiffAt ℝ ω Prod.fst (x,(0:Array G m)) from contDiffAt_fst)).vary contDiffAt_snd
  have hh : MatDiffAt (fun z => f (vary (U z.1) z.2)) (x,(0:Array G m)) :=
    fun i => hw.along (g:=fun v => G.mat (f v i)) (U:=U x) (by simp) (h i)
  have hi := (MatDiffAt.comp (x:=(x,(0:Array G m))) (f:=Prod.fst) (v:=f ∘ U) he contDiffAt_fst).displacement
    hh (by change f (vary (U x) 0) = f (U x); rw [vary_zero])
  exact ContDiffAt.comp (g:=uncurry fun v w => linearAt (localize f (U v)) w) (f:=fun t => (t,0)) x
    (linearAt_diff (m:=Point G m) (n:=Point G k) (x:=x) hi) (contDiffAt_id.prodMk contDiffAt_const)

omit [DecidableEq k] in
lemma smooth_cost {U : E → PatchField G m} {f : E → PatchField G m → ℝ} (hf : ContDiffAt ℝ ω
    (uncurry fun v a => f v (vary (U v) a)) (x,0)) : ContDiffAt ℝ ω (fun t => cost (f t) (U t)) x :=
  ContDiffAt.comp (g:=uncurry fun v w => bilinearAt (f v ∘ vary (U v)) w) (f:=fun t => (t,0)) x
    (bilinearAt_diff hf) (contDiffAt_id.prodMk contDiffAt_const)

lemma smooth_completion (h : S.patch.Branches S.kernel G) (t : S.Choices) {U : E → Loops.Inputs G c f}
    (h1 : U x = 1) (hu : MatDiffAt U x) : ContDiffAt ℝ ω (fun x => completion t (U x)) x := by
  have hX : ContDiffAt ℝ ω (fun x => X₀ t (U x)) x := smooth_rate hu (fun i => mat_inv_diff
    ((Psi_diff h t (by simp [h1]) vary_diff) i))
  have hv : MatDiffAt (positions ∘ U) x := fun i => hu (Sum.inl i)
  exact (smooth_mul (smooth_mul (smooth_regulation mu_pos hv) (smooth_transpose (smooth_R hv))) contDiffAt_const).add
    ((smooth_mul ((smooth_dressing mu_pos hv).pow _) hX).const_smul _)

lemma smooth_vector (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices)
    {V : E → Config G c} {U : E → Loops.Inputs G c f} (h1 : U x = 1) (hu : MatDiffAt U x) (hv : MatDiffAt V x) :
    ContDiffAt ℝ ω (fun x => vector p W t (V x) (U x)) x :=
  (smooth_cost (completed_diff h hw t (U:=fun z : E × Loops.Dual G c f => vary (U z.1) z.2) (x:=(x,0)) ((vary_zero (U x)).trans h1) ((hu.comp contDiffAt_fst).vary contDiffAt_snd)
    (V:=V ∘ Prod.fst) (hv.comp contDiffAt_fst))).add (smooth_mul (smooth_transpose (smooth_completion h t h1 hu)) (smooth_completion h t h1 hu))

lemma smooth_base (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices)
    {V : E → Config G c} {U : E → Loops.Inputs G c f} (h1 : U x = 1) (hu : MatDiffAt U x) (hv : MatDiffAt V x) :
    ContDiffAt ℝ ω (fun x => baseVector p W t (V x) (U x)) x := by
  have hZ : MatDiffAt (Zmap t ∘ vary (U x)) 0 := Zmap_diff h t (by simp [h1]) vary_diff
  have hr := smooth_rate (f:=Zmap t) hu hZ
  have hZ' := (MatDiffAt.comp (x:=(x,(0:Loops.Links G c))) (v:=Zmap t ∘ U) (f:=Prod.fst) (Zmap_diff h t h1 hu) contDiffAt_fst).vary contDiffAt_snd
  have hv' := MatDiffAt.comp (x:=(x,(0:Loops.Links G c))) (v:=V) (f:=Prod.fst) hv contDiffAt_fst
  have hp := smooth_cost (x:=x) (U:=Zmap t ∘ U) (f:=fun x => penalty S (V x))
    (penalty_diff S (x:=(x,(0:Loops.Links G c))) (Z:=fun z => vary (Zmap t (U z.1)) z.2) (V:=V ∘ Prod.fst) hv' hZ')
  have ht := (hu.comp (show ContDiffAt ℝ ω Prod.fst (x,(0:Loops.Dual G c f)) from contDiffAt_fst)).vary contDiffAt_snd
  have he := smooth_completion h t h1 hu
  exact ((smooth_cost (U:=U) (f:=fun _ => mainTerm p W ∘ positions) (Work.F02.mainTerm_contDiffAt hw (A:=fun z : E × Loops.Dual G c f => positions (vary ((U ∘ Prod.fst) z) z.2))
    (x:=(x,0)) (fun i => ht (.inl i)))).add (smooth_mul (smooth_mul (smooth_transpose hr) hp) hr)).add
    (smooth_mul (smooth_transpose he) he)

lemma smooth_reference {U : E → Config G n} {μ : ℝ} (hμ : 0 < μ) (hw : W.Bounds p σ C Λ) (hu : MatDiffAt U x) :
    ContDiffAt ℝ ω (fun x => reference μ p W (U x)) x := by
  have hr := smooth_R hu
  have hp : ContDiffAt ℝ ω (fun x => parallel (dressing μ (U x))) x := by
    refine matrix_diff fun i j => ?_; unfold parallel; dsimp only [of_apply]; split
    · exact matrix_component (smooth_dressing hμ hu) ..
    exact contDiffAt_const
  exact ((smooth_cost (U:=U) (f:=fun _ => mainTerm p W) (Work.F02.mainTerm_contDiffAt hw ((hu.comp contDiffAt_fst).vary contDiffAt_snd))).add
    (smooth_mul (smooth_mul hr ((smooth_regulation hμ hu).pow 2)) (smooth_transpose hr))).add
    ((hp.pow _).const_smul _)

end YM.Push.Loops
