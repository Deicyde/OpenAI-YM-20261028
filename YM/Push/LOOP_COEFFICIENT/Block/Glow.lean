import YM.Push.LOOP_COEFFICIENT.Block.Induce

/-!
# Periodic analyticity of alias sums of degree ≤ two
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Set Filter Matrix Metric Lattice Laurent Bloch RG Complex 
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d e E F : Type} [Fintype a] [Fintype b] [Fintype d] [Fintype e] [DecidableEq a] [DecidableEq b] [DecidableEq d] [DecidableEq e] {L : Side} {η : ℝ} {Y : Profiles L d e}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {x : E}

structure Flow (Y : Profiles L d e) (η : ℝ) : Prop where
  smooth k q : q∈Tube η → ContDiffAt ℂ ω (fun q => Y q k) q
  align k q : q∈Tube η → ∀ z : Cover,Y (q+reciprocal z) k = Y q (k+wrap L z)

omit [DecidableEq d] in
lemma Flow.action {q : E → Momentum} (h : Flow Y η) (hq : ContDiffAt ℂ ω q x) (ht : q x∈Tube η) (l : Site L) (v) : ContDiffAt ℂ ω (fun z => Y (q z) l *ᵥ v) x := contDiffAt_pi.mpr fun i => ContDiffAt.sum fun j _ => ((analyticComponent (h.smooth l _ ht) i j).comp x hq).mul contDiffAt_const

lemma channel_diff {q s : E → Momentum} {f : E → Matrix a b ℂ} (i l : Site L) (hq : ContDiffAt ℂ ω q x) (hs : ContDiffAt ℂ ω s x) (hf : ContDiffAt ℂ ω f x) : ContDiffAt ℂ ω (fun z => channel (q z) (s z) i l (f z)) x := analyticMul (analyticMul ((place_diff ..).comp x hq) hf) ((select_diff ..).comp x hs)

lemma units (x : d → ℂ) : ∑ i, x i • Pi.single i (1:ℂ) = x := by ext j; simp [Finset.sum_apply,Pi.single_apply,mul_ite]
lemma plug₁ {f : E → CSpace d →ₗ[ℂ] F} {v : E → CSpace d} (h : ∀ w, ContDiffAt ℂ ω (fun y => f y w) x) (hv : ContDiffAt ℂ ω v x) : ContDiffAt ℂ ω (fun y => f y (v y)) x := by
  simp_rw [show ∀ y, f y (v y) = ∑ i, v y i • f y (Pi.single i 1) by intro y; conv_lhs => rw [← units (v y),map_sum]; simp]
  exact ContDiffAt.sum fun i _ => (contDiffAt_pi.mp hv i).smul (h _)
lemma plug₂ {f : E → CSpace d →ₗ[ℂ] CSpace d →ₗ[ℂ] F} {v w : E → CSpace d} (h : ∀ u z, ContDiffAt ℂ ω (fun y => f y u z) x) (hv : ContDiffAt ℂ ω v x) (hw : ContDiffAt ℂ ω w x) : ContDiffAt ℂ ω (fun y => f y (v y) (w y)) x := plug₁ (f:=fun y => f y (v y)) (fun u => plug₁ (f:=fun y => (f y).flip u) (fun z => h z u) hv) hw

private lemma reindex {ι : Type*} [Fintype ι] [AddGroup ι] {F : Type*} [AddCommMonoid F] (x : ι) (u v : ι → F) (h : ∀ i,u i = v (i+x)) : ∑ i,u i = ∑ i,v i := (Finset.sum_congr rfl fun i _ => h i).trans (Equiv.sum_comp (Equiv.addRight x) v)
private lemma recv (q p : Momentum) (x y : Cover) : q+reciprocal x + (p+reciprocal y)=q+p+reciprocal (x+y) := by rw [reciprocal_add]; abel

lemma induce_lit {V : Vertex d a b} (hv : Lit V (η/L.val)) (h : Flow Y η) : Lit (induce V Y) η := by
  have he (l : Site L) {p} (hp : p∈Tube η) := alias_tube l hp
  constructor
  · intro q hq; refine ⟨ContDiffAt.sum (fun i _ => channel_diff i i contDiffAt_id contDiffAt_id (hv.zeroD (q:=fun p => aliasAt p i) (alias_diff i).contDiffAt (he i hq))),fun x => reindex (wrap L x) _ _ (fun i => ?_)⟩
    obtain ⟨y,hy⟩ := alias_shift i q x; simp only [channel,matrixMulLinear,LinearMap.comp_apply,LinearMap.mk₂_apply,LinearMap.flip_apply,place_shift,select_shift,hy,(hv.base _ (he _ hq)).2]
  · intro q p v hq hp; simp only [induce,LinearMap.sum_apply,LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have H (i j : Site L) : ContDiffAt ℂ ω (fun z : Momentum × Momentum => V.one (aliasAt z.1 i) (aliasAt z.2 j) ((Y z.2 j) *ᵥ v)) (q,p) := plug₁ (f:=fun z => V.one (aliasAt z.1 i) (aliasAt z.2 j)) (fun w => hv.oneD (x:=(q,p)) ((alias_diff i).contDiffAt.comp (f:=Prod.fst) _ (by fun_prop)) ((alias_diff j).contDiffAt.comp (f:=Prod.snd) _ (by fun_prop)) (he i hq) (he j hp) w) (h.action contDiffAt_snd hp j v)
    constructor
    · apply ContDiffAt.sum; intro j hj; apply ContDiffAt.sum; intro i hi; exact channel_diff (q:=fun z => z.1+z.2) (s:=Prod.fst) (x:=(q,p)) (i+j) i (by fun_prop) contDiffAt_fst (H i j)
    refine fun x y => reindex (wrap L y) _ _ fun j => reindex (wrap L x) _ _ fun i => ?_
    obtain ⟨x',hx⟩ := alias_shift i q x; obtain ⟨y',hy⟩ := alias_shift j p y
    simp only [channel,matrixMulLinear,LinearMap.comp_apply,LinearMap.mk₂_apply,LinearMap.flip_apply,recv,place_shift,select_shift,hx,hy,h.align _ _ hp,(hv.one _ _ _ (he _ hq) (he _ hp)).2,map_add,show i+j+(wrap L x+wrap L y)=i+wrap L x+(j+wrap L y) by abel]
  intro q p s v w hq hp hs; simp only [induce,LinearMap.sum_apply,LinearMap.compr₂_apply,LinearMap.compl₁₂_apply, Matrix.mulVecLin_apply]
  have H (i j l : Site L) : ContDiffAt ℂ ω (fun z : Momentum × Momentum × Momentum => V.two (aliasAt z.1 i) (aliasAt z.2.1 j) (aliasAt z.2.2 l) ((Y z.2.1 j) *ᵥ v) ((Y z.2.2 l) *ᵥ w)) (q,p,s) := plug₂ (f:=fun z : Momentum × Momentum × Momentum => V.two (aliasAt z.1 i) (aliasAt z.2.1 j) (aliasAt z.2.2 l)) (fun a b => hv.twoD (x:=(q,p,s)) ((alias_diff i).contDiffAt.comp (f:=Prod.fst) _ (by fun_prop)) ((alias_diff j).contDiffAt.comp (f:=fun z : Momentum × Momentum × Momentum => z.2.1) _ (by fun_prop)) ((alias_diff l).contDiffAt.comp (f:=fun z : Momentum × Momentum × Momentum => z.2.2) _ (by fun_prop)) (he i hq) (he j hp) (he l hs) a b) (h.action contDiffAt_snd.fst hp _ v) (h.action contDiffAt_snd.snd hs _ w)
  constructor
  · apply ContDiffAt.sum; intro j hj; apply ContDiffAt.sum; intro l hl; apply ContDiffAt.sum; intro i hi; exact channel_diff (s:=Prod.fst) (x:=(q,p,s)) (q:=fun z => z.1+z.2.1+z.2.2) (i+(j+l)) i (by fun_prop) contDiffAt_fst (H i j l)
  refine fun x y z => reindex (wrap L y) _ _ fun j => reindex (wrap L z) _ _ fun l => reindex (wrap L x) _ _ fun i => ?_
  obtain ⟨x',hx⟩ := alias_shift i q x; obtain ⟨y',hy⟩ := alias_shift j p y; obtain ⟨z',hz⟩ := alias_shift l s z
  simp only [channel,matrixMulLinear,LinearMap.comp_apply,LinearMap.mk₂_apply,LinearMap.flip_apply,recv,place_shift,select_shift,hx,hy,hz,h.align _ _ hp,h.align _ _ hs,(hv.two _ _ _ _ _ (he _ hq) (he _ hp) (he _ hs)).2,map_add,show i+(j+l)+(wrap L x+wrap L y+wrap L z)=i+wrap L x+(j+wrap L y+(l+wrap L z)) by abel]
end YM.Push.Loops.Block
