import YM.TraceExtension.Loft.Sled
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {ι κ I W α β:Type}[Fintype α][DecidableEq α]{σ A:ℝ}{g:W→Side}{L:Filter W}{G:Gauge}{f:Side}{p:Clip}{k m n:ℕ}
variable {V:Film ι α α}
-- use bundled compact angles of fixed rank: no diagonal-only vertex estimates
section pack
abbrev rankl (x:Fin n)(p:Phase (Fin n × Axis)):Momentum:= fun i=> p (x,i)
lemma ledge (x:Fin n)(p:Phase (Fin n × Axis)) : DifferentiableAt ℂ (rankl x) p:= differentiableAt_pi.mpr fun j=> (differentiable_apply (x,j)).differentiableAt
lemma scored (x:Fin n){p q:Phase (Fin n × Axis)}(h:rolls p q): rolls (rankl x p) (rankl x q):=by obtain ⟨z,rfl⟩:=h; exact ⟨fun i=> z (x,i),rfl⟩
lemma flap (x:Fin n){p:Phase (Fin n × Axis)}(h:p∈strip σ): rankl x p∈strip σ:=fun i=>h (x,i)
lemma span_m (hx:0 < σ){p q:Momentum}(h:p∈strip (σ/3))(hp:q∈strip (σ/3)): Avenue σ p q:=by
    refine ⟨fun i=>(h i).trans_le (by linarith),fun i=>(hp i).trans_le (by linarith),fun i=>?_⟩
    rw[Pi.add_apply, Complex.add_im]; exact (abs_add_le ..).trans_lt (by linarith[h i,hp i])
lemma tall_m (hx:0 < σ){p q z:Momentum}(h:p∈strip (σ/3))(hp:q∈strip (σ/3))(he:z∈strip (σ/3)): Boulevard σ p q z:=by
    refine ⟨span_m hx h he,span_m hx hp he,fun i=>?_⟩; simp only[Pi.add_apply,Complex.add_im]; exact (abs_add_le ..).trans_lt ((add_le_add_right (abs_add_le ..) _).trans_lt (by linarith[h i,hp i,he i]))
lemma rink_h (h:Skew V σ A)(hp:0 < σ)(i j:α): Firm σ A (fun p=> V.tab p i j) :=⟨⟨hp,fun _ x=> h.covered.tab.shape x i j, fun p hp z => congr_arg (fun M:CompM α α=> M i j) (h.covered.tab.shifts ⟨z,rfl⟩ hp|>.symm)⟩, fun p hx=> (flux_tilt _ _ _).trans (basic_w.mp (h.base hx))⟩
lemma rim_h (h:Skew V σ A)(hp:0 < σ)(a:ι)(i j:α): Firm (σ/3) A (fun z:Phase (Fin 2 × Axis)=> V.spot a (rankl 0 z) (rankl 1 z) i j):=by
    refine ⟨⟨by positivity,fun z hx=> (h.covered.spot a).go (span_m hp (flap 0 hx) (flap 1 hx)) (ledge 0 z) (ledge 1 z) i j,fun z hz x=> ?_⟩,fun z hz=> (flux_tilt _ _ _).trans (basic_w.mp (h.detail a (span_m hp (flap _ hz) (flap _ hz))))⟩
    exact congr_arg (fun V:CompM α α=>V i j) ((h.covered.spot a).shifts (scored 0 ⟨x,rfl⟩) (scored 1 ⟨x,rfl⟩) (span_m hp (flap _ hz) (flap _ hz)) |>.symm)
lemma arch_h (h:Skew V σ A)(hp:0 < σ)(a b:ι)(i j:α): Firm (σ/3) A (fun z:Phase (Fin 3 × Axis)=> V.arch a b (rankl 0 z) (rankl 1 z) (rankl 2 z) i j):=by
    refine ⟨⟨by positivity,fun z hx=> (h.covered.arch a b).go (tall_m hp (flap 0 hx) (flap 1 hx) (flap 2 hx)) (ledge 0 z) (ledge 1 z) (ledge 2 z) i j,fun z hz x=> ?_⟩,fun z hz=> (flux_tilt _ _ _).trans (basic_w.mp (h.stamp a b (tall_m hp (flap _ hz) (flap _ hz) (flap _ hz))))⟩
    exact congr_arg (fun V:CompM α α=>V i j) ((h.covered.arch a b).shifts (scored 0 ⟨x,rfl⟩) (scored 1 ⟨x,rfl⟩) (scored 2 ⟨x,rfl⟩) (tall_m hp (flap _ hz) (flap _ hz) (flap _ hz))|>.symm)
end pack
section family
variable {V: W→Film ι α α} (h:∀ w,Skew (V w) σ A)(hp:0 < σ)(i j:α)
include h hp
abbrev legA (F: Film ι α α) (x:Track):CompM α α:=F.tab (axes x)
abbrev Trail:=Track× Track
abbrev legB (F: Film ι α α) (a:ι) (x:Trail):CompM α α:=F.spot a (axes x.1) (axes x.2)
abbrev Trest:=Track × Trail
abbrev legC (F:Film ι α α)(a b:ι) (x:Trest):CompM α α:=F.arch a b (axes x.1) (axes x.2.1) (axes x.2.2)
lemma lo_h: Honor (fun w x=> legA (V w) x i j) n:=honor_fm fun w =>rink_h (h w) hp i j
lemma pin_h (a:ι) : Honor (fun w x=> legB (V w) a x i j) n:=by
    let P:Trail →L[ℝ] Track:=ContinuousLinearMap.fst ..; let Q:Trail →L[ℝ] Track:=ContinuousLinearMap.snd ..
    let M:Trail→L[ℝ] Corn (Fin 2 × Axis):=ContinuousLinearMap.pi (fun i=> (ContinuousLinearMap.proj i.2) ∘L (![P,Q] i.1))
    exact (honor_fm (n:=n) (fun w=>rim_h (h w) hp a i j)).dam M
lemma row_h (a b:ι): Honor (fun w x=>legC (V w) a b x i j) n:=by
    let P:Trest →L[ℝ] Track:=ContinuousLinearMap.fst ..; let Q:Trest →L[ℝ] Trail:=ContinuousLinearMap.snd ..; let X: Trail→L[ℝ] Track:=ContinuousLinearMap.fst ..; let Y:Trail→L[ℝ] Track:=ContinuousLinearMap.snd ..
    let M:Trest→L[ℝ] Corn (Fin 3 × Axis):=ContinuousLinearMap.pi (fun i=> (ContinuousLinearMap.proj i.2) ∘L (![P,X ∘L Q,Y ∘L Q] i.1))
    exact (honor_fm (n:=n) fun w=> arch_h (h w) hp a b i j).dam M
end family
abbrev TreeF:=Track × Land
def mapD {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] (p:Fin k→ X→L[ℝ] Track)(a b:X→L[ℝ] Track): X→L[ℝ] Backs k:= ((ContinuousLinearMap.pi p).prod a).prod b
variable {V: W →TubeF G k}{F:∀ w,WildM G (g w) k k}
lemma honorsE {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{F H:W → X → ℂ}(h:Honor F m)(hp:∀ w x,F w x= H w x): Honor H m:=by rwa [← funext (fun w=> funext fun x=>hp w x)]
lemma mapD_one {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] (a b c:X→L[ℝ] Track)(x:X): mapD (![a]:Fin 1→_) b c x=((![a x],b x),c x):=by
   refine Prod.ext (Prod.ext (funext (fun i=>?_)) rfl) rfl
   fin_cases i; rfl
lemma mapD_zero {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] (b c:X→L[ℝ] Track)(x:X): mapD (![]:Fin 0→_) b c x=((![],b x),c x):= Prod.ext (Prod.ext (Subsingleton.elim ..) rfl) rfl
lemma honor_sq (h:Oil L F)(hp:∀ w,Skew (V w) σ A)(he:0 < σ)(i j:Loc G k)(a:Fslot G): Honor (fun w (x:TreeF)=> moss (V w) (F w) x.1 a i j x.2) n:=by
    let T : TreeF→L[ℝ] Track:=ContinuousLinearMap.fst ..; let R:TreeF→L[ℝ] Land:=ContinuousLinearMap.snd ..
    let P:=ContinuousLinearMap.proj (0:Fin 2) ∘L R; let Q:=ContinuousLinearMap.proj (1:Fin 2) ∘L R
    have hh:=h.jets; let K w x:=moss (V w) (F w) (T x) a i j (R x)
    -- eta Pi over empty & singleton: construct special CLM by pi, Backs arguments propositional.
    let W₁:= R.prod T |>.prod (-T); let W₂:=mapD (![Q]:Fin 1→_) (T+P) (-T); let W₃:=mapD (![P]:Fin 1→_) (T+Q) (-T); let W₄:= mapD (![]:Fin 0→_) (T+(P+Q)) (-T)
    have ht:= (carb_cap (p:= (![]:Fin 0→_)) (m:=n) i j (hh.tada (by decide))).dam W₄
    have hx:= (carb_cap (p:=(![a,a]:Fin 2→_)) (m:=n) i j hh).dam W₁; have hy:= carb_cap (m:=n) (p:=(![a]:Fin 1→_)) i j (hh.tada (by decide))
    let C:= ContinuousLinearMap.mul ℝ ℂ; have hS:=pin_h (n:=n) hp he j i a; have hz:= (row_h (n:=n) hp he j i a a).dam (P.prod (Q.prod T))
    have hv:= (((Honor.prod C hx ((lo_h (n:=n) hp he j i).dam T)).more (Honor.prod C (hy.dam W₂) (hS.dam (P.prod T)))).more (Honor.prod C (hy.dam W₃) (hS.dam (Q.prod T)))).more (Honor.prod C ht hz)
    apply honorsE hv; intro w x; simp only [Pi.add_apply,Function.comp_apply,W₂,W₃,W₄, mapD_one,mapD_zero]; rfl
end YM.Trace.Loft
