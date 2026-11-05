import YM.Next.STATIONARY.OneLoop.WilsonVertices

set_option autoImplicit false
/-!
# Gauge term completes the longitudinal symbol. First slot only here.
Does not rotate direction labels away. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {V : Jar G} {σ C : ℝ} {p k : Momentum}
section lids
lemma pump_base (i j : Fslot G) : pummel i j 0=0 := by unfold pummel; split <;> simp [scattering_one]
lemma tabBase : (firstB G).tab=0 := by
  ext1 p; ext i j; simp only [firstB,recitalX,patina,Matrix.of_apply]; rw [ show (fun l:Fin 0=>Pi.single ((![]:Fin 0→Loc G 1) l) (1:ℂ))=axes ∘ (![]:Fin 0→Corn (Loc G 1)) from Subsingleton.elim ..,beat_real]; simp [pump_base]
lemma deflect (v : TypeFace 1) (i : Fslot G) : delocalF v G (Pi.single i 1)= if i.1=v then pearl i.2 else 0 := by
  apply (Lilts G).injective; ext1 j
  rcases i with ⟨i,a⟩; change (Pi.single (i,a) (1:ℝ) : Corn (Fslot G)) (v,j)= _
  split <;> rename_i h
  · change i=v at h; rw [h,(Lilts G).apply_symm_apply]; by_cases H:j=a <;> simp [*]
  change ¬i=v at h; simp [Ne.symm h]
lemma pump_cost (a : Axis) (b x y : G.ColorIndex) (i j : Axis) : beat (pummel (coord i,x) (coord j,y)) 0 1 ![Pi.single (coord a,b) 1]= if i=j ∧ a=i then -tintX b x y else 0 := by
  let z : Corn (Fslot G) := Pi.single (coord a,b) 1; let u := pummel (coord i,x) (coord j,y); let T := pearl y; let B : G.El→ℝ := fun g=> (Lilts G (T-G.adjoint g T)) x
  let f (t : ℝ) := u (t • z)
  have he := Push.side u (pummel_diff _ _).differentiableAt z
  rw [show (![_] : Fin 1 → Phase (Fslot G))= axes ∘ (![z]: Fin 1 → Corn (Fslot G)) by
    funext k l; fin_cases k; by_cases h : l=(coord a,b) <;> simp [z,Pi.single_apply, *,axes],beat_real,iteratedFDeriv_one_apply]
  change ((fderiv ℝ u 0 z:ℝ):ℂ)=_
  have hf : fderiv ℝ u 0 z=deriv f 0 := he.deriv.symm
  rw [hf]
  by_cases h : i=j ∧ a=i
  · rw [if_pos h]
    have hx : f=fun t : ℝ => B (G.lieExp (t • pearl b)) := by
      ext1 t; simp only [f,u,pummel,show coord i=coord j from blinkV i j|>.2 h.1,if_true,map_smul]
      rw [deflect,if_pos (show coord a=coord j from blinkV a j|>.2 (h.2.trans h.1))]; rfl
    let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : G.ColorIndex=>ℝ) x ∘L (Lilts G).toContinuousLinearMap
    have ht : deriv f 0= L (0-G.ad (pearl b) T) := by rw [hx]; exact (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hasDerivAt_const _ T).sub (color_pitch (pearl b) T))).deriv
    rw [ht,zero_sub]; change ↑(-(cosetR b x y))= (-tintX b x y:ℂ); rw [Complex.ofReal_neg]; rfl
  rw [if_neg h]; rw [show f=(fun _=>0) from ?_]; simp
  ext1 t; by_cases H:i=j
  · have he : coord a≠coord i := fun hx=> h ⟨H,axisEquiv.injective hx⟩
    unfold f u pummel; rw [if_pos (show coord i=coord j from blinkV i j|>.2 H),map_smul,deflect,if_neg (show ¬((coord a,b) : Fslot G).1=coord i from he)]; simp [scattering_one]
  exact if_neg (fun H' => H (axisEquiv.injective H'))

lemma pedals (i) (x y : G.ColorIndex) : pageD G 0 k (coord i,x) (vac,y)= if x=y then Exterior.q k i else 0 := by simp [pageD,tintedLocal,sym_one]
lemma dash_actual (i : Axis) (x y : G.ColorIndex) : dashboard G (coord i,x) (vac,y)= if x=y then 1 else 0 := by by_cases H:x=y <;> simp [dashboard,dasher,H,Matrix.sum_apply,blinkV]
lemma matinBeige : (matina G).tab= -(pageD G 0) := by
  ext1 p; simp [matina,Film.plus,Pi.add_apply,Film.pay,tabBase,firstRay,Film.cardF]
lemma strums (a i j : Axis) (b x y : G.ColorIndex) : (firstB G).spot (coord a,b) p k (coord i,x) (coord j,y)= if i=j ∧ a=i then -tintX b x y else 0 := by
  have hh := pump_cost a b x y i j; rw [← hh]; unfold firstB recitalX; simp only [patina,Matrix.of_apply]
  congr; ext1 z; fin_cases z; rfl
lemma fireball (i a : Axis) (b x y : G.ColorIndex) : (matina G).spot (coord a,b) p k (coord i,x) (vac,y) = -(mode k (step i))*deer i a*tintX b x y := by
  rw [show (matina G).spot (coord a,b) p k=(firstB G).spot (coord a,b) p k*((boardF G).tab k) from ?_]
  swap; · simp [matina,Film.plus,Film.pay,firstRay,Film.cardF, boardF]
  unfold boardF Film.cardF; rw [Matrix.mul_apply,Fintype.sum_prod_type,← Equiv.sum_comp axisEquiv]; simp_rw [coord_map,strums,Matrix.add_apply,dash_actual,pedals]; unfold deer
  by_cases h : i=a
  · rw [if_pos h, sum_eq_single i]
    · rw [sum_eq_single y]; simp [factor,q,h]; ring
      · intro j _ hj; simp [hj]
      simp
    · intro j _ H'; simp [Ne.symm H']
    simp
  simp [h,Ne.symm h]

-- first ghost Spot in closed form. rear sector incoming −(k+p)
lemma recordStand (a : Axis) (b x y : G.ColorIndex) : (quarry G).spot (coord a,b) p k (vac,x) (vac,y) = (-(mode (-(k+p)) (step a) *Exterior.q k a)+ Exterior.q (-(k+p)) a * mode k (step a))*tintX b x y := by
  rw [quarry, Film.pay]; simp only [matinBeige,Matrix.add_apply,Matrix.mul_apply, Film.rear, Matrix.transpose_apply, matinBeige,Fintype.sum_prod_type];
  simp_rw [← Equiv.sum_comp axisEquiv, coord_map, Pi.neg_apply, Matrix.neg_apply, fireball,pedals]
  rw [sum_eq_single a]; swap
  · intro i _ H; simp [deer,H]
  pick_goal 2; · simp
  rw [sum_eq_single a]
  swap; · intro i _ H; simp [deer,H]
  pick_goal 2; · simp
  rw [sum_eq_single y]; swap
  · intro i _ h; rw [if_neg h]; simp
  pick_goal 2; · simp
  rw [sum_eq_single x]; swap
  · intro i _ h; rw [if_neg h]; simp
  pick_goal 2; · simp
  rw [tintSwap b y x]; simp only [deer, ↓reduceIte, mul_one]; ring
end lids
end YM.Stationary
end

/-!
# Quadratic vector operator. Real scaled expansions NO alpha assumption.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {V : Jar G} {σ C : ℝ} {p k : Momentum}
section sky
lemma recordingA (i j a : Axis) (x y z : G.ColorIndex) : ((matina G).pay (matina G).rear).spot (coord a,z) p k (coord i,x) (coord j,y)= (mode k (step i)*deer i a * Exterior.q (-k) j + -(Exterior.q (k+p) i)*mode (-(k+p)) (step j)*deer j a)*tintX z x y := by
  simp only [Film.pay,matinBeige, Matrix.add_apply, Matrix.mul_apply, Film.rear, Matrix.transpose_apply, Fintype.sum_prod_type]
  simp_rw [vac_only,Pi.neg_apply,Matrix.neg_apply,fireball,pedals]
  let L := tintX z
  have hm (X : ℂ) : ∑ _k : TypeFace 0, X=X := by rw [sum_eq_single vac]; all_goals simp [vac_only]
  rw [hm,hm,sum_eq_single y]
  swap; · intro i _ hi; rw [if_neg hi.symm]; simp
  pick_goal 2; · simp
  rw [sum_eq_single x]
  swap; · intro i _ hi; rw [if_neg hi.symm]; simp
  pick_goal 2; · simp
  rw [tintSwap z y]; simp only [↓reduceIte]; ring

lemma axes_solid (a b : Track) : axes (a+b)=axes a+axes b := by ext; simp [axes]
lemma motile (k : Track) (i : Axis) : Tendsto (fun x : ℝ=>mode (axes (x • k)) (step i)) cutRay (𝓝 1) := by
  have h : Continuous fun x : Track=> mode (axes x) (step i) := by unfold mode axes; fun_prop
  refine (show (mode (axes (0:Track)) (step i))=1 by simp) ▸ (h.continuousAt.tendsto.comp (along k))
lemma ghostPing (a : Axis) (b x y : G.ColorIndex) (p k : Track) :
    Tendsto (fun t : ℝ=> (t:ℂ)⁻¹ *((quarry G).spot (coord a,b) (axes (t • p)) (axes (t • k)) (vac,x) (vac,y))) cutRay (𝓝 (-(2*tachy k a+tachy p a)*tintX b x y)) := by
  let z := -(k+p)
  have he (t:ℝ) : -(axes (t • k)+axes (t • p))=axes (t • z) := by unfold z; rw [smul_neg, axes_flip,smul_add,axes_solid]
  have hh := (((motile z a).mul (qPitch a k)|>.neg).add ((motile k a).mul (qPitch a z))).mul_const (tintX b x y)
  simp_rw [recordStand,he]; convert hh.congr' ?_ using 1
  swap; · refine Eventually.of_forall (fun t=> ?_); dsimp only; ring
  congr 1; unfold tachy z; simp only [Pi.neg_apply,Pi.add_apply, Complex.ofReal_neg, Complex.ofReal_add]; ring

lemma axePing (i j a : Axis) (b x y : G.ColorIndex) (p k : Track) :
    Tendsto (fun t : ℝ=> (t:ℂ)⁻¹ *((matina G).pay (matina G).rear).spot (coord a,b) (axes (t • p)) (axes (t • k)) (coord i,x) (coord j,y)) cutRay (𝓝 ( (-tachy k j*deer i a - tachy (k+p) i*deer j a)* tintX b x y)) := by
  let z := -(k+p)
  have he (t:ℝ) : axes (t • k)+axes (t • p)=axes (t • (k+p)) := by rw [smul_add,axes_solid]
  have hx (t:ℝ) (p : Track) : -axes (t • p)=axes (t • (-p)) := by rw [smul_neg,axes_flip]
  simp_rw [recordingA, he, hx];
  have hh := (((motile k i).mul_const (deer i a)|>.mul (qPitch j (-k))).sub (((motile z j).mul_const (deer j a)).mul (qPitch i (k+p)))).mul_const (tintX b x y)
  convert hh.congr' ?_ using 1
  swap; · refine Eventually.of_forall (fun t=> ?_); dsimp only [z]; ring
  congr 1; unfold tachy; simp only [Pi.add_apply, Pi.neg_apply,Complex.ofReal_neg]; ring

def ghostC (p k : Track) (a : Axis) (b : G.ColorIndex) (x y : G.ColorIndex) := -(2*tachy k a+tachy p a)* tintX b x y
def vectorC (p k : Track) (a : Axis) (b : G.ColorIndex) (i j : Axis) (x y : G.ColorIndex) := deer i j* ghostC p k a b x y + 2*(tachy p j*deer i a-tachy p i*deer j a)* tintX b x y
lemma vectorPing (h : V.grey) (hv : V.fees σ C) (hp : 0<σ) (i j a : Axis) (x y b : G.ColorIndex) (p k : Track) : Tendsto (fun t : ℝ=> (t:ℂ)⁻¹ * (granary G V.cast).spot (coord a,b) (axes (t • p)) (axes (t • k)) (coord i,x) (coord j,y)) cutRay (𝓝 (vectorC p k a b i j x y)) := by
  let M := matina G; have hx := corona_funded (coord a,b) (coord i,x) (coord j,y) p k
  rw [coronet] at hx
  simp_rw [granary,Film.plus,Pi.add_apply,Matrix.add_apply,vintage_sings h hv hp _ _ _ _ _ (axes_real _) (axes_real _),mul_add]
  convert hx.add (axePing i j a b x y p k) using 2
  unfold vectorC ghostC tachy; push_cast; simp; ring
end sky
end YM.Stationary
end

/-!
# Mark the two subquadratic vertices on TOTAL Ward-supported lines.
X2 no leading needed. Ingredients intended consumption as real Vane only.
 -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {V U : Jar G} {B : Bed} {F : KindF G} {σ C D μ ε τ A : ℝ} {p : Clip}

-- comparisons using qualitative rays; also on finite repeats through identity curtain. resin.
-- need undo graniteF.tab. use its tickets, `Poster.renew`
lemma granite_tab (h : 0<μ) (he : μ≤1) : ∀ i∈strip (μ*(1/128:ℝ)),(graniteF G μ).tab i=satin μ i • (1:CompM (Fslot G) (Fslot G)) := by
  apply Poster.renew (granite_green h he).tab (satin_contours h he) (by positivity) walentes
  refine fun i=> ⟨_,(grantV (m:=walent i) (G:=G) h).tab,?_⟩; rw [cardM,input_zero]; exact bingo (satin μ) (tonic_cannon _ h)
lemma barePost (hp : HouseWord G B p D ε σ C μ F) (i : Momentum) (hi : star i=i) : (granary G F).tab i= rug G B i + pageD G 0 i * (pageD G 0 (-i))ᵀ := by
  have he := hp.pact i (Work.F07.realStrip _ hp.pos hi); simp only [massif,Film.plus,Pi.add_apply,dais] at he
  rw [granite_tab hp.amount.1 hp.amount.2 i (Work.F07.realStrip _ (hp.pos.trans_le hp.phase) hi),add_left_inj] at he; exact he
lemma bareQuarry : (quarry G).tab=(fun i => stone i • 1) := by
  ext1 p; simp only [quarry, Film.pay, Film.rear,matinBeige, Pi.neg_apply, Matrix.transpose_neg, Matrix.neg_mul,Matrix.mul_neg,neg_neg,codex_value]

-- Stone momentum. cost

def pebb (p : Track) : ℂ := ∑ j : Axis,(p j:ℂ)^2

def skull (p : Track) (α : Type) [DecidableEq α] := pebb p • (1:CompM α α)
lemma shrimper (i : Axis) : Rays 2 (fun p : Track => Exterior.q (axes p) i - Complex.I*(p i:ℂ)) := by
  let L : Track→L[ℝ] ℂ := Complex.ofRealCLM ∘L ContinuousLinearMap.proj i
  let T : Track →ℂ := fun p => Complex.exp (L p *Complex.I)
  let K : Track→L[ℝ] ℂ := Complex.I • L
  refine twin_shear ?_ fun p=> ?_
  · apply ContDiffAt.analyticAt
    unfold q; apply ContDiffAt.sub; swap; exact K.contDiff.contDiffAt
    let f : Track→ℂ := fun p=> Complex.I * (axes p i)
    apply ContDiffAt.sub _ contDiffAt_const; refine ContDiffAt.comp (x:=0) (g:=Complex.exp) (f:=f) ?_ K.contDiff.contDiffAt
    exact (by fun_prop)
  have hp : ∀ᶠ u : ℝ in cutRay, (u:ℂ)⁻¹ * (q (axes (u • p)) i - Complex.I*((u • p) i:ℂ))=(u:ℂ)⁻¹*q (axes (u • p)) i -Complex.I*(p i:ℂ) := by
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay,t≠0)] with t ht; change t≠0 at ht; simp; field_simp [ht]
  have hx := (qPitch i p).sub_const (Complex.I*(p i:ℂ)); rw [sub_self] at hx; exact hx.congr' (EventuallyEq.symm hp)
lemma rockEdge : Rays 3 (fun p : Track=> stone (axes p)-pebb p) := by
  have hQ i : Rays 1 (fun p : Track=>Exterior.q (axes (-p)) i) :=
    let W := fun p:Momentum=>Exterior.q p i; by
    have ht : Rays 1 (fun p : Track=>W (axes p)) := by have he := ray_symbol (Embedding.refl Axis) (coord i) vac; simp_rw [sym_one] at he; exact he
    intro x; simpa [smul_neg] using ht (-x)
  unfold stone pebb dotProduct; simp_rw [← Finset.sum_sub_distrib];
  have hx i : Rays 1 (fun p : Track=>Complex.I*(p i:ℂ)) := (rays_at_zero (f:=_) ((Complex.I • (Complex.ofRealCLM ∘L ContinuousLinearMap.proj (φ:=fun _ : Axis => ℝ) i) : Track→L[ℝ] ℂ).analyticAt _)).2 (by simp)
  have hZ p (i : Axis) : q (-(axes (p:Track))) i * q (axes p) i-(p i:ℂ)^2 = (q (axes p) i-Complex.I*(p i:ℂ))*q (axes (-p)) i+ Complex.I*(p i:ℂ)*(q (axes (-p)) i - Complex.I*((-p) i:ℂ)) := by
    rw [axes_flip]; simp only [Pi.neg_apply,Complex.ofReal_neg]; linear_combination -(p i:ℂ)^2 * Complex.I_mul_I
  simp_rw [hZ]
  refine rays_total fun i=> Rays.add ((shrimper i).mul (hQ i)) (Rays.mul (hx i) (fun p=> ?_) : Rays (1+2) _)
  have hh := shrimper i (-p); simp_rw [smul_neg] at *; exact hh

lemma bedLum (h : HouseWord G B p D ε σ C μ F) (i j : Fslot G) : Rays 3 (fun x : Track=> (granary G F).tab (axes x) i j-skull x (Fslot G) i j) := by
  have hx a b : Rays 1 (fun x:Track => (B.metric.read (axes x) a b - Row.read leader (axes x) a b)) := by
    have hd a b := price_step_metric h.pos h.metric a b
    refine (rays_at_zero (AnalyticAt.sub ((hd a b).analytic_real 0) ((price_step_metric h.pos (leader_pay σ) a b).analytic_real 0))).2 ?_
    simp [(h.lower 1).starts];
  have he z : tintedLocal G (dcross B.metric z) = rug G B z := by simp only [rug,pageD,tessH,dcross,tinted_flip,tinted_pay]
  have ht z : tintedLocal G (dcross leader z)+ pageD G 0 z*(pageD G 0 (-z))ᵀ=stone z • 1 := by
    rw [dcross, leader_const, Matrix.mul_one, tinted_pay, tinted_flip,add_comm,← kartel z 0]; rfl
  have hw z : (granary G F).tab (axes z) i j - skull z (Fslot G) i j= (tintedLocal G (dcross B.metric (axes z)) i j- tintedLocal G (dcross leader (axes z)) i j)+(stone (axes z)-pebb z)*(1:CompM (Fslot G) _) i j := by
    have hh := congr_fun (congr_fun (ht (axes z)) i) j; rw [Matrix.add_apply, Matrix.smul_apply,smul_eq_mul] at hh
    rw [barePost h _ (axes_real z), Matrix.add_apply, ← he,sub_mul, ← hh]; unfold skull; rw [Matrix.smul_apply,smul_eq_mul]; abel
  simp_rw [hw]
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  have hR v:= (rockEdge v).const_mul_left ((1:CompM (Fslot G) _) (a,b) (c,d))
  intro v; unfold tintedLocal; simp only [Matrix.of_apply]; simp_rw [mul_comm _ ((1:CompM (Fslot G) _) (a,b) (c,d))]; split; next hep=> exact (bed_gain _ _ hx a c v).add (hR v)
  next heq => simp only [sub_zero,zero_add]; exact hR v
lemma quarryLum (i j : Foot G) : Rays 3 (fun x: Track=> (quarry G).tab (axes x) i j-skull x (Foot G) i j) := by
  simp_rw [bareQuarry,skull,Matrix.smul_apply,smul_eq_mul,← sub_mul,mul_comm _ ((1:CompM (Foot G) _) i j)]; intro v; exact (rockEdge v).const_mul_left _
end YM.Stationary
end

/-!
# Orbit leading vertices n=1 as real Track. Slots μ in lower House
only; analytic and rays in pre-L widths. Vector ghost formula specializes
from Jag P arbit.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α β : Type} [Fintype α] [Fintype β] {G : Gauge} {V U : Jar G} {B : Bed} {F : KindF G} {σ C D μ ε τ A : ℝ} {p : Clip}

abbrev GlideTrack := Track×Track
lemma formish {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] {g : X→ℂ} {x : X} (hv : ∀ᶠ i in 𝓝 x, DifferentiableAt ℂ g i) : AnalyticAt ℂ g x := by
  let n := Module.finrank ℂ X
  let T : X ≃L[ℂ] (Fin n→ℂ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hh : AnalyticAt ℂ (g ∘ T.symm) (T x) := by
    apply PolyDisc.formOf
    filter_upwards [(show Tendsto T.symm (𝓝 (T x)) (𝓝 x) by simpa using T.symm.continuous.tendsto (T x)).eventually hv] with z hx
    exact hx.comp z T.symm.differentiableAt
  rw [show g=(g ∘ T.symm) ∘ T from funext fun x=>by simp]; exact hh.comp (f:=T) (T.analyticAt x)
lemma Barter.windowR {f : Momentum→Momentum→CompM α β} (h : Barter σ f) (hv : 0<σ) (x : GlideTrack) (i j) : AnalyticAt ℝ (fun p : GlideTrack=> f (axes p.1) (axes p.2) i j) x := by
  let g (z : Momentum×Momentum) := f z.1 z.2 i j
  let L (z : GlideTrack) : Momentum ×Momentum := (axes z.1,axes z.2)
  have hl : AnalyticAt ℂ g (L x) := by
    apply formish; let p := axes x.1; let q := axes x.2; change ∀ᶠ z in 𝓝 (p,q), DifferentiableAt ℂ g z
    let S := strip (α:=Axis) σ; have hs : IsOpen S := Work.F07.stripOpen σ
    have hx : p∈S := Work.F07.realStrip _ hv (axes_real _); have hy : q∈S := Work.F07.realStrip _ hv (axes_real _)
    have hz : q+p∈S := Work.F07.realStrip _ hv (by unfold q p; simp)
    have he : (fun z : Momentum×Momentum=> z.2+z.1) ⁻¹' S ∈𝓝 (p,q) := (continuous_snd.add continuous_fst).continuousAt.tendsto (hs.mem_nhds hz)
    filter_upwards [he,(hs.prod hs).mem_nhds (Set.mk_mem_prod hx hy)] with z hz hu; exact h.shape ⟨hu.1,hu.2,hz⟩ i j
  exact ((hl.contDiffAt (n:=ω)).restrict_scalars ℝ |>.comp (f:=L) _ ((axes_maps.comp (f:=Prod.fst) contDiff_fst|>.prodMk (axes_maps.comp contDiff_snd)).contDiffAt)).analyticAt

abbrev chosenAxis (b : Fslot G) := axisEquiv.symm b.1

def herr (b : Fslot G) (p k : Track) := of fun x y : Fslot G => vectorC p k (chosenAxis b) b.2 (chosenAxis x) (chosenAxis y) x.2 y.2
def hurr (b : Fslot G) (p k : Track) := of fun x y : Foot G => ghostC p k (chosenAxis b) b.2 x.2 y.2
lemma herr_pitch (p k : Track) (i j a : Axis) (x y z : G.ColorIndex) : herr (coord a,z) p k (coord i,x) (coord j,y)=vectorC p k a z i j x y := by
  have he a : chosenAxis (G:=G) (coord a,z)=a := axisEquiv.symm_apply_apply _
  unfold chosenAxis at *
  unfold herr chosenAxis; simp only [Matrix.of_apply,he]
lemma hurr_pitch (p k : Track) (i) (x y z : G.ColorIndex) : hurr (coord i,z) p k (vac,x) (vac,y)= ghostC p k i z x y := by unfold hurr chosenAxis; simp only [Matrix.of_apply,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _]
lemma taxi_cont (i : Axis) : ContDiff ℝ ω (fun p : Track=>tachy p i) := (Complex.I • (Complex.ofRealCLM ∘L (ContinuousLinearMap.proj (φ:=fun _ : Axis=>ℝ) i)) : Track→L[ℝ] ℂ).contDiff
lemma herr_cont (b : Fslot G) (i j) : ContDiff ℝ ω (fun x : GlideTrack=>herr b x.1 x.2 i j) := by
  unfold herr vectorC ghostC; simp only [Matrix.of_apply]
  have he (a : Axis) := taxi_cont a; fun_prop
lemma hurr_cont (b : Fslot G) (i j) : ContDiff ℝ ω (fun x : GlideTrack=>hurr b x.1 x.2 i j) := by
  have he i := taxi_cont i; unfold hurr ghostC; simp only [Matrix.of_apply]; fun_prop
lemma colorSc (t : ℝ) (i j a : Axis) (x y z : G.ColorIndex) (p k : Track) : vectorC (t • p) (t • k) a z i j x y= (t:ℂ)*vectorC p k a z i j x y := by unfold vectorC ghostC tachy; simp; ring
lemma howlin (h : V.grey) (hx : V.fees σ C) (hs : 0<σ) (b i j : Fslot G) : Rays 2 (fun p : GlideTrack=> (granary G V.cast).spot b (axes p.1) (axes p.2) i j- herr b p.1 p.2 i j) := by
  let hV := hx.live.plus (matina_green.pay matina_green.rear); refine twin_shear ((Barter.windowR ((hV : Play (granary G V.cast) σ).spot b) hs 0 i j).sub ((herr_cont b i j).contDiffAt.analyticAt)) (fun x=> ?_)
  rcases i with ⟨i,u⟩; rcases j with ⟨j,v⟩; rcases b with ⟨b,w⟩; obtain ⟨a,rfl⟩ := axisEquiv.surjective b; obtain ⟨i',rfl⟩ := axisEquiv.surjective i; obtain ⟨j',rfl⟩ := axisEquiv.surjective j
  have ht := (vectorPing h hx hs i' j' a u v w x.1 x.2).sub_const (vectorC x.1 x.2 a w i' j' u v)
  rw [sub_self] at ht; refine ht.congr' ?_; filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay,t≠0)] with t hu
  simp only [coord_map, Prod.smul_fst,Prod.smul_snd,mul_sub,herr_pitch,colorSc]
  change t≠0 at hu; field_simp [hu]
lemma screamer (h : 0<σ) (b : Fslot G) (i j : Foot G) : Rays 2 (fun p : GlideTrack=> (quarry G).spot b (axes p.1) (axes p.2) i j - hurr b p.1 p.2 i j) := by
  refine twin_shear ((Barter.windowR (quarry_p.spot b) h 0 i j).sub ((hurr_cont b i j).contDiffAt.analyticAt)) (fun x=> ?_)
  rcases b with ⟨b,w⟩; rcases i with ⟨i,v⟩; rcases j with ⟨j,u⟩
  obtain ⟨a,rfl⟩ := axisEquiv.surjective b; rw [vac_only i,vac_only j];
  have ht : Tendsto _ _ (𝓝 (ghostC x.1 x.2 a w v u)) := ghostPing a w v u x.1 x.2
  have hv := ht.sub_const (ghostC x.1 x.2 a w v u); rw [sub_self] at hv; refine hv.congr' ?_; filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay,t≠0)] with t hu
  simp only [coord_map, Prod.smul_fst,Prod.smul_snd,mul_sub,hurr_pitch]
  have hg : ghostC (t • x.1) (t • x.2) a w v u=(t:ℂ)*ghostC x.1 x.2 a w v u := by unfold ghostC tachy; simp; ring
  change t≠0 at hu; rw [hg]; unfold ghostC; field_simp [hu]
lemma jarBurst (h : U.soft 3) (b i j : Fslot G) : Rays 2 (fun p : GlideTrack=> U.cast.spot b (axes p.1) (axes p.2) i j) := by
  let L := duoTop 1 (![b]) i j
  let y p k : Space 2 := caftan (t:=2) (wineShift (![p]: Fin 1→_) k)
  let f z : Keys 2→ℝ := fun l=> ((y (axes (Prod.fst (z:GlideTrack))) (axes z.2)) l).re
  have he z t : y (axes ((t:ℝ) • (z:GlideTrack).1)) (axes (t • z.2))=axes (t • f z) := by
    ext1 ⟨i,l⟩; fin_cases i <;> simp [y,f,caftan,wineShift,duoTop,axes,L]; ring_nf
  intro x; change (fun t:ℝ => U.prim _ _ (y (axes (t • x.1)) (axes (t • x.2))))=O[cutRay] _
  simp_rw [he]; exact h.2.1 (Prod.snd ∘ L) (Prod.fst ∘ L) (f x)
lemma inflamed (h : U.soft 3) (hp : V.grey) (hv : V.fees σ C) (hs : 0<σ) (b i j : Fslot G) : Rays 2 (fun p : GlideTrack => (granary G (U.combine V|>.cast)).spot b (axes p.1) (axes p.2) i j - herr b p.1 p.2 i j) := by
  let q z := U.cast.spot b (axes (Prod.fst (z:GlideTrack))) (axes z.2) i j
  let p (z : GlideTrack) := (granary G V.cast).spot b (axes z.1) (axes z.2) i j
  have he z : (granary G (U.combine V|>.cast)).spot b (axes z.1) (axes z.2) i j=q z+p z := by change q z+V.cast.spot b _ _ i j+ ((matina G).pay (matina G).rear).spot b _ _ i j=_; rw [add_assoc]; rfl
  simp_rw [he,add_sub_assoc]; exact (jarBurst h b i j).add (howlin hp hv hs b i j)
end YM.Stationary
end
