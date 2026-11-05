import YM.Next.STATIONARY.Shape.LocalOracle


set_option autoImplicit false
/-! Componentwise jets in logarithmic phase. Faa di Bruno works even
though the path functions are real smooth; `beat` being used pointwise at
a given background introduces *no* hypothesis on a complexified path.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ}

def listen (f : RecordM ℂ (Fin n) α) : ContinuousMultilinearMap ℂ (fun _ : Fin n => Phase α) ℂ where
    __ := f
    cont := by
      rw [show f=recording fun i => f (fun k => Pi.single (i k) 1) from MultilinearMap.ext fun v => (expand_coord ..).symm]
      change Continuous fun v => recording _ v
      simp_rw [recording_apply]; fun_prop

def cluster (f : Corn α → Corn β) (x : Corn α) (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => Phase α) (Phase β) :=
    ContinuousMultilinearMap.pi (fun i => listen (beat (fun a => f a i) x n))
omit [Fintype β] [DecidableEq β] in
lemma band_line (f : Corn α → Corn β) (x : Corn α) (n : ℕ) (b i) : cluster f x n b i=beat (fun a => f a i) x n b := rfl
lemma line_real (f : Corn α → Corn β) (x : Corn α) (n : ℕ) (h : AnalyticAt ℝ f x) (v) : cluster f x n (axes ∘ v)=axes (iteratedFDeriv ℝ n f x v) := by
  ext1 i; rw [band_line,beat_real]
  unfold axes; apply congr_arg; exact DFunLike.congr_fun ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : β => ℝ) i).iteratedFDeriv_comp_left (h.contDiffAt (n:=ω)) le_top) v


lemma roll_compose (f : Corn α → Corn β) (g : Corn β → ℝ) (x : Corn α) (hf : AnalyticAt ℝ f x)
    (hg : AnalyticAt ℝ g (f x)) (n : ℕ) :
    beat (g ∘ f) x n = ∑ c : OrderedFinpartition n,
      (c.compAlongOrderedFinpartition (listen (beat g (f x) c.length)) (fun i => cluster f x (c.partSize i))).toMultilinearMap := by
  apply enlarge_unique; intro v
  rw [_root_.sum_apply,beat_real, iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt (show (↑n : WithTop ℕ∞)≤ω from le_top),FormalMultilinearSeries.taylorComp,_root_.sum_apply,Complex.ofReal_sum]
  apply sum_congr rfl; intro c _
  simp only [ContinuousMultilinearMap.coe_coe, OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  rw [show (fun i : Fin c.length => cluster f x (c.partSize i) ((axes ∘ v) ∘ c.emb i))=axes ∘ (fun i => (iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i))) from funext fun i => line_real f x _ hf _]; exact (beat_real _ _).symm
lemma chain_eval (f : Corn α → Corn β) (g : Corn β → ℝ) (x : Corn α) (hf : AnalyticAt ℝ f x)
    (hg : AnalyticAt ℝ g (f x)) (n : ℕ) (v : Fin n → Phase α) :
    beat (g ∘ f) x n v = ∑ c : OrderedFinpartition n, beat g (f x) c.length (fun i => cluster f x (c.partSize i) (v ∘ c.emb i)) := by rw [roll_compose f g x hf hg,_root_.sum_apply]; rfl

lemma evaluated {L : Corn α →L[ℝ] Corn β} (T : Phase α →ₗ[ℂ] Phase β) (hq : ∀ a, axes (L a)=T (axes a))
    {f : Corn β→ℝ} (hf : AnalyticAt ℝ f 0) (n : ℕ) : beat (f ∘ L) 0 n=(beat f 0 n).compLinearMap (fun _ => T) := by
  apply enlarge_unique; intro v
  rw [beat_real,MultilinearMap.compLinearMap_apply,
    show (fun i => T ((axes ∘ v) i))=axes ∘ (fun i => L (v i)) from funext fun i => (hq _).symm,
    beat_real,wired L (by rw [map_zero]; exact hf), map_zero]; rfl
end YM.Stationary
end

/-!
# Local Fourier reading & collected contractions. Multi-insertions.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {G : Gauge} {n t : ℕ} {m : Side} {σ A : ℝ}

lemma cell_hom {ι : Type} [Fintype ι] (p : ι → Site m) (x : Site m) :
    ∏ i, cell (p i) x=cell (∑ i,p i) x := by
  classical
  suffices hv : ∀ s : Finset ι, (∏ j ∈ s, cell (p j) x) = cell (∑ i ∈ s, p i) x from hv univ
  intro s; induction s using Finset.induction with
  | empty => simp [cell_duality _ x]
  | insert i s hs ih => rw [prod_insert hs, sum_insert hs, ih, cell_duality (_+_),cell_add,cell_duality x,cell_duality x]

-- keep independent phases in Reading. Sum over some of them to get next phase.
lemma collide {ι : Type} [Fintype ι] (p : ι → Site m) (q : ι → Momentum) (he : ∀ i, rolls (mon (p i)) (q i)) :
    rolls (mon (∑ i,p i)) (∑ i,q i) := by
  apply rolls_of_mode; intro x
  rw [← cell_wrap,← cell_hom]
  classical
  suffices hv : ∀ s : Finset ι, (∏ j ∈ s, cell (p j) (wrap m x))=mode (∑ i∈s, q i) x from hv univ
  intro s; induction s using Finset.induction with
  | empty => simp
  | insert i s hs ih => rw [prod_insert hs,sum_insert hs,ih,mode_phase,cell_wrap,(he i).exp]

section band
-- complex coefficients at arbitrary amplitudes, derivative version

def recordField (L : Picture G t) (p : Space t) (v : Fin (t+1) → Phase (Loc G 1)) :=
    ∑ i : Fin (t+1) → Loc G 1, (∏ j,v j (i j)) * L (fun j => (i j).2) (fun j => (i j).1) p

lemma note_eq_tone {L : Picture G t} {F : Link G m → ℝ} (he : ∀ i j,Firm σ A (L i j)) (h : Recorded L F 0)
    (p : Fin (t+1) → Site m) (r : Fin (t+1) → Momentum) (hp : ∑ i,p i=0) (hu : ∀ i,rolls (mon (p i)) (r i))
    (v : Fin (t+1)→Phase (Loc G 1)) :
    noteAt F (t+1) (fun i => tune (p i) (v i))=(cents m:ℂ)*recordField L (fun j => r j.1.succ j.2) v := by
  let T i (j : Loc G 1) := v i j • relay (p i) j
  rw [show (fun i => tune (p i) (v i))=(fun i => ∑ j,T i j) by
    funext i x
    rw [Finset.sum_apply]; simp [T,tune,relay,Pi.single_apply,mul_comm]
  ]
  rw [MultilinearMap.map_sum]; unfold recordField; rw [mul_sum]
  apply sum_congr rfl; intro i _
  rw [show noteAt F _ _ = _ from (noteAt F (t+1)).map_smul_univ (fun j => v j (i j)) (fun j => relay _ _)]
  let x j := (i j).2; let a j := (i j).1
  change _ * noteAt F _ (glyph p x a)=_
  rw [(record_exact F L).1 h,collected,if_pos hp]
  have hy : rolls (outphase p) (fun j => r j.1.succ j.2) := rolls_keys fun j => hu j.succ
  rw [hy.apply (he x a) ((he x a).in_range (out_real p))]; simp only [cents]; push_cast; exact mul_left_comm ..
lemma beat_as_cost (F : Corn α→ℝ) (n : ℕ) : beat F 0 n=(n.factorial:ℂ) • noteAt F n := by
  unfold noteAt; rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n),one_smul]
lemma beat_recorded {L : Picture G t} {F : Link G m → ℝ} (he : ∀ i j,Firm σ A (L i j)) (h : Recorded L F 0)
    (p : Fin (t+1) → Site m) (r : Fin (t+1) → Momentum) (hp : ∑ i,p i=0) (hu : ∀ i,rolls (mon (p i)) (r i))
    (v : Fin (t+1)→Phase (Loc G 1)) :
    beat F 0 (t+1) (fun i => tune (p i) (v i))=(cents m:ℂ)*(((t+1).factorial:ℂ)*recordField L (fun j => r j.1.succ j.2) v) := by
  rw [beat_as_cost F,_root_.smul_apply,note_eq_tone he h _ _ hp hu]; simp [mul_left_comm]
end band

-- local pointwise reading of any convolution with finitely-many requested shifts
section convolution
variable (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : β → Corn ι → ℝ) (p : β → ι → α) (s : β → ι → Cover)

def consult (R : Type) [CommRing R] (x : Co m β) : (Co m α → R) →ₗ[R] (ι → R) :=
    LinearMap.pi fun i => LinearMap.proj (wrap m (s x.2 i)+x.1,p x.2 i)

def bulletin (n : ℕ) (q : Fin n → Momentum) (v : Fin n → Phase α) (b : β) : ℂ :=
    beat (f b) 0 n (fun j i => mode (q j) (s b i)*v j (p b i))

lemma summons (F : Corn (Co m α) → Corn (Co m β))
    (h : ∀ i : Co m β,(fun x => F x i)= f i.2 ∘ (consult ι p s ℝ i))
    (hy : ∀ i, AnalyticAt ℝ (f i) 0) (b : Fin n → Site m) (q : Fin n → Momentum)
    (hQ : ∀ i, rolls (mon (b i)) (q i)) (v : Fin n → Phase α) :
    cluster F 0 n (fun i => tune (b i) (v i))=tune (∑ i,b i) (bulletin ι f p s n q v) := by
  ext1 x; rw [band_line, h]
  let L := (consult ι p s ℝ x).toContinuousLinearMap
  have hu a : axes (L a) = consult ι p s ℂ x (axes a) := rfl
  change beat (_ ∘ L) _ _ _= _
  rw [evaluated _ hu (hy _) _,MultilinearMap.compLinearMap_apply,
    show (fun i : Fin n => consult _ _ _ _ x (tune (b i) (v i)))=fun i => cell (b i) x.1 • (fun j => mode (q i) (s x.2 j)*v i (p x.2 j)) by
      funext i j; simp [tune,consult,cell_wrap, (hQ i).exp]; ring]
  rw [MultilinearMap.map_smul_univ,cell_hom]; rfl

lemma bulletin_cont : Continuous (fun P : (Fin n → Momentum) × (Fin n→Phase α) => bulletin ι f p s n P.1 P.2) := by
  apply continuous_pi; intro b
  let L := listen (beat (f b) 0 n)
  refine L.cont.comp (f:=fun P : (Fin n → Momentum) × (Fin n → Phase α) => fun j i => mode (P.1 j) (s b i) * P.2 j (p b i)) ?_
  exact continuous_pi fun i => continuous_pi fun j => by unfold Laurent.mode; fun_prop
end convolution
end YM.Stationary
end

/-! Uniform stencil for the analytic infinitesimal Ward test.
No volume limits of nonlinear gauge functions. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side}

abbrev Candles (G : Gauge) := Loc G 0 ⊕ Loc G 1

def restMap (R : Type) [CommRing R] : (Co m (Candles G) → R) →ₗ[R] (Lines G m 1→R) := LinearMap.pi fun i => LinearMap.proj (i.1,Sum.inr i.2)
def siteMap (R : Type) [CommRing R] : (Co m (Candles G) → R) →ₗ[R] (Lines G m 0→R) := LinearMap.pi fun i => LinearMap.proj (i.1,Sum.inl i.2)
def bundleSites : Corn (Co m (Candles G)) →L[ℝ] Swatch G m := (LinearMap.toContinuousLinearMap (siteMap ℝ)).prod (LinearMap.toContinuousLinearMap (restMap ℝ))
def bundleLink : Corn (Co m (Candles G)) →L[ℝ] Link G m := (restMap ℝ).toContinuousLinearMap

def dragged (G : Gauge) (m : Side) : Corn (Co m (Candles G)) → Link G m := moveField ∘ bundleSites
lemma dragged_analytic : AnalyticAt ℝ (dragged G m) 0 := by
  unfold dragged; refine AnalyticAt.comp ?_ (ContinuousLinearMap.analyticAt _ _)
  rw [map_zero]; exact moveField_analytic
@[simp] lemma dragged_zero : dragged G m 0=0 := by simp [dragged]

section arrangement
abbrev MapSpec (G : Gauge) := Fin 3 × G.ColorIndex
private def Lx (i : Fin 3) : Corn (MapSpec G) →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
    toFun p := WithLp.toLp 2 fun j => p (i,j)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
private def wax (i : Loc G 1) (p : Corn (MapSpec G)) : ℝ :=
    G.plog (G.mat (G.lieExp (Lx 0 p) * G.lieExp (Lx 1 p) * (G.lieExp (Lx 2 p))⁻¹)) i.2
private def unitRead (i : Loc G 1) (p : MapSpec G) : Candles G := if p.1=1 then Sum.inr (i.1,p.2) else Sum.inl (vac,p.2)
private def unitOff (i : Loc G 1) (p : MapSpec G) : Cover := if p.1=2 then step (axisEquiv.symm i.1) else 0
private lemma waxed (i : Co m (Loc G 1)) : (fun x => dragged G m x i)= wax i.2 ∘ consult (MapSpec G) unitRead unitOff ℝ i := by
  funext x; rcases i with ⟨k,a,j⟩
  obtain ⟨i,rfl⟩ := axisEquiv.surjective a; rw [coord_map,← arm_apply G m 1 (dragged G m x) k (coord i) j]
  simp only [dragged, Function.comp_apply]; rw [moveField,content_at]
  unfold wax
  simp only [shiftLinks,Lattice.gauge,encode_link,switchSite]
  let T := consult (MapSpec G) unitRead unitOff ℝ (k,coord i,j) x
  have h1 : arm G m 0 (bundleSites x).1 (k,vac)=Lx 0 T := by ext; simp [T,bundleSites,Lx,unitOff,unitRead,consult,arm_apply]; rfl
  have h2 : arm G m 1 (bundleSites x).2 (k,coord i)=Lx 1 T := by ext; simp [T,bundleSites,Lx,unitOff,unitRead,consult,arm_apply]; rfl
  have h3 : arm G m 0 (bundleSites x).1 (k+step i,vac)=Lx 2 T := by ext; simp [T,bundleSites,Lx,unitOff,unitRead,consult,arm_apply,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _,add_comm (step i)]; rfl
  rw [h1,h2,h3]
private lemma wax_analytic (i : Loc G 1) : AnalyticAt ℝ (wax i) 0 := by
  let K (b : Corn (MapSpec G)) := G.mat (G.lieExp (Lx 0 b) * G.lieExp (Lx 1 b) * (G.lieExp (Lx 2 b))⁻¹)
  have hK : ContDiffAt ℝ ω K 0 := by
    unfold K; simp only [G.mat_mul,G.mat_inv]
    have hk (i : Fin 3) : ContDiffAt ℝ ω (fun b : Corn (MapSpec G) => G.mat (G.lieExp (Lx i b))) 0 := (G.exp_jet.comp (Lx i).contDiff).contDiffAt
    exact ((hk _).mul (hk _)).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hk _))
  have h : ContDiffAt ℝ ω (G.plog ∘ K) 0 := ContDiffAt.comp _ (by simp only [K,map_zero,G.mat_lieExp_zero,mul_one, inv_one, G.mat_one]; exact G.plog_diff) hK
  exact (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i.2).analyticAt _ |>.comp h.analyticAt

def message := bulletin (α:=Candles G) (β:=Loc G 1) (MapSpec G) wax unitRead unitOff
lemma message_cont (n : ℕ) : Continuous (fun z : (Fin n → Momentum) × (Fin n → Phase (Candles G)) => message n z.1 z.2) := bulletin_cont ..
lemma gauge_message (n : ℕ) (p : Fin n → Site m) (q : Fin n → Momentum) (he : ∀ i, rolls (mon (p i)) (q i)) (v : Fin n→Phase (Candles G)) :
    cluster (dragged G m) 0 n (fun i => tune (p i) (v i))=tune (∑ i,p i) (message n q v) :=
    summons _ _ _ _ (dragged G m) waxed wax_analytic p q he v
end arrangement

lemma interpolate (u : Corn (Co m (Candles G))) :
    fderiv ℝ (dragged G m) 0 u=restMap ℝ u - gradientA G m (siteMap ℝ u) := by
  unfold dragged
  rw [fderiv_comp _ (by rw [map_zero]; exact moveField_analytic.differentiableAt) (bundleSites (G:=G) (m:=m)).differentiableAt,
    map_zero,ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply, moveField_rate]
  rfl
lemma dragged_one (b : Fin 1 → Phase (Co m (Candles G))) :
    cluster (dragged G m) 0 1 b= restMap ℂ (b 0)-gradientA G m (siteMap ℂ (b 0)) := by
  let L := fderiv ℝ (dragged G m) 0
  let T := restMap ℂ-gradientA G m∘ₗ(siteMap (G:=G) (m:=m) ℂ)
  have he x : T (axes x) = axes (L x) := by
    unfold L T
    rw [interpolate]; funext i
    simp [axes,gradientA,restMap,siteMap]
  ext1 i
  suffices hh : beat (fun x => dragged G m x i) 0 1 = ((ContinuousMultilinearMap.mkPiRing ℂ (Fin 1) (1:ℂ)).toMultilinearMap.compLinearMap fun _ => LinearMap.proj i ∘ₗ T) by
    rw [band_line,hh]; simp [T]
  apply enlarge_unique; intro v
  rw [← band_line (dragged G m),line_real (dragged G m) 0 1 dragged_analytic v, MultilinearMap.compLinearMap_apply,
    iteratedFDeriv_one_apply]; simp only [ContinuousMultilinearMap.coe_coe,ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_univ_one,Function.comp_apply,LinearMap.comp_apply,he]; simp; rfl
end YM.Stationary
end

/-!
# Momentum-order consequence of nonlinear Ward

After one slot made a gradient, all terms of lesser arity really evaluate
at routed external momenta tending linearly to zero. This gives a vanishing
order on the contracted leg of the new field kernel. Use cofinal mesh data
first, then rays. All coefficient powers can be qualitative in this file.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ}

section spark
variable (v : Ink G (t+1)) (a : Run (t+1)) (j : Fin (t+1))
def litPoint (i : Fin (t+1)) : Phase (Candles G) := if i=j then Pi.single (Sum.inl (vac,v i)) 1 else Pi.single (Sum.inr (a i,v i)) 1
def lampFare {m : Side} (p : Fin (t+1) → Site m) (i) := tune (p i) (litPoint v a j i)

def rmsg (b : OrderedFinpartition (t+1)) (q : Space t) (w : Fin b.length) := message (b.partSize w) (plotted q ∘ b.emb w) (litPoint v a j ∘ b.emb w)

def tally (b : OrderedFinpartition (t+1)) {R : Type} [AddCommMonoid R] (f : Fin (t+1)→R) (i : Fin b.length) := ∑ k, f (b.emb i k)

def element {m : Side} (p : Fin (t+1) → Site m) (c : OrderedFinpartition (t+1)) (F : Link G m→ℝ) :=
    beat F 0 c.length (fun i => cluster (dragged G m) 0 (c.partSize i) (lampFare v a j p ∘ c.emb i))

lemma flare_area {m : Side} (p : Fin (t+1) → Site m) (H : ∑ i,p i=0) (r : Corn (Keys t))
    (R : rolls (outphase p) (axes r)) (b : OrderedFinpartition (t+1)) (i) :
    let q := tally b (plotted (axes r))
    let g := tally b p
    rolls (mon (g i)) (q i) ∧
    cluster (dragged G m) 0 (b.partSize i) (lampFare v a j p ∘ b.emb i) = tune (g i) (rmsg v a j b (axes r) i) := by
  have he (i : Fin (t+1)) := ((ties H i).symm.trans (projections_roll R i))
  exact ⟨collide (p ∘ b.emb i) (plotted (axes r) ∘ b.emb i) (fun j => he (b.emb i j)), gauge_message _ _ _ (fun j => he (b.emb i j)) (litPoint v a j ∘ b.emb i)⟩

lemma pop_lit {m : Side} (p : Fin (t+1) → Site m) : restMap ℂ (lampFare v a j p j)=0 := by
  ext1 ⟨i,x⟩; simp [restMap, lampFare,tune,litPoint]

lemma tested_area {m : Side} (F : Link G m → ℝ) (hf : AnalyticAt ℝ F 0) (h : force F) (p : Fin (t+1) → Site m) :
    ∑ b : OrderedFinpartition (t+1), element v a j p b F=0 := by
  have H : F ∘ (dragged G m) =ᶠ[𝓝 0] F ∘ bundleLink := by
    have hh : Tendsto bundleSites (𝓝 (0:Corn (Co m (Candles G)))) (𝓝 0) := by simpa using (bundleSites (G:=G) (m:=m)).continuous.tendsto 0
    exact hh.eventually h
  rw [show (∑ b : OrderedFinpartition (t+1), element v a j p b F)=
      beat (F ∘ (dragged G m)) 0 (t+1) (lampFare v a j p) by rw [chain_eval (dragged G m) F _ dragged_analytic (by rw [dragged_zero]; exact hf),dragged_zero]; rfl,
    show beat (F ∘ (dragged G m)) 0 (t+1)=beat (F ∘ bundleLink) 0 (t+1) from congr_arg _ ?_]
  · rw [evaluated (restMap ℂ) (fun _ => rfl) hf,MultilinearMap.compLinearMap_apply]; exact MultilinearMap.map_coord_zero _ j (pop_lit v a j p)
  rw [(H.iteratedFDeriv ℝ  (t+1)).eq_of_nhds]

-- on shell: first order is a gauge tangent
def crux (K : Picture G t) (p : Space t) : ℂ := ∑ i : TypeFace 1, symbol 0 (plotted p j) i vac * K v (update a j i) p

lemma elem_top {m : Side} (F : Link G m → ℝ) (p : Fin (t+1) → Site m) (hp : ∑ i,p i=0)
    (K : Picture G t) {σ A : ℝ} (hf : ∀ i j, Firm σ A (K i j)) (hh : Recorded K F 0)
    (r : Corn (Keys t)) (h : rolls (outphase p) (axes r)) : element v a j p (OrderedFinpartition.atomic _) F=
      -(cents m:ℂ) * (t+1).factorial * crux v a j K (axes r) := by
  have he : (fun i => restMap ℂ (lampFare v a j p i)-gradientA G m (siteMap ℂ (lampFare v a j p i)))=update (glyph p v a) j (-(gradientA G m (relay (p j) (vac,v j)))) := by
    ext1 i
    by_cases H : i=j
    · subst i; rw [pop_lit,update_self]; suffices siteMap ℂ _ = relay (p j) (vac,v j) by rw [this]; simp
      ext1 x; simp [siteMap,lampFare,tune,relay,litPoint,Pi.single_apply]
    rw [update_of_ne H]; have hY : siteMap ℂ (lampFare v a j p i)=0 := by ext1 x; simp [siteMap,lampFare,tune,litPoint,H]
    rw [hY,map_zero,sub_zero]; ext1 x; simp [restMap,glyph,relay,lampFare,tune,litPoint,H,Pi.single_apply]
  unfold element
  change beat F 0 (t+1) (fun i => cluster (dragged G m) 0 1 (fun _ => lampFare v a j p i))=_
  simp_rw [dragged_one]; rw [he,beat_as_cost F, _root_.smul_apply, gradient_wave,MultilinearMap.map_update_neg, MultilinearMap.map_update_sum]
  have hu (x : TypeFace 1) : noteAt F _ (update (glyph p v a) j (symbol 0 (mon (p j)) x vac • relay (p j) (x,v j)))=
        (cents m:ℂ)*(symbol 0 (plotted (axes r) j) x vac*K v (update a j x) (axes r)) := by
    rw [MultilinearMap.map_update_smul]
    rw [show update (glyph p v a) j (relay (p j) (x,v j)) = glyph p v (update a j x) by funext i; by_cases he : i=j <;> simp [*,glyph]]
    rw [(record_exact ..).1 hh,collected,if_pos hp, h.apply (hf v (update a j x)) ((hf v (update a j x)).in_range (out_real p)), rolls_symbol ((ties hp j).symm.trans (projections_roll h j))]
    simp [cents,mul_left_comm]
  simp_rw [hu]; rw [← Finset.mul_sum,smul_eq_mul]; unfold crux; ring
end spark
end YM.Stationary
end

/-! # Leading Ward law with *different* Hessians

Degree-losing sharply enough for the ancestral paths. (No price claims
from these power comparisons.) -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ}

lemma roots_q (p : Corn (Keys t)) (i : Fin (t+1)) : ∃ x : Corn Axis, axes x=plotted (axes p) i ∧
    ∀ b : ℝ, plotted (axes (b • p)) i=axes (b • x) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine ⟨missing p,?_,fun b => ?_⟩
    · rw [plotted, Fin.cons_zero, miss_phase]
    rw [plotted,Fin.cons_zero,miss_phase]; ext1 j; simp [missing,axes,Finset.sum_apply,Finset.mul_sum]
  exact ⟨_,rfl,fun _ => by rw [plotted,Fin.cons_succ]; rfl⟩

private lemma line_grows {x : Type} [Fintype x] (M : x→Corn (Keys t)→ℂ) (u : x→ Corn (Keys t)→ℂ) (s : ℕ)
    (he : ∀ i, Continuous (M i)) (h : ∀ i, Rays s (u i)) :
    Rays s (fun p => ∑ i,M i p*u i p) := by
  intro p
  refine Asymptotics.IsBigO.sum fun i _ => ?_
  have hh := ((he i).continuousAt.tendsto.comp (along p)).isBigO_one ℝ
  simpa using (hh.mul (h i p))

variable (v : Ink G (t+1)) (a : Run (t+1)) (j : Fin (t+1)) {m : ℕ → Side}
    {F : ∀ i, Link G (m i) → ℝ}

def priceEl (s : ℕ) (m : ℕ → Side) (F : ∀ i, Link G (m i) → ℝ) (c : OrderedFinpartition (t+1)) := ∃ g : Corn (Keys t) → ℂ,
    Continuous g ∧ Rays s g ∧ ∀ i p (r : Corn (Keys t)), (∑ k,p k)=0 → rolls (outphase p) (axes r) →
      element v a j p c (F i) = (cents (m i):ℂ)*g r

def LawfulSum (s : ℕ) (m : ℕ → Side) (F : ∀ i, Link G (m i) → ℝ) (n : ℕ) := ∃ L : Picture G n,
    (∃ σ A, ∀ i k,Firm σ A (L i k)) ∧ (∀ i, Recorded L (F i) 0) ∧ ∀ i j, Rays s (L i j ∘ axes)

-- Each higher-order product input routed at q. Make length explicit to
-- transport from the partition. Works for any partition of those inputs.
lemma priced_below {s : ℕ} (c : OrderedFinpartition (t+1)) (he : c.length=n+1) (L : LawfulSum s m F n) :
    priceEl v a j s m F c := by
  obtain ⟨K,⟨σ,A,hk⟩,ht,hs⟩ := L
  rcases c with ⟨l,d,hd,e,h1,h2,h3,h4⟩
  dsimp only at he; subst l
  let C : OrderedFinpartition (t+1) := ⟨_,_,hd,e,h1,h2,h3,h4⟩
  let u (p : Corn (Keys t)) : Fin (n+1)→Momentum := tally C (plotted (axes p))
  let M (p : Corn (Keys t)) : Fin (n+1) → Phase (Loc G 1) := rmsg v a j C (axes p)
  let q (p : Corn (Keys t)) : Space n := fun i => u p i.1.succ i.2
  let g (p : Corn (Keys t)) := ((n+1).factorial:ℂ)*recordField K (q p) (M p)
  have hv i : Continuous (fun p => M p i) := by
    refine (message_cont (G:=G) (C.partSize i)).comp (f:=fun y => (plotted (axes y) ∘ C.emb i, litPoint v a j ∘ C.emb i)) ?_
    exact Continuous.prodMk (continuous_pi fun z => ((platform_diffs _).continuous.comp axes_maps.continuous)) continuous_const
  have hq : Continuous q := by
    refine continuous_pi fun i => ?_
    unfold q u tally; simp only [Finset.sum_apply]; apply continuous_finsetSum; intro a _
    exact (continuous_apply _).comp ((platform_diffs _).continuous.comp axes_maps.continuous)
  have H (i : Fin (n+1)→Loc G 1) (p) : ContinuousAt (fun v => K (fun k => (i k).2) (fun k => (i k).1) (q v)) p := by
    let z := hk (fun k => (i k).2) (fun k => (i k).1)
    have he : star (q p)=q p := by
      ext1 ⟨i,x⟩; unfold q u tally
      simp only [Pi.star_apply,Finset.sum_apply, star_sum]; apply sum_congr rfl; intro u _
      exact congr_fun (real_plot p _) _
    exact (z.analytic (z.in_range he)).continuousAt.comp hq.continuousAt
  have HM (i : Fin (n+1)→Loc G 1) : Continuous (fun x => ∏ b, M x b (i b)) := continuous_finsetProd _ fun j _ => (continuous_apply _).comp (hv j)
  refine ⟨g,continuous_const.mul (continuous_finsetSum _ fun i _ => (HM i).mul (continuous_iff_continuousAt.mpr (H i))),?_,?_⟩
  · have he (i : Ink G (n+1)) (j) : Rays s (fun x => K i j (q x)) := by
      intro p; choose x H hx using roots_q p
      let r : Corn (Keys n) := fun i => ∑ k, x (C.emb i.1.succ k) i.2
      apply (hs i j r).congr_left; intro b
      change K i j _=K i j _; apply congr_arg; ext1 i; simp only [axes,q,r,u,tally,hx, Pi.smul_apply,Finset.sum_apply]
      push_cast; simp [Finset.mul_sum]
    intro p
    exact (line_grows _ _ s HM (fun i => he (fun k => (i k).2) (fun k => (i k).1)) p).const_mul_left ((n+1).factorial:ℂ)
  intro i p r hp h
  have hϕ := flare_area v a j p hp r h C
  let w : Fin (n+1)→ Site (m i) := tally C p
  have hi (x) : cluster (dragged G (m i)) 0 (C.partSize x) (lampFare v a j p ∘ C.emb x) = tune (w x) (M r x) := (hϕ x).2
  change beat (F i) 0 (n+1) (fun k => cluster (dragged G (m i)) 0 (C.partSize k) _)=_
  rw [show (fun k : Fin (n+1) => _)=(fun i => tune (w i) (M r i)) from funext hi]; exact beat_recorded hk (ht i) w _ ((C.sum_sigma_eq_sum p).trans hp) (fun x => (hϕ x).1) (M r)

lemma full_ring {s : ℕ} (hm : Tendsto (fun i => (m i).val) atTop atTop) {σ A : ℝ} (K : Picture G t) (hf : ∀ i j,Firm σ A (K i j)) (H : ∀ i, Recorded K (F i) 0) (h : ∀ i,AnalyticAt ℝ (F i) 0) (h0 : ∀ i, fderiv ℝ (F i) 0=0) (hp : ∀ b, b<t → 0 < b → LawfulSum s m F b) (hw : ∀ i, force (F i)) :
    Rays s (crux v a j K ∘ axes) := by
  classical
  let b := OrderedFinpartition.atomic (t+1)
  have he (i : OrderedFinpartition (t+1)) : ∃ g : Corn (Keys t) → ℂ, i≠b →
      Continuous g ∧ Rays s g ∧ ∀ u p (r : Corn (Keys t)), (∑ k,p k)=0 → rolls (outphase p) (axes r) → element v a j p i (F u)=(cents (m u):ℂ)*g r := by
    by_cases H : i=b
    · exact ⟨0,fun h => False.elim (h H)⟩
    have hv := i.length_pos (by omega)
    have hs : i.length < t+1 := lt_of_le_of_ne i.length_le (fun he => H (allSingle i he))
    match hu : i.length with
    | 0 => omega
    | 1 =>
      refine ⟨fun _ => 0,fun _ => ⟨continuous_const,fun _ => isBigO_zero ..,fun u p r hg he => ?_⟩⟩
      suffices hx : iteratedFDeriv ℝ i.length (F u) 0=0 by
        unfold element beat; rw [hx, enlarge]; simp [recording_apply]
      rw [hu]; ext1 x; simp [iteratedFDeriv_one_apply,h0]
    | n+2 =>
      obtain ⟨G,h₁,h₂,h₃⟩ := priced_below v a j i (n:=n+1) hu (hp (n+1) (by omega) (by omega))
      exact ⟨G,fun _ => ⟨h₁,h₂,h₃⟩⟩
  choose f he using he
  let W := Finset.univ.erase b
  have hy (r : Corn (Keys t)) : ∑ i∈W,f i r=((t+1).factorial:ℂ)*crux v a j K (axes r) := by
    have hx i (p : Fin (t+1)→ Site (m i)) r (hr : ∑ k,p k=0) (ht : rolls (outphase p) (axes r)) : ∑ l∈W,f l r = ((t+1).factorial:ℂ)*crux v a j K (axes r) := by
      have hE (l) (hl : l∈W) := (he l (Finset.mem_erase.mp hl).1).2.2 i p r hr ht
      have h := (Finset.sum_erase_add _ (element v a j p · (F i)) (mem_univ b)).trans (tested_area v a j (F i) (h i) (hw i) p)
      rw [show ∑ l∈W,element v a j p l (F i)= _ from sum_congr rfl hE,show b= _ from rfl,
        elem_top v a j _ p hr K hf (H i) _ ht, ← Finset.mul_sum] at h
      apply mul_left_cancel₀ (show (cents (m i):ℂ)≠0 from by exact_mod_cast cents_pos.ne'); linear_combination h
    obtain ⟨p,u,H,hU⟩ := fleet m hm (axes r) (axes_real r)
    let x (i : ℕ) : Corn (Keys t) := fun j => (u i j).re
    have Hx i : u i=axes (x i) := (axes_of_real ((hU i).2.metric (out_real _))).symm
    have hh : Tendsto x atTop (𝓝 r) := by
      refine tendsto_pi_nhds.mpr fun i => ?_
      have hz := Complex.continuous_re.continuousAt.tendsto (x:=axes r i) |>.comp (tendsto_pi_nhds.mp H i)
      simpa only [axes, Complex.ofReal_re] using! hz
    have hα : Continuous (fun r : Corn (Keys t) => ((t+1).factorial:ℂ)*crux v a j K (axes r)) := by
      apply continuous_const.mul; unfold crux; apply continuous_finsetSum; intro i _
      refine Continuous.mul ?_ (continuous_iff_continuousAt.mpr (fun x => ((hf v (update a j i)).analytic_real x).continuousAt))
      have he : Continuous (fun p : Momentum => symbol 0 p i vac) := by simp only [symbol, Exterior.q,wedge,Matrix.sum_apply,Matrix.smul_apply]; fun_prop
      exact he.comp ((platform_diffs _).continuous.comp axes_maps.continuous)
    refine tendsto_nhds_unique_of_eventuallyEq (f:=fun u => ∑ l∈W,f l (x u)) ((continuous_finsetSum W
      (fun i hi => (he i (Finset.mem_erase.mp hi).1).1)).continuousAt.tendsto.comp hh)
      (hα.continuousAt.tendsto.comp hh) (Eventually.of_forall fun i => hx i (p i) (x i) (hU i).1 (Hx i ▸ (hU i).2))
  have ht : Rays s (fun r => ∑ l∈W,f l r) := fun p => Asymptotics.IsBigO.sum (fun l hl => (he l (Finset.mem_erase.mp hl).1).2.1 p)
  intro p
  have hn : ((t+1).factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
  refine ((ht p).const_mul_left (((t+1).factorial :ℂ)⁻¹)).congr_left fun x => ?_
  change ((t+1).factorial:ℂ)⁻¹*(∑ l∈W,f l _)=_; rw [hy,inv_mul_cancel_left₀ hn]; rfl
end YM.Stationary
end

/-! Soft Ward: the bound on the first-contracted kernel kills also some
*uncontracted* jets. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ}

lemma sym_one (p : Momentum) (i : Axis) : symbol 0 p (coord i) vac=q p i := by
  unfold symbol wedge
  rw [Matrix.sum_apply,sum_eq_single i]
  · simp [Exterior.left,coord, vac_only,parity,pre, Finset.filter_singleton]
  · intro j _ hj; simp [Exterior.left,coord,hj]
  simp

lemma lift_axis_ray (p : Corn (Keys t)) (j : Fin t) (i : Axis) : Tendsto
    (fun a : ℝ => (↑a:ℂ)⁻¹ * symbol 0 (plotted (axes (a • p)) j.succ) (coord i) vac) cutRay
    (𝓝 (Complex.I * (p (j,i):ℂ))) := by
  let f (a : ℝ) := Complex.exp (Complex.I*(a*(p (j,i)):ℝ))-1
  have hu : HasDerivAt f (Complex.I*(p (j,i):ℂ)) 0 := by
    unfold f; push_cast; have he : HasDerivAt (fun p : ℝ => (p:ℂ)) 1 0 := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    convert! ((he.mul_const (p (j,i):ℂ)).const_mul Complex.I).cexp.sub_const 1 using 1 ; simp
  have hx := hasDerivAt_iff_tendsto_slope_zero.mp hu
  simp_rw [sym_one]; change Tendsto (fun a : ℝ => _*f a) _ _
  simpa [f,Complex.real_smul] using hx

lemma reachInv {p : Corn (Keys t) → ℂ} {s : ℕ} (hp : Rays (s+1) p) (v : Corn (Keys t)) :
    Tendsto (fun x : ℝ => ((x:ℂ)^s)⁻¹ * p (x • v)) cutRay (𝓝 0) := by
  simpa [Complex.real_smul] using scale_limit (f:=fun k => p (k • v)) s 0 (by simpa using hp v)

-- hold every leg but one. elementary Ward test on complex forms
variable (L : Picture G t) (v : Ink G (t+1)) (b : Run (t+1))
    (f : TypeFace 1 → Corn (Keys t) → ℂ) (j : Fin t)

lemma ring_ray {s : ℕ} (h : ∀ a : TypeFace 1, ∀ p : Corn (Keys t),
    Tendsto (fun x : ℝ => ((x:ℂ)^s)⁻¹ * L v (update b j.succ a) (axes (x • p))) cutRay (𝓝 (f a p)))
    (hp : Rays (s+1+1) (crux v b j.succ L ∘ axes)) (p : Corn (Keys t)) :
    ∑ i, (p (j,i):ℂ)*f (coord i) p = 0 := by
  have he := tendsto_finsetSum univ (fun i _ => (lift_axis_ray p j i).mul (h (coord i) p))
  have H := reachInv (s:=s+1) hp p
  have hx (z : ℝ) : ∑ i : Axis, ((z:ℂ)⁻¹*symbol 0 (plotted (axes (z • p)) j.succ) (coord i) vac) *
      (((z:ℂ)^s)⁻¹*L v (update b j.succ (coord i)) (axes (z • p))) =
        ((z:ℂ)^(s+1))⁻¹ * crux v b j.succ L (axes (z • p)) := by
    unfold crux; rw [Finset.mul_sum, ← Equiv.sum_comp axisEquiv]; apply sum_congr rfl; intro i _
    rw [coord_map,pow_succ]; simp only [mul_inv_rev]; ring
  simp_rw [hx] at he
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_zero,Finset.mul_sum]
  exact (sum_congr rfl fun i _ => (mul_assoc ..).symm).trans (tendsto_nhds_unique he H)

variable {K : Picture G t} {m : ℕ→Side} {F : ∀ i, Link G (m i) →ℝ} {σ A : ℝ}

lemma rayDark (ht : 0<t) (h : ∀ i j, Firm σ A (K i j)) (hu : ∀ i a b, Rays 2 (crux i a b K ∘ axes)) :
    Rays 1 (K v b ∘ axes) := by
  obtain ⟨i,hi⟩ := axisEquiv.surjective (b (Fin.succ ⟨0,ht⟩))
  let j : Fin t := ⟨0,ht⟩
  apply (rays_at_zero ((h v b).analytic_real 0)).mpr
  let f k := K v (update b j.succ k)
  have hh k (p : Corn (Keys t)) : Tendsto (fun a : ℝ => f k (axes (a • p))) cutRay (𝓝 (f k (axes 0))) :=
    ((h _ _).analytic_real _).continuousAt.tendsto.comp (along p)
  have he := ring_ray K v b (fun k _ => f k (axes 0)) j (s:=0) (fun a p => by simpa using hh a p) (hu v b j.succ) (Pi.single (j,i) 1)
  simpa [f,Pi.single_apply,apply_ite ((↑):ℝ→ℂ),ite_mul, ← coord_map,show axisEquiv i=b j.succ from hi] using he

lemma rayBlack (ht : 2 ≤ t) (h : ∀ i j,Firm σ A (K i j)) (hu : ∀ i a b, Rays 3 (crux i a b K ∘ axes)) :
    Rays 2 (K v b ∘ axes) := by
  let B (v a) := K v a ∘ axes
  have hm i a := (h i a).analytic_real 0
  have H (a) : Rays 1 (B v a) := rayDark v a (by omega) h (fun x y z => (hu x y z).weaker (by decide))
  have he (j : Fin t) (p : Corn (Keys t)) : ∑ i : Axis,(p (j,i):ℂ) * fderiv ℝ (B v (update b j.succ (coord i))) 0 p=0 := by
    refine ring_ray K v b (fun i p => fderiv ℝ (B v (update b j.succ i)) 0 p) j (s:=1) (fun a p => ?_) (hu v b j.succ) _
    have hv := ray_limit (hm v (update b j.succ a)) (H (update b j.succ a)) p
    simpa [Tensor.diagonal,Tensor.coeff,Complex.real_smul,B,iteratedFDeriv_one_apply] using hv
  -- A first differential killing all rays transverse to any chosen independent leg vanishes.
  have hx (j : Fin t) (p : Corn (Keys t)) (hp : ∀ i : Axis,p (j,i)=0) : fderiv ℝ (B v b) 0 p = 0 := by
    let i := axisEquiv.symm (b j.succ)
    let q : Corn (Keys t) := Pi.single (j,i) (1:ℝ)
    have hj : coord i=b j.succ := axisEquiv.apply_symm_apply _
    have hv : update b j.succ (coord i)=b := hj ▸ update_eq_self ..
    have hz : fderiv ℝ (B v b) 0 q=0 := by simpa [q,Pi.single_apply,apply_ite ((↑):ℝ→ℂ),ite_mul,hv] using he j q
    have hs := he j (q+p)
    simpa [map_add,hp,q,Pi.single_apply,apply_ite ((↑):ℝ→ℂ),ite_mul,hv,hz] using hs
  refine (rays_jet (hm v b) _).mpr fun i hi => ?_
  interval_cases i
  · exact (rays_jet (hm v b) _).1 (H b) _ Nat.zero_lt_one
  ext1 p
  simp only [iteratedFDeriv_one_apply]; change fderiv ℝ _ 0 (p 0)=0
  let j : Fin t := ⟨0,by omega⟩
  let k : Fin t := ⟨1,by omega⟩
  let u : Corn (Keys t) := fun i => if i.1=j then p 0 i else 0
  have hj := hx k u (fun i => if_neg (show k≠j from fun h => by have hv := congr_arg Fin.val h; simp [k,j] at hv))
  have hk := hx j (p 0-u) (fun i => by simp [u]); rw [map_sub,hj,sub_zero] at hk; exact hk
end YM.Stationary
end

/-! # Harmonic mark in a changing base

Exact complexified Hessian symbol cost at given linear-data widths; reads
also p=0. `slots` tensors include both real constants. Later annular
continuum comparison needs vanishing jets of the difference from Wilson's
kernel.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {σ A : ℝ}

abbrev FaceRow := Row (TypeFace 2) (TypeFace 2)
def dcross (J : FaceRow) (p : Momentum) := (symbol 1 (-p)).transpose*J.read p * symbol 1 p
def axisPair (p : Space 1) := projected (stick 0) p

def slots (J : FaceRow) (G : Gauge) : Picture G 1 := fun i b p =>
    if i 0=i 1 then (1/2 : ℂ)*dcross J (axisPair p) (b 0) (b 1) else 0


lemma partsWave (p : Site m) (a : TypeFace 1) (i j : G.ColorIndex) : faceParts (G:=G) j (relay p (a,i))=
    if i=j then relay p a else 0 := by
  split <;> rename_i he
  · subst i; ext1 x; simp [faceParts,tune,relay,Pi.single_apply]
  ext1 x; simp [faceParts,tune,relay, Ne.symm he]

lemma tuned {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] (V : Row α β) (h : V.safe)
    (v : Phase β) (p : Site m) : approached (V.acts m) *ᵥ tune p v=tune p (V.read (mon p)*ᵥ v) := by
  have he (k : β) (x : Co m α) : (approached (V.acts m)*ᵥ relay p k) x = cell p x.1 * V.read (mon p) x.2 k := by
    rw [show relay p k=(fun x => rotations m _ x (p,k)) from funext fun x => (coef_wave p x.1 x.2 k).symm]
    change (approached (V.acts m) * rotations m β) x (p,k)=_
    rw [circulant m V h]; exact rot_fiber ..
  rw [show tune p v=∑ k,v k • relay p k by
    funext x; rw [Finset.sum_apply]; simp [tune,relay,Pi.single_apply,mul_comm]]
  simp_rw [Matrix.mulVec_sum, Matrix.mulVec_smul]; ext1 x; rw [Finset.sum_apply]
  conv_rhs => unfold tune; rw [Matrix.mulVec,dotProduct,Finset.mul_sum]
  simp only [Pi.smul_apply,he,smul_eq_mul]; exact sum_congr rfl fun i _ => by ring

private lemma dPair (J : FaceRow) (h : J.safe) (p q : Site m) (i j : TypeFace 1) :
    (relay p i) ⬝ᵥ (approached (Precision.K (J.acts m)) *ᵥ relay q j) = if p+q=0 then
        (Fintype.card (Site m):ℂ)*dcross J (mon q) i j else 0 := by
  have hd (k : Site m) (b : TypeFace 1) : (approached (d 1 m))*ᵥ relay k b = tune k (fun i => symbol 1 (mon k) i b) := by
    unfold d relay; rw [tuned _ (cobound_safe 1),reading]; congr 1; ext1 a; simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  have ht : approached (d 1 m).transpose=(approached (d 1 m)).transpose := rfl
  rw [Precision.K, prom_mul,prom_mul,ht,← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,hd,hd, tuned J h]
  unfold dotProduct
  rw [Fintype.sum_prod_type]
  let y : ℂ := ∑ v, symbol 1 (mon p) v i * (J.read (mon q) *ᵥ fun i => symbol 1 (mon q) i j) v
  have e (x) : cell p x * cell q x = cell (p+q) x := by rw [cell_duality p,cell_duality q,cell_duality (_+_),cell_add]
  have hx (x : Site m) : ∑ i' : TypeFace 2, tune p (fun i' => symbol 1 (mon p) i' i) (x,i') *
      tune q (J.read (mon q)*ᵥ fun i => symbol 1 (mon q) i j) (x,i') = cell (p+q) x * y := by
    rw [← e]; unfold y; rw [Finset.mul_sum]; apply sum_congr rfl; intro a _; unfold tune; dsimp only; ring
  simp_rw [hx]; rw [← Finset.sum_mul]
  split
  next he =>
    rw [he]; simp only [cell,mon_zero,mode_constant,sum_const,card_univ,nsmul_eq_mul,mul_one]; congr 1
    unfold y dcross; rw [Matrix.mul_assoc,Matrix.mul_apply]
    rw [rolls_symbol (p:=mon p) (q:=-mon q)]; rotate_left
    · apply rolls_of_mode; intro i; rw [← cell_wrap,mode_inverse, ← cell_wrap,eq_neg_of_add_eq_zero_left he,
        cell_duality,cell_inverse,cell_duality]
    rfl
  next he => rw [sum_cell he,zero_mul]

section pair
variable {α : Type} [Fintype α] [DecidableEq α]

-- weighted metric expression

def stringFiscal (B : Matrix (Body 1 m) (Body 1 m) ℝ) (x y : Phase (Lines G m 1)) : ℂ := ∑ i : G.ColorIndex,
    faceParts i x ⬝ᵥ (approached B *ᵥ faceParts i y)
lemma lucent {F : Link G m→ℝ} {B : Matrix (Body 1 m) (Body 1 m) ℝ}
    (he : ∀ x y : Link G m, iteratedFDeriv ℝ 2 F 0 ![x,y]=∑ i,
      parts G 1 (arm G m 1 x) i ⬝ᵥ (B *ᵥ parts G 1 (arm G m 1 y) i)) (b : Fin 2→Phase (Lines G m 1)) :
    noteAt F 2 b=(1/2:ℂ)*stringFiscal B (b 0) (b 1) := by
  let w : RecordM ℂ (Fin 2) (Lines G m 1) := MultilinearMap.mk' (fun v => stringFiscal B (v 0) (v 1))
    (fun v i x y => by fin_cases i <;> simp [stringFiscal,add_dotProduct,dotProduct_add,Matrix.mulVec_add,Finset.sum_add_distrib])
    (fun v i x y => by fin_cases i <;> simp [stringFiscal,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct,Finset.mul_sum])
  have hv : beat F 0 2 = w := by
    apply enlarge_unique; intro v
    rw [beat_real]; have hw : v=![v 0,v 1] := by ext j _; fin_cases j <;> simp
    conv_lhs => rw [hw,he]
    change _=stringFiscal (G:=G) B (axes (v 0)) (axes (v 1))
    unfold stringFiscal Matrix.mulVec dotProduct; push_cast; rfl
  unfold noteAt; rw [_root_.smul_apply, hv]; norm_num [Nat.factorial,w,MultilinearMap.mk']

lemma according {F : Link G m → ℝ} {B : FaceRow} (h : B.safe)
    (he : ∀ x y : Link G m, iteratedFDeriv ℝ 2 F 0 ![x,y]=∑ i,
      parts G 1 (arm G m 1 x) i ⬝ᵥ (Precision.K (B.acts m) *ᵥ parts G 1 (arm G m 1 y) i)) :
    Recorded (slots B G) F 0 := by
  apply (record_exact ..).2; intro p i b
  rw [lucent he]; unfold stringFiscal collected
  change _ * (∑ j: G.ColorIndex,(faceParts j (relay _ _)) ⬝ᵥ approached _ *ᵥ (faceParts j (relay _ _)))=_
  rw [Finset.sum_eq_single (i 0)]
  · simp_rw [partsWave]; rw [show (∑ j,p j)=p 0+p 1 from Fin.sum_univ_two p]; unfold slots
    have hy : projected (stick 0) (outphase p)=mon (p 1) := rfl
    by_cases hh : i 1=i 0
    · rw [if_true,if_pos hh,dPair B h]; split <;> simp [*,axisPair,hh] <;> ring
    rw [if_true,if_neg hh,if_neg (Ne.symm hh)]; simp
  · intro j _ hv; simp only [partsWave,if_neg (Ne.symm hv),zero_dotProduct]
  simp
end pair
end YM.Stationary
end

/-!
# Phase-routed rectangular kernels. Counting on Co-type layers.

Exact representation on the given grid m by test waves at every momentum
of that grid (including nonfundamental representatives). Shifts to be fixed
by external insertions. Deliberately requires no statements about other
grids to do algebra; clients needing infinite-volume estimates must ensure
producers of `Jaunt` work *on that very model* for all those periods. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {G : Gauge} {m : Side} {ι α β γ : Type}

lemma rolls.plus {q q' r r' : Phase α} (h : rolls q r) (he : rolls q' r') : rolls (q+q') (r+r') := by
  obtain ⟨d,rfl⟩ := h; obtain ⟨d',rfl⟩ := he
  refine ⟨d+d',?_⟩; ext i; simp only [Pi.add_apply, reciprocal,Int.cast_add,mul_add]; ring
lemma rolls.combine {p q : Site m} {A B : Momentum} (h : rolls (mon p) A) (hp : rolls (mon q) B) : rolls (mon (p+q)) (A+B) := by
  apply rolls_of_mode; intro x
  rw [mode_phase,← h.exp,← hp.exp, ← cell_wrap, ← cell_wrap,← cell_wrap,cell_duality (p+q),cell_add,cell_duality p,cell_duality q]
lemma rolls.flip_sign {p : Site m} {q : Momentum} (h : rolls (mon p) q) : rolls (mon (-p)) (-q) := by
  apply rolls_of_mode; intro x
  rw [mode_inverse,← h.exp,← cell_wrap,← cell_wrap,cell_duality (-p),cell_inverse,cell_duality]

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

abbrev CompM (α β : Type) := Matrix α β ℂ
abbrev CircM (m : Side) (α β : Type) := CompM (Co m α) (Co m β)
lemma ray_pick (p : Site m) : Injective (tune (α:=α) p) := fun u v h =>
    funext fun i => mul_left_cancel₀ (cell_ne p 0) (congr_fun h (0,i))

lemma ray_book (x y : Phase (Co m α)) (h : ∀ k : Site m, ∀ b : Phase α, dotProduct (tune k b) x = dotProduct (tune k b) y) : x=y := by
  let R := rotations m α
  have hv := rotations_gram m α
  have hk : R*(((m.val:ℂ)^4)⁻¹ • star R)=1 := by
    rw [Matrix.mul_smul, show R*star R=_ from hv, smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (side_ne _)),one_smul]
  have hh : x ᵥ* R=y ᵥ* R := by
    ext1 i; unfold Matrix.vecMul
    rw [dotProduct_comm,dotProduct_comm y]
    change dotProduct (fun j => rotations m α _ i) x=_
    rw [show (fun j => rotations m α j i)=tune i.1 (Pi.single i.2 1) from funext fun j => coef_wave i.1 j.1 j.2 i.2]; exact h ..
  exact vecMul_injective_of_isUnit (⟨⟨R,_,hk,mul_eq_one_comm.mp hk⟩,rfl⟩) hh
lemma ray_dots (p q : Site m) (u v : Phase α) : dotProduct (tune p u) (tune q v)=
    if p+q=0 then (Fintype.card (Site m):ℂ)*dotProduct u v else 0 := by
  have he (k : Site m) : (∑ i : α, tune p u (k,i)*tune q v (k,i))=cell (p+q) k*dotProduct u v := by
    rw [cell_duality (p+q),cell_add]; unfold dotProduct tune; rw [mul_sum]; apply sum_congr rfl; intro i _; simp only [cell_duality k]; ring
  change ∑ x,tune p u x*tune q v x=_; rw [Fintype.sum_prod_type]; simp_rw [he]; rw [← Finset.sum_mul]
  split; next hp => rw [hp]; simp [cell]
  next hp => rw [sum_cell hp,zero_mul]

/-- An external INSERTION shifts by k, with cover character e^{i(q+p)y} on coarse cells. -/
def Jaunt (B : CircM m α β) (f : Momentum → CompM α β) (k : Site m) :=
    ∀ (p : Site m) (q : Momentum), rolls (mon p) q → ∀ v : Phase β, B *ᵥ tune p v=tune (p+k) (f q *ᵥ v)
namespace Jaunt
variable {U U' : CircM m α β} {F K : Momentum → CompM α β} {a b : Site m}

lemma plus (h : Jaunt U F a) (hp : Jaunt U' K a) : Jaunt (U+U') (F+K) a := by
  intro p q hv v; rw [add_mulVec,h p q hv,hp p q hv, Pi.add_apply, add_mulVec]; ext1 x; simp [tune,mul_add]
lemma smul (h : Jaunt U F a) (s : ℂ) : Jaunt (s • U) (s • F) a := by
  intro p q hv v; rw [smul_mulVec,h p q hv,Pi.smul_apply,smul_mulVec]; ext1 i; simp [tune,mul_left_comm]
lemma backside (h : Jaunt U F a) : Jaunt (-U) (-F) a := by simpa using h.smul (-1)
lemma zero (p : Site m) : Jaunt (0:CircM m α β) 0 p := by intro p q hv v; ext1 i; simp [tune]
lemma noop : Jaunt (1:CircM m α α) (fun _ => 1) 0 := by intro p q hv v; simp
lemma row (J : Row α β) (he : J.safe) : Jaunt (approached (J.acts m)) J.read 0 := by
  intro p q h u; rw [tuned J he]; congr 1; · simp
  obtain ⟨z,rfl⟩ := h
  rw [J.periods]

lemma adjoin (h : Jaunt U F a) {P : Momentum} (hp : rolls (mon a) P) : Jaunt Uᵀ (fun q => (F (-(q+P)))ᵀ) a := by
  intro p q H v; apply ray_book; intro i w; rw [dotProduct_mulVec, Matrix.vecMul_transpose]
  by_cases he : i+(p+a)=0
  · have hh : rolls (mon i) (-(q+P)) := by rw [eq_neg_of_add_eq_zero_left he]; exact (H.combine hp).flip_sign
    rw [h i _ hh, ray_dots, ray_dots, if_pos he, if_pos (show i+a+p=0 by rw [← add_assoc] at he; rwa [add_right_comm]),dotProduct_mulVec,Matrix.vecMul_transpose]
  rw [h i (mon i) (rolls.refl _) w,ray_dots,ray_dots,if_neg he]; rw [if_neg (show i+a+p ≠ 0 by rw [← add_assoc] at he; rwa [add_right_comm])]

lemma join [Fintype γ] [DecidableEq γ] {V : CircM m β γ} {G : Momentum → CompM β γ} (h : Jaunt U F a) (hv : Jaunt V G b)
    {k : Site m} {P : Momentum} (he : rolls (mon b) P) (hk : b+a=k) : Jaunt (U*V) (fun q => F (q+P)*G q) k := by
  intro p q hp v; rw [← Matrix.mulVec_mulVec,hv _ _ hp,h _ _ (hp.combine he),mulVec_mulVec,add_assoc,hk]

variable {N : CircM m α α} {D : Momentum → CompM α α}
lemma funded (h : Jaunt N D 0) (he : IsUnit N.det) {p : Site m} {q : Momentum} (hp : rolls (mon p) q) : IsUnit (D q).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]; intro i j hj
  apply ray_pick p; apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr he); rw [h _ _ hp,h _ _ hp,hj]
lemma backway (h : Jaunt N D 0) (he : IsUnit N.det) : Jaunt N⁻¹ (fun q => (D q)⁻¹) 0 := by
  intro p q hv v
  apply mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr he); rw [add_zero,h p q hv,mulVec_mulVec,mulVec_mulVec,mul_nonsing_inv N he,mul_nonsing_inv (D q) (h.funded he hv),one_mulVec,one_mulVec,add_zero]

lemma accounting (h : Jaunt N D a) : N.trace=if a=0 then ∑ p : Site m,(D (mon p)).trace else 0 := by
  let T : CircM m α α := of fun i j => if i.1=j.1+a then D (mon j.1) i.2 j.2 else 0
  let R := rotations m α
  have hr : N*R=R*T := by
    ext x ⟨p,b⟩
    have he := h p (mon p) (rolls.refl _) (Pi.single b 1)
    rw [Matrix.mul_apply]
    change (N *ᵥ (fun i => R i (p,b))) x=_
    rw [show (fun i => R i (p,b))=tune p (Pi.single b 1) from funext fun i => coef_wave ..,he]
    simp [T, Matrix.mul_apply,R,rotations,Fintype.sum_prod_type,tune,Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite,ite_mul,eq_comm]
  let Z := (((m.val:ℂ)^4)⁻¹ • star R)
  have hz : R*Z=1 := by
    unfold Z R; rw [Matrix.mul_smul,rotations_gram,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (side_ne _)),one_smul]
  have hx : N.trace=T.trace := by
    have hp : N=R*T*Z := by rw [← hr,Matrix.mul_assoc,hz,mul_one]
    rw [hp,trace_mul_comm, ← Matrix.mul_assoc, mul_eq_one_comm.mp hz, one_mul]
  rw [hx,trace,Fintype.sum_prod_type]; split <;> simp_all [T, Matrix.trace]
end Jaunt
end YM.Stationary
end
