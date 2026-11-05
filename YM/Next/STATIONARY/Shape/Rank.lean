import YM.Next.STATIONARY.Films.TraceDifference
import YM.Next.STATIONARY.Shape.Scaled


set_option autoImplicit false
/-!
# Real flare identification with left-perturbed dough, arbitrary relevant
period. F-only auxiliary use (annulus) also via linear form U. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {n : ℕ} {c f m L : Side} {p : Clip} {R : PathData G} {σ C A D : ℝ}

section generic
variable (p R)
def fireR (m : Side) (x : Corn (Co m (Crisp G))) := intended p R (dough G m x)
variable {p R}
lemma fireCont (m : Side) (h : R.Bounds p σ A D) : ContDiffAt ℝ ω (fireR p R m) 0 := by exact ContDiffAt.comp (g:=intended p R) _ (dough_zero G m ▸ (strain _ _ h).analytic.contDiffAt) (dough_floats G m).contDiffAt
lemma fire_gem : ∀ᶠ x : Corn (Co m (Crisp G)) in 𝓝 0, fireR p R m x=burn p R (input G m (wheat false x)) (wheat true x) := by
  let M (b : Bool) : Corn (Co m (Crisp G)) →L[ℝ] Link G m := (wheat b).toContinuousLinearMap
  let F := fun x : Corn (Co m (Crisp G)) => input G m (M true x)*input G m (M false x)
  have hk : Continuous F := Continuous.mul (input_cont.comp (M true).continuous) (input_cont.comp (M false).continuous)
  have he : F 0=1 := by unfold F; simp
  filter_upwards [(show Tendsto F (𝓝 0) (𝓝 1) by rw [← he]; exact hk.tendsto 0).eventually content_encodes] with x hx
  change mainTerm _ _ (input G m (content (F x)))=_; rw [hx]; rfl

variable (K : Corn α →L[ℝ] Link G m) (B : Lines G m 1≃β)
variable (p R)
def FireMat (x : Corn α) := repackM B B (flare p R (input G m (K x)))
variable {p R}

def fireK : Corn α→L[ℝ] Corn (Co m (Crisp G)) := (show Link G m→ₗ[ℝ] _ from sprout false).toContinuousLinearMap ∘L K
def cracker : Corn β→L[ℝ] Link G m := (LinearMap.pi (fun x : Lines G m 1=> LinearMap.proj (B x))).toContinuousLinearMap
def fireB : Corn β→L[ℝ] Corn (Co m (Crisp G)) := (show Link G m →ₗ[ℝ] _ from sprout true).toContinuousLinearMap ∘L cracker B

lemma flare_bank (h : R.Bounds p σ C A) : ∀ᶠ x in 𝓝 0,∀ u v,
    dotProduct u (FireMat p R K B x *ᵥ v)=iteratedFDeriv ℝ 2 (fun v=> fireR p R m (fireK K x+fireB B v)) 0 ![u,v] := by
  let a := Corn α
  let b := Link G m
  let M : a×b→ Corn (Co m (Crisp G)) := fun x => fireK K x.1+ (sprout (R:=ℝ) (m:=m) (α:=Loc G 1) true).toContinuousLinearMap x.2
  have ht : M 0=0 := by unfold M; simp
  have hh : Tendsto M (𝓝 0) (𝓝 0) := by rw [← ht]; exact (show Continuous M by unfold M; fun_prop).continuousAt
  let F x y := burn p R (input G m (K x)) y
  have he : ∀ᶠ v : a×b in 𝓝 0,F v.1 v.2=fireR p R m (M v) := by
    filter_upwards [hh.eventually fire_gem] with x hx; rw [hx]; change _=burn _ _ (input _ _ (wheat false (sprout false _+sprout true _))) (wheat true (sprout false _+sprout true _))
    rw [map_add,wheat_swims,wheat_avoids (by decide : false≠true),map_add,wheat_swims,wheat_avoids (by decide : true≠false),zero_add,add_zero]; rfl
  have hu : ContDiffAt ℝ ω (fun v : a×b => F v.1 v.2) 0 := ((ht.symm ▸ fireCont m h : ContDiffAt ℝ ω (fireR p R m) (M 0)).comp (f:=M) _ (by unfold M; fun_prop)).congr_of_eventuallyEq he
  have hα : ∀ᶠ x : a in 𝓝 0,AnalyticAt ℝ (F x) 0 := by
    have hx : ∀ᶠ x : a in 𝓝 0,AnalyticAt ℝ (fun v : a×b => F v.1 v.2) (x,0) := by
      apply (show Tendsto (fun x : a => (x,(0:b))) (𝓝 0) (𝓝 ((0:a),0)) from (continuous_id.prodMk continuous_const).continuousAt.tendsto).eventually
      exact hu.analyticAt.eventually_analyticAt
    filter_upwards [hx] with x hx; exact (hx.contDiffAt.comp (f:=fun v => (x,v)) 0 (by fun_prop)).analyticAt
  have hv : ∀ᶠ x : a in 𝓝 0,∀ᶠ y : b in 𝓝 0,F x y=fireR p R m (M (x,y)) := by
    rw [show (0:a×b)=((0:a),(0:b)) from rfl,nhds_prod_eq] at he; exact he.curry
  let T := cracker B
  filter_upwards [hv,hα] with x hx hk u v
  have he : F x ∘ T=ᶠ[𝓝 0] (fun y => fireR p R m (fireK K x+fireB B y)) := (show Tendsto T (𝓝 0) (𝓝 0) by simpa using T.continuous.tendsto 0).eventually hx
  rw [← (he.iteratedFDeriv ℝ 2).eq_of_nhds,wired T (by rw [map_zero]; exact hk),map_zero]
  let H := damage (pocket _) (F x) 0
  have hz (w : Corn β) : w=T w ∘ B.symm := by ext1 i; change w i=w (B (B.symm i)); rw [B.apply_symm_apply]
  calc
    _ = dotProduct (T u ∘ B.symm) (repackM B B H *ᵥ (T v ∘ B.symm)) := congrArg₂ (fun u v => dotProduct u (repackM B B H *ᵥ v)) (hz u) (hz v)
    _ = _ := by rw [repack_act, ← repack_dot, show T∘![u,v]=![T u,T v] by ext1 j; fin_cases j <;> rfl]; simpa only [cash_pocket] using detracts (pocket (Lines G m 1)) (F x) 0 (T u) (T v)

abbrev duoTop (k : ℕ) (v : Fin k → α) (x y : α) : Fin (k+2)→ α := Fin.snoc (Fin.snoc v x : Fin (k+1) → α) y
def creme (n : ℕ) : Fin (n+2)→ Bool := duoTop n (fun _ => false) true true
variable (u : Phase α→ₗ[ℂ] Phase (Lines G m 1)) (hp : ∀ a,u (axes a)=axes (K a))
include hp
lemma published (h : R.Bounds p σ C D) (x y : Phase β) (d : Fin n→Phase α) :
    dotProduct x (art (FireMat p R K B) n d*ᵥ y)=liquid (creme n) (intended p R) (duoTop n (u ∘ d) (x ∘B) (y∘B)) := by
  have he := flare_bank K B h
  let V := fireK K
  let W := fireB B
  let M : Phase β→ₗ[ℂ] Phase (Lines G m 1) := LinearMap.pi fun i=>LinearMap.proj (B i)
  have hk i : (sprout false ∘ₗ u) (axes i)=axes (V i) := by rw [LinearMap.comp_apply,hp,sprout_axes]; rfl
  have hx i : (sprout true∘ₗ M) (axes i)=axes (W i) := by rw [LinearMap.comp_apply,show M (axes i)=axes (cracker B i) from rfl,sprout_axes]; rfl
  have hv := all_hess V W hk hx d (play_memo V W (fireCont m h) he) (fireCont m h) he x y
  rw [hv]; unfold liquid; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg (beat (fireR p R m) _ _)
  ext1 i; unfold creme duoTop; cases i using Fin.lastCases with
  | last => simp; rfl
  | cast i => cases i using Fin.lastCases <;> simp <;> rfl
end generic
end YM.Stationary
end

/-!
# Fixed-dimension census stamp of rank Κ. Energy cost in twisted momentum.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] {n : ℕ} {c f m L : Side} {p q : Momentum} {σ C A D : ℝ}

def syrupC (Φ : Bridge G P) (v : Fin n→ Momentum) (a : Fin n→ Loc G 1) (i : Fin n) := Φ (v i)*ᵥ Pi.single (a i) 1

def gusts (v : Fin n→ Momentum) (q : Momentum) := duoTop n v (-sunshift v q) q

lemma twinBill (X : RecordM ℂ (Fin (n+2)) α) (u : Fin n→ Phase α) (M : CompM α α) (H : ∀ i j,M i j=X (duoTop n u (Pi.single i 1) (Pi.single j 1))) (v w : Phase α) :
    dotProduct v (M*ᵥ w)=X (duoTop n u v w) := by
  have he j (a : Phase α) (x) : X (update x j a)=∑ i,X (update x j (Pi.single i 1))*a i := by
    let L := X.toLinearMap x j
    change L a=∑ i,L _ * a i
    conv_lhs => rw [show a=∑ i,a i • Pi.single i (1:ℂ) by ext i; simp [Finset.sum_apply,Pi.single_apply]]
    rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul]; exact mul_comm ..
  have hv i : (M *ᵥ w) i = X (duoTop n u (Pi.single i 1) w) := by
    unfold duoTop Matrix.mulVec dotProduct; rw [sonnet (Fin.snoc u (Pi.single i 1)) 0 w, he]; apply sum_congr rfl; intro a _; dsimp only; rw [H,← sonnet]
  have hu := he (Fin.castSucc (Fin.last n)) v (Fin.snoc (Fin.snoc u 0 : Fin (n+1) → _) w); simp_rw [← snock, ← sonnet] at hu
  unfold dotProduct; simp_rw [hv]; unfold duoTop; rw [hu]; exact sum_congr rfl fun _ _ => mul_comm ..

section sprice
variable (Φ : Bridge G P) (l : ι → Stitch (n+1)) (K : Needle ι (Loc G 1) (n+1))

def ripple (v : Fin n→ Momentum) (a : Fin n→ Loc G 1) (q : Momentum) : CircM P.L (Loc G 1) (Loc G 1) :=
    Matrix.of fun i j=> tunnels l K (gusts v q) (duoTop n (syrupC Φ v a) (Pi.single i 1) (Pi.single j 1))
lemma ripple_evals (v : Fin n→ Momentum) (a : Fin n→ Loc G 1) (q : Momentum) (u w) : dotProduct u (ripple Φ l K v a q *ᵥ w)=
    tunnels l K (gusts v q) (duoTop n (syrupC Φ v a) u w) := twinBill _ _ _ (fun _ _ => rfl) u w
lemma gust_p {p : Fin n→Momentum} (h : ∀ i,p i∈strip σ) (he : q∈strip σ) (hv : sunshift p q∈strip σ) : ∀ i,gusts p q i∈strip σ := by intro i; unfold gusts duoTop; cases i using Fin.lastCases with
    | last => simpa using he
    | cast j => cases j using Fin.lastCases <;> simp [*,negResident hv]
lemma ripple_flip (h : Poster σ Φ) (v r : Fin n→Momentum) (a : Fin n→Loc G 1) (hv : ∀ i,v i∈strip σ) (he : ∀ i,rolls (v i) (r i)) (hp : rolls p q) :
    ripple Φ l K v a p=ripple Φ l K r a q := by
  have hx : syrupC Φ v a=syrupC Φ r a := by ext1 i; unfold syrupC; rw [h.shifts (he i) (hv i)]
  have hh : ∀ i,rolls (gusts v p i) (gusts r q i) := snockedR rolls _ _ (snockedR rolls v r he ((hp.plus (rolls_sums he)).neg)) hp
  unfold ripple; rw [hx,tunnels_twist l K hh (L:=P.L)]
section loc
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
lemma ripple_bill (v : X→Fin n→Momentum) (a : Fin n→ Loc G 1) (p : X→ Momentum) (x) (hp : ∀ i,DifferentiableAt ℂ (fun y=> v y i) x) (hq : DifferentiableAt ℂ p x)
    (he : ∀ i,v x i∈strip σ) (hv : p x∈strip σ) (hW : sunshift (v x) (p x)∈strip σ) (h : Poster σ Φ) (hf : Dai K (inch P.L*σ) C) (hs : 0<σ) : BillD (fun y => ripple Φ l K (v y) a (p y)) x := by
  intro i j; let H (y : X) := gusts (v y) (p y); let V y := duoTop n (syrupC Φ (v y) a) (Pi.single i 1) (Pi.single j 1); let U y := (H y,V y)
  have hb : DifferentiableAt ℂ H x := by
    unfold H gusts duoTop; apply differentiableAt_pi.mpr; exact diff_snoc (diff_snoc hp (hq.add (DifferentiableAt.fun_sum (fun i _=> hp i))).neg) hq
  have hP : DifferentiableAt ℂ V x := by
    apply differentiableAt_pi.mpr; intro i
    unfold V duoTop; cases i using Fin.lastCases with
    | last => simp [differentiableAt_const]
    | cast j => cases j using Fin.lastCases with
      | last => simp [differentiableAt_const]
      | cast b =>
        simp only [Fin.snoc_castSucc]; apply differentiableAt_pi.mpr; intro c; unfold syrupC Matrix.mulVec dotProduct
        exact DifferentiableAt.fun_sum fun i _=> ((h.shape (he b) c i).comp x (hp b)).mul_const _
  exact (tunnels_bill l K hf hs (U x) (gust_p he hv hW)).comp (f:=U) x (hb.prodMk hP)
end loc
end sprice
end YM.Stationary
end

/-!
# Power counting on true Κ vertex. Keep branch-independent energy slab.
Log correction comparison after normalizing dot. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] {n t : ℕ} {c f m L : Side} {p q : Momentum} {σ C A D : ℝ}
-- word size factors
lemma needleCollapse (l : Stitch t) (u : ℕ) (K : ℝ) (L : Side) (h : (t+1)+∑ j,(l j).length=4+u) :
    (L.val:ℝ)^4*(∏ j, inch L^(1+(l j).length)*K)=inch L^u*K^(t+1) := by
  have hz : (∑ j : Fin (t+1), (1+(l j).length))=4+u := by rw [Finset.sum_add_distrib]; simpa [h]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,hz,pow_add,Finset.prod_const,card_univ,Fintype.card_fin, ← mul_assoc,← mul_assoc, ← mul_pow, mul_comm (L.val:ℝ), inch_unit, one_pow, one_mul]

def roundBay (G : Gauge) (t : ℕ) (ι : Type) [Fintype ι] (C σ E : ℝ) := ((Fintype.card (Breed t (Loc G 1)):ℝ)* Fintype.card ι*robinTax σ t)*E*C

def ruffle (C : ℝ) := C+Real.exp 4*5
lemma ruffled (hc : 0 ≤ C) : 0 ≤ ruffle C := by unfold ruffle; positivity
lemma rip_room (G : Gauge) (t : ℕ) (ι : Type) [Fintype ι] (σ C E : ℝ) (h : 0≤C) (he : 0≤E) : 0 ≤ roundBay G t ι C σ E := by unfold roundBay robinTax; positivity
variable (Φ : Bridge G P) (l : ι → Stitch (n+1)) (K : Needle ι (Loc G 1) (n+1))

lemma ripple_cash (h : Cruise Φ 1 σ D) (hs : 0<σ) (hp : σ≤1) (hc : Dai K (inch P.L*σ) C) (he : 0≤C) (hg : ∀ a i,(l a i).length ≤1) (hx : ∀ a,(n+2)+(∑ i,(l a i).length)=4)
    (v : Fin n→ Momentum) (a : Fin n→Loc G 1) (hv : ∀ i,v i∈strip σ) (p : Momentum) (hi : p∈strip σ) (hS : sunshift v p∈strip σ) :
    serial (altarTile P.L (Loc G 1)|>.dual) (altarTile P.L (Loc G 1)) (sunshift v p) p (ripple Φ l K v a p) (roundBay G (n+1) ι C σ ((ruffle D)^(n+2))) := by
  let x := altarTile P.L (Loc G 1)
  let q:= -sunshift v p
  have hr := negResident hS; have hA := h.2.1
  refine stands_echo _ (rip_room G (n+1) ι _ C _ he (pow_nonneg (ruffled hA) _)) fun u w hu hw => ?_
  let V := syrupC Φ v a; let R := ruffle D; let Y (i : ι) (a : Fin (n+2)) := inch P.L^(1+(l i a).length)*R
  rw [ripple_evals]; refine tunnels_book l K hc hs (gust_p hv hi hS) _ Y (n:=duoTop n (fun _ : Fin n=> (0:ℕ)) 1 1) ?_ ?_ he (fun a => ?_)
  · intro i b j
    have hB p (k : Fin (n+2)) (t : Phase (Co P.L (Loc G 1))) (hp' : p∈strip σ) (hx : x.rate p t≤1) : Hearing (balcony _) 1 (fun z : Site P.L=> flight p (l i k) t (z,j)) (Y i k) := (lower_voice (p:=p) (fun j => (hp' j).trans_le hp) hx _ (hg i k) _).more (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) (pow_nonneg (inch_pos _).le _))
    unfold gusts duoTop; cases b using Fin.lastCases with
    | last => simpa using hB _ _ w hi hw
    | cast r => cases r using Fin.lastCases with
      | last => simpa using hB _ _ u hr hu
      | cast r =>
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        let b := r.castSucc.castSucc
        have hB : Hearing (balcony _) 0 (fun z : Site P.L=> flight (v r) (l i b) (V r) (z,j)) _ := Hearing.sup (mul_nonneg (pow_nonneg (inch_pos _).le _) hA) fun z => h.2.2 (l i b) (hg i b) (v r) (hv r) (a r) (z,j)
        exact hB.more (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (pow_nonneg (inch_pos _).le _))
  · unfold duoTop; rw [snocked_sum, snocked_sum]; simp
  exact le_of_eq ((needleCollapse (l a) 0 R P.L (hx a)).trans (by rw [pow_zero,one_mul]))
end YM.Stationary
end

/-!
# Flare tube on the real resonance sets. External single pick at all
phases, tubes no independence claim off-pencil. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] {n : ℕ} {c f m L : Side} {σ C A D τ : ℝ}

section cash
variable {p q : Momentum}
lemma rolls_strip_REAL (a : Site m) (hp : rolls (mon a) p) (hs : 0<σ) : p∈strip σ := Work.F07.realStrip _ hs (hp.metric (real_frequency _))
omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma duoRoll {u : Fin n→α} {v : Fin n→ β} (h : α →β→Prop) (he : ∀ i,h (u i) (v i)) {x z y w} (hp : h x z) (hv : h y w) : ∀ i,h (duoTop n u x y i) (duoTop n v z w i) := snockedR h _ _ (snockedR h u v he hp) hv
lemma duoSum {R : Type} [AddCommMonoid R] (v : Fin n→R) (x y) : ∑ i,duoTop n v x y i=(∑ i,v i)+x+y := by unfold duoTop; rw [snocked_sum,snocked_sum]
end cash

section reality
variable (S : StepData c f) (Φ : Bridge G S.patch) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (l : ι→ Stitch (n+1)) (K : Needle ι (Loc G 1) (n+1)) {p : Clip} {R : PathData G}
lemma tack_jack (he : Premise S W Φ) {t : Site c} {v : Momentum} (hp : rolls (mon t) v) (i : Phase (Loc G 1)) : approached (patron G W)*ᵥ tune t i = poured S.ratio t (Φ v*ᵥ i) := by
  let x:= tune t i
  let y:= unitSplit G S 1
  have hh : (approached (patron G W)*ᵥ x) ∘ y.symm=tune t (Φ v*ᵥ i) := (repack_act y (Equiv.refl _) _ _).symm.trans ((he _ _ hp i).trans (by rw [add_zero]; rfl))
  ext j; have hk := congr_fun hh (y j); rw [Function.comp_apply, Equiv.symm_apply_apply] at hk; exact hk
lemma wave_skim (he : Premise S W Φ) (h : R.Bounds p τ A D) (hc : Dai K (inch S.patch.L*σ) C) (hp : Bitter l K (creme n) (intended p R (m:=f))) (hs : 0<σ)
    (q : Fin n→Momentum) (i : Fin n→ Loc G 1) (v : Fin n→Site c) (hw : ∀ i,rolls (mon (v i)) (q i)) :
    Jaunt (art (FireMat p R (uniformM W) (unitSplit G S 1)) n (fun j => relay (v j) (i j))) (ripple Φ l K q i) (∑ j,v j) := by
  intro u y H a
  let B:=unitSplit G S 1
  let V := art (FireMat p R (uniformM W) B) n (fun j=>relay (v j) (i j))
  let C' := fun j=> relay (v j) (i j)
  let Y := syrupC Φ q i
  let F : Phase (Lines G c 1)→ₗ[ℂ] Phase (Lines G f 1) := Matrix.mulVecLin (approached (patron G W))
  have hx : F ∘ C'=fun j=>poured S.ratio (v j) (Y j) := funext fun j=> tack_jack S Φ W he (hw j) (Pi.single (i j) 1)
  have hb j : F (axes j)= axes (uniformM W j) := (prom_vec ..).trans (congr_arg axes (patron_fee W j))
  have hq j := rolls_strip_REAL _ (hw j) hs
  apply ray_book; intro r b
  let e := r+(u+∑ j,v j)
  have hy (x) (g : rolls (mon r) x) : dotProduct (tune r b) (V*ᵥ tune u a)= if e=0 then
      (Fintype.card (Site c):ℂ)*tunnels l K (duoTop n q x y) (duoTop n Y b a) else 0 := by
    rw [show V=_ from rfl, published (uniformM W) B F hb h (tune r b) _ (fun j=> relay (v j) (i j))]
    let p' := duoTop n v r u; let q':=duoTop n q x y; let w := duoTop n Y b a
    have h' := duoRoll (n:=n) (u:=v) (v:=q) (fun i j=>rolls (mon i) j) hw g H
    have hd := nectar_run S.ratio hc hp p' q' h' (fun j => rolls_strip_REAL _ (h' j) hs) hs w
    rw [show (∑ i,p' i)=e by unfold p' e; rw [duoSum]; abel] at hd
    refine (congr_arg (liquid (creme n) (intended p R)) ?_).trans hd
    rw [show F ∘ (fun j=> relay _ _)= _ from hx]; unfold p' w duoTop
    ext1 j; cases j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast j => simp only [Fin.snoc_castSucc]; cases j using Fin.lastCases <;> simp only [Fin.snoc_castSucc,Fin.snoc_last] <;> rfl
  change dotProduct _ (V *ᵥ tune u a)= _
  rw [ray_dots]; split
  next hz =>
    have hh : rolls (mon r) (-sunshift q y) := by rw [eq_neg_of_add_eq_zero_left hz]; exact (H.combine (collide v q hw)).flip_sign
    rw [hy _ hh,if_pos hz]; exact congr_arg ((Fintype.card (Site c):ℂ)*·) (ripple_evals Φ l K q i y b a |>.symm)
  next hz => rw [hy _ (rolls.refl _),if_neg hz]
end reality
end YM.Stationary
end

/-!
# Claiming three-vertex sheet pre-L. Persistence on exactly the widths
 chosen from U. InfraAfter budgets `provided` for one path not requiring
 program. Δ leg points are per call. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {i j n t : ℕ} {c f m L : Side} {p q r : Momentum} {σ η C A D : ℝ} {M : ℕ →Side}

abbrev Shirley (n : ℕ) := Ports (n+1) (2-n)

def melon : (n : ℕ) → Shirley n → Stitch (n+1)
  | 0 => roller (t:=1) (n:=2) ![0,1]
  | n+1 => winglet _ _

lemma melon_short {n} (he : n≤2) (z : Shirley n) (i) : (melon n z i).length ≤ 1 := by
  match n with
  | 0 => fin_cases i <;> simp [melon,roller,tabsZ,List.finRange]
  | k+1 => exact (roller_ge _ _ _).trans (by omega)
lemma melon_card {n} (he : n≤2) (z : Shirley n) : (n+2)+(∑ j,(melon n z j).length)=4 := by
  match n with
  | 0 => unfold melon; rw [roller_extent]
  | k+1 => unfold melon winglet; rw [roller_extent]; omega

abbrev Mockup (G : Gauge) (n : ℕ) := Needle (Shirley n) (Loc G 1) (n+1)

def Fruit (U : ∀ n, Mockup G n) (σ C : ℝ) := ∀ i ≤ 2, Dai (U i) σ C
def Syrupy (X : ∀ i,Link G (M i) →ℝ) (U : ∀ n,Mockup G n) := ∀ i n,n≤2 → Bitter (melon n) (U n) (creme n) (X i)
lemma fruit_mono {U : ∀ n,Mockup G n} (h : Fruit U σ C) (he : η≤σ) (hp : C≤A) : Fruit U η A := fun _ a i j=> (h _ a i j).mono he hp
lemma loanChar (G : Gauge) (n : ℕ) (he : n≤2) (hs : 0<σ) : ∃ η C,0<η ∧ 0≤C ∧ ∀ (A : ℝ), 0≤A →
    ∀ M : ℕ→Side,∀ U : ∀ i,Link G (M i)→ℝ, (∀ i,AnalyticAt ℝ (U i) 0 ∧ fderiv ℝ (U i) 0=0) →
    (∀ j,0<j → j≤3 → Drinkable j M U (3-j) σ A) → ∃ k : Mockup G n, Dai k η (A*C) ∧ ∀ i,Bitter (melon n) k (creme n) (U i) := by
  let w := calls ((n+1)+1) σ
  have ht : 0<w := by unfold w calls; positivity
  have h : ∃ η K : ℝ,0<η ∧ 0≤K ∧ ∀ (A : ℝ),0≤A → ∀ (F : Picture G (n+1)),
      (∀ i j,Firm w A (F i j) ∧ Rays (2-n) (F i j ∘ axes)) → ∃ k : Mockup G n,Dai k η (A*K) ∧ Spool F (melon n) k := by
      match n with
      | 0 => exact windTwin _ _ ht
      | k+1 => exact winding _ _ ht
  obtain ⟨η,K,hη,hk,H⟩ := h
  let D := pintCost (creme n) G
  have hc : 0≤D := sum_nonneg (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨η,D*K,hη,mul_nonneg hc hk,fun A hA M U hp hy => ?_⟩
  obtain ⟨Y,hY,hE⟩ := wedlock U (v:=creme n) (u:=2-n) (fun k hk hw=> (hy k hk (by omega)).thins hs le_rfl le_rfl (by omega)) (fun i=>(hp i).2) (fun i=>(hp i).1) hs hA
  obtain ⟨a,ha,hK⟩ := H (A*D) (mul_nonneg hA hc) Y hE
  exact ⟨a,(mul_assoc A D K) ▸ ha,fun i => nectar ha hη hK (hY i)⟩

lemma blenderBar (G : Gauge) (hs : 0<σ) : ∃ η C,0<η ∧ 0≤C ∧ ∀ (A : ℝ), 0≤A →
    ∀ M : ℕ→Side,∀ U : ∀ i,Link G (M i)→ℝ, (∀ i,AnalyticAt ℝ (U i) 0 ∧ fderiv ℝ (U i) 0=0) →
    (∀ j,0<j → j≤3 → Drinkable j M U (3-j) σ A) → ∃ k : ∀ n,Mockup G n,Fruit k η (A*C) ∧ Syrupy U k := by
  obtain ⟨x,V,hx,hV,H⟩ := loanChar G 0 (by decide) hs
  obtain ⟨y,W,hy,hW,T⟩ := loanChar G 1 (by decide) hs
  obtain ⟨z,X,hz,hX,P⟩ := loanChar G 2 le_rfl hs
  let η := min x (min y z)
  let D := V+W+X
  refine ⟨η,D,lt_min hx (lt_min hy hz),by unfold D; positivity,fun A hA M U hp hu => ?_⟩
  obtain ⟨a,ha,H1⟩ := H _ hA _ U hp hu
  obtain ⟨b,hb,H2⟩ := T _ hA _ U hp hu
  obtain ⟨c,hc,H3⟩ := P _ hA _ U hp hu
  let k (n : ℕ) : Mockup G n := match n with
    | 0=> a | 1=>b | 2=>c | n+3=>0
  have hη : η ≤ min y z := min_le_right ..
  refine ⟨k,fun i hi => ?_,fun v n hn => ?_⟩
  · interval_cases i
    · exact fun p q => (ha p q).mono (min_le_left ..) (mul_le_mul_of_nonneg_left (by unfold D; linarith) hA)
    · exact fun p q => (hb p q).mono (hη.trans (min_le_left ..)) (mul_le_mul_of_nonneg_left (by unfold D; linarith) hA)
    exact fun p q => (hc p q).mono (hη.trans (min_le_right ..)) (mul_le_mul_of_nonneg_left (by unfold D; linarith) hA)
  interval_cases n; exacts [H1 v,H2 v,H3 v]

def RippleF (U : ∀ n,Mockup G n) (Φ : Bridge G P) : Spark (Loc G 1) G P := recitalX (fun n => if n≤2 then ripple Φ (melon n) (U n) else 0)
lemma cooking {Φ : Bridge G P} {U : ∀ n,Mockup G n} (h : Cruise Φ 1 σ D) (hp : σ≤1) (hs : 0<σ) (hc : 0≤C) (he : Fruit U (inch P.L*σ) C) : Keels (RippleF (G:=G) U Φ) σ
    (feeHead (fun n=>roundBay G (n+1) (Shirley n) C σ ((ruffle D)^(n+2)))) := by
  unfold Keels RippleF; apply serial_caps
  · refine cosmic _ ?_ ?_
    · intro n p r i q z h1 h2 w1 w2 w3; split
      next hn => exact ripple_flip _ _ _ h.1 p r i w1 h1 h2
      rfl
    intro X _ _ x n p q a h1 h2 h3 hP hQ
    by_cases H : n ≤ 2
    · simp_rw [if_pos H]; exact ripple_bill _ _ _ p a q x hP hQ h1 h2 h3 h.1 (he _ H) hs
    simp_rw [if_neg H]; exact BillD.park x (0:_)
  intro n hn i v hw p hv hz; rw [if_pos hn]; exact (ripple_cash _ _ _ h hs hp (he n hn) hc (melon_short hn) (melon_card hn) _ _ hw _ hv hz).mono (fee_ge (fun n=>roundBay G (n+1) (Shirley n) C σ ((ruffle D)^(n+2))) hn)
end YM.Stationary
end
