import YM.Next.STATIONARY.Films.LeadingRay
import YM.Next.STATIONARY.OneLoop.Lattice
import YM.Next.STATIONARY.Shape.VertexWeights

set_option autoImplicit false
/-!
# Coupled vertical Stationary-Hessian source, real & Fourier. Orbits at
 foreground variable (not the frame K orientation mask). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {n : ℕ} {c f : Side} {S : StepData c f}

section leg
-- s(x,y)_p. convention from first position.

def quarks {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (T : RecordM ℂ (Fin 3) α) (W : Phase β→ₗ[ℂ] Phase α) (x y : Phase α) : Phase β := fun i => T ![W (Pi.single i 1),x,y]
lemma quarks_act {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (T : RecordM ℂ (Fin 3) α) (W : Phase β→ₗ[ℂ] Phase α) (x y : Phase α) (v) : dotProduct v (quarks T W x y)=T ![W v,x,y] := by
  let L : Phase β→ₗ[ℂ] ℂ := (T.toLinearMap ![0,x,y] 0).comp W
  have he u : L u=T ![W u,x,y] := by
    unfold L; rw [LinearMap.comp_apply,MultilinearMap.toLinearMap_apply]; congr 1
    ext1 i; fin_cases i <;> simp
  unfold quarks dotProduct; simp_rw [← he]
  conv_rhs => rw [show v=∑ i : β,v i • Pi.single i (1:ℂ) by ext i; simp [Finset.sum_apply,Pi.single_apply], map_sum]
  simp_rw [map_smul]; rfl

instance (G : Gauge) (L : Side) : DecidableEq (ParcelG G L) := fun a b => instDecidableEqSum a b

def scenicOrbit (G : Gauge) (S : StepData c f) : Phase (Co c (ParcelG G S.patch.L))→ₗ[ℂ] Phase (Co c (Atrium G S.patch)) := spinGather (scenic S.patch)
lemma scenicOrbit_axes (G : Gauge) (S : StepData c f) (x) : scenicOrbit G S (axes x)=axes (torsionX G S x) := by
  ext1 j; rcases j with ⟨j,b|b⟩
  · change (0:ℂ)= ↑(0:ℝ); simp
  change _= ((directX G S ((directX G S).symm x) _:ℝ):ℂ); rw [ContinuousLinearEquiv.apply_symm_apply]; rfl

variable (S) (t : S.Choices) (p : Clip) (R : PathData G) (W : Matrix (Body 1 f) (Body 1 c) ℝ)
variable (U : Phase (Lines G c 1) →ₗ[ℂ] Phase (Co c (Atrium G S.patch)))

def spectrumS (x y) := quarks (beat (centR S t p R) 0 3) (scenicOrbit G S) (U x) (U y)

lemma spectrum_real (h : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A C) (he : ∀ a,U (axes a)=axes (ascentX S W a)) (x y) : spectrumS S t p R U (axes x) (axes y)= axes (fragment S t p R W x y ∘ (clothe G S).symm) := by
  ext1 i; rw [spectrumS, he, he,quarks]; let T := (tourG G S).symm; let L := clothe G S
  let z : GateR G S := torsionX G S (Pi.single i 1)
  let Q : Vault G c f := helmets G c f (L.symm i); let V : Fin 3 → GateR G S := ![z,ascentX S W x,ascentX S W y]; let M := merit S t p R
  have hZ : T z=(0,Q) := by
    let d := directX G S
    change (tourG G S).symm (tourG G S (0,d.symm _))=(0,Q); rw [ContinuousLinearEquiv.symm_apply_apply]
    have hv : d Q=Pi.single i 1 := by
      have he j : cash (helmets G c f) Q j=if j=L.symm i then 1 else 0 := by simp [cash,Q,eq_comm]
      funext b; rw [show d=directX G S from rfl,direct_pay]; simp only [Function.comp_apply,Pi.single_apply]; change cash _ Q (L.symm b)=_; rw [he]; simp
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hx u : T (ascentX S W u)= saluteLe W u := (tourG G S).symm_apply_apply _
  rw [show (Pi.single i (1:ℂ))=axes (Pi.single i 1) by ext b; simp [axes,Pi.single_apply, apply_ite]]
  have hV : axes ∘ V= ![axes (torsionX G S (Pi.single i 1)), axes (ascentX S W x), axes (ascentX S W y)] := funext fun j => by fin_cases j <;> rfl
  rw [scenicOrbit_axes,← hV,beat_real]; unfold axes
  apply congr_arg ((↑):ℝ→ℂ); change iteratedFDeriv ℝ 3 (M ∘ T.toContinuousLinearMap) 0 V=_; rw [show iteratedFDeriv ℝ 3 _ _ _= _ from wired T.toContinuousLinearMap (f:=M) (x:=0) (by rw [map_zero]; exact (merit_diff h t hp).analyticAt) 3 V, map_zero]; unfold Function.comp; change iteratedFDeriv ℝ 3 M _ _= iteratedFDeriv ℝ 3 M _ _; congr 1; ext1 i; change T (V i)=_; fin_cases i; exacts [hZ,hx _,hx _]
end leg
end YM.Stationary
end

/-!
# Harvest classical source on both frequencies. Sign order invariant under
 mesh aliases, no unfolding into reciprocal sheet of analytic telescope.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {c f : Side} {p : Clip} {R : PathData G} {q z : Momentum}

section engaged
variable (Q : TextS 3 P G) (Φ : Bridge G P)

def vergeP (p q : Momentum) (a b : Loc G 1) := quarks (Q ![-(p+q),p,q]) (scenic P) (celestial Φ p (Pi.single a 1)) (celestial Φ q (Pi.single b 1))
lemma withal (p r t : Momentum) (hp : p∈ strip σ) (hq : r∈strip σ) (ht : t∈strip σ) (i : Fin 3) : (![p,r,t]:Fin 3→Momentum) i∈strip σ := by fin_cases i <;> assumption
lemma verge_green (h : Fresh (celestial Φ) σ) (hf : Pungent Q σ) (hp : q∈strip σ) (he : z∈strip σ) (hv : q+z ∈ strip σ) (i j) :
    DifferentiableAt ℂ (fun x : Momentum × Momentum => vergeP Q Φ x.1 x.2 i j) (q,z) := by
  let H := fun x : Momentum × Momentum => (![ -(x.1+x.2),x.1,x.2] : Fin 3→ Momentum)
  refine differentiableAt_pi.mpr fun u => ?_
  let V x : Fin 3→Phase (Atrium G P) := ![scenic P (Pi.single u 1),celestial Φ (Prod.fst x) (Pi.single i 1),celestial Φ (Prod.snd x) (Pi.single j 1)]
  have ht : ∀ l,H (q,z) l∈strip σ := withal _ _ _ (negResident hv) hp he
  apply (hf.hol ht (V (q,z))).comp (f:=fun x=> (H x,V x)) (q,z); refine DifferentiableAt.prodMk (differentiableAt_pi.mpr ?_) (differentiableAt_pi.mpr ?_)
  · intro i; fin_cases i <;> simp [H]
  intro i'; fin_cases i' <;> simp only [V]
  exact differentiableAt_const _
  exact (h.sense hp (Pi.single i 1)).comp (f:=Prod.fst) (q,z) differentiableAt_fst
  exact (h.sense he (Pi.single j 1)).comp (f:=Prod.snd) (q,z) differentiableAt_snd

lemma verge_resets (h : Fresh (celestial Φ) σ) (hf : Pungent Q σ) (p q r t : Momentum) (hp : p∈ strip σ) (he : q∈ strip σ) (hv : p+q∈strip σ) (h1 : rolls p r) (h2 : rolls q t) (a b) : vergeP Q Φ p q a b=vergeP Q Φ r t a b := by
  unfold vergeP; rw [h.shifts h1 hp,h.shifts h2 he]
  rw [hf.shifts _ ![ -(r+t),r,t] ?_ ?_]
  · intro i; fin_cases i; exacts [(h1.plus h2).neg,h1,h2]
  exact withal _ _ _ (negResident hv) hp he

-- unit duality tests for estimate. Using rank-1 object steering avoids paying basis cost # α.
lemma vigor_pays {α : Type} [Fintype α] [DecidableEq α] (X : Slab α) (p) (u : Phase α) (he : 0≤C) (h : ∀ v, X.rate (-p) v≤1 → ‖dotProduct v u‖≤C) : X.dual.rate p u ≤ C := by
  let W : Slab Unit := Slab.basic Unit
  let M : CompM α Unit := Matrix.of fun a _ => u a
  have hx (x : Phase Unit) : M*ᵥ x=x () • u := by ext1 i; simp [Matrix.mulVec,dotProduct, M,mul_comm]
  have hz (x : Phase Unit) : W.rate p x= ‖x ()‖ := by unfold W; rw [Slab.basic_rate]; apply (sq_eq_sq₀ (slug_nonneg _) (by positivity)).1; simp [slug_sq]
  have hp := stands_echo M (X:=X) (Y:=W) (q:=p) (p:=p) he (fun v w hv hw => by rw [hx,dotProduct_smul,norm_smul, mul_comm]; rw [hz] at hw; exact (mul_le_of_le_one_right (by positivity) hw).trans (h v hv))
  have ht := Slab.serial_at hp (fun _ => (1:ℂ)); rw [hx,hz] at ht; simpa using ht

lemma verge_fee (h : Laureate Q Φ σ C) (p q : Momentum) (hp : p∈ strip σ) (he : q∈ strip σ) (hv : p+q∈strip σ) (a b) : (slabW G P.L).dual.rate (p+q) (vergeP Q Φ p q a b)≤ C := by
  apply vigor_pays _ _ _ h.fund; intro v hv'
  unfold vergeP; rw [quarks_act]
  let x := celestial Φ p (Pi.single a 1); let y := celestial Φ q (Pi.single b 1)
  refine h.peak _ (withal _ _ _ (negResident hv) hp he) ![x,y] (fun i=> ?_) v hv'
  fin_cases i; exacts [⟨a,rfl⟩,⟨b,rfl⟩]
end engaged

section exact
variable (S : StepData c f) (t : S.Choices) (Φ : Bridge G S.patch) (Q : TextS 3 S.patch G) (U : Phase (Lines G c 1) →ₗ[ℂ] Phase (Co c (Atrium G S.patch)))

lemma verge_wave (he : Skimming S Q (centR S t p R)) (h : ∀ i : Site c,∀ q,rolls (mon i) q → ∀ v,U (tune i v)= tune i (celestial Φ q v))
    (x y : Site c) (r s : Momentum) (hr : rolls (mon x) r) (hs : rolls (mon y) s) (a b : Loc G 1) :
    spectrumS S t p R U (relay x a) (relay y b) = tune (x+y) (vergeP Q Φ r s a b) := by
  classical
  let X:= celestial Φ r (Pi.single a 1); let Y:= celestial Φ s (Pi.single b 1)
  have hk := h x r hr; have hh := h y s hs
  apply ray_book; intro k v
  unfold spectrumS relay; rw [quarks_act,hk,hh]
  have hu (p' : Momentum) (hp : rolls (mon k) p') := he.beatUp ![k,x,y] ![p',r,s] (fun i => by fin_cases i; exacts [hp,hr,hs]) ![scenic S.patch v,X,Y]
  have hK : scenicOrbit G S (tune k v)=tune k (scenic S.patch v) := spinMoves _ k _
  let V := vergeP Q Φ r s a b
  have hy (z) (hp : rolls (mon k) z) : beat (centR S t p R) 0 3 ![scenicOrbit G S (tune k v),tune x X,tune y Y]= if k+(x+y)=0 then (Fintype.card (Site c):ℂ)* Q ![z,r,s] ![scenic S.patch v,X,Y] else 0 := by
      have HH := hu z hp
      rw [show (fun i => tune ((![k,x,y]:Fin 3 →_) i) ((![scenic S.patch v,X,Y]:Fin 3→_) i))=![tune k (scenic S.patch v),tune x X,tune y Y] by ext1 i; fin_cases i <;> rfl,show (∑ i : Fin 3, (![k,x,y]:Fin 3→_) i)=k+(x+y) by simp [Fin.sum_univ_succ]] at HH
      rw [hK]; exact HH
  rw [ray_dots]; split
  next hp =>
    change beat (centR _ _ _ _) _ 3 ![scenicOrbit _ _ _,tune x X,tune y Y]=_
    have hx : rolls (mon k) (-(r+s)) := by rw [eq_neg_of_add_eq_zero_left hp]; exact (hr.combine hs).flip_sign
    rw [hy _ hx, if_pos hp]
    exact congr_arg ((Fintype.card (Site c):ℂ)*·) (quarks_act _ _ _ _ _ |>.symm)
  next hp => exact (hy (mon k) (rolls.refl _)).trans (if_neg hp)
end exact
end YM.Stationary
end

/-!
# Complexified Q-leg exchange has counting determinant in exact pairing.
Nested cast implicit preserves volleys at all pure phases by extension.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {n : ℕ} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G}

section spectrum
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
lemma quarkLine (T : RecordM ℂ (Fin 3) α) (W : Phase β→ₗ[ℂ] Phase α) :
    (∀ x, IsLinearMap ℂ (fun y=> quarks T W x y)) ∧ (∀ y,IsLinearMap ℂ (fun x=> quarks T W x y)) := by
  have he (u v w : Phase α) : IsLinearMap ℂ (fun x => T ![u,x,w]) ∧ IsLinearMap ℂ (fun x => T ![u,v,x]) := by
    let M := ![u,v,w]
    have H (j) : IsLinearMap ℂ (⇑(T.toLinearMap M j)) := (T.toLinearMap M j).isLinear
    have hy (x) : (T.toLinearMap M 1) x=T ![u,x,w] := by rw [T.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp [M]
    have hz (x) : (T.toLinearMap M 2) x=T ![u,v,x] := by rw [T.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp [M]
    exact ⟨(funext hy) ▸ H 1,(funext hz) ▸ H 2⟩
  refine ⟨fun x => ⟨fun a b => ?_, fun c a=> ?_⟩,fun x=>⟨fun a b => ?_,fun c a=> ?_⟩⟩ <;> funext i
  exacts [(he _ x 0).2.1 a b,(he _ x 0).2.2 c a,(he _ 0 x).1.1 a b,(he _ 0 x).1.2 c a]

lemma richFour (F : Phase α→Phase α→Phase β) (hf : ∀ x,IsLinearMap ℂ (F x)) (ht : ∀ y,IsLinearMap ℂ (fun x => F x y)) (A : CompM β β) :
    ∃ M : RecordM ℂ (Fin 4) α, ∀ v,M v=dotProduct (F (v 0) (v 1)) (A*ᵥ (F (v 2) (v 3))) := by
  refine ⟨{ toFun := fun v=> dotProduct (F (v 0) (v 1)) (A*ᵥ (F (v 2) (v 3)))
            map_update_add' := ?_
            map_update_smul' := ?_ },fun _=> rfl⟩
  · let D : DecidableEq (Fin 4) := inferInstance
    intro I v i a b; have hp : I=D := Subsingleton.elim ..; subst I; unfold D; fin_cases i
    all_goals simp [hf _|>.1 .., ht _|>.1 .., Matrix.mulVec_add, add_dotProduct,dotProduct_add]
  let D : DecidableEq (Fin 4) := inferInstance
  intro I v i c a; have h : I=D := Subsingleton.elim ..; subst I; unfold D; fin_cases i
  all_goals simp [hf _|>.2 .., ht _|>.2 .., Matrix.mulVec_smul, smul_dotProduct,dotProduct_smul]
end spectrum

variable (S) (t : S.Choices) (U : Phase (Lines G c 1) →ₗ[ℂ] Phase (Co c (Atrium G S.patch)))

def bangStroke (p : Clip) (R : PathData G) (n) : RecordM ℂ (Fin n) (Lines G c 1) := (beat (centR S t p R) 0 n).compLinearMap fun _ => U

def fieldPulse (p : Clip) (R : PathData G) (x y a b) := dotProduct (spectrumS S t p R U x y) (approached (repackM (clothe G S) (clothe G S) (commonM S t p R (inch S.patch.L))⁻¹)*ᵥ (spectrumS S t p R U a b))
variable {S}
lemma worked {W} (h : ∀ x,U (axes x)=axes (ascentX S W x)) (he : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A C) (v : Fin n→Link G c) :
    bangStroke S t U p R n (axes ∘ v)= ↑(iteratedFDeriv ℝ n (merit S t p R) 0 (fun i=> saluteLe W (v i))) := by
  unfold bangStroke; rw [MultilinearMap.compLinearMap_apply,show (fun i : Fin n => U ((axes∘v) i))=axes∘(ascentX S W∘v) from funext fun i=> h _,beat_real]; apply congr_arg ((↑):ℝ→ℂ)
  let T := tourG G S
  change iteratedFDeriv ℝ n (merit S t p R ∘ T.symm.toContinuousLinearMap) 0 _=_; rw [wired T.symm.toContinuousLinearMap (by rw [map_zero]; exact (merit_diff he t hp).analyticAt),map_zero]; congr 1; ext1 i; exact T.symm_apply_apply _
lemma field_work {W} (h : ∀ x,U (axes x)=axes (ascentX S W x)) (he : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A C) (x y a b) :
    fieldPulse S t U p R (axes x) (axes y) (axes a) (axes b) = ↑(amount S t p R (inch S.patch.L) W x y a b) := by
  unfold fieldPulse amount; simp_rw [spectrum_real S t p R W U he hp h, prom_vec,repack_act]
  rw [show dotProduct _ _ = ↑(dotProduct (fragment S t p R W x y ∘ (clothe G S).symm) _) from ?_, ← repack_dot]
  simp [axes,dotProduct]
-- permutation order in triumph4.


lemma firePulse (hp : R.Bounds p σ A C) : ∃ F : RecordM ℂ (Fin 4) (Lines G c 1),∀ v,F v= fieldPulse S t U p R (v 0) (v 1) (v 2) (v 3) :=
    by
  refine richFour (spectrumS S t p R U) ?_ ?_ _
  · intro x; refine IsLinearMap.mk (fun v w=> ?_) (fun v w=> ?_) <;> unfold spectrumS
    · rw [map_add]; exact ((quarkLine _ _).1 (U x)).1 _ _
    rw [map_smul]; exact ((quarkLine _ _).1 (U x)).2 _ _
  intro x; refine IsLinearMap.mk (fun v w=> ?_) (fun v w=> ?_) <;> unfold spectrumS
  · rw [map_add]; exact ((quarkLine _ _).2 (U x)).1 _ _
  rw [map_smul]; exact ((quarkLine _ _).2 (U x)).2 _ _
section peak
variable {ρ : fieldDir G c 1 → AxisChart G F} (h : Critical F p R ρ) (W : Matrix (Body 1 f) (Body 1 c) ℝ)
    (hk : ∀ x,U (axes x)=axes (ascentX S W x)) (hf : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A C) (hg : Guessed F W ρ)
include h W hk hf hp hg
lemma peakPulse3 : beat (victory F t p R ρ) 0 3=bangStroke S t U p R 3 := by
  apply enlarge_unique; intro v; rw [beat_real,worked t U hk hf hp]; apply congr_arg ((↑):ℝ→ℂ)
  rw [show (fun i : Fin 3 => saluteLe W (v i))=![saluteLe W (v 0),saluteLe W (v 1),saluteLe W (v 2)] by ext1 i; fin_cases i <;> rfl]
  conv_lhs => rw [show v=![v 0,v 1,v 2] by ext1 i; fin_cases i <;> rfl]; exact triumph3 h hp hf t hg ..

-- use perms explicit. second needs 0 3 1 2, third = 0213. perm proof.
def quadrant : Equiv.Perm (Fin 4) := (Equiv.swap 1 3).trans (Equiv.swap 1 2)
lemma peakPulse4 (he : PriceGap F p R η) (hη : 0<η) (v : Fin 4→Phase (Lines G c 1)) :
    beat (victory F t p R ρ) 0 4 v= bangStroke S t U p R 4 v-fieldPulse S t U p R (v 0) (v 1) (v 2) (v 3)-fieldPulse S t U p R (v 0) (v 3) (v 1) (v 2)-fieldPulse S t U p R (v 0) (v 2) (v 1) (v 3) := by
  obtain ⟨V,hV⟩ := firePulse t U hp
  let K:=Equiv.swap (1:Fin 4) 2
  let X := V.domDomCongr quadrant; let Y := V.domDomCongr K
  have hx v : X v=fieldPulse S t U p R (v 0) (v 3) (v 1) (v 2) := hV (v∘quadrant)
  have hy v : Y v=fieldPulse S t U p R (v 0) (v 2) (v 1) (v 3) := hV (v∘K)
  have hE : beat (victory F t p R ρ) 0 4=bangStroke S t U p R 4 - V-X-Y := by
    apply enlarge_unique; intro w; simp_rw [_root_.sub_apply, hx, hy,hV,worked t U hk hf hp,beat_real,Function.comp_apply, field_work t U hk hf hp, ← Complex.ofReal_sub]; apply congr_arg ((↑):ℝ→ℂ)
    rw [show (fun i : Fin 4=> saluteLe W (w i))=![saluteLe W (w 0),saluteLe W (w 1),saluteLe W (w 2),saluteLe W (w 3)] by ext1 i; fin_cases i <;> rfl]
    conv_lhs => rw [show w=![w 0,w 1,w 2,w 3] by ext1 i; fin_cases i <;> rfl]
    exact triumph4 h hp hf t hg (inch_pos S.patch.L) he hη ..
  simp_rw [hE,_root_.sub_apply,hx,hy,hV]
end peak
end YM.Stationary
end

/-!
# Reading the third and fourth analytic from stationary scene.
 Inputs angular basis and matched ζ Ticket only. TEXT Apertures use blow
 planar width controlled by σ. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {n : ℕ} {c f : Side} {p q r t : Momentum} {k : Clip} {R : PathData G}

def surfHeight (t : ℕ) (σ : ℝ) := σ/(2*(t+1:ℝ))
lemma surf_gradient (hs : 0<σ) (n : ℕ) : 0 < surfHeight n σ := by unfold surfHeight; positivity
lemma surf_le (hs : 0<σ) {p : Space n} (hp : p∈strip (surfHeight n σ)) (i) : plotted p i∈strip (σ / 2) := by
  have hv := tilted p hp (surf_gradient hs _) i
  rw [show (↑n+1)*surfHeight n σ=σ/2 by unfold surfHeight; field_simp] at hv; exact hv
lemma surf_payment {i j : Fin (n+1)} (hs : 0<σ) {p : Space n} (hp : p∈strip (surfHeight n σ)) :
    plotted p i + plotted p j∈strip σ := fun a => by
      simp only [Pi.add_apply, Complex.add_im]; exact lt_of_le_of_lt (abs_add_le ..) (by linarith only [surf_le hs hp i a, surf_le hs hp j a])
lemma surf_heat (hs : 0<σ) {p : Space n} (hp : p∈strip (surfHeight n σ)) (i) : plotted p i∈strip σ := fun a => (surf_le hs hp i a).trans_le (by linarith)

section phase
variable (Φ : Bridge G P)

def squadron (v : TextS (n+1) P G) : Picture G n := fun i b p=> v (plotted p) (fun j=> celestial Φ (plotted p j) (Pi.single (b j,i j) 1))

lemma squadFee (T : TextS (n+1) P G) (h : Pungent T σ) (hv : Laureate T Φ σ C) (hp : Fresh (celestial Φ) σ) (hs : 0<σ) :
    ∀ i j,Firm (surfHeight n σ) C (squadron Φ T i j) := by
  intro i j
  unfold squadron; refine ⟨⟨surf_gradient hs n,fun p w=> ?_,fun p w k=> ?_⟩,fun p w=> hv.plain _ (surf_heat hs w) _ fun i=> ⟨_,rfl⟩⟩
  · let v := fun p (u : Fin (n+1))=> celestial Φ (plotted p u) (Pi.single (j u,i u) 1)
    have hX (a : Fin (n+1)) : DifferentiableAt ℂ (fun x=> v x a) p := by
      have hh := hp.sense (p:=plotted p a) (surf_heat hs w a) (Pi.single (j a,i a) 1)
      exact hh.comp p (platform_diffs a p)
    exact (h.hol (surf_heat hs w) (v p)).comp p (f:=fun p=> (plotted p,v p)) ((differentiableAt_pi.mpr fun i=> platform_diffs i p).prodMk (differentiableAt_pi.mpr hX))
  have he a := projections_roll (show rolls p (p+reciprocal k) from ⟨_,rfl⟩) a
  rw [h.shifts _ _ he (surf_heat hs w)]; simp_rw [hp.shifts (he _) (surf_heat hs w _)]

abbrev SeaFoam (P : Patch) (G : Gauge) := Momentum→ CompM (ParcelG G P.L) (ParcelG G P.L)

def quake (V : SeaFoam P G) (Q : TextS 3 P G) (p : Breed 3 Momentum) (v : Breed 3 (Loc G 1)) := dotProduct (vergeP Q Φ (p 0) (p 1) (v 0) (v 1)) ((V (p 2+p 3))⁻¹ *ᵥ vergeP Q Φ (p 2) (p 3) (v 2) (v 3))
def quaver (V : SeaFoam P G) (Q : TextS 3 P G) (f : Equiv.Perm (Fin 4)) : Picture G 3 := fun i j p=> quake Φ V Q (plotted p ∘ f) (fun k=> (j (f k),i (f k)))
lemma forecast_via {α : Type} [Fintype α] [DecidableEq α] (p : Momentum) (X : Slab α) (v w : Phase α) : ‖dotProduct v w‖ ≤ X.dual.rate (-p) v*X.rate p w := by
  let Y := (X.tile p)⁻¹ *ᵥ w
  rw [Slab.rate,X.inverse_dual, neg_neg]; apply le_trans ?_ (slug_dot ((X.tile p)ᵀ *ᵥ v) Y); rw [Matrix.mulVec_transpose, ← dotProduct_mulVec]; unfold Y; rw [X.rebate]

lemma forecast {Q : TextS 3 P G} (h : Laureate Q Φ σ C) (p : Breed 3 Momentum) (w : ∀ i,p i∈strip σ) (hp : p 0+p 1+p 2+p 3=0) (hz : p 0+p 1∈strip σ) (v : Breed 3 (Loc G 1))
    (V : SeaFoam P G) (hv : Freezer (slabW G P.L|>.dual) (slabW G P.L) V σ D) (hd : 0≤D) : ‖quake Φ V Q p v‖ ≤ C*(D*C) := by
  let a:=p 0+p 1; let k:= p 2+p 3
  let x := vergeP Q Φ (p 0) (p 1) (v 0) (v 1); let y := vergeP Q Φ (p 2) (p 3) (v 2) (v 3)
  let X := slabW G P.L
  have hx : a=-k := eq_neg_of_add_eq_zero_left (by unfold a k; rw [← add_assoc]; exact hp)
  have hk : k∈strip σ := by simpa only [neg_neg] using negResident (show -k∈strip σ from hx ▸ hz)
  apply (forecast_via k X x _).trans
  have he : X.dual.rate (-k) x≤C := hx ▸ verge_fee Q Φ h (p 0) (p 1) (w 0) (w 1) hz (v 0) (v 1)
  have hy : X.rate k ((V k)⁻¹ *ᵥ y)≤ D*C := (Slab.serial_at (hv.price k hk) y).trans (mul_le_mul_of_nonneg_left (verge_fee Q Φ h (p 2) (p 3) (w 2) (w 3) hk (v 2) (v 3)) hd)
  exact mul_le_mul he hy (slug_nonneg _) h.fund

lemma quaverFee (T : TextS 3 P G) (h : Pungent T σ) (hp : Laureate T Φ σ C) (hf : Fresh (celestial Φ) σ) (hs : 0<σ) (V : SeaFoam P G) (he : Poster σ V) (hv : Freezer (slabW G P.L|>.dual) (slabW G P.L) V σ D) (hd : 0≤D) :
    ∀ b i j,Firm (surfHeight 3 σ) (C*(D*C)) (quaver Φ V T b i j) := by
  intro b i j
  unfold quaver; refine ⟨⟨surf_gradient hs _,fun p w=> ?_,fun p w z=> ?_⟩,fun p w=> forecast Φ hp _ (fun i=> surf_heat hs w (b i)) ?_ (surf_payment hs w) _ V hv hd⟩
  · let y x u:= plotted (x:Space 3) (b u)
    let k x:= y x 2 + y x 3
    have hk : DifferentiableAt ℂ k p := (platform_diffs _ _).add (platform_diffs _ _)
    have hu a c : DifferentiableAt ℂ (fun p=> vergeP T Φ (y p a) (y p c) (j (b a),i (b a)) (j (b c),i (b c))) p := (verge_green T Φ hf h (surf_heat hs w (b a)) (surf_heat hs w (b c)) (surf_payment hs w) _ _).comp (f:=fun x=> (y x a,y x c)) p ((platform_diffs (b a) p).prodMk (platform_diffs (b c) p))
    have hK : BillD (fun x=> (V (k x))⁻¹) p := (he.go (show k p∈strip σ from surf_payment hs w) hk).take (hv.period (k p) (surf_payment hs w))
    unfold quake; unfold Matrix.mulVec dotProduct; refine DifferentiableAt.fun_sum fun c _=> (differentiableAt_pi.mp (hu 0 1) c).mul (DifferentiableAt.fun_sum fun i _=> (hK c i).mul (differentiableAt_pi.mp (hu 2 3) i))
  · have he' i := projections_roll (show rolls p (p+reciprocal z) from ⟨_, rfl⟩) i
    unfold quake; simp_rw [Function.comp_apply]; rw [he.shifts ((he' (b 2)).plus (he' (b 3))) (surf_payment hs w), verge_resets T Φ hf h _ _ _ _ (surf_heat hs w (b 0)) (surf_heat hs w (b 1)) (surf_payment hs w) (he' _) (he' _),verge_resets T Φ hf h _ _ _ _ (surf_heat hs w (b 2)) (surf_heat hs w (b 3)) (surf_payment hs w) (he' _) (he' _)]
  rw [show _ +_=∑ j,(plotted p ∘ b) j by simp [Fin.sum_univ_succ, add_assoc],show ∑ j,(plotted p ∘ b) j =∑ j,plotted p j from Equiv.sum_comp b (plotted p)]
  simp [plotted,missing,Fin.sum_univ_succ, projected]
end phase
end YM.Stationary
end

/-!
# Picture wings deployed on BOTH path widths bouth's quotes.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {n : ℕ} {c f : Side} {p : Clip} {R : PathData G}
section exact
variable {S : StepData c f} (t : S.Choices) (U : Phase (Lines G c 1) →ₗ[ℂ] Phase (Co c (Atrium G S.patch)))
variable {Φ : Bridge G S.patch} (hU : ∀ a : Site c,∀ q,rolls (mon a) q →∀ v,U (tune a v)=tune a (celestial Φ q v))
include hU
lemma full_tex {Y : TextS (n+1) S.patch G} (h : Skimming S Y (centR S t p R)) (v : Ink G (n+1)) (i : Run (n+1)) (q) :
    bangStroke S t U p R (n+1) (glyph q v i)= collected (squadron Φ Y) q v i := by
  let V (p' : Breed n Momentum) (j) := celestial Φ (p' j) (Pi.single (i j,v j) 1)
  have hb (p' : Breed n Momentum) (he : ∀ j,rolls (mon (q j)) (p' j)) : bangStroke S t U p R (n+1) (glyph q v i)=if ∑ i,q i=0 then (Fintype.card (Site c):ℂ)* Y p' (V p') else 0 := by
    unfold bangStroke; rw [MultilinearMap.compLinearMap_apply]; unfold glyph relay; simp_rw [hU _ _ (he _)]; exact h.beatUp q p' he (V p')
  unfold collected; split
  next he => exact (hb (plotted (outphase q)) (fun j=> (ties he j).symm)).trans (if_pos he)
  next he => exact (hb (mon∘q) (fun j=> rolls.refl _)).trans (if_neg he)

def shaftInv (S : StepData c f) (t : S.Choices) (p : Clip) (R : PathData G) (V : SeaFoam S.patch G) := Jaunt (approached (repackM (clothe G S) (clothe G S) ((commonM S t p R (inch S.patch.L))⁻¹))) (fun p=> (V p)⁻¹) 0
lemma quavSpike {Y : TextS 3 S.patch G} (h : Skimming S Y (centR S t p R)) (V) (hp : shaftInv S t p R V) (v : Ink G 4) (i : Run 4) (q : Fin (3+1)→ Site c) (b : Equiv.Perm (Fin 4)) :
    fieldPulse S t U p R (glyph q v i (b 0)) (glyph q v i (b 1)) (glyph q v i (b 2)) (glyph q v i (b 3))=collected (quaver Φ V Y b) q v i := by
  let a j := q (b j)
  let z (j : Fin 4) := ((i (b j),v (b j)):Loc G 1)
  have hy : ∑ j,q j=a 0+a 1+a 2+a 3 := (Equiv.sum_comp b q).symm.trans (by simp [a,Fin.sum_univ_succ, add_assoc])
  have hX (p' : Fin 4→Momentum) (he : ∀ j,rolls (mon (a j)) (p' j)) : fieldPulse S t U p R (relay (a 0) (z 0)) (relay (a 1) (z 1)) (relay (a 2) (z 2)) (relay (a 3) (z 3))= if ∑ j,q j=0 then (Fintype.card (Site c):ℂ)*quake Φ V Y p' z else 0 := by
    unfold fieldPulse; rw [verge_wave S t Φ Y U h hU _ _ _ _ (he 0) (he 1),verge_wave S t Φ Y U h hU _ _ _ _ (he 2) (he 3)]
    unfold shaftInv at hp; rw [hp _ _ ((he 2).combine (he 3)),add_zero,ray_dots,hy,← add_assoc]; rfl
  unfold collected; split
  next hx => exact (hX ((plotted (outphase q))∘ b) (fun j=> (ties hx (b j)).symm)).trans (if_pos hx)
  next hx => exact (hX (mon ∘ a) (fun j=> rolls.refl _)).trans (if_neg hx)
end exact
section amplit

def pureStroke (Φ : Bridge G P) (Y : TextS 3 P G) : Picture G 2 := ((3:ℕ).factorial:ℂ)⁻¹ • squadron Φ Y
def pressStroke (Φ : Bridge G P) (Y : TextS 3 P G) (L : TextS 4 P G) (V : SeaFoam P G) : Picture G 3 := ((4:ℕ).factorial:ℂ)⁻¹ • (squadron Φ L-quaver Φ V Y (Equiv.refl _)-quaver Φ V Y quadrant-quaver Φ V Y (Equiv.swap 1 2))

variable {S : StepData c f} {F : Forest S.ratio} (t : S.Choices) {Φ : Bridge G S.patch} {ρ : fieldDir G c 1→ AxisChart G F} {Y : TextS 3 S.patch G}
    (h : Critical F p R ρ) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (hf : Premise S W Φ) (hv : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A D) (hk : Guessed F W ρ) (he : Skimming S Y (centR S t p R))
include h hf hv hp hk he
lemma pure_beat : Recorded (pureStroke Φ Y) (victory F t p R ρ) 0 := by
  apply (record_exact ..).2; intro q v i
  obtain ⟨U,hU,u⟩ := (celestial_scene S Φ W hf).basis
  rw [noteAt,peakPulse3 t U h W hU hv hp hk,_root_.smul_apply, show bangStroke _ _ _ _ _ _ _= _ from full_tex t U u he v i q]; unfold pureStroke collected; split <;> simp [mul_left_comm]
lemma press_beat {T : TextS 4 S.patch G} {V} (ht : Skimming S T (centR S t p R)) (hw : 0<η) (ha : PriceGap F p R η) (hB : shaftInv S t p R V) :
    Recorded (pressStroke Φ Y T V) (victory F t p R ρ) 0 := by
  obtain ⟨U,hU,H⟩ := (celestial_scene S Φ W hf).basis
  refine (record_exact ..).2 fun q v i => ?_
  change ((4:ℕ).factorial:ℂ)⁻¹*beat (victory F t p R ρ) 0 4 (glyph q v i)=_
  rw [peakPulse4 t U h W hU hv hp hk ha hw, show bangStroke _ _ _ _ _ _ _ = _ from full_tex t U H ht v i q]
  -- permutation Quart def eras
  have hx := quavSpike t U H he V hB v i q
  rw [show fieldPulse _ _ _ _ _ (glyph q v i 0) (glyph q v i 1) (glyph q v i 2) (glyph q v i 3)= _ from hx (Equiv.refl _)]
  rw [show fieldPulse _ _ _ _ _ (glyph q v i 0) (glyph q v i 3) (glyph q v i 1) (glyph q v i 2)= _ from hx quadrant]
  rw [show fieldPulse _ _ _ _ _ (glyph q v i 0) (glyph q v i 2) (glyph q v i 1) (glyph q v i 3)= _ from hx (Equiv.swap 1 2)]
  unfold collected; split <;> simp [pressStroke, mul_sub,mul_left_comm]
end amplit
end YM.Stationary
end

/-!
# Classical transition wp on this donated graph (needs for output pricing).
 No Λ or patch constants from determinant feed back into schedule here. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ w C D A τ η : ℝ} {p : Clip} {R : PathData G} {n m : ℕ→Side}

lemma shaftPorts {T B : Bed} {α : Eye (Loc G 1) (Acts G P)} {M : Spark (Loc G 1) G P} {Q : PostCard R p P K α M m n} (X : TicketPost Q η B T) (hη : 0<η) (h : P.Branches K G) (he : R.Bounds p σ C D) (i) :
    shaftInv (Q.ship.boot i) (Q.tags i) p R (medalF α false M K.penalty).tab := by
  let S := Q.ship.boot i; let t := Q.tags i; let L := Q.L i
  let e := clothe G S
  let U x := medals S t p R (inch P.L) (buffOn S t G false) (input G (m i) (L x).1.1) (headOn S t false (L x))
  have heX x : (L x).2.1=0 := congr_arg Prod.fst (Q.bare i x)
  have hf : Ticket (medalF α false M K.penalty) (fun x => repackM e e (U x)) := rewarded S h t false L he heX (Q.tilts i) (Q.meets i)
  have hk : U 0=commonM S t p R (inch P.L) := by unfold U; rw [zero_hat S h, map_zero]; simp only [Prod.fst_zero,input_zero]; rfl
  have ht : IsUnit (U 0).det := hk.symm ▸ (moment_track (X.decor i) h he t (inch_pos _) (X.health i) hη).1.ne'.isUnit
  have hb := (backRepacked e hf ht).tab; unfold cardM at hb; dsimp only at hb; rw [hk] at hb; exact hb

lemma pennies {Φ : Bridge G P} {U : TextS 3 P G} {T : TextS 4 P G} (V : SeaFoam P G) {σ C D E} (h : Fresh (celestial Φ) σ) (hs : 0<σ) (hx : Pungent U σ) (hy : Pungent T σ) (hp : Laureate U Φ σ C) (hq : Laureate T Φ σ D) (he : Poster σ V) (hb : Freezer (slabW G P.L|>.dual) (slabW G P.L) V σ E) (hE : 0≤E) :
    (∀ i j,Firm (surfHeight 2 σ) (C/6) (pureStroke Φ U i j)) ∧ (∀ i j,Firm (surfHeight 3 σ) ((D+3*(C*(E*C)))/24) (pressStroke Φ U T V i j)) := by
  have h₁ := squadFee Φ U hx hp h hs
  have h₂ := squadFee Φ T hy hq h hs
  have hV := quaverFee Φ U hx hp h hs V he hb hE
  constructor
  · intro i j
    unfold pureStroke; simp only [Pi.smul_apply]
    convert (Firm.const (surf_gradient hs 2) (((3:ℕ).factorial:ℂ)⁻¹)).mul (h₁ i j) using 1
    · norm_num [Nat.factorial]; ring
    rfl
  intro i j; unfold pressStroke; simp only [Pi.smul_apply,Pi.sub_apply]
  convert (Firm.const (surf_gradient hs 3) (((4:ℕ).factorial:ℂ)⁻¹)).mul ((((h₂ i j).sub (hV (Equiv.refl _) i j)).sub (hV quadrant i j)).sub (hV (Equiv.swap 1 2) i j)) using 1
  · norm_num [Nat.factorial]; ring
  rfl

section pos
lemma exchangeYield {Φ : Bridge G P} {U : TextS 3 P G} {V : TextS 4 P G} {α : Eye (Loc G 1) (Acts G P)} {M : Spark (Loc G 1) G P} {Q : PostCard R p P K α M m n} {B T : Bed} (X : TicketPost Q η B T) (hp : P.Branches K G) (ht : R.Bounds p τ A C)
    (hη : 0<η) {σ A' C'} (hs : 0<σ) (h : Fresh (celestial Φ) σ) (hv : ∀ i,Premise (Q.ship.boot i) (X.mat i) Φ) (hx : Pungent U σ) (hy : Pungent V σ) (hU : Laureate U Φ σ A') (hV : Laureate V Φ σ C')
    (he : Poster σ (medalF α false M K.penalty).tab) (hf : GrantF P K α M B σ D) (hd : 0≤D) (hK : ∀ i, Skimming (Q.ship.boot i) U (centR (Q.ship.boot i) (Q.tags i) p R) ∧ Skimming (Q.ship.boot i) V (centR (Q.ship.boot i) (Q.tags i) p R)) :
    let E i := victory (X.tree i) (Q.tags i) p R (X.graph i)
    HasRecord E (surfHeight 2 σ) (A'/6) 2 ∧ HasRecord E (surfHeight 3 σ) ((C'+3*(A'*(D*A')))/24) 3 := by
  obtain ⟨hw,hH⟩ := pennies _ h hs hx hy hU hV he hf.medals hd
  refine ⟨⟨pureStroke Φ U,hw,fun i=> ?_⟩,⟨pressStroke Φ U V (medalF α false M K.penalty).tab,hH,fun i=> ?_⟩⟩
  · exact pure_beat (Q.tags i) (X.decor i) (X.mat i) (hv i) hp ht (X.guards i) (hK i).1
  exact press_beat (Q.tags i) (X.decor i) (X.mat i) (hv i) hp ht (X.guards i) (hK i).1 (hK i).2 hη (X.health i) (shaftPorts X hη hp ht i)
end pos
end YM.Stationary
end
