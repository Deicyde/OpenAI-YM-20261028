import YM.Next.STATIONARY.Films.LeadingRay
import YM.Next.STATIONARY.Shape.Vertex

set_option autoImplicit false
/-!
# Footprint bounds for bounded plane-density performances. pre-L.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics Metric
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {σ θ A C D γ η : ℝ}

lemma shoot {f : Momentum→ℂ} (h : Firm η C f) : ‖iteratedFDeriv ℂ 2 f 0‖ ≤ (C/(η/2))/(η/4) := by
  let F := iteratedFDeriv ℂ 1 f
  have hp:= h.width_pos
  rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.norm_map, show η/4=η/2/2 by ring]
  have hz a (hb : a∈ball (0:Momentum) η) : ContDiffAt ℂ ω f a := (h.analytic (air_ride (by simp) hb)).contDiffAt
  apply chord (f:=F) (x:=(0:Momentum)) (R:=η/2) (by linarith) (fun p hp=> ?_) (fun p hp=> ?_) (mem_ball_self (by linarith))
  · exact ((hz p (ball_subset_ball (by linarith only [‹0<η›]) hp)).differentiableAt_iteratedFDeriv (by simp))
  unfold F; rw [norm_iteratedFDeriv_one]; exact chord h.width_pos (fun i hi=> (hz i hi).differentiableAt (by simp)) (fun i hi=> h.2 _ (air_ride (by simp) hi)) hp

def biteCost (σ A : ℝ) := (A/(σ/2/2))/(σ/2/4) * ‖axes (step (0:Axis) : Track)‖ ^ 2
lemma boundedTip {Y : Award G} (hp : Screened Y σ A) (i : G.ColorIndex) (hs : 0<σ) : |alphaPay i (profitable Y)| ≤ biteCost σ A := by
  let p : Loc G 1 := (coord 1,i)
  let X k := stock (Y p p k)
  have he := hp.earns p p; have hx := fireworks (Y p p) he (b:=σ/2) (by linarith) (by linarith)
  let f : Momentum→ℂ := (fun k => (2:ℂ)⁻¹*X k)
  have hy : Firm (σ/2) A f := (((Firm.const (by linarith : 0<σ/2) (2:ℂ)⁻¹).mul hx).mono (by linarith) le_rfl (mul_le_of_le_one_left he.budget_nonneg (by norm_num)))
  let v := (step (0:Axis) : Track)
  let L := axisCL Axis; let u := fun _ : Fin 2 => L v
  have hf : AnalyticAt ℂ f 0 := hy.analytic (hy.in_range (by simp)); have hb : AnalyticAt ℝ f 0 := ((hf.contDiffAt (n:=ω)).restrict_scalars ℝ).analyticAt
  have hp : leapTip (profitable Y) v 1 ![i,i] = ((2:ℝ)⁻¹) • (iteratedFDeriv ℂ 2 f 0 u) := by
    change speedy (f ∘ L) 2 v=_
    unfold speedy Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,wired L (by rw [map_zero]; exact hb),map_zero, ← (hf.contDiffAt (n:=(↑(2:ℕ):WithTop ℕ∞))).restrictScalars_iteratedFDeriv (𝕜:=ℝ)]
    norm_num [Nat.factorial]; rfl
  rw [alphaPay, show leapTip _ _ _ _= _ from hp]; simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_im,zero_mul, Complex.ofReal_re,sub_zero]
  rw [← mul_assoc, mul_inv_cancel₀ (by norm_num),one_mul]
  apply (Complex.abs_re_le_norm _).trans
  have hv : ∏ i : Fin 2, ‖u i‖= ‖axes v‖^2 := by simp [u]; rfl
  exact ((iteratedFDeriv ℂ 2 f 0).le_opNorm u).trans (by rw [hv]; exact mul_le_mul_of_nonneg_right (shoot hy) (sq_nonneg _))
end YM.Stationary
end

/-!
# Quote for uniform wave apertures. Consume the pre-L tickets Jen & K.
Non-root film and exact qualitative drift. Does not compute running of Π by
this call; rankCup is the same-mesh auxiliary to test there.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {σ A C D F η : ℝ}

lemma fresh_narrows {T : Eye α β} (h : Fresh T σ) (hp : η≤σ) : Fresh T η := ⟨fun p hv=> h.shifts p (fun i=>(hv i).trans_le hp),fun v x=> h.sense (fun i=> (v i).trans_le hp) x⟩

section spout
variable {m n : ℕ→Side} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {δ τ w Ω κ Λ Ξ : ℝ} {T B : Bed}
variable {M : Eye (Loc G 1) (Acts G P)} {Y : Spark (Loc G 1) G P} {Q : PostCard R p P K M Y m n} (X : TicketPost Q δ B T)
    (hk : 0<δ) (he : 0<η) (hs : η≤σ) (hw : σ ≤ 1/128) (hx : 0<w) (hp : P.Branches K G) (hS : G.Simple) (h : T.metric.strip w C)
    (hv : Tendsto (fun i=> (m i).val) atTop atTop) (hz : R.Bounds p τ Ω Λ)
    (HT : Spotlight P M σ F) (HL : Amateur G P.L σ A) (HQ : Keels Y σ Ξ)
def feast (G : Gauge) (J : ℕ) (F A Ξ k E : ℝ) := 2*tapeCost G E (mealCap G J F A Ξ k)
include hk he hs hw hx hp hS h hv hz HT HL HQ

theorem quoting (H : GrantF P K M Y B η D) (hD : 0≤D) (i : G.ColorIndex) :
    let a := feast G P.J F A Ξ K.penalty D
    let P₁ := medalCue M K.penalty Y
    let P₂ := rankCue M Y
    let c := (P.L.val:ℝ)^4*a
    Screened P₁ (η/2) c ∧ Screened P₂ (η/2) c ∧
    (∀ i j,Firm (η/2/2) c (profitable P₁ i j)) ∧
    (∀ j : ℕ, Recorded (profitable P₁) (honorarium (X.tree j) (Q.tags j) (inch P.L) p R (X.graph j))
      (cents (m j)*(royalty (η/2) c *Real.exp (-(η/2/4)*(m j).val)))) ∧
    |alphaPay i (profitable P₁)-alphaPay i (profitable P₂)| ≤
      biteCost (η/2) (reserveCost G D (mealCap G P.J F A Ξ K.penalty) (barkPay G P.J F A K.penalty)) := by
  intro a P₁ P₂ c
  have hH := he.trans_le hs
  obtain ⟨hM,hK,hP,hT⟩ := gifts_real hp HT hw he hs HL HQ H hD
  let G₁ := legPay G P.J F A K.penalty Ξ
  have hh : Play (legionF M false Y K.penalty) σ := (legion_right hp hH HT HL Y HQ).covered
  have hy := carrier_live M (fresh_narrows HT.fresh hs) (hh.mono hs) H.core
  have hl : 0<η/2 := half_pos he
  have hd := drift_tip X hk hl hx hp hS (hy.mono (half_le_self he.le)) h hv hz (hM.bound hK) i
  unfold changeCue at hd; rw [alpha_delta hl hM hK i, sub_eq_zero] at hd
  have hb := boundedTip hT i hl
  unfold stageCue at hb; rw [alpha_delta hl hK hP i] at hb
  let M₀ := mealCap G P.J F A Ξ K.penalty
  have ht : (P.L.val:ℝ)^4*tapeCost G D M₀+(P.L.val:ℝ)^4*tapeCost G D M₀=c := by unfold c a feast M₀; ring
  rw [ht] at hP hM
  let k := ((coord 0,i):Loc G 1)
  obtain ⟨W,H⟩ := profit P₁ hl ((hM.earns k k).budget_nonneg) hM.earns
  refine ⟨hM,hP,W,fun j => H _ _ ?_,?_⟩
  · exact questBright (Q.ship.boot j) (Q.tags j) (X.decor j) hz (X.health j) hk hp (X.mat j) (X.event j) (X.shades j) hS (X.guards j)
  rw [show alphaPay i (profitable P₁)=alphaPay i (profitable (coreCue M K.penalty Y)) from hd]; exact hb
end spout
end YM.Stationary
end

/-!
# Covalent pull of an amplitude. Individual aliases on any lift, no
unwrapping external pole defects. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α] {G : Gauge} {P : Patch} {σ A C D F : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum}

lemma mesh_injective {x y : Site L} (h : rolls (mon x) (mon y)) : x=y := by
  by_contra! hk; have hp := orthogonal x y; rw [if_neg hk] at hp
  have he t : cell x t=cell y t := h.exp _
  simp_rw [he,mul_inv_cancel₀ (cell_ne _ _), Finset.sum_const,card_univ,Lattice.site_card,nsmul_eq_mul,mul_one] at hp
  exact_mod_cast (pow_ne_zero 4 (side_ne L)) (by push_cast at hp; exact hp)

lemma shift_immobile {x y : Site L} (p : Momentum) (h : rolls (aliasAt p x) (aliasAt p y)) : x=y := by
  let F : Phase Unit := Pi.single () 1
  have hx : tiled p x F=tiled p y F := by ext1 i; unfold tiled; rw [h.exp]
  have ht := (untier_gear p x F).symm.trans ((congr_arg (untier p) hx).trans (untier_gear _ _ _))
  by_contra hn; have hx := congr_fun ht (x,()); simp [partitionA, F, Ne.symm hn] at hx

variable (S : StepData c f)
def duesM (a : Site c) (p : Momentum) (v : Site S.patch.L) : Site f := by
  classical
  exact if h : rolls (mon a) p then currency S.ratio a (v+wrap _ h.choose) else 0
lemma duesM_real (a : Site c) (v : Site S.patch.L) (hp : rolls (mon a) p) : rolls (mon (duesM S a p v)) (aliasAt p v) := by
  classical
  rw [duesM,dif_pos hp]; apply (currency_real S.ratio a _).trans; conv_rhs => rw [hp.choose_spec]
  exact (alias_roll ..).symm
lemma duesM_one (a : Site c) (hp : rolls (mon a) p) : Injective (duesM S a p) := by
  intro x y h; refine shift_immobile p ((duesM_real S a x hp).symm.trans ?_); rw [h]; exact duesM_real S a y hp
lemma duesM_neg (a : Site c) (hp : rolls (mon a) p) (v : Site S.patch.L) : duesM S (-a) (-p) (-v) = - duesM S a p v := mesh_injective (((duesM_real S (-a) (-v) hp.flip_sign).trans (alias_counter p v)).trans (duesM_real S a v hp |>.flip_sign.symm))
lemma duesM_prongs (a : Site c) (hp : rolls (mon a) p) (v : Site S.patch.L) (x : Phase α) : poured S.ratio a (tiled p v x)=tune (duesM S a p v) x := by
  rw [duesM,dif_pos hp]
  conv_lhs => rw [hp.choose_spec]
  rw [apt_sign]; exact pose_fine ..
lemma cropAll (a : Site c) (hp : rolls (mon a) p) (v : Phase (Co S.patch.L α)) : poured S.ratio a v=∑ l : Site S.patch.L,tune (duesM S a p l) (stackSlice l (untier p v)) := by
  simp_rw [← duesM_prongs S a hp]; conv_lhs => rw [← alias_pack p v]
  ext1 i; unfold poured; simp_rw [Function.comp_apply,Finset.sum_apply]; simp only [tune, Finset.sum_apply, Finset.mul_sum]; rfl

def nose (X : Bridge G P) (p : Momentum) (a : Site P.L) (u : Loc G 1) := stackSlice a (untier p (X p*ᵥ Pi.single u 1))
lemma noses (W : Matrix (Body 1 f) (Body 1 c) ℝ) {X : Bridge G S.patch} (h : Premise S W X) (a : Site c) (hp : rolls (mon a) p) (x : Loc G 1) :
    approached (patron G W)*ᵥ (relay a x)=∑ l : Site S.patch.L,tune (duesM S a p l) (nose X p l x) := by
  let F := unitSplit G S 1; let v := X p *ᵥ Pi.single x 1
  have hh : repackM F (Equiv.refl _) (approached (patron G W)) *ᵥ (relay a x)= tune a v := by
    have ht := h a p hp (Pi.single x 1); rw [add_zero] at ht; exact ht
  suffices he : approached (patron G W)*ᵥ relay a x=poured S.ratio a v from he.trans (cropAll _ a hp _)
  have he : (approached (patron G W)*ᵥ relay a x) ∘ F.symm=tune a v := (repack_act F (Equiv.refl _) _ _).symm.trans hh
  funext i; have hv := congr_fun he (F i); rw [Function.comp_apply,F.symm_apply_apply] at hv; exact hv
lemma clean_nose {X : Bridge G P} (h : Poster σ X) (i a b) {q} (hp : q∈strip σ) : ContinuousAt (fun p => nose X p i a b) q := by
  let F := X; have hh : BillD (fun p => (plankTile P.L (Loc G 1) p)⁻¹ * X p) q := ((tile_lit q).take (tile_solid q)).bond (h.shape hp)
  let P' p := ((inch P.L:ℂ)^2 * ((plankTile P.L (Loc G 1) p)⁻¹* X p) (i,b) a)
  have hy : (fun p => nose X p i a b)=P' := by funext p; unfold nose untier stackSlice crewAlias; simp only [Pi.smul_apply, Matrix.mulVec_mulVec,mulVec_single_one]; rfl
  rw [hy]; exact (continuousAt_const.mul ((hh _ _).continuousAt))
end YM.Stationary
end

/-!
# Normalized comparison across coarse/fine collectors. Requires cofinal
reads; preserves all n. Relative composition audited. Λ error only required
at basis amplitudes. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D F : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum}
section transfer
-- convert aperture to normalized value
def fiscal (F : Link G c → ℝ) (u v : Phase (Lines G c 1)) := (cents c:ℂ)⁻¹ * noteAt F 2 ![u,v]

def rowscape (f : Picture G 1) (q : Momentum) : CompM (Loc G 1) (Loc G 1) := Matrix.of fun i j => f ![i.2,j.2] ![i.1,j.1] (fun k => q k.2)
def skyline (f : Picture G 1) (q : Momentum) (u v : Phase (Loc G 1)) := dotProduct u (rowscape f q *ᵥ v)
variable {F : Link G c →ℝ} {M : Picture G 1}
lemma rise_view (i j : Loc G 1) (a b : Site c) : (![relay a i,relay b j]:Fin 2→_)=glyph ![a,b] ![i.2,j.2] ![i.1,j.1] := by ext1 k; fin_cases k <;> rfl
lemma clips_off (h : Recorded M F (cents c*A)) (i j : Loc G 1) (a b : Site c) (hp : a+b≠0) : ‖fiscal F (relay a i) (relay b j)‖≤ A := by
  have hz := h ![a,b] ![i.2,j.2] ![i.1,j.1]
  rw [collected, Fin.sum_univ_two, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_zero,if_neg hp,sub_zero] at hz
  unfold fiscal; rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (cents_pos (m:=c)).le,rise_view]; exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr cents_pos.le)).trans_eq (inv_mul_cancel_left₀ cents_pos.ne' _)

-- linear toll operations

def beer (F : Link G c → ℝ) (u : Phase (Lines G c 1)) : Phase (Lines G c 1) →ₗ[ℂ] ℂ := (cents c:ℂ)⁻¹ • (noteAt F 2).toLinearMap ![u,0] 1
lemma beer_warm (F : Link G c → ℝ) (u v) : fiscal F u v=beer F u v := by
  unfold fiscal
  change _= (cents c:ℂ)⁻¹ * noteAt F 2 (update ![u,0] 1 v)
  congr 2; ext1 i; fin_cases i <;> simp
def hops (F : Link G c→ℝ) (u : Phase (Lines G c 1)) : Phase (Lines G c 1)→ₗ[ℂ] ℂ := (cents c:ℂ)⁻¹ • (noteAt F 2).toLinearMap ![0,u] 0
lemma summerBeer (F : Link G c→ℝ) (u v) : fiscal F u v=hops F v u := by
  unfold fiscal; change _=(cents c:ℂ)⁻¹ * noteAt F _ (update ![0,v] 0 u); congr 2; ext1 i; fin_cases i <;> simp
lemma fiscal_value (F : Link G c→ℝ) (u v : Phase (Loc G 1)) (a b : Site c) :
    fiscal F (tune a u) (tune b v) = ∑ i,u i*∑ j,v j*fiscal F (relay a i) (relay b j) := by
  rw [relay_value a u, summerBeer,map_sum]; refine sum_congr rfl fun i _ => ?_; rw [map_smul, ← summerBeer F _ (tune b v), relay_value b v, beer_warm, map_sum,smul_eq_mul]; congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, beer_warm]; rfl
end transfer

section columns
variable {M : Picture G 1} (h : ∀ i j,Firm σ A (M i j)) {W : ∀ i, Link G (m i)→ℝ} {ε : ℕ→ℝ} (hp : ∀ i, Recorded M (W i) (cents (m i)*ε i))
include h hp
lemma royalty_right (u v : Loc G 1) (p : ∀ i, Site (m i)) (q : ℕ→ Momentum) (hv : ∀ i, rolls (mon (p i)) (q i))
    {x : Momentum} (ht : Tendsto q atTop (𝓝 x)) (hx : star x=x) (he : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i => fiscal (W i) (relay (-p i) u) (relay (p i) v)) atTop (𝓝 (rowscape M x u v)) := by
  let V : Corn (Keys 1) := fun j => (x j.2).re
  let F i : Fin (1+1)→ Site (m i) := ![-p i,p i]; let U i : Space 1 := fun j => q i j.2
  have hn : axes V=x ∘ Prod.snd := funext fun i => congr_fun (axes_of_real hx) i.2
  have hU : Tendsto U atTop (𝓝 (axes V)) := by rw [hn]; exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mp ht i.2
  have hf i : rolls (outphase (F i)) (U i) := rolls_keys fun a => by fin_cases a; exact hv i
  have hh := harvest h hp he V F U hU (fun i=> ⟨by simp [F, Fin.sum_univ_two],hf i⟩) ![u.2,v.2] ![u.1,v.1]; rw [hn] at hh; simp_rw [fiscal, rise_view]; exact hh
lemma station_alias (u v : ℕ → Phase (Loc G 1)) (p q : ∀ i,Site (m i)) (k : ℕ→ Momentum) (hk : ∀ i, rolls (mon (q i)) (k i)) {x : Momentum} (he : Tendsto k atTop (𝓝 x)) (hx : star x=x)
    (ht : Tendsto ε atTop (𝓝 0)) {l r : Phase (Loc G 1)} (hu : Tendsto u atTop (𝓝 l)) (hr : Tendsto v atTop (𝓝 r)) (H : ∀ i,p i= -q i) :
    Tendsto (fun i=> fiscal (W i) (tune (p i) (u i)) (tune (q i) (v i))) atTop (𝓝 (skyline M x l r)) := by
  simp_rw [fiscal_value,H]
  unfold skyline Matrix.mulVec dotProduct
  refine tendsto_finsetSum univ fun i _=> (tendsto_pi_nhds.mp hu i).mul ?_
  have hh := tendsto_finsetSum univ fun j _ => (tendsto_pi_nhds.mp hr j).mul (royalty_right h hp i j q k hk he hx ht)
  convert hh using 2; apply sum_congr rfl; intro j _; exact mul_comm ..
omit h in
lemma alias_ghost (u v : ℕ → Phase (Loc G 1)) (p q : ∀ i,Site (m i))
    (ht : Tendsto ε atTop (𝓝 0)) {l r : Phase (Loc G 1)} (hu : Tendsto u atTop (𝓝 l)) (hr : Tendsto v atTop (𝓝 r)) (H : ∀ i,p i≠ -q i) :
    Tendsto (fun i=> fiscal (W i) (tune (p i) (u i)) (tune (q i) (v i))) atTop (𝓝 0) := by
  simp_rw [fiscal_value]; have he (i j) : Tendsto (fun z => fiscal (W z) (relay (p z) i) (relay (q z) j)) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) ht); exact clips_off (hp x) _ _ _ _ (fun hz=> H x (eq_neg_of_add_eq_zero_left hz))
  simpa using tendsto_finsetSum univ fun i _=> (tendsto_pi_nhds.mp hu i).mul (tendsto_finsetSum univ fun j _=> (tendsto_pi_nhds.mp hr j).mul (he i j))
end columns
end YM.Stationary
end

/-! # Roll jump before rank normalization. δ=1 factor positivity used in operation. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η τ A C D F : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum}

section glue
variable (S : StepData c f)
lemma fiscal_comp {X : Matrix (Body 1 f) (Body 1 c) ℝ} (K : Link G f → ℝ) (h : AnalyticAt ℝ K 0) (p q) :
    fiscal (K∘uniformM X) p q=(S.patch.L.val:ℂ)^4*fiscal K ((approached (patron G X))*ᵥ p) ((approached (patron G X))*ᵥ q) := by
  let F := uniformM (G:=G) X; let T := patron G X
  let B := (approached T).mulVecLin
  have he : noteAt (K ∘ F) 2 ![p,q]=noteAt K 2 ![B p,B q] := by
    unfold noteAt
    rw [evaluated B (by intro u; rw [show B (axes u)= _ from (show B (axes u)=axes (T *ᵥ u) from prom_vec ..), patron_fee]) h, _root_.smul_apply,_root_.smul_apply,MultilinearMap.compLinearMap_apply]; congr 2; ext1 i; fin_cases i <;> rfl
  unfold fiscal; rw [show uniformM X= F from rfl]
  rw [he, ← mul_assoc, show (cents c:ℂ)⁻¹=(S.patch.L.val:ℂ)^4*(cents f:ℂ)⁻¹ by simp only [cents,Lattice.site_card,Nat.cast_pow]; push_cast; rw [S.sizes]; push_cast; field_simp]; rfl
lemma fiscal_bolted (F : Link G f→ℝ) (a b : Site c) (v w : Loc G 1) (W : Matrix (Body 1 f) (Body 1 c) ℝ) {X : Bridge G S.patch} (hp : Premise S W X) (ha : rolls (mon a) p) (hb : rolls (mon b) q) (h : AnalyticAt ℝ F 0) :
    fiscal (F∘uniformM W) (relay a v) (relay b w)=(S.patch.L.val:ℂ)^4*∑ i : Site S.patch.L,∑ j : Site S.patch.L, fiscal F
      (tune (duesM S a p i) (nose X p i v)) (tune (duesM S b q j) (nose X q j w)) := by
  rw [fiscal_comp S F h,noses S W hp a ha v,noses S W hp b hb w,summerBeer,map_sum]; congr 1; refine sum_congr rfl fun i _ => ?_; rw [← summerBeer,beer_warm, map_sum]; exact sum_congr rfl fun _ _ => (beer_warm ..).symm
end glue
section graft

def carryRow (X : Bridge G P) (F : Picture G 1) (p : Momentum) (a b : Loc G 1) := (P.L.val:ℂ)^4 * ∑ l : Site P.L,
    skyline F (aliasAt p l) (nose X (-p) (-l) a) (nose X p l b)

lemma carry_plan {F Q : Picture G 1} {X : Bridge G P} (H : Armada m n P K) {W : ∀ i, Matrix (Body 1 (n i)) (Body 1 (m i)) ℝ} (hx : Poster σ X) (hz : 0<σ)
    (hs : ∀ i j,Firm η A (F i j)) (hv : ∀ i j,Firm τ C (Q i j)) (hP : ∀ i, Premise (H.boot i) (W i) X) {K : ∀ i, Link G (n i)→ℝ} (hK : ∀ i,AnalyticAt ℝ (K i) 0) {ε δ : ℕ → ℝ}
    (hF : ∀ i, Recorded F (K i) (cents (n i)*ε i)) (hQ : ∀ i, Recorded Q ((K i)∘ uniformM (G:=G) (W i)) (cents (m i)*δ i))
    (hε : Tendsto ε atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0)) (hm : Tendsto (fun i=>(m i).val) atTop atTop) {p : Momentum} (he : star p=p) (a b) : rowscape Q p a b=carryRow X F p a b := by
  obtain ⟨g,u,hu,hk⟩ := mesh_stride m hm p he
  have hh l : Tendsto (fun i : ℕ=> aliasAt (u i) (l : Site P.L)) atTop (𝓝 (aliasAt p l)) := (show Continuous (fun p=> aliasAt p (l:Site P.L)) by unfold aliasAt; fun_prop).continuousAt.tendsto.comp hu
  let A i (l : Site P.L) := duesM (H.boot i) (g i) (u i) l
  let B i (l : Site P.L) := duesM (H.boot i) (-g i) (-u i) l
  let M i (l k : Site P.L) := fiscal (K i) (tune (B i l) (nose X (-u i) l a)) (tune (A i k) (nose X (u i) k b))
  let N (l : Site P.L) := skyline F (aliasAt p l) (nose X (-p) (-l) a) (nose X p l b)
  have hB i k : B i (-k)= -A i k := duesM_neg (H.boot i) (g i) (hk i) k
  have ht l : Tendsto (fun i => nose X (u i) l b) atTop (𝓝 (nose X p l b)) := by refine tendsto_pi_nhds.mpr (fun i => (clean_nose hx l b i (Work.F07.realStrip _ hz he)).tendsto.comp hu)
  have hf l : Tendsto (fun i => nose X (-u i) l a) atTop (𝓝 (nose X (-p) l a)) := by refine tendsto_pi_nhds.mpr (fun i=> (clean_nose hx l a i (negResident (Work.F07.realStrip _ hz he))).tendsto.comp hu.neg)
  have hV (l k : Site P.L) : Tendsto (fun i => M i l k) atTop (𝓝 (if l= -k then N k else 0)) := by
    split <;> rename_i H'
    · subst l; exact station_alias hs hF _ _ _ _ _ (fun i => duesM_real (H.boot i) (g i) k (hk i)) (hh k) (by rw [← alias_conj,he]) hε (hf (-k)) (ht k) (fun i=> hB i k)
    apply alias_ghost hF _ _ (fun i=> B i l) (fun i=> A i k) hε (hf l) (ht k)
    intro i he'; apply H'; exact duesM_one (H.boot i) (-g i) (hk i |>.flip_sign) (he'.trans (hB i k).symm)
  refine tendsto_nhds_unique (royalty_right hv hQ a b g u hk hu he hδ) ?_
  simp_rw [show ∀ i, fiscal (K i ∘ uniformM (G:=G) (W i)) (relay (-g i) a) (relay (g i) b)=(P.L.val:ℂ)^4*∑ l : Site P.L, ∑ j : Site P.L,M i l j from fun i=> fiscal_bolted (H.boot i) (K i) _ _ _ _ _ (hP i) (hk i|>.flip_sign) (hk i) (hK i)]
  change Tendsto _ _ (𝓝 (_* ∑ j : Site P.L,N j)); apply Tendsto.const_mul
  have hv := tendsto_finsetSum univ fun l _=> tendsto_finsetSum univ fun j _=> hV l j
  have he : ∑ l : Site P.L,∑ j : Site P.L,(if l= -j then N j else 0)=∑ j : Site P.L,N j := by rw [sum_comm]; simp
  rw [he] at hv; exact hv
end graft
end YM.Stationary
end

/-!
# Coarse–fine source equations on physical aliases. pΩ real grants. Intrinsic
lower estimate on NONPRINCIPAL aliases. Do not assume suppression of
longitudinal there by the chosen budget witness.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η τ A C D F ε Ω : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum}

lemma patron_line (G : Gauge) (n : Side) (i : ℕ) : patron G (1:Matrix (Body i n) (Body i n) ℝ)=1 := testers fun x y => by rw [patron_fee,one_mulVec]; congr 1; ext1 a; unfold uniformM; dsimp; rw [one_mulVec]; rfl
lemma patron_add {S T : Matrix (Body 1 c) (Body 1 f) ℝ} : patron G (S+T)=patron G S+patron G T := testers fun i j => by
  rw [add_mulVec,patron_fee,patron_fee,patron_fee]; congr 1; ext1 x; change ((S+T)*ᵥ _) _=_; rw [add_mulVec]; rfl
lemma patron_coeff {n₀ : Side} (c : ℝ) (F : Matrix (Body 1 n₀) (Body 1 f) ℝ) : patron G (c • F)=c • patron G F := by
  apply testers; intro i j; rw [smul_mulVec,patron_fee,patron_fee]; congr 1; ext1 x; change ((c • F)*ᵥ _) _ = _; rw [smul_mulVec]; rfl

def primalV (X : Bridge G P) (B T : Bed) (p : Momentum) := furnish P.L (rug G B) p*X p=(meanRay G P (-p))ᵀ*rug G T p
def secondV (X : Bridge G P) (B : Bed) (κ : ℝ) (p : Momentum) := meanRay G P p*X p=1-(κ⁻¹:ℝ) • rug G B p
lemma actor_duo {X : Bridge G P} {B T : Bed} (H : Armada m n P K) {W : ∀ i, Matrix (Body 1 (n i)) (Body 1 (m i)) ℝ}
    (hp : 0<σ) (ht : T.metric.strip σ A) (he : 0<η) (hV : B.metric.strip (inch P.L*η) Ω) (hG : 0< τ) (hk : Poster τ X)
    (hm : Tendsto (fun i=> (m i).val) atTop atTop) (hP : ∀ i, Premise (H.boot i) (W i) X) (hz : ∀ i, Inputs (H.boot i) (W i) (B.metric.acts _) (T.metric.acts _)) (hx : star p=p) : primalV X B T p ∧ secondV X T K.penalty p := by
  classical
  let M := meanRay G P; let Q := rug G B; let k := rug G T
  let s := min σ (min η τ)
  have h' : 0<s := lt_min hp (lt_min he hG)
  have hl := (hV : B.metric.strip _ Ω)
  have hl' := (rug_played (G:=G) B hl (mul_pos (inch_pos _) he)); have hw : Poster s (furnish P.L Q) := hl'.furnish_ok.skinny ((min_le_right ..).trans (min_le_left ..))
  have hr : Poster s k := (rug_played (G:=G) T ht hp).skinny (min_le_left ..); have hi : Poster s M := mean_plays ..
  have hk' := hk.skinny (show s ≤ τ from (min_le_right ..).trans (min_le_right ..))
  have ha := T.metric.rights _ _ ht hp.le
  constructor
  · refine Poster.fuses m hm (hw.forge hk') (hi.reverse.forge hr) h' h' ?_ hx
    intro i p; let S := H.boot i
    let V := unitSplit G S 1; let L := Equiv.refl (Lines G (m i) 1)
    let Z := patron G (W i); let Xq := bondsM G S
    let A := patron G (Precision.K (B.metric.acts (n i))); let Y := patron G (Precision.K (T.metric.acts (m i)))
    have hr : Jaunt (repackM V V (approached A)) (furnish S.patch.L (rug G B)) 0 := Jaunt.press S.ratio (rug_plane (n i) B (B.metric.rights _ _ hl (mul_pos (inch_pos _) he).le)) hl' he
    have hX : A*Z=Xqᵀ *Y := by unfold A Z Xq bondsM Y; rw [← patron_mul, ← patron_star, ← patron_mul, (hz i).primal]
    have hk := hr.hoist (hP i)
    have hZ := (bond_travel (G:=G) S).takes.hoist (rug_plane _ T ha)
    have heq : repackM V V (approached A)*approached (repackM V L Z)=(repackM L V (approached Xq))ᵀ * approached Y := by
      rw [show _ * approached (repackM V L Z)=repackM V L (approached (A*Z)) from (by rw [prom_mul,repack_multiply _ V]; rfl),hX,prom_mul,repack_multiply _ L]; rfl
    have hz : Jaunt (repackM V V (approached A)*approached (repackM V L Z)) (fun p=> furnish P.L Q p * X p) 0 := hk
    rw [heq] at hz; exact hz.offset hZ _ (rolls.refl _)
  let c := K.penalty⁻¹
  let v := fun p => (1:CompM (Loc G 1) (Loc G 1))- c • k p
  refine Poster.fuses m hm (hi.forge hk') (g:=v) (Poster.shares (Poster.web _) (hr.plus_nec (c:ℂ))) h' h' ?_ hx
  intro i p; let S := H.boot i; let V := unitSplit G S 1; let L := Equiv.refl (Lines G (m i) 1)
  let Z := patron G (W i); let T' := bondsM G S; let Y:=patron G (Precision.K (T.metric.acts (m i)))
  have hu : T'*Z=1-c • Y := by unfold T' bondsM Y Z; rw [← patron_mul,(hz i).dual,sub_eq_add_neg, ← neg_smul,patron_add,patron_line,patron_coeff,neg_smul, sub_eq_add_neg]
  have he := (bond_travel (G:=G) S).hoist (hP i)
  have hw := (Jaunt.noop (α:=Loc G 1) (m:=m i)).plus (((rug_plane (G:=G) _ T ha).smul (c:ℂ)).backside)
  have hp : Jaunt (1 + -((c:ℂ) • approached Y)) v 0 := by
    have hx : v=(fun p => (1:CompM (Loc G 1) (Loc G 1)))+-((↑c:ℂ) • k) := by
      ext i j z; simp [v, sub_eq_add_neg]
    rw [hx]; exact hw
  have hx : repackM L V (approached T') * approached (repackM V L Z) = 1+ -((c:ℂ) • approached Y) := by
    have he : repackM L V (approached T') * approached (repackM V L Z)= approached (T'*Z) := by
      rw [show approached (T' * Z)=repackM L L (approached (T'*Z)) from rfl, prom_mul,repack_multiply _ V]; rfl
    rw [he,hu,sub_eq_add_neg,prom_addition,prom_negation,prom_one',prom_tone]
  rw [← hx] at hp; exact he.offset hp _ (rolls.refl _)
end YM.Stationary
end

/-!
# Normal core projection at every nonprincipal l. No claim that X.GA
weights vanish there; project away *every* pure gauge, on mesh extension.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {k : Clip} {K : KernelChoices} {σ η τ A C D F ε Ω : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum} {B T : Bed}

def curtainG (G : Gauge) (B : Bed) (p : Momentum) := rug G B p + pageD G 0 p*(pageD G 0 (-p))ᵀ
def horizontalQ (X : Bridge G P) (p : Momentum) (l : Site P.L) (a : Loc G 1) : Phase (Loc G 0) :=
    let w := aliasAt p l
    (-(stone w)⁻¹) • ((pageD G 0 (-w))ᵀ *ᵥ nose X p l a)
def horizontal (X : Bridge G P) (p : Momentum) (l : Site P.L) (a) :=
    nose X p l a+ pageD G 0 (aliasAt p l) *ᵥ horizontalQ X p l a
lemma sudden {l : Site P.L} (hp : l≠0) : ∀ᶠ v : Track in 𝓝 0,
    0<shadeK (aliasAt (axes v) l) ∧ stone (aliasAt (axes v) l) ≠ 0 := by
  have hv : ∀ᶠ x : Track in 𝓝 0,Nave (axes x) := by
    refine eventually_all.mpr fun i => ?_
    have hh : Continuous (fun p : Track=> |p i|) := by fun_prop
    have hz : Tendsto (fun p : Track=> |p i|) (𝓝 0) (𝓝 0) := by simpa using hh.tendsto 0
    exact hz.eventually (ge_mem_nhds Real.pi_pos)
  filter_upwards [hv] with x hx; have h := lt_of_lt_of_le (by positivity [inch_pos P.L] : (0:ℝ)<2*inch P.L) (printer_ramp P hx hp)
  refine ⟨h,?_⟩; rw [stone_real (by rw [← alias_conj,axes_real])]; exact_mod_cast (pow_pos h 2).ne'
lemma oriented_cap {X : Bridge G P} (l : Site P.L) (x : Track) (hp : stone (aliasAt (axes x) l)≠0) (a) :
    (pageD G 0 (-(aliasAt (axes x) l)))ᵀ *ᵥ horizontal X (axes x) l a=0 := by
  let p := aliasAt (axes x) l
  unfold horizontal horizontalQ; simp only [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_mulVec];
  rw [← Matrix.mul_assoc (pageD _ _ _)ᵀ, codex_value, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec,smul_smul, neg_mul,inv_mul_cancel₀ hp,neg_one_smul,add_neg_cancel]

lemma rug_hole (G : Gauge) (B : Bed) (p) : rug G B p*pageD G 0 p=0 := by rw [rug,Matrix.mul_assoc ((pageD G 1 _)ᵀ * _),page_zero, Matrix.mul_zero]
lemma peel_finer {X : Bridge G P} (B T : Bed) (l : Site P.L) (x : Track) (hp : primalV X B T (axes x)) (a) :
    let p := axes x
    let y := untier p ((meanRay G P (-p))ᵀ *ᵥ (rug G T p*ᵥ Pi.single a 1))
    rug G B (aliasAt p l)*ᵥ nose X p l a=stackSlice l y := by
  intro p y; unfold y; rw [Matrix.mulVec_mulVec,← show _=_ from hp, ← Matrix.mulVec_mulVec _,draping,posterBlock_at]; rfl
lemma pillar_gap (h : B.metric.strip η A) (hp : 0 < η) (hw : ∀ n, Floor B k n ε C) (hε : 0 < ε) {p : Momentum} (he : star p=p) (hx : 0<shadeK p) : IsUnit (curtainG G B p).det := by
  let Gm := pageD G 0 p; let T := rug G B p
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y ht
  by_contra hk
  let v := x-y; have hz : curtainG G B p*ᵥ v=0 := by unfold v; rw [Matrix.mulVec_sub,ht,sub_self]
  have hi : (dotProduct (star v) (curtainG G B p *ᵥ v)).re=0 := by rw [hz, dotProduct_zero]; rfl
  unfold curtainG at hi; rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, page_rear 0 he] at hi
  have ha : (dotProduct (star v) ((Gm*Gmᴴ)*ᵥ v)).re = slug (Gmᴴ*ᵥ v)^2 := by
    rw [← Matrix.mulVec_mulVec]
    have H := vested Gmᴴ v (Gmᴴ *ᵥ v); rw [Matrix.conjTranspose_conjTranspose] at H; rw [H,slug_self]; rfl
  change (dotProduct (star v) ((rug G B p) *ᵥ v)).re + (dotProduct (star v) ((Gm*Gmᴴ)*ᵥ v)).re =0 at hi; rw [ha] at hi
  have hh := rug_test h hp hw he v
  have hv : 0 < slug v := slug_pos (sub_ne_zero_of_ne hk)
  have hw : ε*slug (pageD G 1 p*ᵥ v)^2 ≤ 0 := by linarith [sq_nonneg (slug (Gmᴴ*ᵥv))]
  have ht₁ : slug (pageD G 1 p*ᵥ v)^2=0 := le_antisymm (le_of_mul_le_mul_left (by simpa using hw) hε) (sq_nonneg _)
  have ha := pure_grade he G v; unfold Gm at *; rw [ht₁] at hh ha; nlinarith only [ha, hh, hi,pow_pos (mul_pos hx hv) 2]
end YM.Stationary
end

/-!
# Genuine alias order suppression modulo longitudinal. A qualitative opaque
input to α and deep-loop tests. p.ratio odd; floor needed uniform n for
same B. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α] {G : Gauge} {P : Patch} {K : KernelChoices} {k : Clip} {σ η τ A C D F ε Ω : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum} {B T : Bed} {X : Bridge G P}

lemma ray_constant_here {F : Track →ℂ} (h : ContinuousAt F 0) : Rays 0 F := by
  intro v; simp only [pow_zero]; exact (h.tendsto.comp (along v)).isBigO_one ℝ
lemma selectionG (q : Momentum) (f : Phase (Co L α)) (t : Co L α) : untier q f t=((inch L:ℂ)^2) * ∑ i, (plankTile L α q)⁻¹ t i * f i := rfl

lemma high_halo {l : Site P.L} (hl : l≠0) (a z) (hp : B.metric.strip σ A) (hx : 0<σ) (hw : ∀ n, Floor B k n ε C) (hε : 0<ε)
    (ht : T.metric.strip η D) (hη : 0<η) (hy : ∀ v : Track, primalV X B T (axes v)) : Rays 2 (fun v : Track => horizontal X (axes v) l a z) := by
  let U v := aliasAt (axes v) l
  let H := curtainG G B
  let F (v : Track) := H (U v)
  have hK v : star (U v)=U v := by simp [U, ← alias_conj]
  let p v := rug G T (axes v)*ᵥ Pi.single a 1
  let q v := (meanRay G P (-(axes v)))ᵀ*ᵥ p v
  let y v := (untier (axes v) (q v))
  have he : ∀ᶠ v in 𝓝 0,horizontal X (axes v) l a=(F v)⁻¹ *ᵥ stackSlice l (y v) := by
    filter_upwards [sudden hl] with v ⟨hv,ha⟩
    have hF : IsUnit (F v).det := pillar_gap hp hx hw hε (hK v) hv
    have hi : (F v)*ᵥ horizontal X (axes v) l a=stackSlice l (y v) := by
      unfold F H curtainG; rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec _ (pageD G 0 (U v)),show (pageD G 0 (-(U v)))ᵀ *ᵥ _=0 from oriented_cap l _ ha _, mulVec_zero,add_zero]
      unfold horizontal; simp only [Matrix.mulVec_add]; rw [show rug G B (U v)*ᵥ nose X (axes v) l a=_ from peel_finer B T l v (hy v) a, Matrix.mulVec_mulVec _ (rug G B (U v)), show rug G B (U v) * pageD G 0 (U v)=0 from rug_hole G B _,zero_mulVec,add_zero]
    rw [← hi,mulVec_mulVec, Matrix.nonsing_inv_mul _ hF, one_mulVec]
  have hi' : IsUnit (H (U 0)).det := pillar_gap hp hx hw hε (hK _) (sudden hl).self_of_nhds.1
  have hF i j : ContinuousAt (fun v => ((F v)⁻¹) i j) 0 := by
    have hu : Poster σ H := (rug_played _ hp hx).amounts ((page_linen 0).forge ((page_linen 0).reverse))
    have hh := BillD.take (hu.shape (Work.F07.realStrip _ hx (hK 0))) hi'
    have hv : Continuous U := (show Continuous (fun p : Momentum=> aliasAt p l) by unfold aliasAt; fun_prop).comp axes_maps.continuous
    exact ((hh i j).continuousAt).comp hv.continuousAt
  have hq (u : Loc G 1) : Rays 2 (fun v => p v u) := by
    let x := fun v=> taxTone G T (axes v) a u
    have he : (fun v => p v u)= -x := by ext1 v; simp [x,taxTone,p]
    rw [he]; exact fun z => (tax_ray T ht hη a u z).neg_left
  have hG (u) : Rays 2 (fun v : Track => q v u) := by
    apply rays_total (f:=fun i v => meanRay G P (-(axes v)) i u * p v i)
    intro j; apply Rays.mul (s:=0) (t:=2) (g:=fun v=> p v j) _ (hq j)
    have hv : Poster σ (meanRay G P) := mean_plays ..
    apply ray_constant_here; exact ((hv.reverse.shape (p:=axes 0) (by rw [axes_origin]; exact Work.F07.realStrip _ hx (by simp)) u j).continuousAt).comp (f:=axes) axes_maps.continuous.continuousAt
  have hY i : Rays 2 (fun v : Track => y v i) := by
    unfold y; simp_rw [selectionG]
    have ht : BillD (fun p => (plankTile P.L (Loc G 1) p)⁻¹) (axes 0) := (BillD.take (tile_lit _) (tile_solid _))
    have he j : ContinuousAt (fun (v : Track)=> (plankTile P.L (Loc G 1) (axes v))⁻¹ i j) 0 := (ht i j).continuousAt.comp axes_maps.continuous.continuousAt
    intro v; exact (rays_total (f:= fun j (x:Track)=> (plankTile P.L (Loc G 1) (axes x))⁻¹ i j * q x j) (fun j => (ray_constant_here (he j)).mul (hG j)) v).const_mul_left _
  intro v
  have hy : ∀ᶠ x : ℝ in cutRay,horizontal X (axes (x • v)) l a z = _ := ((along v).eventually he).mono (fun x hx => congr_fun hx z)
  exact ((rays_total (f:=fun i v => ((F v)⁻¹) z i * y v (l,i)) (fun i => (ray_constant_here (hF z i)).mul (hY _))) v).congr' (hy.mono fun _ k => k.symm) EventuallyEq.rfl

end YM.Stationary
end

/-!
# Pinnings at real center. No longitudinal estimates, even for K' momentum
 disk. Govern Kurs. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {k : Clip} {K : KernelChoices} {σ η τ A C D F ε Ω : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum} {B T : Bed} {X : Bridge G P}

lemma rays_force_zero {F : Track→ℂ} (h : Rays 2 F) : F 0=0 := by
  have he := h 0
  have ht : Tendsto (fun t : ℝ => t^2) cutRay (𝓝 0) := by
    simpa using ((show Continuous (fun t : ℝ => t^2) by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (α:=ℝ) (s:={0}ᶜ))
  have he := he.trans_tendsto ht; simp only [smul_zero] at he; exact tendsto_nhds_unique tendsto_const_nhds he

lemma anchored (κ : ℝ) (U : Bridge G P) (B T : Bed) (hq : ∀ p : Momentum, star p=p → primalV U B T p)
    (h : secondV U T κ 0) (he : B.metric.strip η A) (hp : 0<η) (hT : T.metric.strip τ F) (hτ : 0<τ) (hw : ∀ n, Floor B k n ε C) (hε : 0<ε) (v : Loc G 1) :
    nose U 0 0 v=(inch P.L:ℂ) • Pi.single v 1 := by
  let a : Phase (Loc G 1) := Pi.single v 1
  let F := U 0*ᵥ a; let M := meanRay G P 0
  have hs j : pageD G j 0=0 := by ext a b; simp [pageD,tintedLocal,Exterior.symbol,Exterior.wedge,Exterior.q]
  have hh : rug G T 0=0 := by rw [rug,neg_zero,hs,Matrix.mul_zero]
  have hd : M*ᵥ F=a := by rw [show M *ᵥ F= (M*U 0)*ᵥ a from mulVec_mulVec ..,show M*U 0=_ from h,hh,smul_zero,sub_zero,one_mulVec]
  conv at hd => arg 1; rw [← alias_pack (0:Momentum) F,mulVec_sum]
  have hv (l : Site P.L) (p : l≠0) : horizontal U 0 l v=0 := by
    funext i; have he' := high_halo p v i he hp hw hε hT hτ (fun i => hq _ (axes_real i)); simpa only [axes_origin,Pi.zero_apply] using rays_force_zero he'
  rw [Finset.sum_eq_single (0:Site P.L)] at hd
  · have h : aliasAt 0 (0:Site P.L)= (0:Momentum) := by simp [aliasAt]
    have hp (z : Loc G 1) : capBond (0:Momentum) P z=P.L.val := by
      unfold capBond
      rw [rollMean,show ∑ a : P.Points, (↑(P.weight a):ℂ)*mode 0 a.val=1 by simp [← Complex.ofReal_sum]; exact P.weight_sum]; simp
    unfold M at hd; rw [mean_aim] at hd; simp_rw [h,hp] at hd
    ext1 i
    have hy : (P.L.val:ℂ)*nose U 0 0 v i=a i := congr_fun hd i
    change _=(inch P.L:ℂ)*a i; rw [← hy, ← Complex.ofReal_natCast, ← mul_assoc, ← Complex.ofReal_mul, inch_unit, Complex.ofReal_one, one_mul]
  · intro l _ ht
    let x := tiled 0 l (nose U 0 l v); let K := aliasAt 0 l
    rw [show stackSlice _ _=nose U 0 l v from rfl,show nose U 0 l v = pageD G 0 K *ᵥ (-horizontalQ U 0 l v) from ?_, ← furnish_gear _ _ _ _]
    · change M *ᵥ (furnish P.L (pageD G 0) 0 *ᵥ _) = _; rw [mulVec_mulVec, show M * _=pageD G 0 0 * jar G P 0 from mean_stern _, hs, Matrix.zero_mul, zero_mulVec]
    rw [Matrix.mulVec_neg]; exact eq_neg_of_add_eq_zero_left (hv _ ht)
  simp
end YM.Stationary
end

/-!
# Both-leg Ceta gauge projection. Keep only true covariance, no realization
of longitudinal materialization. Real plane. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {k : Clip} {K : KernelChoices} {σ η τ A C D ε Ω : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum} {B T : Bed} {X : Bridge G P} {F : Picture G 1}
lemma perspective (x : Track) : plotted (axes (roads x)) (0:Fin (1+1))= -axes x := by simp [plotted,missing]; rfl

lemma both_ends (h : ∀ i, Contractible (F i)) (hx : star p=p) : rowscape F p * pageD G 0 p=0 ∧ (pageD G 0 (-p))ᵀ * rowscape F p=0 := by
  let v : Track := fun i=> (p i).re
  have hv : p=axes v := (axes_of_real hx).symm
  rw [hv]
  constructor
  · ext ⟨a,b⟩ ⟨q,u⟩; rw [vac_only q]
    have he := h ![b,u] (roads v) 1 ![a,a]
    rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp only [pageD,tintedLocal,Matrix.of_apply,Prod.mk.injEq, mul_ite, mul_zero]
    rw [show (∑ x,∑ z : G.ColorIndex,_) = ∑ x : TypeFace 1, symbol 0 (axes v) x vac * F ![b,u] (update ![a,a] 1 x) (axes (roads v)) from ?_]; exact he
    apply sum_congr rfl; intro i _; rw [sum_eq_single u]
    · simp only [if_true]
      rw [mul_comm]; rw [show update ![a,a] 1 i=![a,i] by funext j; fin_cases j <;> simp]; rfl
    · intro c _ h; rw [if_neg h]
    simp
  ext ⟨q,u⟩ ⟨a,b⟩; rw [vac_only q]
  have he := h ![u,b] (roads v) 0 ![a,a]; rw [perspective] at he
  rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp only [pageD,tintedLocal,Matrix.of_apply, Matrix.transpose_apply,Prod.mk.injEq,ite_mul,zero_mul]
  rw [show (∑ x,∑ z : G.ColorIndex,_)=∑ x : TypeFace 1,symbol 0 (-axes v) x vac * F ![u,b] (update ![a,a] 0 x) (axes (roads v)) from ?_]; exact he
  apply sum_congr rfl; intro i _; rw [sum_eq_single u];
  · simp only [if_true]; rw [show update ![a,a] 0 i=![i,a] by funext j; fin_cases j <;> simp]; rfl
  · intro c _ h; rw [if_neg h]
  simp
lemma happy_sky (h : ∀ i, Contractible (F i)) (l : Site P.L) (hp : star p=p) (a b) : skyline F (aliasAt p l) (nose X (-p) (-l) a) (nose X p l b)=
    skyline F (aliasAt p l) (horizontal X (-p) (-l) a) (horizontal X p l b) := by
  let H := aliasAt p l; have hx := both_ends h (p:=H) (by unfold H; rw [← alias_conj,hp]); unfold horizontal skyline
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec _ (rowscape _ _), hx.1,zero_mulVec,add_zero]
  rw [add_dotProduct, show pageD G 0 (aliasAt (-p) (-l))= pageD G 0 (-aliasAt p l) from congr_arg (tintedLocal G) (rolls_symbol (alias_counter _ _) _), dotProduct_comm (pageD G 0 _*ᵥ _),inflow (pageD G 0 (-aliasAt p l)),Matrix.mulVec_mulVec _ _ (rowscape F _),hx.2,zero_mulVec,zero_dotProduct,add_zero]

section sky
lemma skyline_meets {p : Momentum} (h : ∀ i j,Firm σ C (F i j)) (hp : star p=p) (a b) : ContinuousAt (fun p=> rowscape F p a b) p := by
  let M : Momentum→Space 1 := fun p k=>p k.2
  let B := F ![a.2,b.2] ![a.1,b.1]
  have he : star (M p)=M p := funext fun i=> congr_fun hp i.2
  have ht : Firm σ C B := h ..
  have hP : ContinuousAt B (M p) := (ht.1.hol _ (ht.in_range he)).continuousAt
  exact hP.comp (f:=M) (continuousAt_pi.mpr (fun i => (continuous_apply (A:=fun i : Axis=> ℂ) i.2).continuousAt))
end sky
end YM.Stationary
end

/-!
# Coarse–fine pole normalized in Rad. Suppression ordinal rather than
fixed-coordinate valuation. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {k : Clip} {K : KernelChoices} {σ η τ A C D F ε Ω : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum} {B T : Bed} {X : Bridge G P} {S : Picture G 1}

lemma wellNose {l : Site P.L} (h : Poster σ X) (hp : 0<σ) (a b) : AnalyticAt ℝ (fun x : Track=> nose X (axes x) l a b) 0 := by
  let F q := nose X q l a b
  have hh : AnalyticAt ℂ F 0 := by
    apply PolyDisc.formOf
    filter_upwards [(Work.F07.stripOpen σ).mem_nhds (Work.F07.realStrip _ hp (p:=0) (by simp))] with i hi
    let M : Momentum → CompM (Co P.L (Loc G 1)) (Co P.L (Loc G 1)) := plankTile P.L (Loc G 1)
    have he : BillD (fun p => (M p)⁻¹ * X p) i := ((tile_lit i).take (tile_solid i)).bond (h.shape hi)
    have hr (p : Momentum) : F p=(inch P.L:ℂ)^2 * ((M p)⁻¹*X p) (l,b) a := by unfold F M; simp only [nose, stackSlice,untier,crewAlias,Pi.smul_apply, mulVec_mulVec, mulVec_single_one]; rfl
    unfold F; simp_rw [show ∀ p : Momentum, nose X p l a b = _ from hr]; exact (he _ _).const_mul _
  exact ((show ContDiffAt ℝ ω F (axes (α:=Axis) 0) by rw [axes_origin]; exact (hh.contDiffAt (n:=ω)).restrict_scalars ℝ).comp (f:=axes) _ axes_maps.contDiffAt).analyticAt

lemma alias_zero_loc (x : Track) : aliasAt (axes x) (0:Site P.L)= axes (inch P.L • x) := by simp only [alias_discount]; funext i; simp [axes,Lattice.lift, reciprocal]

def RaysP (n : ℕ) (F : Picture G 1) := ∀ a b,Rays n (fun v : Track => rowscape F (axes v) a b)
lemma rowray (u v : Track→ Phase (Loc G 1)) (M : Track→ Momentum) {n l k : ℕ} {S : Picture G 1} (hS : ∀ i j,Rays n (fun i' => rowscape S (M i') i j))
    (h : ∀ i, Rays k (fun j=> u j i)) (p : ∀ i,Rays l (fun j=> v j i)) : Rays (k+(n+l)) (fun x=> skyline S (M x) (u x) (v x)) := by
  refine rays_total (f:=fun i x' => u x' i*(rowscape S (M x')*ᵥ v x') i) (fun i => ?_)
  exact (h i).mul (rays_total (f:=fun j i' => rowscape S (M i') i j*v i' j) (fun j=> (hS i j).mul (p j)))

section basal
variable {t : ℕ} (hR : RaysP t S) (hp : Poster σ X) (hs : 0<σ)
include hp hs
lemma central_competence (p : RaysP t S) (i j : Loc G 1) : Rays t (fun x : Track => skyline S (aliasAt (axes x) (0:Site P.L)) (nose X (-(axes x)) 0 i) (nose X (axes x) 0 j)) := by
  suffices hv : Rays (0+(t+0)) (fun x : Track => skyline S (aliasAt (axes x) (0:Site P.L)) (nose X (-(axes x)) 0 i) (nose X (axes x) 0 j)) by rwa [Nat.add_zero,Nat.zero_add] at hv
  refine rowray _ _ _ (fun i j v=> ?_) (fun z=> rays_zero (?_)) (fun b=> rays_zero (wellNose hp hs j b))
  · simp_rw [alias_zero_loc, smul_comm (inch P.L)]; exact p i j _
  simp_rw [← axes_flip]; exact (show AnalyticAt ℝ (fun (x : Track)=> nose X (axes x) 0 i z) (-0) by rw [neg_zero]; exact wellNose hp hs i z).comp analyticAt_id.neg

lemma canonicalGap {t} (p : RaysP t S) (a b : Loc G 1) (hx : ∀ b,nose X 0 0 b=(inch P.L:ℂ) • Pi.single b 1) :
    let V := fun (x : Track)=> aliasAt (axes x) (0:Site P.L)
    Rays (t+1) (fun x=> skyline S (V x) (nose X (-(axes x)) 0 a) (nose X (axes x) 0 b) -(inch P.L:ℂ)^2* rowscape S (V x) a b) := by
  intro V
  let A := fun x : Track => nose X (-(axes x)) 0 a; let B := fun x : Track => nose X (axes x) 0 b
  let μ := (inch P.L:ℂ)
  let u : Phase (Loc G 1) := μ • Pi.single a 1; let v : Phase (Loc G 1) := μ • Pi.single b 1
  have hf (x : Track) : μ^2* rowscape S (V x) a b = skyline S (V x) u v := by simp [u,v, skyline,sq,Matrix.mulVec_smul, Matrix.mulVec_single,mul_assoc]
  have hh (x : Track) : skyline S (V x) (A x) (B x) - μ^2* rowscape S (V x) a b = skyline S (V x) (A x-u) (B x) + skyline S (V x) u (B x-v) := by rw [hf]; unfold skyline; rw [sub_dotProduct, Matrix.mulVec_sub,dotProduct_sub]; abel
  have hV i j : Rays t (fun x => rowscape S (V x) i j) := by intro q; simp_rw [V, alias_zero_loc, smul_comm (inch P.L)]; exact p i j _
  change Rays (t+1) (fun x=> skyline S (V x) (A x) (B x)- μ^2* rowscape S (V x) a b); simp_rw [hh]
  have ha i : Rays 1 (fun x : Track=>(A x-u) i) := by
    have he : AnalyticAt ℝ (fun x=>A x i) 0 := by
      simp_rw [A,← axes_flip]
      exact (show AnalyticAt ℝ (fun (x : Track)=> nose X (axes x) 0 a i) (-0) by rw [neg_zero]; exact wellNose hp hs a i).comp analyticAt_id.neg
    exact (rays_at_zero (he.sub (analyticAt_const (v:=u i)))).mpr (by simp [A,hx,u,μ])
  have hb i : Rays 1 (fun x : Track => (B x-v) i) := by
    exact (rays_at_zero ((wellNose (l:=0) hp hs b i).sub (analyticAt_const (v:=v i)))).mpr (by simp [B,v,hx,μ])
  have hu := rowray (fun x => A x-u) B V hV ha (fun i=> rays_zero (wellNose hp hs b i))
  have hq := rowray (fun _ => u) (fun x=> B x-v) V hV (fun i=> rays_zero (f:=fun x : Track=> u i) analyticAt_const) hb
  rw [Nat.add_zero, Nat.add_comm 1 t] at hu; rw [Nat.zero_add] at hq
  exact hu.add hq
end basal
end YM.Stationary
end

/-! # Preservation. Only low normal needed. Width δ independent from
qualitative inheritance; A0.Photo h? zero spin. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {k : Clip} {K : KernelChoices} {σ η τ A C D F ε Ω ν χ Υ : ℝ} {c f L : Side} {m n : ℕ→Side} {p q : Momentum} {B T : Bed} {X : Bridge G P} {S H : Picture G 1}

lemma canyons (h : ∀ i,Contractible (S i)) (hl : ∀ i j,Firm σ A (S i j))
    (hp : ∀ l : Site P.L,l≠0→ ∀ i j,Rays 2 (fun v : Track=> horizontal X (axes v) l i j)) (a b : Loc G 1) (l : Site P.L) (hz : l≠0) :
    Rays 4 (fun x : Track => skyline S (aliasAt (axes x) l) (nose X (-(axes x)) (-l) a) (nose X (axes x) l b)) := by
  simp_rw [happy_sky h _ (axes_real _)]
  let U x := aliasAt (axes x) l
  have hu i j : Rays 0 (fun x=> rowscape S (U x) i j) := by
    apply ray_constant_here
    have hx : Continuous U := (show Continuous (fun p:Momentum => aliasAt p l) by unfold aliasAt; fun_prop).comp axes_maps.continuous
    exact (skyline_meets hl (p:=U 0) (by unfold U; simp [← alias_conj]) i j).comp hx.continuousAt
  refine rowray _ _ U hu ?_ (fun i => hp l hz b i)
  intro i v
  have ht := hp (-l) (neg_ne_zero.mpr hz) a i (-v); simp_rw [smul_neg,axes_flip] at ht; exact ht

lemma raysA_ink {t} (hp : ∀ i j, Rays t (S i j ∘ axes)) : RaysP t S := by
  intro i j b; have ht := hp ![i.2,j.2] ![i.1,j.1] (roads b)
  change _ =O[cutRay] _ ; exact ht
lemma inkA_rays {t} (hp : RaysP t S) : ∀ i j, Rays t (S i j ∘ axes) := by
  intro i j b
  obtain ⟨b,rfl⟩ := roads.surjective b
  have ht := hp (j 0,i 0) (j 1,i 1) b
  have hi : ![i 0,i 1]=i := funext fun k => by fin_cases k <;> rfl
  have hh : ![j 0,j 1]=j := funext fun k => by fin_cases k <;> rfl
  simp only [rowscape,Matrix.of_apply,hi,hh] at ht; exact ht

section rules
-- require standing equations only on real. K_hp all p.
variable (hs : 0<σ) (h : Poster σ X) (he : B.metric.strip η A) (hp : 0<η) (hT : T.metric.strip τ F) (hτ : 0<τ) (hw : ∀ n, Floor B k n ε C) (hε : 0<ε)
    (hr : ∀ i, Contractible (S i)) (hl : ∀ i j,Firm χ Υ (S i j))
    (hx : ∀ v : Momentum, star v=v → primalV X B T v)
    (hh : ∀ p : Momentum, star p=p → ∀ a b, rowscape H p a b=carryRow X S p a b)
include hs h he hp hT hτ hw hε hr hl hx hh

lemma weaken_cop {t : ℕ} (hy : t≤4) (hq : RaysP t S) : RaysP t H := by
  intro a b
  have hr' l (hz : l≠(0:Site P.L)) := canyons hr hl (fun l hl a i=> high_halo hl a i he hp hw hε hT hτ (B:=B) (T:=T) (X:=X) (fun j=> hx _ (axes_real j))) a b l hz
  simp_rw [hh _ (axes_real _)]
  let B (l : Site P.L) := fun x : Track=> skyline S (aliasAt (axes x) l) (nose X (-(axes x)) (-l) a) (nose X (axes x) l b)
  have hB : ∀ l,Rays t (B l) := by
    intro l; by_cases h : l=0
    · subst l; simpa only [B,neg_zero] using! central_competence ‹Poster σ X› hs hq a b
    exact (hr' l h).weaker hy
  intro u; exact ((rays_total hB) u).const_mul_left _

lemma fine_alpha {ω₀} (hU : secondV X T ω₀ 0) (hH : ∀ i j,Firm ν Ω (H i j)) (hg : RaysP 2 S) (y : G.ColorIndex) : alphaPay y H=alphaPay y S := by
  let a := ((coord 1,y):Loc G 1)
  let M := pressLens S ![y,y] 1 1
  let K := pressLens H ![y,y] 1 1; let v := (step (0:Axis) : Track)
  have hr' l (hz : l≠(0:Site P.L)) := canyons hr hl (fun l hl a i=> high_halo hl a i he hp hw hε hT hτ (B:=B) (T:=T) (X:=X) (fun j=> hx _ (axes_real j))) a a l hz
  let μ := inch P.L
  let c : ℝ := (P.L.val:ℝ)^4
  let f : Track→L[ℝ] Track := μ • ContinuousLinearMap.id ℝ Track
  let L := c • (μ^2 • (M ∘ f))
  have h0 := anchored _ X B T hx hU he hp hT hτ hw hε
  have hu := canonicalGap h hs hg a a h0
  let g l x := skyline S (aliasAt (axes x) l) (nose X (-(axes x)) (-l) a) (nose X (axes x) l a)
  have hy : Rays 3 (K-L) := by
    let b := univ.erase (0:Site P.L)
    have ht x : K x=c • ((∑ l∈b,g l x)+ g 0 x) := by
      change rowscape H (axes x) a a=c • ((∑ l∈b,g l x)+g 0 x)
      rw [sum_erase_add _ _ (mem_univ _), hh _ (axes_real _)]; unfold c; rw [Complex.real_smul,Complex.ofReal_pow]; rfl
    intro x
    have hr := Asymptotics.IsBigO.sum (s:=b) (A:=fun l (v':ℝ) => g l (v' • x)) (fun i hi=> ((hr' i (Finset.ne_of_mem_erase hi)).weaker (by decide : 3≤4)) x)
    have hh : Rays 3 (fun x : Track=> g 0 x-μ^2 • M (f x)) := by
      unfold g; simp only [neg_zero]; convert hu using 1
      ext1 v; dsimp only; rw [alias_zero_loc, Complex.real_smul, Complex.ofReal_pow]; rfl
    have hv := (hr.add (hh x)).const_mul_left (c:ℂ)
    refine hv.congr_left (fun k=> ?_)
    change (↑c:ℂ)*((∑ i∈b,g i (k • x))+(g 0 (k • x) - μ^2 • M (f (k • x))))= K (k • x)-c • μ^2 • M (f (k • x)); rw [ht]; simp only [Complex.real_smul]; ring
  have hk : AnalyticAt ℝ K 0 := priceL hH ..
  have hm : AnalyticAt ℝ M 0 := priceL hl ..
  have hn : AnalyticAt ℝ (M ∘ f) 0 := ((show ContDiffAt ℝ ω M (f 0) by rw [map_zero]; exact hm.contDiffAt).comp (f:=fun x => f x) (0:Track) f.contDiff.contDiffAt).analyticAt
  have hL : AnalyticAt ℝ L 0 := hn.const_smul.const_smul
  have hx := (rays_jet (hk.sub hL) 3).mp hy 2 (by norm_num); rw [iteratedFDeriv_sub_apply hk.contDiffAt hL.contDiffAt] at hx
  have hv : speedy K 2 v=speedy M 2 v := by
    unfold speedy Tensor.diagonal Tensor.coeff; rw [sub_eq_zero.mp hx,_root_.smul_apply,_root_.smul_apply]; apply congr_arg; unfold L
    rw [iteratedFDeriv_const_smul_apply ((hn.const_smul (c:=μ^2)).contDiffAt),_root_.smul_apply,iteratedFDeriv_const_smul_apply hn.contDiffAt,_root_.smul_apply, wired f (by rw [map_zero]; exact hm), map_zero]; unfold f; simp only [Function.comp_def, _root_.smul_apply,ContinuousLinearMap.id_apply]
    rw [show iteratedFDeriv ℝ 2 M 0 (fun _ => μ • v) = _ from (iteratedFDeriv ℝ 2 M 0).toMultilinearMap.map_smul_univ (fun _ => μ) (fun _ => v)]; simp only [Finset.prod_const,card_univ,Fintype.card_fin,ContinuousMultilinearMap.coe_coe,smul_smul]
    rw [show c*(μ^2*μ^2)=1 by unfold c μ inch; field_simp,one_smul]
  exact congr_arg (fun x : ℂ => (2:ℝ)*x.re) hv
end rules
end YM.Stationary
end

/-! # Kinetic reduction to transverse fine test. Does not assert values at
 nonactual periods. The StepCard.X remains; predictor on realization.
 -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {K : KernelChoices} {k : Clip} {B T : Bed} {σ ε η A C D F δ Θ τ E Ω ν γ w : ℝ} {c f : Side} {m n : ℕ→Side}

lemma pole_reduced {R : PathData G} {X : Bridge G P} {Y : Spark (Loc G 1) G P} {M : Eye (Loc G 1) (Acts G P)} {Q : PostCard R k P K M Y m n} (W : TicketPost Q δ B T)
    (hh : G.Simple) (hx : Poster σ X) (hp : 0<σ) (hs : R.Bounds k τ C D)
    (hy : T.metric.strip σ A) (hb : B.metric.strip (inch P.L*σ) A) (hr : Screened (rankCue M Y) γ Ω) (hw : ∀ n, Floor B k n ε Θ) (he : 0< ε)
    (hk : ∀ i, Bid.Sworn B (n i) G) (hi : Attached B R) (hu : ∀ i, Premise (Q.ship.boot i) (W.mat i) X) (hν : 0 < γ)
    (ht : Tendsto (fun i => (m i).val) atTop atTop) (a : G.ColorIndex) {πX : Picture G 1} (hd : ∀ i j,Firm ν E (πX i j))
    {e : ℕ→ℝ} (hQ : Tendsto e atTop (𝓝 0)) (hP : ∀ i,Recorded πX (PoleTest k R (inch P.L) (n:=n i)) (cents (n i)*e i)) : alphaPay a (profitable (rankCue M Y))=alphaPay a πX := by
  let t := (coord 1,a)
  obtain ⟨H,H'⟩ := profit (rankCue M Y) hν ((hr.earns t t).budget_nonneg) hr.earns
  let Z i := PoleTest (n:=n i) k R (inch P.L)
  have hm : Tendsto (fun i => (n i).val) atTop atTop := tendsto_atTop_mono (fun i=> (show (m i).val ≤ (n i).val from by rw [Q.ship.binds]; exact Nat.le_mul_of_pos_right _ P.L.pos)) ht
  have hK i := pole_peaks k R (inch P.L) hh hs (inch_pos _) (rank_positive (n:=n i) (inch P.L) hs (hw (n i)) hi (hk i) (inch_pos _) |>.isUnit)
  have he' : TributeColor πX ν E Unsigned := tributing hm hd hQ hP (fun i => (hK i).1.analyticAt) (fun i => pole_green k R (inch P.L) hs (inch_pos _)) (fun i => pole_colored k R (inch P.L) hs (inch_pos _)) (fun i d hl he => by
    rw [show d=1 by omega]; ext1 x; rw [iteratedFDeriv_one_apply,(hK i).2]; rfl) (fun i s hi => pole_flip k R (inch P.L) hs (inch_pos _) s hi)
  have hr : RaysP 2 πX := by
    intro x y
    rcases x with ⟨x,i⟩; rcases y with ⟨y,j⟩
    obtain ⟨x,rfl⟩ := axisEquiv.surjective x; obtain ⟨y,rfl⟩ := axisEquiv.surjective y
    exact he'.crop_edict (fun _ h=> h) ![i,j] x y
  have HQ (i) := questPole (Q.ship.boot i) (Q.tags i) hs hi (hw _) (hk i) (W.mat i) (W.event i) (W.shades i)
  let y i := (royalty γ Ω)* Real.exp (-(γ/4)*(m i).val)
  have Hx i : Recorded (profitable (rankCue M Y)) (Z i ∘ uniformM (W.mat i)) (cents (m i)* y i) := H' _ _ (HQ i)
  have hB p (v : star p=p) := actor_duo Q.ship hp hy hp hb hp hx ht hu W.sworn (p:=p) v
  exact fine_alpha hp hx hb (mul_pos (inch_pos _) hp) hy hp hw he he'.wall hd (fun i hp=> (hB i hp).1) (fun i h=> carry_plan Q.ship hx hp hd H hu (fun i=> (hK i).1.analyticAt) hP Hx hQ (mesh_tend _ ht (by positivity : 0<γ/4)) ht h) ((hB 0 (by simp)).2) H hr a
end YM.Stationary
end
