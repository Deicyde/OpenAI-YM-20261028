import YM.Next.STATIONARY.Films.Contact



set_option autoImplicit false
/-!
# Two-wave authority over actual physical Fourier data. Pull to limit
with real arguments only. Γ continuation law never asserted on arbitrary
complex interpolation. `Flags` includes any torus sequence with winding.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {ε : ℕ→ℝ} {n : ℕ → Side} {σ A : ℝ}
section march
variable {F : ∀ i, Link G (n i)→ℝ} {f : Picture G 1} (h : ∀ i j, Firm σ A (f i j))
    (hf : ∀ p,Recorded f (F p) (cents (n p)* ε p))

include h
/-- Signed action REAL (basis symmetry). No translation needed if recorded.
Requires rotation of the SCALAR score. -/
lemma signed_crumb (s : Signed) {m : Side} {L : Link G m → ℝ} {e : ℝ}
    (hL : AnalyticAt ℝ L 0) (hp : Recorded f L e) (hv : L ∘ (orderTurn s)=ᶠ[𝓝 0] L) :
    Recorded (rotPix s f) L e := by
  intro p i b
  let r := s.perm.symm ∘ axisEquiv.symm ∘ b
  have hh : (fun j => coord (s.perm (r j)))=b := by
    ext1 j; simp only [r,Function.comp_apply,s.perm.apply_symm_apply]; exact axisEquiv.apply_symm_apply _
  let k := s⁻¹.act ∘ p
  let X := ∏ j, reflectFee s (mon (p j)) (r j)
  have ht : noteAt L _ (glyph p i b)= X * noteAt L _ (glyph k i (coord ∘ r)) := by
    have he := priceNote L hL s p i r
    rw [show noteAt (L ∘ orderTurn (m:=m) (G:=G) s) (1+1) = noteAt L (1+1) by unfold noteAt beat; rw [(hv.iteratedFDeriv ℝ (1+1)).eq_of_nhds], hh] at he; exact he
  have hK : ∑ j,k j=s⁻¹.act (∑ j,p j) := (map_sum (s⁻¹.actEquiv (R:=Per m)) p univ).symm
  have he : collected (rotPix s f) p i b=X*collected f k i (coord ∘ r) := by
    unfold collected
    have hP : (∑ j,k j)=0 ↔ (∑ j,p j)=0 := by
      rw [hK]; conv_lhs => rhs; rw [← show s⁻¹.act 0=(0:Site m) from Signed.act_zero _]
      exact s⁻¹.act_injective.eq_iff
    simp only [hP]; split <;> rename_i h0
    · have hi := rotate_lifts s p _ (rolls.refl (outphase p))
      have hq := h i (coord ∘ r)
      have hy := path_roll s p h0 _ (rolls.refl (outphase p)) r
      rw [hi.apply hq (hq.in_range (out_real k))]; unfold X rotPix; simp_rw [← hy]; exact mul_left_comm ..
    rw [mul_zero]
  rw [ht, he, ← mul_sub, norm_mul]; rw [show ‖X‖=1 by simp [X,reflect_size],one_mul]; exact hp ..

include h hf
lemma turn_stage (hs : Tendsto (fun i => (n i).val) atTop atTop) (hp : Tendsto ε atTop (𝓝 0))
    (s : Signed) (hq : ∀ i, AnalyticAt ℝ (F i) 0) (he : ∀ i, F i ∘ orderTurn (G:=G) (m:=n i) s=ᶠ[𝓝 0] F i) (p : Corn (Keys 1)) (i j) :
    f i j (axes p)=rotPix s f i j (axes p) := by
  obtain ⟨u,v,H,e⟩ := fleet n hs (axes p) (axes_real p)
  exact tendsto_nhds_unique (harvest h hf hp p u v H e i j) (harvest (pix_firm s h) (fun i => signed_crumb h s (hq i) (hf i) (he i)) hp p u v H e i j)
lemma cross_stage (hs : Tendsto (fun i => (n i).val) atTop atTop) (hp : Tendsto ε atTop (𝓝 0))
    (hx : ∀ i, AnalyticAt ℝ (F i) 0) (p : Corn (Keys 1)) (i l : G.ColorIndex) (a b : TypeFace 1) :
    f ![i,l] ![a,b] (axes p)=f ![l,i] ![b,a] (axes (-p)) := by
  let d : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  obtain ⟨P,V,hV,hy⟩ := fleet n hs (axes p) (axes_real p)
  let Q (x : ℕ) := P x ∘ d
  have hu t : ∑ i, Q t i=0 ∧ rolls (outphase (Q t)) (-V t) := by
    have ht : Q t=-P t := by
      have he := hy t |>.1
      rw [show ∑ i, P t i = P t 0+P t 1 from Fin.sum_univ_two _] at he
      ext1 i; fin_cases i
      · exact eq_neg_of_add_eq_zero_right he
      exact eq_neg_of_add_eq_zero_left he
    exact ⟨(Equiv.sum_comp d (P t)).trans (hy t).1,by rw [ht]; exact (reflection_negative _).trans (hy t).2.neg⟩
  have hm := harvest h hf hp p P V hV hy ![i,l] ![a,b]
  have he t : standing n F Q ![l,i] ![b,a] t= standing n F P ![i,l] ![a,b] t := by
    unfold standing; congr 1
    rw [show glyph (Q t) ![l,i] ![b,a]=glyph (P t) ![i,l] ![a,b] ∘ d from funext (fun x => by fin_cases x <;> rfl)]
    exact note_perm _ (hx t) _ d
  refine tendsto_nhds_unique hm ?_
  rw [← funext he]
  exact harvest h hf hp (-p) Q _ (axes_flip p |>.symm ▸ hV.neg) hu ![l,i] ![b,a]
end march
end YM.Stationary
end

/-! # Leading Ward jets in external positive oriented two-links. Precision
and coefficient differ by TWO. Real p/tips. Symmetries passed through limit
from actual meshes using `harvest`; no continuous stationarity postulate.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ}

abbrev Track := Corn Axis
def roads : Track ≃L[ℝ] Corn (Keys 1) := LinearEquiv.toContinuousLinearEquiv {
    toFun x := x ∘ Prod.snd
    invFun p := fun j => p (0,j)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv _ := rfl
    right_inv p := funext fun ⟨j,i⟩ => by fin_cases j; rfl
}

def pressLens (f : Picture G 1) (i : Ink G 2) (a b : Axis) (p : Track) : ℂ := f i ![coord a,coord b] (axes (roads p))
lemma priceL {f : Picture G 1} (h : ∀ i j,Firm σ A (f i j)) (i a b) : AnalyticAt ℝ (pressLens f i a b) 0 :=
    ((h _ _).analytic_real (roads 0)).comp (roads.analyticAt _)
def speedy {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (t : ℕ) : X → Y := Tensor.diagonal (Tensor.coeff f t 0)

variable {f : Picture G 1} (h : Features f σ A)
include h
lemma trim_zero (i a b) : Rays 1 (pressLens f i a b) := by
  intro p
  have he : Rays 1 (f i ![coord a,coord b] ∘ axes) := rayDark i ![coord a,coord b] (by decide) h.solid (fun i a b => by
    intro v; apply Asymptotics.IsBigO.congr_left (Asymptotics.isBigO_zero ..); intro u
    change (0:ℂ)=_
    exact (h.wall i (u • v) b a).symm)
  have hp := he (roads p); unfold pressLens; simp_rw [map_smul]; exact hp
lemma pay_corner (i a b k) (hp : Rays k (pressLens f i a b)) (p) : Tendsto (fun v : ℝ => (v^k)⁻¹ • f i ![coord a,coord b] (axes (roads (v • p)))) cutRay
    (𝓝 (speedy (pressLens f i a b) k p)) := ray_limit (priceL h.solid ..) hp _

-- Leading right contraction at every order (with simultaneous lower jets killed)
lemma precipice (u : Ink G 2) {r} (hp : ∀ i j,Rays r (pressLens f u i j)) (p : Track) (i : Axis) :
    ∑ x : Axis, (p x : ℂ) * speedy (pressLens f u i x) r p=0 := by
  let a : Run 2 := ![coord i,coord i]
  let F x : Corn (Keys 1) → ℂ := fun k => speedy (pressLens f u i (axisEquiv.symm x)) r (roads.symm k)
  have H (x : Axis) : update a (0:Fin 1).succ (axisEquiv x)=![coord i,coord x] := by ext1 j; fin_cases j <;> simp [a]
  have hx := ring_ray f u a F (0:Fin 1) (fun a p => ?_) (?_ : Rays (r+1+1) (crux u a _ f ∘ axes)) (roads p)
  · have he x : F (coord x) (roads p)=_ := (show F (coord x) (roads p) = speedy (pressLens f u i x) r p by
      unfold F; rw [← coord_map, axisEquiv.symm_apply_apply, roads.symm_apply_apply])
    simp_rw [he] at hx; exact hx
  · obtain ⟨x,rfl⟩ := axisEquiv.surjective a; obtain ⟨P,rfl⟩ := roads.surjective p
    unfold F; rw [H,roads.symm_apply_apply,axisEquiv.symm_apply_apply]
    simpa only [map_smul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow] using pay_corner h _ _ _ _ (hp i x) P
  intro v; apply (Asymptotics.isBigO_zero ..).congr_left; intro b; exact (h.wall u (b • v) _ _).symm

-- unsigned means *all* +. Flips conditioned by allowed policy.
def signStar (s : Signed) (k : Axis) : ℂ := if s.flip k then -1 else 1
structure TributeColor (f : Picture G 1) (σ A : ℝ) (admitS : Signed → Prop) : Prop extends Features f σ A where
    perm (p : Track) (u v : G.ColorIndex) (a b : Axis) : pressLens f ![u,v] a b p=pressLens f ![v,u] b a (-p)
    law (p : Corn (Keys 1)) (i a) (s : Signed) : admitS s → f i a (axes p)=rotPix s f i a (axes p)

omit h
variable {adm : Signed→Prop}
lemma tributing {m : ℕ→ Side} {F : ∀ i, Link G (m i) → ℝ} {ε : ℕ→ℝ} (hm : Tendsto (fun i => (m i).val) atTop atTop)
    (he : ∀ i j,Firm σ A (f i j)) (hd : Tendsto ε atTop (𝓝 0)) (hf : ∀ i, Recorded f (F i) (cents (m i)*ε i))
    (hA : ∀ i, AnalyticAt ℝ (F i) 0) (hV : ∀ i, force (F i)) (hp : ∀ i, Stained G (F i)) (ht : ∀ i, Quiets (F i) (1+1)) (hW : ∀ p, ∀ s : Signed, adm s → F p ∘ orderTurn (G:=G) (m:=m p) s=ᶠ[𝓝 0] F p) : TributeColor f σ A adm := {
    toFeatures := withdrew hm hd he hf hA hp hV ht
    perm := fun p u v a b => by unfold pressLens; rw [map_neg]; exact cross_stage he hf hm hd hA ..
    law := fun p i a s hs => turn_stage he hf hm hd s hA (fun i => hW i s hs) p i a }

namespace TributeColor
variable (heW : TributeColor f σ A adm)
include heW
lemma leading_shift {r : ℕ} {s : Signed} (ht : adm s) (i) (hp : ∀ a b, Rays r (pressLens f i a b)) (a b : Axis) (p : Track) :
    speedy (pressLens f i (s.perm a) (s.perm b)) r (s.act p)= signStar s a*signStar s b* speedy (pressLens f i a b) r p := by
  let L (v : ℝ) (k j : Axis) := reflectFee s (axes ((v • p) : Track)) k * reflectFee s (axes ((v • p) : Track)) j
  let z (v : ℝ) := v • s.act p
  let K (j : Fin (1+1)) (v : ℝ) := reflectFee s (plotted (axes (roads (z v))) j) (![a,b] j)
  have he (j) : Tendsto (K j) cutRay (𝓝 (signStar s (![a,b] j))) := by
    let g : Corn (Keys 1) → ℂ := fun x => reflectFee s (plotted (axes x) j) (![a,b] j)
    have hh := (reflect_firm s (σ:=1) (by norm_num) j (![a,b] j)).analytic_real 0
    have hp' := hh.continuousAt.tendsto.comp (along (roads (s.act p)))
    have ht : plotted (axes 0) j = 0 := by refine Fin.cases ?_ (fun _ => ?_) j <;> simp [plotted,missing,axes_origin,projected]
    unfold K; simp only [z,map_smul]; simpa only [Function.comp_apply, ht, reflectFee, mode_constant,signStar] using! hp'
  have hb := (he 0 |>.mul (he 1)).mul (pay_corner heW.toFeatures i a b r (hp a b) p)
  apply tendsto_nhds_unique (pay_corner heW.toFeatures i (s.perm a) (s.perm b) r (hp _ _) (s.act p))
  refine hb.congr' ?_
  filter_upwards with v
  have H : f i ![coord (s.perm a),coord (s.perm b)] (axes (roads (z v)))=
      K 0 v*K 1 v*f i ![coord a,coord b] (axes (roads (v • p))) := by
    rw [heW.law _ _ _ s ht]; unfold rotPix; dsimp only
    rw [show s.perm.symm ∘ axisEquiv.symm ∘ ![coord (s.perm a),coord (s.perm b)]=![a,b] by
      ext1 j; fin_cases j <;> simp [← coord_map]]
    have hp : rotatePhase s (axes (roads (z v)))=axes (roads (v • p)) := by
      ext1 ⟨i,j⟩; unfold rotatePhase; rw [show projected (strand i) (axes _) = s.act (axes (v • p)) by
        ext1 k; obtain ⟨k,rfl⟩ := s.perm.surjective k; change ((z v (s.perm k)):ℂ) = _; rw [s.act_at]; unfold z; simp only [Pi.smul_apply,s.act_at]; split <;> simp [axes]]
      rw [s.inv_act]; rfl
    rw [hp,Fin.prod_univ_two,show coord ∘ ![a,b]=![coord a, coord b] by ext1 j; fin_cases j <;> rfl]
  rw [H]; simp only [Complex.real_smul]; ring

lemma mirrors {r : ℕ} (hz : ∀ i j a,Rays r (pressLens f i j a)) (u v : G.ColorIndex) (a b) (p : Track) :
    speedy (pressLens f ![u,v] a b) r p= speedy (pressLens f ![v,u] b a) r (-p) := by
  have ht := ray_limit (priceL heW.solid ![u,v] a b) (hz _ _ _) p
  have hu := ray_limit (priceL heW.solid ![v,u] b a) (hz _ _ _) (-p)
  simp_rw [smul_neg, ← heW.perm] at hu; exact tendsto_nhds_unique ht hu
lemma paired_rule {r : ℕ} (hp : ∀ i a b, Rays r (pressLens f i a b)) (u : Ink G 2) (p : Track) (i : Axis) :
    ∑ x : Axis, (p x : ℂ) * speedy (pressLens f u x i) r p=0 := by
  have hv := precipice heW.toFeatures ![u 1,u 0] (hp _) (-p) i
  simp only [Pi.neg_apply,Complex.ofReal_neg, neg_mul] at hv
  simp_rw [← heW.mirrors hp (u 0) (u 1)] at hv
  rw [sum_neg_distrib,neg_eq_zero,show ![u 0,u 1]=u by ext1 i; fin_cases i <;> rfl] at hv; exact hv
end TributeColor
end YM.Stationary
end

/-!
# Change at infinite Fourier volume. Takes actual mesh identities and
angle costs. No asymptotic needed for rooting costs.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {σ θ A C D γ η : ℝ} {m : ℕ→Side}

lemma stock_sway {F : Momentum→Momentum→ℂ} (h : Firm σ A (starTrack F)) (hm : Tendsto (fun i => (m i).val) atTop atTop) {p : Momentum} (hp : star p=p) (q : ℕ→Momentum) (he : Tendsto q atTop (𝓝 p)) (hv : ∀ i,star (q i)=q i) :
    Tendsto (fun i => shop (m i) (F (q i))) atTop (𝓝 (stock (F p))) := by
  have hs := h.width_pos
  let f := fun p => stock (F p)
  have hx : ContinuousAt f p := by
    have ht := fireworks F h (b:=σ/2) (by linarith) (by linarith)
    exact (ht.1.hol p (ht.in_range hp)).continuousAt
  let g i := shop (m i) (F (q i))
  have hf : Tendsto (fun i => g i-f (q i)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _ => norm_nonneg _) (fun i => (stock_take F h (Work.F07.realStrip _ hs (hv i))).tryout (m i)) (mesh_tend _ hm (by linarith : 0 < σ/4))
  have hh := hf.add (hx.tendsto.comp he)
  rw [zero_add] at hh; simpa only [Function.comp_apply, Pi.add_apply, sub_add_cancel] using hh

lemma tax_cont (B : Bed) (h : B.metric.strip σ A) (hp : 0<σ) (x : Loc G 1) (v : Momentum) (hx : star v=v) (i : Loc G 1) : ContinuousAt (fun v => taxTone G B v x i) v := by
  let F z := rug G B z i x
  have he : ContinuousAt F v := ((rug_played B h hp).shape (Work.F07.realStrip _ hp hx) i x).continuousAt
  simp_rw [taxTone,Pi.neg_apply,Matrix.mulVec_single_one]; exact he.neg
lemma tax_ray (B : Bed) (h : B.metric.strip σ A) (hp : 0<σ) (x i : Loc G 1) : Rays 2 (fun k : Track => taxTone G B (axes k) x i) := by
  simp_rw [taxTone,Pi.neg_apply,Matrix.mulVec_single_one]
  have he p : rug G B p=tintedLocal G (dcross B.metric p) := by simp only [rug,pageD,tessH,dcross,tinted_pay,tinted_flip]
  simp_rw [he, tintedLocal]; change Rays 2 (fun k : Track=> -(if i.2=x.2 then dcross B.metric (axes k) i.1 x.1 else 0)); split
  · have hv u v : Rays 0 (fun p : Corn Axis => B.metric.read (axes p) u v-(0:FaceRow).read (axes p) u v) := by
      have he p : (0:FaceRow).read p u v=0 := by simp [Row.read,Laurent.read]
      simp_rw [he,sub_zero]; exact rays_zero ((price_step_metric hp h u v).analytic_real _)
    have hz p : dcross (0:FaceRow) p=0 := by
      unfold dcross; rw [show (0:FaceRow).read p=0 by ext i j; simp [Row.read,Laurent.read]]; simp
    intro v; have hh := bed_gain _ _ hv i.1 x.1 v; simp_rw [hz,Matrix.zero_apply,sub_zero] at hh; exact hh.neg_left
  simp only [neg_zero]; intro v; exact isBigO_zero ..

section budget
variable {F : Film (ScoreBoard G) β β} (hp : 0<σ) (h : Play F σ)
include h hp
lemma star_analytic (x y) (z : Track) : AnalyticAt ℝ (fun p : Track=> stock (hatchTrace F x y (axes p))) z := by obtain ⟨A,hA⟩ := trace_spot hp h x y; exact ((fireworks (hatchTrace F x y) hA (b:=σ/8) (by linarith) (by linarith))).analytic_real z

lemma alpha_night (hm : Tendsto (fun i=> (m i).val) atTop atTop) (j : Loc G 1)
    (hs : ∀ i,∀ p : Site (m i),∀ q, rolls (mon p) q → ∀ x : Phase (Loc G 0), (∑ u : Loc G 1,(pageD G 0 (-q)*ᵥ x) u*shop (m i) (hatchTrace F (.inl u) (.inr j) q))=0) :
    ∀ p : Momentum, star p=p → ∀ x : Phase (Loc G 0),(∑ u : Loc G 1,(pageD G 0 (-p)*ᵥ x) u*stock (hatchTrace F (.inl u) (.inr j) p))=0 := by
  intro p hp' x
  obtain ⟨k,v,hK,hv⟩ := mesh_stride m hm p hp'
  have hb (u : Loc G 1) : _ := trace_spot hp h (.inl u) (.inr j)
  have hx u : ContinuousAt (fun p => (pageD G 0 (-p)*ᵥ x) u) p := by
    let H : Poster σ (pageD G 0) := page_linen _
    have hh i := ((H.shape (negResident (Work.F07.realStrip _ hp hp')) u i).continuousAt).comp continuous_neg.continuousAt
    exact tendsto_finsetSum univ fun i _ => (hh i|>.mul_const (x i)).tendsto
  choose L hL using hb
  have hl := tendsto_finsetSum univ fun u _ => ((hx u).tendsto.comp hK).mul (stock_sway (hL u) hm hp' v hK (fun i => (hv i).metric (real_frequency _)))
  refine tendsto_nhds_unique_of_eventuallyEq hl tendsto_const_nhds (Eventually.of_forall fun i => ?_)
  exact hs _ _ _ (hv i) _
lemma star_low (j : Loc G 1) (hX : ∀ p : Momentum, star p=p → ∀ x : Phase (Loc G 0),(∑ u : Loc G 1,(pageD G 0 (-p)*ᵥ x) u*stock (hatchTrace F (.inl u) (.inr j) p))=0) (i : Loc G 1) :
    Rays 1 (fun p : Track=> stock (hatchTrace F (.inl i) (.inr j) (axes p))) := by
  apply (rays_at_zero (star_analytic hp h _ _ 0)).2
  let w : Axis := axisEquiv.symm i.1
  let x : Phase (Loc G 0) := Pi.single (vac,i.2) 1
  let M (p : Track) := stock (hatchTrace F (.inl i) (.inr j) (axes p))
  have he t : Exterior.q (axes (-(t:ℝ) • step w)) w * M (t • step w)=0 := by
    have ht : axes (-(t:ℝ) • step w) = - axes (t • step w) := by rw [neg_smul,axes_flip]
    rw [ht]
    let z : Momentum := axes (t • step w)
    have hv := hX z (axes_real _) x
    rw [sum_eq_single i, curtain, show x (vac,i.2)=1 by simp [x],mul_one] at hv
    exact hv
    · intro b _ hz; rcases b with ⟨u,l⟩; rw [curtain]; by_cases h : i.2=l; swap; · simp [x, Pi.single_apply,h,Ne.symm h]
      have he : axisEquiv.symm u≠w := by
        intro he; apply hz; exact Prod.ext (axisEquiv.symm.injective he) h.symm
      rw [show Exterior.q (-z) (axisEquiv.symm u)=0 by simp [Exterior.q,z,axes,he]]; simp
    simp
  have hv : ∀ᶠ t : ℝ in cutRay, M (t • step w) =0 := by
    have hu := divisor_nonzero (r:=0) (-1) (by norm_num)
    filter_upwards [hu] with t ht
    exact (mul_eq_zero.mp (he t)).resolve_left (by simpa [Exterior.q,axes] using ht)
  exact tendsto_nhds_unique_of_eventuallyEq ((star_analytic hp h (.inl i) (.inr j) 0).continuousAt.tendsto.comp (along (step w))) tendsto_const_nhds hv

variable {Y : Award G} (B : Bed) (ht : B.metric.strip γ D) (hC : Screened Y η C)
include ht hC
lemma active (hv : 0<γ) (hm : Tendsto (fun i=> (m i).val) atTop atTop) (i j : Loc G 1)
   (H : ∀ l,∀ u : Site (m l),∀ q, rolls (mon u) q →
    let x := taxTone G B (-q) i
    let y := taxTone G B q j
    shop (m l) (Y i j q)= (1/2:ℂ)*(
      ((∑ a,y a * shop (m l) (hatchTrace F (.inl i) (.inr a) q)) + (∑ a,x a * shop (m l) (hatchTrace F (.inl j) (.inr a) (-q)))) -
         (1/2:ℂ)* ∑ a,x a*∑ b,y b*shop (m l) (hatchTrace (F.pay F) (.inr a) (.inr b) q))) :
    ∀ q : Momentum,star q=q →
    let x := taxTone G B (-q) i; let y := taxTone G B q j
    stock (Y i j q)= (1/2:ℂ)*(
      ((∑ a,y a * stock (hatchTrace F (.inl i) (.inr a) q)) + (∑ a,x a * stock (hatchTrace F (.inl j) (.inr a) (-q)))) -
         (1/2:ℂ)* ∑ a,x a*∑ b,y b*stock (hatchTrace (F.pay F) (.inr a) (.inr b) q)) := by
  intro q hq
  obtain ⟨l,k,hl,hL⟩ := mesh_stride m hm q hq
  have hq' : star (-q)=-q := by rw [star_neg,hq]
  have hx v := tax_cont B ht hv i (-q) hq' v
  have hy v := tax_cont B ht hv j q hq v
  have he (i : ℕ) := (hL i).metric (real_frequency _)
  have hg (i) : star (-(k i))= -(k i) := by rw [star_neg, he]
  have hi a : Tendsto (fun i'=> shop (m i') (hatchTrace F (.inl i) (.inr a) (k i'))) atTop (𝓝 (stock (hatchTrace F (.inl i) (.inr a) q))) := by
    obtain ⟨b,hb⟩ := trace_spot hp h (.inl i) (.inr a); exact stock_sway hb hm hq k hl he
  have hV a : Tendsto (fun i' => shop (m i') (hatchTrace F (.inl j) (.inr a) (-k i'))) atTop (𝓝 (stock (hatchTrace F (.inl j) (.inr a) (-q)))) := by
    obtain ⟨b,hb⟩ := trace_spot hp h (.inl j) (.inr a); exact stock_sway hb hm hq' (fun i => -k i) hl.neg hg
  have hM a b : Tendsto (fun i' => shop (m i') (hatchTrace (F.pay F) (.inr a) (.inr b) (k i'))) atTop (𝓝 (stock (hatchTrace (F.pay F) (.inr a) (.inr b) q))) := by
    obtain ⟨c,hc⟩ := trace_spot hp (h.pay h) (.inr a) (.inr b); exact stock_sway hc hm hq k hl he
  have hY := tendsto_finsetSum univ fun i _ => ((hy i).tendsto.comp hl).mul (hi i)
  have hh := tendsto_finsetSum univ fun i _ => ((hx i).tendsto.comp hl.neg).mul (hV i)
  have hQ := tendsto_finsetSum univ fun i _ => ((hx i).tendsto.comp hl.neg).mul (tendsto_finsetSum univ fun j _ => ((hy j).tendsto.comp hl).mul (hM i j))
  dsimp only
  exact tendsto_nhds_unique_of_eventuallyEq (stock_sway (hC.earns i j) hm hq _ hl he) (((hY.add hh).sub (tendsto_const_nhds.mul hQ)) |>.const_mul (1/2:ℂ)) (Eventually.of_forall fun i => H _ _ (k i) (hL i))
end budget
end YM.Stationary
end

/-!
# Both-leg soft Ward. Even on the fine field (no signed transform
required), Hess action kernel has no O(1), O(p) momentum jet after
passing to actual period-limit. Do not rely on inverting p. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ}

def Unsigned (s : Signed) := ∀ i,s.flip i=false

def platey (s : Equiv.Perm Axis) : Signed := ⟨s,fun _ => false⟩
lemma switched_unit (s : Signed) (i : Axis) : s.act (step i:Track)= if s.flip i then -(step (s.perm i)) else step (s.perm i) := by
  funext j; obtain ⟨j,rfl⟩ := s.perm.surjective j
  rw [s.act_at]; by_cases h : j=i <;> cases hi : s.flip i <;> simp [*]
lemma natural_step (s : Equiv.Perm Axis) (i : Axis) : (platey s).act (step i:Track)=step (s i) := by rw [switched_unit]; rfl

variable {adm : Signed → Prop} {f : Picture G 1} (H : TributeColor f σ A adm)
include H
namespace TributeColor
lemma crop_edict (ha : ∀ s, Unsigned s → adm s) : ∀ i a b, Rays 2 (pressLens f i a b) := by
  intro i a b
  let K x y := fderiv ℝ (pressLens f i x y) 0
  have he x y (p : Track) : speedy (pressLens f i x y) 1 p=K x y p := by simp [speedy,Tensor.diagonal,Tensor.coeff,iteratedFDeriv_one_apply,K]
  have hC j x y := trim_zero H.toFeatures j x y
  have hu (x) (p : Track) : ∑ j : Axis,(p j:ℂ)*K x j p=0 := by
    have ht := precipice H.toFeatures i (hC i) p x; simp_rw [he] at ht; exact ht
  have hv (x) (p : Track) : ∑ j : Axis,(p j:ℂ)*K j x p=0 := by
    have ht := H.paired_rule hC i p x; simp_rw [he] at ht; exact ht
  have hp j k : K k j (step j)=0 := by
    simpa [apply_ite ((↑):ℝ→ℂ),ite_mul] using hu k (step j)
  have hx j k : K j k (step j)=0 := by
    simpa [apply_ite ((↑):ℝ→ℂ),ite_mul] using hv k (step j)
  have hq (j k i) : K j k (step i)+ K j i (step k)=0 := by
    have ht := hu j (step k+step i)
    simpa [map_add,apply_ite ((↑):ℝ→ℂ),add_mul,ite_mul,hp, Finset.sum_add_distrib] using ht
  have hl (j : Axis) : K a b (step j)=0 := by
    by_cases h : b=j
    · rw [h,hp]
    by_cases hh : a=j
    · rw [hh,hx]
    by_cases hi : a=b
    · rw [← hi]; simpa [hx] using hq a a j
    let s := platey (Equiv.swap b j)
    have hu : Unsigned s := fun _ => rfl
    have ht := H.leading_shift (ha s hu) i (hC i) a b (step j)
    rw [he,he,show s.perm a=a from Equiv.swap_apply_of_ne_of_ne hi hh,show s.perm b=j from Equiv.swap_apply_left ..,show s.act (step j:Track)=_ from natural_step _ _, show Equiv.swap b j j=b from Equiv.swap_apply_right .., show signStar s a=1 from rfl,show signStar s b=1 from rfl,one_mul,one_mul] at ht
    have hv := hq a b j; rw [ht,← two_mul] at hv; exact (mul_eq_zero.mp hv).resolve_left (by norm_num)
  apply (rays_jet (priceL H.solid ..) 2).2
  intro j hj
  interval_cases j
  · exact (rays_jet (priceL H.solid ..) _).1 (hC i a b) _ Nat.zero_lt_one
  ext1 p; rw [iteratedFDeriv_one_apply]; change K a b _=0; rw [← show ∑ j,(p 0 j) • (step j : Track)= p 0 from ?_,map_sum]; simp [hl]
  funext j; simp [Finset.sum_apply, mul_ite]
end TributeColor

omit H
lemma roads_extent {t} {q : Space 1 → ℂ} (h : Rays t (fun p : Track => q (axes (roads p)))) : Rays t (q ∘ axes) := by
  intro p; obtain ⟨p,rfl⟩ := roads.surjective p; have he := h p; simp only [map_smul] at he; exact he
end YM.Stationary
end

/-! # Real and Ad-invariant color jets. Only symmetric color bilinear
forms here, in diagonal *axis* entries at even leading orders. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ}

-- use measure-free invariant subspace of colors
section generic
variable (s : Ink G 2 → ℝ)
def iris : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun x y => ∑ i, s i * (x (i 0) * y (i 1)))
    (by intros; simp [add_mul,mul_add,Finset.sum_add_distrib])
    (by intro a x y; simp [mul_assoc,mul_left_comm, Finset.mul_sum]
    )
    (by intros; simp [mul_add,Finset.sum_add_distrib])
    (by intro a x y; simp [mul_left_comm, Finset.mul_sum])
lemma iris_apply (x y : G.Color) : iris s x y=∑ i, s i * (x (i 0) * y (i 1)) := rfl
lemma iris_dual (hs : ∀ i j, s ![i,j]=s ![j,i]) (x y) : iris s x y = iris s y x := by
  let f : Equiv.Perm (Ink G 2) := Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl _)
  rw [iris_apply,iris_apply]; conv_rhs => rw [← Equiv.sum_comp f]
  apply Finset.sum_congr rfl; intro b _
  have hb (i j : G.ColorIndex) : f ![i,j]=![j,i] := funext fun k => by fin_cases k <;> rfl
  rw [show b=![b 0,b 1] from funext fun j => by fin_cases j <;> rfl,hb,hs]; simp [mul_comm]
lemma iris_tones (hs : s∈paints G 2) (v : G.El) (x y) : iris s (G.adjoint v x) (G.adjoint v y)=iris s x y := by
  have he := hs v ![x,y]; simp_rw [Fin.prod_univ_two] at he; exact he
lemma iris_resonant (hG : G.Simple) (hs : s∈paints G 2) (hp : ∀ i j, s ![i,j]=s ![j,i]) :
    ∃ k : ℝ, ∀ x y, iris s x y=k * inner ℝ x y := by
  apply Gauge.invariant_scalar hG _ (iris_dual s hp)
  intro u x y
  let F := (LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (G.Color →ₗ[ℝ] ℝ)≃ₗ[ℝ] (G.Color→L[ℝ] ℝ)).toLinearMap ∘ₗ iris s))
  let X (t : ℝ) := G.adjoint (G.lieExp (t • u)) x; let Y (t : ℝ) := G.adjoint (G.lieExp (t • u)) y
  have HX : HasDerivAt (F ∘ X) (F (G.ad u x)) 0 := F.hasFDerivAt.comp_hasDerivAt 0 (color_pitch u x); have HY : HasDerivAt Y (G.ad u y) 0 := color_pitch u y
  have he := HX.clm_apply HY
  have ht t : F (X t) (Y t)=F x y := iris_tones s hs ..
  simp_rw [Function.comp_apply, ht] at he
  have hi := he.unique (hasDerivAt_const _ _)
  have hy : X 0=x := by simp [X]
  rw [hy,show Y 0=y by simp [Y]] at hi
  exact eq_neg_of_add_eq_zero_left hi
lemma iris_detect (hG : G.Simple) (hs : s∈paints G 2) (hp : ∀ i j,s ![i,j]=s ![j,i]) (i : G.ColorIndex) (he : s ![i,i]=0) : s=0 := by
  obtain ⟨d,hd⟩ := iris_resonant s hG hs hp
  let F := EuclideanSpace.basisFun G.ColorIndex ℝ
  have hx (x y) : iris s (F x) (F y) = s ![x,y] := by
    rw [iris_apply,Finset.sum_eq_single ![x,y]]
    · simp [F]
    · intro b _ hh
      by_cases hi : b 0=x
      · have hk : b 1 ≠ y := fun h => hh (funext fun j => by fin_cases j <;> assumption)
        simp [F,hk]
      simp [F,hi]
    simp
  have he : d=0 := by
    have hb := hd (F i) (F i)
    rw [hx, F.inner_eq_one,mul_one] at hb; exact hb.symm.trans he
  funext b; rw [show b=![b 0,b 1] from funext fun j => by fin_cases j <;> rfl, ← hx,hd,he,zero_mul]; rfl
end generic

variable {f : Picture G 1} {admitS : Signed → Prop}

-- exactly degree-two value used for alpha normalization

def leapTip (f : Picture G 1) (u : Track) (v : Axis) (x : Ink G 2) := speedy (pressLens f x v v) 2 u
namespace TributeColor
variable (h : TributeColor f σ A admitS)
include h
lemma true_tip (hz : ∀ i j a, Rays 2 (pressLens f i j a)) (p : Track) (a : Axis) (i : Ink G 2) :
    ((leapTip f p a i).re : ℂ)=leapTip f p a i := by
  have hc (i k : ℕ) : ((-1:ℝ)^2)=1 := by norm_num
  have hp (x : Ink G 2) : leapTip f (-p) a x=leapTip f p a x := by
    unfold leapTip speedy; rw [show -p=(-1:ℝ) • p by rw [neg_one_smul], Tensor.homogeneous,hc 0 0,one_smul]
  have he := (pay_corner h.toFeatures i a a 2 (hz _ _ _) (-p)).star
  have hb v : star ((v^2:ℝ)⁻¹ • f i ![coord a,coord a] (axes (roads (v • -p))))= (v^2:ℝ)⁻¹ • f i ![coord a,coord a] (axes (roads (v • p))) := by
    rw [smul_neg,map_neg,axes_flip,star_smul, h.born _ _ _ (axes_real _)]; rfl
  simp_rw [hb] at he
  rw [show speedy _ _ (-p)=_ from hp i] at he
  have hx : star (leapTip f p a i)=leapTip f p a i := tendsto_nhds_unique he (pay_corner h.toFeatures i a a 2 (hz i a a) p)
  apply Complex.ext; rfl
  exact (Complex.conj_eq_iff_im.mp hx).symm
lemma true_tone (hG : G.Simple) (hz : ∀ i j a,Rays 2 (pressLens f i j a)) (p : Track) (a : Axis) (i : G.ColorIndex) (he : leapTip f p a ![i,i]=0) : ∀ j, leapTip f p a j=0 := by
  have hb : (fun i => (leapTip f p a i).re)∈paints G 2 := by
    let F t : Ink G 2→ ℝ := ((t^2:ℝ)⁻¹) • (fun i => (f i ![coord a,coord a] (axes (roads (t • p)))).re)
    have he t : F t∈paints G 2 := (paints G 2).smul_mem _ ((h.paint ..).1)
    refine (paints G 2).closed_of_finiteDimensional.mem_of_tendsto (show Tendsto F cutRay _ from tendsto_pi_nhds.mpr (fun i => ?_)) (Eventually.of_forall he)
    have he := Complex.continuous_re.continuousAt.tendsto.comp (pay_corner h.toFeatures i a a 2 (hz _ _ _) p)
    simpa only [F, leapTip, Pi.smul_apply,Function.comp_def,Complex.smul_re] using! he
  have hp (x y : G.ColorIndex) : leapTip f p a ![x,y] =leapTip f p a ![y,x] := by rw [leapTip,h.mirrors hz x y a a p,leapTip, speedy,show -p=(-1:ℝ) • p by rw [neg_one_smul], Tensor.homogeneous]; simp
  have hc := iris_detect (fun i => (leapTip f p a i).re) hG hb (fun x y => congr_arg Complex.re (hp x y)) i (by rw [he]; simp)
  intro j; rw [← h.true_tip hz p a j, show (leapTip f p a j).re=0 from congr_fun hc j,Complex.ofReal_zero]
end TributeColor
end YM.Stationary
end

/-!
# Test on ONE momentum axis. Gives precision coefficient alpha, not
fitted separately on the torus. Remaining jet killed by signed group
on THIS kernel, including reflected-edge phases in leading limit.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent Analysis
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ}
abbrev Universal (_ : Signed) := True

def tipCorner (f : Picture G 1) (i : Ink G 2) (a b : Axis) (p q : Track) := Tensor.coeff (pressLens f i a b) 2 0 ![p,q]

def soleSpin (i : Axis) : Signed := ⟨1,fun j => i=j⟩
def allWag : Signed := ⟨1,fun _ => true⟩
lemma radon (u : Axis) (p q : Track) : (soleSpin u).act (p+q)=(soleSpin u).act p+(soleSpin u).act q := Signed.act_add ..
lemma opposite_track (p : Track) : allWag.act p=-p := by ext i; simp [allWag,Signed.act]; rfl
lemma keep_axis (a b : Axis) (h : a≠b) : (soleSpin a).act (step b:Track)=(step b:Track) := by rw [switched_unit]; simp [soleSpin,h]
lemma swish_axis (a : Axis) : (soleSpin a).act (step a: Track)=-(step a:Track) := by rw [switched_unit]; simp [soleSpin]
lemma custodian {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {s : ℕ}
    (F : X → Y) (h : AnalyticAt ℝ F 0) (hr : Rays s F) (hp : ∀ p,speedy F s p=0) : Rays (s+1) F := by
  have he : Tensor.coeff F s 0=0 := Tensor.ext_diag _ _ (Tensor.coeff_symm h.contDiffAt) (fun _ _ => rfl) (funext hp)
  have ht : iteratedFDeriv ℝ s F 0=0 := by
    unfold Tensor.coeff at he; exact (smul_eq_zero.mp he).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _))
  apply (rays_jet h _).2; intro k hk; rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with hk|hk
  · exact hk.symm ▸ ht
  exact (rays_jet h _).1 hr k hk

namespace TributeColor
variable {f : Picture G 1} (h : TributeColor f σ A Universal)
include h
private lemma post (i : Ink G 2) (a b p q) : tipCorner f i a b p q= tipCorner f i a b q p := by
  unfold tipCorner
  nth_rewrite 1 [show ![p,q]=![q,p] ∘ (Equiv.swap (0:Fin 2) 1) by funext i; fin_cases i <;> rfl]
  exact Tensor.coeff_symm (j:=2) (priceL h.solid i a b |>.contDiffAt) ![q,p] (Equiv.swap 0 1)
omit h in
private lemma neg_tip (i : Ink G 2) (a b u v) : tipCorner f i a b (-u) v = -tipCorner f i a b u v := by
  simp [tipCorner,Tensor.coeff,iteratedFDeriv_two_apply]
omit h in
private lemma d_tip (i : Ink G 2) (a b u) : speedy (pressLens f i a b) 2 u=tipCorner f i a b u u := by
  unfold speedy tipCorner Tensor.diagonal; congr 1; ext1 j; fin_cases j <;> rfl
lemma multiform (i : Ink G 2) (x y u v) (s : Signed) : tipCorner f i (s.perm x) (s.perm y) (s.act u) (s.act v)= signStar s x * signStar s y * tipCorner f i x y u v := by
  have hl : ∀ i a b, Rays 2 (pressLens f i a b) := crop_edict h (fun _ _ => trivial)
  have hp (w) := h.leading_shift (s:=s) trivial i (hl i) x y w
  have hx := hp u; have hy := hp v; obtain he := hp (u+v)
  have hf (a b p q : _) : tipCorner f i a b (p+q) (p+q)=tipCorner f i a b p p+2*tipCorner f i a b p q + tipCorner f i a b q q := by
    have he (t u r : Track) : tipCorner f i a b (t+u) r=tipCorner f i a b t r + tipCorner f i a b u r := by
      simp [tipCorner,Tensor.coeff,iteratedFDeriv_two_apply,smul_add]
    rw [he,post h i a b p _,post h i a b q _,he,he,post h i a b q p]; ring
  simp_rw [d_tip] at hx hy he
  rw [s.act_add,hf,hf,hx,hy] at he
  linear_combination he/2
set_option maxHeartbeats 420000 in
lemma rite_axis (hG : G.Simple) (w : Axis) (p : Axis) (hwp : w≠p) (i : G.ColorIndex) (he : leapTip f (step p) w ![i,i]=0)
    (j : Ink G 2) (a b : Axis) : Rays 3 (pressLens f j a b) := by
  have hZ := h.crop_edict (fun _ _ => trivial)
  have hp := true_tone h hG hZ (step p) w i he j
  have ht : tipCorner f j w w (step p) (step p)=0 := by rw [← d_tip]; exact hp
  let Q := tipCorner f j
  have hb (x t : Axis) : Q x x (step t) (step t)=0 := by
    by_cases hx : x=t
    · rw [hx]; unfold Q; rw [← d_tip]
      simpa [apply_ite ((↑):ℝ→ℂ),ite_mul] using precipice h.toFeatures j (hZ j) (step t) t
    -- orientation that sends (w,p) to (x,t)
    let r : Equiv.Perm Axis := Equiv.swap w x
    let s := r.trans (Equiv.swap (r p) t)
    have hs : s w=x := by
      have h : x≠r p := fun he => hwp (r.injective ((Equiv.swap_apply_left w x).trans he))
      unfold s; rw [Equiv.trans_apply,show r w=x from Equiv.swap_apply_left ..]; exact Equiv.swap_apply_of_ne_of_ne h hx
    have hu : s p=t := by unfold s; rw [Equiv.trans_apply, Equiv.swap_apply_left]
    have hv := multiform h j w w (step p) (step p) (platey s)
    rw [show (platey s).perm w=x from hs,natural_step, hu,ht,mul_zero] at hv; exact hv
  -- parity from leading covariance signed. Cross entry with k != l nonzero only off-diagonal carrying k,l.
  have hy (x y k l r : Axis) : (if r=k then (-1:ℂ) else 1)*(if r=l then (-1:ℂ) else 1)*Q x y (step k) (step l)=
        (if r=x then -1 else 1)*(if r=y then -1 else 1)*Q x y (step k) (step l) := by
    let τ := soleSpin r
    have ht := h.multiform j x y (step k) (step l) τ
    have hf v : signStar τ v= (if r=v then -1 else 1) := by simp [signStar,τ,soleSpin]
    simp_rw [hf] at ht
    have hp (i) (u : Track) : tipCorner f j x y (τ.act (step i)) u = (if r=i then (-1:ℂ) else 1)*Q x y (step i) u := by
      by_cases h' : r=i
      · rw [← h',if_pos rfl,swish_axis,neg_tip,neg_one_mul]
      rw [if_neg h',keep_axis _ _ h',one_mul]
    have hc (u : Track) : tipCorner f j x y u (τ.act (step l))= (if r=l then (-1:ℂ) else 1) *Q x y u (step l) := by unfold Q; rw [post h,hp,post h]
    rw [show τ.perm x=x from rfl, show τ.perm y=y from rfl,hp, show Q x y (step k) _=_ from hc (step k)] at ht
    rwa [mul_assoc]
  have Hz (x k l) : Q x x (step k) (step l)=0 := by
    by_cases hh : k=l
    · rw [hh,hb]
    have ha := hy x x k l k; rw [if_pos rfl,if_neg hh] at ha
    split_ifs at ha
    all_goals apply mul_left_cancel₀ (show (2:ℂ)≠0 by norm_num); linear_combination -ha
  have hh (x y : Axis) (hxy : x≠y) (k) : Q x y (step k) (step k)=0 := by
    have ha := hy x y k k x; rw [if_pos rfl,if_neg hxy] at ha
    split_ifs at ha
    all_goals apply mul_left_cancel₀ (show (2:ℂ)≠0 by norm_num); first | linear_combination -ha | linear_combination ha
  have hU (x y u v : _) : speedy (pressLens f j x y) 2 (u+v) = Q x y u u+2*Q x y u v+Q x y v v := by
    rw [d_tip]
    have he (t u r : Track) : Q x y (t+u) r=Q x y t r + Q x y u r := by
      simp [Q,tipCorner,Tensor.coeff,iteratedFDeriv_two_apply,smul_add]
    change Q x y _ _= _; rw [he]; unfold Q; rw [post h j x y u,post h j x y v,show tipCorner _ _ _ _ _ u=_ from he u v u,show tipCorner _ _ _ _ _ v=_ from he u v v]
    unfold Q; rw [post h j x y v u]; ring
  have hu (x y : Axis) (e : x ≠ y) : Q x y (step x) (step y)=0 := by
    obtain he := precipice h.toFeatures j (hZ j) (step x+step y) x
    simp only [Pi.add_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib] at he
    simp only [step_apply (S:=ℝ),apply_ite ((↑):ℝ→ℂ),Complex.ofReal_one,Complex.ofReal_zero,ite_mul,one_mul,zero_mul, sum_ite_eq',mem_univ, ↓reduceIte] at he
    rw [hU,hU,hb,hb, Hz x, hh x y e,hh x y e] at he
    exact mul_left_cancel₀ (show (2:ℂ) ≠ 0 by norm_num) (by simpa using he)
  have hz (x y : Axis) : Q a b (step x) (step y)=0 := by
    by_cases ha : a=b
    · rw [ha]; exact Hz ..
    by_cases ht : x=y
    · rw [ht]; exact hh a b ha y
    by_cases hX : x=a ∨ x=b
    · by_cases hY : y=a ∨ y=b
      · rcases hX with rfl|rfl <;> rcases hY with hi|hi
        · exact False.elim (ht hi.symm)
        · rw [hi]; exact hu _ _ ha
        · unfold Q; rw [hi,post h]; exact hu _ _ ha
        exact False.elim (ht hi.symm)
      push Not at hY; obtain hh := hy a b x y y
      rw [if_pos rfl, if_neg (Ne.symm ht), if_neg hY.1, if_neg hY.2] at hh
      apply mul_left_cancel₀ (show (2:ℂ)≠0 by norm_num); linear_combination -hh
    push Not at hX; obtain hh := hy a b x y x
    rw [if_pos rfl,if_neg ht,if_neg hX.1,if_neg hX.2] at hh
    apply mul_left_cancel₀ (show (2:ℂ)≠0 by norm_num); linear_combination -hh
  apply custodian _ (priceL h.solid ..) (hZ j a b)
  intro v; rw [d_tip]
  change Q a b _ _=_
  have he x y := hz x y; simp_rw [Q,tipCorner,Tensor.coeff,_root_.smul_apply,iteratedFDeriv_two_apply] at he
  unfold Q tipCorner Tensor.coeff; simp_rw [_root_.smul_apply,iteratedFDeriv_two_apply]
  have heq : v=∑ j,v j • step j := by ext i; simp [Finset.sum_apply, mul_ite]
  rw [heq]; simp only [Matrix.cons_val_zero,Matrix.cons_val_one,map_sum,_root_.sum_apply,map_smul,_root_.smul_apply,Finset.smul_sum]
  simp_rw [Matrix.cons_val_zero,Matrix.cons_val_one] at he
  norm_num [smul_eq_zero] at he
  simp_rw [he]; simp
theorem vanish (hG : G.Simple) (w p : Axis) (hw : w≠p) (i : G.ColorIndex) (he : leapTip f (step p) w ![i,i]=0) (j b) :
    Rays 4 (f j b ∘ axes) := by
  have hp := rite_axis h hG w p hw i he j
  obtain ⟨a,ha⟩ := axisEquiv.surjective (b 0); obtain ⟨u,hu⟩ := axisEquiv.surjective (b 1)
  rw [show b=![coord a,coord u] from funext fun v => by fin_cases v; exact ha.symm; exact hu.symm]
  apply roads_extent
  apply custodian (pressLens f j a u) (priceL h.solid j a u) (hp _ _)
  intro v
  let Q := pressLens f j a u
  have he := h.leading_shift (r:=3) (s:=allWag) trivial j hp a u v
  change speedy Q 3 _ = (-1)*(-1)*speedy Q 3 v at he
  rw [opposite_track,speedy, show -v=(-1:ℝ) • v by rw [neg_one_smul], Tensor.homogeneous] at he
  norm_num at he
  change Tensor.diagonal (Tensor.coeff Q 3 0) v=0
  apply mul_left_cancel₀ (show (2:ℂ)≠0 by norm_num); linear_combination -he
end TributeColor
end YM.Stationary
end

/-!
# Kinetic unit: one transverse BASIS wave suﬃces. B metric `1` at
zero momentum. Needn't sign-normalize a curvature lift or take sup
of all plaquette directions. Two times coefficient for precision.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ} {w p : Axis}

section stroke
variable (w p) (h : w≠p)
include h

def stampFace : TypeFace 2 := ⟨{p,w},by simp [Ne.symm h]⟩
lemma stamped (a : TypeFace 2) (v : Momentum) (hf : ∀ i, i≠p → v i=0) : symbol 1 v a (coord w)=
    if a=stampFace w p h then q v p*parity a.val p ℂ else 0 := by
  simp_rw [symbol,wedge,Matrix.sum_apply]
  rw [Finset.sum_eq_single p]
  · unfold Exterior.left
    simp only [Matrix.smul_apply, Matrix.of_apply,smul_eq_mul]
    split_ifs with H Hy he he
    · rfl
    · exfalso; apply he; apply Subtype.ext
      change a.val=insert p {w}; rw [← show insert p (a.val.erase p)=a.val from Finset.insert_erase H]
      congr; exact congrArg Subtype.val Hy
    · subst a; exfalso; apply Hy; apply Subtype.ext; simp [coord,stampFace,remove,h.symm]
    · rw [mul_zero]
    · subst a; exfalso; apply H; exact Finset.mem_insert_self ..
    rw [mul_zero]
  · intro i _ hi; simp [Exterior.q, hf i hi]
  simp
omit h in
lemma parity_two (a : Finset Axis) : parity a p ℂ * parity a p ℂ=1 := by unfold parity; rw [← sq, ← pow_mul, Nat.mul_comm, pow_mul]; simp
lemma volume_unit (i : G.ColorIndex) : leapTip (slots leader G) (step p) w ![i,i]=(1/2:ℂ) := by
  let Q (t : ℝ) : Momentum := axes (t • (step p:Track))
  let F := slots leader G
  have he (t : ℝ) (j) (hp : j≠p) : Q t j=0 := by simp [Q,axes,hp]
  have ho (t j) (hp : j≠p) : -(Q t) j=0 := by rw [he _ _ hp,neg_zero]
  have hy (t : ℝ) : pressLens F ![i,i] w w (t • step p)=(1/2:ℂ)*(q (-Q t) p*q (Q t) p) := by
    unfold pressLens F slots; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ↓reduceIte]
    congr 1; rw [dcross,leader_const, Matrix.mul_one, Matrix.mul_apply]
    change ∑ a : TypeFace 2, (symbol 1 (-Q t) a (coord w))*(symbol 1 (Q t) a (coord w))=_
    rw [Finset.sum_eq_single (stampFace w p h)]
    · rw [stamped w p h _ (Q t) (he t), stamped w p h _ (-Q t) (ho t),if_pos rfl,if_pos rfl,mul_mul_mul_comm,parity_two p,mul_one]
    · intro a _ ha; rw [stamped w p h _ (Q t) (he t),if_neg ha,mul_zero]
    simp
  have hx : AnalyticAt ℝ (pressLens F ![i,i] w w) 0 := priceL (slots_cost zero_lt_one (leader_pay 1)) ..
  have hu : Rays 2 (pressLens F ![i,i] w w) := by
    intro v; unfold pressLens
    simp only [map_smul]; exact bed_rays zero_lt_one (leader_pay 1) ![i,i] _ (roads v)
  apply tendsto_nhds_unique (ray_limit hx hu (step p))
  have HV (z : Track) : Tendsto (fun t : ℝ => (t:ℂ)⁻¹*q (axes (t • z)) p) cutRay (𝓝 (Complex.I*(z p:ℂ))) := by
    have ht := lift_axis_ray (roads z) (0:Fin 1) p; simp_rw [sym_one] at ht; exact ht
  have HT := HV (-step p)
  simp only [smul_neg,axes_flip,Pi.neg_apply,step_apply,if_true,Complex.ofReal_neg,Complex.ofReal_one] at HT
  have hv := HV (step p)
  simp only [step_apply,if_true,Complex.ofReal_one,mul_one] at hv
  have hh := (HT.mul hv).const_mul (1/2:ℂ)
  simp only [mul_neg,mul_one,neg_mul,Complex.I_mul_I,neg_neg,mul_one] at hh
  refine hh.congr' (Eventually.of_forall fun t => ?_)
  simp only [hy]; simp only [Q,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]; ring
end stroke

variable (i : G.ColorIndex)
-- alpha normalization extraction

def alphaPay (f : Picture G 1) := 2*(leapTip f (step (0:Axis)) 1 ![i,i]).re
lemma tip_fuel {B : FaceRow} (ht : B.strip σ A) (hs : 0<σ) (he : B.read 0=1) : leapTip (slots B G) (step (0:Axis)) 1 ![i,i]=(1/2:ℂ) := by
  let L := pressLens (slots B G) ![i,i] 1 1; let Q := pressLens (slots leader G) ![i,i] 1 1
  have hp := priceL (slots_cost hs ht) ![i,i] 1 1
  have hv := priceL (slots_cost hs (leader_pay σ)) ![i,i] 1 1
  have hx : Rays 3 (L-Q) := by
    intro v; have h := slots_gain hs ht he ![i,i] ![coord 1,coord 1] (roads v); unfold L Q pressLens; simp_rw [Pi.sub_apply,map_smul]; exact h
  have hb := (rays_jet (f:=L-Q) (hp.sub hv) 3).1 hx 2 (by norm_num); rw [iteratedFDeriv_sub_apply (show ContDiffAt ℝ 2 L 0 from hp.contDiffAt) (show ContDiffAt ℝ 2 Q 0 from hv.contDiffAt)] at hb
  change speedy L 2 (step (0:Axis))=_
  unfold speedy Tensor.coeff; rw [sub_eq_zero.mp hb]; exact volume_unit 1 0 (by decide) i

lemma subtract_fee {f : Picture G 1} {v : ℝ} {B : FaceRow} {w A' : ℝ} (hp : TributeColor f σ A Universal)
    (hB : B.strip w A') (hh : 0<w) (he : B.read 0=1) (hv : v=alphaPay i f) : leapTip (f-(v:ℂ) • slots B G) (step (0:Axis)) 1 ![i,i]=0 := by
  let g := f-(v:ℂ) • slots B G
  let X := pressLens f ![i,i] 1 1
  let L := pressLens (slots B G) ![i,i] 1 1
  let q : Track := step (0:Axis)
  have hX : AnalyticAt ℝ X 0 := priceL hp.solid ..
  have hL : AnalyticAt ℝ L 0 := priceL (slots_cost hh hB) ..
  have hZ : pressLens g ![i,i] 1 1=X-v • L := by
    ext x; all_goals simp [g, pressLens,X,L,Complex.real_smul]
  change speedy (pressLens g ![i,i] 1 1) 2 q = 0
  have hz : speedy (X-v • L) 2 q=speedy X 2 q - v • speedy L 2 q := by
    unfold speedy Tensor.coeff Tensor.diagonal; rw [iteratedFDeriv_sub_apply hX.contDiffAt (show ContDiffAt ℝ 2 (v • L) 0 from (hL.contDiffAt).const_smul v), iteratedFDeriv_const_smul_apply hL.contDiffAt]
    simp [smul_sub]; ring
  rw [hZ, hz, show speedy L 2 q= _ from tip_fuel i hB hh he]; unfold alphaPay at hv
  let s := (leapTip f q 1 ![i,i]).re
  rw [Complex.real_smul,hv]; push_cast
  rw [← show (s:ℂ)=speedy X 2 q from hp.true_tip (hp.crop_edict (fun _ _ => trivial)) q 1 ![i,i]]; change (s:ℂ)-2*(s:ℂ)*(1/2)=0; ring
end YM.Stationary
end

/-!
# Second-jet drift removal. Fixed L qualitative extension; pre-L for the
rank-vs-core remainder.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree Asymptotics Metric
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {σ θ A C D γ η : ℝ} {m n : ℕ→Side}

lemma speedy_fits {M : Award G} (h : Screened M σ C) (hs : 0<σ) (i : G.ColorIndex) :
    AnalyticAt ℝ (pressLens (profitable M) ![i,i] 1 1) 0 := by
  have he := (h.earns (coord 1,i) (coord 1,i)).budget_nonneg
  exact priceL (profit M hs he h.earns).1 ..
lemma alpha_delta {F M : Award G} {A D : ℝ} (hs : 0<σ) (hf : Screened F σ A) (hp : Screened M σ D) (i : G.ColorIndex) : alphaPay i (profitable (F-M)) = alphaPay i (profitable F)-alphaPay i (profitable M) := by
  let X := pressLens (profitable (F-M)) ![i,i] 1 1
  let H := pressLens (profitable F) ![i,i] 1 1; let Q := pressLens (profitable M) ![i,i] 1 1
  let a := ((coord 1,i):Loc G 1)
  have he : X=H-Q := by
    funext x
    let p := axes x
    have hh := axes_real x
    change (2:ℂ)⁻¹ * stock (F a a p-M a a p) = (2:ℂ)⁻¹*stock (F a a p)-(2:ℂ)⁻¹*stock (M a a p)
    let f := F a a p; let g := M a a p
    have hw := Work.F07.realStrip _ hs hh
    have hv : Firm σ A f := stock_take (F a a) (hf.earns a a) hw
    have hx : Firm σ D g := stock_take (M a a) (hp.earns a a) hw
    have hu := Firm.retail walent walentes (hv.sub hx : Firm _ _ (f-g))
    rw [← mul_sub]; apply congr_arg ((2:ℂ)⁻¹ * ·)
    exact tendsto_nhds_unique_of_eventuallyEq hu ((Firm.retail walent walentes hv).sub (Firm.retail walent walentes hx)) (Eventually.of_forall fun i => shop_sub ..)
  let z : Track := step (0:Axis)
  have ht : AnalyticAt ℝ H 0 := speedy_fits hf hs i; have hx : AnalyticAt ℝ Q 0 := speedy_fits hp hs i
  have hp : speedy X 2 z=speedy H 2 z-speedy Q 2 z := by
    unfold speedy Tensor.diagonal Tensor.coeff; rw [he,iteratedFDeriv_sub_apply (ht.contDiffAt) hx.contDiffAt, smul_sub,_root_.sub_apply]
  unfold alphaPay; change 2*(speedy X 2 z).re=2*(speedy H 2 z).re-2*(speedy Q 2 z).re; rw [hp,Complex.sub_re,mul_sub]

section postings
variable {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {η τ δ E Ω Λ : ℝ} {T B : Bed}
-- coherent extensions actually of the promised mark, with same S(t) across.
variable {D : Eye (Loc G 1) (Acts G P)} {M : Spark (Loc G 1) G P}
structure TicketPost (Q : PostCard R p P K D M m n) (δ : ℝ) (B T : Bed) : Type where
    tree i : Forest ((Q.ship.boot i).ratio)
    graph i : Bid.Dir G (m i)→AxisChart G (tree i)
    mat i : Matrix (Body 1 (n i)) (Body 1 (m i)) ℝ
    spun i : Q.L i=cardHand (G:=G) (mat i)
    sworn i : Inputs (Q.ship.boot i) (mat i) (B.metric.acts (n i)) (T.metric.acts (m i))
    decor i : Critical (tree i) p R (graph i)
    health i : PriceGap (tree i) p R δ
    guards i : Guessed (tree i) (mat i) (graph i)
namespace TicketPost
variable {Q : PostCard R p P K D M m n} (X : TicketPost Q δ B T)
lemma event (i : ℕ) : Turns D (atlasQ (Q.ship.boot i) (X.mat i)) := by have he := Q.tilts i; rw [X.spun] at he; exact he
lemma shades (i : ℕ) : let S:=Q.ship.boot i;
                         Ticket M (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (flare p R (input G (n i) (uniformM (X.mat i) x)))) := by
  intro S; have he := Q.meets i; dsimp only at he; rw [X.spun] at he; exact he
end TicketPost
private lemma halo_neg {F : Track→ℂ} {l : ℕ} (h : Rays l F) : Rays l (fun p=> F (-p)) := by
  intro p; have ht := h (-p); simpa only [smul_neg] using ht
lemma drift_tip {Q : PostCard R p P K D M m n} (X : TicketPost Q δ B T) (hd : 0<δ) (hp : 0<σ) (hΩ : 0<θ) (h : P.Branches K G) (hS : G.Simple)
    (he : Play (carrierY D K.penalty M) σ) (hk : T.metric.strip θ A) (hm : Tendsto (fun i=> (m i).val) atTop atTop) (hu : R.Bounds p τ E Ω)
    (hC : Screened (changeCue D K.penalty M) σ C) (i : G.ColorIndex) :
    alphaPay i (profitable (changeCue D K.penalty M))=0 := by
  classical
  let Y := changeCue D K.penalty M; let a := ((coord 1,i):Loc G 1)
  let F := pressLens (profitable Y) ![i,i] 1 1
  let U := carrierY D K.penalty M
  have H (j) := alpha_night (F:=U) hp he hm j fun i p q hr b=> stamp_here (Q.tags i) (X.decor i) (X.mat i) hu h (X.health i) hd (X.guards i) hS (X.event i) (X.shades i) p q hr j b
  let x := fun (v : Track) (j) => taxTone G T (axes v) a j
  let M j (v : Track) := stock (hatchTrace U (.inl a) (.inr j) (axes v))
  let B i j (v : Track) := stock (hatchTrace (U.pay U) (.inr i) (.inr j) (axes v))
  let W := fun (v : Track) => ∑ j,x v j*M j v
  let V := fun v : Track => ∑ a,x (-v) a*∑ j,x v j*B a j v
  have heq (v : Track) : stock (Y a a (axes v))=(1/2:ℂ)*((W v + W (-v))-(1/2:ℂ)*V v) := by
    have hc := active (F:=U) hp he T hk hC hΩ hm a a (fun i u q hh=> signing_here (Q.tags i) (X.decor i) (X.mat i) hu h (X.health i) hd (X.guards i) hS (X.event i) (X.shades i) _ T (X.sworn i) (T.metric.rights _ _ hk hΩ.le) u q hh a a hC) (axes v) (axes_real v)
    unfold V W B x M; simp only [axes_flip]; exact hc
  have hx j : Rays 2 (fun k => x k j) := tax_ray _ hk hΩ a j
  have hW : Rays 3 W := rays_total (f:=fun i x' => x x' i*M i x') (fun i=> (hx i).mul (star_low hp he i (H i) a))
  have hV : Rays 4 V := by
    refine rays_total (f:=fun i v=> _) fun i => (halo_neg (hx i)).mul (t:=2) (g:=fun v => ∑ j,x v j*B i j v) ?_
    refine rays_total (s:=2) (f:=fun j v => x v j *B i j v) fun j=> (hx j).mul (g:=B i j) (rays_zero ?_)
    exact star_analytic hp (he.pay he) ..
  have hf : Rays 3 F := by
    intro v
    have H' := hW.add (halo_neg hW) v; have hm := (hV.weaker (by norm_num : 3≤4)) v
    change (fun t : ℝ => (2:ℂ)⁻¹ * stock (Y a a (axes (t • v)))) =O[cutRay] _
    simp_rw [heq]; exact (((H'.sub (hm.const_mul_left _)).const_mul_left _).const_mul_left _)
  have ht := (rays_jet (speedy_fits hC hp i) 3).1 hf 2 (by omega)
  unfold alphaPay leapTip speedy Tensor.diagonal Tensor.coeff; rw [ht]; simp
end postings
end YM.Stationary
end
