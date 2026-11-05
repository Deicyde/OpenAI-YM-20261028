import YM.Next.STATIONARY.Block.Packing
import YM.Next.STATIONARY.Joint.FourPoint

set_option autoImplicit false
/-!
# Critical Hessian in the colored bill basis. Root shear of flat centered
vectors exactly; strip provenance stays analytic on cover for reads. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Tree Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

section currency
variable (G S)

def fortune := -bondsM G S * butt G c f + patron G (d 0 c)*brim G c f
def posting (S : StepData c f) (B : Bed) := (butt G c f)ᵀ * patron G (Precision.K (B.metric.acts f))* butt G c f

def frontR (B : Bed) := posting G S B+ S.kernel.penalty • ((fortune G S)ᵀ * fortune G S)

lemma printer (x : Vault G c f) : expect S (0,x)=fortune G S *ᵥ cash (helmets G c f) x := by
  unfold fortune expect bondsM; rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [butt,brim,bill_at,cash_pocket, rear_cost, neg_mulVec, patron_fee,patron_fee]; rw [first_uniform]; change 0-_+_=_; rw [zero_sub]; rfl

lemma post_shares {p : Clip} {R : PathData G} (B : Bed) (t : S.Choices) (he : S.patch.Branches S.kernel G) {σ A Λ x y : ℝ} (hp : R.Bounds p σ A Λ) (hx : Floor B p f x y) (hh : Attached B R) (hu : Bid.Sworn B f G) :
    postmark S t p R=frontR G S B := by
  let Q := merit S t p R; let T := helmets G c f
  apply damage_eq T; intro a b
  let L := ContinuousLinearMap.inr ℝ (Link G c) (Vault G c f)
  have hA : AnalyticAt ℝ Q (L 0) := by rw [map_zero]; exact (merit_diff he t hp).analyticAt
  have hf : postmark S t p R=damage T (Q ∘ L) 0 := rfl
  rw [hf,detracts,wired L hA,map_zero, show L ∘ ![a,b]= ![L a,L b] by funext i; fin_cases i <;> rfl]; unfold Q; rw [(lit_scene he t hp hx hh hu).2.2, flash]
  rw [frontR,posting, add_mulVec,dotProduct_add,both_cost]
  unfold butt T L; rw [rear_cost,rear_cost,patron_fee,Matrix.smul_mulVec, dotProduct_smul,square_cost]
  simp only [ContinuousLinearMap.inr_apply]; rw [printer,printer]; rfl
end currency

section root
variable (t : S.Choices)
lemma tailor_arch (h : S.patch.Branches S.kernel G) (x : Vault G c f) :
    fderiv ℝ (tailor (fedora S t) (1:Joint G c f)) 0 x = (x.1,x.2+ uniformM (fixRoot S) x.1) := by
  let F := fedora (G:=G) S t
  let U := (1:Joint G c f)
  let Q := tailor F U
  let K := uniformM (G:=G) (fixRoot S)
  have hf := fedora_style h t
  have he : dress F U=1 := dressed_one hf
  have hx : Apparel F U := (atire_out (U:=fun _ : ℝ => U) hf (Thaw.fixed _ 0) rfl).self_of_nhds
  have hp : HasDerivAt (fun v : ℝ => Q (v • x)) (x.1,x.2+K x.1) 0 := by
    let g : ℝ → Joint G c f := fun v => atire F U (v • x)
    have hv : g 0=1 := by simp [g,he]
    have h1 : HasDerivAt (fun z => content (g z).1) x.1 0 := ray_content (u:=fun i => (g i).1) (by rw [hv]; rfl) (by
      intro i; change HasDerivAt (fun z : ℝ => _) _ _
      simp only [g,atire,U,mul_one]; exact ray_input x.1 i)
    have h2 : HasDerivAt (fun z => frameLog (g z).2) (x.2+K x.1) 0 := by
      refine ray_frame (u:=fun z => (g z).2) (by rw [hv]; rfl) ?_
      intro i; simp only [g,atire,U,mul_one,F,dress, Stationary.extend,Prod.smul_fst,Prod.smul_snd, Pi.mul_apply,fedora]
      convert! (ray_power x.2 i).mul (rooted_cap h t x.1 i).star using 1
      simp [bear_zero S t h,Gauge.colorMat_skew,K]
    unfold Q tailor; rw [he]; simp only [inv_one, mul_one]; exact h1.prodMk h2
  exact (Push.side _ ((tailor_diff F U hx).differentiableAt (by simp)) x).unique hp

lemma shear_pole (h : S.patch.Branches S.kernel G) : (shear (fedora S t) (1:Joint G c f))*spreadM S=stood S 1 := by
  apply testers; intro i x; rw [← mulVec_mulVec,parliament, shear, bill_at, tailor_arch t h, stands]
  apply congr_arg _; apply congr_arg (cash _)
  have hv := soldier_mounted S 1 x
  refine Prod.ext ?_ (gaugeColor.injective ?_)
  · rw [show (corps S 1 x).1=_ from hv.1]; exact (cant_one x).symm
  ext1 i; rw [hv.2,Prod.snd_one,Pi.one_apply, G.adjoint_one]; ext j
  let a := gradientA G f x
  change (-(curryG G S *ᵥ x)+ uniformM (fixRoot S) (-a)) (i,vac,j) = -x (S.ratio.embed i,vac,j)
  rw [map_neg,Pi.add_apply,Pi.neg_apply,curry_at,Pi.neg_apply]
  let V := parts G 0 (arm G f 0 x) j
  have hp : uniformM (fixRoot S) a (i,vac,j)=_ := calc
    _ = (fixRoot S *ᵥ (d 0 f*ᵥ V)) (i,vac) := by unfold a; rw [first_uniform]; rfl
    _ = x (S.ratio.embed i,vac,j)-∑ u:S.patch.Points, S.patch.weight u * x (Precision.atPoint S i u,vac,j) := psi_proj S V (i,vac)
  rw [hp]; dsimp; abel
end root
end YM.Stationary
end

/-!
# Zero-arc transforms. Real-momentum testing lossless at the endpoints
and cutoffs; yields comparisons on real slice of Momentum. Applies without
any density assumption on ratio families except grow-to-infinity. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {n m : Side} {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {σ A ε δ : ℝ} {U : CircM n α β} {f g : Momentum→ CompM α β}
    {p q : Momentum}

namespace Jaunt
lemma hoist (h : Jaunt U f 0) {V : CircM n β γ} {W : Momentum→CompM β γ} (he : Jaunt V W 0) : Jaunt (U*V) (fun i => f i*W i) 0 := Ticket.Jaunt0 h he
lemma takes (h : Jaunt U f 0) : Jaunt Uᵀ (fun p => (f (-p))ᵀ) 0 := by
  simpa using h.adjoin (show rolls (mon (0:Site n)) 0 by rw [mon_zero]; exact rolls.refl _)
lemma offset {i : Site n} (h : Jaunt U f i) (hv : Jaunt U g i) {p : Site n} (q) (he : rolls (mon p) q) : f q=g q := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro v; exact ray_pick (p+i) ((h p q he _).symm.trans (hv p q he v))
end Jaunt
namespace Poster
lemma hol {p : Momentum} (h : Poster σ f) (he : p∈strip σ) : ContinuousAt f p := by
  apply continuousAt_pi.mpr; intro i; exact continuousAt_pi.mpr (fun j => (h.shape he i j).continuousAt)
lemma web (A : CompM α β) : Poster σ fun _ => A := ⟨fun _ _ _ => differentiableAt_const _, fun _ _ => rfl⟩
lemma amounts (h : Poster σ f) (hp : Poster σ g) : Poster σ (f+g) := ⟨fun w => BillD.plus (h.shape w) (hp.shape w), fun he hb => congr_arg₂ (·+·) (h.shifts he hb) (hp.shifts he hb)⟩
lemma shares (h : Poster σ f) (hp : Poster σ g) : Poster σ (f-g) := ⟨fun w => BillD.less (h.shape w) (hp.shape w), fun he hb => congr_arg₂ (·-·) (h.shifts he hb) (hp.shifts he hb)⟩
lemma plus_nec (h : Poster σ f) (C : ℂ) : Poster σ (C • f) := ⟨fun w => BillD.debit C (h.shape w), fun he hb => congr_arg (C • ·) (h.shifts he hb)⟩
lemma forge {g : Momentum→CompM β γ} (h : Poster σ f) (hv : Poster σ g) : Poster σ fun p => f p*g p := ⟨fun p => BillD.bond (h.shape p) (hv.shape p), fun he w => congr_arg₂ (·*·) (h.shifts he w) (hv.shifts he w)⟩
lemma reverse (h : Poster σ f) : Poster σ fun p => (f (-p))ᵀ := by
  have H := Play.rear (Play.current (ι:=Axis) h)
  exact H.tab
lemma fuses (m : ℕ → Side) (hm : Tendsto (fun i => (m i).val) atTop atTop) (h : Poster σ f) (hp : Poster δ g) (hs : 0<σ) (he : 0<δ) (hh : ∀ i (p : Site (m i)), f (mon p)=g (mon p))
    {p : Momentum} (hx : star p=p) : f p=g p := by
  obtain ⟨k,u,hu,hK⟩ := mesh_stride m hm p hx
  refine tendsto_nhds_unique_of_eventuallyEq ((h.hol (Work.F07.realStrip _ hs hx)).tendsto.comp hu)
    ((hp.hol (Work.F07.realStrip _ he hx)).tendsto.comp hu) <| Eventually.of_forall fun i => ?_
  rw [Function.comp_apply, Function.comp_apply, ← h.shifts (hK i) (Work.F07.realStrip _ hs (real_frequency _)), ← hp.shifts (hK i) (Work.F07.realStrip _ he (real_frequency _)), hh]
end Poster

-- metric test import. Real counting lower
lemma numeric_credit (V : Row α α) (he : (V.acts m)ᵀ=V.acts m) (hp : Numeric (V.acts m) ε A) (v : Phase (Co m α)) :
    ε*(slug v)^2 ≤ (dotProduct (star v) (approached (V.acts m)*ᵥ v)).re := by
  let x := fun i => (v i).re
  let y := fun i => (v i).im
  let F := approached (V.acts m)
  have h : v=axes x + I • axes y := by funext i; simp [axes,x,y]; rw [mul_comm I,Complex.re_add_im]
  have ht (X : Matrix (Co m α) (Co m α) ℝ) : (dotProduct (star v) (approached X *ᵥ v)).re=dotProduct x (X *ᵥ x)+dotProduct y (X*ᵥ y) := by
    rw [h,star_add]
    simp only [star_smul, axes_real,Matrix.mulVec_add,prom_vec,Matrix.mulVec_smul]
    have hx (x y : Corn (Co m α)) : dotProduct (axes x) (axes y)=(↑(dotProduct x y):ℂ) := by unfold dotProduct; push_cast; rfl
    simp only [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, hx, smul_eq_mul]; simp
  rw [ht, show slug v^2= dotProduct x x+dotProduct y y from ?_]; have heX := (hp x).1; have heY := (hp y).1; linarith
  have hu := ht 1; rw [show approached (1:Matrix (Co m α) (Co m α) ℝ)=1 by ext i j; by_cases he : i=j <;> simp [approached,Matrix.one_apply, *],one_mulVec,one_mulVec,one_mulVec,slug_self] at hu; exact hu
lemma starlight (p : Site m) (v : Phase α) : star (tune p v)=tune (-p) (star v) := by
  funext x; unfold tune
  simp only [Pi.star_apply,star_mul, star_def,cell_bar]; rw [cell_duality (-p),cell_inverse,cell_duality,mul_comm]
lemma credit_plane (V : Row α α) (hv : V.safe) (he : (V.acts m)ᵀ=V.acts m) (hp : Numeric (V.acts m) ε A) (v : Phase α) (p : Site m) (q : Momentum) (hh : rolls (mon p) q) : ε*slug v^2 ≤ (dotProduct (star v) (V.read q*ᵥ v)).re := by
  have hy := numeric_credit V he hp (tune p v)
  have hF : Fintype.card (Site m)>0 := Fintype.card_pos
  rw [Jaunt.row V hv _ _ hh,add_zero,starlight p v,ray_dots,if_pos (neg_add_cancel _)] at hy
  have hk := (slug_self (tune p v)).symm
  rw [starlight,ray_dots,if_pos (neg_add_cancel _),slug_self] at hk
  have hK := congr_arg Complex.re hk
  simp only [Complex.mul_re,natCast_re,natCast_im, ofReal_re,ofReal_im,zero_mul,sub_zero,natCast_re] at hy hK
  rw [hK] at hy; exact le_of_mul_le_mul_left (by linarith only [hy]) (show (0:ℝ)<↑(Fintype.card (Site m)) by positivity)
end YM.Stationary
end

/-!
# Hodge identity and gauge channel static phase. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {L : Side} {p q : Momentum} {σ A : ℝ}

def pageD (G : Gauge) (j : ℕ) (p : Momentum) := tintedLocal G (symbol j p)
lemma page_read (S : Side) (i) : Jaunt (approached (patron G (d i S))) (pageD G i) 0 := by
  rw [show pageD G i=(fun p => tintedLocal G ((cobound i).read p)) from funext fun p => congr_arg (tintedLocal G) (Exterior.reading p i).symm]; exact palette_ship _ (cobound_safe _)
lemma page_linen (i : ℕ) : Poster σ (pageD G i) := by
  refine ⟨fun w a b => ?_,fun he w => congr_arg (tintedLocal G) (rolls_symbol he i)⟩
  unfold pageD tintedLocal; simp only [Matrix.of_apply]; split
  · unfold symbol wedge Exterior.q; simp only [Matrix.sum_apply, Matrix.smul_apply]; fun_prop
  exact differentiableAt_const _
lemma page_rear (i) (h : star p=p) : (pageD G i (-p))ᵀ = (pageD G i p)ᴴ := by
  unfold pageD tintedLocal; ext a b; simp only [Matrix.transpose_apply,Matrix.conjTranspose_apply, Matrix.of_apply]; split; swap; simp
  simp only [symbol,wedge,quanta h,Matrix.sum_apply,Matrix.smul_apply,star_sum,smul_eq_mul,star_mul,Pi.star_apply]
  apply sum_congr rfl; intro i _; rw [mul_comm]
  congr 1; unfold Exterior.left; simp only [Matrix.of_apply]; split
  next h => split <;> simp [parity]
  simp
lemma page_zero (i p) : pageD G (i+1) p*pageD G i p=0 := by rw [pageD,pageD,← tinted_pay]; rw [symbol,symbol,d_d]; ext; simp [tintedLocal]


lemma inkCartan (p : Momentum) (i : ℕ) :
    symbol i p*(symbol i (-p))ᵀ+ (symbol (i+1) (-p))ᵀ*symbol (i+1) p=stone p • 1 := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; rw [Matrix.toLin'_apply,Matrix.toLin'_apply,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.add_mulVec,← Matrix.mulVec_mulVec x, ← Matrix.mulVec_mulVec x]
  unfold symbol
  let m := Exterior.q p; let n := Exterior.q (-p)
  have he : wedge i m *ᵥ ((wedge i n)ᵀ *ᵥ x) + (wedge (i+1) n)ᵀ *ᵥ (wedge (i+1) m *ᵥ x) = ∑ j : Axis,(n j*m j) • x := by
    have hh (k : ℕ) : (wedge k n)ᵀ=∑ j,n j • (Exterior.left ℂ k j)ᵀ := by simp only [wedge,Matrix.transpose_sum,Matrix.transpose_smul]
    rw [hh i,hh (i+1)]
    simp_rw [Matrix.sum_mulVec, Matrix.mulVec_sum, Matrix.smul_mulVec, Matrix.mulVec_smul, ← sum_add_distrib, ← smul_add, Work.F06.cartan,smul_smul]
  rw [stone,dotProduct, Finset.sum_smul]; exact he
-- vacuum i=0 needs site only; no boundary d_-1
lemma vacuum_page (p : Momentum) : (symbol 0 (-p))ᵀ*symbol 0 p=stone p • 1 := by
  ext i j; rw [vac_only i, vac_only j,mul_apply, ← Equiv.sum_comp axisEquiv]; simp only [coord_map,Matrix.transpose_apply,sym_one]; simp [stone,dotProduct]
lemma page_scalar (x : ℂ) (i) : tintedLocal G (x • (1 : Matrix (TypeFace i) (TypeFace i) ℂ))=x • 1 := by
  ext ⟨i,t⟩ ⟨j,u⟩; simp only [Matrix.smul_apply,Matrix.one_apply, tintedLocal, Matrix.of_apply]; by_cases h : t=u <;> simp [h]
lemma codex_value (p : Momentum) : (pageD G 0 (-p))ᵀ* pageD G 0 p=stone p • 1 := by
  unfold pageD; rw [← tinted_flip,← tinted_pay,vacuum_page,page_scalar]
lemma kartel (p : Momentum) (i) : pageD G i p*(pageD G i (-p))ᵀ+ (pageD G (i+1) (-p))ᵀ*pageD G (i+1) p=stone p • 1 := by
  unfold pageD; rw [← tinted_flip,← tinted_pay, ← tinted_flip,← tinted_pay, ← tinted_plus,inkCartan,page_scalar]
end YM.Stationary
end

/-!
# Principal tariffs per fiber. Stationary gap inputs only on raw oriented
axes and colors. Includes high unpin lemma. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {c f n m : Side} {p q : Momentum}
    {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {σ A C ε : ℝ}

lemma range_field (V : Row α α) (hs : 0<σ) (h : V.strip σ A) (hp : star p=p) (x : Phase α)
    (hv : ∀ n : Side, (V.acts n)ᵀ=V.acts n ∧ Numeric (V.acts n) ε C) : ε*slug x^2 ≤ (dotProduct (star x) (V.read p *ᵥ x)).re := by
  obtain ⟨k,u,hu,hk⟩ := mesh_stride walent walentes p hp
  let g p := (dotProduct (star x) (V.read p *ᵥ x)).re
  refine ge_of_tendsto ((show ContinuousAt g p from ?_).tendsto.comp hu) (Eventually.of_forall fun i => credit_plane V (V.rights _ _ h hs.le)
    (hv (walent i)).1 (hv _).2 x _ (u i) (hk i))
  have hf i j : ContinuousAt (fun z => V.read z i j) p := ((Firm.of_series (V.constant_strip h i j) hs).1.hol p (Work.F07.realStrip _ hs hp)).continuousAt
  refine continuous_re.continuousAt.comp (?_ : ContinuousAt (fun p => dotProduct (star x) (V.read p *ᵥ x)) p)
  unfold Matrix.mulVec dotProduct; exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul (tendsto_finsetSum _ (fun j _ => (hf i j).tendsto.mul tendsto_const_nhds)))

-- for each Body

def tessH (G : Gauge) (B : Bed) (p : Momentum) := tintedLocal G (B.metric.read p)
def rug (G : Gauge) (B : Bed) (p : Momentum) := (pageD G 1 (-p))ᵀ * tessH G B p * pageD G 1 p

lemma rug_plane (S : Side) (V : Bed) (h : V.metric.safe) : Jaunt (approached (patron G (Precision.K (V.metric.acts S)))) (rug G V) 0 := by
  have he := palette_ship (G:=G) (c:=S) V.metric h
  rw [Precision.K,patron_mul,patron_mul,patron_star,prom_mul,prom_mul]; exact (((page_read S 1).takes.hoist he).hoist (page_read S 1))
lemma rug_played (B : Bed) (h : B.metric.strip σ A) (hp : 0<σ) : Poster σ (rug G B) :=
    ((page_linen 1 (G:=G)).reverse.forge (exterior_calm _ h hp)).forge (page_linen 1)

lemma pick_norm {i : ℕ} (x : Phase (Loc G i)) : slug x^2=∑ j : G.ColorIndex,slug (pick x j)^2 := by
  simp_rw [slug_sq]; rw [Fintype.sum_prod_type,sum_comm]; rfl
lemma pick_dots {i : ℕ} (x y : Phase (Loc G i)) : dotProduct x y=∑ j : G.ColorIndex,dotProduct (pick x j) (pick y j) := by
  unfold dotProduct; rw [Fintype.sum_prod_type,sum_comm]; rfl
lemma Bed.holo {B : Bed} {w : Clip} (h : B.metric.strip σ A) (hp : 0<σ) (he : ∀ n, Floor B w n ε C) (hv : star p=p) (x : Phase (Loc G 2)) : ε*slug x^2 ≤ (dotProduct (star x) (tessH G B p*ᵥ x)).re := by
  rw [pick_dots,pick_norm, re_sum, mul_sum]; refine sum_le_sum fun i _ => ?_
  have hh : pick (tessH G B p*ᵥ x) i=B.metric.read p*ᵥpick x i := funext fun a => tinted_at _ x (a,i)
  rw [hh]; exact range_field B.metric hp h hv (pick x i) (fun n => ⟨(he n).symmetric.1,(he n).uniform.1⟩)

-- dot precision bottom and pure high complement
lemma vested (X : CompM α β) (x : Phase β) (y : Phase α) : dotProduct (star x) (Xᴴ *ᵥ y)=dotProduct (star (X *ᵥ x)) y := by rw [star_mulVec,dotProduct_mulVec]
lemma pure_grade (hp : star p=p) (G : Gauge) (a : Phase (Loc G 1)) : slug ((pageD G 0 p)ᴴ *ᵥ a)^2 + slug (pageD G 1 p *ᵥ a)^2 = (shadeK p*slug a)^2 := by
  let Gm := pageD G 0 p; let D := pageD G 1 p
  have hv : Gm*Gmᴴ+Dᴴ*D=stone p • 1 := by rw [← page_rear 0 hp, ← page_rear 1 hp]; exact kartel p 0
  have H : ((slug (Gmᴴ *ᵥ a)^2:ℝ):ℂ) + ((slug (D *ᵥ a)^2:ℝ):ℂ) = (((shadeK p *slug a)^2:ℝ):ℂ) := by
    rw [← slug_self, ← slug_self, ← vested,← vested, conjTranspose_conjTranspose,mulVec_mulVec,mulVec_mulVec, ← dotProduct_add, ← add_mulVec,hv,Matrix.smul_mulVec,Matrix.one_mulVec, dotProduct_smul,slug_self,stone_real hp]; push_cast; ring
  exact_mod_cast H
lemma pure_density (hp : star p=p) (a : Phase (Loc G 0)) : slug (pageD G 0 p*ᵥ a)^2=(shadeK p*slug a)^2 := by
  apply Complex.ofReal_injective
  rw [← slug_self,← vested, Matrix.mulVec_mulVec, ← page_rear _ hp, codex_value,Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, slug_self,stone_real hp]
  push_cast; ring
lemma rug_test {B : Bed} {w : Clip} (h : B.metric.strip σ A) (hp : 0<σ) (he : ∀ n, Floor B w n ε C) (hv : star p=p) (x : Phase (Loc G 1)) : ε* slug (pageD G 1 p *ᵥ x)^2 ≤ (dotProduct (star x) (rug G B p *ᵥ x)).re := by
  rw [rug, ← mulVec_mulVec, ← mulVec_mulVec, page_rear 1 hv, vested]; exact Bed.holo h hp he hv _
lemma padlock {p : Momentum} (hp : star p=p) (he : shadeK p≠0) (a : Phase (Loc G 1)) : ∃ k : Phase (Loc G 0), (pageD G 0 p)ᴴ *ᵥ (a+pageD G 0 p *ᵥ k)=0 := by
  let D := pageD G 0 p
  refine ⟨-(stone p)⁻¹ • (Dᴴ*ᵥ a),?_⟩
  have ht : stone p≠0 := by rw [stone_real hp]; exact_mod_cast pow_ne_zero 2 he
  change Dᴴ *ᵥ (a+D *ᵥ _)=0
  rw [mulVec_add,mulVec_smul,mulVec_smul, Matrix.mulVec_mulVec _ _ D]
  rw [show Dᴴ*D=stone p • 1 from (by unfold D; rw [← page_rear 0 hp,codex_value]),Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul,neg_mul,inv_mul_cancel₀ ht,neg_one_smul,add_neg_cancel]
end YM.Stationary
end

/-! # Real aliases: present via plankTile (alias coordinates not slab).
Ready for lower estimate on centered full matrix. Raw torus fields tested
in actual counting. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {c f L : Side} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {σ C : ℝ} {p q : Momentum}
lemma crew_tile (v : Phase (Co L α)) : crewAlias p (plankTile L α p *ᵥ v)=v := by unfold crewAlias; rw [mulVec_mulVec,nonsing_inv_mul _ (tile_solid _),one_mulVec]
lemma tile_crew (v : Phase (Co L α)) : plankTile L α p *ᵥ crewAlias p v=v := by unfold crewAlias; rw [mulVec_mulVec,mul_nonsing_inv _ (tile_solid _),one_mulVec]
lemma crew_funds (v : Phase (Co L α)) (F : Momentum→CompM β α) : crewAlias p (furnish L F p *ᵥ v)=posterBlock L F p*ᵥ crewAlias p v := by
  apply smul_right_injective (Co L β → ℂ) (r:=(inch L:ℂ)^2) (pow_ne_zero _ (by exact_mod_cast (inch_pos L).ne')); dsimp only; rw [← mulVec_smul]; exact draping F _
lemma funds_tile (v : Phase (Co L α)) (F : Momentum→CompM β α) : furnish L F p *ᵥ (plankTile L α p *ᵥ v) = plankTile L β p *ᵥ (posterBlock L F p *ᵥ v) := by
    conv_lhs => rw [← tile_crew (p:=p) (furnish _ _ _*ᵥ _)]
    rw [crew_funds,crew_tile]
lemma slug_slots (v : Phase (Co L α)) : slug v^2=∑ i, slug (stackSlice i v)^2 := by simp_rw [slug_sq]; rw [Fintype.sum_prod_type]; rfl
lemma define_slot (v x : Phase (Co L α)) : dotProduct (star v) x=∑ i, dotProduct (star (stackSlice i v)) (stackSlice i x) := by unfold dotProduct; rw [Fintype.sum_prod_type]; rfl

lemma rate_sq_tile (p : Momentum) (l : Phase (Co L α)) : ((altarTile L α).rate p (plankTile L α p *ᵥ l))^2 = ∑ i, hill p i ^2* slug (stackSlice i l)^2 := by
  rw [rate_alias]; simp_rw [crew_tile]; rw [slug_slots]; apply sum_congr rfl; intro i _
  rw [show stackSlice i (fun j : Co L α => (hill p j.1:ℂ)*l j)=(hill p i:ℂ) • stackSlice i l from rfl, slug_scale]; simp only [norm_real, Real.norm_eq_abs,abs_of_pos (hill_pos _ _), mul_pow]
lemma sleeve (p : Momentum) (h : star p=p) (x : Phase (Co L α)) (y : Phase (Co L β)) (F : Momentum→CompM α β) :
    dotProduct (star x) (furnish L F p *ᵥ y)= ∑ i, dotProduct (star (stackSlice i (crewAlias p x))) (F (aliasAt p i)*ᵥ stackSlice i (crewAlias p y)) := by
  let X := plankTile L α p
  have hx : Skates X := tile_ice h
  let V := furnish L F p *ᵥ y
  rw [show dotProduct (star x) V=_ from (show dotProduct (star x) V=dotProduct (star (crewAlias p x)) (crewAlias p V) by
    unfold crewAlias; rw [show plankTile L α p=X from rfl, ← vested,mulVec_mulVec,hx.back.slides,one_mulVec])]
  unfold V; rw [crew_funds,define_slot]; simp_rw [posterBlock_at]
lemma tile_part (l : Site L) (v : Phase α) : plankTile L α p *ᵥ partitionA l v=(inch L:ℂ)^2 • tiled p l v := by rw [plankTile,smul_mulVec,tiled_gear]



end YM.Stationary
end

/-!
# Ward columns for `commonM`. Uncompleted matrices independent of
X-regularizer. Rend from actual mesh via density; note Jacobian tags not
required for the prediction matrix in this leg. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Tree
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L c f n : Side} {S : StepData c f} {p q : Momentum} {σ A H : ℝ}

-- joint W Fourier chart, no forest

def downX (G : Gauge) (L : Side) : CompM (Co L (Loc G 1)) (ParcelG G L) := shardX _ _ ℂ
def downY (G : Gauge) (L : Side) : CompM (Loc G 0) (ParcelG G L) := shardY _ _ ℂ
lemma downXY (v : Phase (ParcelG G L)) : Sum.elim ((downX G L)*ᵥ v) ((downY G L)*ᵥ v)=v := by unfold downX downY; rw [sliceX,sliceY]; exact (spade_assemble _).symm
lemma left_spill (x : Phase (Co L (Loc G 1))) : (downX G L)ᵀ *ᵥ x=Sum.elim x 0 := by
  funext i; rcases i with i|i <;> simp [downX,shardX,Matrix.mulVec,dotProduct,Pi.single_apply,ite_mul]
lemma right_spill (x : Phase (Loc G 0)) : (downY G L)ᵀ *ᵥ x=Sum.elim (0:Phase (Co L (Loc G 1))) x := by
  funext i; rcases i with i|i <;> simp [downY,shardY,Matrix.mulVec,dotProduct,Pi.single_apply,ite_mul]
lemma downX_star : (downX G L)ᵀ=(downX G L)ᴴ := by unfold downX; rw [← shardPromX]; ext; simp [approached]
lemma downY_star : (downY G L)ᵀ=(downY G L)ᴴ := by unfold downY; rw [← shardPromY]; ext; simp [approached]

def netY (G : Gauge) (P : Patch) (p : Momentum) := -(meanRay G P p)*downX G P.L + pageD G 0 p * downY G P.L
def shadeR (G : Gauge) (P : Patch) (p : Momentum) := -(downX G P.L)ᵀ * furnish P.L (pageD G 0) p - (downY G P.L)ᵀ*jar G P p
def giftQ (G : Gauge) (P : Patch) (B : Bed) (κ : ℂ) (p : Momentum) :=
    (downX G P.L)ᵀ*furnish P.L (rug G B) p * downX G P.L + κ • ((netY G P (-p))ᵀ*netY G P p)
def slabW (G : Gauge) (L : Side) := (altarTile L (Loc G 1)).spade (Slab.basic (Loc G 0))
lemma slab_real (hp : star p=p) : ((slabW G L).tile (-p))ᵀ=((slabW G L).tile p)ᴴ := by
  simp only [slabW,Slab.spade,Slab.basic,spade_slim,spade_heft, Matrix.conjTranspose_one,transpose_one, tiles_pair hp]

lemma shade_split (p : Momentum) (v : Phase (Co P.L (Loc G 0))) : shadeR G P p *ᵥ v = Sum.elim (-(furnish P.L (pageD G 0) p *ᵥ v)) (-(jar G P p *ᵥ v)) := by
  unfold shadeR; rw [Matrix.sub_mulVec,← mulVec_mulVec,← mulVec_mulVec, neg_mulVec,left_spill,right_spill]; ext1 i; cases i <;> simp
lemma net_split (p : Momentum) (x y) : netY G P p *ᵥ Sum.elim x y=pageD G 0 p *ᵥ y-meanRay G P p *ᵥ x := by
  unfold netY downX downY; rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, sliceX,sliceY,neg_mulVec,add_comm]; rfl

section credit
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
lemma prom_negation (U : Matrix α β ℝ) : approached (-U)=-approached U := by ext; simp [approached]
lemma repack_neg (e : α≃β) (g : γ≃δ) (U : Matrix α γ ℂ) : repackM e g (-U)= -repackM e g U := rfl
lemma repack_add (e : α≃β) (g : γ≃δ) (U V : Matrix α γ ℂ) : repackM e g (U+V)=repackM e g U+repackM e g V := rfl
lemma repack_term (e : α≃β) (g : γ≃δ) (U : Matrix α γ ℂ) (a : ℂ) : repackM e g (a • U)=a • repackM e g U := rfl
end credit

lemma staff (n : ℕ) : Jaunt (repackM (unitSplit G S (n+1)) (unitSplit G S n) (approached (patron G (d n f)))) (furnish S.patch.L (pageD G n)) 0 := Jaunt.press S.ratio (page_read f n) (page_linen _) zero_lt_one
lemma net_turn : Jaunt (repackM (Equiv.refl _) (clothe G S) (approached (fortune G S))) (netY G S.patch) 0 := by
  have ht := butt_travel (G:=G) (S:=S)
  have hv := brim_travel (G:=G) (S:=S)
  classical
  have he := bond_travel (G:=G) S
  unfold fortune; rw [prom_addition,repack_add, prom_mul,prom_mul,prom_negation,
    repack_multiply _ (unitSplit G S 1),repack_multiply _ (Equiv.refl _),repack_neg]
  exact (he.backside.hoist ht).plus ((page_read c 0).hoist hv)
lemma shade_turn : Jaunt (repackM (clothe G S) (unitSplit G S 0) (approached (spreadM S (G:=G)))) (shadeR G S.patch) 0 := by
  unfold spreadM
  have hx : Jaunt ((repackM (unitSplit G S 1) (clothe G S) (approached (butt G c f)))ᵀ) (fun p => (downX G S.patch.L)ᵀ) 0 := (butt_travel (G:=G) (S:=S)).takes
  have hy : Jaunt ((repackM (Equiv.refl _) (clothe G S) (approached (brim G c f)))ᵀ) (fun p => (downY G S.patch.L)ᵀ) 0 := (brim_travel (G:=G) (S:=S)).takes
  have hw := ((hx.backside).hoist (staff (G:=G) (S:=S) 0)).plus ((hy.hoist (jar_travel (G:=G) S)).backside)
  classical
  rw [show mail (1:Config G f) = -patron _ (d 0 f) from mailed_zero, Matrix.mul_neg, ← Matrix.neg_mul]
  rw [sub_eq_add_neg,prom_addition,prom_negation _,prom_mul,prom_mul,prom_negation,repack_add,repack_neg]
  have hp (A : Matrix (Lines G f 1) (Bodies G c f) ℝ) : approached Aᵀ=(approached A)ᵀ := rfl
  have he (A : Matrix (Lines G c 0) (Bodies G c f) ℝ) : approached Aᵀ=(approached A)ᵀ := rfl
  rw [hp,he, repack_multiply _ (unitSplit G S 1),repack_multiply _ (Equiv.refl (Lines G c 0)),repack_neg,repack_rotate,repack_rotate]
  exact hw

lemma gift_turn (B : Bed) (hs : 0<σ) (he : B.metric.strip (inch S.patch.L*σ) A) :
    Jaunt (repackM (clothe G S) (clothe G S) (approached (frontR G S B))) (giftQ G S.patch B S.kernel.penalty) 0 := by
  classical
  let Y := frontR G S B
  have ht := butt_travel (G:=G) (S:=S)
  have hb : 0< inch S.patch.L * σ := mul_pos (inch_pos _) hs
  have h := (rug_plane (G:=G) f B (B.metric.rights _ _ he hb.le)).press S.ratio (rug_played B he hb) hs
  have hv := net_turn (G:=G) (S:=S)
  -- rewrite `approached` transpose not `prom_adj`
  unfold frontR posting
  rw [prom_addition,repack_add,prom_mul,prom_mul,prom_tone,repack_term,prom_mul,
    show approached (butt G c f)ᵀ=(approached (butt G c f))ᵀ from rfl,show approached (fortune G S)ᵀ=(approached (fortune G S))ᵀ from rfl,
    repack_multiply _ (unitSplit G S 1),repack_multiply _ (unitSplit G S 1),repack_multiply _ (Equiv.refl (Lines G c 1)),repack_rotate,repack_rotate]
  exact (((ht.takes.hoist h).hoist ht).plus ((hv.takes.hoist hv).smul _))
end YM.Stationary
end
