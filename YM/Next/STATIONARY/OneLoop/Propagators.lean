import Mathlib.Analysis.Real.Pi.Bounds
import YM.Next.STATIONARY.OneLoop.Weights


set_option autoImplicit false
/-!
# K trajectory accounting. epoch: add shifted incoming; departures by ±q,
 arch order always (-q,q) with both at common `b`. `Week` stable under
 pay, back (with real flat), budget per field order. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {G : Gauge} {P : Patch} {V U : Jar G} {σ η A D C ζ r a : ℝ} {L T R M ρ : ι→ℝ}

structure Burst (ι κ : Type) where
    lens : ι → Track
    boost : ι → Track
    mark : ι → κ

def heatXp (X : Burst ι κ) (e : ι→Track) (i) (z:ℝ) := axes (X.lens i) + axes (z • e i)
abbrev springM (X : Burst ι κ) (i t) := axes ((t:ℝ) • X.boost i)
abbrev KPath (ι κ α β : Type) := ι→Film κ α β
abbrev storm (X : Burst ι κ) (Y : KPath ι κ α β) (i) (t : ℝ) := (Y i).tab (axes (X.lens i))
abbrev boomY (X : Burst ι κ) (Y : KPath ι κ α β) (e : ι→Track) (i t) := (Y i).tab (heatXp X e i t)
abbrev boltA (X : Burst ι κ) (Y : KPath ι κ α β) (e : ι→ Track) (i) (t : ℝ) := (Y i).spot (X.mark i) (axes (t • e i)) (axes (X.lens i))
abbrev boltB (X : Burst ι κ) (Y : KPath ι κ α β) (e : ι→ Track) (i) (t : ℝ) := (Y i).spot (X.mark i) (-axes (t • e i)) (heatXp X e i t)
abbrev oozeY (X : Burst ι κ) (Y : KPath ι κ α β) (i) t := (Y i).arch (X.mark i) (X.mark i) (- springM X i t) (springM X i t) (axes (X.lens i))

def fibP (X : Burst ι κ) (ρ L : ι→ℝ) (Y : KPath ι κ α β) (e : ι→Track) := Fiesta ρ L (boomY X Y e)
def fibQ (X : Burst ι κ) (ρ L : ι→ℝ) (Y : KPath ι κ α β) (e : ι→Track) := Fiesta ρ (ρ⁻¹*L) (boltA X Y e) ∧ Fiesta ρ (ρ⁻¹*L) (boltB X Y e)
structure Week (X : Burst ι κ) (ρ L : ι→ℝ) (Y : KPath ι κ α β) : Prop where
    front : fibP X ρ L Y X.boost
    rear : fibP X ρ L Y (-X.boost)
    tab : Fiesta ρ L (storm X Y)
    spot : fibQ X ρ L Y X.boost
    early : fibQ X ρ L Y (-X.boost)
    pays : Fiesta ρ (ρ⁻¹^2*L) (oozeY X Y)

namespace Week
variable {X : Burst ι κ} {Y Z : KPath ι κ α β} {U : KPath ι κ β γ}
lemma pair (h : Week X ρ L Y) (ht : Week X ρ T U) : Week X ρ (L*T) (fun i=> (Y i).pay (U i)) := by
  have he e (hx : fibP X ρ L Y e) (hu : fibQ X ρ L Y e) (hv : fibP X ρ T U e) (hU : fibQ X ρ T U e) : fibQ X ρ (L*T) (fun i=>(Y i).pay (U i)) e := by
    have ha := hu.1.pair ht.tab; have hc := Fiesta.pair hx hU.1
    rw [mul_assoc] at ha; rw [mul_left_comm] at hc
    constructor; exact ha.plus hc
    have hh := hu.2.pair hv; have ht := h.tab.pair hU.2; rw [mul_assoc] at hh; rw [mul_left_comm] at ht
    refine (hh.plus ht).introp (fun i=> Eventually.of_forall fun p=>?_)
    dsimp only [Pi.add_apply, storm,boomY,boltB,Film.pay,heatXp]; congr 3; abel
  refine ⟨Fiesta.pair h.front ht.front,Fiesta.pair h.rear ht.rear, Fiesta.pair h.tab ht.tab,he _ h.front h.spot ht.front ht.spot,he _ h.rear h.early ht.rear ht.early,?_⟩
  have hp := h.pays.pair ht.tab; have hu := h.tab.pair ht.pays
  have h1 := h.early.2.pair ht.early.1; have h2 := h.spot.2.pair ht.spot.1
  rw [mul_assoc] at hp; rw [mul_left_comm] at hu; rw [show ρ⁻¹*L*(ρ⁻¹*T)=ρ⁻¹^2*(L*T) by ring] at h1 h2
  refine (((hp.plus h1).plus h2).plus hu).introp fun i=> Eventually.of_forall fun p=>?_
  simp [storm,boltA, boltB, heatXp,smul_neg,axes_flip,oozeY,springM,Film.pay]
lemma merges (h : Week X ρ L Y) (he : Week X ρ L Z) : Week X ρ L (fun i=>(Y i).plus (Z i)) := ⟨Fiesta.plus h.front he.front,Fiesta.plus h.rear he.rear,Fiesta.plus h.tab he.tab,⟨h.spot.1.plus he.spot.1,h.spot.2.plus he.spot.2⟩,⟨h.early.1.plus he.early.1, h.early.2.plus he.early.2⟩,h.pays.plus he.pays⟩
lemma grew (h : Week X ρ L Y) (he : L ≤ T) : Week X ρ T Y := by
  obtain ⟨_,_,hk,_⟩ := h.tab
  have ht : ρ⁻¹*L≤ρ⁻¹*T := fun i=> mul_le_mul_of_nonneg_left (he i) (inv_nonneg.mpr (hk i).1)
  have hp : ρ⁻¹^2*L≤ρ⁻¹^2*T := fun i=> mul_le_mul_of_nonneg_left (he i) (sq_nonneg _)
  exact ⟨Fiesta.grows h.front he,Fiesta.grows h.rear he,h.tab.grows he,⟨h.spot.1.grows ht,h.spot.2.grows ht⟩,⟨h.early.1.grows ht,h.early.2.grows ht⟩,h.pays.grows hp⟩
lemma airshift (h : Week X ρ L Y) (T : ι→ℂ) (hv : ∀ i, ‖T i‖ ≤ M i) : Week X ρ (M*L) (fun i=> (Y i).weight (T i)) := by
  refine ⟨Fiesta.costsP h.front T hv, Fiesta.costsP h.rear T hv,h.tab.costsP T hv,?_,?_,?_⟩
  · unfold fibQ; rw [mul_left_comm]; exact ⟨h.spot.1.costsP T hv,h.spot.2.costsP T hv⟩
  · unfold fibQ; rw [mul_left_comm]; exact ⟨h.early.1.costsP T hv,h.early.2.costsP T hv⟩
  rw [mul_left_comm]; exact h.pays.costsP T hv
lemma holds (h : ∀ i,0≤ρ i) (Q : CompM α β) : Week X ρ 1 (fun _=> Film.cardF (fun _=> Q)) := by
  have hv : Fiesta ρ (ρ⁻¹*1) (fun _ _=> (0:CompM α β)) := Fiesta.seats (fun i=>⟨h _,mul_nonneg (inv_nonneg.mpr (h _)) zero_le_one⟩) _ rfl
  have ht : Fiesta ρ (ρ⁻¹^2*1) (fun _ _=> (0:CompM α β)) := Fiesta.seats (fun i=>⟨h _,mul_nonneg (sq_nonneg _) zero_le_one⟩) _ rfl
  exact ⟨Fiesta.subs h Q,Fiesta.subs h Q, Fiesta.subs h Q,⟨hv,hv⟩,⟨hv,hv⟩,ht⟩
lemma zeroSet (h : ∀ i,0 ≤ρ i ∧ 0≤M i) : Week X ρ M (fun _=>Film.cardF (fun _=> (0:CompM α β))) := by
  let hv := Fiesta.seats h (0:CompM α β) rfl
  have ht : Fiesta ρ (ρ⁻¹*M) (fun _ _ => (0:CompM α β)) := Fiesta.seats (fun i=>⟨(h i).1,mul_nonneg (inv_nonneg.mpr (h i).1) (h i).2⟩) _ rfl
  exact ⟨hv,hv,hv,⟨ht,ht⟩,⟨ht,ht⟩,Fiesta.seats (fun i => ⟨(h i).1,mul_nonneg (sq_nonneg _) (h i).2⟩) _ rfl⟩
end Week
end YM.Stationary
end

/-!
# Absolute Γ mass vertices. positivity prevents M-cost loss. Explicit prizes
under Week inverse. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {G : Gauge} {P : Patch} {σ η A D C ζ r a : ℝ} {L T R M ρ : ι→ℝ}

section eclipse
variable {Y : KPath ι κ α α} {X : Burst ι κ}
structure Tall (X : Burst ι κ) (L : ι→ℝ) (Y : KPath ι κ α α) : Prop where
    positive : ∀ i,0<L i
    keeps : ∀ i, IsUnit (storm X Y i 0).det
    marble : ∃ A : ℝ,0≤A∧ ∀ i,vflux ((storm X Y i 0)⁻¹)≤A/L i

lemma Tall.storms (h : Tall X L Y) (hp : Fiesta ρ L (storm X Y)) : Fiesta ρ L⁻¹ (fun i t=> (storm X Y i t)⁻¹) := hp.inv (fun i=> ⟨h.positive i,h.keeps i⟩) h.marble
lemma Tall.beats (h : Tall X L Y) {e : ι→Track} (hp : fibP X ρ L Y e) : Fiesta ρ L⁻¹ (fun i t=> (boomY X Y e i t)⁻¹) := by
  apply Fiesta.inv hp
  · intro i; refine ⟨h.positive i,?_⟩; unfold boomY heatXp; rw [zero_smul,axes_origin,add_zero]; exact h.keeps _
  unfold boomY heatXp; simp only [zero_smul,axes_origin,add_zero]; exact h.marble

lemma Week.invW (h : Week X ρ L Y) (ht : Tall X L Y) : Week X ρ L⁻¹ (fun i=> (Y i).back) := by
  let W i := (Y i).back
  have hv := ht.storms h.tab
  have hy : L⁻¹*L=1 := by funext i; exact inv_mul_cancel₀ (ht.positive i).ne'
  have hh e (hp : fibP X ρ L Y e) (hq : fibQ X ρ L Y e) : fibQ X ρ L⁻¹ W e := by
    obtain ⟨hQ,hV⟩ := hq; have he := ht.beats hp
    have h₁ := (he.pair hQ).pair hv |>.neg
    have h₂ := (hv.pair hV).pair he |>.neg
    rw [show L⁻¹*(ρ⁻¹*L)*L⁻¹=ρ⁻¹*L⁻¹ by rw [mul_left_comm L⁻¹, hy, mul_one]] at h₁ h₂
    refine ⟨h₁,h₂.introp fun i=> Eventually.of_forall fun t=>?_⟩
    simp [storm,boltB,boomY,heatXp,W,Film.back,Film.vSpot,Film.coupon]
  have hm := hh _ h.rear h.early; have hs := hh _ h.front h.spot
  refine ⟨ht.beats h.front,ht.beats h.rear,hv, hs,hm, ?_⟩
  have h1 := hm.2.pair h.early.1; have h2 := hs.2.pair h.spot.1; have h3 := hv.pair h.pays
  rw [show ρ⁻¹*L⁻¹*(ρ⁻¹*L)=ρ⁻¹^2 by rw [mul_mul_mul_comm,hy,mul_one,sq]] at h1 h2
  rw [mul_left_comm L⁻¹,hy,mul_one] at h3
  refine (((h1.plus h2).plus h3 |>.pair hv).neg).introp fun i=> Eventually.of_forall fun t=>?_
  simp only [boltB,boltA,storm,heatXp,W,Film.back,oozeY,Pi.add_apply, Pi.smul_apply,Pi.neg_apply,axes_flip, springM,smul_neg,neg_neg,neg_add_cancel,add_zero]; rfl
lemma Week.triple (h : Week X ρ L Y) : Week X ρ (L*L*L) (fun i=> tripleFilm (Y i)) := (h.pair h).pair h
end eclipse

section pace
variable (X : Burst ι (Fslot G)) {ρ μ : ι→ℝ}
lemma chertWeek (h : Week X ρ (ρ^2) (fun i=> cinder G (μ i))) (he : Tall X (ρ^2) (fun i => cinder G (μ i))) (hp : μ ≤ ρ) (hm : ∀ i,0<μ i) : Week X ρ 1 (fun i=> chert G (μ i)) := by
  refine Week.grew (L:=μ^2*(ρ^2)⁻¹) (Week.airshift (h.invW he) (M:=μ^2) (fun i=> ((μ i^2:ℝ):ℂ)) (fun i=>by rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]; rfl
    )) ?_
  intro i; change μ i^2*(ρ i^2)⁻¹≤1; rw [← div_eq_mul_inv,div_le_one (pow_pos ((hm i).trans_le (hp i)) 2)]; exact pow_le_pow_left₀ (hm i).le (hp i) _
lemma cannonWeek (h : Week X ρ 1 (fun i=> chert G (μ i))) : Week X ρ (μ^2) (fun i=> chisel G (μ i)) := by
  have hv := h.triple.triple; simp only [one_mul] at hv
  let Y := fun i=> tripleFilm (tripleFilm (chert G (μ i)))
  change Week X ρ (μ^2) (fun i => (Y i).weight (((μ i)^2:ℝ):ℂ));
  have ht : Week X ρ (μ^2*1) (fun i=> (Y i).weight ((μ i^2:ℝ):ℂ)) := hv.airshift _ (fun i=> by rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]; rfl)
  rwa [mul_one] at ht
lemma stoneWeek (h : Week X ρ (μ^2) (fun i=> chisel G (μ i))) (hp : ∀ i,0 < ρ i) : Week X ρ (μ^2) (fun i=> graniteF G (μ i)) := by
  have ht (a : Axis) : Week X ρ 1 (fun _=>Film.cardF (fun _=>dasher G a)) := Week.holds (fun i=> (hp i).le) _
  have hy (a : Axis) : Week X ρ 1 (fun _=> (Film.cardF (fun _=> dasher G a)).rear) := Week.holds (fun i=> (hp i).le) (dasher G a)ᵀ
  have he (a : Axis) : Week X ρ (μ^2) (fun i => stony G (μ i) a) := by
    have hz := ((hy a).pair h).pair (ht a); simp only [one_mul,mul_one] at hz; exact hz
  have hl (v : List Axis) : Week X ρ (μ^2) (fun i => chore v (stony G (μ i))) := by induction v with
    | nil => exact Week.zeroSet (fun i => ⟨(hp i).le,sq_nonneg (μ i)⟩)
    | cons a l hi => exact (he a).merges hi
  exact hl _
end pace
end YM.Stationary
end

/-!
# Inner norm r. lattice floor REST in uniform cube. `ColdR` links scales
β scratch all before L. Choose ramps to accept T both ≤2*µ and ≤2*r.
No denominator outside t root demanded. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α : Type} [Fintype α] [DecidableEq α] {G : Gauge} {V U : Jar G} {σ η A D C ζ r a : ℝ} {L T μ : ι→ℝ}

-- Sup coordinate fundamental; measure transfer via E4 later
def flay (p : Track) := ‖(WithLp.toLp 2 p : EuclideanSpace ℝ Axis)‖
lemma orbit_nonneg (p) : 0 ≤ flay p := norm_nonneg _
lemma orbit_sqr (p) : flay p^2=∑ i,(p i)^2 := by
  apply (EuclideanSpace.norm_sq_eq ..).trans; simp
lemma orbit_at (p) : ‖p‖≤flay p := by
  apply (pi_norm_le_iff_of_nonneg (orbit_nonneg p)).2; intro i
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (orbit_nonneg _) (by decide : 2≠0),orbit_sqr,Real.norm_eq_abs,sq_abs]; exact single_le_sum (s:=univ) (f:=fun i => p i^2) (fun _ _ => sq_nonneg _) (mem_univ i)
lemma orbit_boundary (p : Track) (h : Nave (axes p)) : flay p ≤ 2 * Real.pi := by
  have H : flay p^2 ≤ ∑ _ : Axis, Real.pi^2 := by
    rw [orbit_sqr]; refine sum_le_sum fun i _ => ?_; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) _
  rw [← pow_le_pow_iff_left₀ (orbit_nonneg _) (by positivity) (by decide : 2≠0)]; simp at H; exact H.trans_eq (by ring)
lemma orbit_lower (p : Track) (h : Nave (axes p)) : 1/4* flay p ≤ shadeK (axes p) := by
  let f := shadeK (axes p); have hf : 0≤f := slug_nonneg _
  rw [← pow_le_pow_iff_left₀ (mul_nonneg (by norm_num) (orbit_nonneg p)) hf (by decide : 2≠0),mul_pow, orbit_sqr,Finset.mul_sum]; unfold f; rw [shadeK,slug_sq];
  refine sum_le_sum fun i _ => ?_
  rw [← sq_abs (p i), ← mul_pow]
  let T := Real.pi
  have hx := real_q_lower (ground_real (axes p)) i (show |(ground (axes p) i).re|≤T from h i)
  have he : (1:ℝ)/4 ≤ 2/Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
  apply pow_le_pow_left₀ (by positivity); exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans hx

structure ColdR (X : Burst ι κ) (T μ : ι→ℝ) (A : ℝ) : Prop where
    topC : 0≤A
    lower i : 0<T i
    upper i : T i ≤ A
    avail i : ‖X.boost i‖ ≤1
    norm i : flay (X.lens i) ≤ T i
    pos i : 0<μ i
    flow i : T i ≤ flay (X.lens i) + μ i
    lease i : μ i ≤ T i
    slim i : μ i ≤ 1
    stage i : Nave (axes (X.lens i))
-- common cap relation r². can take R=µ+|k| or R=r (µ≤r). circle arc derivative scales compar equal to T.
section height
variable {X : Burst ι κ}

lemma cold_safe (h : ColdR X T μ A) (i) : 1/64*T i^2 ≤ pebWeight (axes (X.lens i)) (μ i) := by
  let a := flay (X.lens i)
  let b := shadeK (axes (X.lens i))
  have he : (1:ℝ)/4 * a ≤ b := orbit_lower _ (h.stage i)
  have hh : T i ≤ a+μ i := h.flow i
  have ha : 0 ≤ a := orbit_nonneg _; have hb : 0 ≤ b := slug_nonneg _; have ht := h.lower i
  change _≤b^2+_; nlinarith [pow_le_pow_left₀ ht.le hh 2, sq_nonneg (a-μ i),pow_le_pow_left₀ (mul_nonneg (by norm_num) ha) he 2]
lemma solidT {Y : KPath ι κ α α} {a : ℝ} (h : ∀ i, Stable (storm X Y i 0) (a*T i)) (ha : 0<a) (ht : ∀ i,0<T i) : Tall X T Y := by
  refine ⟨ht,fun i=> (h i).safe (mul_pos ha (ht i)), a⁻¹,(inv_pos.mpr ha).le,fun i=> (Stable.bill (h i) (mul_pos ha (ht i))).trans_eq (by field_simp)⟩
end height
section pact
variable {X : Burst ι (Fslot G)}
lemma cinderTall (h : ColdR X T μ A) : Tall X (T^2) (fun i=> cinder G (μ i)) := by
  let F i := cinder G (μ i)
  have he (i) : Stable (storm X F i 0) (1/64*(T^2) i) := by
    let p := axes (X.lens i)
    intro b; unfold storm; simp only [F,crumbly (σ:=1) zero_lt_one _ (Work.F07.realStrip _ zero_lt_one (axes_real (X.lens i))),Matrix.smul_mulVec,Matrix.one_mulVec]
    rw [slug_scale]; apply mul_le_mul_of_nonneg_right _ (slug_nonneg b)
    let k := μ i
    have hk : soda k p= ↑(pebWeight p k) := by unfold soda pebWeight; rw [stone_real (axes_real _)]; push_cast; rfl
    rw [hk,Complex.norm_real,Real.norm_of_nonneg (peb_pos _ (h.pos _) |>.le)]; exact cold_safe h i
  exact solidT he (by norm_num) (fun i=> pow_pos (h.lower _) _)
lemma grainTall (h : ColdR X T μ A) : Tall X (T^2) (fun i => coring G (μ i)) := by
  let F i := coring G (μ i); have hv i : Stable (storm X F i 0) ((1:ℝ)/(2^10)*(1/64)*(T^2) i) := by
    unfold storm F; rw [flakeTabs (h.pos _) (h.slim _) _ (Work.F07.realStrip _ (mul_pos (h.pos i) (by norm_num)) (axes_real _))];
    exact (stable_real (fun v=> throne_floor (p:=axes (X.lens i)) v (axes_real _) (h.pos i))).mono (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (cold_safe h i) (by norm_num))
  exact solidT hv (by norm_num) (fun i=> pow_pos (h.lower _) _)

structure Skuta (ι : Type) (G : Gauge) where
    light : ι → Jar G
    terra : ι → Bed
    top : ι → Clip
    σ : ι →ℝ
    μ : ι →ℝ
variable {S : Skuta ι G}
def Skuta.Live (S : Skuta ι G) (η D ε C : ℝ) (V : Jar G) : Prop := ∀ i,
    let f := S.light i
    let W := (f.combine V).cast
    HouseWord G (S.terra i) (S.top i) D ε (S.σ i) D (S.μ i) W ∧ f.fees η C ∧ f.soft 3
-- same ε everywhere even if model epochs varying.
lemma granaryTall {B : ι→Bed} {p : ι→Clip} {σ : ι→ℝ} {F : ι→KindF G} {ε : ℝ} (h : ColdR X T μ A) (he : ∀ i, HouseWord G (B i) (p i) D ε (σ i) C (μ i) (F i)) (hx : 0<ε) : Tall X (T^2) (fun i=>massif G (μ i) (F i)) := by
  let K i := massif G (μ i) (F i); let L := min ε 1/(2^10:ℝ)
  have hL : 0 < L := div_pos (lt_min hx zero_lt_one) (by norm_num)
  have ht i : Stable (storm X K i 0) (L*(1/64)*(T^2) i) := by
    let V := he i
    unfold storm K; rw [V.pact _ (Work.F07.realStrip _ V.pos (axes_real _))]
    exact (stable_real (fun x=> dais_floor (axes_real _) (p i) (B i) (h.pos i) x V.metric V.pos V.lower hx)).mono (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (cold_safe h i) hL.le)
  exact solidT ht (by positivity) (fun i=> pow_pos (h.lower _) _)
end pact
end YM.Stationary
end

/-!
# Bare heat matched kernel. Arch only O(D^4) real directions; no leading
claim for arch. Budget `Cast` for true Legend filters.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] {G : Gauge} {P : Patch} {V U : Jar G} {σ η A D C ζ r a ε : ℝ} {T μ : ι →ℝ} {n : ℕ}

section tenor
lemma patrol_house {ι : Type} [Fintype ι] {F : Film ι α α} (v : ℝ) (n) (h : Play F σ) (hp : 0<σ) (a : γ→ι) : Patrol n v (fun _:γ=>ashP F) ∧ Patrol n v (fun i=>ashQ F (a i)) ∧ Patrol n v (fun i => ashR F (a i)) := ⟨Patrol.marries (fun _:Unit=>ashP F) (fun _ x i j=> h.tab.craft hp x i j) (fun _=>()) _ _, Patrol.marries (ashQ F) (fun b x i j=> (h.spot b).windowR hp x i j) _ _ _, Patrol.marries (ashR F) (fun b x i j=> archiveR h hp x b i j) _ _ _⟩
lemma patrol_president (U : ι→Jar G) (ρ : ℝ) (h : ∀ i,(U i).fees σ C) (hp : 0<σ) (n : ℕ) (b : ι→ Fslot G) :
    Patrol n ρ (fun i=> ashP (U i).cast) ∧ Patrol n ρ (fun i=> ashQ (U i).cast (b i)) ∧ Patrol n ρ (fun i=> ashR (U i).cast (b i)) := by
  have hu (f : ℕ→ℝ) : ∃ C : ℝ,0≤C ∧ ∀ j≤n,f j≤C := ⟨∑ j∈Finset.range (n+1),|f j|,sum_nonneg fun i _=>abs_nonneg _,fun i hi=> (le_abs_self _).trans (single_le_sum (f:=fun j=>|f j|) (fun j _=>abs_nonneg _) (mem_range.mpr (by omega)))⟩
  obtain ⟨A,hA,X⟩ := hu (fun j=>C*circleTax σ j*‖coaxes‖^j)
  obtain ⟨B,hB,Y⟩ := hu (fun j=>C*circleTax σ j*‖centaur‖^j)
  obtain ⟨D,hD,W⟩ := hu (fun j=>C*circleTax σ j*‖cinnamon‖^j)
  refine ⟨⟨A,hA,fun i j l=> ⟨fun x=> (h i).live.tab.craft hp _ _ _, fun p hx t hn => (ashCost1 (h i) p j l t).trans (X t hn)⟩⟩,⟨B,hB,fun i j l=> ⟨fun x=> ((h i).live.spot (b i)).windowR hp x j l,fun p hx t hn => (ashCost2 (h i) p (b i) j l t).trans (Y t hn)⟩⟩,
      D,hD,fun i j l=> ⟨fun x=> archiveR (h i).live hp x (b i) j l,fun p hx t hn => (ashCost3 (h i) p (b i) j l t).trans (W t hn)⟩⟩
end tenor

section focus
variable {X : Burst ι κ} {F : KPath ι κ α α}
def Enclave (κ α : Type) [DecidableEq α] (V : κ→ Track→Track →CompM α α) : Prop := ∀ i j k, (∀ x : GlideTrack, AnalyticAt ℝ (fun z : GlideTrack=>V i z.1 z.2 j k) x) ∧ Rays 1 (fun z : GlideTrack=> V i z.1 z.2 j k)

structure Floe (X : Burst ι κ) (F : KPath ι κ α α) (V : κ→ Track→Track →CompM α α) (r : ℝ) : Prop where
    paid : Enclave κ α V
    cap0 : Patrol 3 r (fun i=> ashP (F i))
    cap1 : Patrol 2 r (fun i=> ashQ (F i) (X.mark i))
    cap2 : Patrol 2 r (fun i=> ashR (F i) (X.mark i))
    spot0 : ∀ i j l,Rays 3 (fun x : Track=> ashP (F i) x j l - skull x α j l)
    spot1 : ∀ i j l,Rays 2 (fun x : GlideTrack=> ashQ (F i) (X.mark i) x j l - V (X.mark i) x.1 x.2 j l)
lemma enclaveG (G : Gauge) : Enclave (Fslot G) (Foot G) (hurr (G:=G)) := fun b i j=> ⟨fun _ => (hurr_cont b i j).contDiffAt.analyticAt, (rays_at_zero ((hurr_cont b i j).contDiffAt.analyticAt)).2 (by simp [hurr,ghostC,tachy])⟩
lemma enclaveV (G : Gauge) : Enclave (Fslot G) (Fslot G) (herr (G:=G)) := fun b i j=> ⟨fun _ => (herr_cont b i j).contDiffAt.analyticAt, (rays_at_zero ((herr_cont b i j).contDiffAt.analyticAt)).2 (by simp [herr,vectorC,ghostC,tachy])⟩
lemma Floe.ghost (X : Burst ι (Fslot G)) (ρ) : Floe X (fun _=> quarry G) (hurr (G:=G)) ρ := by
  have hx := quarry_p (G:=G) (σ:=1)
  have h n:=patrol_house ρ n hx zero_lt_one X.mark; exact ⟨enclaveG G,(h 3).1,(h 2).2.1,(h 2).2.2,fun _ v w => quarryLum v w,fun i j k=> screamer zero_lt_one _ _ _⟩

variable {S : Skuta ι G}
def Skuta.useJar (S : Skuta ι G) (W : Jar G) (i) := ((S.light i).combine W).cast
def Border (T : ι→KindF G) : ι→KindF G := fun i=> granary G (T i)
lemma Floe.vector (h : S.Live η D ε C V) (hs : 0<η) (hw : V.grey) (hv : V.fees η A) (X : Burst ι (Fslot G)) (p) : Floe X (Border (S.useJar V)) (herr (G:=G)) p := by
  let F:= fun i=> (S.light i).combine V
  have he i:= h i
  have hk n := patrol_president F p (fun i=> ((h i).2.1.pay hv)) hs n X.mark; let Q := (matina G).pay (matina G).rear
  have hL : Play Q 1 := matina_green.pay matina_green.rear
  have hm n:= patrol_house p n hL zero_lt_one X.mark
  exact ⟨enclaveV _, (hk 3).1.plus (hm 3).1, (hk 2).2.1.plus (hm 2).2.1,(hk 2).2.2.plus (hm 2).2.2,fun i j k => bedLum (h i).1 j k,fun i j k=> inflamed (h i).2.2 hw hv hs _ _ _⟩
end focus
end YM.Stationary
end

/-!
# Aspire bounds. Derivatives `r^n` at τ=0. `fib` frames ∀ unit
axes. Includes envelope of arch2 alone in **unscaled** derivative.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α : Type} [Fintype α] [DecidableEq α] {G : Gauge} {P : Patch} {V U : Jar G} {σ A D C ζ r a ε : ℝ} {T μ : ι →ℝ}
section shape
lemma pebb_t (x : Track) (h : ℝ) : pebb (h • x) = (h:ℂ)^2*pebb x := by unfold pebb; simp [mul_pow,mul_sum]
lemma skull_ray (α : Type) [DecidableEq α] (i j : α) : Rays 2 (fun x : Track=> skull x α i j) := by
  intro p; let L := (skull p α) i j
  have he (t : ℝ) : skull (t • p) α i j = L*(t:ℂ)^2 := by unfold skull L; simp [skull,pebb_t]; ring
  simp_rw [he]; apply Asymptotics.IsBigO.const_mul_left
  apply isBigO_of_le' (c:=1); simp
lemma skull_green (α : Type) [DecidableEq α] (i j : α) (x) : AnalyticAt ℝ (fun p : Track=>skull p α i j) x := by
  unfold skull; simp only [Matrix.smul_apply,smul_eq_mul]; refine AnalyticAt.mul ?_ analyticAt_const; unfold pebb; apply ContDiffAt.analyticAt
  exact ContDiffAt.sum (fun i _ => ContDiffAt.pow ((Complex.ofRealCLM ∘L (ContinuousLinearMap.proj (φ:=fun _ : Axis=>ℝ) i)).contDiff.contDiffAt) 2)
end shape
section lifts
variable [Fintype κ] {W : κ →Track → Track→ CompM α α} {X : Burst ι κ} {F : KPath ι κ α α}

def stroll (X : Burst ι κ) (e : ι→Track) (i : ι) (t : ℝ) := X.lens i+t • e i
def shone (α : Type) [DecidableEq α] (X : Burst ι κ) (e : ι→Track) (i t) := skull (stroll X e i t) α
def panT (X : Burst ι κ) (W : κ→ Track→ Track→CompM α α) (e : ι→Track) (i) (t : ℝ) := W (X.mark i) (t • e i) (X.lens i)
def panL (X : Burst ι κ) (W : κ→ Track→ Track→CompM α α) (e : ι→Track) (i) (t : ℝ) := W (X.mark i) (t • -e i) (stroll X e i t)
variable {e : ι→Track} (h : Floe X F W r) (hp : ColdR X T μ r) (he : ∀ i, ‖e i‖≤1)
include hp in
lemma ColdR.travel (i) : 0<T i ∧ ‖X.lens i‖≤T i ∧ X.lens i∈closedBall 0 r := by have hx := (orbit_at _).trans (hp.norm i); exact ⟨hp.lower i,hx,by simpa using hx.trans (hp.upper i)⟩
lemma pointBoom (X : Burst ι κ) (e : ι → Track) i t : heatXp X e i t=axes (stroll X e i t) := axes_solid _ _|>.symm
include h hp he
lemma bloomJ : Fiesta T (T^3) (boomY X F e-shone α X e) ∧ Fiesta T (T^2) (shone α X e) := by
  let Y := fun _ : ι=> (fun x : Track=>skull x α)
  have hx (n) : Patrol n r Y := Patrol.marries (fun _ : Unit=>fun x=>skull x α) (fun _ x i j=> skull_green α i j x) (fun _=>()) _ _
  constructor
  · have ht := sipPatrol (F:= (fun i => ashP (F i))-Y) (h.cap0.plus (hx 3).neg) (by decide : 2 ≤ 3) hp.topC h.spot0 X.lens e hp.travel he
    refine ht.introp fun i=> Eventually.of_forall fun t=> ?_
    simp [boomY, pointBoom,stroll,Y,ashP,shone]
  exact sipPatrol (hx 2) le_rfl hp.topC (fun _ i j => skull_ray α i j) X.lens e hp.travel he
-- `fibQ` cost T not r^-1. angular path pair stack
lemma sepJ : Fiesta T (T^2) (boltA X F e-panT X W e) ∧ Fiesta T (T^2) (boltB X F e-panL X W e) ∧ Fiesta T T (panT X W e) ∧ Fiesta T T (panL X W e) := by
  let Y := fun i (x : GlideTrack)=> W (X.mark i) x.1 x.2
  have ht : Patrol 2 r Y := Patrol.marries (fun i (x:GlideTrack)=> W i x.1 x.2) (fun i x j k=> (h.paid i j k).1 x) X.mark _ _
  let U := fun i=> ashQ (F i) (X.mark i); let C i : GlideTrack:= (0,X.lens i); let b i : GlideTrack:= (e i,0); let a i : GlideTrack:= (-e i,e i)
  have hz i : ‖C i‖=‖X.lens i‖ := by simp [C]
  have hu i : 0<T i ∧ ‖C i‖ ≤ T i ∧ C i∈closedBall 0 r := by rw [hz]; exact ⟨(hp.travel i).1,(hp.travel i).2.1,by simpa [hz] using ((hp.travel i).2.1.trans (hp.upper i))⟩
  have hb i : ‖b i‖ ≤ 1 := by simpa [b] using he i
  have ha i : ‖a i‖≤ 1 := by simp [a,Prod.norm_def,he i]
  have hv v (hv : ∀ i,‖v i‖ ≤ (1:ℝ)) := sipPatrol (F:=U-Y) (h.cap1.plus ht.neg) (by decide : 2≤2) hp.topC h.spot1 C v hu hv
  have hK (v : ι→GlideTrack) (hv : ∀ i,‖v i‖ ≤ (1:ℝ)) : Fiesta T T (fun i t=> Y i (C i+t • v i)) := by
    have hy := sipLight (F:=Y) ht (by decide : 1≤2) hp.topC hp.topC (fun i a b=> (h.paid _ a b).2) C v (fun i=>⟨(hu i).1,(hu i).2.1,(hu i).2.2,hp.upper i⟩) hv
    simp only [pow_one] at hy; exact hy
  refine ⟨(hv b hb).introp (fun i=> Eventually.of_forall fun t => ?_), (hv a ha).introp (fun i=> Eventually.of_forall fun t => ?_), (hK b hb).introp (fun i=> Eventually.of_forall fun t=> ?_), (hK a ha).introp (fun i=> Eventually.of_forall fun t=> ?_)⟩ <;> simp [boltA,boltB,C,b,a,U,Y, pointBoom,stroll,panL,panT,ashQ,axes_flip]
lemma stepsJ : fibP X T (T^2) F e ∧ fibQ X T (T^2) F e := by
  obtain ⟨hU,hY⟩ := bloomJ h hp he; obtain ⟨h1,h2,h3,h4⟩ := sepJ h hp he
  have ht : T^3 ≤ fun i=> r*(T^2) i := fun i=> by change T i^3 ≤ r*T i^2; rw [pow_succ,mul_comm]; exact mul_le_mul_of_nonneg_right (hp.upper i) (sq_nonneg _)
  have hx := hU.dilutes r hp.topC (fun i => sq_nonneg (T i)) ht
  have hz := hx.plus hY; rw [sub_add_cancel] at hz
  refine ⟨hz,?_⟩
  have ht : T^2 ≤ fun i=>r*T i := fun i=> by rw [Pi.pow_apply,sq]; exact mul_le_mul_of_nonneg_right (hp.upper i) (hp.lower i).le
  have hb (Q R : ι→ReelF α α) (h : Fiesta T (T^2) (Q-R)) (he : Fiesta T T R) : Fiesta T (T⁻¹*T^2) Q := by
    rw [show T⁻¹*T^2=T by ext1 i; dsimp; field_simp [(hp.lower i).ne']]; simpa only [sub_add_cancel] using (h.dilutes r hp.topC (fun i=> (hp.lower i).le) ht).plus he
  exact ⟨hb _ _ h1 h3,hb _ _ h2 h4⟩
omit he in
lemma rainP : Fiesta (fun _=>1) 1 (oozeY X F) := by
  obtain ⟨A,hA,H⟩ := h.cap2
  let v i:= ashR (F i) (X.mark i); let Y:=oozeY X F; let a i : GlideTrack := (0,X.lens i); let b i : GlideTrack := (X.boost i,0)
  have ht i x : Y i x=v i (a i+x • b i) := by simp [Y,v,a,b,oozeY,springM,ashR]
  refine ⟨fest α α*A,mul_nonneg fest_pos hA,fun i=> ⟨zero_le_one,zero_le_one⟩,fun i=>?_⟩; rw [Pi.one_apply,mul_one]
  refine limo_cast _ ?_ hA zero_lt_one fun j k n hz=> ?_
  · intro x y; change AnalyticAt ℝ (fun z=> Y i z x y) 0; simp_rw [ht]
    let g z:= v i z x y
    refine (ContDiffAt.comp (g:=g) _ ((H i x y).1 _ |>.contDiffAt) (by fun_prop)).analyticAt
  rw [one_pow,one_mul]; let f z:= v i z j k
  have he : ‖iteratedFDeriv ℝ n f (a i)‖ ≤ A := (H i j k).2 _ (by simpa [a] using ((hp.travel i).2.2)) _ hz
  have hs : ‖b i‖ ≤1 := by simpa [b] using (hp.avail i)
  rw [show (fun z =>oozeY X F i z j k) = (fun z=> f (a i+z • b i)) from funext (fun z=>congr_fun (congr_fun (ht i z) _) _), sipRay (R:=f) (a i) (b i) ((H i j k).1 _)]
  exact (ContinuousMultilinearMap.le_opNorm ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (by simpa using pow_le_one₀ (norm_nonneg _) hs (n:=n))).trans he)
omit he in
lemma weeks : Week X T (T^2) F := by
  have ha := stepsJ h hp hp.avail; have hb := stepsJ h hp (e:=-X.boost) (fun i=> by simpa using hp.avail i)
  have hf := stepsJ (e:=0) h hp (by simp)
  refine ⟨ha.1, hb.1, Fiesta.introp hf.1 (fun i=> Eventually.of_forall (fun t=> by simp [boomY,heatXp,storm])),ha.2,hb.2,?_⟩
  rw [show T⁻¹^2*T^2=1 by ext1 i; dsimp; field_simp [(hp.lower i).ne']]
  obtain ⟨A,hA,hZ,H⟩ := rainP h hp
  refine ⟨(1+r)^2*A,by positivity,fun i=> ⟨(hp.lower _).le,zero_le_one⟩,fun i=> ?_⟩
  refine ⟨(H i).run,fun n hn=>?_⟩; rw [Pi.one_apply,mul_one]
  have ht := (H i).prices n hn; rw [one_pow,one_mul,Pi.one_apply,mul_one] at ht
  have hx := hp.topC
  exact mul_le_mul ((pow_le_pow_left₀ (hp.lower i).le (show T i≤ 1+r by linarith [hp.upper i]) n).trans (pow_le_pow_right₀ (by linarith) hn)) ht (flux_nonneg _) (sq_nonneg _)
end lifts
end YM.Stationary
end

/-!
# Box app. Tad actual aggregate. Absolute estimate e-functions used over T∈inner and ray exact. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {V : Jar G} {p : Clip} {σ η A C D r a ε : ℝ} {T μ : ι→ℝ} {n : ℕ} {X : Burst ι κ}

section atmosphere
variable {X : Burst ι (Fslot G)} {S : Skuta ι G}
lemma cinderWeek (h : ColdR X T μ r) : Week X T (T^2) (fun i=>cinder G (μ i)) := by
  have he := weeks (Floe.ghost X r) h
  let Q i := Film.cardF (ι:=Fslot G) (fun p : Momentum=> ((μ i^2:ℝ):ℂ) • (1:CompM (Foot G) (Foot G)))
  refine he.merges (?_ : Week X T (T^2) Q)
  let U := Film.cardF (ι:=Fslot G) (fun _=> (1:CompM (Foot G) (Foot G)))
  have ht : Week X T 1 (fun _=>U) := Week.holds (fun i=> (h.lower i).le) _
  have hp := Week.airshift ht (M:=μ^2) (fun i=> ((μ i^2:ℝ):ℂ)) (fun i=> by rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]; rfl)
  rw [mul_one] at hp
  have hx : Q=fun i=> U.weight (((μ i^2:ℝ)):ℂ) := by
    funext i; unfold Q U Film.cardF Film.weight; simp; rfl
  rw [hx]; exact hp.grew (fun i=> pow_le_pow_left₀ (h.pos i).le (h.lease i) 2)
lemma glaze (h : ColdR X T μ r) : Week X T (μ^2) (fun i=> chisel G (μ i)) ∧ Week X T (μ^2) (fun i=> graniteF G (μ i)) := by
  have hp := cannonWeek X (chertWeek X (cinderWeek h) (cinderTall h) h.lease h.pos)
  exact ⟨hp,stoneWeek X hp h.lower⟩

end atmosphere

section contract
variable [Fintype κ]
def Fleet (X : Burst ι κ) (ρ T : ι →ℝ) (Y Z : KPath ι κ α α) (W : κ→ Track→ Track→CompM α α) (r : ℝ) :=
    Floe X Y W r ∧ Week X ρ (T^2) Z ∧ Tall X (ρ^2) (fun i => (Y i).plus (Z i)) ∧ ColdR X ρ T r

end contract
abbrev atopY (F G : KPath ι κ α α) (i) := (F i).plus (G i)
abbrev carre (X : Burst ι κ) (F : KPath ι κ α α) (i) (t : ℝ) := (storm X F i t)⁻¹
abbrev coup (X : Burst ι κ) (F : KPath ι κ α α) (i) (t : ℝ) := (boomY X F X.boost i t)⁻¹
def upperJet (X : Burst ι κ) (F : KPath ι κ α α) (i) t := carre X F i t * oozeY X F i t
def lowerJet (X : Burst ι κ) (Y : KPath ι κ α α) (i) t := carre X Y i t * boltB X Y X.boost i t * coup X Y i t * boltA X Y X.boost i t
lemma framePing (F : KPath ι κ α α) (i t) : (F i).figure (X.mark i) (X.mark i) (springM X i t) (axes (X.lens i))= (upperJet X F i t).trace- (lowerJet X F i t).trace := by
  unfold Film.figure Film.framePay; rw [neg_add_cancel,add_zero,trace_sub]; rfl
lemma flare_trc {u : ReelF α α} (hp : Prick u) : flareY n (fun x=> (u x).trace)=(jarY n u).trace := by
  rw [show (fun x=> (u x).trace)=(fun x=>∑ i,u x i i) from rfl, flare_sum]; rfl
  exact fun i _=> hp i i
lemma Prick.sides {u : ReelF α α} (h : Prick u) : AnalyticAt ℝ (fun x=> (u x).trace) 0 := (ContDiffAt.sum (s:=univ) (f:=fun i x=> u x i i) (n:=ω) (fun i _=> (h i i).contDiffAt)).analyticAt
namespace Fleet
variable [Fintype κ] {F Y : KPath ι κ α α} {W : κ→Track→Track→CompM α α} (h : Fleet X T μ F Y W r)
include h
lemma basic : Week X T (T^2) (atopY F Y) := (weeks h.1 h.2.2.2).merges (h.2.1.grew (fun i=>pow_le_pow_left₀ (h.2.2.2.pos i).le (h.2.2.2.lease i) 2))
lemma bubbleHV : Fiesta T (T^2)⁻¹ (upperJet X (atopY F Y)) ∧ Fiesta T (T^2)⁻¹ (lowerJet X (atopY F Y)) := by
  let Z := atopY F Y; let G := basic h
  have ht := h.2.2.1.storms G.tab
  have hu := h.2.2.1.beats (Y:=Z) G.front
  have hb := ht.pair G.pays
  have he := ((ht.pair G.spot.2).pair hu).pair G.spot.1
  have hx (i) := h.2.2.2.lower i
  refine ⟨?_,?_⟩
  · rw [show _= (T^2)⁻¹ from (show (T^2)⁻¹*(T⁻¹^2*T^2)=(T^2)⁻¹ by ext1 i; dsimp; field_simp [(hx i).ne'])] at hb; exact hb
  rw [show (T^2)⁻¹*(T⁻¹*T^2)*(T^2)⁻¹*(T⁻¹*T^2)=(T^2)⁻¹ by ext1 i; dsimp; field_simp [(hx i).ne']] at he; exact he
lemma lacy (i) : AnalyticAt ℝ (fun t=> (upperJet X (atopY F Y) i t).trace) 0 ∧ AnalyticAt ℝ (fun t=> (lowerJet X (atopY F Y) i t).trace) 0 := by
  obtain ⟨⟨u,_,_,hU⟩,⟨v,_,_,hV⟩⟩ := bubbleHV h; exact ⟨(hU i).run.sides,(hV i).run.sides⟩

-- actual estimate including unscaled tad.
omit h in
lemma focus_bill {F : ι→ ReelF β β} {L : ι →ℝ} (h : Fiesta T L F) (hp : ∀ i,0<T i) : ∃ A : ℝ, 0≤A ∧ ∀ i, ‖flareY 2 (fun t=> (F i t).trace)‖ ≤ A* L i/T i^2 := by
  obtain ⟨A,hA,ht,h⟩ := h; let B : ℝ := (Fintype.card β:ℝ); have hb : 0 ≤ B := Nat.cast_nonneg _
  refine ⟨B*A,mul_nonneg hb hA,fun i=> ?_⟩; rw [flare_trc (h i).run, le_div_iff₀ (pow_pos (hp i) _)]
  exact (mul_le_mul_of_nonneg_right (flux_trace ..) (sq_nonneg _)).trans (by rw [mul_assoc,mul_comm (vflux _),mul_assoc B A]; exact mul_le_mul_of_nonneg_left ((h i).prices 2 le_rfl) hb)
lemma bubbleControl : ∃ A : ℝ, 0≤A ∧ ∀ i, ‖flareY 2 (fun t=> (lowerJet X (atopY F Y) i t).trace)‖≤A/T i^4 := by
  obtain ⟨A,hA,hB⟩ := focus_bill (bubbleHV h).2 h.2.2.2.lower
  exact ⟨A,hA,fun i => (hB i).trans_eq (by simp; ring)⟩
lemma tadControl : ∃ A B : ℝ, 0≤A ∧ 0≤ B ∧ ∀ i, ‖flareY 2 (fun t=> (upperJet X (atopY F Y) i t).trace)‖ ≤ A/T i^2+B*μ i^2/T i^6 := by
  let Z := atopY F Y
  let P i t := (carre X Z i t) * oozeY X Y i t
  have hx := h.2.2.2; have hμ i := hx.lower i
  have ht : Fiesta T (T^2)⁻¹ (carre X Z) := h.2.2.1.storms (basic h).tab
  obtain ⟨A,hA,hP⟩ := focus_bill (ht.pair h.2.1.pays) hx.lower
  let L i t := carre X Z i t*oozeY X F i t
  have hz : Fiesta (fun _=>1) (T^2)⁻¹ L := by
    have hg : Fiesta (fun _=>1) (T^2)⁻¹ (carre X Z) := by
      obtain ⟨A,hA,hm,h⟩ := ht
      refine ⟨A,hA,fun i=>⟨zero_le_one,(hm i).2⟩,fun i=> (Jam.seats (1:ℝ) (carre X Z i 0)).mono (h i|>.ipay)⟩
    have hu := hg.pair (rainP h.1 hx); rw [mul_one] at hu; exact hu
  obtain ⟨B,hB,hL⟩ := focus_bill (T:=fun _ : ι=>1) hz (fun _=>zero_lt_one)
  obtain ⟨u,_,_,hU⟩ := hz
  have he : Fiesta T _ P := ht.pair h.2.1.pays; obtain ⟨v,_,_,HV⟩ := he
  refine ⟨B,A,hB,hA,fun i=> ?_⟩
  let f t := trace (L i t); let g t := trace (P i t)
  have hf : AnalyticAt ℝ f 0 := (hU i).run.sides; have hg : AnalyticAt ℝ g 0 := (HV i).run.sides
  rw [show (fun t=> (upperJet X (atopY F Y) i t).trace)=f+g from funext (fun t=> by
    rw [← show L i t+P i t=upperJet X (atopY F Y) i t by unfold L P; rw [← Matrix.mul_add]; rfl,trace_add]; rfl),flare_add hf hg]
  refine (norm_add_le ..).trans (add_le_add ((hL i).trans_eq ?_) ((hP i).trans_eq ?_)) <;> (simp; ring)
end Fleet
end YM.Stationary
end

/-!
# Annulus limits for bubble. Sign here kept positive in lowerJet;
stamp via frame subtraction. Uses exact peak width Tall at µ+Y. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {G : Gauge} {P : Patch} {V U : Jar G} {σ A D C ζ r a : ℝ} {W : κ→ Track→Track→CompM α α} {T μ : ι →ℝ} {n : ℕ}

section shoes
variable [Fintype κ] {X : Burst ι κ} {F G : KPath ι κ α α}

def rimEdge (T μ : ι→ℝ) := T+ μ^2*(T^2)⁻¹
lemma pebbFl (k : Track) : pebb k=((flay k:ℂ)^2) := by rw [← Complex.ofReal_pow,orbit_sqr]; unfold pebb; push_cast; rfl
lemma skullSafe (k : Track) (h : 0<flay k) : IsUnit (skull k α).det ∧ vflux (skull k α)⁻¹ ≤ (flay k^2)⁻¹ := by
  have ht : pebb k≠0 := by rw [pebbFl]; norm_cast; exact pow_ne_zero _ h.ne'
  unfold skull; constructor
  · rw [Matrix.det_smul,Matrix.det_one, mul_one]; exact ht.isUnit.pow _
  rw [show (pebb k • (1:CompM α α))⁻¹=(pebb k)⁻¹ • 1 by
    apply inv_eq_right_inv; rw [Matrix.mul_smul, Matrix.mul_one,smul_smul,inv_mul_cancel₀ ht,one_smul], flux_cost]
  apply (mul_le_of_le_one_right (norm_nonneg _) flux_one).trans; rw [norm_inv,pebbFl, norm_pow, Complex.norm_real, Real.norm_of_nonneg (orbit_nonneg ..)]

def haloC (X : Burst ι κ) (W : κ→Track→Track→CompM α α) (i t) := (shone α X 0 i t)⁻¹ * panL X W X.boost i t * (shone α X X.boost i t)⁻¹ * panT X W X.boost i t
namespace Fleet
lemma cool0 (h : Fleet X T μ F G W r) (e) (hp : ∀ i,‖e i‖≤1) (hv : ∀ i,e i=0 ∨ e i=X.boost i)
    (hx : T=flay ∘ X.lens) (hb : fibP X T (μ^2) G e) :
    let Z := atopY F G
    let D i t := (shone α X e i t)⁻¹
    let K i t := (boomY X Z e i t)⁻¹
    Fiesta T (T^2)⁻¹ K ∧ Fiesta T (T^2)⁻¹ D ∧ Fiesta T (rimEdge T μ*(T^2)⁻¹) (K-D) := by
  intro Z D K
  obtain ⟨hU,hM⟩ := bloomJ h.1 h.2.2.2 hp
  have hc (i) : 0<T i := h.2.2.2.lower _
  let P := boomY X Z e; let R := shone α X e
  have hk (i) : R i 0=skull (X.lens i) α := by simp [R,shone,stroll]
  have hm i : 0<flay (X.lens i) := (hc i).trans_le ((congr_fun hx i).le)
  have ht : Fiesta T (T^2)⁻¹ D := by
    refine (Fiesta.inv hM (fun i => ?_) ⟨1,zero_le_one,fun i=> ?_⟩)
    · rw [show shone α X e i 0=_ from hk i]; exact ⟨pow_pos (hc _) _,(skullSafe _ (hm _)).1⟩
    rw [show shone α X e i 0=_ from hk i,hx]; simp only [Pi.pow_apply,Function.comp_apply,one_div]; exact (skullSafe _ (hm _)).2
  have hp' : μ^2≤ T^2 := fun i=> pow_le_pow_left₀ (h.2.2.2.pos i).le (h.2.2.2.lease i) 2
  have hy : Fiesta T (T^2) P := (stepsJ h.1 h.2.2.2 hp).1 |>.plus (hb.grows hp')
  have hh := h.2.2.1
  have hN : Fiesta T (T^2)⁻¹ K := hh.beats (Y:=Z) (X:=X) (e:=e) hy
  refine ⟨hN,ht, Fiesta.invDiff (X:=P) (Y:=R) hy hM hN ht ?_ (?_ : Fiesta T (rimEdge T μ*T^2) (P-R))⟩
  · intro i; rw [hk i]; refine ⟨pow_pos (hc _) _,?_,(skullSafe _ (hm _)).1⟩; unfold P boomY heatXp; rw [zero_smul,axes_origin,add_zero]; exact hh.keeps i
  have h1 : rimEdge T μ*T^2= T^3+μ^2 := by
    unfold rimEdge; ext1 i; dsimp; field_simp [(hc i).ne']
  rw [h1]; have he := Fiesta.plus (hU.grows (M:=T^3+μ^2) (fun i=>le_add_of_nonneg_right (sq_nonneg (μ i)))) (Fiesta.grows hb (fun i=>le_add_of_nonneg_left (pow_nonneg (hc _).le 3))); refine he.introp fun i=> Eventually.of_forall fun t=>?_
  change boomY X F e i t- shone α X e i t+ boomY X G e i t= boomY X F e i t+boomY X G e i t - _; unfold R; abel
-- unify Fiesta product difference sign normalization
lemma brass (h : Fleet X T μ F G W r) (hx : T=flay ∘ X.lens) : Fiesta T (T^2)⁻¹ (haloC X W) ∧ Fiesta T (rimEdge T μ*(T^2)⁻¹) (lowerJet X (atopY F G)-haloC X W) := by
  let Z := atopY F G
  have hc i : 0<T i := h.2.2.2.lower i
  have hp : ∀ i,‖X.boost i‖≤1 := h.2.2.2.avail
  have hv e : boomY X e 0=storm X (e:KPath ι κ α α) := by funext i t; simp [boomY,heatXp,storm]
  have hb : Fiesta T (μ^2) (boomY X G 0) := by rw [hv]; exact h.2.1.tab
  obtain ⟨h1,h2,h3⟩ := h.cool0 0 (by simp) (fun _=> Or.inl rfl) hx hb
  let K i t := carre X Z i t; let D i t := (shone α X 0 i t)⁻¹
  have hK : Fiesta T (T^2)⁻¹ K := by unfold K carre; rw [← hv Z]; exact h1
  have hD : Fiesta T (rimEdge T μ*(T^2)⁻¹) (K-D) := by unfold K carre; rw [← hv Z]; exact h3
  have hh := X.boost
  obtain ⟨ha,hP,H⟩ := h.cool0 X.boost hp (fun i=> Or.inr rfl) hx h.2.1.front
  obtain ⟨hx,HY,hU,hV⟩ := sepJ h.1 h.2.2.2 hp
  have he := h.basic.spot
  unfold fibQ at he; rw [show T⁻¹*T^2=T by ext1 i; dsimp; field_simp [(hc i).ne']] at he
  have hc' : T^2 ≤ rimEdge T μ*T := fun i=> by
    change T i^2 ≤ (T i+μ i^2*(T i^2)⁻¹)*T i
    rw [add_mul,sq (T i)]; have h := hc i; apply le_add_of_nonneg_right; positivity
  have hh : T⁻¹*μ^2 ≤ rimEdge T μ*T := fun i=> by
    change (T i)⁻¹*μ i^2 ≤ (T i+μ i^2*(T i^2)⁻¹)*T i
    rw [add_mul,show μ i^2*(T i^2)⁻¹*T i=(T i)⁻¹*μ i^2 by field_simp [(hc i).ne']]; exact le_add_of_nonneg_left (mul_nonneg (hc i).le (hc i).le)
  have hz := (hU : Fiesta T T _); let B i z := boltA X Z X.boost i z
  have hz1 : Fiesta T (rimEdge T μ*T) (boltB X Z X.boost-panL X W X.boost) :=
    ((HY.grows hc').plus ((h.2.1.spot.2).grows hh)).introp (fun i=> Eventually.of_forall fun x=> by simp only [Pi.sub_apply,boltB, atopY, Z, Film.plus,Pi.add_apply]; abel)
  have hz2 : Fiesta T (rimEdge T μ*T) (boltA X Z X.boost-panT X W X.boost) :=
    ((hx.grows hc').plus ((h.2.1.spot.1).grows hh)).introp (fun i=> Eventually.of_forall fun x=> by simp only [Pi.sub_apply,boltA, atopY, Z, Film.plus,Pi.add_apply]; abel)
  have ht : (T^2)⁻¹*T*(T^2)⁻¹*T=(T^2)⁻¹ := by ext1 i; dsimp; field_simp [(hc i).ne'];
  have hA := ((h2.pair hV).pair hP).pair hU
  have hf := hK.pair he.2
  have heq := (hf.pair ha).pairDif hU (hf.pairDif hP (hK.pairDif hV hD hz1) H) hz2
  rw [ht] at hA heq; exact ⟨hA,heq⟩
lemma haloControl (h : Fleet X T μ F G W r) (hx : T=flay ∘ X.lens) : ∃ A : ℝ,0≤A ∧ ∀ i, ‖flareY 2 (fun t=> (lowerJet X (atopY F G) i t).trace) - flareY 2 (fun t => (haloC X W i t).trace)‖ ≤ A*rimEdge T μ i/T i^4 := by
  obtain ⟨⟨A,hA,hp,hL⟩,hv⟩ := h.brass hx
  obtain ⟨B,hB,M⟩ := focus_bill hv h.2.2.2.lower
  refine ⟨B,hB,fun i=>?_⟩
  rw [← flare_dec (h.lacy i).2 (hL i|>.run.sides)]
  have ht : (fun t=> trace ((lowerJet X (atopY F G)-haloC X W) i t))= (fun t=> (lowerJet X (atopY F G) i t).trace) -(fun t=> (haloC X W i t).trace) := by ext1 t; simp
  rw [← ht]; exact (M i).trans_eq (by simp; ring)
end Fleet
end shoes
end YM.Stationary
end
