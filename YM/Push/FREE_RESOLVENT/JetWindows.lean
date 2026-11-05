import YM.Bid.Tar
import YM.Org.Theatre
import YM.Push.FREE_RESOLVENT.Differentiated
import YM.Push.FREE_RESOLVENT.Windows


/-!
# Cut window and discrepancy estimates with all polarizations

Reserve a strictly positive width `room` before application (`k`, s, M, r).
At FOUR-dimensional use set V from torus volume paid at that rate.
Works both for  derivative norm and for coefficient-position prices via
other Move. Explicit σ shrinks also in nonlinear products (Leibniz).

Assuming only precision & gap at actual evaluation. No inference of them for
general flagged A from this lemma. Use geometry held fixed. u arc integrations
have not been performed but the price on discrepancy keeps ≥ quadratic decay
(including order zero!).
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix Filter Function Mark TestD Window
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {τ X E ι κ μ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

namespace TestD
variable {C : Mark τ X} {D : Cost X} {v : τ → E} {a : ι → X} {A B : E → Matrix ι ι ℝ} {k n : ℕ}
variable {s M r d U γ V u ε μ η R W : ℝ} {x : E}

def room (s M r : ℝ) (k : ℕ) := safeRate s M r/(32*(k+1:ℕ)^2 : ℝ)

/-- Split one rate to pay inverse powers of motion and counting. -/
lemma room_grid (hs : 0 < s) (hm : 0 ≤ M) (hr : 0 < r) (k : ℕ) :
    let γ := room s M r k
    let θ := safeRate s M r/2
    0 < γ ∧ progress θ γ k k ≤ s ∧ 4*(k+1:ℕ)*γ ≤ progress θ γ k k ∧ γ ≤ safeRate s M r-θ ∧ θ ≤ s := by
  intro γ θ
  have hh : 0 < safeRate s M r := rate_pos hs hm hr
  have hl : 0 < γ := div_pos hh (by positivity)
  have hw : θ ≤ s := le_trans (half_lt_self hh).le (rate_lt hs).le
  have he : γ * (32*(k+1:ℕ)^2:ℝ)=θ*2 := by rw [show θ*2=safeRate s M r from div_mul_cancel₀ _ (by norm_num)]; exact div_mul_cancel₀ _ (by positivity)
  have hk : 0 ≤ (k:ℝ) := by positivity
  have ht : γ ≤ θ := by push_cast at he; nlinarith only [he,hl,hk,mul_nonneg hl.le hk,mul_nonneg hl.le (sq_nonneg (k:ℝ))]
  refine ⟨hl,(le_trans ((progress_anti _ hl.le _ (Nat.zero_le k)).trans_eq (progress_top ..)) hw),?_, ?_, hw⟩
  · unfold progress; push_cast at *; nlinarith only [he,hl,mul_nonneg hk hl.le,mul_nonneg hl.le (sq_nonneg (k:ℝ))]
  unfold θ at *; linarith

omit [DecidableEq ι] in
lemma volume_down (hV : D.Volume a γ V) (h : γ ≤ η) : D.Volume a η V := by
  constructor; intro i
  refine (Finset.sum_le_sum (g:=fun j => D.weight (-γ) i (a j)) fun j _ => ?_).trans (hV.bound i)
  exact D.weight_mono (neg_le_neg h) ..

lemma Knew.localUnit (hw : Knew C D a v x k s M r ε A) (hu : 0 ≤ u) (hr : 0 < r) :
    Neat A u x := ((hw.gap.shift u).unit_det (by positivity))
lemma Knew.sees (hw : Knew C D a v x k s M r ε A) (hu : 0 ≤ u) (hr : 0 < r) :
    ContDiffAt ℝ k (action A u) x := action_smooth (hw.localUnit hu hr) hw.smooth
omit [DecidableEq ι] in
lemma Knew.bundle (hw : Knew C D a v x k s M r ε A) (hm : 0 ≤ M) (he : ε ≤ 1) :
    Bundle v C D a a A x k s M := by
  refine ⟨hw.smooth,fun l h => ?_⟩
  by_cases h' : l=[]
  · subst l; rw [zeroth]; exact Bill.origin C hw.schur
  exact (hw.jets l h' h).mono le_rfl (mul_le_of_le_one_right hm he)

-- Package common price at volume granularity `d`; keep U param, choose δ=d.
structure Price (s M r d U V ε : ℝ) (k : ℕ) : Prop where
  r0 : 0 < r
  m : 0 ≤ M
  s0 : 0 < s
  height : d=room s M r k
  one : 1 ≤ U
  vol : 0 ≤ V
  low : 0 ≤ ε
  high : ε ≤ 1

namespace Price
lemma pos (p : Price s M r d U V ε k) : 0 < d := p.height ▸ (room_grid p.s0 p.m p.r0 k).1
lemma roomTop (p : Price s M r d U V ε k) : progress (safeRate s M r/2) d k k ≤ s := p.height ▸ (room_grid p.s0 p.m p.r0 k).2.1
lemma roomEnough (p : Price s M r d U V ε k) : 4*(k+1:ℕ)*d ≤ progress (safeRate s M r/2) d k k :=
  p.height ▸ (room_grid p.s0 p.m p.r0 k).2.2.1
lemma roomAbs (p : Price s M r d U V ε k) : d ≤ safeRate s M r-safeRate s M r/2 :=
  p.height ▸ (room_grid p.s0 p.m p.r0 k).2.2.2.1
lemma meter_abs (p : Price s M r d U V ε k) : 0 ≤ meter k k M U (rise V r) :=
  meter_nn _ _ p.m (zero_le_one.trans p.one) (rise_nn p.vol p.r0)
end Price

theorem Knew.cost (hw : Knew C D a v x k s M r ε A) (l : List τ) (hl : l.length ≤ k)
    (p : Price s M r d U V ε k) (hu : 0 ≤ u) (h : C.Move D d U) (hy : D.Volume a d V) :
    Bill C D a a l (4*(k+1:ℕ)*d) (charges l.length ε (meter k k M U (rise V r)) (drain u)) (jet v (action A u) l x) := by
  have ht := p.pos
  exact (measured (le_trans (by positivity) p.roomEnough) h ht.le p.one hw
    p.m p.vol p.s0 (volume_down hy p.roomAbs) (room_grid p.s0 p.m p.r0 k).2.2.2.2 hu p.r0 p.low p.high k le_rfl l hl).mono p.roomEnough le_rfl

theorem Knew.volume_price (hw : Knew C D a v x k s M r ε A) (p : Price s M r d U V ε k)
    (hu : 0 ≤ u) (h : C.Move D d U) (hy : D.Volume a d V) :
    Bundle v C D a a (action A u) x k (4*(k+1:ℕ)*d) (meter k k M U (rise V r)*drain u) :=
  ⟨hw.sees hu p.r0, fun l hl => (hw.cost l hl p hu h hy).mono le_rfl (charges_lax _ p.high (drain_pos hu).le (drain_le hu) p.meter_abs)⟩

-- use A-B jet closeness. Keeps integrable shift bound.
lemma Knew.change (hA : Knew C D a v x k s M r ε A) (hB : Knew C D a v x k s M r ε B) (p : Price s M r d U V ε k)
    (hu : 0 ≤ u) (h : C.Move D d U) (hy : D.Volume a d V) (hh : 0 ≤ W)
    (hp : Bundle v C D a a (A-B) x k ((2*(k+1:ℕ)+1)*d) W) :
    let C0 := meter k k M U (rise V r)*drain u
    Bundle v C D a a (action B u-action A u) x k d (tagPrice U k (tagPrice U k C0 W) C0) := by
  intro C0
  have hv : 0 ≤ U := zero_le_one.trans p.one
  have h1 : 0 ≤ C0 := mul_nonneg p.meter_abs (drain_pos hu).le
  have h2 : 0 ≤ tagPrice U k C0 W := by unfold tagPrice; positivity
  have hL := p.pos
  have hk : 0 ≤ (k:ℝ) := by positivity
  apply Bundle.glue
    (B := action B u-action A u) (A := fun y => (action B u y * (A-B) y)*action A u y) _ (by
      filter_upwards [germ_valid (hA.localUnit hu p.r0) hA.smooth.continuousAt,
        germ_valid (hB.localUnit hu p.r0) hB.smooth.continuousAt] with y hv hw
      exact (resolve_diff (A:=A y) (B:=B y) (u:=u) hv hw).symm)
  have he : (2*(k+1:ℕ)+1)*d ≤ 4*(k+1:ℕ)*d := by push_cast; nlinarith
  have hw := (hB.volume_price p hu h hy).mono he le_rfl
  let c := (k+1:ℕ)*d
  have hc : c+k*d ≤ (2*(k+1:ℕ)+1)*d := by unfold c; push_cast; nlinarith
  have hb := hw.multiply hp h hL.le p.one h1 hh (by unfold c; positivity) hc
  have hj : c ≤ (2*(k+1:ℕ)+1)*d := le_trans (by unfold c; nlinarith) hc
  exact hb.multiply ((hA.volume_price p hu h hy).mono (hj.trans he) le_rfl) h hL.le p.one h2 h1 hL.le (by unfold c; push_cast; nlinarith)

section compression
variable {κ : Type*} [Fintype κ] {e : κ → ι}
-- compress even before invertibility

def limitTo (A : E → Matrix ι ι ℝ) (e : κ → ι) (x : E) := (A x).submatrix e e

def selectL (e : κ → ι) : Matrix ι ι ℝ →L[ℝ] Matrix κ κ ℝ := LinearMap.toContinuousLinearMap
  ({ toFun := fun A : Matrix ι ι ℝ => A.submatrix e e, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
omit [DecidableEq ι] in
lemma compressed (e : κ → ι) (l : List τ) (h : ContDiffAt ℝ l.length A x) :
    jet v (limitTo A e) l x = (jet v A l x).submatrix e e := jet_linear v l (selectL e) h
omit [DecidableEq ι] in
lemma shrink (hw : Knew C D a v x k s M r ε A) (he : Function.Injective e) :
    Knew C D (a ∘ e) v x k s M r ε (limitTo A e) :=
  ⟨(selectL e).contDiff.contDiffAt.comp x hw.smooth, hw.gap.submatrix _ he, hw.schur.submatrix he he,
    fun l h' h => by rw [compressed _ _ (smooth_of_le hw.smooth h)]; exact (hw.jets l h' h).submatrix he he⟩
end compression

section windows
variable {I : ι → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
variable {T : Survey I}

/-- Apply Pi_u to precision germ with *fixed* windows. -/
def glimpse (T : Survey I) (A : E → Matrix ι ι ℝ) (u : ℝ) := fun x => T.inspect (A x) u

-- less magical continuity for rectangular too
section rect
variable {κ : Type*} [Fintype κ]
omit [DecidableEq ι] in
lemma rectangle_smooth {F : E → Matrix ι κ ℝ} (h : ∀ i j, ContDiffAt ℝ k (fun y => F y i j) x) : ContDiffAt ℝ k F x := by
  let L : (ι → κ → ℝ) ≃L[ℝ] Matrix ι κ ℝ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  apply L.contDiff.contDiffAt.comp x (show ContDiffAt ℝ k (fun x i j => F x i j) x from
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (h i))
end rect

lemma glimpse_smooth (hw : Knew C D a v x k s M r ε A) (T : Survey I) (hu : 0 ≤ u) (hr : 0 < r) : ContDiffAt ℝ k (glimpse T A u) x := by
  apply rectangle_smooth; intro i j
  by_cases hi : i ∈ Set.range (T.loc j)
  · obtain ⟨i,rfl⟩ := hi
    let e := T.loc j; let t := T.root j
    have he : (fun y => glimpse T A u y (e i) j) = fun y => action (limitTo A e) u y i t :=
      funext fun y => Pane.local_entry (A y) u (e : I j → ι) e.injective t i
    change ContDiffAt ℝ k _ _; rw [he]
    exact (evaluate i t).contDiff.contDiffAt.comp x ((shrink hw e.injective).sees hu hr)
  have hh : (fun y => glimpse T A u y i j) = fun _ => 0 := funext fun y => Pane.unused (A y) u (T.loc j) (T.root j) i hi
  rw [hh]; exact contDiffAt_const

lemma glimpse_rates (hw : Knew C D a v x k s M r ε A) (p : Price s M r d U V ε k) (T : Survey I)
    (hu : 0 ≤ u) (h : C.Move D d U) (hy : D.Volume a d V) (l : List τ) (hl : l.length ≤ k) :
    Bill C D a a l (3*(k+1:ℕ)*d) (V*charges l.length ε (meter k k M U (rise V r)) (drain u))
      (jet v (glimpse T A u) l x) := by
  let B := charges l.length ε (meter k k M U (rise V r)) (drain u)
  have hb : 0 ≤ B := charges_nn _ p.low p.meter_abs (drain_pos hu).le
  let G := jet v (glimpse T A u) l x
  let η := 4*(k+1:ℕ)*d
  have hf (i j) : C.pay l (a i) * (D.weight η (a i) (a j) * |G i j|) ≤ B ∧
      C.pay l (a j)*(D.weight η (a j) (a i) * |G i j|) ≤ B := by
    unfold G; rw [← TestD.entry v l (smooth_of_le (glimpse_smooth hw T hu p.r0) hl)]
    by_cases hi : i ∈ Set.range (T.loc j)
    · obtain ⟨m,rfl⟩ := hi
      let e := T.loc j; let t := T.root j
      have he : (fun y => glimpse T A u y (T.loc j m) j) = fun y => action (limitTo A e) u y m t :=
        funext fun y => Pane.local_entry (A y) u (e : I j → ι) e.injective t m
      rw [he, TestD.entry v l (smooth_of_le ((shrink hw e.injective).sees hu p.r0) hl)]
      have hh := (shrink hw e.injective).cost l hl p hu h (hy.comp e.injective)
      have ht : a j=(a ∘ e) t := (congr_arg a (T.atRoot j)).symm
      rw [ht]; exact ⟨hh.row.entry _ _, hh.col.entry _ _⟩
    have he : (fun y => glimpse T A u y i j) = fun _ => 0 := funext fun y => Pane.unused (A y) u (T.loc j) (T.root j) i hi
    have hh : jet v (fun _ => (0:ℝ)) l x=0 := by
      by_cases h : l=[]; · subst l; rw [zeroth]
      exact jet_const v l h 0 x
    rw [he,hh]; simp only [abs_zero,mul_zero]; exact ⟨hb,hb⟩
  have ht : d ≤ η-(3*(k+1:ℕ)*d) := by unfold η; have := p.pos; push_cast; nlinarith only [this,mul_nonneg this.le (show 0 ≤ (k:ℝ) by positivity)]
  exact Bill.of_entry (volume_down hy ht) (volume_down hy ht) hb (fun i j => (hf i j).1) fun i j => (hf i j).2

def outsideL (T : Survey I) : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ := LinearMap.toContinuousLinearMap ({
    toFun := T.outside
    map_add' F H := by ext i j; simp only [Matrix.add_apply,T.outside_apply]; split <;> simp
    map_smul' r F := by ext i j; simp only [RingHom.id_apply,Matrix.smul_apply,T.outside_apply]; split <;> simp } : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)

def deficit (T : Survey I) (A : E → Matrix ι ι ℝ) (u : ℝ) := fun x => T.error (A x) u

lemma Knew.miss {T : Survey I} (hA : Knew C D a v x k s M r ε A) (p : Price s M r d U V ε k)
    (hu : 0 ≤ u) (h : C.Move D d U) (hy : D.Volume a d V) (hh : T.Near D a R) :
    let C0 := V*(meter k k M U (rise V r)*drain u)
    Bundle v C D a a (deficit T A u) x k ((k+1:ℕ)*d) (Real.exp (-(k+1:ℕ)*d*R)*tagPrice U k M C0) := by
  classical
  intro C0
  have h2 : Bundle v C D a a (glimpse T A u) x k (3*(k+1:ℕ)*d) C0 :=
    ⟨glimpse_smooth hA _ hu p.r0, fun l hl => (glimpse_rates hA p T hu h hy l hl).mono le_rfl
      (mul_le_mul_of_nonneg_left (charges_lax _ p.high (drain_pos hu).le (drain_le hu) p.meter_abs) p.vol)⟩
  have hn := p.pos
  have hk : 0 ≤ (k:ℝ) := by positivity
  let t : ℝ := (k+1:ℕ)*d
  have ht : 0 ≤ t := by unfold t; positivity
  have he : 3*t ≤ 4*(k+1:ℕ)*d := by rw [mul_assoc (4:ℝ)]; exact mul_le_mul_of_nonneg_right (by norm_num) ht
  have h3 : ↑(k+1:ℕ)*3*d=3*t := by unfold t; ring
  have hp := ((hA.bundle p.m p.high).mono
    (le_trans (show 3*(k+1:ℕ)*d ≤ _ from by rw [mul_comm (3:ℝ), h3]; exact he) (p.roomEnough.trans p.roomTop)) le_rfl).multiply h2 h hn.le p.one p.m
    (show 0 ≤ C0 from mul_nonneg p.vol (mul_nonneg p.meter_abs (drain_pos hu).le)) (γ:=2*t) (by positivity) (by unfold t; push_cast; nlinarith only [hn,mul_nonneg hk hn.le])
  let F y := A y * glimpse T A u y
  apply Bundle.glue (A:=fun y => T.outside (F y))
  · constructor
    · exact (outsideL T).contDiff.contDiffAt.comp x hp.smooth
    intro l hl
    erw [show (fun y => T.outside (F y)) = fun y => outsideL T (F y) from rfl,
      jet_linear v l (outsideL T) (A:=F) (smooth_of_le hp.smooth hl)]
    have hT := hp.bound l hl
    have hM (i j) : T.outside (jet v F l x) i j ≠ 0 → R ≤ D.d (a i) (a j) := by
      rw [T.outside_apply]; split; · tauto
      rename_i H; exact fun _ => (hh j i H).trans_eq (D.comm ..)
    have hB : Bill C D a a l t (Real.exp (-(2*t-t)*R)*tagPrice U k M C0) (outsideL T (jet v F l x)) :=
      (show Bill C D a a l _ _ (jet v F l x) from hT).far R (by linarith) hM (fun i j => by
        change |T.outside (jet v F l x) i j| ≤ _
        rw [T.outside_apply]; split <;> simp)
    rw [show -(2*t-t)*R= -(k+1:ℕ)*d*R by unfold t; push_cast; ring] at hB; exact hB
  let H (i : ι) := limitTo A (T.loc i)
  have hM (i : ι) : ∀ᶠ t in 𝓝 x, Neat (H i) u t :=
    germ_valid ((shrink hA (T.loc i).injective).localUnit hu p.r0) (shrink hA (T.loc i).injective).smooth.continuousAt
  filter_upwards [eventually_all.mpr hM] with y hy
  exact (T.residual (A y) u (hy : _)).symm

lemma Knew.discrepancy {T : Survey I} (hA : Knew C D a v x k s M r ε A) (p : Price s M r d U V ε k)
    (hu : 0 ≤ u) (h : C.Move D d U) (hy : D.Volume a d V) (hh : T.Near D a R) :
    let C0 := meter k k M U (rise V r)*drain u
    Bundle v C D a a (glimpse T A u-action A u) x k d
      (tagPrice U k C0 (Real.exp (-(k+1:ℕ)*d*R)*tagPrice U k M (V*C0))) := by
  intro C0
  have hp := hA.miss p hu h hy hh
  have he : 0 ≤ C0 := mul_nonneg p.meter_abs (drain_pos hu).le
  have hL := p.pos
  have H : (k+1:ℕ)*d ≤ 4*(k+1:ℕ)*d := by
    rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) (by norm_num)
  apply (((hA.volume_price p hu h hy).mono H le_rfl).multiply hp h p.pos.le p.one he (by
      unfold tagPrice
      apply mul_nonneg (Real.exp_pos _).le
      have := p.vol; have := p.m; have h' := lt_of_lt_of_le zero_lt_one p.one; positivity)
      hL.le (by push_cast; nlinarith)).glue
  filter_upwards [germ_valid (hA.localUnit hu p.r0) hA.smooth.continuousAt] with y hy
  exact (T.replacement (A y) u hy).symm
end windows
end TestD
end YM.FreeResolvent
