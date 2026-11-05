import YM.Next.UV_STRESS.Station
import YM.Next.UV_STRESS.Tiles


/-!
# Proving estimates at a station from point and replica regimes

Two precision regimes of **genuine finite root estimates** (analogue of
wbass in E). Consume a given nonbottom subfilter and already fixed S. Never
assume these estimates for S itself, nor need to decide that subfilter in
advance to ask for estimates. Get gradient bound by aligned tests at arbitrary
finer grids, then density (saves another equicontinuity estimate on a
changed Station).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Extraction.Difference Table Ward Climb Cells Lattice Wilson
open scoped Topology ContDiff BigOperators
variable {n : ℕ}

/-- weaker, Max norm gate. -/
def airy (n : ℕ) (s : ℝ) : Set (Points n) := {x | ∀ i j, i ≠ j → s < cubedist (x i) (x j)}
lemma airy_open (s : ℝ) : IsOpen (airy n s) := by
  rw [show airy n s = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i ≠ j,
    {x : Points n | s < cubedist (x i) (x j)} by ext; simp [airy]]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite
    fun _ => isOpen_lt continuous_const (by unfold cubedist; fun_prop)

def openFilm (n : ℕ) (s : ℝ) : Set (Points n) := {x| ∀ i j, i≠j → ∀ a, s < |Gaps.distances x i j a|}
lemma open_film (s : ℝ) : IsOpen (openFilm n s) := by
  rw [show openFilm n s = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i ≠ j,
    ⋂ a : Axis, {x : Points n | s < |Gaps.distances x i j a|} by ext; simp [openFilm]]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite
    fun _ => isOpen_iInter_of_finite fun a => isOpen_lt continuous_const (by fun_prop)

lemma open_fit (s : ℝ) (hs : 0≤s) : openFilm n s ⊆ generic n := by
  intro x hx a i j h; by_contra hu
  have hh := hs.trans_lt (hx i j hu a); change x i a=x j a at h
  simp [Gaps.distances,h] at hh

section leaf
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {m N p : ℕ}

lemma late_period {P : ℕ → Prop} (h : ∀ᶠ i in atTop, P i) : ∀ᶠ i in F.fuse,P i.2 := by
  rw [Extraction.Order.fused, Extraction.Order.late]
  exact (F.per.cofinal.eventually h).mono fun i hi => Eventually.of_forall fun _ => hi

abbrev Bud (C : Family G) (t : Caps n) := (i : Fin n) → C.book.Ref (t i)

def ripped {t : Caps n} (Y : Bud C t) (i : Fin n) : C.book.Token := ⟨t i, Y i⟩

theorem paid_point {t : Caps n} (v : ℕ×ℕ→Bud C t) {𝓛 : Filter (ℕ×ℕ)} [𝓛.NeBot]
    (Y : Bud C t) (hp : _root_.Filter.Tendsto v 𝓛 (𝓝 Y)) (h : 𝓛 ≤ F.fuse)
    (H : F.PointLimits C S) (k : ℕ) (x : Fin n → Cover) (hx : tag (C.S.a k) x ∈ generic _) :
    Tendsto (fun i : ℕ×ℕ => C.numeric i.1 i.2 (ripped (t:=t) (C:=C) (v i)) (location C.S k i.1 i.2 ∘ x))
      𝓛 (𝓝 (S.value t (tag (C.S.a k) x) Y)) := by
  let M (i : ℕ×ℕ) := C.ensemble t (location C.S k i.1 i.2 ∘ x)
  have he (u : Bud C t) : Tendsto (fun i => M i u) 𝓛 (𝓝 (S.value t (tag (C.S.a k) x) u)) := by
    have hz := Order.along (Cells.eventual_grid (k:=k) C F S H x hx (ripped (C:=C) (t:=t) u))
    exact hz.mono_left h
  change Tendsto (fun i => M i (v i)) _ _
  exact tendsto_multi (fun i => C.book.Ref (t i)) M (fun y => S.value t (tag (C.S.a k) x) y)
    he Y v (tendsto_pi_nhds.mp hp)

lemma zoom_at {S : Schedule} {k N p : ℕ} (h : k ≤ N) (x : Fin n → Cover) :
    location S k N p ∘ x = wrap (S.side N p) ∘ (pushSite S h ∘ x) := by
  ext1 i; change location S k N p (x i)=_
  rw [location, dif_pos h, Ratio.embed_wrap]; rfl
lemma scales_tag {S : Schedule} {k N} (h : k ≤ N) (x : Fin n → Cover) : tag (S.a N) (pushSite S h ∘ x)=tag (S.a k) x := by
  ext1 i; exact finer S h (x i)

def bulk {t : Caps n} (v : ℕ×ℕ → Bud C t) (F : Extraction.Order) (A : ℝ) (k : ℕ) : Prop :=
    ∀ i j, F.late fun N p => centeredBudget C (Extraction.Spin.token C.book (ripped (C:=C) (t:=t) (v (N,p)) i) j) A k N p

lemma ample {t : Caps n} (v : ℕ×ℕ → Bud C t) {A : ℝ} {k : ℕ} (hA : bulk (C:=C) (t:=t) v F A k) :
    ∀ᶠ i in F.fuse,Around.imageBudget (C:=C) (ripped (t:=t) (C:=C) (v i)) A k i.1 i.2 := by
  let W (u : Bud C t) i j := Extraction.Spin.token C.book (ripped (C:=C) (t:=t) u i) j
  have he : ∀ᶠ i in F.fuse, ∀ j l, centeredBudget C (W (v i) j l) A k i.1 i.2 :=
    eventually_all.mpr fun j => eventually_all.mpr fun l => hA j l
  have H : ∀ᶠ i in F.fuse, ∀ j l, Around.Fit (C:=C) (W 0 j l) k i.1 i.2 := eventually_all.mpr fun j => eventually_all.mpr fun l => by
    rw [Order.fused, Order.late]
    exact Eventually.of_forall fun p => (Around.fit (C:=C) (f:=F) (W 0 j l) k).mono fun i hi => hi _
  have hp (u : Bud C t) j l : (W u j l).1=t j := Extraction.Spin.stay ..
  filter_upwards [he,H,large_mesh F k] with i hi hh hs
  refine ⟨hs,fun j l => ⟨hi j l,?_⟩⟩
  have hz := hh j l
  change Around.Fit (C:=C) (W (v i) j l) k i.1 i.2
  unfold Around.Fit at *; rw [hp]; rwa [hp] at hz

/-- Crude even through projection ties (for S read). -/
theorem large_gate (H : C.Makes) (Hc : S.Smooth) (hS : F.PointLimits C S)
    (𝓛 : Filter (ℕ×ℕ)) [𝓛.NeBot] (h : 𝓛 ≤ F.fuse)
    {t : Caps n} (v : ℕ×ℕ→Bud C t) (Y : Bud C t) (hp : Tendsto v 𝓛 (𝓝 Y))
    {s A : ℝ} (hs : 0<s) (m k : ℕ) (hm : C.S.a m<s) (hv : m≤k)
    (hx : (n:ℝ)*(2*(3*C.S.a k)) < C.S.a m) (hA : bulk (C:=C) (t:=t) v F A k) :
    ∀ x∈airy n s, ‖S.value t x Y‖ ≤ A^n := by
  let W (i) := ripped (t:=t) (C:=C) (v i)
  have hl (d) (x : Fin n→Cover) (hu : tag (C.S.a d) x∈generic _) (hg : tag (C.S.a d) x∈airy n s) :
      ‖S.value t (tag (C.S.a d) x) Y‖ ≤ A^n := by
    refine le_of_tendsto (paid_point v Y hp h hS d x hu).norm (Eventually.filter_mono h ?_)
    let y := tag (C.S.a d) x
    have he : ∀ᶠ p : ℕ in atTop,Gaps.someFine C.S p s y := by
      filter_upwards [Gaps.expand_equivalent C.S (K:={y}) isCompact_singleton] with p hy i j hij
      obtain ⟨a,ha⟩ : ∃ a : Axis, s ≤ |Gaps.distances y i j a| := by
        by_contra! he
        have hl : cubedist (y i) (y j) < s := by
          unfold cubedist; refine (dist_pi_lt_iff hs).mpr fun a => ?_; rw [dist_comm,Real.dist_eq]; exact he a
        exact hl.not_gt (hg i j hij)
      exact ⟨a,fun u => ha.trans (hy y (mem_singleton _) i j a u)⟩
    filter_upwards [late_period (F:=F) he, large_mesh F d, ample v hA] with i hQ hd he
    change ‖C.numeric _ _ (W i) _‖ ≤ _
    rw [zoom_at hd]
    exact Around.fits_budget H (W i) {y} s (fun _ hx => mem_singleton_iff.mp hx |>.symm ▸ hQ) A hm hv hx he
      (pushSite C.S hd ∘ x) (scales_tag hd x |>.symm ▸ mem_singleton _)
  have he (x) (hx : x∈airy n s) : ContinuousAt (fun y => S.value t y Y) x := by
    have hc : x∈conf n := spaced_conf hs fun i j hij => (hx i j hij).le
    exact ((S.smooth_read Hc (ripped (t:=t) (C:=C) Y)).continuousOn x hc).continuousAt ((conf_open n).mem_nhds hc)
  have hQ (x) (hx : x ∈ airy n s) (hh : x ∈ generic n) : ‖S.value t x Y‖ ≤ A^n := by
    have ht := chosen (S:=C.S) x
    apply le_of_tendsto (((he x hx).tendsto.comp ht).norm)
    filter_upwards [ht.eventually ((airy_open s).mem_nhds hx),ht.eventually ((genericOpen _).mem_nhds hh)] with i hi he using
      hl i (address (C.S.a i) x) he hi
  intro x H
  haveI := mem_closure_iff_nhdsWithin_neBot.mp (Dash.full n x)
  apply le_of_tendsto ((he x H).norm.continuousWithinAt (s:=generic n)).tendsto
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((airy_open s).mem_nhds H)] with y hy hg using hQ y hg hy
end leaf

section slope
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book}

lemma turned_tags {m : ℕ} (Q : Schedule) (x : Fin n → Cover) (k : Fin n) (a : Axis) :
    tag (Q.a m) (advance x k a 1) = tag (Q.a m) x + Q.a m • Points.direction k a := by
  ext i j
  simp only [tag,points_apply,PiLp.add_apply,PiLp.smul_apply, Points.direction, WithLp.ofLp_toLp,advance]
  by_cases h : i=k
  · subst i; by_cases h : j=a
    · subst a; simp [mul_add]
    simp [h]
  simp [h]

lemma advance_deeper (Q : Schedule) {j N p : ℕ} (h : j≤N) (x : Fin n → Cover) (k a) :
    pushSite Q h ∘ advance x k a 1 = advance (pushSite Q h ∘ x) k a (Cells.span Q h p) := by
  ext1 i; by_cases he : i=k
  · subst i; simp only [Function.comp_apply,advance, update_self,pushSite, one_smul, smul_add]; rfl
  simp [advance, he]

def generous {t : Caps n} (v : ℕ×ℕ → Bud C t) (F : Extraction.Order) (A : ℝ) (k : ℕ) : Prop :=
    ∀ᶠ u in F.fuse,Difference.Permit (C:=C) (ripped (t:=t) (C:=C) (v u)) A k u.1 u.2

private lemma slope_paid (H : C.Makes) (hS : F.PointLimits C S) {t : Caps (n+1)} (v : ℕ×ℕ→Bud C t)
    (𝓛 : Filter (ℕ×ℕ)) [𝓛.NeBot] (h : 𝓛≤F.fuse) (Y : Bud C t) (hp : Tendsto v 𝓛 (𝓝 Y))
    (D j : ℕ) (A r : ℝ) (hA : 0 ≤ A) (hr : 0 < r) (hg : C.S.a j ≤ r)
    (hq : generous (C:=C) (t:=t) v F A D) (hy : C.S.a D < r) (x : Fin (n+1) → Cover) (k a)
    (hx : tag (C.S.a j) x ∈ openFilm _ (4*r))
    (he : tag (C.S.a j) (advance x k a 1) ∈ generic _) :
    ‖S.value t (tag (C.S.a j) (advance x k a 1)) Y-S.value t (tag (C.S.a j) x) Y‖ ≤ (A^(n+1)/r)*C.S.a j := by
  rw [← dist_eq_norm]
  have hw := open_fit _ (show 0 ≤ 4*r by positivity) hx
  refine le_of_tendsto ((paid_point v Y hp h hS j (advance x k a 1) he).dist (paid_point v Y hp h hS j x hw))
    (Eventually.filter_mono h ?_)
  let W := tag (C.S.a j) x
  have hz : ∀ᶠ p in atTop, Gaps.allFine C.S p (4*r) W := by
    filter_upwards [Gaps.expand_equivalent C.S (K:={W}) isCompact_singleton] with p hh l i hl a u
    exact (hx l i hl a).le.trans (hh W (mem_singleton _) l i a u)
  unfold generous at hq
  filter_upwards [late_period (F:=F) hz, large_mesh F D, large_mesh F j,hq] with u ht hP hN hQ
  let g := ripped (C:=C) (t:=t) (v u)
  change dist (C.numeric _ _ g _) (C.numeric _ _ g _) ≤ _
  rw [zoom_at hN, zoom_at hN, advance_deeper (p:=u.2)]
  let l := Cells.span C.S hN u.2
  let b := pushSite C.S hN ∘ x
  have hd : dist (tag (C.S.a u.1) (advance b k a l)) (tag (C.S.a u.1) b)=C.S.a j :=
    (Difference.extent _ _ _ _ _ (C.S.a_pos _)).trans (C.S.embeds_scale (C.S.toDepth hN u.2))
  have ht := stepTotal H g hA hr {W} u.2 u.1 D hP hQ (singleton_subset_iff.mpr ht : {W} ⊆ {y| Gaps.allFine C.S u.2 (4*r) y})
    hy k a l b (mem_singleton_iff.mpr (scales_tag hN x)) (hd ▸ hg)
  rw [hd] at ht; exact ht

theorem slope_gate (H : C.Makes) (hS : F.PointLimits C S) (hs : S.Smooth) {t : Caps n} (v : ℕ×ℕ→Bud C t)
    (𝓛 : Filter (ℕ×ℕ)) [𝓛.NeBot] (h : 𝓛≤F.fuse) (Y : Bud C t) (hp : Tendsto v 𝓛 (𝓝 Y))
    (D : ℕ) (A r : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hq : generous (C:=C) (t:=t) v F A D) (hy : C.S.a D < r) (k : Fin n) (a : Axis) :
    let g x := S.value t x Y
    ∀ x∈openFilm _ (4*r), ‖fderiv ℝ g x (Points.direction k a)‖ ≤ A^n/r := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
    intro g
    let e := Points.direction k a
    have ht (x) (hx : x∈openFilm _ (4*r)) : ContDiffAt ℝ ∞ g x := by
      have hc := generic_conf _ (open_fit _ (show 0 ≤ 4*r by positivity) hx)
      exact ((S.smooth_read hs (ripped (t:=t) (C:=C) Y)) x hc).contDiffAt ((conf_open _).mem_nhds hc)
    have he (j x) (hh : tag (C.S.a j) x ∈ openFilm (n+1) (4*r)) :
        ‖fderiv ℝ g (tag (C.S.a j) x) e‖ ≤ A^(n+1)/r := by
      let X := tag (C.S.a j) x
      have hE := ((ht X hh).differentiableAt (by simp)).hasFDerivAt.hasLineDerivAt e
      have hR : Tendsto C.S.a atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨C.S.shrinks,Eventually.of_forall fun i => (C.S.a_pos _).ne'⟩
      apply le_of_tendsto ((hE.tendsto_slope_zero.comp hR).norm)
      have hz : Tendsto (fun i => X+C.S.a i • e) atTop (𝓝 X) := by simpa using ((C.S.shrinks.smul_const e).const_add X)
      filter_upwards [hz.eventually ((open_film (4*r)).mem_nhds hh), C.S.shrinks.eventually (ge_mem_nhds hr),
        eventually_ge_atTop j] with i hi hv hk
      let U := pushSite C.S hk ∘ x
      have hg : tag (C.S.a i) U=X := scales_tag hk x
      have Hq : X+C.S.a i • e = tag (C.S.a i) (advance U k a 1) := by rw [turned_tags,hg]
      have hu : ‖g (X+C.S.a i • e)-g X‖ ≤ A^(n+1)/r*C.S.a i := by
        rw [Hq,← hg]; exact slope_paid H hS v 𝓛 h Y hp D i A r hA hr hv hq hy U k a (hg ▸ hh)
          (open_fit _ (by positivity : 0 ≤ 4*r) (Hq ▸ hi))
      change ‖(C.S.a i)⁻¹ • (g (X+C.S.a i • e)-g X)‖ ≤ _
      rw [norm_smul,norm_inv,Real.norm_eq_abs,abs_of_pos (C.S.a_pos _)]
      apply (mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr (C.S.a_pos _).le)).trans_eq
      rw [mul_comm,mul_assoc,mul_inv_cancel₀ (C.S.a_pos _).ne',mul_one]
    intro x hx
    have Hh : ContinuousAt (fun x => fderiv ℝ g x e) x := (ContDiffAt.continuousAt_fderiv (ht x hx) (by simp)).clm_apply continuousAt_const
    have hE := chosen (S:=C.S) x
    exact le_of_tendsto ((Hh.tendsto.comp hE).norm) ((hE.eventually ((open_film (4*r)).mem_nhds hx)).mono (fun i hi => he _ _ hi))
end slope
end YM.Next.UVStress
