import YM.Next.UV_STRESS.Glide
import YM.UVNext.UV_STATION_TRANSFER.Lipschitz


set_option warningAsError false

/-!
# Two cutoff regimes, directly on the sites of the smear

Pricing in Wheel.Spots suffices even for direct
ordered-tail comparison on the *cutoff* (don't ask for S yet).

Uniform in
all placements at fixed wheel k.

Only the later Riemann step needs to
stake its cutoff threshold on a test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer
open Function Set Filter MeasureTheory Metric Analysis Extraction
open Extraction.Difference Lattice Wilson Cells Climb Ward Table Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {D n : ℕ} {t : Caps n}

/-- Cutoff sites in rescaled `X` units. Cover lifts arbitrary. -/
def fine (X : Wheel C D) (N : ℕ) (u : positions n) := tag (C.S.a N / X.r) u

lemma physical_tag (X : Wheel C D) (N : ℕ) (u : positions n) :
    X.r • fine X N u = tag (C.S.a N) u := by
  ext i a; change X.r*(C.S.a N / X.r * _) = _
  rw [← mul_assoc, mul_div_cancel₀ _ X.rad.ne']; rfl

/-- Current coefficients (no cutoff extraction across different scales). -/
def revenue (X : Wheel C D) (h : ∀ i,t i ≤ D) (w : Ribbon (Bel C.book) t)
    (N p : ℕ) (u : positions n) := lifted C N p (ripped (t:=t) (C:=C) (X.tones h w (N,p))) u

-- Finite detector positions at any fixed station, incl n=0.
lemma bounded_placements {r R : ℝ} (hr : 0 < r) :
    ∃ L : ℕ, ∀ x : positions n, ‖tag r x‖ ≤ R → ∀ i, x i ∈ box L := by
  obtain ⟨L,hL⟩ := exists_nat_gt (R/r)
  refine ⟨L,fun x hx i => ?_⟩
  have he (j : Axis) : |r*(x i j:ℝ)| ≤ R := ((show ‖tag r x i j‖ ≤ _ from PiLp.norm_apply_le (tag r x i) j).trans
    ((PiLp.norm_apply_le (tag r x) i).trans hx))
  have hq (j : Axis) : ((x i j).natAbs : ℝ) < L := by
    specialize he j; rw [abs_mul,abs_of_pos hr] at he
    have hi := ((le_div_iff₀' hr).mpr he).trans_lt hL
    rw [← show (((↑(x i j).natAbs:ℤ):ℝ))=_ from Int.cast_natCast _, Int.natCast_natAbs, Int.cast_abs]; exact hi
  rw [box_test]; constructor
  all_goals intro j; have hi : (x i j).natAbs < L := by exact_mod_cast hq j
  all_goals omega

/-- Use `Wheel.inspection` at ALL the wheel-aligned positions needed for
this fixed station's interpolation, one common cutoff threshold. -/
lemma aligned_price (X : Wheel C D) {e R : ℝ} {w : Ribbon (Bel C.book) t} {h}
    (hi : X.inspection F e (Scaling.window R n) h w) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a : ℕ × ℕ in F.fuse, ∀ (x : positions n), tag X.spacing x∈Scaling.window R n → tag X.spacing x∈generic n →
      ‖C.numeric a.1 a.2 (ripped (t:=t) (C:=C) (X.tones h w a)) (location C.S X.grid a.1 a.2 ∘ x) -
         disc (hang t w) (tag X.spacing x)‖ ≤ e+η := by
  obtain ⟨L,hL⟩ := bounded_placements (n:=n) (R:=R) X.space
  let z (x : Fin n → ↥(box L)) : positions n := fun i => x i
  let Q (a : ℕ×ℕ) (x : positions n) := tag X.spacing x∈Scaling.window R n → tag X.spacing x∈generic n →
      ‖C.numeric a.1 a.2 (ripped (t:=t) (C:=C) (X.tones h w a)) (location C.S X.grid a.1 a.2 ∘ x) -
         disc (hang t w) (tag X.spacing x)‖ ≤ e+η
  have ht : ∀ᶠ a in F.fuse, ∀ x : Fin n → ↥(box L), Q a (z x) := eventually_all.mpr fun x => by
    by_cases hw : tag X.spacing (z x)∈Scaling.window R n ∧ tag X.spacing (z x)∈generic n
    · have hy : ∀ᶠ a : ℕ×ℕ in F.fuse, ‖C.numeric a.1 a.2 (ripped (t:=t) (C:=C) (X.tones h w a))
          (location C.S X.grid a.1 a.2 ∘ z x) - disc (hang t w) (tag X.spacing (z x))‖ ≤ _ :=
        hi _ hw.1 hw.2 η hη
      exact hy.mono fun a hi _ _ => hi
    exact Eventually.of_forall fun a h₁ h₂ => (hw ⟨h₁,h₂⟩).elim
  filter_upwards [ht] with a ha x hx hy
  exact ha (fun i => ⟨x i, hL x hx.2 i⟩) hx hy

lemma cutoff_big (X : Wheel C D) (P : C.Makes) {R e A B : ℝ} (hR : 0<R)
    {w : Ribbon (Bel C.book) t} {h} (hx : X.Spots F R e A B h w) :
    ∀ᶠ i : ℕ×ℕ in F.fuse, ∀ (u : positions n), fine X i.1 u ∈ Scaling.window R n →
      ‖revenue X h w i.1 i.2 u‖ ≤ A^n := by
  obtain ⟨m,k,hg,hm,hk,ha⟩ := hx.crude
  let W := Scaling.window R n
  let M : Set (Points n) := (fun x => X.r • x) '' W
  let s : ℝ := X.r / (2*R)
  have hM : IsCompact M := (window_closed ..).image (by fun_prop)
  have hs : 0<s := div_pos X.rad (by positivity)
  have ht (z : Points n) (hz : z∈M) : z∈airy n s := by
    obtain ⟨y,h,rfl⟩ := hz; exact centered_in hR X.rad y h
  filter_upwards [ample _ ha, late_period (F:=F) (Gaps.expand_equivalent C.S hM)] with i hb hi u hu
  have he : tag (C.S.a i.1) u ∈ M := ⟨fine X i.1 u,hu,physical_tag X ..⟩
  refine Around.fits_budget P _ M s ?_ A hg hm hk hb u he
  intro x hx a b hab
  obtain ⟨j,hj⟩ : ∃ j : Axis, s≤|Gaps.distances x a b j| := by
    by_contra! h
    have hh : cubedist (x a) (x b) < s := by
      unfold cubedist; refine (dist_pi_lt_iff hs).mpr fun j => ?_; rw [dist_comm,Real.dist_eq]; exact h j
    exact hh.not_gt (ht _ hx a b hab)
  exact ⟨j,fun z => hj.trans (hi x hx a b j z)⟩

lemma real_stretch {r : ℝ} (hr : 0≤r) (x y : Points n) : dist (r • x) (r • y) = r* dist x y := by
  simp only [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]

/-- A common p-tail for all the cyclic margins the slab use can need at
this wheel. The ball here is physical (not rescaled). Limit taken only in
period, so R in this lemma is the detector's window and not the period. -/
lemma cyclic_balls (X : Wheel C D) (R : ℝ) :
    ∀ᶠ p : ℕ in atTop, ∀ (x : Points n), x∈Scaling.window R n → x∈openFilm n (8*X.σ) →
      ∀ y ∈ closedBall (X.r • x) (X.r*X.σ), Gaps.allFine C.S p (4*(X.r*X.σ)) y := by
  let g := X.r*X.σ
  let S := cthickening g ((fun x : Points n => X.r • x) '' Scaling.window R n)
  have hS : IsCompact S := ((window_closed ..).image (show Continuous (fun x : Points n => X.r • x) by fun_prop)).cthickening
  filter_upwards [Gaps.expand_equivalent C.S hS] with p hp x hx hg y hy i j hij a
  have hu : y ∈ S := mem_cthickening_of_dist_le _ _ _ _ (mem_image_of_mem _ hx) hy
  have ht := X.rad
  let z := X.r⁻¹ • y
  have he : X.r • z=y := by unfold z; simp only [smul_inv_smul₀ ht.ne']
  have hz : z∈closedBall x X.σ :=
    (le_of_mul_le_mul_left (show X.r*dist z x ≤ g from by rw [← real_stretch ht.le,he]; exact hy) ht : dist z x ≤ X.σ)
  have hh : y∈openFilm n (4*g) := by rw [← he]; exact strict_thin ht z (closed_thin X.stripe.le x hg hz)
  exact fun l => (hh i j hij a).le.trans (hp y hu i j a l)

lemma rescale_round (X : Wheel C D) {h} (w : Ribbon (Bel C.book) t)
    (P : C.Makes) {R e A B : ℝ} (hb : 0≤B)
    (hr : (4*n:ℝ)*X.spacing ≤ X.σ)
    (hs : X.Spots F R e A B h w) :
    ∀ᶠ i : ℕ×ℕ in F.fuse, ∀ (u : positions n),
      let y := fine X i.1 u; let a := address X.spacing y
      y∈Scaling.window R n → y∈openFilm n (8*X.σ) →
      dist (C.numeric i.1 i.2 (ripped (t:=t) (C:=C) (X.tones h w i)) (location C.S X.grid i.1 i.2 ∘ a))
        (revenue X h w i.1 i.2 u) ≤ ((4*n:ℝ)^2) * (B^n*(X.spacing/X.σ)) := by
  obtain ⟨j,hj,HZ⟩ := hs.slab
  unfold generous at HZ
  filter_upwards [HZ, large_mesh F j, large_mesh F X.grid, late_period (F:=F) (cyclic_balls (n:=n) X R)] with i hi he ht ho u
  intro y a hw hh
  let g := X.r*X.σ
  let v : Fin n → C.book.Token := ripped (t:=t) (C:=C) (X.tones h w i)
  let x : positions n := pushSite C.S ht ∘ a
  have hp := X.rad
  let b := tag X.spacing a
  have hu : dist b y ≤ (4*n:ℝ)*X.spacing := approximate X.space y
  have hz : dist (tag (C.S.a i.1) x) (tag (C.S.a i.1) u) = X.r * dist b y := by
    unfold x
    rw [scales_tag ht a, ← X.covers_tag, ← physical_tag X i.1 u, real_stretch X.rad.le]
  rw [zoom_at ht]
  change dist (lifted C i.1 i.2 v x) (lifted C i.1 i.2 v u) ≤ _
  have hG : 0 < g := mul_pos hp X.stripe
  have HT := steps P v hb hG he hi hj x u (by rw [hz]; exact mul_le_mul_of_nonneg_left (hu.trans hr) hp.le) (by
    rw [← physical_tag X i.1 u]; exact ho y hw hh)
  rw [hz] at HT; refine HT.trans ?_
  calc
    _ ≤ ((4:ℝ)*↑n) * ((B^n/g)*(X.r*((4*n:ℝ)*X.spacing))) := by gcongr
    _ = _ := by unfold g; field_simp [hp.ne', X.stripe.ne']

/-- Two regimes for genuine lattice points, common thresholds before joint
test. No continuum limits. Note `k`-dependence of the through-ties bound.
Use this also without `Station.paid` in a test detour. -/
structure PlacementPrices (W : ℕ → Wheel C D) (F : Extraction.Order) (R : ℝ)
    (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t) (A : ℕ→ℝ) : Prop where
  ties : Tendsto (fun k => (W k).σ) atTop (𝓝 0)
  rose : Tendsto (fun k => A k^n * (W k).σ) atTop (𝓝 0)
  whole : ∀ᶠ k in atTop, 0 ≤ A k ∧ F.late fun N p => ∀ u : positions n,
    fine (W k) N u ∈ Scaling.window R n → ‖revenue (W k) h w N p u‖ ≤ A k^n
  away (ε : ℝ) : 0<ε → ∀ᶠ k in atTop, F.late fun N p => ∀ u : positions n,
    fine (W k) N u ∈ Scaling.window R n → fine (W k) N u ∈ openFilm n (8*(W k).σ) →
    ‖revenue (W k) h w N p u - disc (hang t w) (fine (W k) N u)‖ ≤ ε

theorem from_balance (W : ℕ → Wheel C D) {h} (w : Ribbon (Bel C.book) t)
    (P : C.Makes) (L : (Bel C.book).Smooth) {R : ℝ} (hr : 0 < R) {e A B : ℕ→ℝ}
    (hc : Balances W F R h w e A B) : PlacementPrices W F R h w A := by
  constructor
  · exact hc.stripe
  · exact hc.off
  · filter_upwards [hc.pos,hc.costs] with k hk he using ⟨hk.1,cutoff_big _ P hr he⟩
  intro ε he
  let Ω := Scaling.window R n
  let Ω' := Scaling.window (2*R) n
  let Q := disc (hang t w)
  obtain ⟨κ,hκ,hW⟩ := upgrade_window (n:=n) R hr
  have ht : ContinuousOn Q (conf n) := (smoothDisc L _).continuousOn
  have hy : UniformContinuousOn Q Ω' := (window_closed ..).uniformContinuousOn_of_continuous
    (ht.mono (fun x hx => spaced_conf (by positivity : 0 < (2*R)⁻¹) hx.1))
  have hε : 0<ε/4 := by positivity
  obtain ⟨δ,hδ,hQ⟩ := uniformContinuousOn_iff.mp hy _ hε
  have hP : Tendsto (fun k => ((4*n:ℝ)^2)*(B k^n*((W k).spacing/(W k).σ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hc.on_.const_mul ((4*n:ℝ)^2)
  filter_upwards [hc.pos,hc.room,hc.costs,hP.eventually (ge_mem_nhds hε),hc.goes.eventually (ge_mem_nhds hε),
    hc.stripe.eventually (ge_mem_nhds hκ),hc.stripe.eventually (gt_mem_nhds hδ)] with k hp hw hc hl hE hk hd
  let X := W k
  change ∀ᶠ i : ℕ×ℕ in F.fuse, ∀ u : positions n, fine X i.1 u ∈ Ω → fine X i.1 u ∈ openFilm n (8*X.σ) → ‖revenue X h w i.1 i.2 u - Q (fine X i.1 u)‖ ≤ ε
  filter_upwards [aligned_price X hc.compare hε,rescale_round X w P hp.2 hw hc] with i hI hB u hu hs
  let x := fine X i.1 u; let p := address X.spacing x; let y := tag X.spacing p
  have ha : dist y x ≤ X.σ := (approximate X.space x).trans hw
  have hh : y∈Ω' := hW (mem_cthickening_of_dist_le _ x _ _ hu (ha.trans hk))
  have HV : x∈Ω' := hW (self_subset_cthickening _ hu)
  have hY : dist (Q y) (Q x) ≤ ε/4 := (hQ _ hh _ HV (ha.trans_lt hd)).le
  have hz := X.stripe
  have hy : y∈generic n := open_fit _ (by positivity : 0 ≤ 4*X.σ) (closed_thin hz.le x hs ha)
  rw [← dist_eq_norm]
  let l := C.numeric i.1 i.2 (ripped (t:=t) (C:=C) (X.tones h w i)) (location C.S X.grid i.1 i.2 ∘ p)
  let V := revenue X h w i.1 i.2 u
  have HY : dist l (Q y) ≤ e k+ε/4 := by rw [dist_eq_norm]; exact hI p hh hy
  have Ht : dist V l ≤ ε/4 := by rw [dist_comm]; exact (hB u hu hs).trans hl
  change dist V (Q x) ≤ ε
  apply (dist_triangle4 V l (Q y) _).trans; linarith

lemma PlacementPrices.refine {W : ℕ → Wheel C D} {h} {w : Ribbon (Bel C.book) t} {A : ℕ→ℝ} {R : ℝ}
    (hp : PlacementPrices W F R h w A) (f : Extraction.Order) : PlacementPrices W (F.refine f) R h w A :=
  ⟨hp.ties,hp.rose,hp.whole.mono fun _ hk => ⟨hk.1,F.late_refine f hk.2⟩,fun _ he =>
    (hp.away _ he).mono fun _ hk => F.late_refine f hk⟩

end YM.UVNext.StationTransfer
