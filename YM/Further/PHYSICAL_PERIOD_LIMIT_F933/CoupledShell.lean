import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.FreeRanks
import YM.Push.STRESS_FLUX.Cylinder
import YM.Push.STRESS_FLUX.Placement
import YM.Push.STRESS_FLUX.Sharpen
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Charges


/-!
# Coupling the shell ports on a single orientation

This one works for STRESS_FLUX or to pay *Legs* in
COMMON_GRADE. Be careful about which nodes are quoted: the factor of
two in the upper radius here matters. Keep `y` in lattice Cover
placements for the latter, no assumption one may evaluate estimates on
other kinds of tiling, ancestors chosen once per invoice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Shell
open Function Filter Set Lattice Wilson Cells Extraction Analysis Table
  Next.Extract Next.UVStress UVNext.Grade StressFlux Matching
  Push.Common Snap Climb Asymptotics
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book}
variable {f g : Extraction.Order} {N p d D h k m l : ℕ}



/-- The common site-shell invoice. Extent ≤1 would give `Quotes`.
Depth indicators k, e k, ε k here are not the regulator cutoffs and
approach shell-limit zero in the specified direction; the estimate at
fixed node is then required on the actual order f. -/
def Broad (f : Extraction.Order) (v : Rows C) (B : C.label d) (D h : ℕ) :=
  ∀ J : ℕ, ∀ minM, ∃ m≥minM, ∀ minL : ℕ, ∃ l≥max m minL, ∃ e ε : ℕ → ℝ,
    (∀ k, 0<e k ∧ 0 ≤ ε k) ∧ Tendsto e atTop (𝓝 0) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ k : ℕ in atTop, ∀ z : E4, 1/4 ≤ ‖z‖ → ‖z‖ ≤ 2 → ∀ a b : Axis, ∃ A : ℝ,
      ∀ᶠ i : ℕ×ℕ in f.fuse, ∃ u : C.label D, ‖u‖ ≤ A ∧ arrayTest C i.1 i.2 J m l (ε k)
        (cluster (v a b) B (e k ^ h) (ceilSite C i.1 i.2 (e k • z)) u)

variable {v : Rows C} {B : C.label d}




lemma exact_location (C : Family G) (N p m : ℕ) (hm : m≤N) (x : Cover) :
    ceilSite C N p (C.S.gridPoint m x) = location C.S m N p x := by
  unfold ceilSite location
  rw [dif_pos hm, Ratio.embed_wrap, ← finer C.S hm x]
  congr 1 with j
  change ⌈(C.S.a N * ((pushSite C.S hm x j:ℤ):ℝ))/C.S.a N⌉=pushSite C.S hm x j
  rw [mul_div_cancel_left₀ _ (C.S.a_pos N).ne']; exact Int.ceil_intCast _

private lemma align_terrace (C : Family G) {k l N : ℕ} (hk : k+1≤l) (hl : l≤N) (p : ℕ) :
    SiteArray.aligned (Cells.span C.S hl p) (terrace C.S k (hk.trans hl) p).base := by
  intro i
  let n := C.side N p; let b := Cells.span C.S (hk.trans hl) p * ((C.S.block k).val/2)
  let a := Cells.span C.S hl p
  have ha : a∣Cells.span C.S (hk.trans hl) p := Around.inherits hk hl
  have hb : a ∣ b := ha.trans (dvd_mul_right ..)
  have hn : a ∣ n.val := by
    rw [show n.val=(C.side l p).val*a from (C.S.toDepth hl p).exact_size]; exact dvd_mul_left ..
  change a ∣ (-(b : Per n)).val
  let y : Per n := (-(b : Per n))
  by_cases hx : (b : Per n)=0
  · rw [hx]; simp
  haveI : NeZero (b : Per n) := ⟨hx⟩
  rw [ZMod.val_neg_of_ne_zero, ZMod.val_natCast]; exact Nat.dvd_sub hn ((Nat.dvd_mod_iff hn).2 hb)

lemma seat_node (C : Family G) {J k N l : ℕ} (hk : k+1≤l) (hl : l≤N) (p : ℕ) :
    let T := terrace C.S k (hk.trans hl) p
    (T.kind = .site ∧ T.side.val=Cells.span C.S (by omega : k ≤ N) p) ∧
      SiteArray.aligned (Cells.span C.S hl p) T.base ∧
      (0 : Site (C.side N p)) ∈ T.margin 0 (T.side.val / (8*(J+1))) := by
  intro T
  have he := buffered C.S k (hk.trans hl) p 0
  have hx : location C.S k N p 0 = 0 := location_origin ..
  rw [hx,map_zero] at he
  exact ⟨⟨rfl,rfl⟩,align_terrace C hk hl p,Lease.fewer T 0
    (Nat.div_le_div_left (by omega : 3 ≤ 8*(J+1)) (by decide)) he⟩

/-- Per-station transfer to the lattice-node radius tests. J can be
one already: no spectator occupation premise used for this conversion!
No losing the root weights, no adjustment of the centers' sharing at m+1. -/
theorem Broad.pays (H : Broad f v B D h) : ShellBound (S:=S) f D h (S.project d B)
    (fun i j => S.project 4 (v i j)) := by
  refine ⟨v,B,fun i j => rfl,rfl,fun k => ?_⟩
  obtain ⟨m,hm,K⟩ := H 1 k
  obtain ⟨l,hl,e,ε,he,hT,hε,hK⟩ := K (m+1)
  refine ⟨m,hm,fun x hx δ hδ => ?_⟩
  obtain ⟨i,hi,hδ,hε⟩ := (hK.and ((hT.eventually (ge_mem_nhds hδ)).and (hε.eventually (ge_mem_nhds hx)))).exists
  refine ⟨e i,(he i).1,hδ,price_node (C:=C) ?_⟩
  intro a b y z hz
  let q := C.S.gridPoint y z
  let t := (e i)⁻¹ • q
  have hpos := (he i).1
  have ht : 1/4 ≤ ‖t‖ ∧ ‖t‖ ≤ 2 := by
    rw [show ‖t‖ = ‖q‖ / e i by unfold t; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_eq_div]]
    exact ⟨(le_div_iff₀ hpos).2 (by linarith only [show e i/4<‖q‖ from hz.1]),(div_le_iff₀ hpos).2 hz.2.le⟩
  obtain ⟨A,H⟩ := hi t ht.1 ht.2 a b
  rw [show e i • t = q by rw [smul_inv_smul₀ hpos.ne']] at H
  -- add cofinal l and m/y depths; no uniformity in y for free
  refine ⟨max 0 A,le_max_left ..,?_⟩
  change ∀ᶠ j : ℕ × ℕ in f.fuse, ∃ (u : C.label D) (hN : m+1≤j.1), ‖u‖ ≤ max 0 A ∧
    Interior ((terrace C.S m hN j.2).chamber 0) (fragment (d:=d) (C:=C) (D:=D) h (e i) (v a b) B y z j.1 j.2 u) ∧
      (terrace C.S m hN j.2).rootTest (C.beta j.1 j.2) (fragment (d:=d) (C:=C) (D:=D) h (e i) (v a b) B y z j.1 j.2 u) ≤ x
  filter_upwards [large_mesh f l, large_mesh f y,H] with j hj hy hu
  rcases j with ⟨N,p⟩
  obtain ⟨u,hu,hU⟩ := hu
  have hr : m+1≤N := by omega
  let T := terrace C.S m hr p
  obtain ⟨hK,hl',hc⟩ := seat_node C (J:=1) (show m+1≤l from by omega) hj p
  have he : ceilSite C N p q = location C.S y N p z := exact_location C N p y hy z
  have hcluster : cluster (C:=C) (v a b) (B : C.label d) (e i^h) (location C.S y N p z) (u : C.label D) = fragment (C:=C) (D:=D) (d:=d) h (e i) (v a b) B y z N p u := by
    funext U
    unfold cluster fragment
    rw [Complex.ofReal_pow]
  obtain ⟨_hm, _hl, hw⟩ := hU
  obtain ⟨hI,hQ⟩ := hw T hK.1 hK.2 hl' hc
  change ‖u‖ ≤ A at hu
  change _ ≤ ε i at hQ
  refine ⟨u,hr,hu.trans (le_max_right ..),?_,?_⟩
  · simpa only [he,hcluster] using hI
  apply le_trans ?_ hε
  simpa only [he,hcluster] using hQ

/-- Minimal *width patch* to StressFlux.Matching.Ancestor if paying all
seam/arity calls of both types. The stencils, roots, thresholds and ALL
position costs must actually hold with this patch. Alternatively for
just the Grade-closes consumer can weaken further to J=one, to just
terrace seams, lattice placements and `e k` tolerance requests through
the wages estimator above. -/
def PaidNode (f : Extraction.Order) (v : Matching.Rows C) (B : C.label d) (D h : ℕ) :=
  ∀ J : ℕ, ∀ minM, ∃ m≥minM, ∀ minL : ℕ, ∃ l≥max m minL, ∃ b : ℕ → ℕ, ∃ g w : ℕ → ℝ, ∃ γ : ℝ,
    0<γ ∧ Tendsto b atTop atTop ∧ (∀ k, 0<g k) ∧ ((Real.log ∘ g) =o[atTop] (C.S.scale ∘ b)) ∧ (w =o[atTop] (C.S.scale ∘ b)) ∧
    ∀ᶠ k : ℕ in atTop, ∀ z : E4, 1/4 ≤ ‖z‖ → ‖z‖ ≤ 2 → ∀ a j : Axis, ∃ A : ℝ,
      ∀ᶠ i : ℕ×ℕ in f.fuse, ∃ u : C.label D, ‖u‖ ≤ A ∧
        Matching.prepared C i.1 i.2 J m l (Real.exp (-γ * C.S.scale (b k) + w k))
          (cluster (v a j) B (C.S.a (b k)^h) (ceilSite C i.1 i.2 ((g k*C.S.a (b k)) • z)) u)

lemma PaidNode.broad (p : PaidNode f v B D h) : Broad f v B D h := by
  intro J m
  obtain ⟨m,hm,H⟩ := p J m
  refine ⟨m,hm,fun l => ?_⟩
  obtain ⟨l,hl,b,g,w,γ,hγ,hb,hg,hs,hw,he⟩ := H l
  refine ⟨l,hl,fun k => g k*C.S.a (b k),fun k => g k^h * Real.exp (-γ * C.S.scale (b k)+w k),
    fun k => ⟨mul_pos (hg _) (C.S.a_pos _), by have := hg k; positivity⟩, separation_size hg hb hs,
    Matching.squeeze_exp hγ hg (C.S.divergent.comp hb) hs hw,?_⟩
  filter_upwards [he] with k hk z hZ hz a j
  obtain ⟨A,hA⟩ := hk z hZ hz a j
  refine ⟨‖(g k:ℂ)^h‖ * A,hA.mono ?_⟩
  intro i hi; obtain ⟨u,hu,hU⟩ := hi
  refine ⟨_, ?_, Matching.rescale (v a j) B (g k) (hg k).le hU⟩
  exact norm_smul_le .. |>.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))

/-- Dishonest to write *two* requirements even for tiny, on one of
which we'd have an obsolete radius convention. Instead exploit the fact
that accepted Seats holds for ANY sequence approaching zero. Can cheaply
pay Broad already (no PaidNode hypothesis for these weights), same Tiling
margins and all possible offsets/labels. -/
lemma tiny_broad (H : C.Makes) (hh : G.Simple) (ht : CenteredBook C f) (d : ℕ) (hd : d < 4)
    (X : C.label d) (v : Rows C) (D h : ℕ) (hg : 0<h) : Broad f v X D h := by
  obtain ⟨c,hc⟩ := Matching.tiny_reference hh hd X
  intro J m; refine ⟨m,le_rfl,fun l => ?_⟩
  choose A hA HA using fun a b : Axis => Matching.seats H ht ⟨4,v a b⟩ m J C.S.a (fun k => (C.S.a_pos _).le) C.S.shrinks
  obtain ⟨P,hP⟩ := (eventually_all.mpr fun a => eventually_all.mpr fun b => eventually_ge_atTop (A a b)).exists
  let e (k : ℕ) := (2:ℝ)⁻¹*C.S.a k
  have he : Tendsto e atTop (𝓝 0) := by simpa using C.S.shrinks.const_mul (2:ℝ)⁻¹
  have h₁ k : 0 < e k := mul_pos (by norm_num) (C.S.a_pos _)
  refine ⟨max m l,le_rfl, e, fun k => (e k^h * ‖c‖) * P,fun k => ⟨h₁ _,mul_nonneg (mul_nonneg (pow_nonneg (h₁ _).le _) (norm_nonneg _)) ((hA 0 0).trans (hP _ _))⟩,he,?_,?_⟩
  · simpa only [zero_pow hg.ne',zero_mul] using ((he.pow h).mul_const ‖c‖).mul_const P
  filter_upwards [eventually_all.mpr fun a => eventually_all.mpr (HA a)] with k hk z _ hz a b
  refine ⟨0,?_⟩
  let y := ((2:ℝ)⁻¹ • z)
  have hy : e k • z = C.S.a k • y := by unfold e y; rw [smul_smul,mul_comm]
  have hY : ‖y‖ ≤ 1 := calc
    _ = (2:ℝ)⁻¹*‖z‖ := norm_smul_of_nonneg (by norm_num) _
    _ ≤ (2:ℝ)⁻¹*2 := mul_le_mul_of_nonneg_left hz (by norm_num)
    _ = 1 := inv_mul_cancel₀ two_ne_zero
  filter_upwards [large_mesh f (max m l), large_mesh f (C.ref d),hk a b] with i hl href hi
  let t := ceilSite C i.1 i.2 (e k • z)
  let Gs := C.O i.1 i.2 (d:=4) (v a b) t
  have hF : cluster (v a b) X (e k ^ h) t (0 : C.label D)=fun U => ((e k:ℂ)^h*c)*Gs U := by
    unfold cluster Family.seen Gs; rw [hc,(C.linearO ..).map_smul,C.constant H d href,(C.linearO ..).map_zero]
    ext1 U; simp [mul_comm,mul_assoc]
  refine ⟨0,by simp,hi.late,hl,fun T _ hT _ ho => ?_⟩
  obtain ⟨hf,hR⟩ := hi.sit y hY T hT ho
  rw [← hy] at hf hR
  rw [hF]; have : 0 ≤ e k := (h₁ k).le
  refine ⟨(hf _).scale _,(Matching.test_scale_complex ..).trans (mul_le_mul ?_ hR (T.root_nonneg ..) (by positivity) |>.trans
    (mul_le_mul_of_nonneg_left (hP a b) (by positivity)))⟩
  rw [norm_mul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg this]

variable {W : DiffPlan S}




/-- Offer shells on demand for some chosen material w. Note why the
predicate for just `Quotes`/`ForShell` needn't automatically persist:
it may include its own refinement; we can't just intersect two arbitrary
assigned refinements after they were chosen. Need station offers e.g. via
ANY previous order as here. -/
def Occupied (f : Extraction.Order) (w : StressFlux.Coeff) (l : Leg S) :=
    4 ≤ l.1 → ∃ B : C.label l.1, S.project l.1 B = spectrum S l.1 l.2.2 ∧
      Broad f (StressFlux.token C w) B (payLevel l.1 l.2.1) (shellWeight l.2.1)



/-- COHERENT PoweredLeg offer at the Grade interface, w fixed inside
this job (can be whichever of the available stresses; not tied to the
unrealized sign/use of the vacuum). `on_curve` later transfers through
the real stress line to the ORIENTED current actually used. -/
lemma leg_offers (a : FreeInput C) (hH : S.Hierarchy) (hW : W.Orientation hH.spin)
    (h4 : Spin.change S 4) (h5 : Spin.change S 5)
    (hp : Spin.realH hH.spin a.kernels.spin h4) (hp' : Spin.realH hH.spin a.kernels.spin h5)
    (hh : G.Simple) (H : C.Makes) (hP : CenterPort C f)
    (h : ∀ w : StressFlux.Coeff, ‖w‖=1 → StressFlux.nabla W (material S w)=0 → Centers (material S w) →
        Push.Common.Stationed f (fun l : Leg S => fun e => Occupied e w l)) : ProbeOffer f hH W := by
  obtain ⟨w,hw,hz,hc⟩ := StressFlux.exists_stress W hh hH hW h4 h5 hp hp'
  obtain ⟨c,hC,hD⟩ := h w hw hz hc
  have hm := material_conserved W hH.spin hz
  let J := material S w
  have hu : J ∈ KernelSpace hH.spin := sym_of_centers (tableStress hH.spin w).property hc
  refine ⟨c,hC,fun l => ?_⟩
  obtain ⟨k,hk⟩ := hD l
  let t : Extraction.Order := f.refine (c k)
  refine ⟨k,J,hu,hc.alive,hm.1,cleared_iff.mpr ?_⟩
  change leg S l J t
  suffices h : ∃ B : C.label l.1, S.project _ B = spectrum S _ l.2.2 ∧
      Broad t (StressFlux.token C w) B (payLevel _ l.2.1) (shellWeight l.2.1) by
    obtain ⟨B,hB,H⟩ := h; unfold UVNext.Grade.leg legRow
    rw [← hB]; exact H.pays
  rcases le_or_gt 4 l.1 with H|hg
  · exact hk H
  refine ⟨S.representative _ (spectrum S _ l.2.2),S.rep ..,?_⟩
  apply tiny_broad H hh ((Tails.refine f (c k)).center hP).book _ hg
  unfold shellWeight; split <;> decide
end YM.Further.PhysicalPeriodLimitF933.Shell
