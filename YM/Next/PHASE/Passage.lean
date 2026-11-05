import YM.Dash.Regular
import YM.Next.PHASE.Roots



/-!
# Passing the mixed cell estimate to continuum point words

Given a small number of main residue patterns (independent of the number of
replicas when used below), fit those first, then choose a translation by less
than the exterior scale for the exterior margins. Put the main fields at those
residues *up to a perturbation*: require margins even for the perturbed fields,
so during passage to continuum words all slots can vary independently. Use point
limits only on generic tuples, including mesh and period on the same order that
pays the centered bounds. No convergence assumption at projection ties.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Phase
open Function Set Filter Lattice Cells Extraction Extraction.Gaps Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius

/-- Congruent coordinates at coarse spacing `s`. -/
def Pattern (s : ℝ) (x y : E4) := ∀ a : Axis, ∃ d : ℤ, x a = y a + d*s

private def ceilPoint (t : ℝ) (x : E4) : Cover := fun a => ⌈x a / t⌉

private lemma round_near (t : ℝ) (ht : 0<t) (x y : E4) (K : ℕ) (h : ∀ a : Axis, |y a-x a| ≤ t*K) :
    ∀ a, ((ceilPoint t y - ceilPoint t x : Cover) a).natAbs ≤ K := by
  intro a
  have he {w z : ℝ} (he : w-z ≤ t*K) : ⌈w/t⌉ ≤ ⌈z/t⌉ + (K:ℤ) := by
    rw [← Int.ceil_add_natCast]
    apply Int.ceil_le_ceil
    apply (div_le_iff₀ ht).mpr
    rw [add_mul,div_mul_cancel₀ _ ht.ne']; linarith
  obtain ⟨ha,hb⟩ := abs_le.mp (h a)
  have hh := he hb
  have hh' := he (show x a-y a ≤ t*K by linarith)
  change (⌈y a/t⌉ - ⌈x a/t⌉).natAbs ≤ K
  omega

private lemma round_same {n : Side} (T : Tiling n) (t : ℝ) (ht : 0<t) (x y : E4)
    (H : Pattern (t*T.side.val) x y) (a : Axis) :
    stripe T (wrap n (ceilPoint t x)) a = stripe T (wrap n (ceilPoint t y)) a := by
  obtain ⟨d,hd⟩ := H a
  have he : ceilPoint t x a = ceilPoint t y a + d*T.side.val := by
    have hh : x a/t=y a/t + ((d*T.side.val : ℤ) : ℝ) := by rw [hd]; push_cast; field_simp
    unfold ceilPoint; rw [hh, Int.ceil_add_intCast]
  unfold stripe
  change T.hom (((ceilPoint t x a:ℤ): Per n)-_) = T.hom (((ceilPoint t y a:ℤ):Per n)-_)
  rw [he,map_sub,map_sub,map_intCast,map_intCast,Int.cast_add,Int.cast_mul, Int.cast_natCast,ZMod.natCast_self,mul_zero,add_zero]

private lemma room_cast (S : Schedule) {f k N : ℕ} (p : ℕ) (h : f ≤ k) (hk : k ≤ N) (L n : ℕ)
    (hp : (n:ℝ)*(2*((L:ℝ)*S.a k)) < S.a f) : n*(2*(L*span S hk p)) < span S (h.trans hk) p := by
  apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (S.a_pos N).le
  have hh a (ha : a ≤ N) : S.a N * span S ha p = S.a a := S.embeds_scale (S.toDepth ha p)
  rw [hh]; rw [← hh k hk] at hp; push_cast; linarith

private lemma separated_sites (S : Schedule) {n N p m : ℕ} (hm : m ≤ N)
    (w : Fin n → Cover) (i j : Fin n) (x : Points n) (hx : x=tag (S.a N) w)
    (hoff : ∀ a, off S p (distances x j i a) |distances x j i a|)
    (hgap : S.a m < cubedist (x i) (x j)) :
    span S hm p < separation (wrap (S.side N p) (w i)) (wrap (S.side N p) (w j)) := by
  obtain ⟨a,ha⟩ : ∃ a : Axis, S.a m < |distances x j i a| := by
    by_contra! h
    exact hgap.not_ge ((dist_pi_le_iff (f := WithLp.ofLp (x i)) (g := WithLp.ofLp (x j)) (S.a_pos m).le).mpr
      (fun a => by rw [Real.dist_eq]; exact h a))
  let v := wrap (S.side N p) (w i) - wrap (S.side N p) (w j)
  let z := lift v
  subst x
  have he := Gaps.torus S (z a) (show wrap (S.side N p) (w i-w j) a = wrap (S.side N p) z a by
    rw [map_sub,wrap_lift (x := v)]) (hoff a)
  have hp : |((z a : ℤ) : ℝ)| = ((z a).natAbs : ℝ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hp] at he
  apply lt_of_lt_of_le _ (component_le v a)
  apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (S.a_pos N).le
  rw [show S.a N * span S hm p = S.a m from S.embeds_scale (S.toDepth hm p)]
  exact ha.trans_le he

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ} (e : ι ⊕ κ ≃ Fin n)

/-- Main fits to resolution `s`, exterior points can cost smaller `r`. -/
def Gapped (s r : ℝ) (x : Points n) :=
  (∀ i j : ι, i≠j → s < cubedist (x (e (.inl i))) (x (e (.inl j)))) ∧
  (∀ (i : ι) (j : κ), s < cubedist (x (e (.inl i))) (x (e (.inr j)))) ∧
  (∀ i j : κ, i≠j → r < cubedist (x (e (.inr i))) (x (e (.inr j))))

private lemma gapped_open (s r : ℝ) : IsOpen {x : Points n | Gapped e s r x} := by
  rw [isOpen_iff_mem_nhds]
  intro x H
  change Gapped e s r x at H
  have ht i j a (h : a < cubedist (x i) (x j)) : ∀ᶠ y : Points n in 𝓝 x, a < cubedist (y i) (y j) := by
    have hc : Continuous (fun y : Points n => cubedist (y i) (y j)) := by unfold cubedist; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds h)
  have h₀ : ∀ᶠ y : Points n in 𝓝 x, ∀ i j : ι, i≠j → s < cubedist (y (e (.inl i))) (y (e (.inl j))) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun h => ht _ _ _ (H.1 i j h)
  have h₁ : ∀ᶠ y : Points n in 𝓝 x, ∀ (i : ι) (j : κ), s < cubedist (y (e (.inl i))) (y (e (.inr j))) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => ht _ _ _ (H.2.1 i j)
  have h₂ : ∀ᶠ y : Points n in 𝓝 x, ∀ i j : κ, i≠j → r < cubedist (y (e (.inr i))) (y (e (.inr j))) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun h => ht _ _ _ (H.2.2 i j h)
  exact h₀.and (h₁.and h₂)

variable {G : Gauge} (C : Family G)

omit [Fintype ι] in
private lemma margins {N p m k l b P : ℕ} (hm : m≤k) (hk : k≤l) (hl : l≤b) (hb : b ≤ N)
    (x : ι → E4) (z : Fin P → E4) (t : ι → E4)
    (r : κ → Site (C.side N p)) (patterns : ∀ i, ∃ j, Pattern (C.S.a m) (x i) (z j))
    (htags : ∀ i a, |t i a-x i a| ≤ C.S.a k) (headroom : (P:ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (Fintype.card κ : ℝ)*(2*(3*C.S.a b)) < C.S.a l) :
    let h := (hm.trans hk).trans (hl.trans hb)
    ∃ o : Site (C.side N p),
      (∀ i, Inside ((center C.S p h 0).newly o) (3*span C.S (hk.trans (hl.trans hb)) p)
        (wrap _ (ceilPoint (C.S.a N) (t i)))) ∧
      (∀ j, Inside ((center C.S p (hl.trans hb) 0).newly o) (3*span C.S hb p) (r j)) := by
  intro h; classical
  let T := center C.S p h 0
  let f : k≤N := hk.trans (hl.trans hb)
  let d := span C.S f p
  have hp := C.S.a_pos N
  have hs : C.S.a N * d=C.S.a k := C.S.embeds_scale (C.S.toDepth f p)
  let U (x : E4) := wrap (C.side N p) (ceilPoint (C.S.a N) x)
  have hK : P*(2*(5*d)) < T.side.val := room_cast C.S p hm f 5 P (by norm_cast)
  have hd : 0 < 5*d := Nat.mul_pos (by decide) (C.S.toDepth f p).count.property
  obtain ⟨o,ho⟩ := T.fits_together (fun j => U (z j)) (5*d) hd hK
  let X := T.newly o
  have Xlink : X.kind=.link := rfl
  have he (i) : Inside X (5*d) (U (x i)) := by
    obtain ⟨j,hj⟩ := patterns i
    have H : C.S.a N * X.side.val = _ := C.S.embeds_scale (C.S.toDepth h p)
    rw [inside_stripe X Xlink]; intro a
    rw [show stripe X (U (x i)) a = stripe X (U (z j)) a from round_same X _ hp _ _ (H.symm ▸ hj) a]
    exact (inside_stripe X Xlink _ _).mp (ho j) a
  let Y := center C.S p (hl.trans hb) 0
  have hY : Fintype.card κ*(2*(3*span C.S hb p))<Y.side.val := room_cast C.S p hl hb 3 _ (by norm_cast)
  obtain ⟨w,hw,H⟩ := shift_into Y r o rfl (3*span C.S hb p)
    (Nat.mul_pos (by decide) (C.S.toDepth hb p).count.property) hY
  refine ⟨o + wrap _ w,fun i => ?_,H⟩
  have hy : Y.side.val ≤ d := Nat.le_of_dvd (C.S.toDepth f p).count.property (Around.inherits hk (hl.trans hb))
  have ht := inside_after X Xlink _ w _ d (he i) (fun a => ((hw a).le.trans hy))
    (round_near _ hp (x i) (t i) d (fun a => (htags i a).trans_eq hs.symm))
  rw [show U (x i)+_ = U (t i) from (by unfold U; rw [map_sub]; abel)] at ht
  exact ht

private lemma numeric_bound (H : C.Makes) {N p m k l b P : ℕ} (hm : m≤k) (hk : k≤l) (hl : l≤b)
    (hb : b ≤ N) (x : Points n) (z : Fin P → E4) (v : Fin n → C.book.Token)
    (patterns : ∀ i : ι, ∃ j, Pattern (C.S.a m) (x (e (.inl i))) (z j))
    (headroom : (P:ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (Fintype.card κ : ℝ)*(2*(3*C.S.a b)) < C.S.a l)
    (A B : ℝ) (hB : 0 ≤ B) (ha : ∀ i, Single C (v (e (.inl i))) A k N p)
    (hf : ∀ j, Single C (v (e (.inr j))) B b N p)
    (y : Points n) (htags : ∀ (i : Fin n) a, |y i a - x i a| ≤ C.S.a k)
    (s : Points n) (hs : s=tag (C.S.a N) (address (C.S.a N) y))
    (hx : Gapped e (C.S.a m) (C.S.a l) s)
    (hoff : ∀ i j a, off C.S p (distances s i j a) |distances s i j a|) :
    let u := address (C.S.a N) y
    ‖C.numeric N p v (fun i => wrap _ (u i))‖ ≤ A ^ Fintype.card ι * B ^ Fintype.card κ := by
  intro u
  let f (i) := e (Sum.inl i); let g i := e (Sum.inr i)
  let X i := wrap (C.side N p) (u i)
  have hg : l≤N := hl.trans hb
  have he := hk.trans hg
  let D := center C.S p (hm.trans he) 0
  let E := center C.S p hg 0
  obtain ⟨o,hox,hoy⟩ := margins (ι := ι) C hm hk hl hb (fun i => x (f i)) z
    (fun i => y (f i)) (X ∘ g) patterns (fun i => htags _) headroom side
  let T := D.newly o; let Y := E.newly o
  have hh : C.numeric N p v X = moment (C.beta N p)
      (fun U => (∏ i : ι, C.seen (v (f i)) (X (f i)) U) * ∏ i : κ, C.seen (v (g i)) (X (g i)) U) := by
    rw [C.num]; unfold moment
    apply MeasureTheory.integral_congr_ae
    refine Eventually.of_forall fun U => ?_
    have hi := Equiv.prod_comp e (fun i => C.seen (v i) (X i) U)
    rw [Fintype.prod_sum_type] at hi; exact hi.symm
  change ‖C.numeric N p v X‖ ≤ _; rw [hh]
  exact cutoff_bound (Y := Y) (T := T) H rfl rfl rfl (Around.inherits (C:=C) (hm.trans hk) hg)
    he hb (Around.inherits (C:=C) hm he) (Around.inherits (C:=C) hl hb)
    (v ∘ f) (v ∘ g) (X ∘ f) (X ∘ g) hox hoy
    (fun i j h => separated_sites C.S (hm.trans he) u _ _ s hs (hoff _ _) (hx.1 i j h))
    (fun i j => separated_sites C.S (hm.trans he) u _ _ s hs (hoff _ _) (hx.2.1 i j))
    (fun i j h => separated_sites C.S hg u _ _ s hs (hoff _ _) (hx.2.2 i j h))
    A B hB ha hf

/-- Main/exterior continuum estimate with a residue payment depending only on
`P`. Exterior payment may depend on `κ`. Labels can be heterogeneous. -/
theorem point_bound (H : C.Makes) (f : Extraction.Order) (S : Table C.book) (ht : S.Smooth)
    (he : f.PointLimits C S) (m k l b : ℕ) (hm : m≤k) (hk : k≤l) (hl : l≤b)
    (x : Points n) (hc : x∈conf n) (v : Fin n → C.book.Token)
    (hx : Gapped e (C.S.a m) (C.S.a l) x) (P : ℕ) (z : Fin P → E4)
    (patterns : ∀ i : ι, ∃ j, Pattern (C.S.a m) (x (e (.inl i))) (z j))
    (headroom : (P:ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (Fintype.card κ : ℝ)*(2*(3*C.S.a b)) < C.S.a l)
    (A B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ i, f.late (Single C (v (e (.inl i))) A k))
    (hf : ∀ j, f.late (Single C (v (e (.inr j))) B b)) :
    ‖S.read x v‖ ≤ A ^ Fintype.card ι * B ^ Fintype.card κ := by
  obtain ⟨Q,hQ,pay⟩ := he
  let W := {s | Gapped e (C.S.a m) (C.S.a l) s}
  have hopen := gapped_open (e := e) (C.S.a m) (C.S.a l)
  have hr := (conf_open _).mem_nhds hc
  have h : ContinuousAt (fun y => S.read y v) x := ((S.smooth_read ht v).continuousOn x hc).continuousAt hr
  haveI : NeBot (𝓝[generic n] x) := mem_closure_iff_nhdsWithin_neBot.mp (Dash.full n x)
  refine le_of_tendsto (h.norm.continuousWithinAt (s := generic n)).tendsto ?_
  have near (i : Fin n) (a : Axis) : ∀ᶠ y : Points n in 𝓝 x, |y i a-x i a| ≤ C.S.a k := by
    have hc : Continuous (fun y : Points n => |y i a-x i a|) := by fun_prop
    exact hc.continuousAt.eventually (ge_mem_nhds (by simpa using C.S.a_pos k : |x i a-x i a| < C.S.a k))
  have hr := eventually_all.mpr (fun i : Fin n => eventually_all.mpr (near i))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (show W ∈ 𝓝 x from hopen.mem_nhds hx),
    mem_nhdsWithin_of_mem_nhds hr,self_mem_nhdsWithin] with y hy htags hY
  have he : Tendsto (fun i => (Q (f.per i)).read y v) atTop (𝓝 (S.read y v)) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [pay n {y} isCompact_singleton (singleton_subset_iff.mpr hY) v ε hε] with i hi
    rw [dist_eq_norm]; exact hi _ (mem_singleton y)
  obtain ⟨K,hK,hI,Ksub⟩ := exists_compact_subset hopen hy
  have hxy : f.late fun N p => (∀ i, Single C (v (e (.inl i))) A k N p) ∧ ∀ i, Single C (v (e (.inr i))) B b N p := by
    unfold Order.late at *
    filter_upwards [eventually_all.mpr ha,eventually_all.mpr hf] with i hi hp
    exact (eventually_all.mpr hi).and (eventually_all.mpr hp)
  refine le_of_tendsto he.norm ?_
  unfold Order.late at hxy
  filter_upwards [hxy,f.per.cofinal.eventually (room C.S hK),
    f.per.cofinal.eventually (expand_equivalent C.S hK)] with p hp hpos hw
  let u N := address (C.S.a N) y
  have hC := (no_wrap_tie C.S (hpos (interior_subset hI))).2 hY
  have hG := (chosen (S:=C.S) y).comp f.mesh.cofinal
  refine le_of_tendsto (f.evaluated C hQ (f.per p) n v y hC (fun j => u (f.mesh j)) hG).norm ?_
  filter_upwards [hp, hG.eventually (mem_interior_iff_mem_nhds.mp hI), f.mesh.cofinal.eventually (eventually_ge_atTop b)] with j hj hU hb
  exact numeric_bound e C H hm hk hl hb x z v patterns headroom side A B hB hj.1 hj.2 y htags _ rfl (Ksub hU) (hw _ hU)

end YM.Next.Phase
