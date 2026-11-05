import YM.Push.STRESS_FLUX.SiteArray

/-!
Wilson-to-kernel gate for the isolated+joint product estimate used on . Bounded D-coordinates are required at each *fixed* shell;
NOT a scale-uniform bound. No approximation at the ancestor mesh. The
same local representative must pay the signed root over each budgeted seam
(independent of which generic detector positions are put there). The order of
tails retains the prescribed family and every point test at that order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Matching
open Lattice Wilson Extraction Function Set Filter MeasureTheory Cells SiteArray
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {k N p n D d h J m l : ℕ} {f : Extraction.Order}

abbrev Rows (C : Family G) := Axis → Axis → C.label 4

def ceilSite (C : Family G) (N p : ℕ) (y : E4) : Site (C.side N p) := wrap _ (fun i => ⌈y i / C.S.a N⌉)

def cluster (v : C.label 4) (B : C.label d) (r : ℝ) (y : Site (C.side N p)) (u : C.label D) (U : Config G (C.side N p)) :=
  (r : ℂ) * C.seen ⟨4,v⟩ y U * C.seen ⟨d,B⟩ 0 U - C.seen ⟨D,u⟩ 0 U

def arrayTest (C : Family G) (N p J m l : ℕ) (ε : ℝ) (F : Config G (C.side N p) → ℂ) := ∃ (_hm : m ≤ N) (hl : l ≤ N),
  ∀ T : Tiling (C.side N p), T.kind = .site → T.side.val=Cells.span C.S _hm p → aligned (Cells.span C.S hl p) T.base →
    (0 : Site (C.side N p)) ∈ T.margin 0 (T.side.val/(8*(J+1))) → Interior (T.chamber 0) F ∧ T.rootTest (C.beta N p) F ≤ ε

/-- Gate on actual fine cylinders, with test nodes arbitrary in an annulus
(fine Wilson placements by right-ceil at N), no ties or progenitor-offset
restriction. Seam aligned to level l at physical side level m. Powers are
normalized to *physical* shell size. Thus any scale/shell ratio costs after
conversion must be included in ε. `J` bounds the tested arity INCLUDING the
center but not the stress slot, and always adding 1 keeps positive denominators.
-/
def Quotes (f : Extraction.Order) (v : Rows C) (B : C.label d) (D h : ℕ) :=
  ∀ J : ℕ, ∀ minM, ∃ m≥minM, ∀ minL : ℕ, ∃ l≥max m minL, ∃ e ε : ℕ → ℝ,
    (∀ k, 0<e k ∧ 0 ≤ ε k) ∧ Tendsto e atTop (𝓝 0) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ k : ℕ in atTop, ∀ z : E4, 1/4 ≤ ‖z‖ → ‖z‖ ≤ 1 → ∀ a b : Axis, ∃ A : ℝ,
      ∀ᶠ i : ℕ×ℕ in f.fuse, ∃ u : C.label D, ‖u‖ ≤ A ∧ arrayTest C i.1 i.2 J m l (ε k)
        (cluster (v a b) B (e k ^ h) (ceilSite C i.1 i.2 (e k • z)) u)

structure Audience (L : Register G) where
  n : ℕ
  x : Points (n+1)
  center : x 0 = 0
  avoids : x ∈ generic _
  tags : Fin n → L.Token

def rounded (C : Family G) (N p : ℕ) : Table C.book := ⟨fun d x => C.ensemble d (fun i => ceilSite C N p (x i))⟩



lemma rounded_tendsto (hx : f.PointLimits C S) (v : Fin n → C.book.Token) (x : Points n) (he : x ∈ generic n) :
    Tendsto (fun i : ℕ × ℕ => (rounded C i.1 i.2).read x v) f.fuse (𝓝 (S.read x v)) := by
  obtain ⟨P,hP,hu⟩ := hx
  refine Extraction.Order.along (L := fun N p => (rounded C N p).read x v) (p := fun p => x∈Cyclic C.S p n)
    ⟨?_,fun p => (P p).read x v, fun p hp => f.evaluated C hP p n v x hp (fun i => address (C.S.a (f.mesh i)) x) ((chosen x).comp f.mesh.cofinal),?_⟩
  · filter_upwards [f.per.cofinal.eventually (room C.S (isCompact_singleton (x:=x)))] with i hi
    exact (no_wrap_tie C.S (hi (mem_singleton x))).2 he
  apply Metric.tendsto_nhds.mpr
  intro t ht
  filter_upwards [hu n {x} isCompact_singleton (singleton_subset_iff.mpr he) v t ht] with i hi
  simpa only [dist_eq_norm] using hi x (mem_singleton x)

lemma cluster_read (s : Audience C.book) (v : C.label 4) (B : C.label d) (r : ℝ) (y : E4) (u : C.label D) :
    sample (cluster v B r (ceilSite C N p y) u) s.tags (fun i => ceilSite C N p (s.x i.succ)) =
      (r:ℂ) * (rounded C N p).read (Points.cons y s.x) (Fin.cons ⟨4,v⟩ (Fin.cons ⟨d,B⟩ s.tags)) -
        (rounded C N p).injectFront s.tags s.x D u := by
  let prod {j : ℕ} (q : Fin j → C.book.Token) (x : Points j) := fun U : Config G (C.side N p) => ∏ i, C.seen (q i) (ceilSite C N p (x i)) U
  have ht {j} (q : Fin j → C.book.Token) (x : Points j) : Integrable (prod q x) (law G _ (C.beta N p)) := C.integrableR q _
  let q : Fin (s.n+1+1) → C.book.Token := Fin.cons ⟨4,v⟩ (Fin.cons ⟨d,B⟩ s.tags)
  let g : Fin (s.n+1) → C.book.Token := Fin.cons ⟨D,u⟩ s.tags
  change _ = _ * (∫ U, prod q _ U ∂law G _ _) - (∫ U, prod g s.x U ∂law G _ _)
  rw [← integral_const_mul, ← integral_sub ((ht q _).const_mul _) (ht g s.x)]
  refine integral_congr_ae (.of_forall fun U => ?_)
  change cluster v B r _ u U * _ = _ * prod q _ U - prod g s.x U
  have h0 : ceilSite C N p (s.x 0) = 0 := by simp [s.center,ceilSite,show (fun _ : Axis => (0:ℤ))=(0:Cover) from rfl]
  simp only [cluster,prod,Fin.prod_univ_succ,g,q,Points.cons,points_apply,Fin.cons_zero,Fin.cons_succ,h0,sub_mul,mul_assoc]

lemma width (J m : ℕ) : ∀ᶠ l in atTop, ∀ {N p} (hm : m≤N) (hl : l ≤ N),
    3 * Cells.span C.S hl p ≤ Cells.span C.S hm p / (8*(J+1)) := by
  let E := 8*(J+1)
  have hv := (C.S.shrinks.const_mul ((3*E : ℕ):ℝ)).eventually (ge_mem_nhds (show ((3*E:ℕ):ℝ)*0 < C.S.a m by rw [mul_zero]; exact C.S.a_pos _))
  filter_upwards [hv] with l h N p hm hl
  apply (Nat.le_div_iff_mul_le (by omega)).2
  apply (Nat.cast_le (α:=ℝ)).1
  apply le_of_mul_le_mul_left _ (C.S.a_pos N)
  rw [C.S.embeds_scale (C.S.toDepth hm p)]
  have := C.S.embeds_scale (C.S.toDepth hl p)
  change C.S.a N * (Cells.span C.S hl p:ℝ) = C.S.a l at this
  rw [← this] at h
  change C.S.a N * (((3 * Cells.span C.S hl p * E):ℕ):ℝ) ≤ _
  push_cast at *; linarith

lemma apart (s : Audience C.book) : ∀ᶠ m in atTop, ∀ᶠ i in f.fuse, ∀ (hm : m ≤ i.1), ∀ j k, j≠k → Cells.span C.S hm i.2 <
    separation (ceilSite C i.1 i.2 (s.x j)) (ceilSite C i.1 i.2 (s.x k)) := by
  obtain ⟨K,hK,hk,hc⟩ := exists_compact_subset (conf_open _) (generic_conf _ s.avoids)
  obtain ⟨r,hr,H⟩ := Gaps.someGrows C.S hK hc
  filter_upwards [C.S.shrinks.eventually (gt_mem_nhds hr)] with m h
  rw [Extraction.Order.fused, Extraction.Order.late]
  filter_upwards [f.per.cofinal.eventually H] with p hp
  filter_upwards [((chosen (S:=C.S) s.x).comp f.mesh.cofinal).eventually (mem_interior_iff_mem_nhds.mp hk)] with N hN hm j k hk
  have he := Gaps.gridSeparation C.S (fun j => ceilSite C (f.mesh N) (f.per p) (s.x j)) rfl (hp _ hN) k j hk.symm
  have ha := h.trans_le he
  rw [← C.S.embeds_scale (C.S.toDepth hm (f.per p))] at ha
  exact_mod_cast lt_of_mul_lt_mul_left ha (C.S.a_pos _).le

/-- Once the hierarchy levels for site offsets have been fixed, the same
exterior budget works on ANY paid origin object and even on variable objects
(e.g. a family indexed by actual fine sites). -/
lemma sampling (H : C.Makes) (hq : CenteredBook C f) (s : Audience C.book) (hj : s.n+1 ≤ J)
    (hl : ∀ {N p} (hm : m ≤ N) (he : l ≤ N), 3 * Cells.span C.S he p ≤ Cells.span C.S hm p / (8*(J+1))) (hle : m≤l)
    (ha : ∀ᶠ i in f.fuse, ∀ (hm : m ≤ i.1), ∀ j k, j≠k → Cells.span C.S hm i.2 <
      separation (ceilSite C i.1 i.2 (s.x j)) (ceilSite C i.1 i.2 (s.x k))) : ∃ A : ℝ, 0≤A ∧ ∀ᶠ i in f.fuse,
    ∀ ε, 0 ≤ ε → ∀ F, arrayTest C i.1 i.2 J m l ε F → ‖sample F s.tags (fun j => ceilSite C i.1 i.2 (s.x j.succ))‖ ≤ ε * A := by
  obtain ⟨j,hm,hh,A,hA,hB⟩ := ((eventually_ge_atTop m).and ((width (C:=C) J m).and ((Around.image_ s.tags hq).2))).exists
  refine ⟨A^s.n,pow_nonneg hA _,?_⟩
  filter_upwards [ha,(show ∀ᶠ i in f.fuse, Around.imageBudget s.tags A j i.1 i.2 from hB)] with i hi h ε hε F hF
  obtain ⟨h1,h2,h3⟩ := hF
  let T : Tiling (C.side i.1 i.2) := {center C.S i.2 h1 0 with kind := .site}
  let K := T.side.val/(8*(J+1))
  let y := fun j => ceilSite C i.1 i.2 (s.x j)
  have ht : (s.n+1)*(2*(2*K)) < T.side.val := by
    have := Nat.mul_div_le T.side.val (8*(J+1)); change (8*(J+1))*K ≤ T.side.val at this
    have hb : 2*((s.n+1)*(2*(2*K))) ≤ T.side.val := calc
      _ = (s.n+1)*(8*K) := by ring
      _ ≤ (J+1)*(8*K) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := by rwa [show (J+1)*(8*K)=8*(J+1)*K by ring]
    have h0 : 0 < T.side.val := T.side.property; omega
  refine pay H h (T:=T) (K:=K) (D:=Cells.span C.S h2 i.2) ((C.S.toDepth h2 i.2).count.property) (Around.inherits hle h2)
    (by have := hl (p:=i.2) h1 h2; change _ ≤ Cells.span C.S h1 _ / (8*(J+1)); omega)
    (Around.inherits hm h.1) (hh h1 h.1) ht hε y ?_ F ?_
  · exact hi h1
  intro o ho hh
  apply h3 (T.newly o) rfl rfl ho
  have hz : y 0 = 0 := by simp [y,s.center,ceilSite,show (fun _ : Axis => (0:ℤ))=(0:Cover) from rfl]
  exact hz ▸ hh

end YM.StressFlux.Matching
