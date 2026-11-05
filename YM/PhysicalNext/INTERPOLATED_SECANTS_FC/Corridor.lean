import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Frozen

/-!
# Assign no sharp price to the *derivative* of the singleton E expectation

Instead stay at fixed numeric beta on moderated *real* old-entry extensions of relative
price-distance `r` (about a small coupling power). Absolute low-term cancellations required
there on the whole ordered deficit family, with sharp pre-L coefficient, BEFORE taking repeated
input-amplitude derivatives. Those high derivatives on first integrals however can PAY coarsely
in `Hit` (no affine contraction assumed for them). Covers also coincident incoming beta, when
an unpriced motion of scalar and off-mask amplitudes from the given family is possible.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc.Content
open Function Filter Set Finset RG Lattice Wilson Push.Local Push.AbsoluteSums Push.AbsoluteSums.Ursell Trees Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {ι κ H : Type*}

def corridor (c r : ℝ) := Ioo (-r) (c+r)
lemma within_corridor {c r u : ℝ} (hr : 0<r) (hu : u∈Icc (0:ℝ) c) : u∈corridor c r := ⟨by linarith only [hr,hu.1], by linarith only [hr,hu.2]⟩
lemma corridor_open (c r : ℝ) : IsOpen (corridor c r) := isOpen_Ioo

variable (f : Content G n ι κ H) (A : Placement G n ι κ) (p : BudgetPoint)
structure Moving (path : ℝ → H) (b y a D γ q M r : ℝ) : Prop where
  charts (c t : ℝ) : 0<c → D ≤ c → t ∈ corridor c r → ∀ i U, Healthy p.threshold (A.reads i) U → Chart p.order (f.unforced b (path (t/c)) i) U
  paid (c t : ℝ) : 0<c → D ≤ c → t ∈ corridor c r → ∃ e : ι→ℝ, Ready A.reads p.B e (a+2) γ 1 q ∧ ∀ i (u : Reading G p (A.atom i)),
    let F := fun t => u.jet (f.unforced b (path (t/c)) i)
    ContDiffAt ℝ depth F t ∧ ∀ j≤depth, |iteratedDeriv j F t| ≤ e i
  low (c t : ℝ) : 0<c → D ≤ c → t ∈ corridor c r → ∃ e : Clusters ι → ℝ, (∀ z, 0 ≤ e z ∧ (z.1<2 → p.supBounds (A.cluster z).site
      (A.cluster z).support (f.tail A y b (path (t/c)) z) (e z))) ∧ Seated A.cluster p.B e a M

variable {f A p} {path : ℝ → H} {h : H} {c t y a D γ q M M' r b : ℝ}
namespace Moving
variable (hp : Moving f A p path b y a D γ q M r) (ha : 0 ≤ a) (hc : 0<c) (hD : D≤c) (ht : t ∈ corridor c r)
include hp hc hD

lemma positioning (z : Clusters ι) (u : Reading G p (A.cluster z)) : ∀ t∈corridor c r, Chart p.order (f.raw A b (path (t/c)) z) u.point := by
  intro t ht; rw [raw,cost_eq]; apply scale_chart; exact contDiffAt_prod
    (fun j _ => hp.charts _ _ hc hD ht _ _ (Disjoint.mono_left (covered A.reads z j) u.admitted))

include ht in
lemma raw_cost {N} (hN : N ≤ depth) : ∃ e : ι → ℝ, Ready A.reads p.B e (a+2) γ 1 q ∧
    ∀ z (u : Reading G p (A.cluster z)), let F := fun t => u.jet (f.raw A b (path (t/c)) z)
      ContDiffAt ℝ N F t ∧ |iteratedDeriv N F t| ≤ Cluster.expense p A.reads e N z := by
  obtain ⟨e,he,H⟩ := hp.paid _ _ hc hD ht; refine ⟨_,he,fun z u => ?_⟩
  have hh := Cluster.mixed_part p (Y:=A.reads) (o:=A.site) (fun i => (A.atom i).anchor) z _ (A.cluster z).anchor u.admitted N he.2.2.2.2.1
    (f:=fun t => f.unforced b (path (t/c))) ((show ∀ᶠ v in 𝓝 t, v∈corridor c r from (corridor_open c r).mem_nhds ht).mono fun v hv i => hp.charts _ _ hc hD hv i _)
    (fun i hi l hl hd => let h := H i ⟨_,hi,l,hl,hd⟩; ⟨h.1.of_le (Nat.cast_le.mpr hN),fun j hj => h.2 j (hj.trans hN)⟩) _ u.order u.bounds
  exact ⟨hh.1,hh.2 _ le_rfl⟩

abbrev trace (f : Content G n ι κ H) (A : Placement G n ι κ) (p : BudgetPoint) (y b : ℝ) (path : ℝ→H) (c : ℝ) (t : ℝ) (z : Clusters ι)
    (u : Reading G p (A.cluster z)) := u.jet (f.tail A y b (path (t/c)) z)

include ht ha in
lemma trace_value : (roots A.cluster p.B a).Box (trace f A p y b path c t) (M+Cluster.price p 1 γ q 0 2) := by
  obtain ⟨e,he,H⟩ := hp.raw_cost hc hD ht (Nat.zero_le _)
  obtain ⟨d,hd,hd'⟩ := hp.low _ _ hc hD ht
  let w (z : Clusters ι) := if 2≤z.1 then Cluster.expense p A.reads e 0 z else 0
  have hw : Seated A.cluster p.B w a _ := charged ha he (Y:=A.atom) (fun _ => rfl) 0 2
  have hz z : 0 ≤ w z := by unfold w; split; exact Cluster.expense_pos p e he.2.2.2.2.1 0 z; exact le_rfl
  refine ⟨_,seated_iff.mpr ⟨fun i => add_nonneg (hd i).1 (hz i),seated_add hd' hw⟩,fun z u => ?_⟩
  by_cases hZ : z.1<2
  · exact ((Reading.cost _ (hd z).1).mp ((hd z).2 hZ) u).trans (le_add_of_nonneg_right (hz z))
  rw [trace, tail, peeled,if_neg hZ,sub_zero]; exact (H z u).2.trans ((if_pos (show 2≤z.1 by omega) : w z=_).symm.le.trans (le_add_of_nonneg_left (hd z).1))

variable (h₀ : Deficit f A p h y a M')
include ht ha h₀ in
lemma trace_price : ∃ e : Clusters ι → ℝ, (roots A.cluster p.B a).Credits e (Cluster.price p 1 γ q depth 0) ∧ ∀ z (u : Reading G p (A.cluster z)),
    let F t := trace f A p y b path c t z u
    ContDiffAt ℝ depth F t ∧ |iteratedDeriv depth F t| ≤ e z := by
  obtain ⟨d,hd,H⟩ := hp.raw_cost hc hD ht (le_refl depth)
  let w (z : Clusters ι) := Cluster.expense p A.reads d depth z
  have hw : Seated A.cluster p.B w a (Cluster.price p 1 γ q depth 0) := by simpa only [Nat.zero_le,if_true] using! (charged ha hd (Y:=A.atom) (Q:=A.cluster) (fun _ => rfl) depth 0)
  refine ⟨w, seated_iff.mpr ⟨fun z => Cluster.expense_pos p d hd.2.2.2.2.1 depth z,hw⟩,?_⟩
  intro z u F
  let Y t := u.jet (f.raw A b (path (t/c)) z); let R (_ : ℝ) := u.jet (f.peeled y b z)
  have hF : F =ᶠ[𝓝 t] Y-R := by filter_upwards [(corridor_open c r).mem_nhds ht] with t ht using AnalyticBridge.VerifiedReset.left_sub
                                   (hp.positioning hc hD z u t ht) (h₀.peeled_chart z u _) u.order
  have hR : ContDiffAt ℝ depth R t := contDiffAt_const
  have hY : ContDiffAt ℝ depth Y t := (H z u).1
  refine ⟨(hY.sub hR).congr_of_eventuallyEq hF,?_⟩
  rw [hF.iteratedDeriv_eq, iteratedDeriv_sub hY hR]; unfold R; rw [iteratedDeriv_const, if_neg (by have h:=deep; omega),sub_zero]
  exact (H z u).2

include ha h₀ in
lemma change_tail (hr : 0<r) : let cost := Cluster.price p 1 γ q depth 0
    let mass := M + Cluster.price p 1 γ q 0 2 + M
    (roots A.cluster p.B a).Box (fun z (u : Reading G p (A.cluster z)) => u.jet (f.tail A y b (path 1) z)-u.jet (f.tail A y b (path 0) z))
      (c * (interCoeff*mass/r+r^(depth-1)*cost)) := by
  obtain ⟨hC,h⟩ := Classical.choose_spec (interpolation depth (by have := deep; omega))
  intro cost mass; refine Tax.Dual.box (fun o s u e he => ?_)
  let F := fun t => ∑ z∈s,e z * trace f A p y b path c t z (u z)
  have hF t (ht : t∈corridor c r) : ContDiffAt ℝ depth F t ∧ |F t| ≤ mass ∧ |iteratedDeriv depth F t| ≤ cost := by
    obtain ⟨d,hd,H⟩ := hp.trace_price ha hc hD ht h₀
    obtain ⟨e',h',hy⟩ := hp.low _ _ hc hD ht
    have hv : (roots A.cluster p.B a).Box (fun i u => iteratedDeriv depth (fun t => trace f A p y b path c t i u) t) cost := ⟨d,hd,fun i u => (H i u).2⟩
    refine ⟨smooth_sum _ fun i _ => contDiffAt_const.mul (H i (u i)).1, ((hp.trace_value ha hc hD ht).dual o s u e he).trans
      (le_add_of_nonneg_right (budget_nonneg (hy 0))),?_⟩
    unfold F; rw [iteratedDeriv_fun_sum (fun i _ => contDiffAt_const.mul (H i (u i)).1)]; simp_rw [iteratedDeriv_const_mul_field]; exact hv.dual o s u e he
  have hD (t) (ht : t∈corridor c r) := (hF t ht).1.differentiableAt (Nat.cast_ne_zero.mpr (by have := deep; omega))
  have heq : ∑ i∈s,e i * ((u i).jet (f.tail A y b (path 1) i) - (u i).jet (f.tail A y b (path 0) i)) = F c - F 0 := by unfold F trace; rw [show c/c=1 from div_self hc.ne',zero_div]; simp_rw [mul_sub,sum_sub_distrib]
  rw [heq]; convert (interval_cost (f:=F) ⟨le_rfl,hc.le⟩ ⟨hc.le,le_rfl⟩ (continuousOn_of_forall_continuousAt
    fun t ht => (hD t (within_corridor hr ht)).continuousAt) fun t ht => let hx := within_corridor hr (Ioo_subset_Icc_self ht)
      ⟨hD t hx,h (a:=-r) (b:=c+r) hr (by linarith only [hc,hr]) hF t hx⟩) using 1
  simp [abs_of_pos hc, interCoeff]

omit hc hD in
include hp ha h₀ in
theorem change (hD : 0≤D) (hr : 0<r) : let cost := Cluster.price p 1 γ q depth 0
    let mass := M + Cluster.price p 1 γ q 0 2 + M
    (roots A.regular p.B a).Box (fun z (u : Reading G p (A.regular z)) => u.jet (f.logarithm A y b (path 1) z)-u.jet (f.logarithm A y b (path 0) z))
      (D*(interCoeff*mass/r + r^(depth-1)*cost)) := by
  intro cost mass; let C := interCoeff*mass/r + r^(depth-1)*cost
  have hx : (roots A.cluster p.B a).Dual (fun z (u : Reading G p (A.cluster z)) => u.jet (f.tail A y b (path 1) z)-u.jet (f.tail A y b (path 0) z)) (D*C) := by
    intro x s u e he; apply ge_of_tendsto (Filter.Tendsto.mul_const C (tendsto_id (x:=𝓝 D) |>.mono_left (nhdsWithin_le_nhds (s:=Ioi D))))
    filter_upwards [self_mem_nhdsWithin] with c (hc : c∈Ioi D) using (hp.change_tail ha (lt_of_le_of_lt hD hc) hc.le h₀ hr).dual x s u e he
  obtain ⟨e,he,H⟩ := hx.box
  refine ⟨Sum.elim e (fun (_:ℕ) => 0),seated_iff.mpr ⟨fun j => j.casesOn he.positive (fun i => le_rfl),?_⟩, fun j u => ?_⟩
  · simpa only [add_zero] using! seated_join (seated_iff.mp he).2 (show Seated A.aligned p.B (fun (_:ℕ) => (0:ℝ)) a 0 from fun o => by simp [SumBudget])
  cases j; exact H _ u
  simp only [logarithm,Sum.elim_inr,sub_self,abs_zero,le_refl]
end Moving
end YM.PhysicalNext.InterpolatedSecantsFc.Content
