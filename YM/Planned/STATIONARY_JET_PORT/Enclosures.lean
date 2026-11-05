import YM.Planned.STATIONARY_JET_PORT.AtHome
import YM.Planned.STATIONARY_JET_PORT.Speakers

set_option warningAsError false

/-! Fixed-L Taylor remainder service, native real color entry sup. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Filter Function Set Metric Lattice Matrix Push Push.Uniform RG Precision Tree Bid
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace

section Taylor
variable {ι E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} {k : ℕ} {C r : ℝ}

lemma lipschitzLower (h : Convex ℝ s) (hf : ∀ x∈s, ContDiffAt ℝ ω f x)
    (he : ∀ x∈s, ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ C) {x y : E} (hx : x∈s) (hy : y∈s) :
    ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C*‖x-y‖ := by
  apply h.norm_image_sub_le_of_norm_fderiv_le (fun x hx => (hf x hx).differentiableAt_iteratedFDeriv (by simp)) _ hy hx
  intro z hz; rw [norm_fderiv_iteratedFDeriv]; exact he z hz

/-- If matching at zero, can certifiably spend order EVEN on values inside the
real balls. Deliberately don't optimize factorial. Includes genuine jet errors
(including difference in value, i=0, even away from 0).
No proof of small higher field terms *before* obtaining uniform constants
at the prices below. -/
lemma jetSmall (_hr : 0<r) (hf : ∀ x∈ball 0 r, ContDiffAt ℝ ω f x ∧ ‖iteratedFDeriv ℝ k f x‖ ≤ C) (hc : 0 ≤ C)
    (h : ∀ i < k, iteratedFDeriv ℝ i f 0=0) (i : ℕ) (hi : i ≤ k) :
    ∀ x∈ball 0 r, ‖iteratedFDeriv ℝ i f x‖ ≤ C*‖x‖^(k-i) := by
  induction hi using Nat.decreasingInduction with
  | self => intro x hx; simpa using (hf x hx).2
  | of_succ i hi ih =>
    intro x hx
    let v := ‖x‖
    let s := closedBall (0:E) v
    have hs : s ⊆ ball 0 r := closedBall_subset_ball (show v < r by simpa using hx)
    let K := C*v^(k-(i+1))
    have he (x : E) (hx : x∈s) := hf x (hs hx)
    have ht (x : E) (hx : x∈s) : ‖iteratedFDeriv ℝ (i+1) f x‖ ≤ K :=
      (ih x (hs hx)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hx) _) hc)
    have hv := lipschitzLower (convex_closedBall ..) (fun x hx => (he x hx).1) ht (x:=x) (mem_closedBall_zero_iff.mpr le_rfl)
      (y:=0) (mem_closedBall_zero_iff.mpr (by unfold v; simp))
    rw [h i hi,sub_zero,sub_zero] at hv
    refine hv.trans_eq ?_
    unfold K v; rw [mul_assoc, ← pow_succ]; congr 2; omega
end Taylor

variable {G : Gauge} {c f s s' : Side} {S : StepData c f} {B : Forest S.ratio}
    {p q : Clip} {R R' : PathData G} {Q : KernelChoices} {μ C Λ : ℝ} {N j : ℕ}
    {A : Before G μ C j Q (N+3)} {O : ChartRatio G}
    {g : In G c → AxisChart G B} {K : ℕ}

abbrev volumePrice (G : Gauge) (c : Side) (K N : ℕ) (a C : ℝ) :=
  (Fintype.card (Site c):ℝ) * reception G K N a C
abbrev loud (Q : In G c → ℝ) : Positions (Primary c G) → ℝ := Q ∘ tint G _

lemma Busy.indoor {l : Primary c G → Site s} {a C : ℝ} {k : ℕ} {x : Positions (Primary c G)} {Q : In G c → ℝ}
    (h : Busy l K N a C Q (tint G _ x)) (hk : k≠0) (ht : k ≤ N) :
    ‖iteratedFDeriv ℝ k (loud Q) x‖ ≤ volumePrice G c K k a C := by
  have he := h.2.2.2.1; rw [ContinuousLinearEquiv.symm_apply_apply] at he
  -- don't have multiplicity? Busy includes explicit norm read. use swallow
  have hF := h.1.comp x (tint G (Exterior.Body 1 c)).contDiff.contDiffAt
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) (reception_pos h.2.1 h.2.2.1).le) (fun v => ?_)
  have ht := h.2.2.2.2 k hk ht (fun i => tint G _ (v i))
  rw [swallow (u:=Q) hF] at ht; simpa only [ContinuousLinearEquiv.symm_apply_apply, Real.norm_eq_abs, loud,volumePrice] using ht

lemma afterSameJets {k M : ℕ} {l : Primary c G → Site s} {m : Primary c G → Site s'} {a v b D r : ℝ}
    {u w : In G c → ℝ} (hr : 0 < r)
    (h : ∀ x ∈ ball (0 : Positions (Primary c G)) r, Busy l K N a b u (tint G _ x) ∧ Busy m K M v D w (tint G _ x))
    (hk : k ≠ 0) (hi : k ≤ N) (hj : k ≤ M) (he : ∀ j < k, SameJet j u w) (i : ℕ) (hI : i ≤ k) :
    ∀ x ∈ ball (0:Positions (Primary c G)) r,
      ‖iteratedFDeriv ℝ i (loud u) x-iteratedFDeriv ℝ i (loud w) x‖ ≤
        (volumePrice G c K k a b + volumePrice G c K k v D) * ‖x‖^(k-i) := by
  let L := tint G (Exterior.Body 1 c)
  have ht x (hx : x∈ball (0:Positions (Primary c G)) r) : ContDiffAt ℝ ω (loud u) x ∧ ContDiffAt ℝ ω (loud w) x :=
    ⟨(h x hx).1.1.comp x L.contDiff.contDiffAt,(h x hx).2.1.comp x L.contDiff.contDiffAt⟩
  intro x hx
  obtain ⟨hf,hg⟩ := h x hx
  have hw (i : ℕ) {x : Positions (Primary c G)} (hx : x∈ball 0 r) :=
    iteratedFDeriv_sub_apply (𝕜:=ℝ) (i:=i) ((ht x hx).1.of_le le_top) ((ht x hx).2.of_le le_top)
  rw [← hw i hx]
  apply jetSmall hr _ (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (reception_pos hf.2.1 hf.2.2.1).le)
    (mul_nonneg (Nat.cast_nonneg _) (reception_pos hg.2.1 hg.2.2.1).le)) _ i hI x hx
  · intro x hx
    refine ⟨(ht x hx).1.sub (ht x hx).2,?_⟩
    obtain ⟨hf,hg⟩ := h x hx
    rw [hw k hx]; exact (norm_sub_le ..).trans (add_le_add (hf.indoor hk hi) (hg.indoor hk hj))
  intro j hj
  rw [hw j (mem_ball_self hr)]
  apply sub_eq_zero.mpr
  obtain ⟨hu,hv,he⟩ := he j hj
  have rotate (f : In G c → ℝ) (hf : ContDiffAt ℝ ω f 0) :=
    iter_lin_at (k:=j) (L:=L.toContinuousLinearMap) (show ContDiffAt ℝ (j:ℕ) f (L.toContinuousLinearMap 0) by rw [map_zero]; exact hf.of_le le_top)
  change iteratedFDeriv ℝ j (u ∘ L.toContinuousLinearMap) 0 = iteratedFDeriv ℝ j (w ∘ L.toContinuousLinearMap) 0
  rw [rotate u hu,rotate w hv,map_zero,he]

-- reduce to literal classical and thermal clients, no period transport or free new coefficients.

section ClassicalRead
variable (hg : A.Service B p R g) (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) (t : S.Choices)
    {μ' C' Λ' : ℝ} (hP : R'.Bounds q μ' C' Λ')
    (J : BareRates.pre G μ' C' (N+3))
local notation "Y" => (A.tables p S.patch)
include hg hp hK hj ht hP t

theorem onMeeting (hi : 5 ≤ N+3) (hm : ClassicalMatch B p q R R' g) :
    let U y := tested B t p R y (g y)
    let W y := mainTerm (n:=c) q R' (represent y)
    let M := townCost G
    let r := min (Y).horizon 1
    let C := reception G M 5 (classicalRate Y N) (classicalBill Y N) + reception G M 5 (dial μ' (N+3)) (BareRates.bill J q)
    0 < r ∧ 0 < C ∧ ∀ i ≤ 5, ∀ x∈ball (0 : In G c) r, ∀ v : Fin i → In G c,
      let L := tint G (Exterior.Body 1 c)
      |iteratedFDeriv ℝ i U x v-iteratedFDeriv ℝ i W x v| ≤ (Fintype.card (Site c):ℝ)*C * ‖L.symm x‖ ^ (5-i) * ∏ j, ‖L.symm (v j)‖ := by
  intro U W M r P
  let L := tint G (Exterior.Body 1 c)
  have hr : 0<r := lt_min hg.x_pos zero_lt_one
  let a : Primary c G → Site f := account B G ∘ Sum.inl
  have hf x (hx : x∈ball 0 r) := (Counter.service hg hp hK hj ht t).classical (x:=x) (ball_subset_ball (min_le_left ..) hx)
  have hw x (hx : x∈ball (0:Positions (Primary c G)) r) := bareSocket c J hP (x:=x) (ball_subset_ball (min_le_right ..) hx) 0
  have hA x (hx : x∈ball (0:Positions (Primary c G)) r) :
      Busy a M (N+3) (classicalRate Y N) (classicalBill Y N) U (L x) ∧
        Busy (throat c G) M (N+3) (dial μ' (N+3)) (BareRates.bill J q) W (L x) := by
    obtain ⟨ha,hb,hc,h⟩ := hf x hx
    obtain ⟨hd,-,hs,hM,H,-⟩ := hw x hx
    exact ⟨ampere ((town (G:=G) B).comp Sum.inl_injective) h ha hb hc,ampere (device c G) H hd hs hM⟩
  let B₁ := hA 0 (mem_ball_self hr)
  have hP₁ : 0<P := add_pos (reception_pos B₁.1.2.1 B₁.1.2.2.1) (reception_pos B₁.2.2.1 B₁.2.2.2.1)
  refine ⟨hr,hP₁,fun i hI x hx v => ?_⟩
  let z := L.symm x
  have hz : z∈ball 0 r := by
    apply mem_ball_zero_iff.mpr; exact (tint_inv_le x).trans_lt (mem_ball_zero_iff.mp hx)
  obtain ⟨ha,-,-,_⟩ := hf z hz
  obtain ⟨hd,_⟩ := hw z hz
  have he := afterSameJets hr hA (show 5≠0 by norm_num) hi hi (fun j hj => hm j (by omega) t) i hI z hz
  let A' := iteratedFDeriv ℝ i (loud U) z-iteratedFDeriv ℝ i (loud W) z
  change |iteratedFDeriv ℝ i U x v - iteratedFDeriv ℝ i W x v| ≤ _
  nth_rewrite 1 2 [← show L z=x from L.apply_symm_apply x]
  rw [swallow (u:=U) ha,swallow (u:=W) hd]
  change ‖A' _‖ ≤ _
  apply (A'.le_opNorm (fun i => L.symm (v i))).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact he.trans_eq (by unfold volumePrice P; ring)
end ClassicalRead
end YM.Planned.JetPort
