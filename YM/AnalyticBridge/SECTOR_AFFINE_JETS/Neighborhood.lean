import YM.AnalyticBridge.SECTOR_AFFINE_JETS.MarkedGram
import YM.Push.FREE_RESOLVENT.Growth
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur



/-!
# Marked precision jets permit a period-uniform neighborhood

Estimates on the unmasked V function with sector, forest, label paths held
fixed. This can cross a geometry boundary; no assertion about other flags
than the tested base field's. Get both a genuine `TestD.Knew`, and gap even at
V' in this same ball. Not simply a continuous neighborhood chosen after the
period and number of holes. No shift projected away.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Push.Uniform (Allows bolt)
open YM.FreeResolvent (Mark Bundle native Gap)
open YM.FreeResolvent.Mark (Bill)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {x σ d M r : ℝ}

section adapters
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {Q : Matrix ι ι ℝ} {L : Matrix ι κ ℝ} {p : ι → Site c} {q : κ → Site c}

lemma polar_schur {A : PriceCoords G c → Matrix ι κ ℝ} {k : ℕ} {x : PriceCoords G c}
    (hp : Polar x p q A k d M) : (native c).Schur p q d M (A x) := by
  have he := hp.bound [] (by simp); rw [zeroth] at he; exact he.reclaim

lemma priced_pour (h : (native c).Schur p q d M L) (hM : 0 ≤ M) : Schur.Pours L p q d M := by
  refine ⟨hM,fun i => h.rows.bound i,fun j => ?_⟩
  simp_rw [separation_comm _ (q j)]; exact h.cols.bound j

lemma funded_gap (h : YM.FreeResolvent.Gap Q r) : Gapped Q r :=
  fun x => by rw [sumSq_dot]; exact h.lower x
lemma fund_gap (h : Gapped Q r) : YM.FreeResolvent.Gap Q r :=
  ⟨fun x => by rw [← sumSq_dot]; exact h x⟩

lemma price_knowledge {A : PriceCoords G c → Matrix ι ι ℝ} {k : ℕ} {x : PriceCoords G c}
    (hp : Polar x p p A k σ M) (he : d ≤ σ) (h : YM.FreeResolvent.Gap (A x) r) :
    Knew (marks G c d) (native c) p bolt x k σ M r 1 A :=
  ⟨hp.smooth,h,polar_schur hp,fun l _ hl => by rw [mul_one]; exact (Polar.toBundle hp he).bound l hl⟩
end adapters

section lipschitz

lemma directional_bill {ι κ U : Type} [Fintype ι] [Fintype κ]
    {p : ι → Site c} {q : κ → Site c} (o : Site c) (k : ℕ) {B : PriceCoords G c} {A : PriceCoords G c → Matrix ι κ ℝ}
    (v : U → PriceCoords G c) (l : List U) (h : ContDiffAt ℝ l.length A B)
    (hp : ∀ w : Fin l.length → Coord G c,
      Bill (marks G c d) (native c) p q (List.ofFn w) σ M (jet bolt A (List.ofFn w) B))
    (hm : 0 ≤ M) (hd : 0 < d) {γ : ℝ} (hγ : 0 ≤ γ)
    (hl : ∀ i∈l, ∀ j : Coord G c, |v i j| ≤ γ*Mark.hill (native c) o k (coordRoot j)) :
    Bill (Mark.radial U (native c) o k) (native c) p q l σ
      (paramPrice G (d/2)^l.length*((γ*Mark.polynomial (d/2) k)^l.length*M)) (jet v A l B) := by
  refine Mark.activated v h (d:=d) ?_ hm hγ hl (half_pos hd) (le_of_eq (by ring)) (param_volume G c (half_pos hd))
  intro w
  convert hp w
  funext j; simp only [bolt, Pi.single_apply]; congr!


lemma touch (G : Gauge) {c : Side} {ι : Type} [Fintype ι] {a : ι → Site c} {n : ℕ}
    {C γ K : ℝ} {Q : PriceCoords G c → Matrix ι ι ℝ}
    (h : ∀ y : PriceCoords G c, ‖y‖ ≤ r → Polar y a a Q n σ C) (hn : 1 ≤ n)
    (hc : 0 ≤ C) (hσ : 0 < σ) (hp : (native c).Volume a (σ-γ) K)
    (x y : PriceCoords G c) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    (native c).Schur a a γ (K*((paramPrice G (σ/2)*C)*‖y-x‖)) (Q y-Q x) := by
  let d := σ/2; let f (i j : ι) (x) := Q x i j
  let M := paramPrice G d
  have hM : 0 ≤ M := zero_le_one.trans (param_pos ..)
  refine FreeResolvent.Cost.Schur.of_point (mul_nonneg (mul_nonneg hM hc) (norm_nonneg _)) ?_ hp hp
  intro i j
  let e := (native c).weight σ (a i) (a j)
  have he : 0<e := (native c).weight_pos ..
  let S := Metric.closedBall (0 : PriceCoords G c) r
  have ha (u) (hu : u∈S) : Polar u a a Q n σ C := h u (by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hu)
  have hs (u) (hu : u∈S) : ContDiffAt ℝ 1 (f i j) u := by
    refine (evaluate i j).contDiff.contDiffAt.comp _ ?_
    exact (ha u hu).smooth.of_le (by exact_mod_cast hn)
  have hl (u : PriceCoords G c) (hu : u∈S) : ‖fderiv ℝ (f i j) u‖ ≤ e⁻¹ * (M*C) := by
    refine (fderiv ℝ _ u).opNorm_le_bound (mul_nonneg (inv_pos.mpr he).le (mul_nonneg hM hc)) ?_
    intro z
    let l := [z]
    have hj : l.length ≤ n := hn
    have hQ : ContDiffAt ℝ l.length Q u := smooth_of_le (ha u hu).smooth hj
    have hV := directional_bill (p:=a) (q:=a) (0:Site c) 0 id l hQ (fun w => (ha u hu).bound
        _ (by rw [List.length_ofFn]; exact hn)) hc hσ (norm_nonneg z) ?_
    rotate_left
    · intro i hi j
      rw [List.mem_singleton] at hi
      subst i
      simp only [Mark.hill, pow_zero, mul_one]; exact norm_le_pi_norm z j
    have hL := hV.row.entry i j
    rw [← entry id l hQ] at hL
    simp only [l,Mark.pay,Mark.radial,pow_zero,inv_one,one_mul,pow_one,
      Mark.polynomial, mul_one,List.length_cons,List.length_nil,Nat.zero_add] at hL
    change e*‖jet id (f i j) [z] u‖ ≤ M*(‖z‖*C) at hL
    have hz : jet id (f i j) [z] u=fderiv ℝ (f i j) u z :=
      iteratedFDeriv_one_apply ..
    rw [hz] at hL
    rw [mul_assoc, inv_mul_eq_div, le_div_iff₀ he, mul_comm]; exact hL.trans_eq (by ring)
  rw [Matrix.sub_apply,(native c).weight_neg]
  have ht := (convex_closedBall (0:PriceCoords G c) r).norm_image_sub_le_of_norm_fderiv_le (f:=f i j)
    (fun x hx => (hs x hx).differentiableAt one_ne_zero) hl (show x ∈ S by simpa [S] using hx) (show y ∈ S by simpa [S] using hy)
  rw [mul_assoc] at ht
  change |f i j y-f i j x| ≤ e⁻¹ * ((M * C) * ‖y-x‖)
  exact ht
end lipschitz

/-- Uniform flat-comparison gap (of actual active A at flags-correct V)
now combined with marked costs and supports. Perturb in a fixed *post-L*
parameter ball of V with flags fixed. -/
theorem precision (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r s M η : ℝ, 0<r ∧ 0<s ∧ 0<M ∧ 0<η ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (k : S.Choices) (B : PriceCoords G c), ‖B‖≤r →
    let a := Wisps.front A F (G:=G) (x:=x); let Q:=profileGram T x V A F k
    ContDiffAt ℝ ω (profileD T x V A F k) B ∧
    Polar B (Wisps.down S) a (profileD T x V A F k) n s M ∧
    ContDiffAt ℝ ω Q B ∧ Polar B a a Q n s M ∧
    YM.FreeResolvent.Gap (Q B) η ∧ Knew (marks G c s) (native c) a bolt B n s M η 1 Q := by
  obtain ⟨r,s,M,hr,hs,hM,H⟩ := input_polar G P Pt hk (n+1)
  obtain ⟨η,hη,hw⟩ := YM.Next.SectorChange.Gap.not_flat G P Pt hk
  let E := priceFiber P G s
  let D := paramPrice G (s/2)
  have he : 0 < E := priceFiber_pos ..
  have hD : 1 ≤ D := param_pos ..
  have hK : 0 < E*(D*M) := mul_pos he (mul_pos (zero_lt_one.trans_le hD) hM)
  let C := η/2 / (E*(D*M)); let R := min r C
  refine ⟨R,s,M,η/2,lt_min hr (div_pos (by positivity) hK),hs,hM,half_pos hη,?_⟩
  filter_upwards [H,hw] with x hx hh
  intro c f S T hP hf hT A F V hA k B hB a Q
  have hi : YM.FreeResolvent.Gap (Q 0) η := ⟨fun v => by
    unfold Q profileGram; rw [field_zero]; exact hh S T hP hf hT A F k V hA v⟩
  have hs' := hx S T hP hf hT A F V k hA
  have hb : ‖B‖≤r := hB.trans (min_le_left ..)
  obtain ⟨hm,h,hQ⟩ := hs' B hb
  have hp : Polar B a a Q n s M := thin hQ (by omega) le_rfl le_rfl
  have hL := gram_analytic T x k A F hm
  have hvB : (native c).Volume a (s-0) E := by
    rw [sub_zero]; unfold E; rw [← hP]; exact (fiber_volume S G hs _ _ _).1
  have ht := touch G (fun B H => (hs' B H).2.2) (Nat.le_add_left ..) hM.le
    hs hvB 0 B (by rw [norm_zero]; exact hr.le) hb
  rw [sub_zero,← mul_assoc E] at ht
  have hv : YM.FreeResolvent.Gap (Q B) (η/2) := by
    apply (hi.perturb ht).mono
    have hu := (le_div_iff₀ hK).1 (hB.trans (min_le_right ..))
    unfold D at hu; linarith
  exact ⟨hm,thin h (Nat.le_succ _) le_rfl le_rfl,hL,hp,hv,price_knowledge hp le_rfl hv⟩
end YM.AnalyticBridge.SectorAffine
