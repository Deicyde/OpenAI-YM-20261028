import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Point
import YM.Push.SECTOR_MEASURE.Presented

/-!
# Root budgets for the selected affine source - the two `plotted`

Jet on the path-letter field plus the actual value bound on each used
plaquette, not requiring a common gauge along a long stencil. Path
coefficients in their period conventions (do NOT drop winding in costs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset

open Filter Function Lattice Wilson RG Precision Pressure Tree
open YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD
open YM.Push.Uniform (bolt Allows Requests travelCost)
open YM.Work (E03.sep_walk)
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c m : Side} {R L k n : ℕ} {C M K Q s σ d t r κ : ℝ} {p : Site m → Site c}

structure Letters (U : PriceCoords G c → Config G m) (p : Site m → Site c) (n : ℕ) (C : ℝ) : Prop where
  step (y : Site m) (i : Axis) : separation (p y) (p (y+Lattice.step i)) ≤ 1
  use (i : Bond m) : Requests Set.univ (fun y => U y i) coordRoot (p i.1) 1
  through (i : Bond m) : Allows n (fun y => G.mat (U y i)) 0 C

namespace Letters
variable {U : PriceCoords G c → Config G m} {L : ℕ}
lemma travel_use (h : Letters U p n C) (i : Site m) (w : Walk) (hw : w.length ≤ L) :
    Requests Set.univ (fun y => travel (U y) i w) coordRoot (p i) (L+1) := by
  intro u _ v _ he
  apply travel_near p h.step _ _ _ _ L hw
  intro j hj; exact h.use j _ (Set.mem_univ u) _ (Set.mem_univ v) (fun x hx =>
    he x ((separation_triangle (p i) (p j.1) _).trans (Nat.add_le_add hj hx)))
lemma scaled_use {p : Site c} {X : Type} {u : PriceCoords G c → X} (h : Requests Set.univ u coordRoot p L) (t : ℝ) :
    Requests Set.univ (fun x => u (t • x)) coordRoot p L := fun x _ y _ he => h _ (Set.mem_univ _) _ (Set.mem_univ _)
      (fun i hi => by change t • x i=t • y i; rw [he _ hi])
lemma through_travel (h : Letters U p n C) (hs : 0 ≤ s) (ht : s ≤ 1) (hd : 0 ≤ d) (i : Site m)
    (w : Walk) (hl : w.length ≤ L) : Point (G:=G) 0 (p i) d n (fun y => G.mat (travel (U (s • y)) i w))
      (Real.exp (n*d*(L+1:ℕ))*travelCost G n L C) := by
  let X := s • ContinuousLinearMap.id ℝ (PriceCoords G c)
  have hX : ‖X‖ ≤ 1 := by unfold X; rw [norm_smul, Real.norm_of_nonneg hs]; exact (mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le).trans ht
  have he := Push.Uniform.travel_jets (U:=U) h.through i hl
  refine Point.of_support (Through.control (pre_short (f:=fun y => G.mat (travel (U y) i w)) (x:=0) X (X.map_zero.symm ▸ he) hX)) (scaled_use
    (fun u hu v hv ht => congr_arg G.mat (h.travel_use i w hl u hu v hv ht)) s : Requests Set.univ (fun y => G.mat (travel (U (s • y)) i w)) coordRoot (p i) (L+1)) hd
end Letters

section cost
variable (G : Gauge)
private def passCost (k : ℕ) (K C : ℝ) :=
  G.colorScale⁻¹*((2:ℝ)^k*(((2:ℝ)^k*(K*(G.colorScale*C)))*K))
private lemma pass_pos (hK : 0<K) (hC : 0<C) : 0<passCost G k K C := by unfold passCost; have := G.colorScale_pos; positivity

private abbrev op {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (j : E →L[ℝ] F) := ‖j‖
variable {G}
lemma carry_cost {x : PriceCoords G c} {U : PriceCoords G c → G.El} {V : PriceCoords G c → G.Color} {p : Site c}
    (h : Point x p σ k (fun y => G.mat (U y)) K) (hx : Point x p σ k V C) :
    Point x p σ k (fun y => G.adjoint (U y) (V y)) (passCost G k K C) := by
  let L := G.projectColor.toContinuousLinearMap
  have hL : op (E:=G.Mat) (F:=G.Color) L ≤ G.colorScale⁻¹ := by
    refine L.opNorm_le_bound (inv_nonneg.mpr G.colorScale_pos.le) fun u => ?_
    rw [mul_comm,← div_eq_mul_inv]; exact G.project_norm u
  let J := G.colorMat.toContinuousLinearMap
  have hJ : op (F:=G.Mat) (E:=G.Color) J ≤ G.colorScale := J.opNorm_le_bound G.colorScale_pos.le (fun v => (G.colorMat_norm v).le)
  have hb {X Y : PriceCoords G c → G.Mat} {A B : ℝ} (h : Point x p σ k X A) (hp : Point x p σ k Y B) :
      Point x p σ k (fun z => X z * Y z) (2^k*(A*B)) := by
    simpa only [one_mul,ContinuousLinearMap.mul_apply'] using (Point.multiply
      (ContinuousLinearMap.mul ℝ G.Mat) (ContinuousLinearMap.opNorm_mul_le ℝ G.Mat) h hp)
  let T := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).toContinuousLinearMap
  have hT : op (E:=G.Mat) (F:=G.Mat) T ≤ 1 := T.opNorm_le_bound zero_le_one (fun x => by change ‖star x‖ ≤ _; simp)
  have hm := h.line hT; rw [one_mul] at hm
  exact (hb (hb h (hx.line hJ)) hm).line hL

/-- Pay polynomial true-length debt uniformly under any chosen positive
real decay κ, provided using sufficiently small location weights even
when consuming shifts. Allows the *target* vector of the transported
term to be budgeted in its own column location. -/
lemma carried (G : Gauge) (hκ : 0 < κ) (k : ℕ) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 < M) :
    ∃ d N : ℝ, 0<d ∧ 0<N ∧ ∀ {c m : Side} (U : PriceCoords G c → Config G m) (p : Site m → Site c), Letters U p k C →
    ∀ (s t : ℝ), 0≤t → 0≤s → s≤1 →
    ∀ i : Site m, ∀ l : Walk, ∀ B : PriceCoords G c → G.Color, ∀ (w : ℝ), 0≤w → w≤d →
    Point 0 (p (stop i l)) w k B (M*t) →
      Point 0 (p i) w k (fun z => G.adjoint (travel (U (s • z)) i l) (B z))
        (N*Real.exp (κ*l.length)*t) := by
  let r := κ/6
  have hr : 0<r := by unfold r; positivity
  obtain ⟨A,hA,HA⟩ := travel_coupon G k C hC hr
  let d := r/(k+1:ℕ)
  have hd : 0<d := by unfold d; positivity
  have hh : k*d ≤ r := by
    have he : d*(k+1:ℕ)=r := div_mul_cancel₀ _ (by positivity)
    push_cast at he; linarith only [he,hd]
  let X := Real.exp r * A; let N := passCost G k X M
  refine ⟨d,N,hd,pass_pos G (mul_pos (Real.exp_pos _) hA) hM,?_⟩
  intro c m U p hp s t ht hs hv i l B w hw hb h
  let R := Real.exp (r*l.length)
  have hL : k*w ≤ r := le_trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)) hh
  have hu := h.shift (Work.E03.sep_walk p hp.step i l) hw
  have hj := Real.exp_monotone (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg l.length))
  have hm := hu.mono le_rfl (mul_le_mul_of_nonneg_right hj (mul_nonneg hM.le ht))
  have hg : Point (G:=G) 0 (p i) w k (fun y => G.mat (travel (U (s • y)) i l)) (X*(R*R)) := by
    apply (hp.through_travel hs hv hw i l (le_refl l.length)).mono le_rfl
    have hk : Real.exp (k*w*((l.length+1:ℕ):ℝ)) ≤ R*Real.exp r := by
      unfold R; rw [← Real.exp_add]
      apply Real.exp_monotone
      have hf := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (l.length+1))
      push_cast at *; linarith only [hf]
    apply le_trans (mul_le_mul_of_nonneg_left (HA l.length) (Real.exp_pos _).le)
    exact (mul_le_mul_of_nonneg_right hk (mul_nonneg hA.le (Real.exp_pos _).le)).trans_eq (by unfold X R; ring)
  have hR : 1≤R := Real.one_le_exp (by positivity)
  have hj := carry_cost hg hm
  refine hj.mono le_rfl ?_
  have he : Real.exp (κ*l.length)=R^5 * R := by unfold R r; rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [he]; calc passCost G _ _ _ = N*R^5*t := by unfold N passCost R; ring
                _ ≤ N*(R^5*R)*t := by apply mul_le_mul_of_nonneg_right _ ht; refine mul_le_mul_of_nonneg_left ?_ ?_
                                      · exact le_mul_of_one_le_right (by unfold R; positivity) hR
                                      exact (pass_pos G (mul_pos (Real.exp_pos _) hA) hM).le
end cost
section values
variable {U : PriceCoords G c → Config G m}
lemma face_cost (h : Letters U p n C) (o : Cell m)
    (hs : 0 ≤ s) (ht : s ≤ 1) (hd : 0 ≤ σ)
    (hx : ‖G.curvature (faceValue (U 0) o)‖ ≤ K*t) (hh : (curvatureCost G * travelCost G n 4 C)*s ≤ K*t) :
    Point 0 (p o.1) σ n (fun y => G.curvature (faceValue (U (s • y)) o)) (Real.exp (n*σ*5)*(K*t)) := by
  refine Point.of_support (Through.contract (f:=fun y => G.curvature (faceValue (U y) o)) ?_ hs ht hx hh) (R:=5) ?_ hd
  · exact Through.control (curvature_price (U:=fun y => faceValue (U y) o) (Push.Uniform.travel_jets (U:=U) h.through _ (le_refl 4)))
  intro u hu v hv he; apply congr_arg G.curvature
  exact Letters.scaled_use (h.travel_use _ (square o.2.val.1 o.2.val.2) (le_refl 4)) s _ hu _ hv he

/-- Through cut labels collapsed geometrically; preserves counting
price with true `Slot.length`. -/
lemma bound_plotted (G : Gauge) (hσ : 0<σ) (k : ℕ) {D L C : ℝ} (A : Clip)
    (hC : 0≤C) (hD : 0<D) :
    ∃ d M : ℝ, 0<d ∧ 0<M ∧ ∀ {m c : Side} (U : PriceCoords G c → Config G m) (p : Site m → Site c),
    Letters U p k C → ∀ (P : PathData G) (a : ℝ), P.Bounds A σ L a →
    ∀ (s t : ℝ), 0≤t → 0≤s → s≤1 → s≤2*t →
    ∀ (R b : ℕ), 0<b → ∀ x : Twin m,
    (∀ y : Cell m, separation (p x.1.1) (p y.1) ≤ R → toll (U 0) y ≤ D*t) →
      Point 0 (p x.1.1) d k (fun z => plotted P A R b (U (s • z)) x) (M*t) := by
  let X := curvatureCost G * travelCost G k 4 C
  let K := max D (2*X)
  have hK : 0<K := hD.trans_le (le_max_left ..)
  let M := Real.exp (k*(1:ℝ)*5)*K
  have hm : 0<M := mul_pos (Real.exp_pos _) hK
  obtain ⟨d,N,hd,hN,H⟩ := carried G hσ k C M hC hm
  let r := min 1 d; let W := Real.sqrt A.direct*M
  have hr : 0<r := lt_min zero_lt_one hd; have hw : 0<W := mul_pos (Real.sqrt_pos.mpr A.quadratic_pos) hm
  refine ⟨r,max W (L*N),hr,hw.trans_le (le_max_left ..),?_⟩
  intro m c U p hp P a hP s t ht hs hst ht' R b hb i h
  have hX : 0≤X := by
    have ha := hp.through (Classical.arbitrary _)
    have hz : 0 ≤ travelCost G k 4 C := (Push.Uniform.travel_jets hp.through
      (0:Site m) (w:=[]) (by decide : ([] : Walk).length≤4)).nonneg
    exact mul_nonneg (curvature_nn _) hz
  have hf (j : Cell m) (hj : separation (p i.1.1) (p j.1) ≤ R) : Point 0 (p j.1) r k (fun z =>
      G.curvature (faceValue (U (s • z)) j)) (M*t) := by
    have hy : ‖G.curvature (faceValue (U 0) j)‖ ≤ K*t := (G.curvature_norm _).trans
      ((h j hj).trans (mul_le_mul_of_nonneg_right (le_max_left ..) ht))
    have hv : X*s ≤ K*t := calc X*s ≤ X*(2*t) := mul_le_mul_of_nonneg_left ht' hX
                                _ = (2*X)*t := by ring
                                _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) ht
    exact (face_cost hp j hs hst zero_le_one hy hv).mono (min_le_left ..) (le_of_eq (mul_assoc _ _ _).symm)
  unfold plotted; split
  next hk =>
    have hm (U : Config G m) (x : Cell m) : shorten P R b U x =
        ∑ z ∈ Stack.allShort (R/b), Stack.grouped P x.2 z •
            G.adjoint (travel U x.1 z.walk) (G.curvature (faceValue U (Work.F03.slotFace z x.1))) := by
      rw [← Stack.finite_price x (R/b) U (fun i => G.curvature (faceValue U i)) hP, barrel_term]
      unfold shorten; refine tsum_congr fun i => ?_
      simp [shortenTerm, Nat.le_div_iff_mul_le hb]
    simp_rw [hm]
    refine Point.mono (Point.sum_price (Stack.allShort (R/b)) (fun z => |Stack.grouped P i.1.2 z| *
      (N*Real.exp (σ*z.length)*t)) fun z hz => ?_) le_rfl ?_
    · let j := Work.F03.slotFace z i.1.1
      have he : j.1=stop i.1.1 z.walk := by
        unfold j Work.F03.slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm,← Work.E03.stop_add_left]; simp
      have hW : z.walk.length ≤ z.length := Nat.le_add_right ..
      have hu : separation (p i.1.1) (p j.1) ≤ R := by
        rw [he]; exact ((Work.E03.sep_walk _ hp.step ..).trans hW).trans (((Stack.short_iff ..).mp hz).trans (Nat.div_le_self ..))
      have hJ := hf j hu
      have ht := H U p hp s t ht hs hst i.1.1 z.walk _ r hr.le (min_le_right ..) (he ▸ hJ)
      refine ((ht.mono le_rfl ?_).scale (Stack.grouped P _ z))
      gcongr
    · calc
        _ = (∑ z∈Stack.allShort (R/b), |Stack.grouped P i.1.2 z| * Real.exp (σ*z.length)) * (N*t) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
        _ ≤ _ := ((mul_le_mul_of_nonneg_right (Stack.grouped_le _ hP i.1.2) (mul_nonneg hN.le ht)).trans_eq
          (mul_assoc _ _ _).symm).trans (mul_le_mul_of_nonneg_right (le_max_right ..) ht)
  next hk =>
    have hy := (hf i.1 (by simp)).scale (Real.sqrt A.direct)
    rw [abs_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc] at hy
    exact hy.mono le_rfl (mul_le_mul_of_nonneg_right (le_max_left ..) ht)
end values
end YM.AnalyticBridge.SectorAffine.Offset
