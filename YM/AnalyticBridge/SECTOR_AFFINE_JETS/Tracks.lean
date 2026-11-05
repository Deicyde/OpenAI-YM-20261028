import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Visits

/-!
# Cross routed M factors applied to columns at corners/bonds

Charge counting on the full cover, including for jets of the parallel
transports. Do not identify or reorient paths differently by location.
Row rates obtained uniformly after L independent of truncation lengths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset

open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior Bloch Laurent
open YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD
open YM.Push.Uniform (bolt Allows Requests travelCost)
open YM.Work.E03
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {R k n : ℕ} {C D M K Q s σ d t r κ : ℝ} {p : Site f → Site c}

section tracks
variable {α β : Type}
/-- One actual path query. Require y match also to be *carried* before paying its downstream value. -/
def ticket {Y : Type} (q : Y ≃ Co c β) (K : Row α β) (l : Co c α) (a : Site f) (x : Cover → Walk)
    (U : Config G f) (R D : ℕ) (i : Y) (u : Cover) : Pay G :=
  if (x u).length * D ≤ R ∧ (q i).1=l.1+wrap c u then rated U a (x u) (K l.2 (q i).2 u) else 0

open Finset
/-- Arc application when each covered target carries the indicated budget at its actual endpoint.
No finiteness cost on winding (path strip consumes true length), but use the actual
length cut also to sum vs infinite cover definition. γ per root visit small
after length factor B is fixed. -/
lemma follows (G : Gauge) (n : ℕ) {C γ A B M : ℝ} (hC : 0 ≤ C) (hA : 0<A) (hB : 0<B) (hg : 0<γ)
    (β : Type) [Fintype β] :
    ∃ d N : ℝ, 0<d ∧ 0<N ∧
    ∀ {α Y : Type} [Fintype Y] {c f : Side} (l : Co c α) (q : Y ≃ Co c β) (K : Row α β), K.strip γ M →
    ∀ (p : Site f → Site c) (a : Site f) (w : Cover → Walk),
    (∀ i, ((w i).length:ℝ) ≤ B*(1+size i)) → ∀ (U : PriceCoords G c → Config G f) (H : Y → PriceCoords G c → G.Color),
    Letters U p n C →
    ∀ (R D : ℕ), 0<D → ∀ (s t δ : ℝ), 0≤t → 0≤s → s≤1 → 0≤δ → δ≤d →
    (∃ F : Finset Cover, ∀ i, (w i).length ≤ R → i∈F) →
    (∀ i j, (w j).length*D ≤ R → (q i).1=l.1+wrap c j →
      Point 0 (p (stop a (w j))) δ n (H i) (A*t)) →
    Point 0 (p a) δ n
      (fun y => ∑ i : Y, (∑' j : Cover, ticket q K l a w (U (s • y)) R D i j) (H i y)) (N*t) := by
  let r := γ/B; have hr : 0<r := div_pos hg hB
  obtain ⟨d,N,hd,hN,he⟩ := carried G hr n C A hC hA
  let E := N*Real.exp γ
  let O := Fintype.card β * M*E
  refine ⟨d,max 1 O,hd,zero_lt_one.trans_le (le_max_left ..),?_⟩
  rintro α Y _ c f l q K hK p a w hb U H h R D hD s t δ ht hs hu hδ hv ⟨F,hF⟩ hy
  have hp (i : Y) (y : PriceCoords G c) :
      (∑' j : Cover, ticket q K l a w (U (s • y)) R D i j) (H i y) =
      ∑ j ∈ F, ticket q K l a w (U (s • y)) R D i j (H i y) := by
    rw [tsum_eq_sum ?_, _root_.sum_apply]
    intro j hj; unfold ticket
    rw [if_neg ?_]
    exact fun ht => hj (hF _ ((le_mul_of_one_le_right (Nat.zero_le _) hD).trans ht.1))
  simp_rw [hp]
  let X (b : Co c β) (u : Cover) := if b.1=l.1+wrap c u then Real.exp (γ*size u)*|K l.2 b.2 u| else 0
  have hJ : 0≤E*t := mul_nonneg (mul_nonneg hN.le (Real.exp_pos _).le) ht
  refine Point.mono (Point.sum_price Finset.univ _ (fun i _ => Point.sum_price F (fun u => X (q i) u*(E*t)) fun j _ => ?_))
    le_rfl ?_
  · unfold ticket; split
    next hi =>
      have hm := he U p h s t ht hs hu a (w j) (H i) δ hδ hv (hy _ _ hi.1 hi.2)
      refine ((hm.scale (K l.2 (q i).2 j))).mono le_rfl ?_
      have hu : Real.exp (r*(w j).length) ≤ Real.exp γ * Real.exp (γ*size j) := by
        rw [← Real.exp_add]
        refine Real.exp_monotone ((mul_le_mul_of_nonneg_left (hb _) hr.le).trans_eq ?_)
        unfold r; field_simp
      simp only [X, if_pos hi.2]; unfold E
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hN.le) ht) (abs_nonneg _)).trans_eq (by ring)
    next hi =>
      apply Point.zero (mul_nonneg _ hJ)
      unfold X; split <;> positivity
  simp_rw [← Finset.sum_mul]
  have he : ∑ i : Y, ∑ j∈F, X (q i) j ≤ (Fintype.card β:ℝ)*M := by
    rw [Equiv.sum_comp q (fun i : Co c β => ∑ j ∈ F, X i j), Fintype.sum_prod_type, Finset.sum_comm,
      show (Fintype.card β:ℝ)*M=∑ _ : β,M by simp]
    refine Finset.sum_le_sum fun i _ => ?_; rw [Finset.sum_comm]
    simp only [X]; simp only [Finset.sum_ite_eq', mem_univ, ↓reduceIte]
    have hh := hK l.2 i; change (∑ j∈F, Real.exp (γ*size j)*‖K l.2 i j‖) ≤ _
    exact ((Summable.sum_le_tsum F (fun i _ => hh.1 i) hh.2.1)).trans hh.2.2
  exact ((mul_le_mul_of_nonneg_right he hJ).trans_eq (mul_assoc _ _ _).symm).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) ht)
end tracks

section geom
private lemma route_size (x y : Cover) : (route x y 1).length = size (y-x) := by
  have ha : allAxes 1 = [0,1,2,3] := by decide
  simp [route, axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]
private lemma size_scaled (x : Cover) (d : ℕ) : size (d • x) = d * size x := by
  simp [size,Pi.smul_apply,Int.natAbs_mul, Finset.mul_sum]
private lemma max_lift (L : Side) (x : Site L) : size (lift x) ≤ 4 * L.val := calc
  _ ≤ ∑ _i : Axis, L.val := Finset.sum_le_sum fun i _ => by have hh := lift_centers x i; omega
  _ = _ := by simp [Axis]

private lemma contained {R : ℕ} {i : Cover} (h : size i ≤ R) : i ∈ box R := by
  rw [box_test]
  constructor <;> intro k <;> have hh : (i k).natAbs ≤ R := (FreeResolvent.own_size i k).trans h <;> omega

private def elasticity (L : Side) : ℝ := 5*(L.val:ℝ)
private lemma elasticity_pos (L : Side) : 0 < elasticity L := by
  unfold elasticity; have := L.property; positivity
private def itinerary (L : Side) (x : Site L) (i : Cover) := route (lift x) (L.val • i) 1
private lemma elastic (L : Side) (z : Site L) (u : Cover) : ((itinerary L z u).length:ℝ) ≤ elasticity L*(1+size u) := by
  unfold itinerary; rw [route_size]
  have hSize : size (L.val • u - lift z) ≤ L.val * size u + 4 * L.val := by
    rw [sub_eq_add_neg]; apply (size_add ..).trans
    rw [size_neg, size_scaled]; exact Nat.add_le_add_left (max_lift L z) _
  have hl : (size (L.val • u - lift z):ℝ) ≤ L.val * (size u:ℝ) + 4 * (L.val:ℝ) := by exact_mod_cast hSize
  apply hl.trans; unfold elasticity
  have hx : 0 ≤ (L.val:ℝ)*(size u:ℝ) := by positivity
  linarith

private lemma finite_routed (L : Side) (z : Site L) (R : ℕ) (u : Cover) (h : (itinerary L z u).length ≤ R) :
    u ∈ box (R+4*L.val) := by
  unfold itinerary at h; rw [route_size] at h
  apply contained
  have hl : size u ≤ size (L.val • u) := by rw [size_scaled]; exact Nat.le_mul_of_pos_left _ L.property
  refine hl.trans ?_
  nth_rw 1 [← sub_add_cancel (L.val • u) (lift z)]
  exact (size_add ..).trans (Nat.add_le_add h (max_lift L z))
end geom
section crossed
/-- Cross-kernel estimate incl every component hit, no count lost at
adjoint endpoints. The use is at the prescribed `s` with both fields
turned in the *same* comparison, leaving true V paths. `Q` needn't be
thinned; application uses the unmasked good m' extension. -/
lemma wide (G : Gauge) (Pt : Teller G) (L : Side) (n : ℕ) (C M : ℝ) (hC : 0≤C) (hm : 0<M) :
    ∃ d N : ℝ, 0<d ∧ 0<N ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → S.patch.L=L →
    ∀ (W : PriceCoords G c → Config G c) (H : Twin c → PriceCoords G c → G.Color) (g : Site c → Site c),
    Letters (fun y => replica S.ratio (W y)) (g ∘ S.ratio.parent) n C →
    ∀ (R : ℕ) (s t δ : ℝ), 0≤t → 0≤s → s≤1 → 0≤δ → δ≤d → ∀ i : Twin f,
    (∀ y : Twin c, separation (S.ratio.parent i.1.1) y.1.1 ≤ R → Point 0 (g y.1.1) δ n (H y) (M*t)) →
      Point 0 (g (S.ratio.parent i.1.1)) δ n (fun z => ∑ j : Twin c, T.Φ R (W (s • z)) i j (H j z)) (N*t) := by
  obtain ⟨d,N,hd,hN,h⟩ := follows G n (M:=Pt.C / (L.val:ℝ)^2) hC hm (elasticity_pos L) Pt.width Layers2
  refine ⟨d,N,hd,hN,?_⟩
  intro c f S T hP he W H g hL R s t δ ht hs hu hδ hv i hi
  subst L
  let z := S.ratio.residue (mesh i).1
  let a := S.ratio.parent (mesh i).1
  let w := itinerary S.patch.L z
  let r : Co c (Co S.patch.L Layers2) := (a,z,(mesh i).2)
  obtain ⟨-, -, hf,-⟩ := hP.crosses
  have hx j (x : PriceCoords G c) : T.Φ R (W (s • x)) i j = ∑' k : Cover, ticket (meshEquiv c) T.R.mf r
      (mesh i).1 w (replica S.ratio (W (s • x))) R 1 j k := by
    unfold Tube.Φ leap; refine tsum_congr fun k => ?_; simp only [ticket,mul_one]; rfl
  simp_rw [hx]
  refine h r (meshEquiv c) _ hf _ _ w (elastic S.patch.L z) _ _ hL R 1 (by decide) s t δ ht hs hu hδ hv
    ⟨box (R+4*S.patch.L.val), finite_routed S.patch.L z R⟩ (fun j k hk hl => ?_)
  have he : S.ratio.parent (stop i.1.1 (w k)) = j.1.1 := by
    rw [show stop i.1.1 (w k)=_ from casted_endpoint S i.1.1 k, S.ratio.embed_parent]; exact hl.symm
  have hm := hi j (by
    rw [← he]; apply (sep_walk _ (parent_step S) i.1.1 (w k)).trans; simpa using hk)
  change Point 0 (g (S.ratio.parent (stop i.1.1 (w k)))) δ n (H j) (M*t); rw [he]; exact hm

lemma noise (G : Gauge) (Pt : Teller G) (n : ℕ) (C M : ℝ) (hC : 0≤C) (hm : 0<M) :
    ∃ d N : ℝ, 0<d ∧ 0<N ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T →
    ∀ (W : PriceCoords G c → Config G c) (H : Twin c → PriceCoords G c → G.Color) (g : Site c → Site c),
    Letters W g n C → ∀ (R : ℕ) (s t δ : ℝ), 0≤t → 0≤s → s≤1 → 0≤δ → δ≤d → ∀ i : Bond c,
    (∀ y : Twin c, separation i.1 y.1.1 ≤ R → Point 0 (g y.1.1) δ n (H y) (M*t)) →
      Point 0 (g i.1) δ n (fun z => ∑ j : Twin c, T.Φ' R (W (s • z)) i j (H j z)) (N*t) := by
  obtain ⟨d,N,hd,hN,h⟩ := follows G n (M:=Pt.C) hC hm zero_lt_one Pt.width Layers2
  refine ⟨d,N,hd,hN,?_⟩
  intro c f S T hP W H g hL R s t δ ht hs hu hδ hv i hi
  obtain ⟨hm,-⟩ := hP.crosses
  let w (k : Cover) := route 0 k 1
  refine h (pole i) (meshEquiv c) _ hm _ _ w (fun z => by simp [w, route_size]) _ _ hL R S.patch.L.val
    S.patch.L.property s t δ ht hs hu hδ hv ⟨box R, fun i hi => contained (by simpa [w,route_size] using hi)⟩
    (fun j k hk h => ?_)
  have he : stop i.1 (w k)=j.1.1 := by
    have ht : j.1.1=i.1+wrap c k := h
    rw [ht]
    simpa only [map_zero,add_zero] using stop_route i.1 0 k
  rw [he]; exact hi _ (he ▸ ((sep_walk id (fun i j => sep_step i j) i.1 (w k)).trans
    ((le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property).trans hk)))
end crossed
end YM.AnalyticBridge.SectorAffine.Offset
