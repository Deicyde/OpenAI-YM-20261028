import YM.Branch.Pick
import YM.Pressure.Route
import YM.Pressure.Single


/-!
# Synchronize either branch with parent macro frame. ANY input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Filter Function Lattice RG RG.Patch Axial Wilson Finset YM.Branch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal
variable {G : Gauge}

namespace Road
variable (P : Patch)

lemma route (U : CoverConfig G) (o : Lattice.Order) :
    (∑ x : P.Points, ∑ y : P.Points,G.chord (travel U x.val (Lattice.route x.val y.val o))) ≤
      4 * Fintype.card P.Points * (2*P.radius+1)*edges P.sites U := by
  have hx := route_sum P.radius U (allAxes o) ((List.nodup_finRange _).map o.injective)
  rw [show (allAxes o).length=4 by simp [allAxes]] at hx
  push_cast at hx
  unfold Lattice.route
  rw [Fintype.card_coe]; exact hx

def pairs (U : CoverConfig G) : Pairs P.Points Lattice.Order G where
  W i j k := travel U i.val (Lattice.route i.val j.val k)
  mirror := backOrder
  same := by simp [travel]
  reflect := fun i j k => by rw [back_route, ← travel_reverse _ U,route_end]

lemma strips (C : KernelChoices) (U : CoverConfig G) (h : P.usesMin C U) (t : P.FrameTag) (H : Cover → G.El) :
    (pairs P (gauge H U)).Solves (fun x => P.frame C U t x*(H x.val)⁻¹) := by
  let A := pairs P (gauge H U)
  let toM (b : P.Frame G) := fun x : P.Points => b x* (H x.val)⁻¹
  have he (b) : A.cost (toM b)=P.score U b := by
    have hh (i j k) : A.term (toM b) i j k=G.price (P.via b U i j k) := by
      unfold Pairs.term A toM via
      simp only [pairs,travel_gauge,route_end]; congr 1; group
    unfold Pairs.cost; simp_rw [hh]; rfl
  intro b
  change A.cost (toM _) ≤ A.cost b
  rw [he,frame, if_pos h]
  let c : P.Points → G.El := fun x => b x*H x.val
  let f : P.Frame G := fun x => (c P.center)⁻¹ * c x
  have hy : A.cost b=P.score U f := by rw [← he,show toM f=(fun i => (c P.center)⁻¹*b i) by ext i; simp [toM,f,c,mul_assoc],A.moves]
  rw [hy]; exact (P.min_exists U).choose_spec.2 f (by simp [f])

lemma sum_avg {A B : Type*} [Fintype A] (t : Finset B) (f : A → B → ℝ) :
    (∑ i ∈ t, avg fun j => f j i) = avg fun j => ∑ i ∈ t, f j i := by
  unfold avg; simp only [smul_eq_mul,← Finset.mul_sum]; rw [sum_comm]

lemma revenue (U : CoverConfig G) : Fintype.card P.Points * mean (pairs P U) ≤
    4*(2*P.radius+1:ℝ)*edges P.sites U := by
  let n : ℝ := Fintype.card P.Points
  have hn : 0<n := by unfold n; exact_mod_cast Fintype.card_pos
  change n * mean _≤_
  unfold mean; rw [avg,smul_eq_mul]; change n*(n⁻¹ * _)≤_
  rw [mul_inv_cancel_left₀ hn.ne']; unfold income
  simp only [pairs]
  let f := fun x : P.Points => fun y : P.Points => avg fun k : Lattice.Order => G.chord (travel U x.val (Lattice.route x.val y.val k))
  change (∑ i : P.Points,n⁻¹*(∑ y : P.Points,f i y))≤_
  rw [← Finset.mul_sum]
  change n⁻¹*_ ≤ _
  rw [inv_mul_le_iff₀ hn]; unfold f
  simp_rw [sum_avg]; apply le_trans (avg_mono (g := fun _ => 4*n*(2*P.radius+1)*edges P.sites U) (fun i => route P _ i))
  rw [avg_const]; apply le_of_eq; ring
end Road

-- gu costs for two charts
lemma edges_ge (X : Finset Cover) (U : CoverConfig G) : 0≤edges X U := sum_nonneg fun _ _ => sum_nonneg fun _ _ => per_nn ..

lemma risks (K H : Cover → G.El) (U : CoverConfig G) (X : Finset Cover) :
    edges X (gauge (fun x => K x*(H x)⁻¹) (1:CoverConfig G)) ≤ edges X (gauge K U)+edges X (gauge H U) := by
  simp_rw [edges,← sum_add_distrib]
  -- pay discrepancy
  apply sum_le_sum
  intro x _; apply sum_le_sum; intro i _
  unfold perEdge
  split_ifs
  · let t : G.El := K x * (H x)⁻¹; let u := K (x+step i) * (H (x+step i))⁻¹
    let v := gauge H U (x,i); let w := gauge K U (x,i)
    change G.chord (t*1*u⁻¹) ≤ G.chord w + G.chord v
    have hh : t*1*u⁻¹=w*(u*v⁻¹*u⁻¹) := by unfold w v t u Lattice.gauge; group
    rw [hh]; apply (G.chord_triangle _ _).trans; simp
  · rw [add_zero]

lemma one {x : Cover} (p : Walk) : travel (1:CoverConfig G) x p=1 := by
  induction p generalizing x with
  | nil => simp [travel]
  | cons i l ih => rw [travel,ih,mul_one]; simp [Step.read]

lemma fallback (P : Patch) (K : KernelChoices) (t : P.FrameTag) (U : CoverConfig G) (he : ¬ P.usesMin K U)
    (h : 0 < P.frameMass K U t) (H : Cover → G.El) : ∃ c : G.El,
    (∑ x : P.Points, G.chord (P.frame K U t x*(H x.val)⁻¹*c⁻¹)) ≤
      4*(2*P.radius+1)*(edges P.sites (gauge H U)+K.axial_factor*(2*P.radius+1)*faces P.sites U) := by
  classical
  let r (x : Cover) := travel U t.1.val (route t.1.val x t.2)
  let d (x : Cover) := (r P.center.val)⁻¹*r x
  have ht : ∀ x : P.Points, P.frame K U t x=d x.val := fun i => by rw [frame, if_neg he]; rfl
  have hv : t∈P.eligible K U := by
    by_contra hh; simp [frameMass,he,hh] at h
  unfold Patch.eligible at hv
  have hb := (mem_filter.mp hv).2
  rw [edge_cost,face_cost] at hb
  have hd : edges P.sites (gauge d U) = edges P.sites (gauge r U) := by
    refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j _ ↦ ?_
    unfold perEdge; split; swap; rfl
    unfold Lattice.gauge d
    simp only
    rw [show _ * _ * (_*_)⁻¹=(r P.center.val)⁻¹*(r i*U (i,j)*(r (i+step j))⁻¹)*r P.center.val by group]
    simpa only [inv_inv] using G.chord_conj (r P.center.val)⁻¹ (r i * U (i,j) * (r (i+step j))⁻¹)
  let g (x : Cover) := d x*(H x)⁻¹
  let V := gauge g (1:CoverConfig G)
  have eq (x y : P.Points) : travel V x.val (route x.val y.val t.2)=g x.val*(g y.val)⁻¹ := by rw [show V=_ from rfl, travel_gauge,route_end,one,mul_one]
  let f (x y : P.Points) := G.chord (travel V x.val (route x.val y.val t.2))
  let F y := ∑ x, f x y
  obtain ⟨v,hv⟩ := le_avg F
  refine ⟨g v.val,le_trans ?_ (mul_le_mul_of_nonneg_left (a:=(4:ℝ)*(2*P.radius+1)) (b:=edges P.sites V) ?_ (by positivity))⟩
  · have hn : 0 < (Fintype.card P.Points : ℝ) := by exact_mod_cast Fintype.card_pos
    have hi := Road.route P V t.2
    change ∑ x, ∑ y, f x y ≤ _ at hi
    rw [sum_comm] at hi
    simp_rw [ht]
    apply le_trans ?_ (le_trans hv (show avg F ≤ 4*(2*P.radius+1)*edges P.sites V from ?_))
    · apply le_of_eq
      unfold F f; simp_rw [eq]; rfl
    unfold avg; rw [smul_eq_mul,inv_mul_le_iff₀ hn]; exact hi.trans_eq (by ring)
  have hh := risks d H U P.sites; rw [hd,add_comm (edges P.sites _)] at hh
  exact hh.trans (add_le_add_right hb _)

/-- Actual frame ANY branch local comparison gauge. -/
theorem synchronized (G : Gauge) : ∃ A : ℝ, 0<A ∧ ∀ (P : Patch) (K : KernelChoices) (t : P.FrameTag) (U : CoverConfig G), 0 < P.frameMass K U t →
    ∀ H : Cover → G.El, ∃ c : G.El, (∑ x : P.Points,G.chord (c⁻¹ * P.frame K U t x * (H x.val)⁻¹)) ≤
        A*(2*P.radius+1)*(edges P.sites (gauge H U)+K.axial_factor*(2*P.radius+1)*faces P.sites U) := by
  obtain ⟨C,h,D⟩ := cluster G
  let A := max (C*4) 4
  have ht : 0<A := lt_of_lt_of_le (by positivity) (le_max_left ..)
  refine ⟨A,ht,fun P K t U b H => ?_⟩
  let v := gauge H U
  let a : ℝ := 2*P.radius+1
  have hs : 0≤a := by unfold a; positivity
  have he := edges_ge P.sites v
  have hh : 0 ≤ K.axial_factor*a*faces P.sites U := mul_nonneg (mul_nonneg K.axial_factor_pos.le hs) (faces_nonneg ..)
  by_cases hg : P.usesMin K U
  · obtain ⟨c,hc⟩ := D _ _ (Road.pairs P v) _ (Road.strips P _ _ hg t H)
    refine ⟨c,?_⟩
    have hx := Road.revenue P v
    let B : ℝ := Fintype.card P.Points
    have hn : 0<B := by unfold B; exact_mod_cast Fintype.card_pos
    rw [avg,smul_eq_mul,inv_mul_le_iff₀ hn] at hc
    change _ ≤ B*(C*mean _) at hc
    change _ ≤ A*a*_
    simp_rw [mul_assoc (c⁻¹),chord_cyc (c⁻¹)]
    exact le_trans hc (le_trans (by rw [mul_left_comm B]; apply mul_le_mul_of_nonneg_left hx h.le)
      (le_trans (by rw [← mul_assoc,← mul_assoc] : C*(4*a*edges P.sites v) ≤ (C*4)*a*edges P.sites v) (mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left ..) hs) (le_add_of_nonneg_right hh) he (mul_nonneg ht.le hs))))
  obtain ⟨c,hb⟩ := fallback P K t U hg b H
  refine ⟨c,?_⟩
  simp_rw [mul_assoc (c⁻¹),chord_cyc (c⁻¹)]
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hs) (add_nonneg he hh))
end YM.Pressure
