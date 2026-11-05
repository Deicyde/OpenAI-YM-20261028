import YM.Bid.Energy

/-!
# Pre-L pricing for the shell test against the flat output

Strengthening in L necessary for the Hessian gap/inverse. Adapted from
`YM.Work.E02` which has the mathematical argument for this stronger L-control
(uses `planting`), but only provides the theorem with an existential *after*
L; its lemmas are file-private. Preserve that file unchanged. Would propose
factoring these common lemmas/exporting pre-L from there after integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform

open Function Lattice Wilson RG Axial Tree Precision Pressure Pressure.Stores Bid
open scoped BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}

private lemma wider {x : Cover} {t r : ℕ} (h : x ∈ box t) (e : t ≤ r) : x ∈ box r := by
  obtain ⟨ha,hb⟩ := box_test.mp h
  exact box_test.mpr ⟨fun i => le_trans (neg_le_neg (by exact_mod_cast e)) (ha i),
    fun i => le_trans (hb i) (by exact_mod_cast e)⟩

private lemma box_next {x : Cover} {r : ℕ} (h : x ∈ box r) (d : Step) :
    x + d.vec ∈ box (r+1) := by
  obtain ⟨ha,hb⟩ := box_test.mp h
  rw [box_test]; constructor <;> intro i
  all_goals
    have h₁ := ha i
    have h₂ := hb i
    unfold Step.vec; split <;>
      simp only [Pi.add_apply, Pi.neg_apply, step_apply] <;> split <;> omega

private lemma read_le (U : CoverConfig G) (X : Finset Cover) (x : Cover) (d : Step)
    (hx : x ∈ X) (he : x + d.vec ∈ X) : G.chord (d.read U x) ≤ edges X U := by
  have h (y : Cover) (i : Axis) (hy : y ∈ X) (hi : y + step i ∈ X) :
      G.chord (U (y,i)) ≤ edges X U := calc
    _ = perEdge X U y i := by rw [perEdge, if_pos hi]
    _ ≤ ∑ j, perEdge X U y j := Finset.single_le_sum (fun j _ => per_nn X U y j) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun z => ∑ j, perEdge X U z j)
        (fun z _ => Finset.sum_nonneg (fun j _ => per_nn ..)) hy
  rcases d with ⟨i,b|b⟩
  · exact h x i hx he
  change G.chord (U (x-step i,i))⁻¹ ≤ _
  rw [G.chord_inv]
  apply h
  · simpa only [Step.vec, ↓reduceIte, sub_eq_add_neg] using he
  · rwa [sub_add_cancel]

/-- Coarse bound by length times the *same* macro bill, including repeated steps. -/
private lemma walk_bound (U : CoverConfig G) (r t : ℕ) (x : Cover) (w : Walk)
    (hx : x ∈ box t) (he : t+w.length ≤ r) :
    stop x w ∈ box r ∧ G.chord (travel U x w) ≤ w.length * edges (box r) U := by
  induction w generalizing x t with
  | nil =>
    exact ⟨wider hx (by simpa using he), by simp [travel]⟩
  | cons d w ih =>
    have hb := box_next hx d
    simp only [List.length_cons] at he
    obtain ⟨hs,h⟩ := ih (t+1) _ hb (by omega)
    refine ⟨hs, ?_⟩
    rw [travel]
    apply (G.chord_triangle _ _).trans
    refine (add_le_add (read_le U (box r) x d (wider hx (by omega)) (wider hb (by omega))) h).trans_eq ?_
    simp [add_mul, add_comm]

/-- Hike transport is the identity on the actual slice. -/
private lemma on_hike {S : StepData c f} (F : Forest S.ratio) {U : Config G f}
    (h : SliceSet S F U) (x : Site f) : travel U x (F.hike x) = 1 := by
  induction x using Forest.hike.induct F with
  | case1 i hi ih =>
    have he := h _ ((F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩)
    rw [Forest.hike, dif_pos hi, travel, ih]
    simp [Step.read, he]
  | case2 i hi => rw [Forest.hike, dif_neg hi, travel]

-- Form a single possibly seam-crossing walk. No replacement of the forest.
private lemma root_walk {S : StepData c f} (F : Forest S.ratio) (x : Site f) (a : Axis)
    (U : Config G f) (h : SliceSet S F U) :
    ∃ w : Walk, w.length ≤ 8*S.patch.L.val+1 ∧
      stop (S.ratio.embed (S.ratio.parent x)) w = S.ratio.embed (S.ratio.parent (x+step a)) ∧
      travel U (S.ratio.embed (S.ratio.parent x)) w = U (x,a) := by
  refine ⟨Lattice.reverse (F.hike x) ++ posDir a :: F.hike (x+step a), ?_, ?_, ?_⟩
  · have hlen (y) : (F.hike y).length ≤ 4*S.patch.L.val := (F.hike_lower y).trans (F.bound y)
    simp only [Lattice.reverse, List.length_append, List.length_map, List.length_reverse,
      List.length_cons]
    have hx := hlen x
    have hh := hlen (x+step a)
    omega
  · rw [← F.hike_root x, stop_append, reverse_stop, stop, Step.vec_pos, F.hike_root]
  rw [← F.hike_root x, travel_append, travel_reverse, reverse_stop, travel,
    Step.pos_read, Step.vec_pos, on_hike F h, on_hike F h, mul_one, inv_one, one_mul]

private lemma stop_at (w : Walk) (x : Cover) (b : Site f) :
    wrap f (stop x w)+b = stop (wrap f x+b) w := by
  rw [wrap_stop_cover]
  have he (w : Walk) (y : Site f) : stop y w + b = stop (y+b) w := by
    induction w generalizing y with
    | nil => rfl
    | cons i w ih => rw [stop,stop,ih,add_right_comm y]
  exact he w _

private lemma inj_macro (P : Patch) (f : Side) (he : 100*macroR P ≤ f.val)
    (x y : Cover) (hx : x ∈ box (macroR P)) (hy : y ∈ box (macroR P))
    (eq : wrap f x = wrap f y) : x = y := by
  have h (x : Cover) (hx : x ∈ box (macroR P)) (i : Axis) :
      -(f.val : ℤ) < 2*x i ∧ 2*x i ≤ f.val := by
    have hf := f.property
    have h₁ := (box_test.mp hx).1 i
    have h₂ := (box_test.mp hx).2 i
    change 0 < f.val at hf
    omega
  exact wrap_injOn f (h x hx) (h y hy) eq

private lemma pad_root (S : StepData c f) (C : ℝ) (H : Cover → G.El) (x : Site c)
    (y : Cover) (U : Config G f) (p : G.El) (t : S.Choices) (h : pad S C H x y U p t) :
    G.chord (H (centerRoot S.patch y)*p) ≤ C*(S.patch.L.val:ℝ)^2*port S x U := by
  have he : S.frames U t.1 (plank x y) S.patch.center=1 := by
    unfold StepData.frames Patch.frame
    split
    · exact (S.patch.min_exists _).choose_spec.1
    simp
  let e (i : S.patch.Points) := p⁻¹ * S.frames U t.1 (plank x y) i *
      (H (i.val+centerRoot S.patch y))⁻¹
  have hk : G.chord (e S.patch.center) ≤ C*(S.patch.L.val:ℝ)^2*port S x U :=
    (Finset.single_le_sum (fun i _ => G.chord_nonneg (e i)) (Finset.mem_univ S.patch.center)).trans h
  unfold e at hk
  rwa [he, mul_one, show S.patch.center.val = 0 from rfl, zero_add, ← mul_inv_rev, G.chord_inv] at hk

def linkCost (K : KernelChoices) (C D : ℝ) (L : Side) :=
    let l := (L.val : ℝ)
    let α := 2*max 1 K.predictor_cut⁻¹ * (2*C+D)
    (8*l+1)*(D*l)+(C*l^2 + α/l^2 + C*l^2)

lemma linkCost_pos (K : KernelChoices) {C D : ℝ} (hC : 0<C) (hD : 0<D) (L : Side) :
    0 < linkCost K C D L := by unfold linkCost; positivity

def Harness (G : Gauge) (j : ℕ) (K : KernelChoices) (C D : ℝ) := 0<C ∧ 0<D ∧
    ∀ {c f : Side} (S : StepData c f), S.kernel=K → S.patch.J=j → 100*macroR S.patch ≤ f.val →
    ∀ (F : Forest S.ratio) (U : Config G f), SliceSet S F U → ∀ (e : Bond f) (t : S.Choices),
      usable S U (S.ratio.parent e.1) t → Cops (S:=S) U 1 (S.prediction U t) e (linkCost K C D S.patch.L)

theorem link_charge (G : Gauge) (j : ℕ) (K : KernelChoices) : ∃ C D, Harness G j K C D := by
  obtain ⟨C,D,hC,hD,plant⟩ := planting G K j
  refine ⟨C,D,hC,hD,?_⟩
  intro c f S hk hj he F U hU e t ht
  let l : ℝ := S.patch.L.val
  have hl : 0 < l := by unfold l; positivity
  let α := 2*max 1 K.predictor_cut⁻¹ * (2*C+D)
  have ha : 0 < α := by unfold α; positivity
  let u := (8*l+1)*(D*l)
  let v := C*l^2 + α/l^2 + C*l^2
  have hu : 0 < u := by unfold u; positivity
  have hv : 0 < v := by unfold v; positivity
  rcases e with ⟨x,a⟩
  let g := S.ratio
  let i := g.parent x
  obtain ⟨H,p,hH,hp⟩ := plant c f S hk.symm hj.symm U i t ht
  let r := macroR S.patch
  let s := port S i U
  let B := g.embed i
  obtain ⟨w,hw,hw',eq⟩ := root_walk F x a U hU
  let z := stop (0:Cover) w
  have hR : w.length ≤ r := by
    unfold r macroR Patch.radius
    apply hw.trans
    have h := Nat.mul_le_mul_right S.patch.L.val
      (show 7 ≤ S.patch.J + 3 by have := S.patch.order_cut; omega)
    have h1 := S.patch.coarse
    omega
  obtain ⟨hz,hh⟩ := walk_bound (gauge H (expandAt B U)) r 0 0 w (center_box 0) (by omega)
  have hs : 0 ≤ s := faces_nonneg ..
  have hfin : G.chord (H 0 * U (x,a) * (H z)⁻¹) ≤ u*s := by
    rw [travel_gauge, travel_at, map_zero, zero_add] at hh
    change travel U B w = _ at eq
    rw [eq] at hh
    refine hh.trans ((mul_le_mul (b := 8*l+1) ?_ (d := D*l*s) ?_ (edges_ge ..) (by positivity)).trans_eq ?_)
    · unfold l
      exact_mod_cast hw
    · unfold l; exact hH
    unfold u; ring
  have hwrap : wrap f z+B = g.embed (g.parent (x+step a)) := by
    rw [show wrap f z+B = _ from stop_at w 0 B, map_zero, zero_add]
    exact hw'
  let Q := S.prediction U t (i,a)
  unfold Cops; simp only [replica_one,Pi.one_apply,mul_one, wire, inv_one,mul_one,one_mul, G.chord_inv]
  change G.chord (U (x,a)) ≤ (u+v)*s + if i=g.parent (x+step a) then 0 else G.chord Q
  by_cases hi : i=g.parent (x+step a)
  · -- Closed lifted loop at the first root.
    have hb : z=0 := inj_macro S.patch f he z 0 hz (center_box _) (by
      rw [← hi] at hwrap
      rw [map_zero]
      exact add_right_cancel (hwrap.trans (zero_add B).symm))
    rw [hb, G.chord_conj] at hfin
    rw [if_pos hi,add_zero]
    exact hfin.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hv.le) hs)
  -- Crossing. The second lift must be at the next center even at a seam.
  have hstep : g.parent (x+step a)=i+step a := by
    have h := g.parents_hop S.patch.odd_side x a
    split at h
    · exact h
    exact False.elim (hi h.symm)
  let y := (step a : Cover)
  let Z := centerRoot S.patch y
  have hy : y ∈ box 2 := by
    rw [box_test]; constructor <;> intro j <;> unfold y <;> rw [step_apply] <;> split <;> norm_num
  have hb : z=Z := by
    apply inj_macro S.patch f he z Z hz
    · have hg : 0 + centerRoot S.patch y ∈ box (macroR S.patch) :=
        shifted S.patch y hy (Finset.mem_image_of_mem _ (center_box S.patch.radius))
      rwa [zero_add] at hg
    rw [hstep, show i+step a=plank i y by simp [plank,y,add_comm], offsets] at hwrap
    exact add_right_cancel hwrap
  have hx : G.chord (H 0 * p 0) ≤ C*l^2*s := by
    have h := pad_root S C H i 0 U (p 0) t (hp _ (center_box 2))
    simp only [centerRoot, smul_zero] at h
    exact h
  have hend : G.chord (H Z * p y) ≤ C*l^2*s := by
    have h := pad_root S C H i y U (p y) t (hp _ hy)
    change G.chord (H Z * p y) ≤ _ at h
    exact h
  have hpr : G.chord ((p 0)⁻¹ * Q * p y) ≤ α/l^2*s := by
    have hy' : (0:Cover)+step a ∈ box 2 := by rw [zero_add]; exact hy
    have h := indicated S C D U i t 0 a (center_box 2) H _ _ (hp _ (center_box 2)) (hp _ hy') hH
    simp only [plank, map_zero, zero_add] at h
    -- keep prediction itself on this S and t
    change (S.patch.L.val:ℝ)^2 * G.chord ((p 0)⁻¹*Q*p y) ≤ _ at h
    rw [hk] at h
    apply le_of_mul_le_mul_left _ (show 0<l^2 by positivity)
    refine le_trans h (le_of_eq ?_)
    change α*s = l^2 * (α/l^2*s)
    field_simp
  have hQ : G.chord (H 0 * Q * (H z)⁻¹) ≤ v*s := by
    rw [hb, show H 0 * Q * (H Z)⁻¹ =
      (H 0 * p 0) * ((p 0)⁻¹*Q*p y) * (H Z * p y)⁻¹ by group]
    apply (G.chord_triangle _ _).trans
    rw [G.chord_inv]
    apply (add_le_add ((G.chord_triangle _ _).trans (add_le_add hx hpr)) hend).trans_eq
    unfold v; ring
  have hd : G.chord (U (x,a)*Q⁻¹) ≤ (u+v)*s := by
    rw [← G.chord_conj (H 0), show H 0 * (U (x,a)*Q⁻¹) * (H 0)⁻¹ =
      (H 0 * U (x,a) * (H z)⁻¹) * (H 0 * Q * (H z)⁻¹)⁻¹ by group]
    apply (G.chord_triangle _ _).trans
    rw [G.chord_inv, add_mul]
    exact add_le_add hfin hQ
  rw [if_neg hi]
  have hg := G.chord_triangle (U (x,a)*Q⁻¹) Q
  rw [mul_assoc, inv_mul_cancel, mul_one] at hg
  exact hg.trans (add_le_add_left hd _)
end YM.Push.Uniform
