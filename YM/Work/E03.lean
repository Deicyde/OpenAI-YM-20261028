import YM.Bid.Energy

/-!
# E03 — row and column estimates for the physical kernels cut on the cover

Use absolute sums *before* periodization and bound real-colour transport in
operator norm even for a winding route. The row prices for `mf` are per fixed
pair of types (including the one fine residue). Charge all the residues in the
column estimate. Only numerical stencil incidence of these kernels is asserted
in `Anchored`, not a bound on everything read by a larger operation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.E03
open Filter Function Lattice RG Wilson Finset Precision Exterior Bloch Pressure Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {c f : Side}

lemma norm_rated_le (U : Config G c) (x : Site c) (w : Walk) (a : ℝ) :
    ‖rated U x w a‖ ≤ ‖a‖ := by
  have h : ‖(G.adjoint (travel U x w)).toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i => by
      change ‖G.adjoint _ i‖ ≤ _
      rw [G.norm_adjoint, one_mul])
  calc
    ‖rated U x w a‖ = ‖a‖ * _ := norm_smul a _
    _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖a‖ := mul_one _

section count
variable {α β m n : Type*} [Fintype α] [Fintype β] [Fintype m] [Fintype n]
  (K : Row α β) {η A : ℝ}
  (e : m ≃ Co c α) (d : n ≃ Co c β) (F : m → n → Cover → Pay G)

/-- Count on the torus while paying the absolute cover bound separately for
    each type. The same absolute envelope works for rows and for columns. -/
lemma anchored_of_terms (B : ℕ) (he : 0 ≤ η) (hK : K.strip η A)
    (hm : ∀ i j u, ‖F i j u‖ ≤
      if (d j).1 = (e i).1 + wrap c u then ‖K (e i).2 (d j).2 u‖ else 0)
    (hs : ∀ i j u, F i j u ≠ 0 → separation (e i).1 (d j).1 ≤ B/50) :
    Anchored (fun i j => ∑' u, F i j u) ((Fintype.card β : ℝ) * A)
      ((Fintype.card α : ℝ) * A) (fun i => (e i).1) (fun j => (d j).1) B := by
  classical
  let cap (p : Co c α) (q : Co c β) (u : Cover) : ℝ :=
    if q.1 = p.1 + wrap c u then ‖K p.2 q.2 u‖ else 0
  have hu (i : α) (j : β) := (hK i j).unweighted he
  have hc (p q) : Summable (cap p q) := by
    apply (hu p.2 q.2).2.1.of_nonneg_of_le
    · intro u; dsimp only [cap]; split <;> simp
    intro u; dsimp only [cap]; split <;> simp
  have hh (i j) : ‖∑' u, F i j u‖ ≤ ∑' u, cap (e i) (d j) u := by
    have hv : Summable fun u => ‖F i j u‖ :=
      (hc (e i) (d j)).of_nonneg_of_le (fun u => norm_nonneg _) (hm i j)
    exact (norm_tsum_le_tsum_norm hv).trans (hv.tsum_le_tsum (hm i j) (hc _ _))
  constructor
  · intro i; refine (sum_le_sum fun j _ => hh i j).trans ?_
    calc
      ∑ j, ∑' u, cap (e i) (d j) u = ∑ q : Co c β, ∑' u, cap (e i) q u :=
        d.sum_comp (fun q => ∑' u, cap (e i) q u)
      _ = ∑ b : β, ∑ y : Site c, ∑' u, cap (e i) (y,b) u := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ ≤ ∑ _b : β, A := Finset.sum_le_sum fun b _ => calc
        ∑ y : Site c, ∑' u, cap (e i) (y,b) u =
            ∑' u, ∑ y : Site c, cap (e i) (y,b) u :=
              (Summable.tsum_finsetSum (fun y _ => hc (e i) (y,b))).symm
        _ = ∑' u, ‖K (e i).2 b u‖ := by simp [cap]
        _ ≤ A := (hu _ _).2.2
      _ = _ := by simp
  · intro j; refine (sum_le_sum fun i _ => hh i j).trans ?_
    calc
      ∑ i, ∑' u, cap (e i) (d j) u = ∑ p : Co c α, ∑' u, cap p (d j) u :=
        e.sum_comp (fun p => ∑' u, cap p (d j) u)
      _ = ∑ a : α, ∑ x : Site c, ∑' u, cap (x,a) (d j) u := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ ≤ ∑ _a : α, A := Finset.sum_le_sum fun a _ => calc
        ∑ x : Site c, ∑' u, cap (x,a) (d j) u =
            ∑' u, ∑ x : Site c, cap (x,a) (d j) u :=
              (Summable.tsum_finsetSum (fun x _ => hc (x,a) (d j))).symm
        _ = ∑' u, ‖K a (d j).2 u‖ := by simp [cap, ← sub_eq_iff_eq_add]
        _ ≤ A := (hu _ _).2.2
      _ = _ := by simp
  · intro i j h
    by_contra hn
    have hf (u : Cover) : F i j u = 0 := by
      by_contra hv
      exact hn (hs i j u hv)
    apply h
    simp [hf]
end count

section geometry
lemma sep_step (x : Site c) (i : Axis) : separation x (x + step i) ≤ 1 := by
  rw [separation_comm, separation, add_comm, add_sub_cancel_right]
  exact pdist_step _

lemma sep_walk (g : Site c → Site f)
    (hg : ∀ x (i : Axis), separation (g x) (g (x + step i)) ≤ 1)
    (x : Site c) (w : Walk) : separation (g x) (g (stop x w)) ≤ w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons d w ih =>
    have h : separation (g x) (g (x + d.vec)) ≤ 1 := by
      unfold Step.vec; split
      · rw [separation_comm]
        have hv := hg (x + -step d.dir) d.dir
        rw [show x + -step d.dir + step d.dir = x by abel] at hv; exact hv
      exact hg x _
    calc
      separation (g x) (g (stop x (d :: w))) ≤
          separation (g x) (g (x + d.vec)) +
          separation (g (x + d.vec)) (g (stop (x + d.vec) w)) := separation_triangle ..
      _ ≤ 1 + w.length := Nat.add_le_add h (ih _)
      _ = _ := by simp [add_comm]

lemma parent_step (S : StepData c f) (x : Site f) (i : Axis) :
    separation (S.ratio.parent x) (S.ratio.parent (x + step i)) ≤ 1 := by
  rw [S.ratio.parents_hop S.patch.odd_side]
  split
  · exact sep_step ..
  simp

lemma stop_add_left (o x : Site c) (w : Walk) : stop (o+x) w = o + stop x w := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => rw [stop, stop, add_assoc, ih]

/-- Endpoint holds even on wrapping routes. -/
lemma stop_route (o : Site c) (x y : Cover) :
    stop (o + wrap c x) (route x y 1) = o + wrap c y := by
  rw [stop_add_left, ← wrap_stop_cover, route_end]

lemma casted_endpoint (S : StepData c f) (x : Site f) (i : Cover) :
    stop x (route (lift (S.ratio.residue x)) (S.patch.L.val • i) 1) =
      S.ratio.embed (S.ratio.parent x + wrap c i) := by
  let o := S.ratio.parent x
  let r := S.ratio.residue x
  calc
    stop x (route (lift r) (S.patch.L.val • i) 1) =
        stop (S.ratio.embed o + wrap f (lift r)) (route (lift r) (S.patch.L.val • i) 1) :=
          congr_arg (fun z => stop z (route (lift r) (S.patch.L.val • i) 1))
            (S.ratio.unpack_at x).symm
    _ = S.ratio.embed o + wrap f (S.patch.L.val • i) := stop_route ..
    _ = S.ratio.embed (o + wrap c i) := by
      change S.ratio.embed o + wrap f (S.ratio.count.val • i) = _
      rw [← S.ratio.embed_wrap, ← S.ratio.root_embed, ← S.ratio.root_embed, ← map_add]
      rfl
end geometry

/-- Match each physical type once, using `plaqEquiv` on each layer. -/
def meshEquiv (c : Side) : Twin c ≃ Co c Layers2 where
  toFun := mesh
  invFun := fun q => match q.2 with
    | .inl a => ((q.1, plaqEquiv.symm a), false)
    | .inr a => ((q.1, plaqEquiv.symm a), true)
  left_inv := by
    rintro ⟨⟨x, a⟩, b⟩; cases b <;> simp [mesh, ← plaq_map]
  right_inv := by
    rintro ⟨x,a|a⟩ <;> simp [mesh, ← plaq_map]

def poleEquiv (c : Side) : Bond c ≃ Co c (TypeFace 1) :=
  Equiv.prodCongr (Equiv.refl _) axisEquiv

section applications
variable {α β m n : Type*} [Fintype α] [Fintype β] [Fintype m] [Fintype n]
variable {η A : ℝ}

lemma lane_anchored (K : Row α β) (e : m ≃ Co c α) (d : n ≃ Co c β)
    (B l : ℕ) (hp : 0 < l) (V : Config G c) (he : 0 ≤ η) (hK : K.strip η A) :
    Anchored (fun i j => lane (B/100000) l V K (e i) (d j)) ((Fintype.card β : ℝ) * A)
      ((Fintype.card α : ℝ) * A) (fun i => (e i).1) (fun j => (d j).1) B := by
  refine anchored_of_terms K e d (fun i j => priced (B/100000) l V K (e i) (d j))
    B he hK ?_ ?_
  · intro i j u; dsimp only [priced]
    split
    next h => rw [if_pos h.2]; exact norm_rated_le ..
    next h => split <;> simp
  intro i j u h; dsimp only [priced] at h; split at h
  next hq =>
    let w := route 0 u 1
    have hx : stop (e i).1 w = (e i).1 + wrap c u := by
      simpa only [map_zero, add_zero] using stop_route (e i).1 0 u
    calc
      separation (e i).1 (d j).1 = separation (e i).1 (stop (e i).1 w) := by rw [hx, hq.2]
      _ ≤ w.length := sep_walk (c:=c) (f:=c) id sep_step (e i).1 w
      _ ≤ w.length*l := by
        simpa only [mul_one] using Nat.mul_le_mul_left w.length (show 1 ≤ l from hp)
      _ ≤ B/100000 := hq.1
      _ ≤ B/50 := by omega
  next _ => exact (h rfl).elim

lemma leap_anchored (S : StepData c f) (M : Towers S.patch.L) (B : ℕ) (V : Config G c)
    (he : 0 ≤ η) (hK : M.mf.strip η A) :
    Anchored (leap S M (B/100000) V) ((Fintype.card Layers2 : ℝ) * A)
      ((Fintype.card (Co S.patch.L Layers2) : ℝ) * A) (S.ratio.parent ∘ tagged) tagged B := by
  let e : Twin f ≃ Co c (Co S.patch.L Layers2) := (meshEquiv f).trans (splitCo S.ratio Layers2)
  have hsplit (x : Twin f) :
      e x = (S.ratio.parent (mesh x).1, S.ratio.residue (mesh x).1, (mesh x).2) := split_co ..
  have hv : (S.ratio.parent ∘ tagged) = fun i => (e i).1 := by
    funext i; rw [hsplit]; rfl
  rw [hv]
  refine anchored_of_terms M.mf e (meshEquiv c)
    (fun i j u => casted S M (B/100000) V (mesh i) (mesh j) u) B he hK ?_ ?_
  · intro i j u; rw [hsplit]; dsimp only [casted, meshEquiv, Equiv.coe_fn_mk]
    split
    next h => rw [if_pos h.2]; exact norm_rated_le ..
    next h => split <;> simp
  intro i j u h; rw [hsplit]; dsimp only [casted] at h; split at h
  next hq =>
    let x := (mesh i).1
    let w := route (lift (S.ratio.residue x)) (S.patch.L.val • u) 1
    have hx : S.ratio.parent (stop x w) = (mesh j).1 := by
      rw [show stop x w = _ from casted_endpoint S x u, S.ratio.embed_parent]
      exact hq.2.symm
    change separation (S.ratio.parent x) (mesh j).1 ≤ _
    rw [← hx]
    exact ((sep_walk _ (parent_step S) x w).trans hq.1).trans (by omega)
  next _ => exact (h rfl).elim
end applications

lemma anchored_mono {m n : Type*} [Fintype m] [Fintype n] {F : m → n → Pay G}
    {x y X Y : ℝ} {d : m → Site c} {v : n → Site c} {B : ℕ} (h : Anchored F x y d v B)
    (hx : x ≤ X) (hy : y ≤ Y) : Anchored F X Y d v B :=
  ⟨fun i => (h.rows i).trans hx, fun i => (h.columns i).trans hy, h.stencil⟩

-- Witness uses only P's cover prices and fixed type multiplicities.
theorem answer : YM.Bid.E03 := by
  intro G P
  let a := (Fintype.card Layers2 : ℝ) * P.C
  let b := (Fintype.card (TypeFace 1) : ℝ) * P.C
  let d := (Fintype.card Gain : ℝ) * P.C
  let A := max 1 (max a (max b d))
  have ha : a ≤ A := le_max_of_le_right (le_max_left ..)
  have hb : b ≤ A := le_max_of_le_right (le_max_of_le_right (le_max_left ..))
  have hd : d ≤ A := le_max_of_le_right (le_max_of_le_right (le_max_right ..))
  refine ⟨A, lt_of_lt_of_le zero_lt_one (le_max_left ..), fun _L _W => ⟨Eventually.of_forall ?_⟩⟩
  intro x c f S _hL _hc T hT _F _A _U _k V _hs _hp
  obtain ⟨hm, ho, hf, -⟩ := hT.crosses
  let L : Side := S.patch.L
  have hl : 0 < (L.val : ℝ) := Bloch.side_pos _
  constructor
  · refine anchored_mono (leap_anchored S T.R (radiusB x) V P.width.le hf) ?_ ?_
    · change (Fintype.card Layers2 : ℝ)*(P.C / (L.val:ℝ)^2) ≤ A/(L.val:ℝ)^2
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right ha (by positivity)
    calc
      ((Fintype.card (Co L Layers2) : ℝ) * (P.C / (L.val:ℝ)^2)) = a * (L.val:ℝ)^2 := by
        dsimp only [a, Co]
        rw [Fintype.card_prod, site_card, Nat.cast_mul, Nat.cast_pow]
        field_simp
      _ ≤ A * (L.val:ℝ)^2 := mul_le_mul_of_nonneg_right ha (by positivity)
  · exact anchored_mono (lane_anchored T.R.mn (poleEquiv c) (meshEquiv c)
      (radiusB x) S.patch.L.val S.patch.L.property V P.width.le hm) ha hb
  · exact anchored_mono (lane_anchored T.R.o (Equiv.refl _) (meshEquiv c)
      (radiusB x) S.patch.L.val S.patch.L.property V P.width.le ho) ha hd

end YM.Work.E03
