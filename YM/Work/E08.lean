import YM.Bid.Energy
import YM.Corona.Spend
import YM.TimeKernel.Trace
import YM.Vac.Treasury


/-!
# E08: chord size on unaffected cones at post-L costs.

Work with the same tags and actual input/output fields. Use the total
axial edge bound on a box in the coarse cover, allowing polynomial
loss; no regularity across sectors is needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E08

open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree
open Pressure Pressure.Stores Pressure.Teller Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-! Numerics are for fixed post-L parameters. -/

lemma eventual_radiusB (k : ℕ) : ∀ᶠ x : ℝ in atTop, k ≤ radiusB x := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((k:ℝ)+1)] with x hx
  have hk : (k:ℝ) ≤ (Real.log x)^2 := by nlinarith only [hx, Nat.cast_nonneg (α:=ℝ) k]
  exact_mod_cast hk.trans (Nat.le_ceil _)

lemma eventual_fiery (G : Gauge) (L : Side) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * fiery G x L ≤ largeT G x L := by
  let e : ℝ := 1/200
  have he : 0 < e := by unfold e; norm_num
  have ht : Tendsto (fun x => betaF G x L) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hc := ht.eventually (Vac.Numbers.cost 1 e he)
  filter_upwards [hc, ht.eventually_gt_atTop 0,
      ht.eventually ((tendsto_rpow_atTop he).eventually_ge_atTop C)] with x hx hpos hC
  let s := betaF G x L
  have hs : 0 < s := hpos
  have hP : Vac.Numbers.P s ≤ s^e := by simpa only [Real.rpow_one] using hx
  change C ≤ s^e at hC
  have hi : (Real.sqrt s)⁻¹ = s^(-(1/2:ℝ)) := by rw [Real.rpow_neg hs.le,Real.sqrt_eq_rpow]
  change C * ((Real.sqrt s)⁻¹ * Vac.Numbers.P s) ≤ ((Real.sqrt s)⁻¹) ^ ((98:ℝ)/100)
  rw [hi, ← Real.rpow_mul hs.le]
  rw [mul_left_comm C]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul hC hP (Real.exp_pos _).le (by positivity)) (by positivity : 0 ≤ s ^ (-(1/2:ℝ)))).trans
  rw [← Real.rpow_add hs, ← Real.rpow_add hs, show -(1/2:ℝ)+(e+e) = -(1/2:ℝ)*(98/100) by unfold e; norm_num]

variable {n c f : Side} {G : Gauge}

lemma separation_box_add (x : Site n) {i : Cover} {r} (h : i ∈ box r) :
    separation x (wrap n i + x) ≤ r := by
  rw [separation_comm, separation, add_sub_cancel_right]
  obtain ⟨h1,h2⟩ := box_test.mp h
  apply Finset.sup_le
  intro a _
  apply (Corona.lap i a).trans
  have := h1 a; have := h2 a; omega

lemma lift_mem_box {x y : Site n} {r} (h : separation x y ≤ r) : lift (y-x) ∈ box r := by
  rw [separation_comm, separation] at h
  rw [box_test]
  constructor <;> intro i <;> have he := (component_le (y-x) i).trans h <;> omega

lemma faces_expand_le (o : Site n) (U : Config G n) (r : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (h : ∀ x ∈ box r, ∀ p : PlaqAxes, toll U (wrap n x + o,p) ≤ q) :
    faces (box r) (expandAt o U) ≤ (2*(r:ℝ)+1)^4 * (Fintype.card PlaqAxes:ℝ) * q := by
  unfold faces field
  calc
    _ ≤ ∑ _x ∈ box r, ∑ _p : PlaqAxes, q := by
      refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun p _ => ?_
      unfold face; split
      · unfold faceValue; rw [travel_at]; exact h x hx p
      exact hq
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, Corona.box_size]
      push_cast; ring

/-- Descend the cover estimate to bonds in a strictly smaller periodic patch.
Pay the total edge bound even for an individual bond. -/
lemma axial_patch (o : Site n) (U : Config G n) (d r : ℕ) (hdr : d + 1 ≤ r)
    (hsize : 2*r < n.val) (q : ℝ) (hq : 0 ≤ q)
    (hface : ∀ y : Site n, separation o y ≤ r → ∀ p : PlaqAxes, toll U (y,p) ≤ q) :
    ∃ z : Site n → G.El, ∀ b : Bond n, separation o b.1 ≤ d →
      G.chord (Lattice.gauge z U b) ≤
        16*(2*(r:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ) * q := by
  let l := allAxes (1:Lattice.Order)
  let X := box r
  let V := expandAt o U
  obtain ⟨a,-,ha⟩ := Axial.existence l r 0 V
    ((List.nodup_finRange _).map (1:Lattice.Order).injective) (center_box r)
  let H := traveller l V a
  have hl : slab r 0 l = box r := by
    have h (i : Axis) : i ∈ l := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    ext i; simp [slab_iff,h]
  rw [hl,card_layers, show l.length=4 by simp [l,allAxes]] at ha
  push_cast at ha
  have hsum : edges X (gauge H V) ≤
      16*(2*(r:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ) * q := by
    apply ha.trans
    apply (mul_le_mul_of_nonneg_left
      (faces_expand_le o U r q hq (fun x hx p => hface _ (separation_box_add o hx) p))
      (by positivity)).trans_eq
    ring
  let z := fun y : Site n => H (lift (y-o))
  have hH (x : Cover) (hx : x ∈ box r) : z (wrap n x + o) = H x := by
    unfold z; rw [add_sub_cancel_right]
    apply congrArg H
    apply lift_eq_iff.mpr ⟨rfl,?_⟩
    intro j
    have hi := (box_test.mp hx).1 j
    have hj := (box_test.mp hx).2 j
    omega
  refine ⟨z,fun ⟨b,i⟩ hd => ?_⟩
  let x := lift (b-o)
  have hx : x∈box d := lift_mem_box hd
  obtain ⟨hb,hb'⟩ := box_test.mp hx
  have h1 : x ∈ X := box_test.mpr ⟨fun j => by have := hb j; omega,fun j => by have := hb' j; omega⟩
  have h2 : x + step i ∈ X := by
    unfold X; rw [box_test]
    constructor <;> intro j <;> simp only [Pi.add_apply,step_apply] <;>
      split <;> have ho := hb j <;> have ho' := hb' j <;> omega
  have hy : wrap n x + o = b := by unfold x; rw [wrap_lift,sub_add_cancel]
  calc
    _ = G.chord (expandAt o (Lattice.gauge z U) (x,i)) := by simp only [expandAt,hy]
    _ = perEdge X (Lattice.gauge H V) x i := by
      rw [expandAt_gauge]
      simp only [Lattice.gauge,perEdge,if_pos h2,hH x h1,hH _ h2,V]
    _ ≤ ∑ j : Axis, perEdge X (Lattice.gauge H V) x j := Finset.single_le_sum
          (f:=perEdge X (Lattice.gauge H V) x) (fun _ _ => per_nn ..) (Finset.mem_univ i)
    _ ≤ edges X (Lattice.gauge H V) := Finset.single_le_sum
          (f:=fun x => ∑ j : Axis, perEdge X (Lattice.gauge H V) x j)
          (fun _ _ => Finset.sum_nonneg fun _ _ => per_nn ..) h1
    _ ≤ _ := hsum

variable {S : StepData c f} {x w : ℝ}
variable {A : Stores S} {U : Config G f} {k : S.Choices} {V : Config G c} {p : Cell c}

lemma out_near_dome (hp : p ∈ A.outs x) {y} (hy : separation p.1 y ≤ 4*radiusB x/5) :
    y ∈ A.dome (5*radiusB x) := by
  have h0 := (Finset.mem_filter.mp hp).2
  obtain ⟨z,hz,hzp⟩ := halo_spec.mp h0
  refine halo_spec.mpr ⟨z,hz,?_⟩
  have h := separation_triangle z p.1 y
  omega

/-- Nearby fine plaquette roots (projected) and noise bond roots have
size ≤ largeT. Use Plot where not listed and exploit spend where listed. -/
lemma unhit_local (hplot : Plot A U k V x w) (hp : p ∈ A.outs x)
    (hunhit : p ∉ A.hit U (S.prediction U k) V x)
    (ht : fiery G x S.patch.L/2 ≤ largeT G x S.patch.L)
    (hw : 2*w*fiery G x S.patch.L ≤ largeT G x S.patch.L) :
    (∀ b : Cell f, separation p.1 (S.ratio.parent b.1) ≤ 4*radiusB x/5 →
      toll U b ≤ largeT G x S.patch.L) ∧
    (∀ b : Bond c, separation p.1 b.1 ≤ 4*radiusB x/5 →
      wire (S.prediction U k) V b ≤ largeT G x S.patch.L) := by
  let Q := S.prediction U k
  let E := A.spend U Q V x
  have hh (y : Site c) (hy : separation p.1 y ≤ 4*radiusB x/5) (he : y ∈ E.place) : False :=
    hunhit (Finset.mem_filter.mpr ⟨hp,halo_spec.mpr
      ⟨y,he,(separation_comm p.1 y) ▸ hy⟩⟩)
  constructor
  · intro b hb
    let y := S.ratio.parent b.1
    have hi : y ∈ startPos S b := Finset.mem_image_of_mem _ (by simp [touched,visits,square])
    by_cases hy : b ∈ A.costs
    · by_contra! h
      have hsub : b ∈ E.costs := Finset.mem_filter.mpr ⟨hy,h⟩
      exact hh y hb (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨b,hsub,hi⟩)))
    have hm := hplot.consumes b fun H =>
      Finset.disjoint_left.mp H (out_near_dome hp hb) hi
    exact (hm.2 hy).trans ht
  intro b hb
  have hi : b.1 ∈ pinPos b := by simp [pinPos]
  by_cases hy : b ∈ A.aisles
  · by_contra! h
    have hsub : b ∈ E.aisles := Finset.mem_filter.mpr ⟨hy,h⟩
    exact hh b.1 hb (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨b,hsub,hi⟩)))
  have hm := hplot.drive b fun H =>
    Finset.disjoint_left.mp H (out_near_dome hp hb) hi
  exact (hm.2 hy).trans hw

/-- Bound a port by the maximum charge times size of the macro patch.
Charge even with repetitions; this is a post-L bound. -/
lemma port_le (o : Site c) (b : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (htoll : ∀ i : Cell f, separation o (S.ratio.parent i.1) ≤ b → toll U i ≤ q)
    (y : Site c) (hy : separation o y + macroR S.patch + S.patch.L.val ≤ b) :
    port S y U ≤ (2*(macroR S.patch:ℝ)+1)^4 * (Fintype.card PlaqAxes:ℝ) * q := by
  apply faces_expand_le (S.ratio.embed y) U _ q hq
  intro z hz a
  apply htoll
  let x' := wrap f z + S.ratio.embed y
  change separation o (S.ratio.parent x') ≤ b
  have hi := Corona.foreshorten S.ratio (S.ratio.embed y) x'
  rw [S.ratio.embed_parent] at hi
  have hj : separation (S.ratio.embed y) x' ≤ macroR S.patch := separation_box_add _ hz
  change S.patch.L.val * _ ≤ _ + S.patch.L.val at hi
  have he : separation y (S.ratio.parent x') ≤ S.patch.L.val * separation y (S.ratio.parent x') := by
    have hL : 1 ≤ S.patch.L.val := S.patch.L.property
    exact (by simpa using Nat.mul_le_mul_right (separation y (S.ratio.parent x')) hL)
  have hs := separation_triangle o y (S.ratio.parent x')
  omega

lemma stitches_of_shell (e02 : Bid.E02) (P : Teller G) (L : Side) (W : ℝ) (_hW : 0 < W) :
    Stitches P L W := by
  obtain ⟨J,hJ,HJ⟩ := qdc G P.bind P.j
  obtain ⟨D,hD,HD⟩ := e02 G L P.j P.bind
  -- M fine sites; K the macro face count bound; F' the coarse plaquette
  -- price in largeT units. H the edge price coefficient, excluding B^5.
  let M := (P.j + 3)*L.val + 4*L.val
  let nP := (Fintype.card PlaqAxes:ℝ)
  let K : ℝ := (2*(M:ℝ)+1)^4*nP
  let F' := 4 + J/(L.val:ℝ)^2*K
  let H : ℝ := 16*3^5*nP*F'
  have hnP : 0 ≤ nP := Nat.cast_nonneg _
  have hK : 0 ≤ K := by unfold K; positivity
  have hF : 0 < F' := by unfold F'; positivity
  have hH : 0 ≤ H := by unfold H; positivity
  let C := H + (D*K + 1)
  refine ⟨C,by unfold C; positivity,⟨?_⟩⟩
  filter_upwards [eventual_radiusB (20*(M+L.val+1)), eventual_fiery G L (2*W),
      eventual_fiery G L (1/2)] with x hx hw ht
  intro c f S hL hs T Hfund F A U k V hslice hplot
  let B := radiusB x
  let r := B/2
  let a := largeT G x L
  let Q := S.prediction U k
  change ∀ p ∈ A.outs x, p ∉ A.hit U Q V x → ∃ z : Site c → G.El,
    (∀ i : Bond c, separation p.1 i.1 ≤ 2*B/5 → G.chord (Lattice.gauge z V i) ≤ C*(B:ℝ)^10*a) ∧
    ∀ i : Bond f, separation p.1 (S.ratio.parent i.1) ≤ 2*B/5 →
      G.chord (Lattice.gauge (z∘S.ratio.parent) U i) ≤ C*(B:ℝ)^10*a
  intro p hp hunhit
  have hj := Hfund.atStep
  have hb := Hfund.knobs
  have hm : macroR S.patch=M := by unfold macroR RG.Patch.radius; rw [hL,hj]
  have ha : 0 ≤ a := by unfold a largeT; positivity
  change 20*(M+L.val+1) ≤ B at hx
  change 100*(1+B) ≤ c.val at hs
  have hsize : 100*macroR S.patch ≤ f.val := by
    have hcf : c.val ≤ f.val := by
      rw [S.sizes]
      have h : 1 ≤ S.patch.L.val := S.patch.L.property
      simpa using (Nat.mul_le_mul_left c.val h)
    omega
  have hB0 : 1 ≤ B := by omega
  have hBd : 2*B/5+1 ≤ r := by unfold r; omega
  -- r and all needed inputs fit inside 4B/5.
  have hr : r + M + L.val ≤ 4*B/5 := by unfold r; omega
  have hr2 : r + 2 ≤ 4*B/5 := by unfold r; omega
  obtain ⟨hsmall,hnoise⟩ := unhit_local hplot hp hunhit
    (by rw [hL]; linarith only [ht]) (by rw [hL]; exact hw)
  rw [hL] at hsmall hnoise
  -- port bound and usable on the coarse patch.
  have hport (y : Site c) (h : separation p.1 y ≤ r) : port S y U ≤ K*a := by
    have he : separation p.1 y + macroR S.patch + S.patch.L.val ≤ 4*B/5 := by
      rw [hm,hL]; omega
    have hg := port_le p.1 (4*B/5) a ha hsmall y he
    rw [hm] at hg; exact hg
  have huse (y : Site c) (h : separation p.1 y ≤ r) : usable S U y k := by
    intro z hz; apply hplot.list; apply out_near_dome hp
    have hi : separation y (plank y z) ≤ 2 := separation_box_add _ hz
    have hh := separation_triangle p.1 y (plank y z)
    change separation _ _ ≤ 4*B/5; omega
  have hface (y : Site c) (h : separation p.1 y ≤ r) (j : PlaqAxes) :
      toll V (y,j) ≤ F'*a := by
    have he := (HJ c f S hb.symm hj.symm U V y k (huse y h) j).2
    rw [hL] at he
    apply he.trans
    have hb0 (k' : Axis) : wire Q V (y,k') ≤ a := by
      apply hnoise; change separation p.1 y ≤ 4*B/5; omega
    have hb1 (j' k' : Axis) : wire Q V (y + step j',k') ≤ a := by
      apply hnoise
      have hi : separation y (y+step j') ≤ 1 := by
        rw [separation_comm,separation,add_comm y, add_sub_cancel_right]; exact pdist_step _
      have hh := separation_triangle p.1 y (y+step j')
      change separation p.1 (y+step j') ≤ 4*B/5; omega
    have hfuel : Pressure.fuel Q V y j ≤ 4*a :=
      (add_le_add (add_le_add (add_le_add (hb0 _) (hb1 _ _)) (hb1 _ _))
        (hb0 _)).trans_eq (show a+a+a+a = 4*a by ring)
    apply (add_le_add hfuel (mul_le_mul_of_nonneg_left (hport y h)
      (by positivity : 0 ≤ J/(L.val:ℝ)^2))).trans_eq
    unfold F'; ring
  -- Coarse gauge patch.
  obtain ⟨z,hz⟩ := axial_patch p.1 V (2*B/5) r hBd (by unfold r; omega)
    (F'*a) (by positivity) hface
  have hB : 1 ≤ (B:ℝ) := by exact_mod_cast hB0
  let t0 := H*(B:ℝ)^5*a
  have hzV (b : Bond c) (h : separation p.1 b.1 ≤ 2*B/5) :
      G.chord (Lattice.gauge z V b) ≤ t0 := by
    apply (hz b h).trans
    have hi : (r:ℝ) ≤ (B:ℝ) := by exact_mod_cast Nat.div_le_self B 2
    have hh : 2*(r:ℝ)+1 ≤ 3*(B:ℝ) := by linarith
    change 16*(2*(r:ℝ)+1)^5*nP*(F'*a) ≤ _
    calc
      _ ≤ 16*(3*(B:ℝ))^5*nP*(F'*a) := by gcongr
      _ = _ := by unfold t0 H; ring
  have ht0 : 0 ≤ t0 := by unfold t0; positivity
  have htotal : (D*K+1)*a + t0 ≤ C*(B:ℝ)^10*a := by
    have h1 : 1 ≤ (B:ℝ)^10 := one_le_pow₀ hB
    have h2 : (B:ℝ)^5 ≤ (B:ℝ)^10 := pow_le_pow_right₀ hB (by norm_num)
    calc
      _ ≤ (D*K+1)*(B:ℝ)^10*a + H*(B:ℝ)^10*a := by
        apply add_le_add _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hH) ha)
        apply mul_le_mul_of_nonneg_right _ ha
        simpa using mul_le_mul_of_nonneg_left h1 (show 0 ≤ D*K+1 by positivity)
      _ = _ := by unfold C; ring
  refine ⟨z,fun b h => le_trans (hzV b h) ((le_add_of_nonneg_left (by positivity)).trans htotal),
    fun b h => ?_⟩
  -- Fine links. Compare to replica V via E02 in the original gauge,
  -- then apply simultaneous block-constant gauge.
  let R := replica S.ratio V
  let y := S.ratio.parent b.1
  have hy : separation p.1 y ≤ r := by change separation p.1 y ≤ _ at h; omega
  have he : G.chord (U b*(R b)⁻¹) ≤ (D*K+1)*a := by
    have he := HD c f S hb hL hj hsize (by omega) F U hslice V b k (huse y hy)
    apply he.trans
    have hw' : wire Q V (y,b.2) ≤ a := by
      apply hnoise; change separation p.1 y ≤ 4*B/5; omega
    have hw'' : (if y=S.ratio.parent (b.1+step b.2) then 0 else wire Q V (y,b.2)) ≤ a := by
      split <;> assumption
    apply (add_le_add (mul_le_mul_of_nonneg_left (hport y hy) hD.le)
      hw'').trans_eq
    ring
  let g := z∘S.ratio.parent
  have hc : G.chord (gauge g R b) ≤ t0 := by
    change G.chord (gauge (constantGauge z S.ratio) (replica S.ratio V) b) ≤ t0
    rw [copied _ S.patch.odd_side V z]
    unfold replica; split
    · rw [G.chord_one]; exact ht0
    exact hzV _ h
  have hh : gauge g U b = (g b.1*(U b*(R b)⁻¹)*(g b.1)⁻¹)*gauge g R b := by
    unfold Lattice.gauge; group
  change G.chord (gauge g U b) ≤ _
  rw [hh]
  apply (G.chord_triangle _ _).trans
  rw [G.chord_conj]
  exact (add_le_add he hc).trans htotal

theorem answer : YM.Bid.E08 := by
  intro _ e02 G P L W hW
  exact stitches_of_shell e02 P L W hW

end YM.Work.E08
