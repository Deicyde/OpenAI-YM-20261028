import YM.Next.EXTRACTION.Base
import YM.Planned.ATOM_REGULAR_ESTIMATE.Norm
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest

/-!
Patch launch for principal field kernels. Use a single root gauge,
with bounds even on the direction weights near that anchor independent
of eventual size of the hull. (Full window aggregate from Axial is a
different, averaged absolute sum.) Never gauges over a winding halo using a
`Nonwrapping` promise on only its central link. No slack assumption on the
output marker mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform Next.Foundations
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {n : Side} {r q : ℕ} {G : Gauge}
namespace Cube
open Finset Axial
lemma march_diff (f : ℤ → ℝ) (t : ℝ) (h : ∀ j,j∈layers r → j+1∈layers r → |f (j+1)-f j| ≤ t)
    (i : ℤ) (hi : i∈layers r) : f i ≤ f 0 + (i.natAbs:ℝ)*t := by
  have zero : (0:ℤ)∈layers r := by simp [layers]
  have hl : ∀ a b : ℤ, a∈layers r → b∈layers r → a ≤ b → |f b-f a| ≤ ((b-a).natAbs:ℝ)*t := by
    intro a b ha hb hh
    induction b,hh using Int.leInduction with
    | base => simp
    | succ j hj ih =>
      have hv : j ∈ layers r := by simp only [layers,Finset.mem_Icc] at *; omega
      calc
        _ ≤ |f j - f a| + |f (j+1)-f j| := by rw [show f (j+1)-f a=(f j-f a)+(f (j+1)-f j) by abel]; exact abs_add_le ..
        _ ≤ _ := by
          apply (add_le_add (ih hv) (h _ hv hb)).trans_eq
          rw [show (j+1-a).natAbs=(j-a).natAbs+1 by omega]; push_cast; ring
  rcases le_total 0 i with H|H
  · have hh := (abs_le.mp (hl 0 i zero hi H)).2; rw [sub_zero] at hh; linarith
  have hh := (abs_le.mp (hl i 0 hi zero H)).1; rw [zero_sub,Int.natAbs_neg] at hh; linarith

lemma variation_plane {w : ℝ} (U : CoverConfig G) (hw : 0 ≤ w)
    (h : ∀ x∈box r, ∀ p : PlaqAxes, G.chord (faceValue U (x,p)) ≤ w)
    (l : List Axis) (hl : l.Nodup) (x : Cover) (hx : x∈slab r 0 l)
    (i : Axis) (he : x+step i∈slab r 0 l) :
    G.chord ((gauge (traveller l U 0) U) (x,i)) ≤ (l.length:ℝ)*r*w := by
  induction l using List.reverseRecOn generalizing x i with
  | nil =>
    have hy : (x+step i:Cover) i=x i := ((slab_iff.mp he).2 i (by simp)).trans ((slab_iff.mp hx).2 i (by simp)).symm; simp at hy
  | append_singleton l j ih =>
    rw [List.nodup_append] at hl
    have hj : j∉l := fun ha => hl.2.2 j ha j (by simp) rfl
    let X := slab r 0 (l++[j]); let V := gauge (traveller (l++[j]) U 0) U
    have H (y : Cover) (hy : y∈X) : V (y,j)=1 := vertical hj hl.1 hy (z:=0) (p:=0) (by simp [slab_iff]) U
    by_cases hh : i=j
    · subst i; rw [show gauge (traveller (l++[j]) U 0) U (x,j)=1 from H x hx, G.chord_one]; positivity
    let z := x j
    let T (k : ℤ) : Cover := x+(k-z) • step j
    let Q k := G.chord (V (T k,i))
    have hz : z∈layers r := (box_iff_layers ..).mp (slab_iff.mp hx).1 j
    have ha (k) (hk : k∈layers r) : T k ∈ slab r (update 0 j k) l := step_between hj z k hk ((lower_pin hj _).mpr ⟨hx,rfl⟩)
    have hc k (hk : k∈layers r) : T k+step i ∈ slab r (update 0 j k) l := by
      unfold T; rw [add_right_comm]; exact step_between hj z k hk ((lower_pin hj _).mpr ⟨he,by simp [z,Ne.symm hh]⟩)
    have ha' k hk := ((lower_pin hj _).mp (ha k hk)).1
    have hu k hk := ((lower_pin hj _).mp (hc k hk)).1
    have hv k (hk : k∈layers r) (hp : k+1∈layers r) : |Q (k+1)-Q k| ≤ w := by
      have he (u v) (hn : u < v) : G.chord (travel V (T k) (square u v)) ≤ w := by
        let p : PlaqAxes := ⟨(u,v),hn⟩
        change G.chord (faceValue (gauge _ U) (T k,p)) ≤ _
        rw [face_gauge,G.chord_conj]; exact h (T k) (slab_iff.mp (ha' k hk)).1 p
      have hh : T (k+1)=T k+step j := by unfold T; rw [add_sub_right_comm, add_smul,one_smul]; abel
      unfold Q; rw [hh]; apply (Axial.variation V (H _ (ha' k hk)) (H _ (hu k hk))).trans
      rcases lt_or_gt_of_ne ‹i ≠ j› with h|h
      · exact he i j h
      rw [show travel V (T k) (square i j)=(travel V (T k) (square j i))⁻¹ from oriented_swap (posDir j) (posDir i) (T k) V, G.chord_inv]
      exact he j i h
    have H0 : Q 0 ≤ (l.length:ℝ) * r * w := by
      have hh : (0:ℤ)∈layers r := by simp [layers]
      have hh₁ : T 0∈slab r 0 l := (show _ = (0:Cover) from update_eq_self j (0:Cover)) ▸ ha 0 hh
      have hh₂ : T 0+step i∈slab r 0 l := (show _ = (0:Cover) from update_eq_self j (0:Cover)) ▸ hc 0 hh
      have ht y (hy : y∈slab r 0 l) : traveller (l++[j]) U 0 y=traveller l U 0 y := by
        have hb := (slab_iff.mp hy).2 j hj
        rw [traveller,axisRoute_append]; simp only [axisRoute,List.flatMap_cons,List.flatMap_nil,List.append_nil,hb,sub_self]; simp [straight,traveller,axisRoute]
      change G.chord (traveller _ _ _ _ * _ * _⁻¹) ≤ _
      rw [ht _ hh₁, ht _ hh₂]; exact ih hl.1 _ hh₁ _ hh₂
    have hl : (z.natAbs:ℝ) ≤ r := by
      simp only [layers,Finset.mem_Icc] at hz
      exact_mod_cast (show z.natAbs ≤ r by omega)
    calc
      _ = Q z := by simp [Q,V,T] -- LHS reducible let
      _ ≤ _ := (march_diff Q w hv z hz).trans ((add_le_add H0 (mul_le_mul_of_nonneg_right hl hw)).trans_eq (by simp; ring))

open Work.E08
/-- Gauge from origin, coherent on the whole cube. Tests using log
charts further restrict to a small enough cube compared to its budget.
Here only geometry needed. -/
lemma anchored {Y : Support n} {t : ℝ} {V : Config G n}
    (o : Site n) (h : Healthy t Y V) (ht : 0≤t)
    (hy : halo (q+1) {o} ⊆ Y) (hn : 2*(q+1)<n.val) :
    ∃ g : Site n → G.El, ∀ b : Link n, separation o b.1 ≤ q →
      G.chord (gauge g V b) ≤ 4*(t*(1+separation o b.1)) := by
  let l := allAxes (1 : Lattice.Order)
  let A := traveller l (expandAt o V) 0
  let g (x : Site n) := A (lift (x-o))
  let u := box (q+1)
  have hg (x : Cover) (hx : x∈u) : g (wrap n x + o) = A x := by
    unfold g; rw [add_sub_cancel_right]; apply congrArg A; apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro i
    obtain ⟨h0,h1⟩ := box_test.mp hx; specialize h0 i; specialize h1 i; omega
  refine ⟨g, fun ⟨a,b⟩ h₁ => ?_⟩
  let c := separation o a
  let x := lift (a-o)
  have hw : wrap n x+o=a := by unfold x; rw [wrap_lift,sub_add_cancel]
  have hx : x∈box (c+1) := by
    have he (j) := (box_iff_layers ..).mp (lift_mem_box (x:=o) (y:=a) le_rfl) j
    rw [box_iff_layers]; intro j; have h := he j; change x j∈layers c at h; unfold layers at *; simp only [Finset.mem_Icc] at *; omega
  have hb : x+step b ∈ box (c+1) := by
    obtain ⟨hi,hj⟩ := box_test.mp (lift_mem_box (x:=o) (y:=a) le_rfl)
    change _ ∈ box (separation o a+1)
    rw [box_test]; constructor <;> intro i <;> unfold x <;> simp only [Pi.add_apply,step_apply] <;> split <;>
      have ho := hi i <;> have hq := hj i <;> omega
  have h' : box (c+1) ⊆ u := fun z hz => by
    obtain ⟨hi,hj⟩ := box_test.mp hz
    have hq : c ≤ q := h₁
    apply box_test.mpr; constructor <;> intro i <;> have ho:=hi i <;> have hh:=hj i <;> omega
  have ht' : ∀ p∈box (c+1), ∀ f : PlaqAxes, G.chord (faceValue (expandAt o V) (p,f)) ≤ t := by
    intro p hp f; unfold faceValue; rw [travel_at]; change G.chord (faceValue V (wrap n p+o,f)) ≤ _
    have hh : wrap n p+o ∈ Y := hy (halo_spec.mpr ⟨o,by simp,separation_box_add o (h' hp)⟩)
    by_contra! he; exact Finset.disjoint_left.mp h hh ((flags_spec ..).mpr ⟨(wrap n p+o,f),by simp [touched,square_corners],he⟩)
  have hQ : slab (c+1) 0 l=box (c+1) := by
    ext x; simp only [slab_iff]; exact ⟨And.left,fun hh => ⟨hh,fun i hi => False.elim (hi (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))⟩⟩
  have he := variation_plane _ ht ht' l ((List.nodup_finRange _).map (1:Lattice.Order).injective)
    x (hQ.symm ▸ hx) b (hQ.symm ▸ hb)
  have ha : (l.length:ℝ)=4 := by simp [l,allAxes]
  calc
    _ = G.chord (expandAt o (Lattice.gauge g V) (x,b)) := by simp [expandAt,hw]
    _ = G.chord (Lattice.gauge A (expandAt o V) (x,b)) := by rw [expandAt_gauge]; simp only [Lattice.gauge,hg _ (h' hx),hg _ (h' hb)]
    _ ≤ _ := he.trans (by rw [ha]; push_cast; change _ ≤ 4*(t*(1+(c:ℝ))); apply le_of_eq; ring)
end Cube
end YM.Planned.AtomRegular.Foliage
