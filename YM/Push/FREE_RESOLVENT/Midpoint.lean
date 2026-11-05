import YM.Corona.Spend
import YM.Push.FREE_RESOLVENT.Layout

/-!
# Checking the  window

Physical distance to link midpoint on periodic torus, computed on the
*doubled* site lattice. Includes even-side ties. No interior-only equivalence
of metrics used. Therefore the actual window selection keeps rotated bond
placements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix TestD Mark  Filter Function Set Lattice RG Precision Wilson Tree
open Exterior Affine
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c n f : Side} {S : StepData c f} {u σ M A : ℝ} {W : PathData G}
namespace Mid

def double (n : Side) : Ratio n (n*2) := ⟨2,rfl⟩

def axis (e : Edge (Site n)) : Site (n*2) := (double n).embed e.1 + step e.2

def cull (e : Slot G n 1) : Edge (Site n) := (e.1, axisEquiv.symm e.2.1)

lemma piece (e : Edge (Site n)) (s : Signed) (t : Site n) :
    axis (sendEdge s t e)=affine s ((double n).embed t) (axis e) := by
  let w := (posDir e.2).rotate s
  let q := double n; let y := affine s t e.1
  have he : (affine s (q.embed t) (axis e))=q.embed y+w.vec := by
    have hh : (w.vec:Site (n*2))=s.act (step e.2) := by unfold w; rw [Step.vec_rotate, Step.vec_pos]
    rw [hh]; unfold affine y axis
    rw [Signed.act_add, ← Ratio.signed]; unfold affine; rw [show q.embed _ = _ from q.root.map_add (s.act e.1) t]
    change q.embed _ + _ + _ = _ + q.embed t+_; rw [q.root_embed]; abel
  rw [he]; change axis (w.used y) = _
  rcases h : w with ⟨i,x|x⟩
  · rfl
  change q.embed (y-step i)+step i=q.embed y+-step i
  have hh := q.embed_leap (y-step i) i; rw [sub_add_cancel] at hh
  rw [hh,show q.count.val=2 from rfl,two_nsmul]; abel

lemma turned (e f : Edge (Site n)) (s : Signed) (t : Site n) :
    separation (axis (sendEdge s t e)) (axis (sendEdge s t f))=separation (axis e) (axis f) := by simp only [piece,affine, separation_signed,separation_translate]

lemma upto (g : Ratio c f) (x y : Site c) :
    separation (g.embed x) (g.embed y)=g.count.val*separation x y := by
  apply le_antisymm _ (Corona.below g x y); unfold separation
  rw [← g.root_embed, ← g.root_embed,← map_sub,g.root_embed]; apply Finset.sup_le
  intro i _
  rw [g.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (component_le (x-y) i)

lemma priced (S : StepData c f) (p q : Slot G f 1) :
    let h := separation (home S p) (home S q)
    let L := S.patch.L.val
    separation (axis (cull p)) (axis (cull q)) ≤ 2*(L*h+L)+2 := by
  intro h L; let g := S.ratio
  have hh : separation p.1 q.1 ≤ L*h+L := by
    have h1 := Corona.near g p.1; have h2 := Corona.near g q.1
    have he : separation (g.embed (g.parent p.1)) (g.embed (g.parent q.1))=L*h := upto g _ _
    have hh := separation_triangle p.1 (g.embed (g.parent p.1)) (g.embed (g.parent q.1)); rw [he] at hh
    have hu := separation_triangle p.1 (g.embed (g.parent q.1)) q.1
    rw [separation_comm (g.embed (g.parent q.1)) q.1] at hu
    change _ ≤ L at h1 h2; omega
  have hw : separation ((double f).embed p.1) ((double f).embed q.1) ≤ 2*(L*h+L) :=
    (upto ..).trans_le (Nat.mul_le_mul_left 2 hh)
  have hP (p : Slot G f 1) : separation ((double f).embed p.1) (axis (cull p)) ≤ 1 := Work.E03.sep_step ..
  have hx := separation_triangle (axis (cull p)) ((double f).embed p.1) ((double f).embed q.1)
  have hu := separation_triangle (axis (cull p)) ((double f).embed q.1) (axis (cull q)); rw [separation_comm _ ((double f).embed p.1)] at hx
  have hm := hP p; have ht := hP q; omega

/-- Entries of the  closed windows. -/
def window (S : StepData c f) (B : ℕ) (p : Slot G f 1) := Finset.univ.filter fun q : Slot G f 1 =>
  20 * separation (axis (cull p)) (axis (cull q)) ≤ 2*S.patch.L.val*B

lemma member (S : StepData c f) (B : ℕ) (p : Slot G f 1) : p ∈ window S B p := by simp [window]

def cutView (G : Gauge) (S : StepData c f) (B : ℕ) := ({
    loc _ := Function.Embedding.subtype _
    root p := ⟨p,member ..⟩
    atRoot _ := rfl
  } : Window.Survey (fun p : Slot G f 1 => ↥(window S B p)))

lemma near (G : Gauge) (S : StepData c f) (B : ℕ) (hB : 200 ≤ B) : (cutView G S B).Near (native c) (home S) ((B:ℝ)/25) := by
  intro i j h
  have H : j ∉ window S B i := fun he => h ⟨⟨_,he⟩,rfl⟩
  simp only [window,Finset.mem_filter,Finset.mem_univ,true_and] at H
  have hx := Nat.lt_of_not_ge H
  let q := separation (home S i) (home S j)
  let L := S.patch.L.val
  have hu : 2*L*B < 20*(2*(L*q+L)+2) := lt_of_lt_of_le hx (Nat.mul_le_mul_left 20 (priced S i j))
  have hl : 3 ≤ L := S.patch.coarse
  have he : B ≤ 25*q := by
    have hp : L*B ≥ L*200 := Nat.mul_le_mul_left L hB
    by_contra! h
    have hh : L*(25*q) ≤ L*B := Nat.mul_le_mul_left L h.le
    nlinarith
  change ↑B/25 ≤ (q:ℝ); rw [div_le_iff₀ (by norm_num), mul_comm]
  exact_mod_cast he
end Mid
end YM.FreeResolvent
