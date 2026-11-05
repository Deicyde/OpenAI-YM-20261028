import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Chroma

/-!
# real jets of energy on ANY V chart, U hard inputs fixed option

C projected coordinates in Frobenius. Keep haptic asymmetry for future moving
cores. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {o : Site c} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k j : ℕ} {U : E→ Config G f} {V Q : E→ Config G c} {x : E} {v z a w b d e : ℝ}
open Brush

lemma stroke {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {A B : E → Y} (p : Brush k v d A x) (h : Brush k w e B x) :
    Brush k (v*w) (d+e) (fun i=> inner ℝ (A i) (B i)) x := by
  let L := innerSL ℝ (E:=Y)
  apply (p.twins h L).climb _ le_rfl
  apply mul_le_of_le_one_left (mul_nonneg p.nonneg h.nonneg); apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x; rw [one_mul]; apply ContinuousLinearMap.opNorm_le_bound (L x) (norm_nonneg x); intro i; exact abs_real_inner_le_norm ..
lemma squared {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {A : E→Y} (p : Brush k v d A x) :
    Brush k (v*v) (d+d) (fun i=> ‖A i‖^2) x := by simpa only [real_inner_self_eq_norm_sq] using! stroke p p
lemma semi {A : E→ℝ} (p : Brush k v d A x) : Brush k v d (fun i=> A i/2) x := by
  have he : (fun i=> A i/2)=(fun i=> (1/2:ℝ) • A i) := by ext; simp; ring
  rw [he]; apply (p.smul _).climb _ le_rfl; rw [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  exact mul_le_of_le_one_left p.nonneg (by norm_num)

def flawBill (G : Gauge) : ℝ := (royalty G ^2)⁻¹*((royalty G+royalty G)*(royalty G+royalty G))+1*1
lemma cracked {f : E→G.El} (p : Brush k (royalty G) d (G.mat ∘ f) x) :
    Brush k (flawBill G) (d+d) (fun i=> flaw (f i)) x := by
  let a x:= ‖G.mat (f x)-1‖^2
  let c:= royalty G
  have hh : Brush k ((c+c)*(c+c)) (d+d) a x := squared (p.separating (a_oneB G 1 p.pos))
  have hv := hh.smul ((c^2)⁻¹)
  have he : 1 ≤ c := royalty_ge G
  rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (c^2)⁻¹)] at hv
  have hp : (fun i=> flaw (f i))=(fun i => (((c^2)⁻¹) • a i-‖G.curvature (f i)‖^2)/2) := by
    ext; unfold flaw Gauge.chord a; rw [div_pow, div_eq_mul_inv (‖_‖^2),mul_comm (‖_‖^2)]; rfl
  rw [hp]; exact semi (hv.separating (squared (sculpt p)))

namespace Quill

variable {C R B D C' D' : ℝ} (M : ℕ) (p : Primary P U V Q x C D M T k) (h : Canopied U V Q M k T C' D' R B x)
    (hp : D ≤ D') (ht : D' ≤ B)
include h
lemma canopy_read (i : Rod c f) : Brush k C' D' (fun z=> visual T M (V z) i) x := by
  rcases i with i|i
  · exact h.p0 i
  exact h.p1 i
include p hp
lemma talents (i : Rod c f) : Brush k (C+C') D' (fun z=> effective T M (U z) (Q z) (V z) i) x := by
  let f z:= Sum.elim (T.Xf M (U z)) (Tube.Z S (Q z) (V z)) i
  apply Brush.separating (p:=?_) (canopy_read M h i); change Brush k C D' f x
  rcases i with i|i
  · exact (p.high i).climb le_rfl hp
  exact (p.wanted i).climb le_rfl hp

def ldCost (C D : ℝ) := 2*(C*(D+D+C))
def octaves (C D : ℝ) := 2*(C*(C+(D+D+D)))
include p h hp
lemma graceL (i : Cell c) : Brush k (ldCost C C') (D'+D') (fun z=> stormL T M (U z) (Q z) (V z) i) x := by
  have hb : 0 ≤ D'+D' := add_nonneg ((p.hill).trans hp) ((p.hill).trans hp)
  unfold stormL; refine (Brush.spree _ _ (fun _=>C*(C'+C'+C)) hb (fun j _ => ?_)).climb ?_ le_rfl
  · exact stroke ((p.down (i,_)).climb le_rfl hp) (((h.warp (i,_)).gathering (h.wear (i,_))).separating ((p.down (i,_)).climb le_rfl hp))
  unfold ldCost; simp
include ht in
lemma graceD (i : Cell c) : Brush k (octaves C R) (B+B) (fun z=> stormD T M (V z) i) x := by
  have hb : 0≤B := p.hill.trans (hp.trans ht)
  unfold stormD; refine (Brush.spree _ _ (fun _=> C*(C+(R+R+R))) (add_nonneg hb hb) (fun j _=>?_)).climb ?_ le_rfl
  · have he := (p.down (i,j)).climb le_rfl (hp.trans ht)
    exact semi (stroke he (he.separating (((h.wo _).gathering (h.wq (i,j))).gathering (h.wp (i,j)))))
  unfold octaves; simp
lemma beautyF (i : Cell f) (hu : Mode U x k v) (hy : 4*(v*royalty G)≤D') : Brush k
    (‖T.high.direct‖*flawBill G+2*((C+C')*(C+C'))) (D'+D') (fun z=> flora T M (U z) (Q z) (V z) i) x := by
  have hv : Brush k (royalty G) (4*(v*royalty G)) (fun z=> G.mat (faceValue (U z) i)) x := by convert! tour (U:=U) (square i.2.val.1 i.2.val.2) i.1 hu.pos hu.atLink using 1
  have hh := (cracked (f:=fun z=> faceValue (U z) i) (hv.climb le_rfl hy)).smul T.high.direct
  have hg := Brush.spree (Finset.univ (α:=Bool)) _ _ hh.pos (fun z _=> semi (squared (talents M p h hp (.inl (i,z)))))
  exact hh.gathering (hg.climb (by simp) le_rfl)
lemma beautyI (i : Bond c) (hv : Mode V x k v) (hQ : Mode Q x k v) (hy : v*royalty G+v≤D') : Brush k
    (‖S.kernel.penalty‖ * flawBill G+(C+C')*(C+C')) (D'+D') (fun z=> nora T M (U z) (Q z) (V z) i) x := by
  have hs := links (hv.atLink i) (reverse (f:=fun x=>Q x i) (hQ.atLink i)) (royalty G) (max_le (royalty_ge G) le_rfl)
  exact ((cracked (f:=fun x=> V x i*(Q x i)⁻¹) (hs.climb le_rfl hy)).smul S.kernel.penalty).gathering (semi (squared (talents M p h hp (.inr i))))
end Quill
end YM.ConnectedActivityE6.Blaze
