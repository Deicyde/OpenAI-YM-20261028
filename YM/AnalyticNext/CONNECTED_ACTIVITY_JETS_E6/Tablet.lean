import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood

/-!
# Matrix joint jets: preserve real glides; derivative order both ways

Use row/column Price of vertex norms. Entries combine repeatedly without
unknown dimensional constant. Zeros of tails: may erase them before pricing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c : Side} {E ι κ ν : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush
variable {v z f g : ℝ} {k : ℕ} {A B : E→Matrix ι κ ℝ} {K : E → Matrix κ ν ℝ}
variable [Fintype ι] [Fintype κ] {x : E} {a : ι → Site c} {b : κ → Site c} {d : ν → Site c} {η γ : ℝ}

structure Tablet (k : ℕ) (η f v : ℝ) (A : E → Matrix ι κ ℝ) (a : ι → Site c) (b : κ → Site c) (x : E) : Prop where
  scale : 0≤η
  pos : 0≤v
  basis : 0≤f
  shape : ∃ B : Matrix ι κ ℝ, (∀ i j, Brush k (B i j) v (fun x=>A x i j) x) ∧ Price a b B η f

namespace Tablet
variable (p : Tablet k η f v A a b x)
include p
lemma tilt (hf : f ≤ g) (hd : v ≤ z) (h : 0≤γ) (he : γ ≤ η) : Tablet k γ g z A a b x := by
  obtain ⟨B,hB,hp⟩:=p.shape; exact ⟨h,p.pos.trans hd,p.basis.trans hf, B,
    fun i j=>(hB i j).climb le_rfl hd,increase hp he hf⟩
lemma enjoin [Fintype ν] (h : Tablet k η g z K b d x) : Tablet k η (f*g) (v+z) (fun x=>A x*K x) a d x := by
  obtain ⟨B,hB,hp⟩:=p.shape; obtain ⟨W,hW,hw⟩:= h.shape
  have hz := add_nonneg p.pos h.pos
  refine ⟨p.scale,hz,mul_nonneg p.basis h.basis, B*W,fun i j=> ?_, paid_mul hp hw p.scale p.basis h.basis⟩
  simp_rw [Matrix.mul_apply]; exact spree _ _ _ hz (fun u _=> (hB i u).paints (hW u j))

lemma joined (q : Tablet k η g v B a b x) : Tablet k η (f+g) v (A+B) a b x := by
  obtain ⟨B,hB,hp⟩:= p.shape; obtain ⟨D,hD,hq⟩:=q.shape
  refine ⟨p.scale,p.pos,add_nonneg p.basis q.basis, B+D, fun i j=> (hB i j).gathering (hD i j), ⟨hp.1.plus hq.1,?_⟩⟩
  rw [transpose_add]; exact hp.2.plus hq.2
lemma mirror : Tablet k η f v (-A) a b x := by
  obtain ⟨B,hB,h⟩:= p.shape; exact
    ⟨p.scale,p.pos,p.basis,B,fun i j=>(hB i j).opposite,h⟩
lemma scalar (u : ℝ) : Tablet k η (‖u‖*f) v (u • A) a b x := by
  obtain ⟨B,hB,h⟩ := p.shape; refine ⟨p.scale,p.pos,mul_nonneg (norm_nonneg _) p.basis,
    ‖u‖ • B, fun i j=>(hB i j).smul u,?_⟩
  have he := weighted_by h ‖u‖; rwa [abs_of_nonneg (norm_nonneg _)] at he
lemma reverse : Tablet k η f v (fun i=> (A i).transpose) b a x := by
  obtain ⟨B,hB,h⟩:=p.shape; exact ⟨p.scale,p.pos,p.basis,B.transpose,fun i j=> hB j i,flipped h⟩
lemma merges (h : A=ᶠ[𝓝 x] B) : Tablet k η f v B a b x := by
  obtain ⟨L,hL,hk⟩:= p.shape; exact
    ⟨p.scale,p.pos,p.basis,L, fun i j=> (hL i j).shimmy (h.symm.mono fun x hx=> by dsimp only; rw [hx]), hk⟩
lemma singular i j : Brush k f v (fun z=>A z i j) x := by
  obtain ⟨B,hB,hp⟩:=p.shape; exact (hB ..).climb ((le_abs_self _).trans (only_price hp.1 p.scale i j)) le_rfl

lemma entry i j : Brush k (f / wt η (a i) (b j)) v (fun z=>A z i j) x := by
  obtain ⟨B,hB,hp⟩:=p.shape
  refine (hB ..).climb ((le_abs_self _).trans ?_) le_rfl
  rw [le_div_iff₀ (wt_pos ..),mul_comm]; exact Control.trace0 hp.1 i j

lemma rests {B : E→ Matrix ι κ ℝ} (h : ∀ i j, Brush k 0 v (fun y=>B y i j) x) : Tablet k η f v (A+B) a b x := by
  have hv : Tablet k η 0 v B a b x := ⟨p.scale,p.pos,le_rfl,0,h,⟨fun i=>by simp, fun i=>by simp⟩⟩
  simpa only [add_zero] using! p.joined hv

omit p
lemma fixed (M : Matrix ι κ ℝ) (h : Price a b M η f) (hp : 0≤η) (hv : 0≤f) (ho : 0≤v) :
    Tablet k η f v (fun _=> M) a b x := by
  let B : Matrix ι κ ℝ := Matrix.of (fun i j=> |M i j|)
  refine ⟨hp,ho,hv,B,(fun _ _ => certified ho _),fun i=> by simpa only [B,Matrix.of_apply,abs_abs] using! h.1 i,
    fun j => by simpa only [B,transpose_apply,Matrix.of_apply,abs_abs] using! h.2 j⟩

variable {D : E→ Matrix ι ι ℝ} [DecidableEq ι]

lemma tall (h : Tablet k η f v D a a x) (j : ℕ) : Tablet k η (f^j) (j*v) (D^j) a a x := by
  induction j with
  | zero => rw [pow_zero,pow_zero, Nat.cast_zero,zero_mul]; exact fixed (1:Matrix ..) (one_pay ..) h.scale zero_le_one le_rfl
  | succ j ih => rw [pow_succ,pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; exact ih.enjoin h

omit [DecidableEq ι] in
lemma trim_left {κ ν : Type} [Fintype κ] [Fintype ν] (h : Tablet k η f v D a a x) (K : κ ↪ ι) (X : ν ↪ ι) :
    Tablet k η f v (fun u => (D u).submatrix K X) (a ∘ K) (a ∘ X) x := by
  obtain ⟨A,hA,hp⟩:= h.shape
  exact ⟨h.scale,h.pos,h.basis,A.submatrix K X,fun i j=> hA (K i) (X j),hp.1.restrict K X,hp.2.restrict X K⟩
end Tablet
end YM.ConnectedActivityE6.Blaze
