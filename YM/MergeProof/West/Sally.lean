import YM.MergeProof.West.Compass
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Comparison
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}(hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy)
open Extraction.Gaps Extraction.Spin
variable {p k N m:ℕ}
def slide (S:Schedule)(m:ℕ)(x:Points n):Prop:=∀ i j,i≠j→4*S.a m< ‖x j-x i‖
lemma slide_open (S:Schedule)(m n:ℕ):IsOpen {x:Points n|slide S m x}:=by
   let I:Type:= {i: Fin n × Fin n//i.1≠i.2}; let U (i:I):Set (Points n):={x|4*S.a m<‖x i.val.2-x i.val.1‖}
   have hz : {x:Points n|slide S m x}=⋂ i,U i:= Set.ext fun x=> ⟨fun (h:slide S m x)=>mem_iInter.mpr fun i=>h _ _ i.property,fun h (i j:Fin n) hi=> mem_iInter.mp h (⟨(i,j),hi⟩:I)⟩
   rw [hz]; exact isOpen_iInter_of_finite fun i=>isOpen_lt continuous_const (by fun_prop)
lemma slide_conf (X:Schedule)(x:Points n)(h:slide X m x):x∈conf n:= by
    intro i j hi;by_contra hh; have he:= h i j hh; rw [← hi, sub_self,norm_zero] at he;nlinarith [X.a_pos m]
lemma fur (t:ℕ)(i:ℕ)(S:Schedule):(t+1:ℝ)*S.a (i+t) ≤ S.a i:=by
   induction t with
   | zero=>simp
   | succ t ih =>
      have hh:=S.embeds_scale (S.oneStep (i+t) 0); have ht:(3:ℝ)≤ (S.block (i+t)).val:=by exact_mod_cast S.block_large (i+t)
      have hx:3*S.a (i+t+1)≤S.a (i+t):= (mul_le_mul_of_nonneg_right ht (S.a_pos _).le).trans_eq ((mul_comm ..).trans hh)
      refine le_trans ?_ ih; push_cast; rw [← add_assoc]; nlinarith [Nat.cast_nonneg (α:=ℝ) t, S.a_pos (i+t+1)]
lemma above_coord (r:ℝ)(x:E4)(h: 4*r< ‖x‖):∃ i:Axis,r< |x i|:=by
    let W:=EuclideanSpace.basisFun Axis ℝ
    have hw: ∑ i:Axis,x i • W i=x:=W.sum_repr x
    by_contra! hh; apply h.not_ge
    calc ‖x‖ ≤ ∑ i:Axis,‖x i • W i‖ := (le_of_eq (congrArg norm hw.symm)).trans (norm_sum_le ..)
         _ ≤ ∑ _:Axis,r:=Finset.sum_le_sum fun i _=> (show ‖x i • W i‖ ≤ r from by rw [norm_smul,W.norm_eq_one,mul_one]; exact hh i)
         _ = _:=by simp [Axis]
include hC hq ho H
def honor (S:Schedule) (u:Fin n→C.book.Token)(k:ℕ):=∏ i:Fin n, Real.exp ((((u i).1:ℝ)+2)*S.scale k)
-- use C.book linear tags
lemma maine {q:Fin n→S.Tag} (l:ℕ) (hw:(n:ℝ)*6<(l:ℝ)) :∀ᶠ m in atTop, ∀ x, slide C.S m x→ ‖disc q x‖ ≤ honor C.S (expose ∘ q) (m+l):=by
    let w : Fin n→ C.book.Token := expose ∘ q
    filter_upwards [(tendsto_add_atTop_nat l).eventually (spectra (v:=w) hq)] with m hm x hs
    apply le_of_tendsto_of_frequently (x:=𝓝 x) ((cont_disc H q (slide_conf C.S x hs)).continuousAt.norm)
    refine (((meets_grid C x).and_eventually (show ∀ᶠ y in 𝓝 x,slide C.S m y from (slide_open C.S m n).mem_nhds hs)).mono ?_)
    rintro y ⟨⟨hy,j,a,rfl⟩,hh⟩
    let y:=Extraction.Order.grid C j a; let I:= {i:Fin n×Fin n//i.1≠i.2}; let d:= m+l
    have ht : Tendsto (fun i:ℕ×ℕ=> C.numeric i.1 i.2 w (Cells.location C.S j i.1 i.2 ∘ a)) F.fuse (𝓝 (disc q y)) := by
       have ht:= Extraction.Order.along (Cells.eventual_grid (k:=j) C F S ho a hy w)
       exact ht
    change ‖disc q _‖ ≤ _; apply le_of_tendsto ht.norm
    have he (i:I): ∃ b:Axis, C.S.a m < |distances y i.val.1 i.val.2 b|:=by
        have hp := above_coord (C.S.a m) (y i.val.2-y i.val.1) (hh i.val.1 i.val.2 i.property); exact hp
    choose b hb using he
    obtain ⟨r,hr,hQ⟩:= ((show ∀ᶠ r in 𝓝[>] (C.S.a m),C.S.a m < r from self_mem_nhdsWithin).and (eventually_all.mpr fun i:I=> (show ∀ᶠ r in 𝓝[>] (C.S.a m), r ≤ |distances y i.val.1 i.val.2 (b i)| from mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (hb i))))).exists -- fix
    have hp : ∀ᶠ i:ℕ×ℕ in F.fuse, ∀ x∈({y}:Set _), someFine C.S i.2 r x := by
       rw [Extraction.Order.fused,Extraction.Order.late]
       filter_upwards [F.per.cofinal.eventually (expand_equivalent C.S (isCompact_singleton (x:=y)))] with p hp
       apply Eventually.of_forall; intro N x hx k l hk
       obtain rfl : x=y:= hx; let u:I:=⟨(k,l),hk⟩
       exact ⟨b u,fun t=>(hQ u).trans (hp _ (mem_singleton _) k l (b u) t)⟩
    filter_upwards [hp,large_mesh F j,hm] with i hi hj h'
    let a':=pushSite C.S hj ∘ a
    have hP (t:Fin n): wrap (C.side i.1 i.2) (a' t)= Cells.location C.S j i.1 i.2 (a t):=by
        rw [Cells.location,dif_pos hj,Ratio.embed_wrap]; rfl
    have hz:tag (C.S.a i.1) a'=y:=by
       ext1 t; exact finer ..
    change ‖C.numeric _ _ w _‖ ≤ _; rw [show (Cells.location C.S j i.1 i.2 ∘ a)=(wrap _ ∘ a') from (funext hP).symm]
    refine contour hC w {y} r hi _ hr (Nat.le_add_right m l) ?_ h' a' hz
    have ht := mul_lt_mul_of_pos_right hw (C.S.a_pos (m+l))
    linarith [fur l m C.S,C.S.a_pos (m+l)]
end YM.MergeProof.Ribbons
