import YM.MultipleContact.Matching.Estimates
import YM.Work.A15

/-! Discrete seam avoidance by the actual orthogonal covariance, not presumed for cutoff data. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Local
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Acme Ribbons Around Cells Wilson Lattice Climb Set Matrix
open Matching
open scoped Topology Matrix Matrix.Norms.Frobenius BigOperators Classical
open YM.Next.UVStress
attribute [local instance] YM.Work.A15.compact_ortho
set_option linter.unusedSimpArgs false
private def swing (j k:Axis)(t:ℝ):M4:=fun a b=>if b=j then (if a=j then Real.cos t else if a=k then Real.sin t else 0) else if b=k then (if a=k then Real.cos t else if a=j then -Real.sin t else 0) else if a=b then 1 else 0
variable {j k N:Axis} (h:j≠k)
include h
private lemma first (b:Axis)(t:ℝ) : swing j k t b j=(if b=j then Real.cos t else 0)+(if b=k then Real.sin t else 0):=by
   unfold swing; by_cases he:b=j <;> simp [he,h]
   
private lemma second (b:Axis)(t:ℝ) : swing j k t b k=(if b=k then Real.cos t else 0)+(if b=j then -Real.sin t else 0):=by
   unfold swing; by_cases he:b=k <;> simp [he,Ne.symm h]
private lemma twirls (t:ℝ):star (swing j k t)*swing j k t=1 :=by
    ext i n; simp only [mul_apply,star_eq_conjTranspose,conjTranspose_apply,star_trivial,one_apply]
    have h':k≠j:= Ne.symm h
    by_cases h1:i=j
    · subst i
      simp only [first h,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte]
      simp only [swing]
      split_ifs <;> (try subst n) <;> try (linarith only [Real.cos_sq_add_sin_sq t])
      all_goals contradiction
    by_cases h2:i=k
    · subst i; simp only [second h,add_mul,Finset.sum_add_distrib,ite_mul, zero_mul, Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte]
      simp only [swing]
      split_ifs <;> (try subst n) <;> try (linarith only [Real.cos_sq_add_sin_sq t])
      all_goals contradiction
    simp only [swing,h1,h2, ↓reduceIte, ite_mul,zero_mul, Finset.sum_ite_eq',Finset.mem_univ, one_mul]
    split_ifs <;> aesop
variable (x:E4)(a:ℝ)
include h
lemma noSphere (ha:a≠0): Dense ({R:Ortho| a≠Ortho.move R x j}) :=by
    rw [dense_iff_inter_open]
    rintro U hU ⟨R,hR⟩
    let f(t:ℝ):Ortho:=⟨swing j k t,Matrix.mem_unitaryGroup_iff'.2 (twirls h t)⟩
    have hf:f 0=1:=by
      apply Subtype.ext
      change swing j k 0=(1:M4)
      ext i l; unfold swing; rw [one_apply,Real.cos_zero,Real.sin_zero]; split_ifs <;> subst_vars <;> first| contradiction|rfl|simp
    have ht: Continuous f:=Continuous.subtype_mk (continuous_pi fun i=> continuous_pi fun l=>(by
         change Continuous (fun t=>if l=j then (if i=j then Real.cos t else if i=k then Real.sin t else 0) else if l=k then (if i=k then Real.cos t else if i=j then -Real.sin t else 0) else if i=l then 1 else 0); split_ifs <;> fun_prop)) _
    obtain ⟨δ,hδ,hg⟩:=Metric.mem_nhds_iff.mp (show ∀ᶠ t in 𝓝 (0:ℝ), f t * R∈U from (ht.mul continuous_const).continuousAt.eventually (hU.mem_nhds (by simpa only [Pi.mul_apply,hf,one_mul] using hR)))
    let t:=min (δ/2) 1; have ht0:0<t:= lt_min (half_pos hδ) zero_lt_one
    have htδ:t < δ:=(min_le_left ..).trans_lt (half_lt_self hδ)
    have hu(t) : Ortho.move (f t) (Ortho.move R x) j=Real.cos t*(Ortho.move R x j)-Real.sin t* (Ortho.move R x k) :=by
       let y:=Ortho.move R x
       have h':k≠j:=Ne.symm h
       unfold Ortho.move; rw [M4.at_coord]
       change ∑ i, swing j k t j i*_ = _
       have hv(i): swing j k t j i = (if i=j then Real.cos t else 0) + if i=k then -Real.sin t else 0 := by
           unfold swing; by_cases he:i=j
           · simp [he,h]
           simp only [he,Ne.symm he,h',h,if_true,if_false,zero_add]
       simp only [hv, add_mul, Finset.sum_add_distrib, ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true, neg_mul]
       rfl
    classical
    by_contra hC
    rw [Set.not_nonempty_iff_eq_empty] at hC
    have hh(t:ℝ)(ht:|t|<δ): a=Ortho.move (f t*R) x j:=not_ne_iff.mp (fun hh=> Set.Nonempty.ne_empty (s:=U ∩ {R:Ortho|a ≠ Ortho.move R x j}) ⟨_,hg (Metric.mem_ball.mpr (by rwa [dist_zero_right,Real.norm_eq_abs])),hh⟩ hC) -- fix h'
    have h0:=hh 0 (by rw [abs_zero];exact hδ)
    rw [hf,one_mul] at h0
    have hq:Real.cos t≠1:=fun h=> (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three,min_le_right (δ/2) (1:ℝ)])).1 h |>.symm.not_lt ht0
    have h'₁:=hh t (by rw [abs_of_pos ht0];exact htδ); have h'₂:=hh (-t) (by rw [abs_neg, abs_of_pos ht0];exact htδ)
    rw [Ortho.move_mul,hu] at h'₁ h'₂; rw [Real.cos_neg,Real.sin_neg] at h'₂
    apply ha; rw [h0]
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero.mpr hq) (by nlinarith only [h0,h'₁,h'₂])
-- now all cells (only need one p, all exterior coords per pack). 
omit h
variable {ι:Type*}[Finite ι]{n:ι→ℕ}
open scoped NNReal
lemma safe_rotation {G:Gauge}(x:∀i,Points (n i))(C:Family G)(p:ℕ):∃ (R:Ortho) (ℓ:∀i,Fin (n i)→ Cover),∀ i,Locations C p 0 (ℓ i) (Points.move R (x i)):=by
    let v:=C.S.a p
    letI:= Fintype.ofFinite ι
    have hv:= C.S.a_pos p
    have ht : v≠0:=hv.ne'
    let f(i:ι) (j:Fin (n i)) (k:Axis) (m:ℤ):Set Ortho:={R:Ortho|v*(m+1/2:ℝ)≠ (Ortho.move R (x i j) k)}
    have hMove (v:E4)(k:Axis):Continuous (fun R:Ortho=> Ortho.move R v k):=by
       unfold Ortho.move; simp_rw [M4.at_coord]; apply continuous_finsetSum _ (fun j _=>(by
          apply Continuous.mul _ continuous_const
          let a:Ortho→Axis→Axis→ℝ:=Subtype.val
          have ha:Continuous a:= continuous_subtype_val (p:=(·∈Matrix.unitaryGroup Axis ℝ))
          exact (continuous_apply (A:=fun _:Axis=>ℝ) j).comp ((continuous_apply k).comp ha)))
    have ho(i j k m):IsOpen (f i j k m):=isOpen_ne_fun continuous_const (hMove ..)
    have h'(k m) : Dense (⋂ i,⋂ (j:Fin (n i)), f i j k m):=by
        refine dense_iInter_of_isOpen (fun i=>isOpen_iInter_of_finite fun j=>ho i j k m) (fun i=> dense_iInter_of_isOpen (fun j=>ho i j k m) fun j=>?_)
        obtain ⟨l,hL⟩:=exists_ne k
        apply noSphere (Ne.symm hL) (x i j) _ (mul_ne_zero ht ?_)
        have hμ:m ≤ 0 ∨ 0 < m:= le_or_gt _ _
        by_cases hm:m=0; simp [hm]
        rcases hμ with h₁|h₂
        · have h₁:(m:ℝ)≤ -1:=by exact_mod_cast (show m≤ -1 by omega)
          linarith
        exact ne_of_gt (by have he:(0:ℝ) < m:=(by exact_mod_cast h₂); positivity)
    obtain ⟨R,hR⟩ :=(dense_iInter_of_isOpen (ι:=Axis×ℤ) (f:=fun k=> ⋂ i, ⋂ j:Fin (n i), f i j k.1 k.2) (fun b=>isOpen_iInter_of_finite fun i=>isOpen_iInter_of_finite fun j=>ho i j b.1 b.2) (fun b=>h' b.1 b.2)).nonempty -- cannot show open over m; reorder
    have hA {w:ℝ}(hw:∀m:ℤ, v*(m+1/2)≠w) : ∃a:ℤ,|w-v*a|<v/2:=by
        let q:=w/v+1/2; let a:=⌊q⌋; refine ⟨a, abs_lt.mpr (?_)⟩
        have hf := Int.floor_le q
        have hf':=Int.lt_floor_add_one q
        have he:q*v=w+1/2*v:=by dsimp [q];rw [add_mul,div_mul_cancel₀ _ ht]
        have hTop := mul_le_mul_of_nonneg_right hf hv.le
        have hBottom:=mul_lt_mul_of_pos_right hf' hv
        have hh:=hw (a-1)
        constructor; swap
        · change w-v*a < v/2; change q*v < (a+1:ℝ)*v at hBottom; nlinarith only [hBottom,he]
        change -(v/2) < w-v*a
        push_cast at hh; change (a:ℝ)*v ≤ q*v at hTop; apply lt_of_le_of_ne (by nlinarith only [hTop,he]) (fun heq=>hh (by nlinarith only [heq]))
    choose a ha using fun i j k=> hA (w:=Ortho.move R (x i j) k) fun m=> mem_iInter.mp (mem_iInter.mp ((mem_iInter.mp hR) (k,m)) i) j
    exact ⟨R,fun i j k=>a i j k,fun i j k=> by exact lt_of_lt_of_le (ha i j k) (sub_zero _|>.symm.le)⟩
end YM.MultipleContact.Local
