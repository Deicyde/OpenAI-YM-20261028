import YM.FullVolume.Tess.Barque
/- washes on continuous data. No global analyt assumed. Interior sufficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Tess
open Filter Function Set Metric MeasureTheory Lattice RG Ray Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp Amp.Beam
variable {S:Schedule} {n N j m p:ℕ}{K K':Set (Points n)}
local notation "A"=>S.a
namespace Scroll
lemma sealed {Y:Type}[MetricSpace Y]{F:Points n→Y}{g:ℕ→ Positions n→Y} (ht:IsCompact K)(hp:ContinuousOn F K) (h: ∀ x∈ K, ∀ (j:ℕ→ℕ)(y:ℕ→Positions n), (∀ i:ℕ,tag (S.a (j i)) (y i)∈K)→ StrictMono j→ Tendsto (fun i=>tag (S.a (j i)) (y i)) atTop (𝓝 x)→ Tendsto (fun i=>g (j i) (y i)) atTop (𝓝 (F x))):Scroll S K g F:=by
    refine ⟨hp,fun ε he=>?_⟩; by_contra! hx; obtain ⟨p,hp',hX⟩:= extraction_of_frequently_atTop hx; choose u hu H using hX
    obtain ⟨x,hx,v,hv,hV⟩:= ht.tendsto_subseq hu
    let y(n:ℕ):= tag (A (p (v n))) (u (v n)); have hy := h x hx (p∘v) (u∘v) (fun i=> hu _) (hp'.comp hv) hV
    have hG: Tendsto (fun i=>F (y i)) atTop (𝓝 (F x)):= (hp x hx|>.tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨hV,Eventually.of_forall (fun i=>hu _)⟩)
    have ht:=hy.dist hG; rw [dist_self] at ht; obtain ⟨i,hi⟩:= (ht.eventually (gt_mem_nhds he)).exists; exact not_lt.mpr (H (v i)) hi
variable {U:ℕ→ Positions n→ Beam ℂ}{G: Points n→ Beam ℂ}(hk: Scroll S K U G)
def spur (u:Reach n)(y:ℕ)(x:Positions n):= x-u.back • u.axis_+y • u.axis_
abbrev washQ (u:Reach n) (V:Positions n→Beam ℂ)(x:Positions n):= (u.e:ℝ)⁻¹ • ∑ y∈Finset.range u.e, V (spur u y x)
def waves (l:List (Reach n))(V:Positions n→ Beam ℂ):Positions n→Beam ℂ:=l.rec V (fun i _ l_=>washQ i l_)
variable {z:ℝ}
lemma spur_k (u:Reach n)(x: Positions n)(t:ℝ) : tag t (x-u.back • u.axis_)=tag t x-((u.back:ℝ)*t) • Dir u.where_:= by
      symm; exact sub_eq_iff_eq_add.mpr (by conv_lhs=> rw [← sub_add_cancel x (u.back • u.axis_)]; rw [Reach.axis_,taggedN])
lemma term_d (x:ℕ→Positions n)(v:ℕ→ℕ) (z:Points n)(hp:Tendsto v atTop atTop)(h:Tendsto (fun i=>tag (S.a (v i)) (x i)) atTop (𝓝 z))(u:Reach n)(k:ℕ): Tendsto (fun i=>tag (S.a (v i)) (spur u k (x i))) atTop (𝓝 z):=by
    unfold spur; simp_rw [Reach.axis_,taggedN]; have he:= S.shrinks.comp hp
    simp_rw [← show u.axis_=drive u.where_ from rfl, spur_k]; simpa only [mul_zero,zero_smul,sub_zero,add_zero] using! ((h.sub ((he.const_mul (u.back:ℝ)).smul_const (Dir u.where_))).add ((he.const_mul (k:ℝ)).smul_const (Dir u.where_)))
include hk
lemma voyages (ht:IsCompact K')(hv: K' ⊆ interior K)(l:List (Reach n)): Scroll S K' (fun i=> waves l (U i)) G:=by
    have hp:=hk.land.mono (hv.trans interior_subset)
    induction l generalizing K' with
    | nil=> exact hk.restrict (hv.trans interior_subset)
    | cons i l ih=>
       obtain ⟨X,hK,hY,hP⟩:= exists_compact_between ht isOpen_interior hv -- order
       refine sealed ht hp (fun x hx a g h ha he=>?_)
       let P i:=∑ j∈Finset.range i,G x
       have ht0 := ih hK hP (hk.land.mono (hP.trans interior_subset))
       let t i:=A (a i); let f n k:= waves l (U (a n)) (spur i k (g n))
       have hG(k): Tendsto (fun n=> f n k) atTop (𝓝 (G x)):= ht0.inure ha.tendsto_atTop (hY hx) (term_d g a x ha.tendsto_atTop he i k)
       have h(q:ℕ): Tendsto (fun n=> ∑ j∈Finset.range q,f n j) atTop (𝓝 (P q)):= tendsto_finsetSum _ (fun j _=>hG j)
       have hb := i.paid; have hx:= ne_of_gt (show 0<(i.e:ℝ) from (by exact_mod_cast hb)); let c:=i.e
       have hw : (i.e:ℝ)⁻¹ • P c=G x:=by unfold P; simp only [Finset.sum_const,Finset.card_range]; rw [← Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ hx]
       exact hw ▸ ((h c).const_smul ((i.e:ℝ)⁻¹)) -- motive
omit hk
lemma charged (u:Reach n)(x y:Positions n){t:ℝ}(ht:0<t)(k:ℕ) : dist (tag t (spur u k x)) (tag t x) ≤ (u.back+k:ℕ)*t:=by
   let v:= x-u.back • u.axis_; apply le_trans (dist_triangle _ (tag t v) _); unfold spur; rw [paidDist _ _ ht u.where_, dist_comm (tag t v)]; have he:dist (tag t x) (tag t v)=(u.back:ℝ)*t:=by
       nth_rw 1 [← sub_add_cancel x (u.back • u.axis_)]; exact paidDist _ _ ht ..
   rw [he,Nat.cast_add]; linarith
lemma readsWave {f:sun→ℕ→ Positions n→ℂ}(ht:IsCompact K')(hv: K'⊆ interior K)(l:List (Reach n))(hU :∀ᶠ i:ℕ in atTop,∀ x:Positions n,tag (S.a i) x∈K → ∀ s:sun,f s i x= read ℂ s (U i x)) :∀ᶠ i:ℕ in atTop,∀ x:Positions n,tag (A i) x∈K'→∀ s:sun, tides l (f s i) x=read ℂ s (waves l (U i) x):=by
    induction l generalizing K' with
    | nil=> filter_upwards [hU] with i h p hp s; exact h _ (interior_subset (hv hp)) s
    | cons i l ih=>
       obtain ⟨v,hv,hV⟩:=ht.exists_cthickening_subset_open isOpen_interior hv; let K':=K'
       have he:Tendsto (fun N=>(↑(i.back+i.e):ℝ)*A N) atTop (𝓝 0):=by simpa only [mul_zero] using! (S.shrinks.const_mul ((i.back+i.e:ℕ):ℝ))
       filter_upwards [ih ht.cthickening hV,he.eventually (ge_mem_nhds hv)] with N h hg x hx s
       change Reach.wash i (tides l _) _=read ℂ s (washQ _ _ _)
       unfold washQ Reach.wash; rw [blur_at,map_smul,map_sum]; rw [Complex.real_smul]; simp only [Complex.ofReal_inv,Complex.ofReal_natCast]; congr 1
       exact Finset.sum_congr rfl (fun k hk=>h _ (mem_cthickening_of_dist_le _ _ _ _ hx ((charged i x x (S.a_pos _) k).trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.add_le_add_left (Finset.mem_range.mp hk|>.le) _)) ((S.a_pos _).le)).trans hg))) s)
end Scroll
end YM.FullVolume.Tess
#print axioms YM.FullVolume.Tess.Scroll.voyages
#print axioms YM.FullVolume.Tess.Scroll.readsWave
