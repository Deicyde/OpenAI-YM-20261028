import YM.UVExtension.Poppy.Axels
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter Metric Lattice Extraction Fallow
open scoped Topology BigOperators ContDiff Classical
variable {S:Schedule}{n m k N:ℕ}{x y u: Tabletop n}
variable {F:ℕ→ Tabletop n→ℂ}{A:Set (Points n)}{f g:Points n→ℂ}(i:Axel n)
    (h:IsOpen A)(hp: Meets A (Ink S F) f) (hh: Extraction.oscillation A (Ink S (fun n=> climbing (S.a n) (F n) i)))
local notation "Y"=> fun j=>climbing (S.a j) (F j) i
set_option quotPrecheck false
local notation "dir"=> Points.direction i.1 i.2
-- uniform cauchy limit. ax is demanded for this direction
include hp hh h
lemma points1 (x:Points n)(hx:x∈A): CauchySeq fun j=> Ink S Y j x:=by
   rw [Metric.cauchySeq_iff]; intro ε he; obtain ⟨δ,hδ,H⟩:= slopeEstimate h hp i hx hh (ε/3) (by positivity)
   obtain ⟨K,hK,hS⟩:= H δ hδ.ne' (abs_of_pos hδ|>.le)
   obtain ⟨T,hT⟩:= Metric.cauchySeq_iff.mp hK.cauchySeq (ε/3) (by positivity); obtain ⟨U,hU⟩:= eventually_atTop.mp hS
   let z n := Ink S Y n x; have he(n)(h: U ≤ n) : dist (K n) (z n) ≤ ε/3:=by rw [dist_eq_norm]; exact hU _ h
   refine ⟨max T U,fun n hn m hm=>?_⟩
   refine lt_of_le_of_lt (dist_triangle4 (z n) (K n) (K m) (z m)) ?_; rw [dist_comm (z n)]; linarith only [he n (by omega),he m (by omega),hT n (by omega) m (by omega)]

-- derivatives read as actual iterated coordinate-wise classical derivative.
lemma slopes (g:Points n→ℂ) (ht:Meets A (Ink S Y) g)(x:Points n)(hx:x∈ A): HasDerivAt (fun t:ℝ=>f (x+t • dir)) (g x) 0:=by
   rw [hasDerivAt_iff_tendsto_slope]
   apply Metric.tendsto_nhds.mpr; intro ε he
   obtain ⟨δ,hδ,hp⟩:= slopeEstimate h hp i hx hh _ (half_pos he)
   -- neighborhood punct
   rw [eventually_nhdsWithin_iff]; filter_upwards [ball_mem_nhds (0:ℝ) hδ] with t ht' ht''
   obtain ⟨f',hF,hQ⟩:=hp t ht'' ((mem_ball_zero_iff.mp ht').le)
   have hz : Tendsto (fun j=> Ink S Y j x) atTop (𝓝 (g x)):= Metric.tendsto_nhds.mpr fun ε hε=> (ht.uniform {x} (singleton_subset_iff.mpr hx) isCompact_singleton ε hε).mono fun j hj=> hj _ rfl -- mem singleton
   have hh:= le_of_tendsto (hF.dist hz) (hQ.mono fun i hi=> (show dist (f' i) _≤ ε/2 from by rw [dist_eq_norm]; exact hi))
   simpa [slope_def_module, Complex.real_smul] using lt_of_le_of_lt hh (half_lt_self he)

-- fix g via deriv_ value. At all points (not asserting off patch)
def derivative (i:Axel n)(f : Points n→ℂ)(x : Points n):= deriv (fun t:ℝ=> f (x+t • Points.direction i.1 i.2)) 0
lemma folio : Meets A (Ink S Y) (Poppy.derivative i f) ∧ ∀ x∈A,HasDerivAt (fun t:ℝ=> f (x+t • dir)) (Poppy.derivative i f x) 0:=by
   obtain ⟨V,hV⟩:= growFrom h hh Set.univ dense_univ (fun x hx=> points1 i h hp hh x hx.2)
   have hx (x:Points n)(hx:x∈A) : V x=Poppy.derivative i f x:= ((slopes i h hp hh V hV x hx).deriv).symm
   refine ⟨⟨(hV.continuousOn.congr (fun _ hp=> (hx _ hp).symm)),fun K hk he ε hi=>(hV.uniform K hk he ε hi).mono (fun i h x hx'=>by rw [← hx x (hk hx')]; exact h x hx')⟩, fun x he=>?_⟩; rw [←hx x he]; exact slopes i h hp hh V hV _ he

def ivy (f:Points n→ℂ): List (Axel n)→ Points n→ℂ
    | []=> f
    | a::as => Poppy.derivative a (ivy f as)

structure Shelf (S:Schedule)(K:Set (Points n))(F:ℕ→Tabletop n→ℂ)(k:ℕ): Prop where
   fees (i:List (Axel n)) : i.length≤k→ ∀ M⊆K, IsCompact M →∃ b:ℝ,0≤b∧∀ᶠ N in atTop,∀ x:Tabletop n,tag (S.a N) x ∈ M → ‖rake (S.a N) (F N) i x‖≤ b

omit hp hh
include h
lemma sunny (H:Shelf S A F (k+1))(i:List (Axel n))(hi:i.length≤k): Extraction.oscillation A (Ink S fun j=>rake (S.a j) (F j) i):=by
    apply Poppy.tending S (fun j=> rake (S.a j) (F j) i) h; intro K hK hp; choose b hb hT using fun j: Axel n=> H.fees (j::i) (by simp [hi]) K hK hp
    let X:= ∑ i,b i; refine ⟨X,sum_nonneg (fun i _=> hb i),?_⟩; exact (eventually_all.mpr hT).mono fun n hn a x hx=> (hn a x hx).trans (Finset.single_le_sum (fun i _=>hb i) (mem_univ _))
include hp
lemma seasoning (H:Shelf S A F (k+1))(i:List (Axel n))(hi:i.length≤k): Meets A (Ink S fun j=>rake (S.a j) (F j) i) (ivy f i):=by
   induction i with
   | nil=> exact hp
   | cons a i IH=>
     have he:= folio a h (IH (by simp at hi; omega)) (F:=fun j=>rake (S.a j) (F j) i) (sunny h H (a::i) hi); exact he.1

lemma actually (H:Shelf S A F (k+1))(j:List (Axel n))(hi:j.length<k): ∀ x∈A, HasDerivAt (fun t:ℝ=> (ivy f j) (x+t • dir)) (ivy f (i::j) x) 0:=by
    exact (folio i h (F:=fun n=> rake (S.a n) (F n) j) (seasoning h hp H j hi.le) (sunny h H (i::j) hi)).2
end YM.UVExtension.Poppy
