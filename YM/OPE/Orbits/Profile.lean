import YM.OPE.Orbits.Continuity

/-! Tested OPE as honest tested-kernel integrals over all separated compact
joint geometries, including probability mixtures. Positive underlying measures
with arbitrary complex densities of bounded mass (hence need no density wrt
Lebesgue nor disjoint supports for each child point). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set MeasureTheory Filter Table Extraction TopologicalSpace
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book} (U:Spec.Final C F S)
    (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (h:Services C F S){I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ} (v:Labels S d)(w:Labels S e)
variable {M η δ ε:ℝ}(hM:0≤ M)(hη:0<η)(hδ:0<δ) (hε:0< ε)

def FitsOn (I J:Type) [Fintype I][Fintype J] (M η δ r:ℝ) := {z:Loc I J|WithinRoom r M η z.1 z.2.1 ∧ ClearOf z.2.1 z.2.2 δ}
def costRaw (d:I→ℕ)(ε r:ℝ):=r^(-weight d-ε)
def costRemainder (D:ℕ)(d:I→ℕ)(ε r:ℝ):=r^((D:ℝ)+1-weight d-ε)
include hM hη hδ hε h
lemma raw_price :∀ᶠ r:ℝ in 𝓝[>]0,∀ z∈FitsOn I J M η δ r,∀ i:Viewers U, ‖whole (spectator U i) z.1 v z.2.2 w‖ ≤ costRaw d ε r :=by
    let P:=fun r (z:Loc I J)=> z∈FitsOn _ _ M η δ r; let Q r (z:Loc I J) := ∀ i:Viewers U, ‖whole (spectator U i) z.1 v z.2.2 w‖ ≤ costRaw d ε r
    apply refine_geometry (P:=P) (Q:=Q); rintro f ψ hψ ht he; let x(r:ℝ):= (f r).1; let o r:=(f r).2.1; let y r:= (f r).2.2
    have he':∀ᶠ i in ψ,ClearOf (o i) (y i) δ:=he.mono fun i hi=>hi.2
    have hx:∀ᶠ i:ℝ in ψ,WithinRoom (id i) M η (x i) (o i):=he.mono fun i hi=>hi.1
    obtain ⟨hx',he⟩ := room_regime (r:=id) (φ:=ψ) (by exact tendsto_id.mono_left ht) hM hη hx
    -- time control
    have hT:= run_towards (r:=id) (tendsto_id.mono_left ht)
    have hy:∀ᶠ i:ℝ in ψ,ClearOf (o i) (y i) δ:= he'
    obtain ⟨hc,hp⟩:=free_clear hT hδ hy
    have h(i:ℝ→Viewers U) : RateLE ψ run (fun r=> whole (spectator U (i r)) (x r) v (y r) w) (weight d):=by
       rw [weighting v]; change RateLE _ _ _ _; simp_rw [whole_observed]; simpa only [mul_one,mul_zero,add_zero,id_eq] using (viewer_alt U h.schedule (names v) (names w) hT i he hc (shrinking hT zero_lt_one hx' hp) (le_refl 0) zero_le_one)
    exact ⟨ψ,hψ,le_rfl, universalize (fun i:ℝ→Viewers U => ((loglife (r:=id) (φ:=ψ) (tendsto_id.mono_left ht)).rpow (-weight d-ε)).outweigh (h i) (by linarith only [hε]) hT)⟩
lemma profile_scope (D:ℕ): ∀ᶠ r:ℝ in 𝓝[>]0,0 ≤ r ∧ ∀ z∈FitsOn I J M η δ r,z∈ guardZone U R D ∧ ∀ i:Viewers U, ‖whole (spectator U i) z.1 v z.2.2 w‖ ≤ costRaw d ε r ∧ ‖formula U R z.1 z.2.1 v z.2.2 w D i‖≤costRemainder D d ε r:=by
    filter_upwards [raw_price U h v w hM hη hδ hε,admissible_separated U R (I:=I) hM hη D,quantitative_separated U R h v w hM hη hε D hδ,(self_mem_nhdsWithin : ∀ᶠ r:ℝ in (𝓝[>]0),0<r)] with r h' hv hl hr
    exact ⟨hr.le,fun z hz=> by
      obtain ⟨hi,hj,_,hg⟩:=hl _ _ _ hz.1 hz.2
      exact ⟨⟨hv _ _ hz.1,hi,hj⟩,fun i=>⟨h' z hz i,hg i⟩⟩⟩
omit hM hη hδ hε h
private lemma raw_meas (D:ℕ)(i:Viewers U): Measurable ((guardZone U R D).indicator (fun t:Loc I J=>whole (spectator U i) t.1 v t.2.2 w)) :=
    ContinuousOn.measurable_piecewise (f:=fun t:Loc I J=>whole _ t.1 v t.2.2 w) (fun z hz=> (Orbits.whole_cont_at _ _ _ (spectate U _) hz.2.1).continuousWithinAt) continuousOn_const (guard_open U R D|>.measurableSet)
private lemma raw_meas_mixed (D:ℕ): Measurable (fun z:Loc I J × U.α.space.X => (guardZone (I:=I) (J:=J) U R D).indicator (fun t:Loc I J=>whole (U.α.ensemble z.2) t.1 v t.2.2 w) z.1):=by
    letI : Nonempty U.α.space.X:= ⟨U.α.atPoint⟩
    refine measurable_mixed (f:=fun i z=> (guardZone U R D).indicator (fun t:Loc I J=>whole (U.α.ensemble i) t.1 v t.2.2 w) z) (fun z=> ?_) (fun i=> raw_meas U R v w D (some i))
    by_cases hx:z∈guardZone U R D
    · simp only [indicator_of_mem hx]; exact (U.phase.phase.decomposition.weak (viewing U (beside z.1 z.2.2) (beside (names v) (names w)))).congr (fun i=>(character_sees U i _ _ hx.2.1).trans ((whole_observed ..).symm))
    simp only [indicator_of_notMem hx]; exact continuous_const

variable {K:Type}[MeasurableSpace K]

def uponDiscount (U:Spec.Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (D:ℕ) (v:Labels S d)(w:Labels S e) (z:Loc I J)(i:Viewers U) := Orbits.trunc (spectator U i) U R D z.1 z.2.1 v z.2.2 w

def JointEstimate (U:Spec.Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(m:ℕ)(v:Labels S d)(w:Labels S e)(bound:ℝ)(μ:Measure K)(f:K→ℂ)(p:K→Loc I J) (i:K→Viewers U) :=
       let raw:= fun α:K=>f α * whole (spectator U (i α)) (p α).1 v (p α).2.2 w
       let cut:= fun α:K=>f α * uponDiscount U R m v w (p α) (i α)
       let delta:=fun α:K=> f α * formula U R (p α).1 (p α).2.1 v (p α).2.2 w m (i α)
       Integrable raw μ ∧ Integrable cut μ ∧ Integrable delta μ ∧ (∫ α,raw α ∂μ)-(∫ α,cut α ∂μ) = ∫ α,delta α ∂μ ∧ ‖∫ α,delta α ∂μ‖ ≤ bound

lemma price_measurable {A B:ℝ}{Y:Type}[MeasurableSpace Y] (z:K→Loc I J) (phase:K→Y) (g:Y→Viewers U) (D:ℕ)
    {μ:Measure K}{f:K→ℂ}{c:ℝ}
    (p:Measurable (fun x:Loc I J × Y=> (guardZone U R D).indicator (fun t=> formula U R t.1 t.2.1 v t.2.2 w D (g x.2)) x.1)) (p':Measurable (fun x:Loc I J × Y=> (guardZone U R D).indicator (fun t=> whole (spectator U (g x.2)) t.1 v t.2.2 w) x.1)) (mz:AEMeasurable z μ)(mP:AEMeasurable phase μ)(hf:Integrable f μ) (hf':∫ α, ‖f α‖ ∂μ ≤ B) (he:∀ᵐ α:K ∂μ,f α≠0→ z α∈ guardZone U R D)
    (hx:∀ᵐ α:K ∂μ,f α≠0→ ‖formula U R (z α).1 (z α).2.1 v (z α).2.2 w D (g (phase α))‖ ≤ c)
    (hx': ∀ᵐ α:K ∂μ,f α≠0→ ‖whole (spectator U (g (phase α))) (z α).1 v (z α).2.2 w‖ ≤ A)
    (hc:0≤c):JointEstimate U R D v w (B*c) μ f z (g ∘ phase):=by
    -- generic c may be negative if no support; hc from price
    let s:=guardZone (I:=I) (J:=J) U R D; let d:=fun (x:Y) (y:Loc I J)=>formula U R y.1 y.2.1 v y.2.2 w D (g x); let d':=fun (x:Y) (y:Loc I J)=>whole (spectator U (g x)) y.1 v y.2.2 w
    have hbody(u:Y→ (Loc I J)→ℂ)(c:ℝ)(h:Measurable (fun x:Loc I J × Y=> s.indicator (u x.2) x.1))(hh:∀ᵐ α ∂μ,f α≠0→ ‖u (phase α) (z α)‖≤c): Integrable (fun α=>f α*u (phase α) (z α)) μ:=by
        have hm:= hf.1.mul ((h.comp_aemeasurable (mz.prodMk mP)).aestronglyMeasurable)
        refine (hf.norm.mul_const c).mono' (hm.congr (he.mono (fun a ha=> ?_))) ((hh).mono fun a ha=>?_)
        · by_cases h0:f a=0
          · change f a * _ = f a * _; rw [h0,zero_mul,zero_mul]
          apply congr_arg (f a * ·) (s.indicator_of_mem (ha h0) _)
        by_cases h0:f a=0
        · simp [h0]
        exact (norm_mul_le .. |>.trans (mul_le_mul_of_nonneg_left (ha h0) (norm_nonneg _)))
    have hraw:=hbody d' A p' hx'; have hdelta:=hbody d c p hx; unfold JointEstimate; dsimp only
    have hz:(fun a=> f a*uponDiscount U R D v w (z a) ((g ∘ phase) a)) = fun a=> f a*d' (phase a) (z a)-f a*d (phase a) (z a):=funext fun a=>by unfold d d' formula uponDiscount; rw [mul_sub,sub_sub_cancel]; rfl
    rw [hz]; refine ⟨hraw,hraw.sub hdelta,hdelta,(MeasureTheory.integral_sub hraw hdelta ▸ (sub_sub_cancel ..)),?_⟩
    refine norm_integral_le_of_norm_le (hf.norm.mul_const c) ?_ |>.trans ?_
    · filter_upwards [hx] with x h; by_cases he:f x=0
      · simp [he]
      exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (h he) (norm_nonneg _))
    rw [MeasureTheory.integral_mul_const]; exact mul_le_mul_of_nonneg_right hf' hc
end YM.OPE.Orbits

namespace YM.OPE.Orbits
open Function Set MeasureTheory Filter Table Extraction TopologicalSpace
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book} (U:Spec.Final C F S)
    (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (h:Services C F S){I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ} (v:Labels S d)(w:Labels S e)
variable {M η δ ε:ℝ}(hM:0≤ M)(hη:0<η)(hδ:0<δ) (hε:0< ε)
variable {K:Type}[MeasurableSpace K](m:ℕ)(B:ℝ)
include h hM hη hδ hε
/-- Output tail for arbitrary joint profiles with the positive comparison mass B bounding the L¹
   weight (includes characteristic functions/delta measures inside the separated apertures).
    The length threshold is independent even of the supporting measure. -/
lemma estimates_weighted : ∀ᶠ r:ℝ in 𝓝[>]0,
    ∀ (μ:Measure K)(f:K→ℂ)(p:K→Loc I J), AEMeasurable p μ→ Integrable f μ→ (∫ s, ‖f s‖ ∂μ) ≤ B→ (∀ᵐ s ∂μ,f s ≠ 0 → p s∈FitsOn I J M η δ r) →
    ((∀ χ : K→U.α.space.X,AEMeasurable χ μ→ JointEstimate U R m v w (B*costRemainder m d ε r) μ f p (some ∘ χ)) ∧
       JointEstimate U R m v w (B*costRemainder m d ε r) μ f p (fun _=>none)) :=by
       filter_upwards [profile_scope U R h v w hM hη hδ hε m] with i ⟨hi,hq⟩ μ f p hP hf hw he
       have h₁:= he.mono (q:=fun s=> f s ≠ 0→ p s∈guardZone U R m) (fun s hs h=>(hq _ (hs h)).1)
       have h₂(t:K→Viewers U):∀ᵐ s ∂μ,f s≠0→ ‖formula U R (p s).1 (p s).2.1 v (p s).2.2 w m (t s)‖ ≤ costRemainder m d ε i:= he.mono (fun s hs h=> ((hq _ (hs h)).2 _).2)
       have h₃(t:K→Viewers U):∀ᵐ s ∂μ, f s≠0→ ‖whole (spectator U (t s)) (p s).1 v (p s).2.2 w‖ ≤ costRaw d ε i:= he.mono (fun s hs h=>((hq _ (hs h)).2 _).1)
       have hh : 0 ≤ costRemainder m d ε i:= Real.rpow_nonneg hi ..
       exact ⟨fun χ hx=> price_measurable U R v w p χ some _ (mixed_meas U R v w m) (raw_meas_mixed U R v w m) hP hx hf hw h₁ (h₂ _) (h₃ _) hh,
             price_measurable U R v w p (fun _=>()) (fun _:Unit=>none) m ((indicator_meas _ _ _ _ _ none).comp measurable_fst) ((raw_meas _ _ _ _ _ none).comp measurable_fst) hP aemeasurable_const hf hw h₁ (h₂ _) (h₃ _) hh⟩

end YM.OPE.Orbits
