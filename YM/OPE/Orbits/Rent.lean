import YM.OPE.Orbits.Clearance

/-! Match discrepancy costs on separated exteriors, including moving tests
with their admitted scale prices. These use full phase/unselected laws of
`viewer U r` (`r : Option ...`, so every phase), not fresh states fitted to
polarizers. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter Extraction Table
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{S:Table C.book}{F:Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)
    {I J L:Type} [Fintype I] [Fintype J] {A:L→ℝ}{φ:Filter L}(hA:Tendsto A φ atTop) [φ.NeBot]
    {d:I→ℕ}{e:J→ℕ}{a b c:ℝ} {x:L→ I→ E4}{y:L→J→E4}{o:L→E4} (r:L→ Viewers U)

def weight (d:I→ℕ):ℝ := ∑ i:I, (d i:ℝ)
lemma weighting (u:Labels S d) : weight d=(sigma (names u):ℝ):= by unfold weight sigma; push_cast; rfl

variable (v:Labels S d) (w:Labels S e)(hx:enveloped φ A a x o) (hk:Kept φ A a x)
    (hp:Intervals φ A b (fun l=>sole (o l)) y) (hy:Kept φ A c y)(ha:0 < a)(hb:0≤b)(hba:b<a)(hc:b≤c)

private lemma admittance {f:L→ℂ}{g:L→ℂ}(hF:RateLE φ A f c) (he:f =ᶠ[φ] g) (hb:c≤a):RateLE φ A g a:=(hF.congr he).mono hb

include hx hk hp hy hba hc hA
omit [φ.NeBot] in
lemma clearance_both : (∀ᶠ l in φ, Injective (beside (sole (o l)) (y l))) ∧ (∀ᶠ l in φ,Injective (beside (x l) (y l))):= by
    have h0 :=Kept.sole φ A o c; refine ⟨(h0.chorus hy (hp.mono hc)).inject,?_⟩
    have h1:= (shrinking (x:=x) (y:=y) hA hba hx hp).mono (show b ≤ max a c from hc.trans (le_max_right ..))
    exact ((hk.mono (le_max_left ..)).chorus (hy.mono (le_max_right ..)) h1).inject

include h hb ha U R
lemma discrepancy_rate_old (m:ℕ): RateLE φ A (fun l=>discrepancy (spectator U (r l)) m (x l) (o l) v (shadowOld R.port m (x l) (o l) v) (y l) w) (weight d*a -(m+1:ℝ)*(a-b)+weight e*c):=by
    let z(l):=groundError U R.port m (x l) (names v) (o l) (y l) (names w)
    have h' : RateLE φ A (fun l=>glance U (r l) (z l)) (weight d*a- (m+1:ℝ)*(a-b)+weight e*c) :=by
        have hI:= (arrangement_cost U R.port m (names v) (names w) (O:=o) hA h R.spans hx hk ha hy hp hb hc hba).transfer (Eventually.of_forall fun i=> glance_bound U (r i) (z i))
        rw [weighting v,weighting w]; exact hI
    refine h'.congr ?_; filter_upwards [(clearance_both hA hx hk hp hy hba hc).2,(clearance_both hA hx hk hp hy hba hc).1] with i hi he; rw [discrepancy_old ..]
    · exact glance_terms _ _ _ _ _ _ _ _ _ hi he
    · exact spectate ..
    · exact spectate_respects U (r i)
    · exact spectate_ready U (r i)
    exact he

omit U R h ha hp hy hc hba hb hx hk hA [φ.NeBot]
private def discrepancy_flip {S':Table C.book}(T:Table C.book)(m:ℕ)(x:I→E4)(v:Labels S' d)(o:E4)(c:S'.Field m)(y:J→E4):MultilinearMap ℂ (fun j=>S'.Field (e j)) ℂ:= (show MultilinearMap ℂ (fun j=> S'.Field (e j)) ℂ from sectionLabels v (moment T (beside y x) (d:=Sum.elim e d))) - (show MultilinearMap ℂ (fun j=>S'.Field (e j)) ℂ from sectionLabels (fun _:Unit=>c) (moment T (beside y (sole o)) (d:=Sum.elim e (fun _:Unit=> m))))
private lemma flip_cost {S':Table C.book} (T:Table C.book)(v:Labels S' d)(w:Labels S' e)(m:ℕ)(x:I→E4)(o:E4)(y:J→E4)(c:S'.Field m)(h:T.Hierarchy)(hx:Injective (beside x y))(ho:Injective (beside (sole o) y)) : discrepancy T m x o v c y w= discrepancy_flip T m x v o c y w:=by
     unfold discrepancy_flip discrepancy; erw [MultilinearMap.sub_apply, sectionLabels_apply,sectionLabels_apply]; change _ - upon T m o y w c= whole T y w x v - whole T y w (sole o) (sole c:Labels S' (fun _:Unit=> m)); rw [whole_flip _ _ _ _ h hx, whole_flip _ _ _ _ h ho]; rfl
include hx hk hp hy hba hc hA U
lemma old_moving {m:ℕ}{ζ:L→S.Field m}{ξ:ℝ} -- undeclared m? binder
    (h:∀ w:Labels S e, RateLE φ A (fun i=>discrepancy (spectator U (r i)) m (x i) (o i) v (ζ i) (y i) w) ξ)
    (w:L→ Labels S e)(hw:∀ j:J, RateLE φ A (fun s=>w s j) 0) : RateLE φ A (fun i=>discrepancy (spectator U (r i)) m (x i) (o i) v (ζ i) (y i) (w i)) ξ:=by
    let f:= fun i=>discrepancy_flip (spectator U (r i)) m (x i) v (o i) (ζ i) (y i) (e:=e)
    obtain ⟨h₁,h₂⟩:=clearance_both hA hx hk hp hy hba hc
    have he(w:L→ Labels S e) : (fun i=>discrepancy (spectator U (r i)) m (x i) (o i) v (ζ i) (y i) (w i)) =ᶠ[φ] (fun i=>f i (w i)):=by
        filter_upwards [h₁,h₂] with i h₁ h₂; exact flip_cost _ _ _ _ _ _ _ _ (spectate U (r i)) h₂ h₁
    have hf:= contract (a:=ξ) hA f (fun v=>(h v).congr (he (fun _=>v))) w (fun _=>0) hw; simpa only [Finset.sum_const_zero,add_zero] using hf.congr (he w).symm
end YM.OPE.Orbits
