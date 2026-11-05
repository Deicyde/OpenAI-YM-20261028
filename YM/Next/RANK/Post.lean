import YM.Next.RANK.North

/-!
# Replacing into regular and attaching letters

Local value pass applied first, later bit carries shape. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {V : Type} [Fintype V] [DecidableEq V]
variable {N k d p i q' : ℕ} (v : C.label d) (i) (H : C.Makes) (hk : C.ref d≤k) (hN : k≤N)
variable {ζ : V→Site (C.side k p)} (s : Signed) (r : Prop) (j : V) {q : BudgetPoint}

-- Q.O partition supplies a local W on orientation 0
structure Ticket (v : C.label d) (i k N p : ℕ) (q : BudgetPoint) (X : Keepat (C.side k p))
    (B : Config G (C.side k p)→ℂ) (t : ℝ) : Prop where
  contains : HealthyCube C v i k N p X.val
  fresh : Reliable q.threshold G _ X.val B
  loss (U : Config G (C.side k p)) : Healthy q.threshold X.val U → ‖nearHol C v i k N p U-B U‖ ≤ t

variable {X : Keepat (C.side k p)} {B : Config G (C.side k p)→ℂ} {u : ℝ}
variable (h : Ticket v i k N p q X B u)

def traverse (v : V) {Z : Support (C.side k p)} (H : 0∈Z) {t : ℝ} {F : Config G (C.side k p)→ℂ} (h : Reliable t G _ Z F): SourceAt G ζ:= by
  refine fulcrum v (X:=swath s (ζ v) Z) ?_ (dot r∘ F ∘ pull s (ζ v)) (b:=t) ⟨?_,(dot_meas r).comp (h.meas.comp (continuous_pull ..|>.measurable)),?_⟩
  · simpa only [affine,Signed.act_zero,zero_add] using (stay s (ζ v) Z|>.2 H)
  · exact fun i k=> congr_arg (dot r) (p_invar s (ζ v) h.inv i k)
  exact fun U V hU=> congr_arg (dot r) (p_local s (ζ v) Z h.locally _ _ hU)

def openW := traverse (C:=C) s r j X.property (ζ:=ζ) h.fresh

-- argument transform X.

def Rshot : SourceAt G ζ:= by
  have hh:= reads_glance v H hk hN p i h.contains
  let P:= C.path.rep N p k
  let Z := nearHol C v i k N p
  refine traverse (ζ:=ζ) s r j X.property (F:=fun U=>Z U-B U) ⟨?_,hh.2.1.meas.sub h.fresh.meas,?_⟩ (C:=C) (t:=q.threshold)
  · exact fun f U=>congr_arg₂ _ (hh.2.1.inv f U) (h.fresh.inv ..)
  exact fun U V hU=> congr_arg₂ _ (hh.2.1.locally _ _ hU) (h.fresh.locally _ _ hU)

def Ember (hu : q.threshold ≤ (C.path.rep N p k).p.threshold) : Strike G ζ q.threshold:= by
  have hp := reads_glance v H hk hN p i h.contains; let P:= (C.path.rep N p k).p
  let F:=pull (K:=G.El) s (ζ j); let t:=swath s (ζ j) X.val; let x:=halo 8 t
  let R:=nearHol C v i k N p
  refine { extent:=x, active:=?_, fires:=slot j, remembers:=?_,
           value:=fun U=> dot r (glance v i k N p (F U)) -masked q.threshold t (dot r∘ R∘F) U,
           meas:=?_, inv:= ?_, sees:=?_, only:=?_ }
  · exact Finset.Nonempty.mono (halo_subset ..) ((show X.val.Nonempty from ⟨_,X.property⟩).image (affine s (ζ j)))
  · intro i H; obtain rfl : i=j:= Finset.mem_singleton.mp H; refine halo_subset _ _ ?_; simpa only [t,affine,Signed.act_zero,zero_add] using (stay s (ζ i) _|>.2 X.property)
  · exact ((dot_meas r).comp (hp.1.meas.comp (continuous_pull ..|>.measurable))).sub (masked_measurable _ _ _ ((dot_meas _).comp (hp.2.1.meas.comp (continuous_pull ..|>.measurable))))
  · intro i U; apply congr_arg₂ (·-·)
    · exact congr_arg (dot r) (p_invar s (ζ j) hp.1.inv i U)
    exact sails _ _ _ (fun i U=>congr_arg (dot r) (p_invar s (ζ j) hp.2.1.inv i U)) i U
  · intro U V H _; refine congr_arg₂ (·-·) ?_ ?_
    · apply congr_arg (dot r); exact p_local s (ζ j) _ hp.1.locally U V (by rw [swath_iffHalo]; exact H)
    exact sail _ t _ (fun a b ht=> congr_arg (dot r) (p_local s (ζ j) X.val hp.2.1.locally _ _ ht)) U V H
  intro U hh; have ht:Healthy q.threshold t U:=Disjoint.mono_left (halo_subset _ _) hh
  rw [hp.2.2 _ ((s_healthy ..).2 (threshold_fit _ _ hu _ ht)),masked_eq _ _ _ _ ht]; exact sub_self _

lemma snow (hu : q.threshold ≤ (C.path.rep N p k).p.threshold) (U : Config G (C.side k p)) :
    let t:=ζ j
    Poly.send (slot j) (dot r (glance v i k N p (pull s t U)))=(openW v i s r j h (ζ:=ζ) |>.amount q.threshold U)+ (Rshot v i H hk hN s r j h (ζ:=ζ) |>.amount q.threshold U)+ (Ember v i H hk hN s r j h hu (ζ:=ζ) |>.occ U):= by
  intro t; dsimp only [Rshot,SourceAt.amount,openW,traverse,fulcrum, Ember,Strike.occ]; rw [← send_plus,← send_plus]; apply congr_arg
  by_cases hf:Healthy q.threshold (swath s t X.val) U
  · rw [masked_eq _ _ _ _ hf,masked_eq _ _ _ _ hf,masked_eq _ _ _ _ hf,Function.comp_apply,Function.comp_apply, Function.comp_apply,Function.comp_apply,Function.comp_apply,Function.comp_apply]
    rw [← dot_add, add_comm (B _), sub_add_cancel]; abel
  rw [masked_ne _ _ _ _ hf,masked_ne _ _ _ _ hf,masked_ne _ _ _ _ hf]; simp only [add_zero,zero_add,sub_zero];rfl

lemma hW_damp (hv : q.threshold ≤ (C.path.rep N p k).p.threshold) (P : V→ℝ) (he : 0≤ P j) :
    Taxed (Ember v i H hk hN s r j h hv (ζ:=ζ)) (q:=q) P (3*(P j*moneys C d k N p v)):= by
  have hp:= money_nn C d k N p v
  refine ⟨by positivity,fun U=> ?_⟩; unfold Ember; dsimp only
  by_cases hx : Healthy q.threshold (swath s (ζ j) X.val) U
  · have hh : Healthy (C.path.rep N p k).p.threshold X.val (pull s (ζ j) U):= (s_healthy ..).2 (threshold_fit _ _ hv _ hx)
    rw [masked_eq _ _ _ _ hx, (reads_glance v H hk hN p i h.contains).2.2 _ hh]; simp only [Function.comp_apply,sub_self,norm_zero,mul_zero]; positivity
  rw [masked_ne _ _ _ _ hx,sub_zero, Poly.solo_toll,dot_norm]; linarith only [mul_le_mul_of_nonneg_left (income_ten v H hk hN i (pull s (ζ j) U)) he]

lemma Rshot_cost (P : V→ℝ) (he : 0≤P j) (hb : 0 ≤ u) : transported (Rshot v i H hk hN s r j h (ζ:=ζ)) q.threshold P (P j*u):= by
  refine (transferD ..).2 ⟨mul_nonneg he hb,fun U hU=>?_⟩; dsimp only [Rshot, fulcrum,traverse]; rw [Function.comp_apply, Function.comp_apply,dot_norm,Poly.solo_toll]; exact mul_le_mul_of_nonneg_left (h.loss _ ((s_healthy ..).2 hU)) he
end YM.Next.Rank.Edition
