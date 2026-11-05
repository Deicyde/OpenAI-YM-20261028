import YM.RG12.Shadows.Beryl
/-! General two-clock purchases from per-link compact probes. z sign extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Filter Function ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{I K E F Q:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)][∀ i,NormedAddCommGroup (F i)][∀ i,NormedSpace ℝ (F i)]
variable [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
namespace Flares
variable {f g:Counter I E F}{u v:ℝ}{n:ℕ}
lemma reports (h:Flares R n u f)(hh:Smooths n f)(r:∀ i,K i→ I i)(L:∀ i,K i→ F i →L[ℝ] Q i)(he:∀ i j, ‖L i j‖ ≤ 1): Flares R n u (fun i j=> (L i j) ∘ f i (r i j)) :=by
  have hP := Keeps.rename h r; refine Keeps.assures hP (g:=fun i j=> normJ n ((L i j) ∘ f i (r i j)) 0) ?_
  filter_upwards [hh] with i hi j; rw [abs_of_nonneg (norm_nonneg _),abs_of_nonneg (norm_nonneg _)]
  exact ((L i j).norm_iteratedFDeriv_comp_left (hi (r i j)) le_rfl).trans (mul_le_of_le_one_left (norm_nonneg _) (he ..))
end Flares
namespace Sleeve
variable {v w t:ℝ}{f g:Counter I E F}(H:Sleeve R v w t f)
include H
lemma reports (r:∀ i,K i→ I i)(L:∀ i,K i→ F i →L[ℝ] Q i)(he:∀ i j, ‖L i j‖ ≤ 1): Sleeve R v w t (fun i j=> (L i j) ∘ f i (r i j)) :=
  ⟨Filter.Eventually.mono H.smooth fun _ hi _=> ContinuousLinearMap.contDiff _ |>.contDiffAt.comp _ (hi _), H.zero.reports (H.smooth.mono (by decide)) r L he,H.first.reports (H.smooth.mono (by decide)) r L he,H.second.reports H.smooth r L he⟩
lemma eq (he:∀ i j x, f i j x=g i j x):Sleeve R v w t g:=H.congr (Eventually.of_forall fun i j=> Eventually.of_forall fun v=> (he i j v).symm)
lemma add (hg:Sleeve R v w t g):Sleeve R v w t (f+g):= by
  have hg:= hg.scales (Charges.frozen (-1) R); simp only [add_zero] at hg; have hv:=H.sub hg
  exact hv.eq (fun i j x => by simp)
end Sleeve
section
variable {f h: Drift I E}{p:ℝ}{s:Bool}
abbrev rend (h:Drift I E):Drift I E:= fun i j y=>h i j (-y)
lemma cusp (H:Sleeve R p p (p+1) f)(L:Sleeve R p p (p+1) h)(he:∀ᶠ i:ℕ in atTop, ∀ j, f i j 0 = -(h i j 0))(hp:Flares R 1 (p+1) (f-h)):Touch R 2 p false f (rend h):=by
   have hX: Sleeve R p p (p+1) (f+rend h):= H.add L.flips
   have hZ:Sleeve R (p+1) (p+1) (p+1) (f+rend h):= by
     refine ⟨hX.smooth,Flares.mk (Charges.idle _ R) (he.mono fun i hi j=>?_),hp.same ?_,hX.second⟩
     · rw [normJ,norm_iteratedFDeriv_zero,Pi.add_apply,Pi.add_apply,Pi.add_apply,rend,neg_zero,hi,neg_add_cancel,norm_zero]
     filter_upwards [H.smooth.mono (m:=1) (by decide),L.smooth.mono (m:=1) (by decide),L.flips.smooth.mono (m:=1) (by decide)] with i hf hg hq j
     change normJ 1 (f i j+ fun y=> h i j (-y)) _ ≤ normJ 1 (f i j-h i j) _
     rw [normJ,iteratedFDeriv_add_apply (f:=f i j) (g:= (fun y=>h i j (-y))) (hf j) (hq j),iter_neg _ (hg j),normJ,iteratedFDeriv_sub_apply (hf j) (hg j)]
     simp [sub_eq_add_neg]
   refine ⟨H.call le_rfl le_rfl (by linarith), (hZ.call le_rfl le_rfl le_rfl).same (fun i j x=>by simp [aura])⟩
lemma awakes (H:Sleeve R p (p+1) (p+1) f)(L:Sleeve R p (p+1) (p+1) h)(he:∀ᶠ i:ℕ in atTop,∀ j,f i j 0=h i j 0):Touch R 2 p true f (rend h):=by
   have hz:= H.sub (L.flips)
   refine ⟨H.call le_rfl (by linarith) (by linarith),?_⟩
   simp only [aura,one_smul]; refine Sleeve.call (f:=f-rend h) ⟨hz.smooth,?_, hz.first,hz.second⟩ le_rfl le_rfl le_rfl
   refine Flares.mk (Charges.idle _ R) (he.mono fun i he j=> ?_)
   simp only [normJ,norm_iteratedFDeriv_zero, rend, neg_zero, Pi.sub_apply,he j,sub_self,norm_zero,le_rfl]
end
end YM.RG12.Shadows
