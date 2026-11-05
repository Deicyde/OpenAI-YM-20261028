import YM.RG08.Invert.Hole
/-!
 # Physical-program noise at flat in this turn.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Matrix
open Planned.PrimaryIntegral295 Carrier
open Stationary Analysis FreeResolvent Tree UVExt.Paths Reflect
open scoped BigOperators Topology Real Classical Matrix ContDiff
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}{S:StepData c f}

-- uncolored only if Simple. use colored P. q color by member.
private def al (S: StepData c f) (G:Gauge) : Alley G S.ratio →L[ℝ] Alley G S.ratio:= LinearMap.toContinuousLinearMap {
    toFun:= fun x=>lodgeP G S.ratio (orderTurn sigma (fineL G S.ratio x)) (orderTurn sigma (coarseL G S.ratio x))
    map_add':= by intro x y; simp_rw [map_add]; funext p; rcases p with ⟨p,i|i⟩ <;> rfl
    map_smul':= by intro a x; simp_rw [map_smul]; funext p; rcases p with ⟨p,i|i⟩ <;> rfl }
private lemma al_c (x : Alley G S.ratio): coarseL G S.ratio (al S G x)=orderTurn sigma (coarseL G S.ratio x):= lodge_c ..
private lemma al_f (x : Alley G S.ratio): fineL G S.ratio (al S G x)=orderTurn sigma (fineL G S.ratio x):= lodge_f ..

lemma tone_probe (h: S.patch.Branches S.kernel G) (ξ:G.ColorIndex): HeatV (toneP G c 1) (toneP G f 1) (patron G (probe S)) := by
   let t:S.Choices:= (fun _=>(S.patch.center,1),fun _=>S.patch.center); let w:= S.withinChoice sigma 0 t
   have he : (noiseLaw S t) ∘ al S G=ᶠ[𝓝 0] noiseLaw S t:= by
      let u:=input G f ∘ fineL G S.ratio; have hp : Tendsto u (𝓝 0) (𝓝 1) := by simpa only [← show u 0=1 by unfold u; simp] using (input_cont.comp (fineL ..).continuous).tendsto (0:Alley G S.ratio)
      filter_upwards [hp.eventually (Work.F04.prediction_germ h w t)] with x hx
      have hv:= S.prediction_channel h sigma 0 (u x) t
      rw [show S.prediction _ (S.withinChoice _ _ t)= _ from hx, show S.ratio.embed 0=0 from map_zero S.ratio.root] at hv
      change noiseLaw S t _ = noiseLaw S t _; unfold noiseLaw; rw [al_f,al_c,show input G c (orderTurn sigma (coarseL G S.ratio x))=pull sigma 0 (input G c (coarseL G S.ratio x)) from (flip_links ..).symm, show input G f (orderTurn sigma (fineL G S.ratio x))=pull sigma 0 (u x) from (flip_links ..).symm,hv, ticket_spin]; rfl
   let M:= patron G (probe S)
   have hh (x:Link G c)(y:Link G f): x ⬝ᵥ (M*ᵥ y)=(orderTurn sigma x) ⬝ᵥ (M*ᵥ(orderTurn sigma y)):= by
      let p:=lodgeP G S.ratio 0 x; let q:= lodgeP G S.ratio y 0
      have hp := DFunLike.congr_fun (((he.iteratedFDeriv ℝ 2).eq_of_nhds)) ![p,q] -- chain right
      have ht: iteratedFDeriv ℝ 2 (noiseLaw S t ∘ al S G) 0 ![p,q]=iteratedFDeriv ℝ 2 (noiseLaw S t) 0 ![al S G p,al S G q]:= by
          have hm := Next.Foundations.jets_linear (k:=2) (al S G) ((blot_true S t ξ h 2).1.contDiffAt.of_le le_top)
          refine (DFunLike.congr_fun hm ![p,q]).trans ?_; change iteratedFDeriv ℝ 2 (noiseLaw S t) 0 (fun i=> al S G (![p,q] i))=_; apply congr_arg (fun v:Fin 2→ _ => iteratedFDeriv ℝ 2 (noiseLaw S t) 0 v); ext1 i; fin_cases i <;> rfl
      have hy:= jasper S t ξ h|>.2.2
      rw [ht,hy,hy] at hp; dsimp only at hp
      rw [al_c,al_f,al_c,al_f,show coarseL G S.ratio p=x from lodge_c ..,show coarseL G S.ratio q=0 from lodge_c ..,show fineL G S.ratio p=0 from lodge_f ..,show fineL G S.ratio q=y from lodge_f ..,map_zero,map_zero] at hp
      change S.kernel.penalty*((orderTurn sigma x-M*ᵥ 0) ⬝ᵥ ((0:Link G c)- M*ᵥ orderTurn sigma y))=S.kernel.penalty*((x-M*ᵥ 0) ⬝ᵥ (0 - M *ᵥ y)) at hp
      rw [Matrix.mulVec_zero,sub_zero,sub_zero,zero_sub,zero_sub,dotProduct_neg,dotProduct_neg,mul_neg,mul_neg,neg_inj,mul_right_inj' S.kernel.penalty_pos.ne'] at hp; exact hp.symm
   refine ⟨fun i j=>?_⟩
   have hp (L:Side)(i):orderTurn sigma (Pi.single (toneP G L 1 i) 1)= -(Pi.single i 1 :Link G L):= by rw [signedAs]; congr 1; funext k; simp only [Function.comp_apply,Pi.single_apply,(toneP G L 1).injective.eq_iff]
   have hz:= hh (Pi.single (toneP G c 1 i) 1) (Pi.single (toneP G f 1 j) 1); rw [hp,hp,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg] at hz; simpa using hz.symm
end YM.RG08.Invert
