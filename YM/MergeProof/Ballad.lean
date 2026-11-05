import YM.MergeProof.Gallery
import YM.MergeProof.Weathervane
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{f c:Side}
variable {R:Rep G f}{E:Rep G c}
   {ι:Type}(m:Motion)
-- Bolts don't depend on population order class. permute labels
variable (x:Site c)(a: Site f)(H: GaugeDoor R E)(π:R.activities.Moves m.1 a)
lemma climb_entry (M:Leaf R): entry (Leaf.route π M)=floatUp m a (entry M):=by
   funext p U; obtain ⟨q,rfl⟩:= (puff m a).surjective p
   unfold entry floatUp stepUp Leaf.route; simp only [Equiv.symm_apply_apply]; cases M.turn
   · exact (scalar_z m).symm
   rename_i i; unfold Wing.labelRoute; dsimp only; simp_rw [location m a π]; simp only [Equiv.apply_eq_iff_eq];split;exact (scalar_real ..).symm; exact (scalar_z m).symm
lemma climb_p (M:Leaf R): prose (Leaf.route π M)= stepUp m a (prose M):=by
    funext U; unfold prose stepUp Leaf.route; dsimp only; cases M.turn
    exact (scalar_real _ _).symm; exact (scalar_z m).symm
lemma crestSky (M:Leaf R): (Leaf.route π M).crest= sky m a M.crest:=by
   change (Wing.labelRoute π M.turn).support R=_; rw [Wing.supRoute,shading];rfl
lemma fareSky (M:Leaf R):load (Leaf.route π M)=load M:=by
   unfold load; rw [crestSky m a π M, shading]; unfold BudgetPoint.mass; rw [cover_map (turnSites m.1 a) (turn_sep m.1 a)]; rfl
lemma carries_quote {S:StepData c f} (h:SoundDoor S H) (π: R.activities.Moves m.1 (S.ratio.embed x)):
   ∀ M:Leaf R, quoted H (Leaf.route π M)=floatUp m x (quoted H M):=by
   obtain ⟨p,h⟩:= h.conduct m x π; intro M; unfold quoted; refine roam m x p (fun i U=>?_); dsimp [stepUp]; rw [h,scalar_real]
lemma seriesScalar {f:ι→ℂ}{a}(h:HasSum f a):HasSum (fun i=> scalar m (f i)) (scalar m a):=by
   unfold Motion.scalar;split_ifs;exact h.star;exact h
lemma scalar_sub (a b:ℂ):Motion.scalar m (a-b)= Motion.scalar m a-Motion.scalar m b:= by unfold Motion.scalar; split<;>simp
namespace Odyssey
variable {X:Wing→Prop}{o:Site f}{b:Site c}{v δ:ℂ}{α:Config G f→ℂ}{ωs:Res G f}{β:Res G c}{t u:ℝ}{M:ι→Lotus.Leaf R}{s:ι→ℂ}{ψ:Response G c}
    {H:GaugeDoor R E}(h: Odyssey X o b v α ωs β δ t u H M s ψ)
include h
lemma dancing {S:StepData c f}(hs:SoundDoor S H)(π : R.activities.Moves m.1 (S.ratio.embed x))(hv: scalar m v=v):
    Odyssey (Set.image (Wing.labelRoute π) X) (affine m.1 (S.ratio.embed x) o) (affine m.1 x b) v (stepUp m (S.ratio.embed x) α) (floatUp m (S.ratio.embed x) ωs) (floatUp m x β) (scalar m δ) t u H (Leaf.route π ∘ M) (fun i=> scalar m (s i)) (upwards m x ψ):= by
    obtain ⟨Z,hZ⟩:=hs.conduct m x π; let j:= S.ratio.embed x; refine ⟨fun i=> ⟨?_,⟨_,(h.member i).2,rfl⟩⟩,?_,rise m x h.cost,fun U=> ?_,fun i U=>?_,fun i U=>?_⟩
    · simp_rw [Function.comp_apply,crestSky m _ π,shading]; exact Finset.mem_image_of_mem (turnSites m.1 j) (h.member i).1
    · simpa only [Function.comp_apply, fareSky m j π,norm_scalar] using! h.purchase -- j issue
    · have he:= seriesScalar m (h.lyric (pull m.1 j U)); rw [scalar_sub] at he; exact he.congr_fun (fun i=> by rw [scalar_mul];rw [Function.comp_apply,climb_p m _ π];rfl)
    · obtain ⟨i,rfl⟩:= (puff m (S.ratio.embed x)).surjective i; simp only [Function.comp_apply,climb_entry m _ π,floatUp, stepUp, Equiv.symm_apply_apply, ← scalar_mul]; exact seriesScalar m (h.old i (pull m.1 j U))
    obtain ⟨i,rfl⟩:= (puff m x).surjective i
    rw [hooked m x Z]; simp only [Function.comp_apply,carries_quote m x H hs π,floatUp, stepUp, Equiv.symm_apply_apply,← scalar_sub]
    exact (seriesScalar m (h.grants i (pull m.1 x U))).congr_fun (fun j=> by rw [scalar_mul,scalar_mul,hv])
end Odyssey
end YM.MergeProof
