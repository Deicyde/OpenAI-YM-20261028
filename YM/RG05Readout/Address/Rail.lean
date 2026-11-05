import YM.RG05Readout.Address.Saved

/-!
# Tape alignment ticket, single inspected child/parent pair

Paid alignment JUST on THIS STEP. Multiplication under relative normalizations
later changes reciprocal provisional costs. This is not an arbitrary multisource
replacement. Afterwards `Useful` exposes integrable slice and the same log/gas
single-cut compatible with using Duty.pre in the multisource call.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}{n m:Side}{F:Rep G m}{R:Rep G n}{A: GaugeDoor F R}(S:StepData n m) {Y: Wing→Prop} (o:Site m)(b:Site n)

structure Ride (D:GaugeDoor F R) (χ:ℂ) (p:Three G m) (q:Three G n) (t:ℝ):Prop where
   old : Useful F p
   tomorrow : Useful R q
   pays : ∃ (Y:Set Wing),Y.Finite ∧ ∃ x:ℂ, ‖x‖ ≤ t ∧ Tale Y o b χ p.2.1 (profile F.activities p.2.2) (profile R.activities q.2.2) x t t D
   exactStep : q.1=χ • (S.push F.beta p.1)
section
variable {S o b} {χ ζ θ:ℂ} {p p':Three G m}{q q':Three G n} {c t v w Λ σ k e σ' a b' y z s:ℝ}
variable (h:Ride S o b A χ p q t)
include h
lemma Ride.nonneg :0≤ t:=by obtain ⟨X,hA,x,hx,hB⟩:= h.pays; exact (norm_nonneg _).trans hx
lemma Ride.cost (hp:t≤v) : Ride S o b A χ p q v:=by
    obtain ⟨X,hA,x,hx,hB⟩:= h.pays; exact ⟨h.old,h.tomorrow,⟨X,hA,x,hx.trans hp,hB.climb le_rfl hp hp⟩,h.exactStep⟩
lemma Ride.taller (h' : Ride S o b A χ p' q' v) (ht:SoundDoor S A)(hS:S.IsKernel F.beta G)(hf:F.Lawful σ k e y w)(hr:R.Lawful σ' b' Λ z a): Ride S o b A χ (p+p') (q+q') (t+v):=by
    obtain ⟨X,u,φ,hx,hB⟩:= h.pays; obtain ⟨X',u',ψ,hy,hC⟩:= h'.pays; refine ⟨Useful.join F hf h.old h'.old,Useful.join R hr h.tomorrow h'.tomorrow,⟨X∪X',u.union u',_,(norm_add_le ..).trans (add_le_add hx hy),?_⟩,?_⟩
    · change Tale _ _ _ _ (p.2.1+p'.2.1) (profile F.activities _) (profile R.activities _) _ _ _ _; rw [show (p+p').2.2 = p.2.2+p'.2.2 from rfl, show (q+q').2.2=q.2.2+q'.2.2 from rfl, MergeProof.Float.prof_add _ h.old.normK h'.old.normK,MergeProof.Float.prof_add _ h.tomorrow.normK h'.tomorrow.normK]; exact (hB.climb (fun i h => Or.inl h) le_rfl le_rfl|>.plus (hC.climb (fun i h=>Or.inr h) le_rfl le_rfl) ht)
    change q.fst+q'.fst=_; rw [h.exactStep,h'.exactStep,← smul_add, ← StepData.push_add hS _ _ h.old.integr h'.old.integr]; rfl
omit h in
lemma preserves (X:StepData n m) (p:ℝ) (f:Goods G m)(c:ℂ): X.push p (c • f)=c • X.push p f:=by
    funext U; unfold StepData.push; change ∫ u, X.density p u U • (c • f u) ∂prior G _= c • ∫ u, X.density p u U • f u ∂prior G _; simp_rw [smul_comm _ c,integral_smul]
lemma Ride.matchPay (u:ℂ)(w:ℂ)(v:ℂ)(hu:w*χ = v*u): Ride S o b A v (u • p) (w • q) (max ‖u‖ ‖w‖*t):=by
    obtain ⟨X,hX,x,hx,hB⟩:= h.pays; have hp:=mul_le_mul_of_nonneg_right (le_max_left ‖u‖ ‖w‖) h.nonneg; have hr:=mul_le_mul_of_nonneg_right (le_max_right ‖u‖ ‖w‖) h.nonneg; refine ⟨Useful.smul F p u h.old,Useful.smul R q w h.tomorrow,⟨X,hX,u*x,(norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans hp),?_⟩,?_⟩
    · obtain ⟨I,hI,M,s,ψ,J⟩:=hB; have hJ:=J.quaver u
      have he : Odyssey X o b v (u • p.2.1) (u • profile F.activities p.2.2) (w • profile R.activities q.2.2) (u*x) (max ‖u‖ ‖w‖*t) (max ‖u‖ ‖w‖*t) A M (u • s) (w • ψ):=by
         refine ⟨hJ.member, ⟨hJ.purchase.1,hJ.purchase.2.1,hJ.purchase.2.2.trans hp⟩,stackFee (stack_of J.cost w) hr,hJ.lyric,hJ.old,fun i U=> ?_⟩
         simp only [hook_scale,Pi.smul_apply,smul_eq_mul, ← mul_sub]; exact ((J.grants i U).mul_left w).congr_fun (fun j=>by rw [←mul_assoc,←mul_assoc, ← hu]; ring)
      exact ⟨_,inferInstance, M,u • s,w • ψ,by
        change Odyssey X o b _ (u • p.snd.1) (profile F.activities (u • p.snd.2)) (profile R.activities (w • q.snd.2)) _ _ _ _ _ _ _
        rw [profile_scale, profile_scale]; exact he⟩
    change w • q.fst=_; rw [h.exactStep,show (u • p).fst=u • p.fst from rfl,preserves,smul_smul,smul_smul,hu]
omit h in
lemma Ride.vac :Ride S o b A χ 0 0 0:=by
    refine ⟨Useful.zero F,Useful.zero R,⟨∅,finite_empty,0,(norm_zero.le),?_⟩,?_⟩
    · simp_rw [show profile F.activities (0:Three G m).2.2=0 by ext; simp [profile,cram],show profile R.activities (0:Three G n).2.2=0 by ext; simp [profile,cram]]
      exact taped le_rfl le_rfl
    funext U; simp [StepData.push]
omit h in
lemma Ride.group {I:Type*}(ht:SoundDoor S A)(hS:S.IsKernel F.beta G)(hf:F.Lawful σ k e y w)(hr:R.Lawful σ' b' Λ z a)(V:Finset I){p:I→Three G m}{q:I→Three G n}{u:I→ℝ}(h:∀ i∈ V, Ride S o b A χ (p i) (q i) (u i)): Ride S o b A χ (∑ i ∈ V,p i) (∑ i∈ V,q i) (∑ i∈ V,u i):=by
    induction V using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Ride.vac
    | @insert i r hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).taller (ih (fun i' hi=>h i' (Finset.mem_insert_of_mem hi))) ht hS hf hr
omit h in
lemma tribute {f:Response G n}{s:ℝ}{X:Set Wing}(hw:Attainment R.p b f s):Tale X o b χ 0 0 (hook R.activities R.p.threshold f) 0 0 s A:=by
   refine ⟨Empty,inferInstance, Empty.elim,0,f,⟨by intro i; exact i.elim,by simp [SumBudget],?_,?_,?_,?_⟩⟩ -- purchase massage
   exact hw
   intro; simp; intro; intro; simp; intro; intro; simp
lemma Ride.change (hp:q'.1=q.1)(hr:SoundDoor S A)(hf: Useful R q'){g:Response G n}(hs:profile R.activities q'.2.2=profile R.activities q.2.2+hook R.activities R.p.threshold g)(hc:Attainment R.p b g s) :Ride S o b A χ p q' (t+s):=by -- s undeclared
    obtain ⟨X,hX,x,hx,hB⟩:= h.pays; obtain ⟨a,h₀,hy⟩:=hc.toll; have hn:= sumBudget_credit h₀; refine ⟨h.old,hf,⟨X,hX,x,hx.trans (le_add_of_nonneg_right hn),?_⟩,hp.trans h.exactStep⟩
    rw [hs]; have ht:= hB.plus (tribute hc) hr; simp only [add_zero] at ht; exact ht.climb le_rfl (le_add_of_nonneg_right hn) le_rfl
end
end YM.RG05Readout.Address
