import YM.TraceExtension.Perfect.Salon

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
namespace Lot
variable {P:Patch}{Y:KernelChoices} {p:Clip}{G:Gauge}{α D β v:ℝ} {W:Type*}(L:W→ Lot G P Y p α D)
set_option quotPrecheck false
variable (K:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1)) (o:∀ w,Site (L w).f)(u:∀ w,Site (L w).c)(hb:0<β)(hp: ∀ w,(K w).strip β (v/P.L.val)) (t:∀ w,(L w).s.Choices)
local notation "K!"=>fun w=> installed (L w).s.ratio (K w)
local notation "F!"=>fun w=>fresh (L w).wood (L w).ρ (K! w) (o w)
local notation "T!"=>fun w=>stampA (L w).s (t w) (F! w)
include hb hp
private lemma doubleC (n:ℕ) (y:∀ w,Lines G (L w).f 1): Calm (overLoc L fun w=> (y w).1) (fun w x=> (T! w) x (Sum.inl (y w))) n:= (left_output (fun i=>(L i).c) _ _ (entire L K o hb hp y))
lemma calm_post (n:ℕ) (y:∀ w, pairA G (L w).f): Calm (overLoc L (fun w=>pairLoc (y w))) (fun w x=> (T! w) x (y w)) n:=by
 classical
 refine Calm.assemble (I:=(fun i=>pairA G (L i).c)) (P:=fun b w=> (y w).isLeft=b) (Finset.univ:Finset Bool) (fun i=>⟨_,mem_univ _,rfl⟩) ?_
 intro i _
 cases i
 · let M:= {w:W// (y w).isLeft=false}; let p m:Lot G P Y p α D:= L (m:M).val
   have h(i:M) : ∃ g,y i.val=Sum.inr g:= by
       cases H:y i.val with
       | inl j=> have h:= i.property; simp [H] at h
       | inr j=> exact ⟨j,rfl⟩
   choose g hg using h
   let D:=fun w:M=>overLoc L (fun w=> pairLoc (y w)) w.val
   have he : overLoc p (fun i:M=>(g i).1)=D:= funext fun i=> by funext z; unfold D overLoc fromV; dsimp only; rw [hg i]; rfl
   change Calm D _ n; erw [← he]
   refine (touch_tangent p (fun i=>K i.val) (fun i=>o i.val) hb (fun i=>hp i.val) (fun i=>t i.val) g).near (fun w=>?_)
   exact Eventually.of_forall fun x=>by rw [hg w]
 let M:= {w:W// (y w).isLeft=true}; let p m:Lot G P Y p α D:= L (m:M).val
 have h(i:M):∃ g,y i.val=Sum.inl g:=by
       cases H:y i.val with
       | inl j=> exact ⟨_,rfl⟩
       | inr j=>have h:= i.property; simp [H] at h
 choose g hg using h
 let D:=fun w:M=> overLoc L (fun w=> pairLoc (y w)) w.val
 have he : overLoc p (fun i:M=>(g i).1)=D := funext fun i=> by funext z; unfold D overLoc fromV; dsimp only; rw [hg i]; rfl
 change Calm D _ n; erw [← he];refine (doubleC p (fun i=>K i.val) (fun i=>o i.val) hb (fun i=>hp i.val) (fun i=>t i.val) n g).near (fun w=>?_); exact Eventually.of_forall fun x=>by rw [hg w]
-- fromV interpolation
lemma paid_post (T : ℝ)(hT:0≤T)(h:∀ w,separation ((L w).s.ratio.embed (u w)) (o w) ≤ T*P.L.val)(n γ:ℕ):
    (∀ w,ContDiffAt ℝ ω (T! w) 0) ∧ ∃ a C:ℝ,0<a ∧ 0≤C ∧ ∀ w k i,k≤n → ∀ d:ℝ,0≤d→ d≤a→
            sail (T! w) 0 (landW (u w)) k i d γ (landW (o w) i /(P.L.val:ℝ)) ≤ C:=by
 let W':=Σ w,pairA G (L w).f
 let L' i:=L (i:W').1
 let Z(i:W'):= pairLoc i.2
 have he:= calm_post L' (fun i=>K i.1) (fun i=>o i.1) hb (fun i=>hp i.fst) (fun i=>t i.fst) n Sigma.snd
 have ht (w): ContDiffAt ℝ ω (T! w) 0:= contDiffAt_pi.mpr fun i=> he.velvet (⟨w,i⟩:W')
 obtain ⟨a,C,c,y,H⟩:= he.shape; let b:=a/2; have h0:= half_pos c
 obtain ⟨M,hM,hx⟩:= shelter_paid (t:=γ) h0.le (half_lt_self c)
 let V:= shelter b γ T; have hV :0≤ V:= (shelter_pos b _ hT).le
 refine ⟨ht,b,(V*M)*C,h0,by positivity,fun w k i hk d hd hv=>?_⟩
 let A:= overLoc L' (fun k:W'=> pairLoc k.snd) ⟨w,i⟩
 apply le_trans ?_ (mul_le_mul_of_nonneg_left (H ⟨w,i⟩ k hk) (show 0 ≤ V*M by positivity))
 change sail (T! w) 0 (landW (u w)) k i d γ (landW (o w) i / _) ≤ V*M*cost A a 0 0 (leaf (fun x=> (T! w) x i) 0 k)
 rw [← footed A (T! w) _ a i (ht w)]; unfold sail cost; rw [Finset.mul_sum]; apply sum_le_sum; intro j _; rw [← mul_assoc (V*M)]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 let l:ℝ:= P.L.val; have hL : 1 ≤ l:=by unfold l; exact_mod_cast (show 1 ≤ P.L.val from P.L.property)
 let p:= (landW (o w) i:ℝ)/l
 let F:=landW (u w) (G:=G); let s:ℝ:= ↑(limitN A j); have hS : 0 ≤ s:= by unfold s; positivity
 have hp : ((limitN F j):ℝ) ≤ p+T+s:=by
    by_cases hq : k = 0
    · subst k; unfold limitN; simp; have hv:0 ≤ p:=by unfold p; positivity
      positivity
    obtain ⟨b,hb⟩:=limitN_mem F j (Nonempty.intro ⟨0,Nat.pos_of_ne_zero hq⟩)
    have he : (A (j b):ℝ) ≤ s:= Nat.cast_le.mpr (limitN_ge ..); rw [hb]
    let R:= (L w).s.ratio; have ht : l=(R.count.val:ℝ):= by unfold l; rw [show R.count=P.L from congr_arg Patch.L (L w).patch]
    let x:= pairLoc i; let y:=pairLoc (j b)
    have hb : A (j b)= separation x (R.embed y):=by simp only [A,overLoc,fromV,x,y,pairLoc]; cases j b <;> rfl
    have hh : F (j b)=separation (u w) y:=by simp only [F,y,landW,pairLoc]; cases j b <;> rfl
    have hu : p=(separation (o w) x:ℝ)/l:=by unfold p x; congr 1; cases i<;>rfl
    have hV := Corona.below R (u w) y; rw [hh,hu]; have hx': l* (separation (u w) y:ℝ) ≤ (T*l+(separation (o w) x:ℝ))+s:=by
       calc
         _ ≤ (separation (R.embed (u w)) (R.embed y):ℝ):=by rw [ht]; exact_mod_cast hV
         _ ≤ ((separation (R.embed (u w)) (o w):ℝ)+(separation (o w) x:ℝ))+(separation x (R.embed y):ℝ) := by exact_mod_cast (separation_triangle (R.embed (u w)) x (R.embed y)).trans (Nat.add_le_add_right (separation_triangle (R.embed (u w)) (o w) x) _)
         _ ≤ _:= add_le_add (add_le_add (h w) le_rfl) (hb ▸ he)
    apply le_of_mul_le_mul_left _ (show 0<l by linarith only [hL]); field_simp; nlinarith only[hx',hL,mul_le_mul_of_nonneg_right hL hS]
 change spot d γ p (limitN F j) ≤ V*M*spot a 0 0 _
 apply (shelter_top hd hv (le_max_left (0:ℝ) ((limitN F j:ℝ)-p)) (max_le (add_nonneg hT hS) (by linarith only[hp])) le_rfl).trans ((shelter_add b _ hT hS).trans ?_)
 refine (mul_le_mul_of_nonneg_left (hx _ hS) hV).trans_eq ?_; unfold V; rw [mul_assoc]; congr 2; simp [spot,shelter,s]

end Lot
end YM.Trace.Perfect
