import YM.RG12.Shadows.Surface
/-! Simultaneous parity/discrepancy through fixed order n. Argument `remote` meant already
pulled jointly: coarse panel signs reversed and centered gas signs reversed. No derivative
scale assumed. Use to cancel integrated O(g) by *both* quadratic sources & true volumes. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function ConnectedActivityE6 ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{n:ℕ}{p t :ℝ}{s q : Bool}{I I' J:ℕ→Type}{E:ℕ→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
-- true = even
def aura : Bool→ℝ
 | true=>1
 | false=>-1
lemma aura_pair (s : Bool):aura s*aura s=1:= by cases s <;> norm_num [aura]
def fit (s q:Bool): Bool:= if q then s else (!s)
lemma aura_fit (s q:Bool) : aura (fit s q)=aura s*aura q:= by cases s <;> cases q <;> norm_num [aura,fit]
lemma fit_neg_f (s q:Bool):fit (!s) q= !(fit s q):= by cases s <;> cases q <;> rfl
lemma fit_neg_s (s q:Bool):fit s (!q)= !(fit s q):= by cases s <;> cases q <;> rfl
structure Touch (R:Haze)(n:ℕ)(p:ℝ)(s:Bool)(f g:Drift I E): Prop where
  origin : Call R n p f
  listens : Call R n (p+1) (f-aura s • g)
namespace Touch
variable {f g h k:Drift I E}(U:Touch R n p s f h)(V:Touch R n t q g k)
include U
lemma remote : Call R n p h := by
  have hv:= (U.origin.subs (U.listens.mono (show p≤p+1 by linarith))).coat (aura s)
  exact hv.same (fun i j x=> by simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul]; cases s <;> norm_num [aura])
lemma mono (ht:t≤p):Touch R n t s f h := ⟨U.origin.mono ht,U.listens.mono (add_le_add_left ht _)⟩
omit U in
lemma welcomed (hf:Call R n p f): Touch R n p true f f:= ⟨hf,by
   refine Call.same (f:=fun (i:ℕ) (j:I i) (x:E i)=> (0:ℝ)) (Call.up (Charges.idle _ R)) ?_
   intro i j x; simp [aura]⟩
omit U in
lemma antipode (hf:Call R n p f):Touch R n p false f (-f):= ⟨hf,by
   refine Call.same (f:=fun (i:ℕ) (j:I i) (x:E i)=> (0:ℝ)) (Call.up (Charges.idle _ R)) ?_
   intro i j x; simp [aura]⟩
lemma reskin :Touch R n (p-1) q f h:= ⟨U.origin.mono (by linarith),by rw [sub_add_cancel];exact U.origin.subs (U.remote.coat _)⟩
lemma reindex (r:∀ i,I' i→I i):Touch R n p s (fun i j=> f i (r i j)) (fun i j=> h i (r i j)):= ⟨U.origin.reindex r,U.listens.reindex r⟩
lemma same (hf:∀ i j x,g i j x=f i j x)(he:∀ i j x,k i j x=h i j x):Touch R n p s g k:= ⟨U.origin.same hf,U.listens.same (fun i j x=> by simp only [Pi.sub_apply,Pi.smul_apply,hf,he])⟩
lemma plus (V:Touch R n p s g k):Touch R n p s (f+g) (h+k):=⟨U.origin.adds V.origin,by
    exact (U.listens.adds V.listens).same (fun i j x=> by simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_add]; abel)⟩
lemma negates : Touch R n p s (-f) (-h):= ⟨U.origin.negates,U.listens.negates.same (fun i j x=>by simp only [Pi.sub_apply,Pi.smul_apply,Pi.neg_apply,smul_neg]; abel)⟩
lemma coat (r:ℝ): Touch R n p s (r • f) (r • h):= ⟨U.origin.coat _,(U.listens.coat r).same (fun i j x=>by simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring)⟩
lemma subs (V:Touch R n p s g k):Touch R n p s (f-g) (h-k):=by simpa only [sub_eq_add_neg] using U.plus V.negates
include V in
lemma times : Touch R n (p+t) (fit s q) (f*g) (h*k):= by
   have hf:= U.listens.times V.origin; rw [show p+1+t=p+t+1 from by ring] at hf
   refine ⟨U.origin.times V.origin,?_⟩
   have hy:= (U.remote.coat (aura s)).times V.listens; rw [← add_assoc] at hy
   exact (hf.adds hy).same (fun i j x=>by simp only [Pi.sub_apply,Pi.smul_apply, Pi.add_apply,Pi.mul_apply,aura_fit,smul_eq_mul]; ring)
lemma total [∀ i,Fintype (J i)] (r:∀ i,I' i→J i→I i)(hv:Charges R 0 (fun i=> (Fintype.card (J i):ℝ))) : Touch R n p s (fun i k x=>∑ j:J i,f i (r i k j) x) (fun i k x=>∑ j:J i,h i (r i k j) x):=by
  have hg:= U.origin.totals r hv; have hf:= U.listens.totals r hv; rw [zero_add] at hg hf; exact ⟨hg,hf.same (fun i j x=>by simp only [Pi.sub_apply,Pi.smul_apply,Finset.smul_sum,Finset.sum_sub_distrib])⟩
end Touch
-- inputs f6 and change d= f9-f6. Vaccine fit.Learns derivative signs using true parity without assuming linearity.
structure Tilts (R:Haze)(n:ℕ)(p:ℝ)(s:Bool)(f h g k:Drift I E):Prop where
  beam : Touch R n p s f h
  shade : Touch R n (p+1) (!s) (g-f) (k-h)
namespace Tilts
variable {f h g k F H G K:Drift I E}(U: Tilts R n p s f h g k)(V: Tilts R n t q F H G K)
include U
lemma companion :Touch R n p s g k:= by
   have hv:= U.shade.reskin (q:=s); rw [add_sub_cancel_right] at hv; exact (hv.plus U.beam).same (fun _ _ _=>by simp) (fun _ _ _=>by simp)
lemma adds (V: Tilts R n p s F H G K) : Tilts R n p s (f+F) (h+H) (g+G) (k+K):=by
  exact ⟨U.beam.plus V.beam,(U.shade.plus V.shade).same (fun _ _ _=>by simp only [Pi.sub_apply, Pi.add_apply]; abel) (fun _ _ _=>by simp only [Pi.sub_apply, Pi.add_apply]; abel)⟩
lemma same (hf:∀ i j x,F i j x=f i j x)(hh:∀ i j x,H i j x=h i j x)(hg:∀ i j x,G i j x=g i j x)(hk:∀ i j x,K i j x=k i j x):Tilts R n p s F H G K:=
   ⟨U.beam.same hf hh,U.shade.same (fun i j x=> by simp only [Pi.sub_apply,hg,hf]) (fun i j x=> by simp only [Pi.sub_apply,hh,hk])⟩
omit U in
lemma noCast (F: Touch R n p s f h):Tilts R n p s f h f h:= ⟨F,by
    let L: Drift I E:= fun _ _ _=>0; have hl : Call R n (p+1) L:= Call.up (Charges.idle _ R); exact ⟨hl.same (fun _ _ _=> by simp [L]),(Call.up (Charges.idle _ R) (f:=fun _=>(0:ℝ))).same (fun _ _ _=> by simp)⟩⟩
include V in
lemma times : Tilts R n (p+t) (fit s q) (f*F) (h*H) (g*G) (k*K):=by
  have hs:=U.shade.times V.beam; rw [fit_neg_f,show p+1+t=p+t+1 from by ring] at hs
  have ht:=U.companion.times V.shade; rw [fit_neg_s,←add_assoc] at ht
  exact ⟨U.beam.times V.beam,(hs.plus ht).same (fun _ _ _=>by simp only [Pi.add_apply, Pi.sub_apply,Pi.mul_apply]; ring) (fun _ _ _=>by simp only [Pi.add_apply, Pi.sub_apply,Pi.mul_apply]; ring)⟩
lemma reindex (r:∀ i,I' i→I i):Tilts R n p s (fun i j=> f i (r i j)) (fun i j=> h i (r i j)) (fun i j=>g i (r i j)) (fun i j=>k i (r i j)):= ⟨U.beam.reindex r,U.shade.reindex r⟩
lemma total [∀ i,Fintype (J i)] (r:∀ i,I' i→J i→I i)(hv:Charges R 0 (fun i=> (Fintype.card (J i):ℝ))) : Tilts R n p s (fun i k' x=>∑ j:J i,f i (r i k' j) x) (fun i k' x=>∑ j:J i,h i (r i k' j) x) (fun i k' x=>∑ j:J i,g i (r i k' j) x) (fun i k' x=>∑ j:J i,k i (r i k' j) x):=
    ⟨U.beam.total r hv,(U.shade.total r hv).same (fun _ _ _=> by simp only [Pi.sub_apply, Finset.sum_sub_distrib]) (fun _ _ _=>by simp only [Pi.sub_apply,Finset.sum_sub_distrib])⟩
lemma negates : Tilts R n p s (-f) (-h) (-g) (-k):= ⟨U.beam.negates,U.shade.negates.same (fun i j x=>by simp only [Pi.neg_apply,Pi.sub_apply]; abel) (fun i j x=>by simp only [Pi.neg_apply,Pi.sub_apply]; abel)⟩
lemma subs (V: Tilts R n p s F H G K):Tilts R n p s (f-F) (h-H) (g-G) (k-K):=by simpa only [sub_eq_add_neg] using U.adds V.negates
lemma coat (r:ℝ):Tilts R n p s (r • f) (r • h) (r • g) (r • k):= by
   refine ⟨U.beam.coat r,(U.shade.coat r).same ?_ ?_⟩ <;> intro i j x <;> simp only [Pi.sub_apply,Pi.smul_apply,smul_sub]
end Tilts
end YM.RG12.Shadows
