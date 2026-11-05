import YM.Extension.UV.Station.JetSeq
import YM.Extra.WILSON_STARTUP.OnShell
/-! Jet accounting where all basepoints and branch projections are exact. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology BigOperators
open Finset Filter Function
namespace YM.Extension.UV.StationaryData
variable {k:ℕ} (c : OrderedFinpartition k)
lemma counts_parts : ∑ i,c.partSize i = k:=by simpa using (c.sum_sigma_eq_sum (fun (_:Fin k) => (1:ℕ)))
lemma combined_parts (i j:Fin c.length) (h:i≠j): c.partSize i+c.partSize j ≤ k:=by
 have he : ({i,j}:Finset (Fin c.length))⊆univ:=subset_univ _
 simpa [h] using (sum_le_sum_of_subset_of_nonneg (f:=c.partSize) he (by intros; omega)).trans_eq (counts_parts c)
lemma solo_part [hc:Nonempty (Fin c.length)] (h:c.length=1) (i:Fin c.length): c.partSize i=k:= by
 haveI : Subsingleton (Fin c.length):=by rw [h]; infer_instance
 apply Eq.trans _ (counts_parts c); calc
  c.partSize i=(∑ _:Fin c.length,c.partSize i):= by simp [h]
  _ = _ := (congr_arg (fun p=>∑ j : Fin c.length,p j) (show c.partSize=(fun _=>c.partSize i) from funext fun j=>congr_arg c.partSize (Subsingleton.elim j i))).symm -- `Fintype.card_of...` simp
lemma strict_fin_id {n:ℕ} (φ:Fin n→Fin n)(h:StrictMono φ): φ=id:=by
 cases n
 case zero=> exact funext fun i=>i.elim0
 case succ n=>
  have hl (i:Fin (n+1)) : i ≤ φ i:=by
    induction i using Fin.inductionOn with
    | zero=> exact Fin.zero_le _
    | succ j ih=> have he:= ih.trans_lt (h (@Fin.castSucc_lt_succ _ j)); exact Nat.succ_le_of_lt he
  have hu (i:Fin (n+1)) : φ i ≤ i := by
    induction i using Fin.reverseInduction with
    | last=> exact Fin.le_last _
    | cast j ih=> have ht:=(h (@Fin.castSucc_lt_succ _ j)).trans_le ih; exact Nat.le_of_lt_succ ht
  exact funext fun i=>le_antisymm (hu _) (hl _)

lemma full_part [NeZero k] (c:OrderedFinpartition k) (hc:c.length=k): c=OrderedFinpartition.atomic k:=by
 cases c with
 | mk m p ha φ hφ hp hd hv =>
   change m=k at hc; subst m
   have h' := counts_parts (⟨k,p,ha,φ,hφ,hp,hd,hv⟩ : OrderedFinpartition k)
   change (∑ i,p i)= k at h'
   have he : p=(fun _=>1):= funext fun i=> by
     have := single_le_sum (f:=fun j=>p j-1) (fun j _=> Nat.zero_le _) (mem_univ i)
     have hu := calc k = ∑ i, ((p i-1)+1) := by apply h'.symm.trans; exact (sum_congr rfl (fun j _=> (Nat.sub_add_cancel (by apply Nat.succ_le_of_lt; exact ha j)).symm)) -- naming risky
                     _ = (∑ i,(p i-1))+k:=by simp [sum_add_distrib]
     have hi : 0 < p i:=ha i
     omega
   subst p
   have hy := strict_fin_id (fun m=>φ m 0) hp
   obtain rfl := (show φ= (fun m _=>m) from funext fun m=>funext fun j=> (congr_arg (φ m) (Subsingleton.elim j 0)).trans (congr_fun hy m))
   rfl

variable {E F V : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F][NormedAddCommGroup V][NormedSpace ℝ V]
def dirT (f:E→F) (k:ℕ) (x v:E) := iteratedFDeriv ℝ k f x (fun _=>v)
@[simp] lemma dirT_zero (f:E→F) (x v): dirT f 0 x v=f x:=iteratedFDeriv_zero_apply ..
@[simp] lemma dirT_one (f:E→F)(x v): dirT f 1 x v=fderiv ℝ f x v:=iteratedFDeriv_one_apply ..
lemma dirT_ext {x} {f g:E→F} (hf:ContDiffAt ℝ ω f x)(hg:ContDiffAt ℝ ω g x) (hh:∀ v,dirT f k x v=dirT g k x v): iteratedFDeriv ℝ k f x=iteratedFDeriv ℝ k g x:=by
  apply Tensor.ext_diag _ _ (hf.iteratedFDeriv_comp_perm) (hg.iteratedFDeriv_comp_perm); exact funext hh
lemma linear_dirT (g:F→L[ℝ] V)(f:E→F) (x:E) (z:F) (hz:z=f x) (hf:ContDiffAt ℝ ∞ f x) (k:ℕ): ∀ v,dirT (g ∘ f) k x v=g (dirT f k x v):=by
  intro v; unfold dirT; rw [g.iteratedFDeriv_comp_left hf (by exact_mod_cast (le_top (a:=(k:ENat))))]; rfl
lemma tracks_t (f:ℕ→E→F) (f':E→F) (x:E)(hf:Tracks ∞ f f' x)(k) (v:E): Tendsto (fun n=>dirT (f n) k x v) atTop (𝓝 (dirT f' k x v)):=by
 exact mapply (h:=fun n=>iteratedFDeriv ℝ k (f n) x) (hf.jet _ (by exact_mod_cast (le_top (a:=(k:ENat))))) (show Tendsto _ _ _ from tendsto_const_nhds)

abbrev contribution (a:OrderedFinpartition k) (g:F→V) (f:E→F) x v := iteratedFDeriv ℝ a.length g (f x) (fun i=>dirT f (a.partSize i) x v)
lemma pipeline (g:F→V) (f:E→F) (x:E)(hg:ContDiffAt ℝ ∞ g (f x)) (hf:ContDiffAt ℝ ∞ f x) (k:ℕ) : ∀ v,dirT (g ∘ f) k x v=∑ a:OrderedFinpartition k,contribution a g f x v:=by
  intro v; rw [dirT,iteratedFDeriv_comp hg hf (by exact_mod_cast (le_top (a:=(k:ENat))))]
  rw [FormalMultilinearSeries.taylorComp,_root_.sum_apply]; exact sum_congr rfl fun _ _=>rfl

def middle (f:ℕ→E→F) (p:ℕ→F→V) (x v:E) (a:OrderedFinpartition k) (n:ℕ):=contribution a (p n) (f n) x v
lemma partial_tends {k:ℕ} (s:Finset (OrderedFinpartition k)) (f:ℕ→E→F) (p:ℕ→F→V) (g:E→F)(q:F→V) {x} v {r:ℕ} (hs:∀ a∈s,∀ i,a.partSize i≤r)
   (hs':∀ a∈s, a.length ≤ k)
   (h0:∀ᶠ i in atTop,f i x=g x) (hf:∀ j≤r,Tendsto (fun n=>dirT (f n) j x v) atTop (𝓝 (dirT g j x v)))
   (hp:Tracks ∞ p q (g x)): Tendsto (fun n=>∑ a∈s,middle f p x v a n) atTop (𝓝 (∑ a∈s,contribution a q g x v)):=by
 apply tendsto_finsetSum s; intro a ha
 have hu:Tendsto (fun n=> iteratedFDeriv ℝ a.length (p n) (f n x)) atTop _ :=(hp.jet a.length (by exact_mod_cast (le_top (a:=(a.length:ENat))))).congr' (h0.mono fun n hn=>by simp [hn])
 exact mapply hu (tendsto_pi_nhds.mpr fun i=> hf _ (hs a ha i))
end YM.Extension.UV.StationaryData
