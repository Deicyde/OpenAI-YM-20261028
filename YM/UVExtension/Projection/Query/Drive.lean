import YM.UVExtension.Projection.Query.Run

/-! Solve implicit backwards on Taylor jets inside the query. Uses real-tree differential. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Filter Function Finset ContinuousLinearMap MenuView Run Module
open scoped Topology BigOperators ContDiff Classical
set_option linter.unusedSectionVars false
variable {I X Y E : Type} (P : MenuView I)
  [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup E] [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ E] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]
lemma short {k : ℕ} (c : OrderedFinpartition k) (h : 0<k) (hh : c.length≠1) (i : Fin c.length): c.partSize i<k:=by
  apply lt_of_le_of_ne (c.partSize_le i); intro he
  have hz : Surjective (c.emb i):= by
    let f:= finCongr he
    have hx:= ((c.emb_strictMono i).injective.comp f.symm.injective).surjective_of_finite (Equiv.refl _)
    intro j; obtain ⟨x,hx⟩:= hx j; exact ⟨_,(show c.emb i (f.symm x)=j from hx)⟩
  haveI : Nontrivial (Fin c.length):= by
    have hi:= c.length_pos h; exact Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j,hj⟩:= exists_ne i
  let w : Fin (c.partSize j):= ⟨0,c.partSize_pos j⟩
  have hx := c.disjoint (Set.mem_univ i) (Set.mem_univ j) hj.symm
  exact Set.disjoint_left.mp hx (show c.emb j w∈Set.range (c.emb i) from hz _) ⟨w,rfl⟩
lemma edge_coin {k:ℕ}(h:0<k)(v : Fin k→ X) (f:X→ Y)(g:Y→ E)(x : X)(hp:ContDiffAt ℝ ω f x)(_he:ContDiffAt ℝ ω g (f x)):
    fderiv ℝ g (f x) (iteratedFDeriv ℝ k f x v)=∑ c ∈ univ.filter (fun c : OrderedFinpartition k=> c.length=1), flight c g f x v:=by
  let L:= fderiv ℝ g (f x)
  have hu (c:OrderedFinpartition k) (hc : c.length=1): flight c L f x v=flight c g f x v:=by
    -- length transport using jet equality not cast embeddings
    unfold flight
    have hx : iteratedFDeriv ℝ c.length L (f x)= iteratedFDeriv ℝ c.length g (f x):=by
      rw [hc]; ext1 v; simp; rfl
    rw [hx]
  have hv (c: OrderedFinpartition k) (hc : c.length≠1) : flight c L f x v=0 := by
    have hl : 2 ≤ c.length := by have hx:= c.length_pos h; omega
    unfold flight
    have hx : iteratedFDeriv ℝ c.length L (f x)=0:=by
      obtain ⟨n,hn⟩:= Nat.exists_eq_add_of_le hl
      rw [hn,show 2+n=n+1+1 by omega]; ext1 w; rw [iteratedFDeriv_succ_apply_right]; simp [iteratedFDeriv_succ_const]
    rw [hx]; rfl
  rw [← (show iteratedFDeriv ℝ k (L ∘ f) x v=fderiv ℝ g (f x) (iteratedFDeriv ℝ k f x v) from DFunLike.congr_fun (L.iteratedFDeriv_comp_left hp le_top) v), path hp L.contDiff.contDiffAt]
  apply Eq.trans (sum_subset (filter_subset (fun c:OrderedFinpartition k=> c.length=1) univ) (fun i hi hh=> hv i (fun he=> hh (mem_filter.mpr ⟨hi,he⟩)))).symm
  exact sum_congr rfl fun i hi=> hu i (mem_filter.mp hi).2
lemma arising {k : ℕ} (v : Fin k→ X)(h : 0<k) (g : Y→E) (f:X→Y)(x:X)(he:ContDiffAt ℝ ω f x)(hg:ContDiffAt ℝ ω g (f x)):
    iteratedFDeriv ℝ k (g∘f) x v=fderiv ℝ g (f x) (iteratedFDeriv ℝ k f x v)+∑ c∈univ.filter (fun c:OrderedFinpartition k=> c.length≠1), flight c g f x v:=by
  rw [edge_coin h v f g x he hg,path he hg]; exact (sum_filter_add_sum_filter_not ..).symm

def mast (d : ℕ) : ℕ→ℕ
  | 0=>0
  | n+1=> (n+1)*mast d n+d
lemma mast_rises (d : ℕ):Monotone (mast d):= monotone_nat_of_le_succ (fun i=> by rw [mast]; exact le_trans (le_mul_of_one_le_left (Nat.zero_le _) (by omega)) (Nat.le_add_right ..))

def cannon (V : X×Y→ E):Y→L[ℝ] E:= (fderiv ℝ V 0).comp (ContinuousLinearMap.inr ℝ _ _)

lemma producing {F : I→X×Y→ E} {U : I → X → Y} {d k : ℕ} (h : Run P d k F 0) (he: ∀ i,ContDiffAt ℝ ω (U i) 0) (hv : ∀ i,U i 0=0) (T : Set (Y →L[ℝ] E)) (ht : IsClosed T) (hp : ∀ i,cannon (F i) ∈ T) (hi : ∀ i : Y →L[ℝ] E,i∈T → i.IsInvertible) (hx : P.sees 0 fun i=> fderiv ℝ (F i) 0) (hh : ∀ i,(fun x=> F i (x,U i x)) =ᶠ[𝓝 0] 0) : Run P (mast d k) k U 0:=by
  letI := FiniteDimensional.complete ℝ Y
  -- prepare inverse paid by zero degree only
  let g i a := (a,U i a)
  have hg i: ContDiffAt ℝ ω (g i) 0:= contDiffAt_id.prodMk (he i)
  have ho i : g i 0=0:=by unfold g; rw [hv]; rfl
  let V i:=cannon (F i)
  have hu i := hi _ (hp i)
  have hc : P.sees 0 V:= laminate P _ fun i=> acts hx (ContinuousLinearMap.apply ℝ E (0,i)).toLinearMap
  have hh':P.sees 0 fun i=> (V i).inverse:= crossing hc hp ht (fun i hb=> ((hi i hb).contDiffAt_map_inverse (n:=1)).continuousAt.continuousWithinAt)
  refine ⟨he,fun i hi p=> ?_⟩
  suffices H : P.sees (mast d i) (fun j=> iteratedFDeriv ℝ i (U j) (0 : X) p) from sees_up H (mast_rises d hi)
  induction i using Nat.strong_induction_on with
  | h i ih=>
  cases i with
  | zero=> simp_rw [iteratedFDeriv_zero_apply,hv]; exact steady P _ _
  | succ i=>
    let v:= iteratedFDeriv ℝ (i+1) (fun x:X=> x) 0 p
    let L:= fun t=> fderiv ℝ (F t) 0 (v,0)
    let s:= univ.filter (fun c:OrderedFinpartition (i+1)=> c.length≠1)
    let D t:=∑ c∈s, flight c (F t) (g t) 0 p
    let l t:=iteratedFDeriv ℝ (i+1) (U t) 0 p
    have H t : V t (l t)= -(L t+D t):=by
      have hh : iteratedFDeriv ℝ (i+1) (F t ∘ g t) 0=iteratedFDeriv ℝ (i+1) 0 0:= ((hh t).iteratedFDeriv ℝ (i+1)).eq_of_nhds
      have He : iteratedFDeriv ℝ (i+1) (g t) 0 p=(v,l t):= DFunLike.congr_fun (iteratedFDeriv_prodMk (f:=fun x:X=>x) (g:=U t) (n:=ω) contDiffAt_id (he t) le_top) p
      have hi:= DFunLike.congr_fun hh p
      rw [arising p (by omega) (F t) _ _ (hg t) (by rw [ho]; exact h.born t),ho,He,show (v,l t)=(v,(0:Y))+(0,l t) by simp,map_add] at hi
      change L t + V t (l t) + D t=iteratedFDeriv ℝ (i+1) (fun _ : X=> (0:E)) 0 p at hi
      simp  at hi
      rw [eq_neg_iff_add_eq_zero, ← hi]; abel
    have Hv : P.sees 0 L:= acts hx (ContinuousLinearMap.apply ℝ E (v,0)).toLinearMap
    have H' : P.sees (mast d (i+1)) D := aggregated s _ fun j hj=> soar (x:=fun i=>0) j p (fun v=>by simp_rw [ho]; exact h.tests j.length (j.length_le.trans hi) v) fun u v=>by
      have hz:= short j (by omega) (mem_filter.mp hj).2 u
      have Hx:= ih _ hz (le_trans (le_of_lt hz) hi) v
      unfold g; simp_rw [iteratedFDeriv_prodMk (f:=fun x:X=>x) contDiffAt_id (he _) le_top]; exact sees_both (steady P _ _) (sees_up Hx (mast_rises d (Nat.le_of_lt_succ hz)))
    have hW t : l t=(V t).inverse (-(L t+D t)):= by
      rw [← H]; obtain ⟨z,hz⟩:= hu t; change _= V t at hz; rw [← hz,inverse_equiv]; simp
    change P.sees _ l
    refine (put_linear P _ _ hh' (acts (joins (sees_up Hv (Nat.zero_le _)) H') (-(LinearMap.id (R:=ℝ))))) |> fun hQ=> ?_
    convert hQ using 1
    simp
    exact funext hW
end YM.UVExtension.Projection
