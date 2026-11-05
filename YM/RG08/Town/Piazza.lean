import YM.RG08.Run.Eclog
/-!
# Situated cover operations: move the root by translating true positions

Everything here scalar unless measuring another chosen carrier. No translation
of kernels wrapped before changing native mesh.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run
open scoped BigOperators Topology Real ContDiff Classical
variable {I α β Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y] {F : Screed Y α}
variable {n r t k i : ℕ}{z x:Cover}{m:Side}{η A:ℝ} {U : Rooted Y α r}
section place
def gang (z:Cover) : Beads α r≃Beads α r where
  toFun:=shiftedBy z
  invFun:= shiftedBy (-z)
  left_inv a:= funext fun i=>by simp [shiftedBy]
  right_inv a:= funext fun i=>by simp [shiftedBy]
def roam (x : Cover)(U : Rooted Y α r) := U ∘ (gang x).symm
def season (x: Cover)(F : Screed Y α) : Screed Y α:=fun i r=> roam x (F i r)
lemma pens_roam (h : Pens U)(x:Cover) : Pens (roam x U) := h.comp_injective (gang x).symm.injective
lemma tidy_roam (h : Tidy U)(x:Cover) : Tidy (roam x U) := ⟨pens_roam h.pens x, fun i j=> h.woven (shiftedBy (-x) i) j⟩
lemma roam_grows (a:Beads α r)(z) : girth (gang z a) ≤ girth a + r*size z := by
   unfold girth; rw [show r*size z=∑ _ : Fin r,size z by simp,←sum_add_distrib]; apply sum_le_sum; intro i _; exact size_add ..
lemma roam_cis (h:cis k η U A)(hp:0≤ η)(z:Cover): cis k η (roam z U) ((1+η*r*size z)^k*A) := by
   let p:=(1+η*r*size z)^k; have hg:0 ≤ p:= by unfold p; positivity
   refine budget_mono (budget_scale hg (budget_pull (gang (α:=α) (r:=r) z).symm (gang (α:=α) (r:=r) z).symm.injective h)) (fun i=>mul_nonneg (zero_le_one.trans (tailp hp i)) (norm_nonneg _)) ?_
   intro i; apply le_trans (mul_le_mul_of_nonneg_right (show tailP k η i ≤ p*tailP k η ((gang z).symm i) from ?_) (norm_nonneg _)) (le_of_eq (mul_assoc ..)); unfold tailP p; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity)
   let q:= girth ((gang z).symm i)
   have he: (girth i:ℝ) ≤ q + (r:ℝ)*size z := by exact_mod_cast (by simpa using roam_grows ((gang z).symm i) z: girth i≤ q+r*size z)
   change _≤ _*(1+η*q); nlinarith only [mul_le_mul_of_nonneg_left he hp,show 0 ≤ (η * ((r:ℕ):ℝ) * (size z:ℝ))*(η*q) by positivity]
lemma roam_group (s:Finset I)(f:I→Rooted Y α r): roam x (∑ i∈s,f i)=∑ i∈s,roam x (f i):= funext fun i=> by simp [roam,Finset.sum_apply]
@[simp] lemma roam_zero (x: Cover) : roam x (0: Rooted Y α r)=0 := rfl
@[simp] lemma roam_scale (x:Cover)(z:ℝ): roam x (z • U)=z • roam x U:=rfl
@[simp] lemma roam_plus (x:Cover) (U V:Rooted Y α r): roam x (U+V)=roam x U+roam x V:=rfl
@[simp] lemma roam_less (x:Cover) (U V:Rooted Y α r): roam x (U-V)=roam x U-roam x V:=rfl
lemma roam_cap (h:Fits t F) : Fits t (season x F) := fun i r he=> h i r fun hp=> he (by rw [season,hp]; rfl)
variable {f:Rooted ℝ α r}[Fintype α]
lemma roam_song (h:Pens f)(p: Site m) : rootSong (roam x f) m p=rootSong f m (p+wrap m x):= by
   funext v; unfold rootSong Tensor.diagonal; rw [stitch_apply (pens_roam h x|>.of_norm), stitch_apply h.of_norm,←Equiv.tsum_eq (gang x)]
   apply tsum_congr; intro i; simp only [roam,Function.comp_apply,Equiv.symm_apply_apply]
   congr 1; apply prod_congr rfl; intro j _; unfold silks; change v (p+wrap m ((i j).1+x),(i j).2)=_; rw [_root_.map_add, ← add_assoc, add_right_comm p]
lemma spring_space [Fintype β]{K:Row α β}(h:Pens f)(ht:Whole K): roam x (spring f K)=spring (roam x f) K := Tidy.uniquely (tidy_roam (spring_tidy h ht) x) (spring_tidy (pens_roam h _) ht) (fun m=> funext fun i=> by
   rw [roam_song (spring_tidy h ht).pens,spring_tell _ h ht,spring_tell _ (pens_roam h x) ht,roam_song h])
end place

-- exact translation without charging any projector error
section step
variable [Fintype α]{p:Option Side}{f:Rooted ℝ α (r+2)}{K:Row α α}
private lemma knot_space : knot p (roam x f) K=roam x (knot p f K):= by
   funext i; let j:Fin (r+2):= Fin.succ (0:Fin (r+1))
   unfold knot; change tuneS K p i • _= tuneS K p (shiftedBy (-x) i) • _; congr 1
   have he : (i j).1 - (i 0).1=(i j).1+ -x - ((i 0).1+ -x):= by abel
   cases p
   · exact congr_arg (K _ _) he
   next m => exact congr_arg (fun z:Cover=> K.acts m (0,(i 0).2) (wrap m z,(i j).2)) he

omit [Fintype α] in
private lemma inward {P:Equiv.Perm α}{k: Equiv.Perm β}{f:α→β}(h : f∘P=k∘f) (g:α→Y): tub (g∘P) f=tub g f∘k := by
   funext b; let u := Equiv.subtypeEquiv P (p:=fun i=> f i=b) (q:=fun i=>f i=k b) (fun i=> by change (f i=b↔ (f∘P) i=k b); rw [h,Function.comp_apply,k.apply_eq_iff_eq]); exact Equiv.tsum_eq u (fun i => g i.val)
-- easier sew via uniqueness
private lemma sew_space {U:Shale α r}(h:Pens U) : roam x (sew U)=sew (roam x U):= Tidy.uniquely (tidy_roam (Tidy.sewn h) _) (Tidy.sewn (pens_roam h _)) (fun m=> by rw [roam_song (Tidy.sewn h|>.pens),sew_diagonal h,sew_diagonal (pens_roam h _),roam_song h])
lemma jib_moves (h:Pens f)(hk:Whole K): roam x (jib p K f)=jib p K (roam x f):= by
   unfold jib; rw [sew_space (((knot_prices h hk _).pours _).scale _),roam_scale,knot_space]; refine congr_arg sew (congr_arg (batting r • ·) ?_); exact Eq.symm (inward (k:=(gang x).symm) (P:=(gang x).symm) (f:=stems) rfl _)
variable {U': Shale α (r+1)} {V': Shale α (k+1)} -- typo
lemma clasp_moves (h:Pens U')(he:Summable V')(hp:Whole K): roam x (clasp K U' V')=clasp K (roam x U') V':= by
   unfold clasp; rw [sew_space ((tie_pens h he hp).scale _),roam_scale]; congr 2
   unfold tie
   let W:=(Equiv.prodCongr (Equiv.prodCongr (gang (α:=α) (r:=r+1) x).symm (Equiv.refl (Beads α (k+1)))) (Equiv.refl Cover)); let X := sires (stemLayer U' V') (wakes K)
   rw [show sires (stemLayer (roam x U') V') (wakes K) = X ∘ W from rfl]; symm; apply inward
   funext i; apply funext; intro j; refine Fin.addCases ?_ ?_ j; clear j
   · intro j; change tide ( _, _ ) (Fin.castAdd k j)= shiftedBy (-x) _ _; simp [W,tide,shiftedBy,coral]; rfl
   intro j; change tide (_ , _) (Fin.natAdd r j)= shiftedBy (-x) _ _; simp only [coral,tide,Fin.append_right, shiftedBy]; refine Prod.ext ?_ rfl; change (stem1 (i.1.2) j).1 + ((i.1.1 0).1+ -x + i.2)=(stem1 (i.1.2) j).1+((i.1.1 0).1+i.2)+ -x; abel
lemma grant_moves {U: Rooted ℝ α r} : roam x (grant k U)=grant k (roam x U):= by unfold grant; split_ifs with h; subst k; rfl; rfl
variable {A₀:Screed ℝ α}{S:Canticle α}
set_option maxHeartbeats 400000 in
lemma murmur_places (hK:Whole K)(hS:∀ i j,Tunable (S i j))(h : ∀ i j,Tidy (A₀ i j)) : roam x (murmur p K S A₀ n i r)=murmur p K S (season x A₀) n i r:= by
   induction n using Nat.caseStrongRecOn generalizing i r with
   | zero=> rw [murmur,murmur]; rfl
   | ind n ih=>
     rw [murmur_step,murmur_step,roam_scale,roam_plus, jib_moves (quiet_tidily hK hS h p ..|>.pens) hK,ih n le_rfl,roam_group]
     refine congr_arg (_ • ·) (add_right_inj _|>.mpr (sum_congr rfl ?_)); intro j hj; rw [roam_group]; refine sum_congr rfl ?_; intro k hk; unfold Quire.hymn; rw [roam_group]; refine sum_congr rfl fun l hl=>?_
     rw [grant_moves,clasp_moves (quiet_tidily hK hS h ..|>.pens) (refrains_tune hK hS ..|>.1) hK,ih j.1 (by have he:=mem_antidiagonal.mp hj; omega)]
lemma washes (t:ℕ)(h:∀ i j,Tidy (A₀ i j))(hk:Whole K)(hS:∀ i j,Tunable (S i j)) : season x (washed t p K S A₀)=washed t p K S (season x A₀) := by
   funext i r; unfold washed season; rw [roam_group]; exact sum_congr rfl fun i _=>murmur_places hk hS h
lemma hill_places (Q:PowerSeries ℝ) : season x (hill Q A₀)=hill Q (season x A₀) := by
  funext i r; simp only [season,Tall.hill,roam_group,roam_scale]
end step
end YM.RG08.Town
