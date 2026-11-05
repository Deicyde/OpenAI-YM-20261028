import YM.Next.WARD_BIN.Alone
import YM.Next.WARD_BIN.Lambda
import YM.Next.WARD_BIN.Printing

/-!
# Full-rank stop / attaching at the *same physical* cutoff

Initialization of simultaneous differences. R-dependent mesh thresholds only in
this top operation (estimates consume via fuse, not strengthen to cofinal
period-independent estimates!). Uses no extrapolation of `Hit A` to `A+a`.
No factorial hidden; explicit `card_Torus^K` or such NOT affordable for tanks
repeated over steps: here we consume `Fintype.card Strong` at cutoff once for
all losses, can pay in fused meshes at actual period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Cloud
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay Gas Lambda Crest
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] {R : Rep G n} {Y : V → Support n} {T : V → Site n} {f : V → Config G n → ℂ}
  {Q : V → Rib G n} {u v c d a δ w κ' : ℝ} {W b : V → ℝ} {A : Bands (Full V) R}

abbrev Strong (V : Type) [Fintype V] [DecidableEq V] := {i : Mode V // 2 ≤ i.val.card}
abbrev shell (p : Strong V) := p.val.val
lemma tall (p : Strong V) : (shell p).Nonempty := card_pos.mp (by have h : 2 ≤ (shell p).card := p.property; omega)
lemma divides (p : Mode V) : p=(Full V).quiet ∨ (∃ i,p=(Full V).fire i) ∨ 2≤p.val.card := by
  by_cases h : p.val=∅; exact Or.inl (Subtype.ext h)
  have hG : 0 < p.val.card := card_pos.mpr (nonempty_iff_ne_empty.mpr h)
  refine Or.inr ?_; by_cases he : p.val.card=1
  · obtain ⟨i,hi⟩:=card_eq_one.mp he; exact Or.inl ⟨i,Subtype.ext hi⟩
  exact Or.inr (by omega)

variable [Nontrivial V] (D : Pad R.activities R.p)

abbrev mode2 (V : Type) [Fintype V] [DecidableEq V] := Stock.final V

-- canonical pad for expansion (may differ from the single-marker addresses)
def plume (Y : V → Support n) (f : V → Config G n → ℂ) : Crest G n (Full V) where
  surface _ := Finset.univ
  bits := 0
  aims _ := mode2 V
  doses i j := Sum.elim (fun p : Strong V => D.lay (offer Y f R.activities R.p.threshold (shell p)) i) (fun _ => 0)
    ((enf (Strong V)).symm j)
  creed _ j := Sum.elim Subtype.val (fun _ => mode2 V) ((enf (Strong V)).symm j)

omit [Nontrivial V] in
lemma populous (i) (v : Strong V) : (plume D Y f).doses i (enf _ (.inl v))=D.lay (offer Y f R.activities R.p.threshold (shell v)) i := by simp only [plume,Equiv.symm_apply_apply, Sum.elim_inl]



omit [Nontrivial V] in
lemma roof (Y : V → Support n) {p : BudgetPoint} {w : ℝ} (hw : 0≤w) (e : V → ℝ) (X : Strong V) (Z : ℕ)
    (h : ∀ i,(Y i).card ≤ Z) (ht : ∀ i,0 ≤ e i) (hU : ∀ i, 0 ≤ W i) (hf : ∀ i,W i*p.mass (Y i) (e i) ≤ 1) :
    Poly.toll W X.val * bill p w Y e (shell X) ≤ Real.exp ((Z*Fintype.card V:ℕ)*w)-1 := by
  have hH := ((card_biUnion_le (s:=shell X) (t:=Y)).trans (sum_le_sum (g:=fun _ => Z) (fun i _ => h i))).trans
    (show (∑ _i∈shell X,Z)≤Z*Fintype.card V by
      rw [sum_const,nsmul_eq_mul,mul_comm Z]; apply Nat.mul_le_mul_right; exact card_le_univ _)
  unfold Poly.toll bill
  rw [← mul_assoc, ← prod_mul_distrib]
  apply le_trans (mul_le_of_le_one_left (by apply sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    (show ∏ i∈shell X, W i*p.mass (Y i) (e i) ≤ 1 by
      exact prod_le_one (fun i _ => mul_nonneg (hU _) (mul_nonneg (Real.exp_pos _).le (ht _))) (fun i _ => hf _)))
  exact sub_le_sub_right (Real.exp_monotone <| mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hH) hw) 1

omit [Nontrivial V] in
lemma climates (k : ℕ) (hk : ∀ i, (Y i).card ≤ k) (hf : ∀ i U,‖f i U‖ ≤ b i) (hx : ∀ i,W i*R.p.mass (Y i) (b i) ≤ 1)
    (h : R.activities.KBound R.p w) (hw : 0 ≤ w) (hg : 0 ≤ c) (ht : ∀ i,0 < W i)
    (hi : (Fintype.card (Strong V):ℝ)*(Real.exp ((k*Fintype.card V:ℕ)*w)-1)≤κ'*c) :
    (plume D Y f).Rich R T W 0 c κ' := by
  let L:=plume D Y f
  let F := Real.exp ((k*Fintype.card V:ℕ)*w)-1
  have he (v : Strong V) : ∃ b : ℕ→ℝ,(∀ i,0 ≤ b i ∧ ∀ U, ‖L.doses i (enf _ (.inl v)) U‖ ≤ b i) ∧
      SumBudget (fun i => Poly.toll W v.val*air R.p (R.activities.forced i).support 0 (b i)) F := by
    obtain ⟨b',hB,hP,hb⟩ := all_cost Y (tall v) h hf
    obtain ⟨hE,H⟩ := D.cash hB hP (p:=R.p)
    refine ⟨D.lay b',fun i => by rw [show L=plume D Y f from rfl,populous]; exact H i,?_⟩
    simp_rw [air_mass]; exact purse_mono (roof Y hw b v k hk (fun i => (norm_nonneg _).trans (hf i 1)) (fun i => (ht i).le) hx)
      (purse_unit (Poly.worth ht _).le (purse_mono hb hE))
  choose b' hB hH using he
  let d (p : ℕ×ℕ) := Sum.elim (fun v => b' v p.1) (fun _ => (0:ℝ)) ((enf (Strong V)).symm p.2)
  let t (p : ℕ×ℕ) := Poly.toll W (L.creed p.1 p.2)*air R.p (R.activities.forced p.1).support 0 (d p)
  have hs (v : Strong V) : SumBudget (fun i => t (each (Strong V) (.inl (i,v)))) F := by
    simpa only [each_inl,t,L,plume,d,Equiv.symm_apply_apply,Sum.elim_inl] using hH v
  have hv (p : ℕ×ℕ) : t (each (Strong V) (.inr p))=0 := by simp [t,d,each_inr,air]
  have hT : SumBudget t (κ'*c) := by
    refine purse_roll (each (Strong V)) (purse_mono (u:= (Fintype.card (Strong V):ℝ)*F + 0) ?_ (purse_sum ?_ ?_)) rfl
    · rw [add_zero]; exact hi
    · let g := fun p : Strong V×ℕ => t (each (Strong V) (.inl (p.2,p.1)))
      refine purse_roll (Equiv.prodComm (Strong V) ℕ) (g:=g) ?_ rfl
      have he (p : Strong V×ℕ) : 0≤g p := (hs p.1).1 p.2
      have hp : Summable g := (summable_prod_of_nonneg he).mpr ⟨fun i => (hs i).2.1,(hasSum_fintype _).summable⟩
      refine ⟨he,hp,?_⟩
      rw [hp.tsum_prod,tsum_fintype]; exact (sum_le_sum (g:=fun _=>F) (fun i _ => (hs i).2.2)).trans (by simp)
    simp only [comp_def,hv]; exact ⟨fun _ => le_rfl,summable_zero, by simp⟩
  refine ⟨⟨fun _ => 0,fun _ => le_rfl,fun i j _ => (zeroPrice _ _ _).2,fun i => ?_⟩,⟨d,fun ⟨i,j⟩ => ?_,fun i j Us => ?_,fun i => ?_⟩⟩
  · simp only [air,mul_zero,ite_self]; exact purse_mono hg ⟨fun _ => le_rfl,summable_zero,by simp⟩
  · obtain ⟨p|k,rfl⟩ := (enf (Strong V)).surjective j
    · simp only [d,Equiv.symm_apply_apply,Sum.elim_inl]; exact (hB p i).1
    simp [d]
  · obtain ⟨p|k,rfl⟩ := (enf (Strong V)).surjective j
    · simp only [d,Equiv.symm_apply_apply, Sum.elim_inl]; exact (hB p i).2 _
    simp [d,plume]
  exact purse_low hT (fun p => by split; exact hT.1 _; exact le_rfl) (fun p => by split; exact le_rfl; exact hT.1 _)

omit [Nontrivial V] in
lemma full_vac (M : Support n) (K : Shape n → ℝ) :
    Poly.send (Full V).quiet (↑(fest M K):ℂ)=fest M (fun i => Poly.send (Full V).quiet (K i:ℂ)) := by
  unfold fest; change Poly.bead _ _= _
  rw [Complex.ofReal_sum,map_sum]; refine sum_congr rfl fun i _ => ?_; unfold occ; split
  · rw [Complex.ofReal_prod, map_prod]; rfl
  rw [Complex.ofReal_zero,map_zero]

omit [Nontrivial V] in
lemma till_lambda (Y : V → Support n) (F : V → ℂ) (K : Shape n → ℝ) (X : Finset V) (M : Support n) (q : Shape n) :
    till Y (fun i => fuse i (F i)) (fun i => Poly.send (Full V).quiet (K i : ℂ)) M X q=Poly.send (chest X)
      (till Y F (fun i => (K i : ℂ)) M X q) := by
  unfold till; split
  · have he (B : Finset (Shape n)) : (∏ i∈B, Poly.send (Full V).quiet (K i : ℂ))=Poly.send (Full V).quiet (∏ i∈B,(K i:ℂ)) := (map_prod (Poly.bead _) _ _).symm
    ext i; rw [Poly.part_sum]
    by_cases h : i=chest X
    · subst i; rw [Poly.part_send,if_pos rfl]
      refine sum_congr rfl fun j hj => ?_; unfold Gas.chance
      rw [he,parade,scalar_mul,Poly.part_send]; simp only [((goes Y _ _ _).mp hj).1, ↓reduceIte]
    rw [Poly.part_send,if_neg h]; refine sum_eq_zero fun j hj => ?_; unfold Gas.chance
    rw [he,parade,scalar_mul,Poly.part_send]; simp only [((goes Y _ _ _).mp hj).1,if_neg h]
  exact (Poly.send_zero _).symm

omit [Nontrivial V] in
lemma till_slots (Y : V→ Support n) (F : V→ℂ) (K : Shape n→ℝ) (M : Support n) (q : Shape n) (i : Mode V) :
    let G := merge Y (fun i => fuse i (F i)) (fun i => Poly.send (Full V).quiet (K i:ℂ)) M q
    G.part i=(if i=(Full V).quiet then (K q:ℂ) else 0)+till Y F (fun i => (K i:ℂ)) M i.val q := by
  intro G; unfold G; rw [Gas.front,Poly.part_plus,Poly.part_send,Poly.part_sum]
  simp_rw [till_lambda,Poly.part_send]; congr 1; rw [sum_eq_single i.val]
  · exact if_pos rfl
  · exact fun j _ hj => if_neg fun H => hj (congr_arg Subtype.val H).symm
  simp

omit [Nontrivial V] in
lemma buried (D : Pad R.activities R.p) (i : ℕ) (b : Strong V) (U : Config G n) (h : A.Active)
    (hr : A.Radial W u v c d) (hh : R.activities.Valid R.p δ w) (he : A=meld Q (plume D Y f) R) :
    (A.each i U).part b.val=D.lay (offer Y f R.activities R.p.threshold (shell b)) i U := by
  have hx : b.val≠(Full V).quiet := fun H => (tall b).ne_empty (congr_arg Subtype.val H)
  rw [Bands.each, Poly.part_plus, Poly.share ((A.baseBound h hr hh U).1 i),Poly.part_send,if_neg hx,zero_add,
    ← Equiv.tsum_eq (enf V), tsum_eq_single (Sum.inr (enf _ (Sum.inl b)))]
  · subst A; simp [Bands.tagged,plume,meld]
  intro k hk; rcases k with a|p
  · subst A; simp only [Bands.tagged, meld,Equiv.symm_apply_apply,Sum.elim_inl, Poly.part_send]
    exact if_neg (distant a _ b.property).symm
  obtain ⟨a|j,rfl⟩ := (enf (Strong V)).surjective p
  · subst A; simp only [Bands.tagged,plume,meld,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,Poly.part_send]
    exact if_neg (fun H => hk (congr_arg _ (congr_arg _ (congr_arg Sum.inl (Subtype.ext H.symm)))))
  subst A; simp [Bands.tagged,plume,meld]

omit [Nontrivial V] in
lemma thicker (h : ∀ i,(Q i).Pitched R) (hg : (plume D Y f).Green R (fun i => (Q i).root))
    (hr : (meld Q (plume D Y f) R).Radial W u v c d) (U : Config G n) :
    (meld Q (plume D Y f) R).extra U = ∑ i,fuse i ((Q i).fares R U) := by
  ext t; rcases divides t with (rfl|⟨i,rfl⟩|hp)
  · rw [quiet_extra _ ((plume D Y f).joined h hg) hr,Poly.part_sum]; symm
    exact sum_eq_zero fun i _ => by simp only [fuse,Poly.part_send,if_neg ((Full V).fire_hot i).symm]
  · simp [fire_extra h hg hr,fuse,Poly.part_sum]
  rw [Poly.part_sum, sum_eq_zero (fun i _ => by simp only [fuse,Poly.part_send,if_neg (distant i t hp).symm])]
  rw [Bands.extra,Poly.part_plus,Poly.part_sum,sum_eq_zero (fun i _ => by rw [Poly.part_send,if_neg (distant i t hp).symm]),
    zero_add,Poly.share (((meld Q (plume D Y f) R).bulkBound ((plume D Y f).joined h hg) hr U).1)]
  have he (i) : ((meld Q (plume D Y f) R).ray i U).part t=0 := by
    obtain ⟨⟨i,j⟩|i,rfl⟩ := (enr V).surjective i
    · simp only [Bands.ray,meld,Equiv.symm_apply_apply,Sum.elim_inl,Poly.part_send,if_neg (distant i t hp).symm]
    simp only [Bands.ray, meld, plume, Equiv.symm_apply_apply,Sum.elim_inr, Pi.zero_apply]
    by_cases h : Healthy R.p.threshold Finset.univ U
    · rw [masked_eq _ _ _ _ h,Pi.zero_apply]; simp
    rw [masked_ne _ _ _ _ h]; simp
  simp_rw [he,tsum_zero]

omit [Nontrivial V] in
lemma each_sum (A : Bands (Full V) R) (hv : A.Active) (hr : A.Radial W u v c d) (he : R.activities.Valid R.p δ w)
    (U : Config G n) : Summable fun i => A.each i U := (Poly.budgeted hr.pure (A.baseBound hv hr he U).2.2.1 (fun i => (le_refl (Poly.price W (A.each i U))))).1

/- Grouped offer entry. Don't require top solo tags all at Pad D, use
Pressed certificate to identify after *grouping*. Pointwise all configs. -/



end YM.WardBin.Cloud
