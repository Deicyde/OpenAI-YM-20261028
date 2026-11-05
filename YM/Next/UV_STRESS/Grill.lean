import YM.Next.UV_STRESS.Cover
import YM.Next.UV_STRESS.Stack


/-!
# Grill producers from an old/new marker-array estimate

Conditional expectations *in the actual history*. The remaining estimate is
one real reference **basis** token at a time, but needs a full all-copies root, and changes from
fine O to a coarse bounded localized observable. It is a finite-volume,
finite-scale estimate (uniform in the stated parameters); its production is an
outstanding physical/RG question. We neither assume a positivity property of
any phase, nor try to get the estimate itself from `CellHyp`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Around Wilson Cells Lattice RG
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G) {h d k N p : ℕ}

section shift
variable (t : h ≤ k) (H : k ≤ N) (U : Config G (C.side k p) → ℂ) (D : Config G (C.side N p) → ℂ)

/-- Joint old/new delta product at level k with original O held fixed. No claim
that the *unconditional* coarse placements are independent. -/
def removal (x : Config G (C.side N p)) (y : Config G (C.side k p)) :=
    ∏ i : Site (C.side h p), ((center C.S p t 0).copy i U y-(center C.S p (t.trans H) 0).copy i D x)

def retrieve (x : Config G (C.side N p)) := stack C p N k N (removal C t H U D x) H x

private noncomputable def freed (x : Config G (C.side N p)) (i : Site (C.side h p)) :=
    D (pull ((center C.S p (t.trans H) 0).omega i) ((center C.S p (t.trans H) 0).translateBy i) x)

private lemma coarse_terms (x : Config G (C.side N p)) : removal C t H U D x =
    fun y => ∏ i : Site (C.side h p), (center C.S p t 0).copy i (U-fun _ => freed C t H D x i) y := by
  classical
  funext y; unfold removal; apply Finset.prod_congr rfl; intro i _
  let T := center C.S p (t.trans H) 0
  let M := center C.S p t 0
  change M.copy i U y-T.copy i D x=M.copy i _ y
  by_cases hv : M.hand i
  · have hu : T.hand i:=hv
    simp only [Tiling.copy,hv,hu, ↓reduceIte,Pi.sub_apply, star_sub]
    rfl
  have hu : ¬T.hand i:=hv; simp only [Tiling.copy,hv,hu, ↓reduceIte,Pi.sub_apply]; rfl

lemma attained (r : ℕ) (hp : Interior (region (C.side k p) r) U)
    (fit : ∀ m, m≤N → ∀ l:k≤m, region (C.side m p) (advanceSize C k r m) ⊆ (center C.S p (t.trans l) 0).chamber 0) :
    retrieve C t H U D = fun x => ∏ i, (center C.S p (t.trans H) 0).copy i (stack C p N k N U H - D) x := by
  classical
  funext x
  unfold retrieve; rw [coarse_terms]
  let T := center C.S p (t.trans H) 0
  let f (i : Site (C.side h p)) := fun _ : Config G (C.side k p) => freed C t H D x i
  have hh i : Interior (region (C.side k p) r) (f i) := Interior.constant _ _
  have eq := stack_product C p N k t r H (fun i => U-f i) (fun i => minus hp (hh _)) fit
  refine Eq.trans (congr_fun eq x) ?_
  apply Finset.prod_congr rfl; intro i _
  change T.copy i _ x = T.copy i _ x
  rw [stack_sub _ _ _ _ _ _ _ _ (borel_bounded hp) (borel_bounded (hh i)),
    show stack C p N k N (f i) H=(fun _ => freed C t H D x i) from stack_constant ..]
  by_cases h : T.hand i <;> simp only [Tiling.copy,h, ↓reduceIte, Pi.sub_apply] <;> rfl




end shift

/-- Input proposal.

`r` bound *in native k sites*; cost of the coarse
observable need only be sup bounded at fixed k on these N,p (dependence
on v etc allowed).

Root estimate is in the positive **full same history** law.

Compare ; there the k estimate is through still further coarse
scales, with its own costs.

Here we need the consequence for the last read on
the k-marginal of all the fine O's plus new probes.

Use
all cutoffs with same orthogonal maps and charged schedule; never multiply
one-point estimates instead.

At its uses the integrals are live (above, use also old budgets and
fit). -/
structure Coarse (F : Extraction.Order) (v : C.book.Token) (t : h ≤ k) (r : ℕ) (A ε : ℝ)
    (D : (N p : ℕ) → Config G (C.side k p) → ℝ) : Prop where
  pays : 0 ≤ A
  estimate : F.late fun N p => ∃ H : k≤N,
    Interior (region (C.side k p) r) (paint (D N p)) ∧ (∀ x, |D N p x| ≤ A) ∧
      ‖moment (C.beta N p) (retrieve C t H (paint (D N p)) (C.seen v (0:Site (C.side N p))))‖ ^
        ((Fintype.card (Site (C.side h p)) : ℝ)⁻¹) ≤ ε

def Credit (F : Extraction.Order) (v : C.book.Token) (h : ℕ) : Prop := ∃ r : ℕ,∀ j : ℕ,∀ ε : ℝ,0<ε →
    ∃ k : ℕ,k≥j ∧ ∃ (hp : h ≤ k) (A : ℝ), ∃ D, Coarse C F v hp r A ε D

def Furnace (F : Extraction.Order) := ∀ d m : ℕ,∃ h : ℕ,m≤h ∧ ∀ l≤d, ∀ i : Stones C l, Credit C F ⟨l,piece C l i⟩ h

private def proposed (k : ℕ) (A : (N p : ℕ) → Config G (C.side k p) → ℝ) (N p : ℕ) : Config G (C.side N p) → ℝ :=
    if h : k ≤ N then fun x => (stack C p N k N (paint (A N p)) h x).re else 0

private lemma represents (A : (N p : ℕ) → Config G (C.side k p) → ℝ) (p) (h : k ≤ N) :
    paint (proposed C k A N p) = stack C p N k N (paint (A N p)) h := by
  let G := paint (A N p); let X := stack C p N k N G h
  have he := stack_bar C p N k N G h
  rw [show (fun x => star (G x))=G from funext fun x => by simp [G,paint]] at he
  funext x; unfold proposed paint; rw [dif_pos h]
  have hz : star (X x)=X x := (congr_fun he x).symm
  change (↑(X x).re:ℂ)=X x
  refine Complex.ext ?_ ?_
  · rfl
  have he := congr_arg Complex.im hz
  change -(X x).im=(X x).im at he; rw [Complex.ofReal_im]; linarith

lemma drawing {F : Extraction.Order} (k : ℕ) (v : C.book.Token) (h : Credit C F v k) (ε : ℝ) (he : 0<ε) :
    ∃ D M, Origin C F k v ε D M := by
  obtain ⟨r,hv⟩ := h
  obtain ⟨p,hp⟩ := eventually_atTop.mp (sufficient C r k)
  obtain ⟨j,hi,H,A,D,hD⟩ := hv p ε he
  have hx N p (hz:j≤N) := (hp j hi).choose_spec N p hz
  refine ⟨proposed C _ D,A,hD.pays,?_⟩
  refine hD.estimate.mono fun i hi => hi.mono fun l hh => ?_
  let N:=F.mesh l; let Q:=F.per i
  obtain ⟨hK,hG,hf,hb⟩:=hh
  refine ⟨H.trans hK,?_,?_,?_⟩
  · intro x
    have ht y : ‖paint (D N Q) y‖ ≤ A := (by simpa [paint] using hf y)
    change |proposed C j D N Q x| ≤ A
    rw [show |proposed C j D N Q x|= ‖paint (proposed C j D N Q) x‖ from by simp [paint], represents C D Q hK]
    exact stack_bound C Q N j N _ hK A ht x
  · rw [represents C _ Q hK]
    exact (stack_region C _ _ _ _ _ hK r hG).enlarges (hx N Q hK)
  unfold Tiling.rootTest; rw [represents C _ Q hK, ← attained C H hK _ _ r hG (fun m _ hm => hx m Q hm)]; exact hb

lemma coalesces {F : Extraction.Order} (H : C.Makes) (hp : CellHyp C F) (k : ℕ) (v : Entitled C d) (ε : ℝ) (he : 0<ε)
    (hv : ∀ l≤d, ∀ i : Stones C l, Credit C F ⟨l,piece C l i⟩ k) : ∃ D M, Origin C F k v.val ε D M := by
  obtain ⟨⟨l,v⟩,hl,hw⟩ := v
  let G₁ (i : Stones C l) : C.book.Token := ⟨l,piece C l i⟩
  let V (i : Stones C l) := |(v i).re|
  let B := ∑ i,V i
  have ht : 0≤B := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hf : 0<B+1 := by linarith
  let q := ε/(B+1)
  choose X M hX using fun i : Stones C l => drawing C k (G₁ i) (hv l hl i) q (div_pos he hf)
  choose m hm hx using fun i : Stones C l => budgets_at H hp k (G₁ i)
  let Y (N p) (x) := ∑ i,(v i).re*X i N p x
  refine ⟨Y,∑ i,V i*M i,Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hX i).bound),?_⟩
  change ∀ᶠ u in F.fuse, ∃ hk : k ≤ u.1,
    let N := u.1; let p := u.2
    (∀ x, |Y N p x| ≤ _) ∧ Interior ((center C.S p hk 0).chamber 0) (paint (Y N p)) ∧
      (center C.S p hk 0).rootTest (C.beta N p) (paint (Y N p)-C.seen ⟨l,v⟩ (0:Site (C.side N p))) ≤ ε
  have he' i : ∀ᶠ u in F.fuse, ∃ hk : k ≤ u.1, Interior ((center C.S u.2 hk 0).chamber 0)
      (C.seen (G₁ i) (0:Site (C.side u.1 u.2))) ∧
      (center C.S u.2 hk 0).rootTest (C.beta u.1 u.2) (C.seen (G₁ i) (0:Site (C.side u.1 u.2))) ≤ m i := hx i
  have hy (i) : ∀ᶠ u in F.fuse, ∃ hk : k ≤ u.1,
      let N := u.1; let p := u.2
      (∀ x, |X i N p x| ≤ M i) ∧ Interior ((center C.S p hk 0).chamber 0) (paint (X i N p)) ∧
        (center C.S p hk 0).rootTest (C.beta N p) (paint (X i N p)-C.seen (G₁ i) (0:Site (C.side N p))) ≤ q := (hX i).honest
  filter_upwards [eventually_all.mpr he', eventually_all.mpr hy, large_mesh F k] with u ha hQ hk
  obtain ⟨N,p⟩ := u
  let T := center C.S p hk 0; let β := C.beta N p
  let A i := paint (X i N p); let H₁ i := C.seen (G₁ i) (0:Site (C.side N p))
  have hr (i) : ((v i).re:ℂ)=v i := by
    refine Complex.ext rfl ?_
    have he := congr_arg Complex.im (congr_fun (show star v=v from hw) i)
    change -(v i).im=(v i).im at he; rw [Complex.ofReal_im]; linarith
  have he (i : Stones C l) : ‖v i‖=V i := by rw [← hr i,Complex.norm_real,Real.norm_eq_abs]
  have hz : paint (Y N p)=∑ i,v i • A i := by
    ext1 x; unfold paint Y
    simp_rw [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_apply,Pi.smul_apply,hr]; rfl
  have hl : C.seen ⟨l,v⟩ (0:Site (C.side N p))=∑ i,v i • H₁ i := by
    have ht := seen_sum (C:=C) l (0:Site (C.side N p)) (piece C l) v; rw [pieces_at] at ht; exact ht
  have hu (i) : Interior (T.chamber 0) (A i) := (hQ i).choose_spec.2.1
  refine ⟨hk,fun x => ?_,?_,?_⟩
  · change |Y N p x|≤_
    unfold Y; apply (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_); intro i _; rw [abs_mul]; exact
      mul_le_mul_of_nonneg_left ((hQ i).choose_spec.1 x) (abs_nonneg _)
  · rw [hz]; exact (root_sum T β Finset.univ A v (fun i _ => hu i) (hp.all N p)).1
  change T.rootTest β (paint (Y N p) - C.seen ⟨l,v⟩ (0:Site (C.side N p))) ≤ ε
  rw [hz,hl, ← Finset.sum_sub_distrib]; simp_rw [← smul_sub]
  refine le_trans (root_sum T β Finset.univ (fun i => A i-H₁ i) v
    (fun i _ => minus (hu i) (ha i).choose_spec.1) (hp.all N p)).2 ?_
  calc
    _ ≤ ∑ i : Stones C l,V i*q := Finset.sum_le_sum (fun i _ => by
      rw [he i]; exact mul_le_mul_of_nonneg_left (hQ i).choose_spec.2.2 (abs_nonneg _))
    _ = B*q := (Finset.sum_mul ..).symm
    _ ≤ ε := by
      have hp : (B+1)*q=ε := (mul_comm ..).trans (div_mul_cancel₀ _ hf.ne')
      exact le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (div_pos (by assumption) hf).le) hp.le

theorem provides_Grill {F : Extraction.Order} (H : C.Makes) (hp : CellHyp C F) (h : Furnace C F) : Org.Grill C F := by
  intro d m
  obtain ⟨k,hk,ht⟩ := h d m
  choose D A hv using fun i (v : Entitled C d) => coalesces C H hp k v _ (cost_pos i) ht
  refine ⟨k,hk,fun _ v hv' h => Maker.patrons ?_ H hp v hv' h⟩
  exact ⟨D,A,hv⟩
end YM.Next.UVStress
